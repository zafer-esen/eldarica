package lazabs.horn.heap

import ap.basetypes.IdealInt
import ap.Signature
import ap.parser.IExpression.Predicate
import ap.parser._
import ap.types._
import ap.proof.theoryPlugins.Plugin
import ap.terfor.{Formula, TermOrder}
import ap.terfor.conjunctions.Conjunction
import ap.terfor.preds.Atom
import ap.terfor.substitutions.VariableShiftSubst
import ap.theories._
import ap.theories.ADT
import ap.types.{MonoSortedIFunction, Sort}
import ap.util.Debug

import scala.collection.mutable.{HashMap => MHashMap}
import scala.collection.{Map => GMap}
import scala.collection.mutable.{Map => MMap, Set => MSet}

object Heap {
  //private val AC = Debug.AC_ADT // todo
  abstract sealed class CtorArgSort
  case class ADTSort(num : Int) extends CtorArgSort
  case class OtherSort(sort : Sort) extends CtorArgSort
  case object AddressSort extends CtorArgSort
  case class CtorSignature(arguments : Seq[(String, CtorArgSort)],
                           result : ADTSort)

  class HeapException(m : String) extends Exception(m)

  /** implicit converters from Heap.CtorArgSort to ADT.CtorArgSort */
  private implicit def HeapSortToADTSort(s : CtorArgSort) : ADT.CtorArgSort =
    s match {
      case t : ADTSort => ADT.ADTSort(t.num)
      case t : OtherSort => ADT.OtherSort(t.sort)
      case AddressSort => ADT.OtherSort(Sort.Nat) // todo: might be wrong
  }

  private implicit def HeapSortToADTSort(l : Seq[(String, Heap.CtorSignature)]):
  Seq[(String, ADT.CtorSignature)] = {
    for (s <- l) yield (s._1, ADT.CtorSignature(
      for (arg <- s._2.arguments) yield (arg._1, HeapSortToADTSort(arg._2)),
      ADT.ADTSort(s._2.result.num)))
  }

  class Address(sortName : String,
                heapTheory : Heap) extends ProxySort(Sort.Nat) {
    import IExpression.toFunApplier

    override val name = sortName
    override def decodeToTerm(
                 d : IdealInt,
                 assignment : GMap[(IdealInt, Sort), ITerm]) : Option[ITerm] =
      Some(heapTheory.nthAddr(d.intValue))

    override lazy val individuals : Stream[ITerm] =
      for (t <- Sort.Nat.individuals) yield heapTheory.nthAddr(t)
  }

  class HeapSort(sortName : String,
                 heapTheory : Heap) extends ProxySort(Sort.Integer) {
    import IExpression.toFunApplier
    import heapTheory.{emptyHeap, newHeap, alloc, ObjectSort}
    override val name = sortName

    override lazy val individuals : Stream[ITerm] =
      emptyHeap() #:: (for (t <- individuals;
                            obj <- ObjectSort.individuals)
        yield newHeap(alloc(t, obj)))

    override def decodeToTerm(
                 d : IdealInt,
                 assignment : GMap[(IdealInt, Sort), ITerm]) : Option[ITerm] = {
      assignment get ((d, this))
    }

    override def augmentModelTermSet(
                 model : Conjunction,
                 terms : MMap[(IdealInt, Sort), ITerm],
                 allTerms : Set[(IdealInt, Sort)],
                 definedTerms : MSet[(IdealInt, Sort)]) : Unit = {

      /** Helper function to collect atoms from theory functions */
      def getAtoms (f : IFunction) : IndexedSeq[Atom] =
        model.predConj positiveLitsWithPred heapTheory.heapFunPredMap(f)

      /* Collect the relevant functions and predicates of the theory */
      import heapTheory.{read, emptyHeap, counter}
      val readAtoms = getAtoms(read)
      val counterAtoms = getAtoms(counter)
      val emptyHeapAtoms = getAtoms(emptyHeap)

      import IExpression.{toFunApplier, i}
      /**
       * Helper function to create a heap term recursively. Writes defObj in all
       * places except the last.
       * @param n The counter value of the heap (the last location).
       * @param lastObj The object to be placed at the last location.
       * @return The created heap object.
       */
      def createHeapTerm(n : Int, lastObj : ITerm) : ITerm = {
        n match{
          case 0 => heapTheory.emptyHeap()
          case _ if n > 0 =>
            createNestedHeapTerm(n, heapTheory.emptyHeap(), lastObj)
          case _ => throw new HeapException("createNestedHeapTerm called with" +
                                            " n: " + n + " (must be positive)")
        }
      }
      def createNestedHeapTerm(n : Int, initTerm : ITerm, lastObj : ITerm)
      : ITerm = {
        import heapTheory.{alloc, newHeap, _defObj}
        n match{
          case 1 => newHeap(alloc(initTerm, lastObj))
          case _ => createNestedHeapTerm(n-1,
            newHeap(alloc(initTerm, _defObj)), lastObj)
        }
      }

      /*
       * Every (unique) heap has an associated counter value in the model.
       * So we are first looking at each counter to obtain the heap ids and
       * counter values. Empty heap has counter value 0.
       *
       * Then, for each heap id, we will go through reads to get the value of
       * the object at the last location, which will enable us to create the
       * new heap term.
       *
       * If the heap term (h) cannot be found in reads, it might be just that it
       * was never allocated nor written to from a previous heap
       * (i.e. only isAlloc(h) is asserted). Then this heap term is created
       * using defObj at its last location.
       * */

       /* counter atoms have the form: counter(heapId, counterVal) */
      for (a <- counterAtoms) {
        val heapId = a(0).constant
        val counterVal = a(1).constant
        val heapKey = (heapId, this)
        /* if the heap term has not been assigned a term yet (and it is not
         * the empty heap) */
        if(!(definedTerms contains heapKey) && counterVal != IdealInt(0)) {
          /* First look through all the reads to see if we can gather info
           * on this term (more specifically we want the object value at
           * the last location, i.e. at counterVal)*/

          /* Read atoms have the form: read(heapId, addrVal, objId)
           * We need to find the read (if it exists), where heapId matches and
           * addrVal = counterVal. counterVal = 0 is the empty heap.
           * */
          val objTermId : IdealInt = readAtoms.find(
            ra => ra(0).constant == heapId &&
                  ra(1).constant == counterVal) match {
            case Some(ra) => ra(2).constant
            case None => -1 // create the term using defObj.
          }
          val objTerm : ITerm = objTermId match {
            case IdealInt(-1) => heapTheory._defObj
            case _ => terms.getOrElse((objTermId, heapTheory.ObjectSort), -1)
          }

          if(objTerm != i(-1)) { // skip if objTerm is not defined yet
            val newHeapTerm = createHeapTerm(counterVal.intValue, objTerm)
            terms.put(heapKey, newHeapTerm)
            definedTerms += heapKey
          }
        }
        else if (!(definedTerms contains heapKey)) {
          terms.put(heapKey, emptyHeap())
          definedTerms += heapKey
        }
      }

      // This atom (should be only one in model) has the form emptyHeap(heapId)
      for (a <- emptyHeapAtoms) {
        val heapKey = (a(0).constant, this)
        if (!(definedTerms contains heapKey)) {
          terms.put(heapKey, emptyHeap())
          definedTerms += heapKey
        }
      }
    }
  }
}

/**
 * @param heapSortName
 * @param addressSortName
 * @param objectSort
 * @param sortNames
 * @param ctorSignatures
 */
class Heap(heapSortName : String, addressSortName : String,
           objectSort : Heap.ADTSort, sortNames : Seq[String],
           ctorSignatures : Seq[(String, Heap.CtorSignature)],
           defaultObjectCtor : ADT => ITerm)
    extends Theory {
  import Heap._
  //-BEGIN-ASSERTION-///////////////////////////////////////////////////////////
  /*Debug.assertCtor(AC,
    ctorSignatures forall {
      case (_, sig) =>
        ((sig.arguments map (_._2)) ++ List(sig.result)) forall {
          case Heap.ADTSort(id) => id >= 0 && id < sortNames.size
          case _ : OtherSort => true
          case Heap.AddressSort => true
        }
    })*/
  //-END-ASSERTION-/////////////////////////////////////////////////////////////
  val AddressSort = new Address(addressSortName, this)
  val HeapSort = new HeapSort(heapSortName, this)
  val emptyHeap = new MonoSortedIFunction("emptyHeap", argSorts = List(),
    resSort = HeapSort, _partial = false, _relational = false)

  val nthAddr = new MonoSortedIFunction("nthAddr", List(Sort.Nat), AddressSort,
    false, false) // todo: part of private API?
  val ObjectADT = new ADT(sortNames, ctorSignatures)
  val ObjectSort = ObjectADT.sorts.head

  /** Create return sort of alloc as an ADT: Heap x Address */
  private val AllocResCtorSignature = ADT.CtorSignature(
    List(("newHeap", ADT.OtherSort(HeapSort)),
      ("newAddress", ADT.OtherSort(AddressSort))), ADT.ADTSort(0))
  private val AllocResADT = new ADT(List("AllocRes"),
    List(("AllocRes", AllocResCtorSignature)))
  val AllocResSort = AllocResADT.sorts.head
  val newHeap = AllocResADT.selectors(0)(0)
  val newAddr = AllocResADT.selectors(0)(1)

  /** Functions and predicates of the theory
   * ***************************************************************************
   * Public functions and predicates
   * ***************************************************************************
   * emptyHeap: ()                   --> Heap
   * alloc    : Heap x Obj           --> Heap x Address (allocRes)
   * read     : Heap x Address       --> Obj
   * write    : Heap x Address x Obj --> Heap
   * isAlloc  : Heap x Address       --> Bool
   * ***************************************************************************
   * Private functions and predicates
   * ***************************************************************************
   * counter  : Heap                 --> Nat
   * nthAddr  : Nat                  --> Address
   * ***************************************************************************
   * */
  val alloc = new MonoSortedIFunction("alloc", List(HeapSort, ObjectSort),
    AllocResSort, false, false)
  val read = new MonoSortedIFunction("read", List(HeapSort, AddressSort),
    ObjectSort, false, false)
  val write = new MonoSortedIFunction("write",
    List(HeapSort, AddressSort, ObjectSort), HeapSort, false, false)
  val isAlloc = new MonoSortedPredicate("isAlloc", List(HeapSort, AddressSort))
  val nullAddr = new MonoSortedIFunction("null", List(), AddressSort,
    false, false)

  val counter = new MonoSortedIFunction("counter", List(HeapSort),
    Sort.Nat, false, false)

  val functions = List(emptyHeap, alloc, read, write,
                       nullAddr,
                       counter, nthAddr)
  val predefPredicates = List(isAlloc)

  private val _defObj : ITerm = defaultObjectCtor(ObjectADT)
  private def _isAlloc(h: ITerm , p: ITerm) : IFormula = {
    import IExpression._
    counter(h) >= p & p > 0
  }

  val triggeredAxioms : IFormula = {
    import IExpression._
    (HeapSort.all(h => AddressSort.all(p => ObjectSort.all(
      o => trig(_isAlloc(h, p) ==> (read(write(h, p, o), p) === o),
        write(h, p, o))))) &

    HeapSort.all(h => AddressSort.all(p1 => ObjectSort.all(o => AddressSort.all(
      p2 => trig(p1 =/= p2 ==> (read(write(h, p1, o), p2) === read(h, p2)),
        read(write(h, p1, o), p2)))))) &

    HeapSort.all(h => AddressSort.all(p => ObjectSort.all(
      o => trig(!_isAlloc(h, p) ==> (write(h, p, o) === h), write(h, p, o))))) &

    HeapSort.all(h => AddressSort.all(p => ObjectSort.all(
      o => trig(counter(write(h, p, o)) === counter(h), write(h, p, o))))) &

    HeapSort.all(h => AddressSort.all(p => trig(
      containFunctionApplications(!_isAlloc(h, p) ==> (read(h, p) === _defObj)),
      read(h, p)))) &

    HeapSort.all(h => ObjectSort.all(o => trig(
      read(newHeap(alloc(h, o)), newAddr(alloc(h, o))) === o,
      alloc(h, o)))) &

    HeapSort.all(h => AddressSort.all(p => ObjectSort.all(o => trig(
      (p =/= newAddr(alloc(h, o))) ==>
      (read(newHeap(alloc(h, o)), p) === read(h, p)),
      read(newHeap(alloc(h, o)), p))))))
  }

  val inductionAxioms : IFormula = {
    import IExpression._
    (
    /* counter(emptyHeap()) === 0 &*/

    HeapSort.all(h => trig(counter(h) >= 0, counter(h))) &

    HeapSort.all(h => ObjectSort.all(o => trig(
      counter(newHeap(alloc(h, o))) === counter(h) + 1 &
      newAddr(alloc(h, o)) === counter(h) + 1, alloc(h, o)))))
  }

  val theoryAxioms = triggeredAxioms & inductionAxioms

  val (funPredicates, axioms1, order, functionTranslation) = Theory.genAxioms(
    theoryFunctions = functions, theoryAxioms = theoryAxioms,
    genTotalityAxioms = false, otherTheories = List(ObjectADT, AllocResADT))

  val predicates = predefPredicates ++ funPredicates
  val functionPredicateMapping = functions zip funPredicates
  private val heapFunPredMap = new MHashMap[IFunction, Predicate]
  functionPredicateMapping.map(m => heapFunPredMap.put(m._1, m._2))

  import ap.terfor.TerForConvenience._
  implicit val o : TermOrder = order
  val axioms2 : Formula =
    forall(Atom(heapFunPredMap(emptyHeap), List(l(v(0))), order) ==>
           Atom(heapFunPredMap(counter), List(l(v(0)), l(0)), order))

  val axioms = Conjunction.conj(List(axioms1, axioms2), order)

  /**
   * Information which of the predicates satisfy the functionality axiom;
   * at some internal points, such predicates can be handled more efficiently
   */
  val functionalPredicates : Set[Predicate] = funPredicates.toSet // todo
  /**
   * Information how interpreted predicates should be handled for
   * e-matching.
   */
  val predicateMatchConfig : Signature.PredicateMatchConfig = Map() // todo
  /**
   * A list of functions that should be considered in automatic trigger
   * generation
   */
  val triggerRelevantFunctions : Set[IFunction] = functions.toSet
  /**
   * Additional axioms that are included if the option
   * <code>+genTotalityAxioms</code> is given to Princess.
   */
  val totalityAxioms : Conjunction = Conjunction.TRUE // todo
  /**
   * Optionally, a plug-in implementing reasoning in this theory
   */
  def plugin : Option[Plugin] = None // todo
  /**
   * Optionally, other theories that this theory depends on.
   */
  override val dependencies : Iterable[Theory] = List(ObjectADT, AllocResADT)

  /**
   * Optionally, a pre-processor that is applied to formulas over this
   * theory, prior to sending the formula to a prover. This method
   * will be applied very early in the translation process.
   */
  override def iPreprocess(f : IFormula,
                           signature : Signature) : (IFormula, Signature) =
    (Preproc.visit(f, ()).asInstanceOf[IFormula], signature)

  private object Preproc extends CollectingVisitor[Unit, IExpression] {
    import IExpression._
    private def isFunAndMatches (e : IExpression, f : IFunction) : Boolean = {
      e match {
        case IFunApp(`f`, _) => true
        case _ => false
      }
    }
    def postVisit(t : IExpression, arg : Unit,
                  subres : Seq[IExpression]) : IExpression = t match {
      case IAtom(`isAlloc`, _) if subres(1) == i(0) => false
      case IAtom(`isAlloc`, _) =>
        _isAlloc(subres(0).asInstanceOf[ITerm], subres(1).asInstanceOf[ITerm])
      case IFunApp(`nullAddr`, _) =>  i(0)
      case IFunApp(`nthAddr`, _) => subres.head // todo: can this even show up?
      case IFunApp(`write`, _) if subres(1) == i(0) => subres(0)
      case IFunApp(`write`, _) if isFunAndMatches(subres(0), emptyHeap) =>
        emptyHeap()
      case IFunApp(`read`, _) if subres(1) == i(0) => _defObj
      case IFunApp(`read`, _) if isFunAndMatches(subres(0), emptyHeap) =>
        _defObj
     /* case IFunApp(`newAddr`, _) if isFunAndMatches(subres(0), alloc) =>
        subres(0).asInstanceOf[IFunApp] match {
          case IFunApp(_, Seq(IFunApp(`emptyHeap`, _), _)) =>  i(1)
          case IFunApp(_, ht) =>
            println(Console.RED_B + t + " -> " + (counter(ht.head) + 1) +Console.RESET )
            counter(ht.head) + 1 // todo: bad idea?
        }*/
      case IFunApp(`counter`, _) if isFunAndMatches(subres(0), newHeap) =>
        subres(0).asInstanceOf[IFunApp] match {
          case IFunApp(_, Seq(IFunApp(`alloc`, Seq(ht, _*)))) =>
            counter(ht) + 1
        }
      case IFunApp(`counter`, _) if isFunAndMatches(subres(0), emptyHeap) =>
        i(0)
      case t =>
        //println(Console.YELLOW_B + t /*+ t.getClass */+ Console.RESET)
        t update subres
    }
  }
  /**
   * Optionally, a pre-processor that is applied to formulas over this
   * theory, prior to sending the formula to a prover.
   */

  /*override def preprocess(f : Conjunction,
                          order : TermOrder) : Conjunction = {
    println
    println("Preprocessing:")
    println(f) //println(Console.YELLOW_B + f.quans + Console.RESET)
    val reducerSettings = Param.FUNCTIONAL_PREDICATES.set(ReducerSettings.DEFAULT,
      functionalPredicates)
    val after = ReduceWithConjunction(Conjunction.TRUE, order, reducerSettings)(
      f)
    println(" -> " + after)
    println
    after
  }*/

  /* def preprocess(f : Conjunction, order : TermOrder) : Conjunction = f // todo
  */
  /**
   * Optionally, a plugin for the reducer applied to formulas both before
   * and during proving.
   */
  // val reducerPlugin : ReducerPluginFactory = IdentityReducerPluginFactory // todo
  /**
   * Optionally, a function evaluating theory functions applied to concrete
   * arguments, represented as constructor terms.
   */
  // def evalFun(f : IFunApp) : Option[ITerm] = None // todo
  /**
   * Optionally, a function evaluating theory predicates applied to concrete
   * arguments, represented as constructor terms.
   */
  // def evalPred(p : IAtom) : Option[Boolean] = None // todo
  /**
   * If this theory defines any <code>Theory.Decoder</code>, which
   * can translate model data into some theory-specific representation,
   * this function can be overridden to pre-compute required data
   * from a model.
   */
  /* def generateDecoderData(model : Conjunction)
  : Option[Theory.TheoryDecoderData] =
    None */
  // todo
  /**
   * Check whether we can tell that the given combination of theories is
   * sound for checking satisfiability of a problem, i.e., if proof construction
   * ends up in a dead end, can it be concluded that a problem is satisfiable.
   */
  override def isSoundForSat( // todo
                  theories : Seq[Theory],
                  config : Theory.SatSoundnessConfig.Value) : Boolean =
    config match {
      case Theory.SatSoundnessConfig.Elementary  => true
      case Theory.SatSoundnessConfig.Existential => true
      case _                                     => false
    }

  TheoryRegistry register this
  override def toString = "HeapTheory"
}
