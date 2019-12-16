package lazabs.horn.heap

import ap.basetypes.IdealInt
import ap.parser.IExpression.Predicate
import ap.{Signature, theories}
import ap.parser._
import ap.types._
import ap.proof.theoryPlugins.Plugin
import ap.terfor.TermOrder
import ap.terfor.conjunctions.Conjunction
import ap.terfor.linearcombination.LinearCombination
import ap.terfor.preds.Atom
import ap.theories._
import ap.theories.ADT
import ap.types.{MonoSortedIFunction, Sort}
import ap.util.Debug

import scala.collection.mutable.{ArrayBuffer, ArrayStack, LinkedHashMap, HashMap => MHashMap, HashSet => MHashSet}
import scala.collection.{mutable, Map => GMap}
import scala.collection.mutable.{Map => MMap, Set => MSet}

object Heap {
  private val AC = Debug.AC_ADT // todo
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
    import IExpression._

    override val name = sortName
    override def decodeToTerm(
                 d : IdealInt,
                 assignment : GMap[(IdealInt, Sort), ITerm]) : Option[ITerm] =
      Some(heapTheory.nthAddr(d.intValue))

   // override individuals : Stream[ITerm] = for (t <- Sort.Nat.individuals) yield nthAddr(t)
  }

  class HeapSort(sortName : String,
                 heapTheory : Heap) extends ProxySort(Sort.Nat) {
    import IExpression._

    override val name = sortName
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
      import heapTheory.{read, emptyHeap, counter, alloc}
      val readAtoms = getAtoms(read)
      val counterAtoms = getAtoms(counter)
      val emptyHeapAtoms = getAtoms(emptyHeap)
      val allocAtoms = getAtoms(alloc)

      /*val allocResCtorPred = heapTheory.AllocResADT.constructorPreds.head
      val allocResCtor = heapTheory.AllocResADT.constructors.head
      val allocResAtoms = model.predConj positiveLitsWithPred allocResCtorPred*/

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
  Debug.assertCtor(AC, // todo: redundant with the one in ADT or have it here too?
    ctorSignatures forall {
      case (_, sig) =>
        ((sig.arguments map (_._2)) ++ List(sig.result)) forall {
          case Heap.ADTSort(id) => id >= 0 && id < sortNames.size
          case _ : OtherSort => true
          case Heap.AddressSort => true
        }
    })
  //-END-ASSERTION-/////////////////////////////////////////////////////////////

  val ObjectADT = new ADT(sortNames, ctorSignatures)


  // todo: good first approx.
  // start with the AddressSort
  // change it to a proxy sort underlying: Nat => Addr
  // Numbers to Terms (nthAddr)
  val HeapSort = new HeapSort(heapSortName, this)
  val AddressSort = new Address(addressSortName, this)
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
   * nthAddr  : Nat                  --> Nat
   * ***************************************************************************
   * */
  val emptyHeap = new MonoSortedIFunction("emptyHeap", argSorts = List(),
    resSort = HeapSort, _partial = false, _relational = false)
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
  val nthAddr = new MonoSortedIFunction("nthAddr", List(Sort.Nat), Sort.Nat,
    false, false) // todo: part of private API?

  val functions = List(emptyHeap, alloc, read, write,
                       nullAddr,
                       counter, nthAddr)
  val predefPredicates = List(isAlloc)

  import IExpression._

  private val _defObj : ITerm = defaultObjectCtor(ObjectADT)
  private def _isAlloc(h: ITerm , p: ITerm) : IFormula =
    counter(h) >= p & p > 0

  val triggeredAxioms = (
    HeapSort.all(h => AddressSort.all(p => ObjectSort.all(o => trig(
      _isAlloc(h, p) ==> (read(write(h, p, o), p) === o),
      write(h, p, o))))) &

    HeapSort.all(h => AddressSort.all(p1 => ObjectSort.all(o =>
      AddressSort.all(p2 => trig(
        _isAlloc(h, p1) & _isAlloc(h, p2) & p1 =/= p2 ==>
                          (read(write(h, p1, o), p2) === read(h, p2)),
        read(write(h, p1, o), p2)))))) &

    HeapSort.all(h => AddressSort.all(p => ObjectSort.all(o => trig(
      _isAlloc(h, p) ==> (counter(write(h, p, o)) === counter(h)),
      write(h, p, o))))) &

    HeapSort.all(h => AddressSort.all(p => trig(
      !_isAlloc(h, p) ==> (read(h, p) === _defObj),
      read(h, p)))) &

    HeapSort.all(h => AddressSort.all(p => ObjectSort.all(o => trig(
      !_isAlloc(h, p) ==> (write(h, p, o) === emptyHeap()),
      write(h, p, o))))) &

    HeapSort.all(h => ObjectSort.all(o => trig(
      read(newHeap(alloc(h, o)), newAddr(alloc(h, o))) === o,
      alloc(h, o)))) &

    HeapSort.all(h => AddressSort.all(p => ObjectSort.all(o => trig(
      (p =/= newAddr(alloc(h, o))) ==>
        (read(newHeap(alloc(h, o)), p) === read(h, p)),
      read(newHeap(alloc(h, o)), p))))))

  val inductionAxioms = (
    counter(emptyHeap()) === 0 &
    //HeapSort.all(h => trig(
    //  (counter(h) > 0) <=> (h =/= emptyHeap()), counter(h))) &

    HeapSort.all(h => trig(
      counter(h) >= 0,
      counter(h))) &

    HeapSort.all(h => ObjectSort.all(o => trig(
      counter(newHeap(alloc(h, o))) === counter(h) + 1 &
        newAddr(alloc(h, o)) === counter(h) + 1,
      alloc(h, o)))))

  val theoryAxioms = triggeredAxioms & inductionAxioms

  val (funPredicates, axioms, _, functionTranslation) = Theory.genAxioms(
    theoryFunctions = functions, theoryAxioms = theoryAxioms,
    genTotalityAxioms = false, otherTheories = List(ObjectADT, AllocResADT))
  val predicates = predefPredicates ++ funPredicates
  val functionPredicateMapping = functions zip funPredicates
  private val heapFunPredMap = new MHashMap[IFunction, Predicate]
  functionPredicateMapping.map(m => heapFunPredMap.put(m._1, m._2))

  /**
   * Information which of the predicates satisfy the functionality axiom;
   * at some internal points, such predicates can be handled more efficiently
   */
  val functionalPredicates = funPredicates.toSet // todo
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
  val totalityAxioms = Conjunction.TRUE // todo
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
  override def iPreprocess(f : IFormula, signature : Signature) = // todo
    (Preproc.visit(f, ()).asInstanceOf[IFormula], signature)

  private object Preproc extends CollectingVisitor[Unit, IExpression] {
    def postVisit(t : IExpression, arg : Unit,
                  subres : Seq[IExpression]) : IExpression = t match {
      case IAtom(`isAlloc`, Seq(_, IFunApp(`nullAddr`, _))) => false
      case IAtom(`isAlloc`, Seq(h, p)) =>
        _isAlloc(h, p)
      case IFunApp(`nullAddr`, _) => 0 // todo do these cases make sense?
      case IFunApp(`nthAddr`, Seq(n)) => n
      case IFunApp(`write`, Seq(_, IFunApp(`nullAddr`, _), _)) => emptyHeap()
      case IFunApp(`read`, Seq(_, IFunApp(`nullAddr`, _))) => _defObj
      case t => //println("preprocess: " + t + " " + t.getClass)
        t update subres
    }
  }
  /**
   * Optionally, a pre-processor that is applied to formulas over this
   * theory, prior to sending the formula to a prover.
   */
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
