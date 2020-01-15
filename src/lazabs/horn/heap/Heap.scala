package lazabs.horn.heap

import ap.basetypes._
import ap.parser._
import ap.theories.{ADT, Theory, TheoryRegistry}
import ap.types.{MonoSortedIFunction, Sort, _}
import ap.util.Debug
import lazabs.ast.ASTree.Disjunction

import scala.collection.mutable.{HashMap => MHashMap, Map => MMap, Set => MSet}
import scala.collection.{Map => GMap}

object Heap {
  private val AC = Debug.AC_ADT
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
    import ap.terfor.conjunctions.Conjunction
    import ap.terfor.preds.Atom
    import heapTheory.{ObjectSort, alloc, emptyHeap, newHeap}
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
      import heapTheory.{counter, emptyHeap, read}
      val readAtoms = getAtoms(read)
      val counterAtoms = getAtoms(counter)
      val emptyHeapAtoms = getAtoms(emptyHeap)

      import IExpression.{i, toFunApplier}
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
        import heapTheory.{_defObj, alloc, newHeap}
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
  Debug.assertCtor(AC,
    ctorSignatures forall {
      case (_, sig) =>
        ((sig.arguments map (_._2)) ++ List(sig.result)) forall {
          case Heap.ADTSort(id) => id >= 0 && id < sortNames.size
          case _ : OtherSort => true
          case Heap.AddressSort => true
        }
    })
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
   * nthAddr  : Nat                  --> Address
   * ***************************************************************************
   * Private functions and predicates
   * ***************************************************************************
   * counter  : Heap                 --> Nat
   *
   * * Below two functions are shorthand functions to get rid of allocRes ADT.
   * * They return a single value instead of the pair <Heap x Addr>.
   * * This is done to get rid of quantifiers related to the ADT in the
   * * generated interpolants.
   * allocHeap: Heap x Obj           --> Heap
   * allocAddr: Heap x Obj           --> Addr
   *
   * * allocAddr is further removed by reducing it to counter(h) + 1
   * ***************************************************************************
   * */
  val alloc = new MonoSortedIFunction("alloc", List(HeapSort, ObjectSort),
    AllocResSort, false, false)
  val allocHeap = new MonoSortedIFunction("allocHeap",
    List(HeapSort, ObjectSort), HeapSort, false, false)

  val read = new MonoSortedIFunction("read", List(HeapSort, AddressSort),
    ObjectSort, false, false)
  val write = new MonoSortedIFunction("write",
    List(HeapSort, AddressSort, ObjectSort), HeapSort, false, false)
  val isAlloc = new MonoSortedPredicate("isAlloc", List(HeapSort, AddressSort))
  val nullAddr = new MonoSortedIFunction("null", List(), AddressSort,
    false, false)

  val counter = new MonoSortedIFunction("counter", List(HeapSort),
    Sort.Nat, false, false)

  val functions = List(emptyHeap, alloc, allocHeap, /*allocAddr,*/ read, write,
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
      read(allocHeap(h, o), counter(h)+1) === o,
      allocHeap(h, o), counter(h)+1))) &

    HeapSort.all(h => AddressSort.all(p => ObjectSort.all(o => trig(
      (p =/= counter(h)+1) ==>
      (read(allocHeap(h, o), p) === read(h, p)),
      read(allocHeap(h, o), p))))))
  }

  val inductionAxioms : IFormula = {
    import IExpression._
    (
    HeapSort.all(h => trig(counter(h) >= 0, counter(h))) & // todo: why removing this fails some test cases? counter resType is Nat.

    HeapSort.all(h => ObjectSort.all(o => trig(
      counter(allocHeap(h, o)) === counter(h) + 1,
      allocHeap(h, o))))
    )
  }

  val theoryAxioms = triggeredAxioms & inductionAxioms

  val (funPredicates, axioms1, order, functionTranslation) = Theory.genAxioms(
    theoryFunctions = functions, theoryAxioms = theoryAxioms,
    genTotalityAxioms = false, otherTheories = List(ObjectADT, AllocResADT))

  val predicates = predefPredicates ++ funPredicates
  val functionPredicateMapping = functions zip funPredicates
  import IExpression.Predicate
  private val heapFunPredMap = new MHashMap[IFunction, Predicate]
  functionPredicateMapping.map(m => heapFunPredMap.put(m._1, m._2))

  import ap.terfor.TerForConvenience._
  import ap.terfor.conjunctions.Conjunction
  import ap.terfor.preds.Atom
  import ap.terfor.{Formula, TermOrder}
  val axioms2 : Formula = {
    implicit val o : TermOrder = order
    forall(Atom(heapFunPredMap(emptyHeap), List(l(v(0))), order) ==>
           Atom(heapFunPredMap(counter), List(l(v(0)), l(0)), order))
  }

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
  import ap.Signature
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
  import ap.proof.goal.Goal
  import ap.proof.theoryPlugins.Plugin
  def plugin: Option[Plugin] = Some(new Plugin {
      def generateAxioms(goal : Goal) : Option[(Conjunction, Conjunction)] =
        None

      override def handleGoal(goal : Goal) : Seq[Plugin.Action] = {
        import goal.facts.arithConj.negativeEqs
        import goal.facts.predConj.positiveLitsWithPred
        val counterLits = positiveLitsWithPred(heapFunPredMap(counter))
        val emptyHeapTerms =
          for (l <- positiveLitsWithPred(heapFunPredMap(emptyHeap)))
            yield l.head.head._2

        import ap.terfor.TerForConvenience._
        import ap.terfor.linearcombination.{LinearCombination => LC}
        import ap.terfor.Term
        import scala.collection.mutable.ArrayBuffer
        val neqTermArr = /* (neq, (h1, h2, c1, c2)) */
          new ArrayBuffer[(LC, (Term, Term, LC, LC))]
        for (neq <- negativeEqs) {
          val (lhs : Term, rhs : Term) = (neq(0)._2, neq(1)._2)
          if (!emptyHeapTerms.contains(lhs) && !emptyHeapTerms.contains(rhs)) {
            counterLits.find(a => a.head.head._2 == lhs) match {
              case Some(l1) =>
                val lhsCounterTerm : LC = l1.last
                val rhsCounterTerm : LC =
                  counterLits.find(a1 => a1.head.head._2 == rhs) match {
                  case Some(l2) => l2.last
                  case None =>
                    println(Console.MAGENTA_B + goal.facts + Console.RESET)
                    println(Console.RED_B + neq + Console.RESET)
                    throw new HeapException(
                    "Second counter lit " + "not found!")
                }
                neqTermArr += ((neq, (lhs, rhs, lhsCounterTerm, rhsCounterTerm)))
              case None =>
            }
          }
        }

        implicit val to = goal.order
        val (neqsToRemove, neqsToAdd) =
          (for ((neq, (h1, h2, c1, c2)) <- neqTermArr) yield {
            import ap.terfor.TerForConvenience.{l, v}
            val readPred : Predicate = heapFunPredMap(read)
            val neqToAdd : Formula =  disjFor(c1 =/= c2,
                exists(exists(exists(
                c1 >= v(2) & v(2) > 0 & // isAlloc(h1, v(2))
                Atom(readPred, List(l(h1), l(v(2)), l(v(1))), goal.order) &
                Atom(readPred, List(l(h2), l(v(2)), l(v(0))), goal.order) &
                l(v(0)) =/= l(v(1))
              ))))
            (neq, neqToAdd)}).unzip

        if (neqsToRemove.isEmpty) {
          List()
        } else {
          List(
            Plugin.RemoveFacts(
              ap.terfor.equations.NegEquationConj(neqsToRemove, goal.order)),
            Plugin.AddAxiom(List(), conj(neqsToAdd), Heap.this)
          )
        }
      }
    })

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
      case IFunApp(`counter`, _) if isFunAndMatches(subres(0), emptyHeap) =>
        i(0)
      case IFunApp(`alloc`, _) =>
        val h = subres(0).asInstanceOf[ITerm]
        val o = subres(1).asInstanceOf[ITerm]
        AllocResADT.constructors.head(allocHeap(h, o), counter(h)+1)
      case IFunApp(`newHeap`, _) if isFunAndMatches(subres(0), alloc) =>
        val Seq(h, o) = subres(0).asInstanceOf[IFunApp].args
        allocHeap(h, o)
      case IFunApp(`newAddr`, _) if isFunAndMatches(subres(0), alloc) =>
        val Seq(h, _) = subres(0).asInstanceOf[IFunApp].args
        counter(h) + 1
      case t =>
        /*println(Console.YELLOW_B + t + Console.GREEN_B + " " +
                t.getClass + Console.RESET)
        println(Console.BLUE_B + subres + Console.RESET)*/
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
