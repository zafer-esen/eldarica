package lazabs.horn.heap

import ap.basetypes.IdealInt
import ap.parser.IExpression.Predicate
import ap.{Signature, theories}
import ap.parser._
import ap.types._
import ap.proof.theoryPlugins.Plugin
import ap.terfor.TermOrder
import ap.terfor.conjunctions.Conjunction
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

      /** Collect the relevant functions and predicates of the theory */
      import heapTheory.{read, emptyHeap, counter, alloc}
      val readAtoms = getAtoms(read)
      val counterAtoms = getAtoms(counter)
      val emptyHeapAtoms = getAtoms(emptyHeap)
      val allocAtoms = getAtoms(alloc)


      /*val allocResCtorPred = heapTheory.AllocResADT.constructorPreds.head
      val allocResCtor = heapTheory.AllocResADT.constructors.head
      val allocResAtoms = model.predConj positiveLitsWithPred allocResCtorPred*/
      /**
       *  Helper function to get the counter value of a given heap term.
       *  @return counter : Int
       */
      def getCounterVal (heapTerm : ITerm) : Int = {
        counterAtoms.find(a =>
          getSubTerms(a.init, heapTheory.counter.argSorts, terms) match {
            case Left(args) if args.head == heapTerm => true
            case _ => false
          }) match {
          case Some(a) => a.last.constant.intValue
          case None => -1
        }
      }
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

      /** Replace empty heap terms. */
    /*  for (a <- emptyHeapAtoms) {
        val key = (a.last.constant, this)
        if(!(terms contains key))
          terms.put(key, emptyHeap())
      }*/

      /**
       * Look at read predicates and define the heap terms in the model.
       * This part turns the representation of heap terms in the model from
       * integer values to actual terms (like newHeap(alloc(emptyHeap, 42)) )
       */
      println(Console.BLUE + model + Console.RESET + "\n")
      for (a <- readAtoms if terms contains(a.last.constant, read.resSort)) {
        val resTerm : ITerm = terms getOrElse
                              ((a.last.constant, read.resSort), -1)
        if(resTerm != IIntLit(-1)) {
          getSubTerms(a.init, read.argSorts, terms) match {
            case Left(argTerms) if !argTerms.head.isInstanceOf[IFunApp] =>
              val key = (a.head.constant, this)
              if(argTerms.length == 2) {
                val counterVal = argTerms(1) match {
                  case IFunApp(heapTheory.nthAddr, Seq(IIntLit(n))) => n.intValue
                  case _ => -1
                }
                if (counterVal >= 0) {
                  val newTerm = createHeapTerm(counterVal, resTerm)
                  if (!(definedTerms contains key)) {
                    terms.put(key, newTerm)
                    definedTerms += key
                  }
                }
              }
            case _ =>
          }
        }
      }
     /* for (a <- allocAtoms if terms contains(a.last.constant, alloc.resSort)) {
        getSubTerms(a.init, alloc.argSorts, terms) match {
          case Left(argTerms) => val key = (a.last.constant, alloc.resSort)
            println(Console.MAGENTA_B + argTerms + Console.RESET)
            val resTerm = terms.getOrElse(key, -1)
            println(Console.BLUE_B + resTerm + Console.RESET)
            val allocResCtr = heapTheory.AllocResADT.constructors.head
            resTerm match {
              case IFunApp(allocresCtr, Seq(IIntLit(hid),
              IFunApp(heapTheory.nthAddr,
              Seq(IIntLit(n))))) =>
                println(Console.BLUE_B + resTerm + Console.RESET)
                val newHeapTerm = createHeapTerm(n.intValue + 1, argTerms.last)
                val newHeapKey = (hid, this)
                println(Console.BLUE_B + resTerm + Console.RESET)
                if (!(definedTerms contains newHeapKey)) {
                  terms.put(newHeapKey, newHeapTerm)
                  definedTerms += newHeapKey
                }
              /*case IFunApp(allocResCtr, Seq(heapTerm,
              IFunApp(heapTheory.nthAddr, Seq(IIntLit(n))))) => println(
                Console.RED + "newHeap(" + args + Console.RESET)
                if (!(definedTerms contains newHeapKey)) {
                  terms.put(newHeapKey, heapTerm)
                  definedTerms += newHeapKey
                }*/
              case _ =>
            }
        }
      }*/

      /*for (a <- allocResAtoms) {
        val key = (a.last.constant, allocResCtor.resSort)
        if(!(definedTerms contains key)) {
          val term : ITerm = terms getOrElse(key, -1)
          if (term != IIntLit(-1)) {
            val heapKey = (a.head.constant, this)
            if (definedTerms contains heapKey) {
              val heapTerm : ITerm = terms.getOrElse(heapKey, -1)
              val addrTerm : ITerm = term match {
                case IFunApp(allocResCtor, Seq(_, t)) => t
                case _ => -1
              }
              if(addrTerm != IIntLit(-1)) {
                val newTerm = allocResCtor(heapTerm, addrTerm)
                terms.put(key, newTerm)
                definedTerms += key
              }
            }
          }
        }
      }*/
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

  // todo: what about writing a sort other than ObjectSort to the heap?
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
      counter(write(h, p, o)))))) &

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
