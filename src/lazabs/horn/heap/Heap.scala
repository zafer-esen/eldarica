package lazabs.horn.heap

import ap.basetypes.IdealInt
import ap.{Signature, types}
import ap.parser._
import ap.types._
import ap.proof.theoryPlugins.Plugin
import ap.terfor.TermOrder
import ap.terfor.conjunctions.Conjunction
import ap.theories._
import ap.theories.ADT
import ap.types.{MonoSortedIFunction, Sort}
import ap.util.Debug

import scala.collection.mutable

object Heap {
  private val AC = Debug.AC_ADT // todo
  abstract sealed class CtorArgSort
  case class ADTSort(num : Int) extends CtorArgSort
  case class OtherSort(sort : Sort) extends CtorArgSort
  case class CtorSignature(arguments : Seq[(String, CtorArgSort)],
                           result : ADTSort)

  class HeapException(m : String) extends Exception(m)

  /** implicit converters from Heap.CtorArgSort to ADT.CtorArgSort */
  private implicit def HeapSortToADTSort(s : CtorArgSort) : ADT.CtorArgSort =
    s match {
      case t : ADTSort => ADT.ADTSort(t.num)
      case t : OtherSort => ADT.OtherSort(t.sort)
  }

  private implicit def HeapSortToADTSort(l : Seq[(String, Heap.CtorSignature)]):
  Seq[(String, ADT.CtorSignature)] = {
    for (s <- l) yield (s._1, ADT.CtorSignature(
      for (arg <- s._2.arguments) yield (arg._1, HeapSortToADTSort(arg._2)),
      ADT.ADTSort(s._2.result.num)))
  }
}

/** first sort in sortNames should be the object sort *
 *
 * @param heapSortName
 * @param addressSortName
 * @param objectSort
 * @param sortNames
 * @param ctorSignatures
 */
class Heap(heapSortName : String, addressSortName : String,
           objectSort : Heap.ADTSort, sortNames : Seq[String],
           ctorSignatures : Seq[(String, Heap.CtorSignature)])
    extends Theory {
  import Heap._
  //-BEGIN-ASSERTION-///////////////////////////////////////////////////////////
  Debug.assertCtor(AC, // todo: redundant with the one in ADT or have it here too?
    ctorSignatures forall {
      case (_, sig) =>
        ((sig.arguments map (_._2)) ++ List(sig.result)) forall {
          case Heap.ADTSort(id)   => id >= 0 && id < sortNames.size
          case _ : OtherSort => true
        }
    })
  //-END-ASSERTION-/////////////////////////////////////////////////////////////
  private val ObjectADT = new ADT(sortNames, ctorSignatures)

  val HeapSort = Sort.createInfUninterpretedSort(heapSortName)
  val AddressSort = Sort.createInfUninterpretedSort(addressSortName) //todo: nat?
  val ObjectSort = ObjectADT.sorts.head

  /** A mapping of ctor names to ctors (for ObjectADT) for convenience*/
  val ctrMap : Map[String, MonoSortedIFunction] =
    ObjectADT.constructors.map(c => c.name -> c).toMap
  /** A mapping of (ctorName, selName) to selectors (for ObjectADT)*/
  val selMap : Map[(String, String), MonoSortedIFunction] =
    (for(cid <- ObjectADT.constructors.indices; sel <- ObjectADT.selectors(cid))
      yield (ObjectADT.constructors(cid).name, sel.name) -> sel).toMap

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
   * emptyHeap: ()                   --> Heap
   * alloc    : Heap x Obj           --> Heap x Address (allocRes)
   * read     : Heap x Address       --> Obj
   * write    : Heap x Address x Obj --> Heap
   * isAlloc  : Heap x Address       --> Bool
   *
   * counter  : Heap                 --> Nat
   * */
  val emptyHeap = new MonoSortedIFunction("emptyHeap", argSorts = List(),
    resSort = HeapSort, _partial = false, _relational = false)
  val alloc = new MonoSortedIFunction("alloc", List(HeapSort, ObjectSort),
    AllocResSort, false, false)
  val read = new MonoSortedIFunction("read", List(HeapSort, AddressSort),
    ObjectSort, false, false)
  val write = new MonoSortedIFunction("write",
    List(HeapSort, AddressSort, ObjectSort), HeapSort, false, false)
  private val counter = new MonoSortedIFunction("counter", List(HeapSort),
    Sort.Nat, false, false)
  val isAlloc = new MonoSortedPredicate("isAlloc", List(HeapSort, AddressSort))

  val functions = List(emptyHeap, alloc, read, write, counter,
    newHeap, newAddr)
  val predefPredicates = List(isAlloc)

  import IExpression._

  val detObj = ObjectSort.newConstant("detObj")

  private def _isAlloc(h: ITerm , p: ITerm) : IFormula =
    counter(h) >= p & p > 0

  val triggeredAxioms = (
    HeapSort.all(h => AddressSort.all(p => ObjectSort.all(o => trig(
      _isAlloc(h, p) ==> (read(write(h, p, o), p) === o),
      read(write(h, p, o), p))))) &

    HeapSort.all(h => AddressSort.all(p1 => ObjectSort.all(o =>
      AddressSort.all(p2 => trig(
        _isAlloc(h, p1) & _isAlloc(h, p2) ==>
                          (read(write(h, p1, o), p2) === read(h, p2)),
        read(write(h, p1, o), p2)))))) &

    HeapSort.all(h => AddressSort.all(p => ObjectSort.all(o => trig(
      _isAlloc(h, p) ==> (counter(write(h, p, o)) === counter(h)),
      counter(write(h, p, o)))))) &

    HeapSort.all(h => AddressSort.all(p => trig(
      !_isAlloc(h, p) ==> (read(h, p) === detObj),
      read(h, p)))) &

    HeapSort.all(h => AddressSort.all(p => ObjectSort.all(o => trig(
      !_isAlloc(h, p) ==> (write(h, p, o) === emptyHeap()),
      write(h, p, o))))) &

    HeapSort.all(h => ObjectSort.all(o => trig(
      read(newHeap(alloc(h, o)), newAddr(alloc(h, o))) === o,
      read(newHeap(alloc(h, o)), newAddr(alloc(h, o)))))) &

    HeapSort.all(h => AddressSort.all(p => ObjectSort.all(o => trig(
      (p =/= newAddr(alloc(h, o))) ==>
        (read(newHeap(alloc(h, o)), p) === read(h, p)),
      read(newHeap(alloc(h, o)), p))))))

  val inductionAxioms = (
    counter(emptyHeap()) === 0 &

    HeapSort.all(
      h => counter(h) >= 0 ) & HeapSort.all(h => ObjectSort.all(o => (
      counter(newHeap(alloc(h, o))) === counter(h) + 1 &
      newAddr(alloc(h, o)) === counter(h) + 1))))

  val theoryAxioms = triggeredAxioms & inductionAxioms

  val (funPredicates, axioms, _, functionTranslation) = Theory.genAxioms(
    theoryFunctions = functions, theoryAxioms = theoryAxioms,
    genTotalityAxioms = false,
    order = TermOrder.EMPTY.extendPred(isAlloc).extend(detObj))
  val f = funPredicates.toArray
  val predicates = predefPredicates ++ funPredicates
  val functionPredicateMapping = functions zip funPredicates

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
  override val dependencies : Iterable[Theory] = List()

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
      case IAtom(`isAlloc`, Seq(h, p)) =>
        _isAlloc(h, p)/*
      case IFunApp(`counter`,
      Seq(IFunApp(`newHeap`, Seq(IFunApp(`alloc`, Seq(h, _)))))) =>
        counter(h) + 1
      case IFunApp(`newAddr`, Seq(IFunApp(`alloc`, Seq(h, _)))) =>
        counter(h) + 1*/
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
  override def isSoundForSat(theories : Seq[Theory],
                             config : Theory.SatSoundnessConfig.Value) = true
  // todo

  TheoryRegistry register this
  override def toString = "HeapTheory"
}
