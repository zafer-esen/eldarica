package lazabs.horn

import ap.Signature
import ap.parser._
import ap.types._
import ap.proof.theoryPlugins.Plugin
import ap.terfor.conjunctions.Conjunction
import ap.theories._
import ap.theories.ADT
import ap.types.{MonoSortedIFunction, Sort}
import ap.util.Debug
import lazabs.horn.bottomup.HornClauses

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



object Main extends App {
  val heap = new Heap("MyHeap", "MyAddress", Heap.ADTSort(0),
      List("HeapObject", "struct_S"),
      List(("WrappedInt", Heap.CtorSignature(List(("getInt",Heap.OtherSort(Sort.Integer))), Heap.ADTSort(0))),
           ("WrappedS",   Heap.CtorSignature(List(("getS", Heap.ADTSort(1))), Heap.ADTSort(0))),
           ("struct_S",   Heap.CtorSignature(List(("x", Heap.OtherSort(Sort.Integer))), Heap.ADTSort(1)))))
  val WrappedInt = heap.ObjectADT.constructors(0)
  val GetInt = heap.ObjectADT.selectors(0).head
  val GetS   = heap.ObjectADT.selectors(1).head
  val Sel_Sx  = heap.ObjectADT.selectors(2).head
  val WrappedS = heap.ObjectADT.constructors(1)
  val struct_S = heap.ObjectADT.constructors(2)

  println("Program:")
  println("--------")
  val progList = List(
    "  int *p = calloc(int); ",
    "  *p = 42; ",
    "  struct S* ps = calloc(struct S); ",
    "  ps->x = *p; ",
    "  assert(ps->x == 42); ",
    ""
  )
  progList.foreach(println)

  import ap.parser.IExpression._
  import HornClauses._
  val I0 = new Predicate("I0", 1)
  val I1 = new Predicate("I1", 2)
  val I2 = new Predicate("I2", 2)
  val I3 = new Predicate("I3", 3)
  val I4 = new Predicate("I4", 3)
  val I5 = new Predicate("I5", 3)

  val h = new ConstantTerm("h")
  val h1 = new ConstantTerm("h'")
  val p = new ConstantTerm("p")
  val ps = new ConstantTerm("ps")
  val ar = new ConstantTerm("ar") // heap alloc res
  val o = new ConstantTerm("o") // heap object

  val clauses1 = List(
    I0 (h) :- heap.emptyHeap(h),
    I1 (heap.newHeap(ar), heap.newAddr(ar))  :-
      (I0(h), heap.alloc(h, WrappedInt(0), ar)),
    I2(h1, p) :- (I1(h, p), heap.write(h, p, WrappedInt(42), h1)),
    I3(heap.newHeap(ar), p, heap.newAddr(ar)) :-
      (I2(h, p), heap.alloc(h, WrappedS(struct_S(0)), ar)),
    I4(h1, p, ps) :- (I3(h, p, ps), heap.read(h, p, o),
      heap.write(h, ps, WrappedS(struct_S(GetInt(o))), h1)),
    I5(h, p, ps) :- I4(h, p, ps),
    false :- (I4(h, p, ps), heap.read(h, ps, o), Sel_Sx(GetS(o)) === 42)
  )
  println("Clauses:")
  println("--------")
  for(c <- clauses1) println("  " ++ c.toPrologString)
  println
}

/** first sort in sortNames should be the object sort */
class Heap(heapSortName: String, addressSortName: String, objectSort: Heap.ADTSort,
           sortNames : Seq[String],
           ctorSignatures : Seq[(String, Heap.CtorSignature)]) extends Theory {
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
  val ObjectADT = new ADT(sortNames, ctorSignatures)

  val HeapSort = Sort.createInfUninterpretedSort(heapSortName)
  val AddressSort = Sort.createInfUninterpretedSort(addressSortName) //todo: nat?
  val ObjectSort = ObjectADT.sorts.head

  /** Create return sort of alloc as an ADT: Heap x Address */
  val AllocResCtorSignature = ADT.CtorSignature(
    List(("newHeap", ADT.OtherSort(HeapSort)),
         ("newAddress", ADT.OtherSort(AddressSort))), ADT.ADTSort(0))
  val AllocResADT = new ADT(List("AllocRes"),
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
   * */
  val emptyHeapFun = new MonoSortedIFunction("emptyHeap", argSorts = List(),
    resSort = HeapSort, _partial = false, _relational = false)
  val allocFun = new MonoSortedIFunction("alloc", List(HeapSort, ObjectSort),
    AllocResSort, false, false)
  val readFun = new MonoSortedIFunction("read", List(HeapSort, AddressSort),
    ObjectSort, false, false)
  val writeFun = new MonoSortedIFunction("write",
    List(HeapSort, AddressSort, ObjectSort), HeapSort, false, false)
  val isAlloc = new MonoSortedPredicate("isAlloc", List(HeapSort, AddressSort))

  val functions = List(emptyHeapFun, allocFun, readFun, writeFun)
  val predefPredicates = List(isAlloc)
  val (funPredicates, axioms, _, functionTranslation) = Theory
    .genAxioms(theoryFunctions = functions)
  val f = funPredicates.toArray
  val (emptyHeap, alloc, read, write) = (f(0), f(1), f(2), f(3)) // todo: a better way?


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
  val triggerRelevantFunctions : Set[IFunction] = Set() // todo: any triggers?
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
  override val dependencies : Iterable[Theory] = List() // todo: theory of ADTs?
  /**
   * Optionally, a pre-processor that is applied to formulas over this
   * theory, prior to sending the formula to a prover. This method
   * will be applied very early in the translation process.
   */
  /* def iPreprocess(f : IFormula, signature : Signature) // todo
  : (IFormula, Signature) =
    (f, signature) */
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
  /* def isSoundForSat(theories : Seq[Theory],
                    config : Theory.SatSoundnessConfig.Value) : Boolean = false*/
  // todo
}
