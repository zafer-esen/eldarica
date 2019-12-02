package lazabs.horn

import ap.Signature
import ap.parser._
import ap.types._
import ap.proof.theoryPlugins.Plugin
import ap.terfor.TermOrder
import ap.terfor.conjunctions.Conjunction
import ap.theories._
import ap.theories.ADT
import ap.types.{MonoSortedIFunction, Sort}
import ap.util.Debug
import lazabs.horn.abstractions.VerificationHints
import lazabs.horn.bottomup.HornClauses
import lazabs.horn.concurrency.ParametricEncoder.{Infinite, NoSync, NoTime, System}
import lazabs.horn.concurrency.{ParametricEncoder, VerificationLoop}

import scala.collection.immutable
import scala.collection.immutable.HashMap

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
  val NullObjName = "NullObj"
  val ObjSort = Heap.ADTSort(0)
  val StructSSort = Heap.ADTSort(1)
  val heap = new Heap("MyHeap", "MyAddress", ObjSort, NullObjName,
    List("HeapObject", "struct_S"), List(
      (NullObjName, Heap.CtorSignature(List(), ObjSort)),
      ("WrappedInt", Heap.CtorSignature(List(("getInt", Heap.OtherSort(Sort.Integer))), ObjSort)),
      ("WrappedS", Heap.CtorSignature(List(("getS", StructSSort)), ObjSort)),
      ("struct_S", Heap.CtorSignature(List(("x", Heap.OtherSort(Sort.Integer))),
        StructSSort))))

  val wrappedInt = heap.ctrMap("WrappedInt")
  val getInt = heap.selMap("WrappedInt", "getInt")
  val wrappedS = heap.ctrMap("WrappedS")
  val getS = heap.selMap("WrappedS", "getS")
  val struct_S = heap.ctrMap("struct_S")
  val sel_Sx = heap.selMap("struct_S","x")

  println("\nProgram:")
  println("--------")
  val progList = List("  int *p = calloc(int); ", "  *p = 42; ",
    "  struct S* ps = calloc(struct S); ", "  ps->x = *p; ",
    "  assert(ps->x == 42); ", "")
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

  /*
  > C1:
> ----------------
>   I0(emptyHeap).
>   I1(newHeap(ar), newAddress(ar))    :- I0(h), alloc(h, WrappedInt(0)) = ar.
>   I2(h', p)                          :- I1(h, p), write(h, p, WrappedInt(42)) = h'.
>   I3(newHeap(ar), p, newAddress(ar)) :- I2(h, p), alloc(h, WrappedS(struct_S(0))) = ar.
>   I4(h', p, ps)                      :- I3(h, p, ps), read(h, p) = o & write(h, ps, WrappedS(struct_S(getInt(o)))) = h'.
>   I5(h, p, ps)                       :- I4(h, p, ps).
>   false                              :- I4(h, p, ps), read(h, ps) = o & x(getS(o)) != 42.

> C2:
> ----------------
>   I0(emptyHeap).
>   I1(newHeap(ar), newAddress(ar))                                 :- I0(h), alloc(h, WrappedInt(0)) = ar.
>   I2(write(h, p, WrappedInt(42)), p)                              :- I1(h, p).
>   I3(newHeap(ar), p, newAddress(ar))                              :- I2(h, p), alloc(h, WrappedS(struct_S(0))) = ar.
>   I4(write(h, ps, WrappedS(struct_S(getInt(read(h, p))))), p, ps) :- I3(h, p, ps).
>   I5(h, p, ps)                                                    :- I4(h, p, ps).
>   false                                                           :- I4(h, p, ps), x(getS(read(h, ps))) != 42.
  */

  val clauses1 = List(I0(heap.emptyHeap()) :- true,
    I1(heap.newHeap(ar), heap.newAddr(ar)) :- (I0(h), heap.alloc(h, wrappedInt(0)) === ar),
    I2(heap.write(h, p, wrappedInt(42)), p) :- I1(h, p), // C2
    //I2(h1, p) :- (I1(h, p), heap.writeFun(h, p, WrappedInt(42)) === h1), //C1
    I3(heap.newHeap(ar), p, heap.newAddr(ar)) :- (I2(h, p), heap.alloc(h, wrappedS(struct_S(0))) === ar),
    I4(heap.write(h, ps, wrappedS(struct_S(getInt(heap.read(h, p))))), p, ps) :- I3(h, p, ps), // C2
    //I4(h1, p, ps) :- (I3(h, p, ps), heap.readFun(h, p) === o, heap.writeFun(h, ps,wrappedS(struct_S(getInt(o)))) === h1), // C1
    I5(h, p, ps) :- I4(h, p, ps)
  )
  val assertions = List(
    false :- (I0(h), heap.counter(h) =/= 0), // emptyHeap = 0
    false :- (I0(h), heap.addrToNat(p) === 0, heap.isAlloc(h,p)),
    //false :- (I0(h), heap.alloc(h, wrappedInt(0)) === ar, !heap.isAlloc(heap.newHeap(ar),heap.newAddr(ar)))
    false :- (I1(h,p), heap.counter(h) =/= 1) // after 1 alloc heap = 1
    //false :- (I1(h,p), heap.addrToNat(p) =/= 42) // after 1 alloc p = 1
    //false :- (I1(h,p), !heap.isAlloc(h,p)) // <h,p> is allocated
    //false :- (I1(h,p), getInt(heap.read(h,p)) =/= 42) // 1 alloc obj was Int(0)
    //false :- (heap.counter(heap.emptyHeap())  =/= 0)
    //false :- (I4(h, p, ps), sel_Sx(getS(heap.read(h, ps))) =/= 42) // C2
    //false :- (I4(h, p, ps), heap.read(h, ps) === o, sel_Sx(getS(o)) =/= 42) // C1
  )
  println("Clauses:")
  println("--------")
  val clauseHeads = for (c <- clauses1 ++ assertions) yield (ap.DialogUtil.asString
  {PrincessLineariser printExpression c.head})
  val maxHeadLen = clauseHeads.maxBy(_.length).length
  for (c <- clauses1 ++ assertions) {
    val curHeadLen = ap.DialogUtil.asString {
      PrincessLineariser printExpression c.head}.length
    println("  " ++ c.toPrologString(maxHeadLen - curHeadLen))
  }
  println

  val process: ParametricEncoder.Process = clauses1.zip(List.fill(clauses1.length)(NoSync))

  val system = System(List((process, ParametricEncoder.Singleton)),
      0, None, NoTime, List(), assertions)

  new VerificationLoop(system)

}

/** first sort in sortNames should be the object sort *
 *
 * @param heapSortName
 * @param addressSortName
 * @param objectSort
 * @param nullObjName
 * @param sortNames
 * @param ctorSignatures
 */
class Heap(heapSortName : String, addressSortName : String,
             objectSort : Heap.ADTSort, nullObjName : String,
             sortNames : Seq[String],
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
  val ObjectADT = new ADT(sortNames, ctorSignatures)

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

  val nullObj : MonoSortedIFunction = ctrMap(nullObjName)

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
  val counter = new MonoSortedIFunction("counter", List(HeapSort),
    Sort.Nat, false, false)
  val addrToNat = new MonoSortedIFunction("addrToNat",
    List(AddressSort), Sort.Nat, false, false)
  val isAlloc = new MonoSortedPredicate("isAlloc", List(HeapSort, AddressSort))

  val functions = List(emptyHeap, alloc, read, write, counter, addrToNat,
    newHeap, newAddr, nullObj)
  val predefPredicates = List(isAlloc)

  import IExpression._

  //val factsAboutAllocation =
    //all(List(AddressSort), !isAlloc(emptyHeap(), v(0))) //&
    //all(List(HeapSort), !isAlloc(v(0), null)) & // todo: change last v(0) null
    /*all(List(HeapSort, ObjectSort, AllocResSort),
        alloc(v(0), v(1)) === v(2) ==>
        (!isAlloc(v(0), newAddr(v(2))) & isAlloc(newHeap(v(2), newAddr(v(2)))) &
          all(List(AddressSort),
            v(0) =/= newAddr(v(3)) ==>
            (isAlloc(v(1), v(0)) <=> isAlloc(newHeap(v(3), a)))))) &*/
    /*all(List(HeapSort, HeapSort, ObjectSort, ObjectSort, HeapSort, HeapSort,
      AddressSort, AddressSort, AllocResSort, AllocResSort),
      // 0 h, 1 h', 2 o, 3 o', 4 h'', 5 h''', 6 p, 7 p', 8 ar, 9 ar'
      all(List(AddressSort), isAlloc(v(1), v(0)) <=> isAlloc(v(2), v(0))) &
      (alloc(v(0), v(2)) === v(8)) & (alloc(v(1), v(3)) === v(9)) ==>
                                     (v(6) === v(7)))*/
/*
    val factsAboutReadWrite =
      all(List(HeapSort, AddressSort, ObjectSort), // h, a, v
        isAlloc(v(0), v(1)) ==> (read(write(v(0), v(1), v(2)), v(1)) === v(2))
      ) &
      all(List(HeapSort, ObjectSort, AllocResSort),
        (alloc(v(0), v(1)) === v(2)) ==> // 0 h, 1 o, 2 ar
        (read(newHeap(v(2)), newAddr(v(2))) === v(1))
      ) &
      all(List(HeapSort, AddressSort),
        !isAlloc(v(0), v(1)) ==> (read(v(0), v(1)) === null)) & // todo: replace null with detObj
      all(List(HeapSort, AddressSort, AddressSort, ObjectSort), // h, a, a', o
        (v(1) =/= v(2)) & isAlloc(v(0), v(1)) & isAlloc(v(0), v(2)) ==>
          (read(write(v(0), v(2), v(3)), v(1)) === read(v(0), v(1)))) &
      all(List(HeapSort, AddressSort, ObjectSort), // h, a, o
        !isAlloc(v(0), v(1)) ==> (write(v(0), v(1), v(2)) === emptyHeap())) &
      all(List(HeapSort, AddressSort, ObjectSort, AllocResSort),  // h, a, o, ar
        isAlloc(v(0), v(1)) & (alloc(v(0), v(2)) === v(3)) ==>
        (read(newHeap(v(3), v(1))) === read(v(0), v(1)))) */

    /*val factsAboutReadWriteTriggered =
      all(List(HeapSort, AddressSort, ObjectSort), // h, a, v
        ITrigger(List(read(write(v(0), v(1), v(2)), v(1))), // todo: pattern makes sense? or just read without write?
          isAlloc(v(0), v(1)) ==> (read(write(v(0), v(1), v(2)), v(1)) === v(2)))) &
      all(List(HeapSort, ObjectSort, AllocResSort),
        ITrigger(List(read(newHeap(v(2)), newAddr(v(2)))), // todo: does this pattern make sense?
          (alloc(v(0), v(1)) === v(2)) ==> // 0 h, 1 o, 2 ar // todo: should it be a simple read(v(m), v(n)) where ar == <v(m),v(n)>
          (read(newHeap(v(2)), newAddr(v(2))) === v(1)))) &
      all(List(HeapSort, AddressSort, ObjectSort),
        ITrigger(List(read(v(0), v(1))), // todo: ok to have the same trigger pattern?
          !isAlloc(v(0), v(1)) ==> (read(v(0), v(1)) === nullObj()))) &
      all(List(HeapSort, AddressSort, AddressSort, ObjectSort), // h, a, a', o
        ITrigger(List(read(v(0), v(1))),
          (v(1) =/= v(2)) & isAlloc(v(0), v(1)) & isAlloc(v(0), v(2)) ==>
            (read(write(v(0), v(2), v(3)), v(1)) === read(v(0), v(1))))) &
      all(List(HeapSort, AddressSort, ObjectSort), // h, a, o
        ITrigger(List(write(v(0), v(1), v(2))),
          !isAlloc(v(0), v(1)) ==> (write(v(0), v(1), v(2)) === emptyHeap()))) &
      all(List(HeapSort, AddressSort, ObjectSort, AllocResSort),  // h, a, o, ar
        ITrigger(List(read(newHeap(v(3)), v(1))),
          isAlloc(v(0), v(1)) & (alloc(v(0), v(2)) === v(3)) ==>
            (read(newHeap(v(3)), v(1)) === read(v(0), v(1)))))*/

  val factsAboutReadWriteTriggered =
    all(List(HeapSort, AddressSort, ObjectSort), // h, a, v
      ITrigger(List(read(write(v(0), v(1), v(2)), v(1))), // todo: pattern makes sense? or just read without write?
        isAlloc(v(0), v(1)) ==> (read(write(v(0), v(1), v(2)), v(1)) === v(2)))) &
    all(List(HeapSort, ObjectSort, AllocResSort),
      ITrigger(List(read(newHeap(v(2)), newAddr(v(2)))), // todo: does this pattern make sense?
        (alloc(v(0), v(1)) === v(2)) ==> // 0 h, 1 o, 2 ar // todo: should it be a simple read(v(m), v(n)) where ar == <v(m),v(n)>
        (read(newHeap(v(2)), newAddr(v(2))) === v(1)))) &
    all(List(HeapSort, AddressSort, ObjectSort),
      ITrigger(List(read(v(0), v(1))), // todo: ok to have the same trigger pattern?
        !isAlloc(v(0), v(1)) ==> (read(v(0), v(1)) === nullObj()))) /*&
    all(List(HeapSort, AddressSort, AddressSort, ObjectSort), // h, a, a', o
      ITrigger(List(read(v(0), v(1))),
        (v(1) =/= v(2)) & isAlloc(v(0), v(1)) & isAlloc(v(0), v(2)) ==>
                                                (read(write(v(0), v(2), v(3)), v(1)) === read(v(0), v(1))))) &
    all(List(HeapSort, AddressSort, ObjectSort), // h, a, o
      ITrigger(List(write(v(0), v(1), v(2))),
        !isAlloc(v(0), v(1)) ==> (write(v(0), v(1), v(2)) === emptyHeap()))) &
    all(List(HeapSort, AddressSort, ObjectSort, AllocResSort),  // h, a, o, ar
      ITrigger(List(read(newHeap(v(3)), v(1))),
        isAlloc(v(0), v(1)) & (alloc(v(0), v(2)) === v(3)) ==>
                              (read(newHeap(v(3)), v(1)) === read(v(0), v(1)))))*/

    /*val extensionality =
      all(List(HeapSort, HeapSort), //0 h, 1 h'
        all(List(AddressSort), (isAlloc(v(1), v(0)) <=> isAlloc(v(2), v(0))) &
             read(v(1), v(0)) === read(v(2), v(0))) //0 a, 1 h, 2 h'
        ==> (v(0) === v(1)))
    */
  // 1. (counter(emptyHeap) = 0)   // counter val of empty heap
  // 2. forall h, a : addrToNat(a)=0 ==> !isAlloc(h, a) // a=0 is never allocated
  // 3. forall h, obj, ar, n:Nat : // incrementing heap counter with each alloc
  //      (alloc(h, obj) = ar) & (counter(h) = n) ==>  // calling alloc
  //        (counter(newHeap(ar) = n+1) &    // heap counter +1
  //        (addrToNat(newAddr(ar)) = n+1) &  // pointer points to new addr
  //        isAlloc(newHeap(ar), newAddr(ar)) & !isAlloc(h, newAddr(ar)) // new addr was previously unallocated, but now allocated
  // 4 & 5. Only between 0 < k <= counter is allocated.
  val inductionAxioms =
    all(List(HeapSort, AddressSort),
      (v(0) === emptyHeap()) ==> // 1 empty heap starts from 0
      (counter(v(0)) === 0) & !isAlloc(v(0), v(1))) & // and is unallocated
    all(List(HeapSort, AddressSort),
      addrToNat(v(1)) === 0 ==> !isAlloc(v(0), v(1))) & // 0 is null addr
    all(List(AddressSort),
      ex(List(IExpression.Sort.Nat),
        addrToNat(v(1)) === v(0))) &
    all(List(HeapSort),
      ex(List(IExpression.Sort.Nat),
        counter(v(1)) === v(0))) &
    all(List(HeapSort, ObjectSort, AllocResSort, HeapSort, AddressSort),
      (v(2) === alloc(v(0), v(1)) & //todo: this and the following two axioms do not seem to work
        v(3) === newHeap(v(2)) & v(4) === newAddr(v(2))) ==> // ar = alloc(h, obj)
      ((counter(v(3)) === counter(v(0))+1 & //ar.h.c = h.c+1
       addrToNat(v(4)) === counter(v(3))) &
       isAlloc(v(3), v(4)))) &
    all(List(AllocResSort, HeapSort), // newHeap
      ITrigger(List(newHeap(v(0))), (v(1) === newHeap(v(0))) ==>
      (counter(v(1)) === counter(newHeap(v(0)))))) &
    all(List(AllocResSort, AddressSort), //newAddr
      ITrigger(List(newAddr(v(0))), (v(1) === newAddr(v(0))) ==>
      (addrToNat(v(1)) === addrToNat(newAddr(v(0))))))
  /*
    all(List(HeapSort, ObjectSort, AllocResSort),
        (v(2) === alloc(v(0), v(1))) ==> // ar = alloc(h, obj)
        (counter(newHeap(v(2))) === counter(v(0))+1 & //ar.h.c = h.c+1
        addrToNat(newAddr(v(2))) === counter(v(0))+1 & //ar.a.c = h.c+1
        isAlloc(newHeap(v(2)), newAddr(v(2))) & !isAlloc(v(0), newAddr(v(2)))))*/
  /*all(List(HeapSort, ObjectSort, AllocResSort, IExpression.Sort.Nat), // 3
    ((alloc(v(0), v(1)) === v(2)) & (counter(v(0)) === v(3))) ==>
    (counter(newHeap(v(2))) === v(3) + 1) &
    (addrToNat(newAddr(v(2))) === v(3) + 1)) //&
    isAlloc(newHeap(v(2)), newAddr(v(2))) & !isAlloc(v(0), newAddr(v(2)))) &*/
  /*all(List(HeapSort, AddressSort, IExpression.Sort.Nat), // 4
    (0 < v(2) & v(2) <= counter(v(0)) & addrToNat(v(1)) === v(2)) ==>
    isAlloc(v(0), v(1))) & // 0 < k <= counter & a=k ==> isAlloc(h, a)
  all(List(HeapSort, AddressSort, IExpression.Sort.Nat), // 5
    ((v(2) <= 0) | v(2) > counter(v(0))) & addrToNat(v(1)) === v(2) ==>
    !isAlloc(v(0), v(1)))*/

  val theoryAxioms = factsAboutReadWriteTriggered & inductionAxioms

  val (funPredicates, axioms, _, functionTranslation) = Theory.genAxioms(
    theoryFunctions = functions, theoryAxioms = theoryAxioms,
    genTotalityAxioms = false, order = TermOrder.EMPTY.extendPred(isAlloc))
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

  TheoryRegistry register this
  override def toString = "HeapTheory"
}
