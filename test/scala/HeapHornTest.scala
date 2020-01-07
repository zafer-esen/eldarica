import lazabs.horn.bottomup.{DagInterpolator, HornClauses, HornPredAbs, Util}
import lazabs.horn.concurrency.ParametricEncoder.{Infinite, NoSync, NoTime, System}
import lazabs.horn.concurrency.{ParametricEncoder, VerificationLoop}
import ap.types.{Sort, _}
import ap.parser._
import ap.theories.ADT
import ap.util.Debug
import lazabs.Main.{StoppedException, TimeoutException}
import org.scalatest.FlatSpec
import lazabs.horn.heap.Heap

class HeapHornTests extends FlatSpec {
  Debug enableAllAssertions true

  val NullObjName = "NullObj"
  val ObjSort = Heap.ADTSort(0)
  val StructSSort = Heap.ADTSort(1)
  val heap = new Heap("heap", "addr", ObjSort,
    List("HeapObject", "struct_S"), List(
      ("WrappedInt", Heap.CtorSignature(List(("getInt",
        Heap.OtherSort(Sort.Integer))), ObjSort)),
      ("WrappedS", Heap.CtorSignature(List(("getS", StructSSort)), ObjSort)),
      ("struct_S", Heap.CtorSignature(List(("x", Heap.OtherSort(Sort.Integer))),
        StructSSort)),
      ("defObj", Heap.CtorSignature(List(), ObjSort))),
    defObjCtor)

  def defObjCtor(objectADT : ADT) : ITerm = {
    import IExpression.toFunApplier
    //h.ObjectADT.constructors.last
    objectADT.constructors.last()
  }

  val Seq(wrappedInt, wrappedS, struct_S, defObj) = heap.ObjectADT.constructors
  val Seq(Seq(getInt), Seq(getS), Seq(sel_x), _*) = heap.ObjectADT.selectors

  println("\nProgram:")
  println("--------")
  val progList = List("  int *p = calloc(int); ", "  *p = 42; ",
    "  struct S* ps = calloc(struct S); ", "  ps->x = *p; ",
    "  assert(ps->x == 42); ", "")
  progList.foreach(println)

  import ap.parser.IExpression._
  import HornClauses._
  import heap._

  val I0 = new Predicate("I0", 1)
  val I1 = new Predicate("I1", 2)
  val I2 = new Predicate("I2", 2)
  val I3 = new Predicate("I3", 3)
  val I4 = new Predicate("I4", 3)
  val I5 = new Predicate("I5", 3)

  val h = HeapSort.newConstant("h")
  val h1 = HeapSort.newConstant("h'")
  val ar = AllocResSort.newConstant("ar")
  val p = AddressSort.newConstant("p")
  val ps = AddressSort.newConstant("ps")
  val o = ObjectSort.newConstant("o")

  //addConstants(List(h1, h2, h3, p, p1, ar, x, ar2, o, o2))

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

  val clauses1 = List(I0(emptyHeap()) :- true,
    I1(newHeap(ar), newAddr(ar)) :- (I0(h), alloc(h, wrappedInt(0)) === ar),
    I2(write(h, p, wrappedInt(42)), p) :- I1(h, p), // C2
    //I2(h1, p) :- (I1(h, p), writeFun(h, p, WrappedInt(42)) === h1), //C1
    I3(newHeap(ar), p, newAddr(ar)) :- (I2(h, p), alloc(h, wrappedS(struct_S(0))) === ar),
    I4(write(h, ps, wrappedS(struct_S(getInt(read(h, p))))), p, ps) :- I3(h, p, ps), // C2
    //I4(h1, p, ps) :- (I3(h, p, ps), readFun(h, p) === o, writeFun(h, ps,wrappedS(struct_S(getInt(o)))) === h1), // C1
    I5(h, p, ps) :- I4(h, p, ps)
  )
  val assertions = List(
    false :- (I0(h), counter(h) =/= 0), // emptyHeap = 0
    false :- (I0(h), p === 0, isAlloc(h,p)),
    //false :- (I0(h), heap.alloc(h, wrappedInt(0)) === ar, !heap.isAlloc(heap.newHeap(ar),heap.newAddr(ar)))
    false :- (I1(h,p), counter(h) =/= 1) // after 1 alloc heap = 1
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
  import ParametricEncoder._
  import lazabs.horn.bottomup.Util

  val process: ParametricEncoder.Process = clauses1.zip(List.fill(clauses1.length)(NoSync))

  val system = System(List((process, ParametricEncoder.Singleton)),
      0, None, NoTime, List(), assertions)

  val result = try {
    Console.withOut(Console.err) {
      new lazabs.horn.concurrency.VerificationLoop(system).result
    }
  } catch {
    case TimeoutException => {
      println("timeout")
      throw TimeoutException
    }
    case StoppedException => {
      println("stopped")
      throw StoppedException
    }
  }

  result match {
    case Left(_) =>
      println("SAFE")
    case Right(cex) => {
      println("UNSAFE")
      println
      lazabs.horn.concurrency.VerificationLoop.prettyPrint(cex)
    }
  }

  "..." should "pass" in {
    assert(true)
  }
}
