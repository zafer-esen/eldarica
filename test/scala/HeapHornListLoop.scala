import lazabs.horn.bottomup.{DagInterpolator, HornClauses, HornPredAbs, Util}
import lazabs.horn.concurrency.ParametricEncoder.{Infinite, NoSync, NoTime, System}
import lazabs.horn.concurrency.{ParametricEncoder, VerificationLoop}
import ap.types.{Sort, _}
import ap.parser._
import ap.theories.ADT
import ap.util.Debug
import lazabs.GlobalParameters
import lazabs.Main.{StoppedException, TimeoutException}
import lazabs.horn.concurrency.VerificationLoop.Counterexample
import org.scalatest.FlatSpec
import lazabs.horn.heap.Heap

class HeapHornListLoop extends FlatSpec {
  Debug enableAllAssertions true

  val NullObjName = "NullObj"
  val ObjSort = Heap.ADTSort(0)
  val NodeSort = Heap.ADTSort(1)
  val heap = new Heap("heap", "addr", ObjSort,
    List("HeapObject", "structNode"), List(
      ("WrappedInt", Heap.CtorSignature(List(("getInt",
        Heap.OtherSort(Sort.Integer))), ObjSort)),
      ("WrappedNode", Heap.CtorSignature(List(("getNode", NodeSort)), ObjSort)),
      ("structNode", Heap.CtorSignature(
        List(("data", Heap.OtherSort(Sort.Integer)), ("next", Heap.AddressSort)), NodeSort)),
      ("defObj", Heap.CtorSignature(List(), ObjSort))),
    defObjCtor)

  def defObjCtor(objectADT : ADT) : ITerm = {
    import IExpression.toFunApplier
    objectADT.constructors.last()
  }

  val Seq(wrappedInt, wrappedNode, structNode, defObj) =
    heap.ObjectADT.constructors
  val Seq(Seq(getInt), Seq(getNode), Seq(nodeData, nodeNext), _*) =
    heap.ObjectADT.selectors

  import ap.parser.IExpression._
  import HornClauses._
  import heap._

  val I0 = new MonoSortedPredicate("I0", List(HeapSort))
  val I1 = new MonoSortedPredicate("I1", List(HeapSort, IExpression.Sort.Integer))
  val I2 = new MonoSortedPredicate("I2", List(HeapSort, IExpression.Sort.Integer, AddressSort))
  val I3 = new MonoSortedPredicate("I3", List(HeapSort, IExpression.Sort.Integer, AddressSort))
  val I4 = new MonoSortedPredicate("I4", List(HeapSort, IExpression.Sort.Integer, AddressSort))
  val I5 = new MonoSortedPredicate("I5", List(HeapSort, IExpression.Sort.Integer, AddressSort, AddressSort))
  val I6 = new MonoSortedPredicate("I6", List(HeapSort, IExpression.Sort.Integer, AddressSort, AddressSort))
  val I7 = new MonoSortedPredicate("I7", List(HeapSort, IExpression.Sort.Integer, AddressSort, AddressSort))
  val I8 = new MonoSortedPredicate("I8", List(HeapSort, IExpression.Sort.Integer, AddressSort, AddressSort))
  val I9 = new MonoSortedPredicate("I9", List(HeapSort, IExpression.Sort.Integer, AddressSort))
  val I10 = new MonoSortedPredicate("I10", List(HeapSort, IExpression.Sort.Integer, AddressSort))

  val h = HeapSort.newConstant("h")
  val n = AddressSort.newConstant("n")
  val o = ObjectSort.newConstant("o")
  val listNotEmpty = IExpression.Sort.Integer.newConstant("listNotEmpty")
  val head = AddressSort.newConstant("head")
  val nonDet = IExpression.Sort.Integer.newConstant("nonDet")

  val clauses1 = List(
    I0(emptyHeap()) :- true,
    I1(h, 0):- I0(h), // (h, listNotEmpty)
    I2(h, listNotEmpty, nullAddr()) :- I1(h, listNotEmpty), // h, listNotEmpty, head
    I4(h, listNotEmpty, head) :- (I2(h, listNotEmpty, head), nonDet === 0), // terminate loop
    I3(h, listNotEmpty, head) :- (I2(h, listNotEmpty, head), nonDet =/= 0), // continue loop
    I5(newHeap(alloc(h, o)), listNotEmpty, head, newAddr(alloc(h, o))) :- (I3(h, listNotEmpty, head), o =/= defObj()), /*todo: crashes without o =/= defObj() if UNSAT, why?*/
    I6(write(h, n, wrappedNode(structNode(0, nodeNext(getNode(read(h, n)))))), listNotEmpty, head, n) :- I5(h, listNotEmpty, head, n),
    I7(write(h, n, wrappedNode(structNode(nodeData(getNode(read(h, n))), 0))), listNotEmpty, head, n) :- I6(h, listNotEmpty, head, n),
    I8(h, listNotEmpty, n, n) :- (I7(h, listNotEmpty, head, n), head === nullAddr()),
    I8(write(h, head, wrappedNode(structNode(nodeData(getNode(read(h, head))), n))), listNotEmpty, head, n) :- (I7(h, listNotEmpty, head, n), head =/= nullAddr()),
    I2(h, 1, head) :- I8(h, listNotEmpty, head, n),
    I9(h, listNotEmpty, head)  :- (I4(h, listNotEmpty, head), listNotEmpty =/= 0), // if list is not empty
    I10(h, listNotEmpty, head)  :- (I4(h, listNotEmpty, head), listNotEmpty === 0), // if list is empty
    I10(h, listNotEmpty, head) :- I9(h, listNotEmpty, head)
  )
  val assertions = List(
    false :- (I9(h, listNotEmpty, head), nodeData(getNode(read(h, head))) =/= 0)
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

  val process: ParametricEncoder.Process = clauses1.zip(List.fill(clauses1.length)(NoSync))

  val system = System(List((process, ParametricEncoder.Singleton)),
      0, None, NoTime, List(), assertions)

  GlobalParameters.get.log = true
  val verificationLoop = new lazabs.horn.concurrency.VerificationLoop(system)
  val result = try {
    Console.withOut(Console.err) {
      verificationLoop.result
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
    case Left(x) =>
      println("SAFE")
      println(x)
    case Right(cex : Counterexample) => {
      println("UNSAFE")
      println
      lazabs.horn.concurrency.VerificationLoop.prettyPrint(cex)
    }
  }

  "..." should "pass" in {
    assert(true)
  }
}
