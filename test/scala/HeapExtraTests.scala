import org.scalatest._
import ap.SimpleAPI
import ap.types._
import ap.parser._
import ap.util.Debug
import lazabs.horn.heap.Heap

class HeapTheoryExtraTests extends FlatSpec {
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
        StructSSort))))

  val wrappedInt = heap.ctrMap("WrappedInt")
  val getInt = heap.selMap("WrappedInt", "getInt")
  val wrappedS = heap.ctrMap("WrappedS")
  val getS = heap.selMap("WrappedS", "getS")
  val struct_S = heap.ctrMap("struct_S")
  val sel_Sx = heap.selMap("struct_S","x")

  SimpleAPI.withProver(enableAssert = true) { pr : SimpleAPI =>
    import pr._
    import heap._
    val h = HeapSort.newConstant("h")
    val ar = AllocResSort.newConstant("ar")

    addConstants(List(h, ar, detObj))

    import IExpression.{all => forall, _}

    val priTests = new PrincessTester(pr,
      printModels = true,
      printModelOnlyOnFail = true,
      printOnlyOnFail = true)
    import priTests._

    TestCase (
      "Reading back written value after chain allocation and a write.",
      CommonAssert(
        ar === alloc(newHeap(
                             alloc(emptyHeap(), wrappedInt(0)) // h(0)
                     ), wrappedInt(3))                         // h(0, 3)
      ),
      SatStep(isAlloc(newHeap(ar), newAddr(ar))),
      SatStep(getInt(read(newHeap(ar), newAddr(ar))) === 3),
      UnsatStep(getInt(read(newHeap(ar), newAddr(ar))) =/= 3),
      SatStep(read(newHeap(ar), newAddr(ar)) === wrappedInt(3)),
      CommonAssert(
        h === write(newHeap(ar), newAddr(ar), wrappedInt(50))  // h(0, 50)
      ),
      SatStep(read(h, 2) =/= read(newHeap(ar),2)),
      UnsatStep(read(h, 2) === read(newHeap(ar),2)),
      SatStep(isAlloc(h, newAddr(ar))),
      UnsatStep(getInt(read(h, newAddr(ar))) === 0),
      UnsatStep(getInt(read(h, newAddr(ar))) === 3),
      SatStep(getInt(read(h, newAddr(ar))) =/= 3),
      SatStep(read(h, newAddr(ar)) =/= wrappedInt(3)),
      UnsatStep(getInt(read(h, newAddr(ar))) =/= 50),
      SatStep(getInt(read(h, newAddr(ar))) === 50),
      SatStep(read(h, newAddr(ar)) === wrappedInt(50))
    )

    "All extra heap theory tests" should "pass" in {
      assert(getRes._1 == getRes._2)
    }
  }
}
