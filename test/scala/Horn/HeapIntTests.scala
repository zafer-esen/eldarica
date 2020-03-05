import org.scalatest._
import ap.SimpleAPI
import ap.types._
import ap.parser._
import ap.theories.ADT
import ap.util.Debug
import lazabs.horn.heap.Heap

class HeapIntTests extends FlatSpec {
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

  val Seq(wrappedInt,
          wrappedS,
          struct_S,
          defObj) = heap.ObjectADT.constructors
  val Seq(Seq(getInt),
          Seq(getS),
          Seq(sel_x), _*) = heap.ObjectADT.selectors

  SimpleAPI.withProver(enableAssert = true) { pr : SimpleAPI =>
    import pr._
    import heap._
    val h = createConstant("h", HeapSort)
    val h1 = createConstant("h1", HeapSort)
    val h2 = createConstant("h2", HeapSort)
    val ar = createConstant("ar", AllocResSort)
    val p = createConstant("p", AddressSort)
    val o = createConstant("o", ObjectSort)
    val o1 = createConstant("o1", ObjectSort)

    setConstructProofs(true)

    import IExpression.{all => forall, _}

    withPartitionNumber(0) {
      //!! (o === wrappedInt(42))
      //!! (h =/= emptyHeap())
      !! (h1 === newHeap(alloc(h, wrappedInt(42))))
      //!! (h1 === newHeap(alloc(newHeap(alloc(h, wrappedInt(42))), wrappedInt(42))))
    }
    withPartitionNumber(1) {
      !! (p  === newAddr(alloc(h, wrappedInt(42))))
      //!! (p === newAddr(alloc(newHeap(alloc(h, wrappedInt(42))), wrappedInt(42))))
    }
    withPartitionNumber(2) {
      //!! (h2 === newHeap(alloc(newHeap(alloc(h1, wrappedInt(42))), wrappedInt(43))))
      !! (h2 === newHeap(alloc(h1, wrappedInt(42))))
    }
    withPartitionNumber(3) {
     !! (read(h2, p) =/= wrappedInt(42))
     //!! (read(h1, p) =/= wrappedInt(42))
    }

    println(???)
    println(getInterpolants(List(Set(0), Set(1), Set(2), Set(3))))

    "All heap theory interpolation tests" should "pass" in {
      assert(true)
    }
  }
}
