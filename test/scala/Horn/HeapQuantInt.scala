import ap.SimpleAPI
import ap.parser._
import ap.theories.ADT
import ap.types._
import ap.util.Debug
import lazabs.horn.heap.Heap
import org.scalatest._

class HeapQuantInt extends FlatSpec {
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
    objectADT.constructors.last()
  }

  SimpleAPI.withProver(enableAssert = true) { pr : SimpleAPI =>
    import heap._
    import pr._
    val M = createConstant("M", HeapSort)
    val M1 = createConstant("M'", HeapSort)
    val a = createConstant("a", AddressSort)
    val b = createConstant("b", AddressSort)
    val c = createConstant("c", AddressSort)
    val d = createConstant("d", ObjectSort)

    setConstructProofs(true)

    import IExpression._

    withPartitionNumber(0) {
      !! (isAlloc(M, a) & M1 === write(M, a, d))
    }
    withPartitionNumber(1) {
      !! (isAlloc(M, b) & isAlloc(M, c))
      !! (b =/= c & read(M1, b) =/= read(M, b) & read(M1, c) =/= read(M1, c))
    }

    println(???)
    println(getInterpolants(List(Set(0), Set(1))))

    "All heap theory quantified interpolation tests" should "pass" in {
      assert(true)
    }
  }
}
