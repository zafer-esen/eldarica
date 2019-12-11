import org.scalatest._
import ap.SimpleAPI
import ap.types._
import ap.parser._
import ap.theories.ADT
import ap.util.Debug
import lazabs.horn.heap.Heap

class DevTests extends FlatSpec {
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
    val h1 = HeapSort.newConstant("h1")
    val h2 = HeapSort.newConstant("h2")
    val h3 = HeapSort.newConstant("h3")
    val ar = AllocResSort.newConstant("ar")
    val p = AddressSort.newConstant("p")

    addConstants(List(h1, h2, h3, p, ar))

    import IExpression.{all => forall, _}

    val priTests = new PrincessTester(pr,
      printModels = true,
      printModelOnlyOnFail = false,
      printOnlyOnFail = false)
    import priTests._

    TestCase (
      "Reading back written value after chain allocation and a write.",
      CommonAssert(
        ar === alloc(emptyHeap(), wrappedInt(1))//,
        /*h1 === newHeap(ar),
        h2 === newHeap(alloc(h1, wrappedInt(2))),
        p === newAddr(alloc(h1, wrappedInt(2))),
        h3 === write(h2, p, wrappedInt(3))*/
      ),
      //SatStep(read(h3, p) === wrappedInt(3))
      SatStep(counter(newHeap(ar)) === 1)
    )

    "..." should "pass" in {
      assert(getRes._1 == getRes._2)
    }
  }
}
