import org.scalatest._
import ap.SimpleAPI
import ap.types._
import ap.parser._
import ap.theories.ADT
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
    val h = HeapSort.newConstant("h")
    val h1 = createConstant("h1", HeapSort)
    val ar = AllocResSort.newConstant("ar")
    val p1 =  createConstant("p1", AddressSort)
    val p2 =  createConstant("p2", AddressSort)
    val x = createConstant("x")
    val o = createConstant("o", ObjectSort)


    addConstants(List(h, ar))

    import IExpression.{all => forall, _}

    val priTests = new PrincessTester(pr,
      printModels = true,
      printModelOnlyOnFail = false,
      printOnlyOnFail = false)
    import priTests._

    /*TestCase (
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
      SatStep(read(h, nthAddr(2)) =/= read(newHeap(ar),nthAddr(2))),
      UnsatStep(read(h, nthAddr(2)) === read(newHeap(ar),nthAddr(2))),
      SatStep(isAlloc(h, newAddr(ar))),
      UnsatStep(getInt(read(h, newAddr(ar))) === 0),
      UnsatStep(getInt(read(h, newAddr(ar))) === 3),
      SatStep(getInt(read(h, newAddr(ar))) =/= 3),
      SatStep(read(h, newAddr(ar)) =/= wrappedInt(3)),
      UnsatStep(getInt(read(h, newAddr(ar))) =/= 50),
      SatStep(getInt(read(h, newAddr(ar))) === 50),
      SatStep(read(h, newAddr(ar)) === wrappedInt(50))
    )

    TestCase(
      "list-001-fail.c-1",
      CommonAssert(h === newHeap(alloc(emptyHeap(), wrappedS(struct_S(0))))),
      CommonAssert(p1 === newAddr(alloc(emptyHeap(), wrappedS(struct_S(0))))),
      CommonAssert(p2 === p1),
      SatStep(p1 === p2)
    )*/
    TestCase(
      "list-001-fail.c-2",
      //SatStep(defObj() =/= wrappedS(struct_S(0)))
      /*SatStep( h === emptyHeap() &&&
        newHeap(alloc(emptyHeap(), defObj())) ===
              newHeap(alloc(h, wrappedS(struct_S(0)))))*/
      /*UnsatStep( h === emptyHeap() &&&
               allocHeap(emptyHeap(), defObj()) ===
               allocHeap(h, wrappedS(struct_S(0))))*/
//      SatStep( h === newHeap(alloc(emptyHeap(), wrappedS(struct_S(42)))) &&&
 //              p1 === newAddr(alloc(emptyHeap(), wrappedS(struct_S(42)))) &&&
 //              o === read(h, p1))
      SatStep(   h === newHeap(alloc(emptyHeap(), wrappedS(struct_S(0)))) &&&
                 p1 === newAddr(alloc(emptyHeap(), wrappedS(struct_S(0)))) &&&
                 //p2 === p1 &&&
                 o === (getS(read(h, p1)))// &&&
                 //p1 === p2
      )

    )
    "All extra heap theory tests" should "pass" in {
      assert(getRes._1 == getRes._2)
    }
  }
}
