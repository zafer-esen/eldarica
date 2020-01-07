import org.scalatest._
import ap.SimpleAPI
import ap.types._
import ap.parser._
import ap.theories.ADT
import ap.util.Debug
import lazabs.horn.heap.Heap

class HeapTheoryTests extends FlatSpec {
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
          defObjCtr) = heap.ObjectADT.constructors
  val Seq(Seq(getInt),
          Seq(getS),
          Seq(sel_x), _*) = heap.ObjectADT.selectors

  import IExpression.toFunApplier
  val defObj = defObjCtr()

  SimpleAPI.withProver(enableAssert = true) { pr : SimpleAPI =>
    import pr._
    import heap._

    val h = HeapSort.newConstant("h")
    val h1 = HeapSort.newConstant("h'")
    val p = AddressSort.newConstant("p")
    val p1 = AddressSort.newConstant("p'")
    val ar = AllocResSort.newConstant("ar")
    val ar1 = AllocResSort.newConstant("ar'")
    val o = ObjectSort.newConstant("o")
    val o1 = ObjectSort.newConstant("o'")
    val c = Sort.Nat.newConstant("c")
// todo use create constant
    addConstants(List(h, h1, p, p1, ar, ar1, o, o1, c))

    import IExpression.{all => forall, _}

    val priTests = new PrincessTester(pr,
      printModels = true,
      printModelOnlyOnFail = true,
      printOnlyOnFail = true)
    import priTests._

    TestCase (
      "All locations on the empty heap are unallocated.",
      UnsatStep(isAlloc(emptyHeap(), p)),
      SatStep(!isAlloc(emptyHeap(), p))
    )

    TestCase (
      "For all heaps, null pointer always points to an unallocated location.",
      UnsatStep(isAlloc(h, nullAddr()))
    )

    TestCase(
      "For all heaps, trying to read the null pointer returns the defined " +
      "object.",
      UnsatStep(read(h, nullAddr()) =/= defObj),
      SatStep(read(h, nullAddr()) === defObj)
    )

    TestCase(
      "For all heaps, writing to the null pointer returns the original heap.",
      UnsatStep(write(h, nullAddr(), o) =/= h),
      SatStep(write(h, nullAddr(), o) === h)
    )

    TestCase (
      "After alloc, the returned pointer points to an allocated address.",
      CommonAssert(alloc(h, o) === ar),
      SatStep(isAlloc(newHeap(ar), newAddr(ar))),
      UnsatStep(!isAlloc(newHeap(ar), newAddr(ar)))
    )


    TestCase (
      "After alloc, previously allocated addresses are the same in both heaps.",
      CommonAssert(
        alloc(h, o) === ar
      ),
      UnsatStep(
        isAlloc(h, p) & !isAlloc(newHeap(ar), p)
      ),
      UnsatStep(
        p =/= newAddr(ar),
        !isAlloc(h, p),
        isAlloc(newHeap(ar), p)
      )
    )

    TestCase(
      "Deterministic allocation",
      UnsatStep(
        forall(List(AddressSort), isAlloc(h, v(0)) <=> isAlloc(h1, v(0))),
        alloc(h, o) === ar,
        alloc(h1, o1) === ar1,
        newAddr(ar) =/= newAddr(ar1)
      )
    )

    /** Test cases for facts about read/write */
    TestCase(
      "Reading from a previously written (alloc.) " +
      "location returns that value.",
      CommonAssert(
        isAlloc(h, p)
      ),
      SatStep(
        read(write(h, p, o), p) === o
      ),
      UnsatStep(
        read(write(h, p, o), p) =/= o
      )
    )

    TestCase(
      "Reading a newly allocated location returns the allocated value",
      CommonAssert(
        ar === alloc(h, o)
      ),
      SatStep(
        read(newHeap(ar), newAddr(ar)) === o
      ),
      UnsatStep(
        read(newHeap(ar), newAddr(ar)) =/= o
      )
    )

    TestCase(
      "Allocation does not modify any of the values on the old heap",
      CommonAssert(
        ar === alloc(h, o),
        p =/= newAddr(ar)
      ),
      SatStep(
        read(newHeap(ar), p) === read(h, p)
      ),
      UnsatStep(
        read(newHeap(ar), p) =/= read(h, p)
      )
    )

    TestCase(
      "Reading a newly allocated location returns the allocated value (v2)",
      CommonAssert(
        alloc(h, o) === ar,
        h1 === newHeap(ar),
        p === newAddr(ar)
      ),
      SatStep(
        read(h1, p) === o
      ),
      UnsatStep(
        read(h1, p) =/= o
      )
    )

    TestCase(
      "Reading an unallocated location returns the defined object",
      CommonAssert(
        !isAlloc(h, p)
      ),
      SatStep(
        read(h, p) === defObj
      ),
      UnsatStep(
        read(h, p) =/= defObj
      )
    )

    TestCase(
      "Writing to a location does not modify the rest of the locations",
      CommonAssert(
        p =/= p1,
        isAlloc(h, p),
        isAlloc(h, p1)
      ),
      SatStep(
        read(write(h, p1, o), p) === read(h, p)
      ),
      UnsatStep(
        read(write(h, p1, o), p) =/= read(h, p)
      )
    )

    TestCase(
      "Writing to an unallocated location returns the same heap.",
      CommonAssert(!isAlloc(h, p)),
      SatStep(write(h, p, o) === h),
      UnsatStep(write(h, p, o) =/= h),

      CommonAssert(h =/= emptyHeap()),
      SatStep(write(h, p, o) === h),
      UnsatStep(write(h, p, o) =/= h),

      CommonAssert(p =/= nullAddr()),
      SatStep(write(h, p, o) === h),
      UnsatStep(write(h, p, o) =/= h)
    )

    "All heap theory tests" should "pass" in {
      assert(getRes._1 == getRes._2)
    }
  }
}
