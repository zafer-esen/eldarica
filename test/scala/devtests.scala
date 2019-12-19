import org.scalatest._
import ap.SimpleAPI
import ap.types._
import ap.parser._
import ap.theories.ADT
import ap.util.Debug
import lazabs.horn.heap.Heap

class DevTests extends FlatSpec {
  Debug enableAllAssertions false

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

  SimpleAPI.withProver(enableAssert = false) { pr : SimpleAPI =>
    import pr._
    import heap._
    val h1 = HeapSort.newConstant("h1")
    val h2 = HeapSort.newConstant("h2")
    val h3 = HeapSort.newConstant("h3")
    val ar = AllocResSort.newConstant("ar")
    val ar2 = AllocResSort.newConstant("ar2")
    val p = AddressSort.newConstant("p")
    val p1 = AddressSort.newConstant("p1")
    val o = ObjectSort.newConstant("o")
    val o2 = ObjectSort.newConstant("o2")
    val x = Sort.Integer.newConstant("x")

    addConstants(List(h1, h2, h3, p, p1, ar, x, ar2, o, o2))

    pr setConstructProofs true


    import IExpression.{all => forall, _}

    val priTests = new PrincessTester(pr,
      printModelOnlyOnFail = true,
      printOnlyOnFail = false,
      printProofOnlyOnFail = false)
    import priTests._
/*
    TestCase (
      "Model generation case 1",
      CommonAssert(
        //ar === alloc(emptyHeap(), wrappedInt(1))//,
        /*h1 === newHeap(ar),
        h2 === newHeap(alloc(h1, wrappedInt(2))),
        p === newAddr(alloc(h1, wrappedInt(2))),
        h3 === write(h2, p, wrappedInt(3))*/
        isAlloc(h1, p),
        read(h1, p) === wrappedInt(x),
        p === nthAddr(3)
      ),
      //SatStep(read(h3, p) === wrappedInt(3))
      //SatStep(counter(newHeap(ar)) === 1)
      SatStep(x > 0)
    )

    TestCase (
      "Model generation case 2",
      CommonAssert(
        isAlloc(h1,p),
        h2 === newHeap(alloc(h1, wrappedInt(42))),
        wrappedInt(x) === read(h1, p)
      ),
      SatStep(x > 0)
    )

    TestCase (
      "Model generation case 3",
      CommonAssert(
        isAlloc(h1,p),
        h2 === newHeap(alloc(h1, wrappedInt(42))),
        wrappedInt(x) === read(h2, p)
      ),
      SatStep(x > 0)
    )

    TestCase (
      "Model generation case 4",
      CommonAssert(
        isAlloc(h1,p),
        h2 === write(newHeap(alloc(h1, wrappedInt(42))),
                     newAddr(alloc(h1, wrappedInt(42))), wrappedInt(43)),
        wrappedInt(x) === read(h2, p)
      ),
      SatStep(x > 0)
    )

    TestCase (
      "Model generation case 5",
      CommonAssert(
        isAlloc(h1,p),
        p === nthAddr(10),
        h2 === write(newHeap(alloc(h1, wrappedInt(42))),
          newAddr(alloc(h1, wrappedInt(42))), wrappedInt(43)),
        wrappedInt(x) === read(h2, p)
      ),
      SatStep(x > 0)
    )

    TestCase (
      "Model generation case 6",
      CommonAssert(
        isAlloc(h1, p),
        p === nthAddr(2),
        h3 === newHeap(alloc(emptyHeap(), wrappedInt(41))),
        h1 === newHeap(alloc(h3, wrappedInt(40))),
        h2 === write(write(h1, nullAddr(), wrappedInt(42)), p, wrappedInt(43))
      ),
      SatStep(h2 === emptyHeap()),
      UnsatStep(h2 =/= emptyHeap())
    )
*//*
    TestCase (
      "",
      SatStep(read(emptyHeap(), p) === defObj())
    )

    scope{
      withPartitionNumber(0)(
        !! (h1 === newHeap(alloc(emptyHeap(), wrappedInt(42)))),
        !! (p  === newAddr(alloc(emptyHeap(), wrappedInt(42))))
      )
      withPartitionNumber(1)(
        !! (read(h1, p) =/= wrappedInt(42))
      )
      ???
      println("-"*80)
      val interpolants = getInterpolants(List(Set(0), Set(1)))
      println("Interpolants" + Console.GREEN)
      interpolants.foreach(PrincessLineariser printExpression)
      println("\n" + Console.RESET + "-"*80)
    }

    scope{
      withPartitionNumber(0)(
        !! (h1 === newHeap(alloc(emptyHeap(), wrappedInt(42)))),
        !! (p  === newAddr(alloc(emptyHeap(), wrappedInt(42))))
      )
      withPartitionNumber(1)(
        !! (h2 === newHeap(alloc(newHeap(alloc(h1, wrappedInt(43))), wrappedInt(44))
        )),
        !! (read(h2, p) =/= wrappedInt(42))
      )
      ???
      println("-"*80)
      val interpolants = getInterpolants(List(Set(0), Set(1)))
      println("Interpolants" + Console.GREEN)
      interpolants.foreach(PrincessLineariser printExpression)
      println("\n" + Console.RESET + "-"*80)
    }

    scope{
      withPartitionNumber(0)(
        //!! (read(h1,p) === wrappedInt(42))
        !! (h1 === newHeap(alloc(emptyHeap(), wrappedInt(42)))),
        !! (p  === newAddr(alloc(emptyHeap(), wrappedInt(42))))
      )
      withPartitionNumber(1)(
        !! (p =/= p1 &
          h2 === write(write(h1, p1, wrappedInt(43)), p1, wrappedInt(44))
        ),
        !! (read(h2, p) =/= wrappedInt(42))
      )
      ???
      println("-"*80)
      val interpolants = getInterpolants(List(Set(0), Set(1)))
      println("Interpolants" + Console.GREEN)
      interpolants.foreach(PrincessLineariser printExpression)
      println("\n" + Console.RESET + "-"*80)
    }

*/
    scope{
      withPartitionNumber(0)(
        !! (o === wrappedInt(43)),
        !! (h1 === newHeap(alloc(emptyHeap(), wrappedInt(42)))),
        !! (p  === newAddr(alloc(emptyHeap(), wrappedInt(42))))
      )
      withPartitionNumber(1)(
        !! (h2 === newHeap(alloc(newHeap(alloc(h1, wrappedInt(42))), wrappedInt(43)))),
        !! (read(h2, p) =/= wrappedInt(42))
      )
      ???
      println("-"*80)
      val interpolants = getInterpolants(List(Set(0), Set(1)))
      println("Interpolants" + Console.GREEN)
      interpolants.foreach(PrincessLineariser printExpression)
      println("\n" + Console.RESET + "-"*80)
    }

    "..." should "pass" in {
      assert(getRes._1 == getRes._2)
    }
  }
}
