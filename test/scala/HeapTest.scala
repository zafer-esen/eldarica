import org.scalatest._
import ap.SimpleAPI
import ap.SimpleAPI.{NoModelException, ProverStatus}
import ap.types._
import ap.parser._
import ap.util.Debug
import lazabs.horn.heap.Heap

class PriTest (p : SimpleAPI, var printModels : Boolean = true,
               var printModelOnlyOnFail : Boolean = true) {
  import p._
  private var testCaseCounter : Int = 1
  private var successCounter : Int = 0
  private var totalTestCounter : Int = 0

  def reset {
    testCaseCounter = 1
    successCounter = 0
    totalTestCounter = 0
  }

  def getRes = (successCounter, totalTestCounter)

  private def expect[A](x : A, expected : A) : (A, Boolean) = {
    val res = x == expected
    if (res) successCounter = successCounter + 1
    totalTestCounter = totalTestCounter + 1
    val color = if (x == expected) Console.GREEN else Console.RED_B
    println(color + x + Console.RESET)
    (x, res)
  }

  abstract sealed class TestStep (val fs : IFormula*)
  case class SatStep(override val fs : IFormula*) extends TestStep
  case class UnsatStep(override val fs : IFormula*) extends TestStep
  case class CommonAssert (override val fs : IFormula*) extends TestStep

  private def printModel {
    val newline = "\n" + " "*2
    println {"Model:" + newline +
             (for ((l, v) <- partialModel.interpretation.iterator)
               yield ("" + l + " -> " + v)).mkString(newline)
    }
  }

  private def justAssert(s : TestStep) = {
    for (f <- s.fs) {
      addAssertion(f)
      print("  ")
      PrincessLineariser printExpression f
      println
    }
  }

  private def executeStep(ps : ProverStatus.Value, s : TestStep) {
    for (f <- s.fs) {
      addAssertion(f)
      print("  ")
      PrincessLineariser printExpression f
      if(s.fs.last != f) println(" &")
    }
    print(" --> ")
    val (proverResult, passed) = expect(???, ps)
    if (printModels && !(printModelOnlyOnFail && passed)
        && proverResult == ProverStatus.Sat) printModel
  }

  def TestCase(name : String, steps : TestStep*) {
    println("=" * 80)
    println(Console.BOLD + "Test " + testCaseCounter + ": " + name +
            Console.RESET)
    println("-" * 80)
    var stepNo = 1;
    scope {
      for (s <- steps) {
        if (s.isInstanceOf[CommonAssert]) {
          println("Common assertion: ")
          justAssert(s)
        } else {
          print("Step " + testCaseCounter + "." + stepNo + " (expected: ")
          stepNo = stepNo + 1
          s match {
            case _ : SatStep => println("Sat)")
              scope {executeStep(ProverStatus.Sat, s)}
            case _ : UnsatStep => println("Unsat)")
              scope {executeStep(ProverStatus.Unsat, s)}
            case _ => // do not execute anything for common assertions
          }
        }
        if (steps.last != s) println("-" * 80)
      }
      println("=" * 80)
      println
      testCaseCounter = testCaseCounter + 1
    }
  }
}

class UnitSpec extends FlatSpec {
  Debug enableAllAssertions true

  val NullObjName = "NullObj"
  val ObjSort = Heap.ADTSort(0)
  val StructSSort = Heap.ADTSort(1)
  val heap = new Heap("heap", "addr", "null", ObjSort,
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
    val h1 = HeapSort.newConstant("h'")
    val p = AddressSort.newConstant("p")
    val p1 = AddressSort.newConstant("p'")
    val ar = AllocResSort.newConstant("ar")
    val ar1 = AllocResSort.newConstant("ar'")
    val o = ObjectSort.newConstant("o")
    val o1 = ObjectSort.newConstant("o'")
    val c = Sort.Nat.newConstant("c")

    addConstants(List(h, h1, p, p1, ar, ar1, o, o1, c, nullObj))

    import IExpression.{all => forall, _}

    val priTests = new PriTest(pr)
    import priTests._


    /** Test cases for facts about allocation */
    TestCase("Empty heap has counter value 0.",
      UnsatStep(counter(emptyHeap()) =/= 0),
      SatStep(counter(emptyHeap()) === 0)
    )

    TestCase (
      "All locations on the empty heap are unallocated.",
      UnsatStep(isAlloc(emptyHeap(), p)),
      SatStep(!isAlloc(emptyHeap(), p))
    )

    TestCase (
      "For all heaps, location 0 (null) always stays unallocated.",
      UnsatStep(isAlloc(h, 0))
    )

    TestCase (
      "Allocation increases counter value by one.",
      CommonAssert(counter(newHeap(alloc(h, o))) === c),
      SatStep(c === counter(h) + 1),
      UnsatStep(c =/= counter(h) + 1)
    )

    TestCase (
      "After alloc, the returned pointer points to an allocated address.",
      CommonAssert(alloc(h, o) === ar),
      SatStep(isAlloc(newHeap(ar), newAddr(ar))),
      UnsatStep(!isAlloc(newHeap(ar), newAddr(ar)))
    )

    TestCase (
      "After alloc, previously allocated addresses are the same in both heaps",
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
      "Reading an unallocated location returns the null object",
      CommonAssert(
        !isAlloc(h, p)
      ),
      SatStep(
        read(h, p) === nullObj
      ),
      UnsatStep(
        read(h, p) =/= nullObj
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
      "Writing to an unallocated location returns the empty heap.",
      CommonAssert(
        !isAlloc(h, p)
      ),
      SatStep(
        write(h, p, o) === emptyHeap()
      ),
      UnsatStep(
        write(h, p, o) =/= emptyHeap()
      )
    )

    if(getRes._1 == getRes._2)
      println(Console.GREEN_B + "All " + getRes._1 + " tests passed!" +
              Console.RESET)
    else {
      println(Console.GREEN_B + "Pass:" + Console.RESET + " " + getRes._1)
      println(
        Console.RED_B + "Fail:" + Console.RESET + " " + (getRes._2 - getRes._1))
    }
    "Heap theory tests" should "succeed" in {
      assert(getRes._1 == getRes._2)
    }
  }
}
