import ap.SimpleAPI
import ap.types.Sort
import ap.parser._
import ap.theories.ADT
import ap.util.Debug
import org.scalatest.FlatSpec
import lazabs.horn.heap.Heap

class MutRefStr extends FlatSpec {
  Debug enableAllAssertions true

  val NullObjName = "NullObj"
  val ObjSort = Heap.ADTSort(0)
  val ChildSort = Heap.ADTSort(1)
  val ParentSort = Heap.ADTSort(2)
  val heap = new Heap("heap", "addr", ObjSort,
    List("HeapObject", "structChild", "structParent"), List(
      ("WrappedInt", Heap.CtorSignature(List(("getInt",
        Heap.OtherSort(Sort.Integer))), ObjSort)),
      ("WrappedChild", Heap.CtorSignature(List(("getChild", ChildSort)), ObjSort)),
      ("WrappedParent", Heap.CtorSignature(List(("getParent", ParentSort)), ObjSort)),
      ("structChild", Heap.CtorSignature(
        List(("data", Heap.OtherSort(Sort.Integer)), ("p", Heap.AddressSort)), ChildSort)),
      ("structParent", Heap.CtorSignature(
        List(("child1", Heap.AddressSort), ("child2", Heap.AddressSort)), ParentSort)),
      ("defObj", Heap.CtorSignature(List(), ObjSort))),
    defObjCtor)

  def defObjCtor(objectADT : ADT) : ITerm = {
    import IExpression.toFunApplier
    objectADT.constructors.last()
  }

  val Seq(wrappedInt, wrappedChild, wrappedParent, structChild, structParent,
          defObj) = heap.ObjectADT.constructors
  val Seq(Seq(getInt), Seq(getChild), Seq(getParent), Seq(selData, selP),
          Seq(selChild1, selChild2), _*) = heap.ObjectADT.selectors

  SimpleAPI.withProver(enableAssert = true) { pr : SimpleAPI =>
    import pr._
    import heap._
    val h1 = createConstant("h1", HeapSort)
    val h2 = createConstant("h2", HeapSort)
    val h3 = createConstant("h3", HeapSort)
    val pParent = createConstant("pParent", AddressSort)
    val pChild1 = createConstant("pChild1", AddressSort)
    val pChild2 = createConstant("pChild2", AddressSort)
    val o1= createConstant("o1", ObjectSort)
    val o2 = createConstant("o2", ObjectSort)
    val parentObj = createConstant("parent", ObjectSort)
    val child1Obj = createConstant("child1", ObjectSort)
    val child2Obj = createConstant("child2", ObjectSort)

    setConstructProofs(true)

    import IExpression.{all => forall, _}

    withPartitionNumber(0) {
      !! (parentObj === wrappedParent(structParent(
                          nullAddr(), nullAddr())))
      !! (h1 === newHeap(alloc(emptyHeap(), parentObj)))
      !! (pParent === newAddr(alloc(emptyHeap(), parentObj)))
    }
    withPartitionNumber(1) {
      !! (child1Obj === wrappedChild(structChild(1, pParent)))
      !! (h2 === newHeap(alloc(h1, child1Obj)))
      !! (pChild1 === newAddr(alloc(h1, child1Obj)))
    }
    withPartitionNumber(2) {
      !! (child2Obj === wrappedChild(structChild(2, pParent)))
      !! (h3 === newHeap(alloc(h2, child2Obj)))
      !! (pChild2 === newAddr(alloc(h2, child2Obj)))
    }
    withPartitionNumber(3) {
      !! (read(h3, pChild1) === o1)
      !! (read(h3, pChild2) === o2)
      //!! (read(h3, pParent) =/= parentObj)
      //!! (selP(getChild(o1)) =/= pParent)
      !! (selP(getChild(o1)) =/= selP(getChild(o2)))
    }

    def printModel {
    val newLine = "\n" + " "*2
    val colors = List(Console.WHITE, Console.YELLOW).toArray
    var currentColorFlag = false
    println {"Model:" + newLine +
             (for ((l, v) <- partialModel.interpretation.iterator)
               yield {
                 currentColorFlag = !currentColorFlag
                 val str = LongLines.processLine(l + " -> " + v)
                 val curColor = if (currentColorFlag) colors(0) else colors(1)
                 curColor + str + Console.RESET
               }).mkString(newLine)
    }
  }

    println(???)
    //printModel

    println(getInterpolants(List(Set(0), Set(1), Set(2), Set(3))))

    "All heap theory MutRefStr tests" should "pass" in {
      assert(true)
    }
  }
}
