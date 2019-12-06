package lazabs.horn.heap

import ap.basetypes.IdealInt
import ap.{Signature, types}
import ap.parser._
import ap.types._
import ap.proof.theoryPlugins.Plugin
import ap.terfor.TermOrder
import ap.terfor.conjunctions.Conjunction
import ap.theories._
import ap.theories.ADT
import ap.types.{MonoSortedIFunction, Sort}
import ap.util.Debug

import scala.collection.mutable

object Heap {
  private val AC = Debug.AC_ADT // todo
  abstract sealed class CtorArgSort
  case class ADTSort(num : Int) extends CtorArgSort
  case class OtherSort(sort : Sort) extends CtorArgSort
  case class CtorSignature(arguments : Seq[(String, CtorArgSort)],
                           result : ADTSort)

  class HeapException(m : String) extends Exception(m)

  /** implicit converters from Heap.CtorArgSort to ADT.CtorArgSort */
  private implicit def HeapSortToADTSort(s : CtorArgSort) : ADT.CtorArgSort =
    s match {
      case t : ADTSort => ADT.ADTSort(t.num)
      case t : OtherSort => ADT.OtherSort(t.sort)
  }

  private implicit def HeapSortToADTSort(l : Seq[(String, Heap.CtorSignature)]):
  Seq[(String, ADT.CtorSignature)] = {
    for (s <- l) yield (s._1, ADT.CtorSignature(
      for (arg <- s._2.arguments) yield (arg._1, HeapSortToADTSort(arg._2)),
      ADT.ADTSort(s._2.result.num)))
  }
}

/** first sort in sortNames should be the object sort *
 *
 * @param heapSortName
 * @param addressSortName
 * @param objectSort
 * @param nullObjName
 * @param sortNames
 * @param ctorSignatures
 */
class Heap(heapSortName : String, addressSortName : String,
           nullObjName : String, objectSort : Heap.ADTSort,
             sortNames : Seq[String],
             ctorSignatures : Seq[(String, Heap.CtorSignature)])
    extends Theory {
  import Heap._
  //-BEGIN-ASSERTION-///////////////////////////////////////////////////////////
  Debug.assertCtor(AC, // todo: redundant with the one in ADT or have it here too?
    ctorSignatures forall {
      case (_, sig) =>
        ((sig.arguments map (_._2)) ++ List(sig.result)) forall {
          case Heap.ADTSort(id)   => id >= 0 && id < sortNames.size
          case _ : OtherSort => true
        }
    })
  //-END-ASSERTION-/////////////////////////////////////////////////////////////
  private val ctorSignaturesWithNull = ctorSignatures ++
    List(("nullCtr", Heap.CtorSignature(List(), objectSort)))
  private val ObjectADT = new ADT(sortNames, ctorSignaturesWithNull)

  val HeapSort = Sort.createInfUninterpretedSort(heapSortName)
  val AddressSort = Sort.createInfUninterpretedSort(addressSortName) //todo: nat?
  val ObjectSort = ObjectADT.sorts.head

  /** A mapping of ctor names to ctors (for ObjectADT) for convenience*/
  val ctrMap : Map[String, MonoSortedIFunction] =
    ObjectADT.constructors.map(c => c.name -> c).toMap
  /** A mapping of (ctorName, selName) to selectors (for ObjectADT)*/
  val selMap : Map[(String, String), MonoSortedIFunction] =
    (for(cid <- ObjectADT.constructors.indices; sel <- ObjectADT.selectors(cid))
      yield (ObjectADT.constructors(cid).name, sel.name) -> sel).toMap

  val nullObjCtr = ctrMap("nullCtr");

  /** Create return sort of alloc as an ADT: Heap x Address */
  private val AllocResCtorSignature = ADT.CtorSignature(
    List(("newHeap", ADT.OtherSort(HeapSort)),
         ("newAddress", ADT.OtherSort(AddressSort))), ADT.ADTSort(0))
  private val AllocResADT = new ADT(List("AllocRes"),
    List(("AllocRes", AllocResCtorSignature)))
  val AllocResSort = AllocResADT.sorts.head
  val newHeap = AllocResADT.selectors(0)(0)
  val newAddr = AllocResADT.selectors(0)(1)

  /** Functions and predicates of the theory
   * emptyHeap: ()                   --> Heap
   * alloc    : Heap x Obj           --> Heap x Address (allocRes)
   * read     : Heap x Address       --> Obj
   * write    : Heap x Address x Obj --> Heap
   * isAlloc  : Heap x Address       --> Bool
   *
   * counter  : Heap                 --> Nat
   * */
  val emptyHeap = new MonoSortedIFunction("emptyHeap", argSorts = List(),
    resSort = HeapSort, _partial = false, _relational = false)
  val alloc = new MonoSortedIFunction("alloc", List(HeapSort, ObjectSort),
    AllocResSort, false, false)
  val read = new MonoSortedIFunction("read", List(HeapSort, AddressSort),
    ObjectSort, false, false)
  val write = new MonoSortedIFunction("write",
    List(HeapSort, AddressSort, ObjectSort), HeapSort, false, false)
  val counter = new MonoSortedIFunction("counter", List(HeapSort),
    Sort.Nat, false, false)
  val isAlloc = new MonoSortedPredicate("isAlloc", List(HeapSort, AddressSort))

  val functions = List(emptyHeap, alloc, read, write, counter,
    newHeap, newAddr)
  val predefPredicates = List(isAlloc)

  import IExpression._

  val nullObj = ObjectSort.newConstant(nullObjName)

  private def _isAlloc(h: ITerm , p: ITerm) : IFormula =
    counter(h) >= p & p > 0
 /* private def _alloc(ar: ITerm, h: ITerm, o: ITerm) : IFormula = {
    counter(newHeap(ar)) === counter(h) + 1 & newAddr(ar) === counter(h) + 1 &
    read(newHeap(ar), newAddr(ar)) === o /*&
    all(v(0) =/= newAddr(ar) ==> (read(newHeap(ar), v(0)) === read(h, v(0))))*/
  }*/

  //val factsAboutAllocation =
    //all(List(AddressSort), !isAlloc(emptyHeap(), v(0))) //&
    //all(List(HeapSort), !isAlloc(v(0), null)) & // todo: change last v(0) null
    /*all(List(HeapSort, ObjectSort, AllocResSort),
        alloc(v(0), v(1)) === v(2) ==>
        (!isAlloc(v(0), newAddr(v(2))) & isAlloc(newHeap(v(2), newAddr(v(2)))) &
          all(List(AddressSort),
            v(0) =/= newAddr(v(3)) ==>
            (isAlloc(v(1), v(0)) <=> isAlloc(newHeap(v(3), a)))))) &*/
    /*all(List(HeapSort, HeapSort, ObjectSort, ObjectSort, HeapSort, HeapSort,
      AddressSort, AddressSort, AllocResSort, AllocResSort),
      // 0 h, 1 h', 2 o, 3 o', 4 h'', 5 h''', 6 p, 7 p', 8 ar, 9 ar'
      all(List(AddressSort), isAlloc(v(1), v(0)) <=> isAlloc(v(2), v(0))) &
      (alloc(v(0), v(2)) === v(8)) & (alloc(v(1), v(3)) === v(9)) ==>
                                     (v(6) === v(7)))*/
/*
    val factsAboutReadWrite =
      all(List(HeapSort, AddressSort, ObjectSort), // h, a, v
        isAlloc(v(0), v(1)) ==> (read(write(v(0), v(1), v(2)), v(1)) === v(2))
      ) &
      all(List(HeapSort, ObjectSort, AllocResSort),
        (alloc(v(0), v(1)) === v(2)) ==> // 0 h, 1 o, 2 ar
        (read(newHeap(v(2)), newAddr(v(2))) === v(1))
      ) &
      all(List(HeapSort, AddressSort),
        !isAlloc(v(0), v(1)) ==> (read(v(0), v(1)) === null)) & // todo: replace null with detObj
      all(List(HeapSort, AddressSort, AddressSort, ObjectSort), // h, a, a', o
        (v(1) =/= v(2)) & isAlloc(v(0), v(1)) & isAlloc(v(0), v(2)) ==>
          (read(write(v(0), v(2), v(3)), v(1)) === read(v(0), v(1)))) &
      all(List(HeapSort, AddressSort, ObjectSort), // h, a, o
        !isAlloc(v(0), v(1)) ==> (write(v(0), v(1), v(2)) === emptyHeap())) &
      all(List(HeapSort, AddressSort, ObjectSort, AllocResSort),  // h, a, o, ar
        isAlloc(v(0), v(1)) & (alloc(v(0), v(2)) === v(3)) ==>
        (read(newHeap(v(3), v(1))) === read(v(0), v(1)))) */

    /*val factsAboutReadWriteTriggered =
      all(List(HeapSort, AddressSort, ObjectSort), // h, a, v
        ITrigger(List(read(write(v(0), v(1), v(2)), v(1))), // todo: pattern makes sense? or just read without write?
          isAlloc(v(0), v(1)) ==> (read(write(v(0), v(1), v(2)), v(1)) === v(2)))) &
      all(List(HeapSort, ObjectSort, AllocResSort),
        ITrigger(List(read(newHeap(v(2)), newAddr(v(2)))), // todo: does this pattern make sense?
          (alloc(v(0), v(1)) === v(2)) ==> // 0 h, 1 o, 2 ar // todo: should it be a simple read(v(m), v(n)) where ar == <v(m),v(n)>
          (read(newHeap(v(2)), newAddr(v(2))) === v(1)))) &
      all(List(HeapSort, AddressSort, ObjectSort),
        ITrigger(List(read(v(0), v(1))), // todo: ok to have the same trigger pattern?
          !isAlloc(v(0), v(1)) ==> (read(v(0), v(1)) === nullObj()))) &
      all(List(HeapSort, AddressSort, AddressSort, ObjectSort), // h, a, a', o
        ITrigger(List(read(v(0), v(1))),
          (v(1) =/= v(2)) & isAlloc(v(0), v(1)) & isAlloc(v(0), v(2)) ==>
            (read(write(v(0), v(2), v(3)), v(1)) === read(v(0), v(1))))) &
      all(List(HeapSort, AddressSort, ObjectSort), // h, a, o
        ITrigger(List(write(v(0), v(1), v(2))),
          !isAlloc(v(0), v(1)) ==> (write(v(0), v(1), v(2)) === emptyHeap()))) &
      all(List(HeapSort, AddressSort, ObjectSort, AllocResSort),  // h, a, o, ar
        ITrigger(List(read(newHeap(v(3)), v(1))),
          isAlloc(v(0), v(1)) & (alloc(v(0), v(2)) === v(3)) ==>
            (read(newHeap(v(3)), v(1)) === read(v(0), v(1)))))*/

  val factsAboutReadWriteTriggered =
    all(List(HeapSort, AddressSort, ObjectSort),
      ITrigger(List(read(write(v(0), v(1), v(2)), v(1))),
        _isAlloc(v(0), v(1)) ==> (read(write(v(0), v(1), v(2)), v(1)) === v(2)))
    ) &
    all(List(HeapSort, AddressSort, ObjectSort, AddressSort),
      ITrigger(List(read(write(v(0), v(1), v(2)), v(3))),
        _isAlloc(v(0), v(1)) & _isAlloc(v(0), v(3)) ==>
        (read(write(v(0), v(1), v(2)), v(3)) === read(v(0), v(3))))
    ) &
    all(List(HeapSort, AddressSort, ObjectSort),
      ITrigger(List(counter(write(v(0), v(1), v(2)))),
        _isAlloc(v(0), v(1)) ==>
        (counter(write(v(0), v(1), v(2))) === counter(v(0))))
    ) &
    all(List(HeapSort, AddressSort),
      ITrigger(List(read(v(0), v(1))),
        !_isAlloc(v(0), v(1)) ==> (read(v(0), v(1)) === nullObj))
    ) &
    all(List(HeapSort, AddressSort, ObjectSort),
        ITrigger(List(write(v(0), v(1), v(2))),
          !_isAlloc(v(0), v(1)) ==> (write(v(0), v(1), v(2)) === emptyHeap()))
    ) &
    all(List(HeapSort, ObjectSort),
      ITrigger(List(
        read(newHeap(alloc(v(0), v(1))), newAddr(alloc(v(0), v(1))))),
        read(newHeap(alloc(v(0), v(1))), newAddr(alloc(v(0), v(1)))) === v(1))
    ) &
    all(List(HeapSort, AddressSort),
      ITrigger(List(read(v(0), v(1))),
        all(List(ObjectSort),
          (v(2) =/= newAddr(alloc(v(1), v(0)))) ==>
          (read(v(1), v(2)) === read(newHeap(alloc(v(1), v(0))), v(2)))))
    )
  /*&
    all(List(),
      (_isAlloc(v(0), v(1)) & v(2) === write(v(0), v(1), v(3))) ==>
      (counter(v(0)) === counter(v(2))))*/
    /*all(List(HeapSort, AddressSort, ObjectSort),
      isAlloc(v(0), v(1)) ==> (read(v(0), v(1)) =/= nullObj)
    )
    all(List(HeapSort, AddressSort, ObjectSort, HeapSort),
      ITrigger(List(write(v(0), v(1), v(2))),
        ex(List(ObjectSort),
          v(0) === nullObj & v(3) === v(0)) ==>
        (write(v(0), v(1), v(2)) =/= v(3)))) &
    all(List(ObjectSort, ObjectSort),
      (v(0) === nullObj & v(1) === nullObj ==> (v(0) === v(1))))*/


  /*
    all(List(HeapSort, AddressSort, ObjectSort), // h, a, v
      ITrigger(List(read(write(v(0), v(1), v(2)), v(1))), // todo: pattern makes sense? or just read without write?
        isAlloc(v(0), v(1)) ==> (read(write(v(0), v(1), v(2)), v(1)) === v(2)))) //& */
   /* all(List(HeapSort, ObjectSort, AllocResSort),
      ITrigger(List(read(newHeap(v(2)), newAddr(v(2)))), // todo: does this pattern make sense?
        (alloc(v(0), v(1)) === v(2)) ==> // 0 h, 1 o, 2 ar // todo: should it be a simple read(v(m), v(n)) where ar == <v(m),v(n)>
        (read(newHeap(v(2)), newAddr(v(2))) === v(1)))) &
    all(List(HeapSort, AddressSort, ObjectSort),
      ITrigger(List(read(v(0), v(1))), // todo: ok to have the same trigger pattern?
        !isAlloc(v(0), v(1)) ==> (read(v(0), v(1)) === nullObj()))) /*&*/
    all(List(HeapSort, AddressSort, AddressSort, ObjectSort), // h, a, a', o
      ITrigger(List(read(v(0), v(1))),
        (v(1) =/= v(2)) & isAlloc(v(0), v(1)) & isAlloc(v(0), v(2)) ==>
                                                (read(write(v(0), v(2), v(3)), v(1)) === read(v(0), v(1))))) &
    all(List(HeapSort, AddressSort, ObjectSort), // h, a, o
      ITrigger(List(write(v(0), v(1), v(2))),
        !isAlloc(v(0), v(1)) ==> (write(v(0), v(1), v(2)) === emptyHeap()))) &
    all(List(HeapSort, AddressSort, ObjectSort, AllocResSort),  // h, a, o, ar
      ITrigger(List(read(newHeap(v(3)), v(1))),
        isAlloc(v(0), v(1)) & (alloc(v(0), v(2)) === v(3)) ==>
                              (read(newHeap(v(3)), v(1)) === read(v(0), v(1)))))*/

    /*val extensionality =
      all(List(HeapSort, HeapSort), //0 h, 1 h'
        all(List(AddressSort), (isAlloc(v(1), v(0)) <=> isAlloc(v(2), v(0))) &
             read(v(1), v(0)) === read(v(2), v(0))) //0 a, 1 h, 2 h'
        ==> (v(0) === v(1)))
    */
  // 1. (counter(emptyHeap) = 0)   // counter val of empty heap
  // 2. forall h, a : addrToNat(a)=0 ==> !isAlloc(h, a) // a=0 is never allocated
  // 3. forall h, obj, ar, n:Nat : // incrementing heap counter with each alloc
  //      (alloc(h, obj) = ar) & (counter(h) = n) ==>  // calling alloc
  //        (counter(newHeap(ar) = n+1) &    // heap counter +1
  //        (addrToNat(newAddr(ar)) = n+1) &  // pointer points to new addr
  //        isAlloc(newHeap(ar), newAddr(ar)) & !isAlloc(h, newAddr(ar)) // new addr was previously unallocated, but now allocated
  // 4 & 5. Only between 0 < k <= counter is allocated.
  val inductionAxioms =
    /*all(List(HeapSort, AddressSort),
      isAlloc(v(0), v(1)) <=> (0 < v(1) & v(1) <= counter(v(0)))) &*/
    all(List(HeapSort, AddressSort),
      (v(0) === emptyHeap()) ==> // 1 empty heap starts from 0
      (counter(v(0)) === 0) & !_isAlloc(v(0), v(1))) & // and is unallocated
    all(List(HeapSort, ObjectSort, AllocResSort),
      (v(2) === alloc(v(0), v(1))) ==> // ar = alloc(h, obj)
      (counter(newHeap(v(2))) === counter(v(0)) + 1 & //ar.h.c = h.c+1
       newAddr(v(2)) === counter(v(0)) + 1) &
      _isAlloc(newHeap(v(2)), newAddr(v(2))))// &
    /*all(List(HeapSort, ObjectSort, AllocResSort),
      isAlloc(newHeap(alloc(v(0), v(1))), newAddr(alloc(v(0), v(1)))))*/
    /*all(List(HeapSort, ObjectSort, AllocResSort),
        (v(2) === alloc(v(0), v(1))) ==> // ar = alloc(h, obj)
        (counter(newHeap(v(2))) === counter(v(0)) + 1 & //ar.h.c = h.c+1
        newAddr(v(2)) === counter(v(0)) + 1 & //ar.a.c = h.c+1
        isAlloc(newHeap(v(2)), newAddr(v(2))) & !isAlloc(v(0), newAddr(v(2))))) &
    all(List(HeapSort, ObjectSort),
      ex(List(AllocResSort),
        v(0) === alloc(v(1), v(2))))*/
    /*all(List(HeapSort, AddressSort),
      addrToNat(v(1)) === 0 ==> !isAlloc(v(0), v(1))) & // 0 is null addr
    all(List(AddressSort),
      ex(List(IExpression.Sort.Nat),
        addrToNat(v(1)) === v(0))) &
    all(List(HeapSort),
      ex(List(IExpression.Sort.Nat),
        counter(v(1)) === v(0))) &

    all(List(AllocResSort, HeapSort), // newHeap
      ITrigger(List(newHeap(v(0))), (v(1) === newHeap(v(0))) ==>
      (counter(v(1)) === counter(newHeap(v(0)))))) &
    all(List(AllocResSort, AddressSort), //newAddr
      ITrigger(List(newAddr(v(0))), (v(1) === newAddr(v(0))) ==>
      (addrToNat(v(1)) === addrToNat(newAddr(v(0))))))*/
  /*all(List(HeapSort, ObjectSort, AllocResSort, IExpression.Sort.Nat), // 3
    ((alloc(v(0), v(1)) === v(2)) & (counter(v(0)) === v(3))) ==>
    (counter(newHeap(v(2))) === v(3) + 1) &
    (addrToNat(newAddr(v(2))) === v(3) + 1)) //&
    isAlloc(newHeap(v(2)), newAddr(v(2))) & !isAlloc(v(0), newAddr(v(2)))) &*/
  /*all(List(HeapSort, AddressSort, IExpression.Sort.Nat), // 4
    (0 < v(2) & v(2) <= counter(v(0)) & addrToNat(v(1)) === v(2)) ==>
    isAlloc(v(0), v(1))) & // 0 < k <= counter & a=k ==> isAlloc(h, a)
  all(List(HeapSort, AddressSort, IExpression.Sort.Nat), // 5
    ((v(2) <= 0) | v(2) > counter(v(0))) & addrToNat(v(1)) === v(2) ==>
    !isAlloc(v(0), v(1)))*/

  val inductionAxiomsv2 =
    counter(emptyHeap()) === 0 &
    all(List(HeapSort), counter(v(0)) >= 0) &
    all(List(HeapSort, ObjectSort, AllocResSort),
      (v(2) === alloc(v(0), v(1))) ==> // ar = alloc(h, obj)
      (counter(newHeap(v(2))) === counter(v(0)) + 1 & //ar.h.c = h.c+1
       newAddr(v(2)) === counter(v(0)) + 1))

  val theoryAxioms = factsAboutReadWriteTriggered & inductionAxiomsv2

  val (funPredicates, axioms, _, functionTranslation) = Theory.genAxioms(
    theoryFunctions = functions, theoryAxioms = theoryAxioms,
    genTotalityAxioms = false,
    order = TermOrder.EMPTY.extendPred(isAlloc).extend(nullObj))
  val f = funPredicates.toArray
  val predicates = predefPredicates ++ funPredicates
  val functionPredicateMapping = functions zip funPredicates

  /**
   * Information which of the predicates satisfy the functionality axiom;
   * at some internal points, such predicates can be handled more efficiently
   */
  val functionalPredicates = funPredicates.toSet // todo
  /**
   * Information how interpreted predicates should be handled for
   * e-matching.
   */
  val predicateMatchConfig : Signature.PredicateMatchConfig = Map() // todo
  /**
   * A list of functions that should be considered in automatic trigger
   * generation
   */
  val triggerRelevantFunctions : Set[IFunction] = functions.toSet
  /**
   * Additional axioms that are included if the option
   * <code>+genTotalityAxioms</code> is given to Princess.
   */
  val totalityAxioms = Conjunction.TRUE // todo
  /**
   * Optionally, a plug-in implementing reasoning in this theory
   */
  def plugin : Option[Plugin] = None // todo
  /**
   * Optionally, other theories that this theory depends on.
   */
  override val dependencies : Iterable[Theory] = List()

  /**
   * Optionally, a pre-processor that is applied to formulas over this
   * theory, prior to sending the formula to a prover. This method
   * will be applied very early in the translation process.
   */
  override def iPreprocess(f : IFormula, signature : Signature) = // todo
    (Preproc.visit(f, ()).asInstanceOf[IFormula], signature)

  private object Preproc extends CollectingVisitor[Unit, IExpression] {
    def postVisit(t : IExpression, arg : Unit,
                  subres : Seq[IExpression]) : IExpression = t match {
      case IAtom(`isAlloc`, Seq(h, p)) =>
        _isAlloc(h, p)
      /*case IIntFormula(IIntRelation.EqZero,
      IPlus(ar, ITimes(IdealInt.MINUS_ONE, IFunApp(`alloc`, Seq(h, o))))) =>
        _alloc(ar, h, o)
      case IIntFormula(IIntRelation.EqZero,
      IPlus(IFunApp(`alloc`, Seq(h, o)), ITimes(IdealInt.MINUS_ONE, ar))) =>
        _alloc(ar, h, o)
      case IFunApp(`counter`,
      Seq(IFunApp(`newHeap`, Seq(IFunApp(`alloc`, Seq(h, _)))))) =>
        counter(h) + 1
      case IFunApp(`newAddr`, Seq(IFunApp(`alloc`, Seq(h, _)))) =>
        counter(h) + 1*/
      case t => //println("preprocess: " + t + " " + t.getClass)
        t update subres
    }
  }
  /*alloc(h, o) = ar
  (counter(newHeap(v(2))) === counter(v(0)) + 1 & //ar.h.c = h.c+1
   newAddr(v(2)) === counter(v(0)) + 1))*/
  /**
   * Optionally, a pre-processor that is applied to formulas over this
   * theory, prior to sending the formula to a prover.
   */
  /* def preprocess(f : Conjunction, order : TermOrder) : Conjunction = f // todo
  */
  /**
   * Optionally, a plugin for the reducer applied to formulas both before
   * and during proving.
   */
  // val reducerPlugin : ReducerPluginFactory = IdentityReducerPluginFactory // todo
  /**
   * Optionally, a function evaluating theory functions applied to concrete
   * arguments, represented as constructor terms.
   */
  // def evalFun(f : IFunApp) : Option[ITerm] = None // todo
  /**
   * Optionally, a function evaluating theory predicates applied to concrete
   * arguments, represented as constructor terms.
   */
  // def evalPred(p : IAtom) : Option[Boolean] = None // todo
  /**
   * If this theory defines any <code>Theory.Decoder</code>, which
   * can translate model data into some theory-specific representation,
   * this function can be overridden to pre-compute required data
   * from a model.
   */
  /* def generateDecoderData(model : Conjunction)
  : Option[Theory.TheoryDecoderData] =
    None */
  // todo
  /**
   * Check whether we can tell that the given combination of theories is
   * sound for checking satisfiability of a problem, i.e., if proof construction
   * ends up in a dead end, can it be concluded that a problem is satisfiable.
   */
  override def isSoundForSat(theories : Seq[Theory],
                             config : Theory.SatSoundnessConfig.Value) = true
  // todo

  TheoryRegistry register this
  override def toString = "HeapTheory"
}
