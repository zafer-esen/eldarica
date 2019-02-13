/**
 * Copyright (c) 2015-2018 Philipp Ruemmer. All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 *
 * * Redistributions of source code must retain the above copyright notice, this
 *   list of conditions and the following disclaimer.
 *
 * * Redistributions in binary form must reproduce the above copyright notice,
 *   this list of conditions and the following disclaimer in the documentation
 *   and/or other materials provided with the distribution.
 *
 * * Neither the name of the authors nor the names of their
 *   contributors may be used to endorse or promote products derived from
 *   this software without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
 * AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
 * IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
 * DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE
 * FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
 * DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR
 * SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER
 * CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,
 * OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
 * OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 */

package lazabs.horn.concurrency


import ap.basetypes.IdealInt
import ap.parser._
import ap.theories.{ADT, ModuloArithmetic}
import ap.types.MonoSortedPredicate
import ap.util.Combinatorics
import lazabs.horn.bottomup.HornClauses
import lazabs.horn.preprocessor.HornPreprocessor

import concurrentC._
import concurrentC.Absyn._

import scala.collection.mutable.{ArrayBuffer, Buffer, LinkedHashSet, Stack, HashMap => MHashMap}

object CCReader {

  def apply(input : java.io.Reader, entryFunction : String,
            arithMode : ArithmeticMode.Value = ArithmeticMode.Mathematical)
           : ParametricEncoder.System = {
    def entry(parser : concurrentC.parser) = parser.pProgram
    val prog = parseWithEntry(input, entry _)
//    println(printer print prog)

    var useTime = false
    var reader : CCReader = null
    while (reader == null)
      try {
        reader = new CCReader(prog, entryFunction, useTime, arithMode)
      } catch {
        case NeedsTimeException => {
          warn("enabling time")
          useTime = true
        }
      }

    reader.system
  }

  /**
   * Parse starting at an arbitrarily specified entry point
   */
  private def parseWithEntry[T](input : java.io.Reader,
                                entry : (parser) => T) : T = {
    val l = new Yylex(new ap.parser.Parser2InputAbsy.CRRemover2 (input))
    val p = new parser(l)

    try { entry(p) } catch {
      case e : Exception =>
        throw new ParseException(
             "At line " + String.valueOf(l.line_num()) +
             ", near \"" + l.buff() + "\" :" +
             "     " + e.getMessage())
    } finally {
      input.close
    }
  }

  //////////////////////////////////////////////////////////////////////////////

  class ParseException(msg : String) extends Exception(msg)
  class TranslationException(msg : String) extends Exception(msg)
  object NeedsTimeException extends Exception

  def warn(msg : String) : Unit =
    Console.err.println("Warning: " + msg)

  object ArithmeticMode extends Enumeration {
    val Mathematical, ILP32, LP64, LLP64 = Value
  }

  //////////////////////////////////////////////////////////////////////////////

  import IExpression._

  private abstract sealed class CCType {
  }
  private abstract class CCArithType extends CCType {
    val UNSIGNED_RANGE : IdealInt
    val isUnsigned : Boolean
  }
  private case object CCVoid extends CCType {
    override def toString : String = "void"
  }
  private case object CCInt extends CCArithType {
    override def toString : String = "int"
    val UNSIGNED_RANGE : IdealInt = IdealInt("FFFFFFFF", 16) // 32bit
    val isUnsigned : Boolean = false
  }
  private case object CCUInt extends CCArithType {
    override def toString : String = "unsigned int"
    val UNSIGNED_RANGE : IdealInt = IdealInt("FFFFFFFF", 16) // 32bit
    val isUnsigned : Boolean = true
  }
  private case object CCLong extends CCArithType {
    override def toString : String = "long"
    val UNSIGNED_RANGE : IdealInt = IdealInt("FFFFFFFFFFFFFFFF", 16) // 64bit
    val isUnsigned : Boolean = false
  }
  private case object CCULong extends CCArithType {
    override def toString : String = "unsigned long"
    val UNSIGNED_RANGE : IdealInt = IdealInt("FFFFFFFFFFFFFFFF", 16) // 64bit
    val isUnsigned : Boolean = true
  }
  private case object CCLongLong extends CCArithType {
    override def toString : String = "long long"
    val UNSIGNED_RANGE : IdealInt = IdealInt("FFFFFFFFFFFFFFFF", 16) // 64bit
    val isUnsigned : Boolean = false
  }
  private case object CCULongLong extends CCArithType {
    override def toString : String = "unsigned long long"
    val UNSIGNED_RANGE : IdealInt = IdealInt("FFFFFFFFFFFFFFFF", 16) // 64bit
    val isUnsigned : Boolean = true
  }
  private trait Composite extends CCType {

  }
  private case class CCStruct(adt: ADT, name: String, fields: List[(String, CCType)])
    extends CCType with Composite{
    override def toString : String = "struct " + name + ": (" +fields.mkString + ")"

    def getFieldIndex(name: String) =  fields.indexWhere(_._1 == name)

    def getADTSelector(ind: Int) = {
      if(ind < 0)
        throw new TranslationException(
          "struct " + name + " does not contain field with index: " + ind)
      adt.selectors(0)(ind)
    }
  }
  private case object CCClock extends CCType {
    override def toString : String = "clock"
  }
  private case object CCDuration extends CCType {
    override def toString : String = "duration"
  }

  //////////////////////////////////////////////////////////////////////////////

  private abstract sealed class CCExpr(val typ : CCType) {
    def toTerm : ITerm
    def toFormula : IFormula
    def occurringConstants : Seq[ConstantTerm]
  }
  private case class CCTerm(t : ITerm, _typ : CCType)
               extends CCExpr(_typ) {
    def toTerm : ITerm = t
    def toFormula : IFormula = t match {
      case IIntLit(value) => !value.isZero
      case t =>              !eqZero(t)
    }
    def occurringConstants : Seq[ConstantTerm] =
      SymbolCollector constantsSorted t
  }
  private case class CCFormula(f : IFormula, _typ : CCType)
                     extends CCExpr(_typ) {
    def toTerm : ITerm = f match {
      case IBoolLit(true) =>  1
      case IBoolLit(false) => 0
      case f =>               ite(f, 1, 0)
    }
    def toFormula : IFormula = f
    def occurringConstants : Seq[ConstantTerm] =
      SymbolCollector constantsSorted f
  }
}

////////////////////////////////////////////////////////////////////////////////

class CCReader private (prog : Program,
                        entryFunction : String,
                        useTime : Boolean,
                        arithmeticMode : CCReader.ArithmeticMode.Value) {

  import CCReader._

  private val printer = new PrettyPrinterNonStatic

  //////////////////////////////////////////////////////////////////////////////

  import IExpression._

  private implicit def toRichType(typ : CCType) = new Object {
    import ModuloArithmetic._

    def toSort : Sort = typ match {
      case CCStruct(adt, _, _) => adt.sorts.head
      case CCDuration => Sort.Nat
      case CCClock => Sort.Integer
      case typ : CCArithType => arithmeticMode match {
      case ArithmeticMode.Mathematical => typ match {
        case typ : CCArithType if typ.isUnsigned  => Sort.Nat
        case _                                    => Sort.Integer
      }
      case ArithmeticMode.ILP32 => typ match {
        case CCInt      => SignedBVSort  (32)
        case CCUInt     => UnsignedBVSort(32)
        case CCLong     => SignedBVSort  (32)
        case CCULong    => UnsignedBVSort(32)
        case CCLongLong => SignedBVSort  (64)
        case CCULongLong=> UnsignedBVSort(64)
        case _          => Sort.Integer
      }
      case ArithmeticMode.LP64 => typ match {
        case CCInt      => SignedBVSort  (32)
        case CCUInt     => UnsignedBVSort(32)
        case CCLong     => SignedBVSort  (64)
        case CCULong    => UnsignedBVSort(64)
        case CCLongLong => SignedBVSort  (64)
        case CCULongLong=> UnsignedBVSort(64)
        case _          => Sort.Integer
      }
      case ArithmeticMode.LLP64 => typ match {
        case CCInt      => SignedBVSort  (32)
        case CCUInt     => UnsignedBVSort(32)
        case CCLong     => SignedBVSort  (32)
        case CCULong    => UnsignedBVSort(32)
        case CCLongLong => SignedBVSort  (64)
        case CCULongLong=> UnsignedBVSort(64)
        case _          => Sort.Integer
      }
    }}

    def rangePred(t : ITerm) : IFormula =
      toSort membershipConstraint t

    def newConstant(name : String) =
      toSort newConstant name

    def cast(t : ITerm) : ITerm = toSort match {
      case s : ModSort => cast2Sort(s, t)
      case _ => t
    }

    def cast2Unsigned(t : ITerm) : ITerm = toSort match {
      case SignedBVSort(n) => cast2UnsignedBV(n, t)
      case _ => t
    }

    def cast(e : CCExpr) : CCExpr = e match {
      case CCTerm(t, _)    => CCTerm(cast(t), typ)
      case CCFormula(f, _) => CCFormula(f, typ)
    }

  }

  //////////////////////////////////////////////////////////////////////////////

  private implicit def toRichExpr(expr : CCExpr) = new Object {
    def mapTerm(m : ITerm => ITerm) : CCExpr =
      // TODO: type promotion when needed
      CCTerm(expr.typ cast m(expr.toTerm), expr.typ)
  }

  //////////////////////////////////////////////////////////////////////////////

  import HornClauses.Clause

  private val globalVars = new ArrayBuffer[ConstantTerm]
  private val globalVarTypes = new ArrayBuffer[CCType]
  private val globalVarsInit = new ArrayBuffer[CCExpr]
  private var globalPreconditions : IFormula = true

  private def globalVarIndex(name : String) : Option[Int] =
    (globalVars indexWhere (_.name == name)) match {
      case -1 => None
      case i  => Some(i)
    }

  private def lookupVarNoException(name : String) : Int =
    (localVars lastIndexWhere (_.name == name)) match {
      case -1 => globalVars lastIndexWhere (_.name == name)
      case i  => i + globalVars.size
    }

  private def lookupVar(name : String) : Int =
    lookupVarNoException(name) match {
      case -1 =>
        throw new TranslationException(
                      "Symbol " + name + " is not declared")
      case i => i
    }

  private val localVars = new ArrayBuffer[ConstantTerm]
  private val localVarTypes = new ArrayBuffer[CCType]
  private val localFrameStack = new Stack[Int]

  private def addLocalVar(c : ConstantTerm, t : CCType) = {
    localVars += c
    localVarTypes += t
    variableHints += List()
  }
  private def popLocalVars(n : Int) = {
    localVars trimEnd n
    localVarTypes trimEnd n
    variableHints trimEnd n
    assert(variableHints.size == localVars.size + globalVars.size &&
           localVarTypes.size == localVars.size)
  }

  private def pushLocalFrame =
    localFrameStack push localVars.size
  private def popLocalFrame = {
    val newSize = localFrameStack.pop
    localVars reduceToSize newSize
    localVarTypes reduceToSize newSize
    variableHints reduceToSize (globalVars.size + newSize)
  }

  private def allFormalVars : Seq[ITerm] =
    globalVars.toList ++ localVars.toList
  private def allFormalVarTypes : Seq[CCType] =
    globalVarTypes.toList ++ localVarTypes.toList

  private def allFormalExprs : Seq[CCExpr] =
    ((for ((v, t) <- globalVars.iterator zip globalVarTypes.iterator)
      yield CCTerm(v, t)) ++
     (for ((v, t) <- localVars.iterator zip localVarTypes.iterator)
      yield CCTerm(v, t))).toList
  private def allVarInits : Seq[ITerm] =
    (globalVarsInit.toList map (_.toTerm)) ++ (localVars.toList map (i(_)))

  private def freeFromGlobal(t : IExpression) : Boolean =
    !ContainsSymbol(t, (s:IExpression) => s match {
                      case IConstant(c) => globalVars contains c
                      case _ => false
                    })

  private def freeFromGlobal(t : CCExpr) : Boolean = t match {
    case CCTerm(s, _) =>    freeFromGlobal(s)
    case CCFormula(f, _) => freeFromGlobal(f)
  }

  private val variableHints =
    new ArrayBuffer[Seq[HornPreprocessor.VerifHintElement]]
  private var usingInitialPredicates = false

  //////////////////////////////////////////////////////////////////////////////

  private var tempVarCounter = 0

  private def getFreshEvalVar : ConstantTerm = {
    val res = new ConstantTerm("__eval" + tempVarCounter)
    tempVarCounter = tempVarCounter + 1
    res
  }

  //////////////////////////////////////////////////////////////////////////////

  private val channels = new MHashMap[String, ParametricEncoder.CommChannel]

  private val functionDefs  = new MHashMap[String, Function_def]
  private val functionDecls = new MHashMap[String, (Direct_declarator, CCType)]
  private val structDefs    = new MHashMap[String, CCStruct]

  //////////////////////////////////////////////////////////////////////////////

  private val processes =
    new ArrayBuffer[(ParametricEncoder.Process, ParametricEncoder.Replication)]

  private val assertionClauses, timeInvariants = new ArrayBuffer[Clause]

  private val clauses =
    new ArrayBuffer[(Clause, ParametricEncoder.Synchronisation)]

  private def output(c : Clause,
                     sync : ParametricEncoder.Synchronisation =
                       ParametricEncoder.NoSync) : Unit = {
//println(c)
    clauses += ((c, sync))
  }

  private def mergeClauses(from : Int) : Unit = if (from < clauses.size - 1) {
    val concernedClauses = clauses.slice(from, clauses.size)
    val (entryClauses, transitionClauses) =
      if (concernedClauses.head._1.body.isEmpty) {
        concernedClauses partition (_._1.body.isEmpty)
      } else {
        val entryPred = concernedClauses.head._1.body.head.pred
        concernedClauses partition (_._1.body.head.pred == entryPred)
      }

    val lastClauses = transitionClauses groupBy (_._1.body.head.pred)

    clauses reduceToSize from

    def chainClauses(currentClause : Clause,
                     currentSync : ParametricEncoder.Synchronisation,
                     seenPreds : Set[Predicate]) : Unit =
      if (!currentClause.hasUnsatConstraint) {
        val headPred = currentClause.head.pred
        if (seenPreds contains headPred)
          throw new TranslationException(
            "cycles in atomic blocks are not supported yet")

        (lastClauses get headPred) match {
          case Some(cls) => {
            if (timeInvariants exists (_.predicates contains headPred))
              throw new TranslationException(
                "time invariants in atomic blocks are not supported")

            for ((c, sync) <- cls)
              if (currentSync == ParametricEncoder.NoSync)
                chainClauses(c mergeWith currentClause, sync,
                             seenPreds + headPred)
              else if (sync == ParametricEncoder.NoSync)
                chainClauses(c mergeWith currentClause, currentSync,
                             seenPreds + headPred)
              else
                throw new TranslationException(
                  "Cannot execute " + currentSync + " and " + sync +
                  " in one step")

            // add further assertion clauses, since some intermediate
            // states disappear
            for (c <- assertionClauses.toList)
              if (c.bodyPredicates contains headPred) {
                if (currentSync != ParametricEncoder.NoSync)
                  throw new TranslationException(
                    "Cannot execute " + currentSync + " and an assertion" +
                    " in one step")
                val newAssertionClause = c mergeWith currentClause
                if (!newAssertionClause.hasUnsatConstraint)
                  assertionClauses += newAssertionClause
              }
          }
          case None =>
            clauses += ((currentClause, currentSync))
        }
      }

    for ((c, sync) <- entryClauses)
      chainClauses(c, sync, Set())
  }

  private var atomicMode = false

  private def inAtomicMode[A](comp : => A) : A = {
      val oldAtomicMode = atomicMode
      atomicMode = true
      val res = comp
      atomicMode = oldAtomicMode
      res
  }

  private var prefix : String = ""
  private var locationCounter = 0

  private def setPrefix(pref : String) = {
    prefix = pref
    locationCounter = 0
  }

  private def newPred : Predicate = newPred(0)

  private def newPred(extraArgs : Int) : Predicate = {
    import HornPreprocessor.{VerifHintTplElement, VerifHintTplEqTerm}

    val res = MonoSortedPredicate(prefix + locationCounter,
                                  (allFormalVarTypes map (_.toSort)) ++
                                  (for (_ <- 0 until extraArgs)
                                   yield Sort.Integer))
    locationCounter = locationCounter + 1

    val hints = for (s <- variableHints; p <- s) yield p
    val allHints =
      if (hints exists (_.isInstanceOf[VerifHintTplElement])) {
        // make sure that all individual variables exist as templates
        val coveredVars =
          (for (VerifHintTplEqTerm(IVariable(n), _) <- hints.iterator)
           yield n).toSet
        hints ++ (for (n <- (0 until res.arity).iterator;
                       if (!(coveredVars contains n)))
                  yield VerifHintTplEqTerm(v(n), 10000))
      } else {
        hints
      }

    predicateHints.put(res, allHints)
    res
  }

  private val predicateHints =
    new MHashMap[Predicate, Seq[HornPreprocessor.VerifHintElement]]

  //////////////////////////////////////////////////////////////////////////////

  /** Implicit conversion so that we can get a Scala-like iterator from a
    * a Java list */
  import scala.collection.JavaConversions.{asScalaBuffer, asScalaIterator}

  // Reserve two variables for time
  val GT = CCClock newConstant "_GT"
  val GTU = Sort.Integer newConstant "_GTU"

  if (useTime) {
    globalVars += GT
    globalVarTypes += CCClock
    globalVarsInit += CCTerm(GT, CCClock)
    globalVars += GTU
    globalVarTypes += CCInt
    globalVarsInit += CCTerm(GTU, CCInt)
    variableHints += List()
    variableHints += List()
  }

  private def translateProgram : Unit = {
    // First collect all declarations. This is a bit more
    // generous than actual C semantics, where declarations
    // have to be in the right order

    atomicMode = true
    val globalVarSymex = Symex(null)

    for (decl <- prog.asInstanceOf[Progr].listexternal_declaration_)
      decl match {
        case decl : Global =>
          collectVarDecls(decl.dec_, true, globalVarSymex)

        case decl : Chan =>
          for (name <- decl.chan_def_.asInstanceOf[AChan].listcident_) {
            if (channels contains name)
              throw new TranslationException(
                "Channel " + name + " is already declared")
            channels.put(name, new ParametricEncoder.CommChannel(name))
          }

        case decl : Afunc => {
          val name = decl.function_def_ match {
            case f : NewFunc => getName(f.declarator_)
            case f : NewFuncInt => getName(f.declarator_)
          }

          if (functionDefs contains name)
            throw new TranslationException(
              "Function " + name + " is already declared")
          functionDefs.put(name, decl.function_def_)
        }

        case _ =>
          // nothing
      }

    if (useTime)
      // prevent time variables from being initialised twice
      globalVarsInit ++= (globalVarSymex.getValues drop 2)
    else
      globalVarsInit ++= globalVarSymex.getValues

    globalPreconditions = globalPreconditions &&& globalVarSymex.getGuard

    // then translate the threads
    atomicMode = false

    for (decl <- prog.asInstanceOf[Progr].listexternal_declaration_)
      decl match {
        case decl : Athread =>
          decl.thread_def_ match {
            case thread : SingleThread => {
              setPrefix(thread.cident_)
              val translator = FunctionTranslator.apply
              translator translateNoReturn thread.compound_stm_
              processes += ((clauses.toList, ParametricEncoder.Singleton))
              clauses.clear
            }
            case thread : ParaThread => {
              setPrefix(thread.cident_2)
              pushLocalFrame
              addLocalVar(CCInt newConstant thread.cident_1, CCInt)
              val translator = FunctionTranslator.apply
              translator translateNoReturn thread.compound_stm_
              processes += ((clauses.toList, ParametricEncoder.Infinite))
              clauses.clear
              popLocalFrame
            }
          }

        case _ =>
          // nothing
      }

    // is there a global entry point in the program?
    (functionDefs get entryFunction) match {
      case Some(funDef) => {
        setPrefix(entryFunction)

        pushLocalFrame
        val exitPred = newPred(1)
        val stm = pushArguments(funDef)

        val translator = FunctionTranslator(exitPred)
        translator.translateWithReturn(stm)

        processes += ((clauses.toList, ParametricEncoder.Singleton))
        clauses.clear

        popLocalFrame
      }
      case None =>
        warn("entry function \"" + entryFunction + "\" not found")
    }

    // remove assertions that are no longer connected to predicates
    // actually occurring in the system

    val allPreds =
      (for ((cls, _) <- processes.iterator;
            (c, _) <- cls.iterator;
            p <- c.predicates.iterator)
       yield p).toSet

    val remainingAssertions =
      assertionClauses filter { c => c.bodyPredicates subsetOf allPreds }
    assertionClauses.clear
    assertionClauses ++= remainingAssertions
  }

  //////////////////////////////////////////////////////////////////////////////

  private def collectVarDecls(dec : Dec,
                              global : Boolean,
                              values : Symex) : Unit = dec match {
    case decl : Declarators => {
      val typ = getType(decl.listdeclaration_specifier_)

      for (initDecl <- decl.listinit_declarator_) {
        var isVariable = false

        initDecl match {
          case _ : OnlyDecl | _ : HintDecl => {
            val declarator = initDecl match {
              case initDecl : OnlyDecl => initDecl.declarator_
              case initDecl : HintDecl => initDecl.declarator_
            }
            val name = getName(declarator)
            val directDecl =
              declarator.asInstanceOf[NoPointer].direct_declarator_

            directDecl match {
              case _ : NewFuncDec /* | _ : OldFuncDef */ | _ : OldFuncDec =>
                functionDecls.put(name, (directDecl, typ))
              case _ => {
                isVariable = true
                val c = typ newConstant name
                if (global) {
                  globalVars += c
                  globalVarTypes += typ
                  variableHints += List()
                  typ match {
                    case typ : CCArithType =>
                      // global variables are initialised with 0
                      values addValue CCTerm(0, typ)
                    case typ => {
                      values addValue CCTerm(c, typ)
                      values addGuard (typ rangePred c)
                    }
                  }
                } else {
                  addLocalVar(c, typ)
                  values addValue CCTerm(c, typ)
                  values addGuard (typ rangePred c)
                }
              }
            }
          }

          case _ : InitDecl | _ : HintInitDecl => {
            val (declarator, initializer) = initDecl match {
              case initDecl : InitDecl =>
                (initDecl.declarator_, initDecl.initializer_)
              case initDecl : HintInitDecl =>
                (initDecl.declarator_, initDecl.initializer_)
            }

            isVariable = true
            val c = typ newConstant getName(declarator)
            val (initValue, initGuard) = initializer match {
              case init : InitExpr =>
                if (init.exp_.isInstanceOf[Enondet])
                  (CCTerm(c, typ), typ rangePred c)
                else
                  (values eval init.exp_, i(true))
            }

            if (global) {
              globalVars += c
              globalVarTypes += typ
              variableHints += List()
            } else {
              addLocalVar(c, typ)
            }

            typ match {
              case CCClock =>
                values addValue translateClockValue(initValue)
              case CCDuration =>
                values addValue translateDurationValue(initValue)
              case typ =>
                values addValue (typ cast initValue)
            }

            values addGuard initGuard
          }
        }

        if (isVariable) {
          // parse possible model checking hints
          val hints : Seq[Abs_hint] = initDecl match {
            case decl : HintDecl => decl.listabs_hint_
            case decl : HintInitDecl => decl.listabs_hint_
            case _ => List()
          }

          processHints(hints)
        }
      }
    }
    case nodecl : NoDeclarator => {
      getType(nodecl.listdeclaration_specifier_) // TODO: is calling getType here ok? this is done just to create struct
    }
  }

  private def processHints(hints : Seq[Abs_hint]) : Unit =
          if (!hints.isEmpty) {
            import HornPreprocessor.{VerifHintInitPred,
                                     VerifHintTplPred, VerifHintTplEqTerm}

            val hintSymex = Symex(null)
            hintSymex.saveState

            val subst =
              (for ((c, n) <-
                      (globalVars.iterator ++ localVars.iterator).zipWithIndex)
               yield (c -> v(n))).toMap

            val hintEls =
              for (hint <- hints;
                   cHint = hint.asInstanceOf[Comment_abs_hint];
                   hint_clause <- cHint.listabs_hint_clause_;
                   if (hint_clause.isInstanceOf[Predicate_hint]);
                   pred_hint = hint_clause.asInstanceOf[Predicate_hint];
                   cost = pred_hint.maybe_cost_ match {
                     case c : SomeCost => c.unboundedinteger_.toInt
                     case _ : NoCost => 1
                   };
                   e <- inAtomicMode(hintSymex evalList pred_hint.exp_))
              yield pred_hint.cident_ match {
                case "predicates" => {
                  usingInitialPredicates = true
                  VerifHintInitPred(ConstantSubstVisitor(e.toFormula, subst))
                }
                case "predicates_tpl" =>
                  VerifHintTplPred(ConstantSubstVisitor(e.toFormula, subst),
                                   cost)
                case "terms_tpl" =>
                  VerifHintTplEqTerm(ConstantSubstVisitor(e.toTerm, subst),
                                     cost)
                case _ =>
                  throw new TranslationException("cannot handle hint " +
                                                 pred_hint.cident_)
              }

            if (!hintSymex.atomValuesUnchanged)
              throw new TranslationException(
                "Hints are not side effect-free: " +
                (for (h <- hints.iterator)
                 yield (printer print h)).mkString(""))

            variableHints(variableHints.size - 1) = hintEls
          }

  // TODO: review below function
  private def getName(decl : Struct_dec) : String = decl match {
    case decl : Structen => getName(
      decl.liststruct_declarator_.iterator.next().asInstanceOf[Decl].declarator_)
  }

  private def getName(decl : Declarator) : String = decl match {
    case decl : NoPointer => getName(decl.direct_declarator_)
  }

  private def getName(decl : Direct_declarator) : String = decl match {
    case decl : Name      => decl.cident_
    case decl : ParenDecl => getName(decl.declarator_)
    case dec : NewFuncDec => getName(dec.direct_declarator_)
//    case dec : OldFuncDef => getName(dec.direct_declarator_)
    case dec : OldFuncDec => getName(dec.direct_declarator_)
  }

  private def getType(specs : Seq[Declaration_specifier]) : CCType =
    getType(for (specifier <- specs.iterator;
                 if (specifier.isInstanceOf[Type]))
            yield specifier.asInstanceOf[Type].type_specifier_)

  private def getType(name : Type_name) : CCType = name match {
    case name : PlainType =>
      getType(for (qual <- name.listspec_qual_.iterator;
                   if (qual.isInstanceOf[TypeSpec]))
              yield qual.asInstanceOf[TypeSpec].type_specifier_)
  }

  private def getType(name : Struct_dec) : CCType = name match {
    case name : Structen =>
      getType(for (qual <- name.listspec_qual_.iterator;
                   if (qual.isInstanceOf[TypeSpec]))
        yield qual.asInstanceOf[TypeSpec].type_specifier_)
  }

  private def getType(specs : Iterator[Type_specifier]) : CCType = {
    // by default assume that the type is int
    var typ : CCType = CCInt

    for (specifier <- specs)
      specifier match {
            case _ : Tvoid =>
              typ = CCVoid
            case _ : Tint =>
              // ignore
            case _ : Tchar =>
              // ignore
            case _ : Tsigned =>
              typ = CCInt
            case _ : Tunsigned =>
              typ = CCUInt
            case _ : Tlong if (typ == CCInt) =>
              typ = CCLong
            case _ : Tlong if (typ == CCUInt) =>
              typ = CCULong
            case _ : Tlong if (typ == CCLong) =>
              typ = CCLongLong
            case _ : Tlong if (typ == CCULong) =>
              typ = CCULongLong
            case structOrUnion : Tstruct => //does not currently support union

              /* Three possibilities:
                1. Tag.      Struct_or_union_spec ::= Struct_or_union CIdent "{" [Struct_dec] "}" ;
                2. Unique.   Struct_or_union_spec ::= Struct_or_union "{" [Struct_dec] "}";
                3. TagType.  Struct_or_union_spec ::= Struct_or_union CIdent ;

                1. Tag     : Struct definition: introduces the new type struct name and defines its meaning
                2. Unique  : means that this is an anonymous struct, and must be defined inside another struct.
                3. TagType : Two possibilities:
                             a) If used on a line of its own as in struct name ;, declares but doesn't define the struct
                               name (see forward declaration).
                             b) In other contexts, names the previously-declared struct.
               */

              structOrUnion.struct_or_union_spec_ match {
                case spec : Tag => // struct definition
                  val structName = spec.cident_
                  if (structDefs contains structName)
                    throw new TranslationException(
                      "struct " + structName + " is already declared")

                  val fields = spec.liststruct_dec_
                  val fieldList : List[(String, CCType)] = (for ( field <- fields ) yield
                    (getName(field.asInstanceOf[Structen]),
                      getType(field.asInstanceOf[Structen]))).toList  // .asInstanceOf[ArrayBuffer[String]].toList

                  val ADTFieldList : List[(String, ap.theories.ADT.OtherSort)] =
                    for((fieldName, fieldType) <- fieldList)
                      yield (fieldName, ADT.OtherSort(fieldType.toSort))

                  val structADT =
                    new ADT(List("struct" + structName),
                      List((structName, ADT.CtorSignature(ADTFieldList, ADT.ADTSort(0)))))

                  val newStruct = CCStruct(structADT, structName, fieldList)
                  structDefs += (structName -> newStruct)
                  typ = newStruct
                case spec : Unique => // anonymous struct (i.e. a definition inside another struct)
                  println("Unique types are not supported yet") // TODO handle unique types
                case spec : TagType => // if struct not defined yet, forward declaration; else, Type_specifier
                  val structName = spec.cident_
                  structDefs.get(structName) match {
                    case Some(struct) => typ = struct
                    case None => throw new TranslationException( // TODO handle forward declarations here, currently not supported
                      "struct " + structName + " is used without being defined first! (Forward declarations " +
                        "are not supported yet.)")
                  }
              }
            case _ : Tclock => {
              if (!useTime)
                throw NeedsTimeException
              typ = CCClock
            }
            case _ : Tduration => {
              if (!useTime)
                throw NeedsTimeException
              typ = CCDuration
            }
            case x => {
              warn("type " + (printer print x) +
                   " not supported, assuming int")
              typ = CCInt
            }
          }

    typ
  }

  private def getType(functionDef : Function_def) : CCType =
    functionDef match {
      case f : NewFunc    => getType(f.listdeclaration_specifier_)
      case _ : NewFuncInt => CCInt
    }

  private def translateClockValue(expr : CCExpr) : CCExpr = {
    if (!useTime)
      throw NeedsTimeException
    expr.toTerm match {
      case IIntLit(v) if (expr.typ.isInstanceOf[CCArithType]) =>
        CCTerm(GT + GTU*(-v), CCClock)
      case t if (expr.typ == CCClock) =>
        CCTerm(t, CCClock)
      case t if (expr.typ == CCDuration) =>
        CCTerm(GT - t, CCClock)
      case t =>
        throw new TranslationException(
          "clocks can only be set to or compared with integers")
    }
  }

  private def translateDurationValue(expr : CCExpr) : CCExpr = {
    if (!useTime)
      throw NeedsTimeException
    expr.toTerm match {
      case _ if (expr.typ == CCDuration) =>
        expr
      case IIntLit(v) if (expr.typ.isInstanceOf[CCArithType]) =>
        CCTerm(GTU*v, CCDuration)
      case t =>
        throw new TranslationException(
          "duration variable cannot be set or compared to " + t)
    }
  }

  //////////////////////////////////////////////////////////////////////////////

  private object Symex {
    def apply(initPred : Predicate) = {
      val values = new ArrayBuffer[CCExpr]
      values ++= allFormalExprs
      new Symex(initPred, values)
    }
  }

  private def atom(pred : Predicate, args : Seq[ITerm]) =
    IAtom(pred, args take pred.arity)

  private class Symex private (oriInitPred : Predicate,
                               values : Buffer[CCExpr]) {
    private var guard : IFormula = true

    def addGuard(f : IFormula) : Unit = {
      guard = guard &&& f
      touchedGlobalState =
        touchedGlobalState || !freeFromGlobal(f)
    }

    def getGuard = guard

    private var initAtom =
      if (oriInitPred == null)
        null
      else
        atom(oriInitPred, allFormalVars)
    private def initPred = initAtom.pred

    private val savedStates = new Stack[(IAtom, Seq[CCExpr], IFormula, Boolean)]
    def saveState =
      savedStates push ((initAtom, values.toList, guard, touchedGlobalState))
    def restoreState = {
      val (oldAtom, oldValues, oldGuard, oldTouched) = savedStates.pop
      initAtom = oldAtom
      values.clear
      oldValues copyToBuffer values
      popLocalVars(localVars.size - values.size + globalVars.size)
      guard = oldGuard
      touchedGlobalState = oldTouched
    }

    def atomValuesUnchanged = {
      val (oldAtom, oldValues, _, _) = savedStates.top
      initAtom == oldAtom &&
      ((values.iterator zip oldValues.iterator) forall {
         case (x, y) => x == y
       })
    }

    private var touchedGlobalState : Boolean = false

    private def maybeOutputClause : Unit =
      if (!atomicMode && touchedGlobalState) outputClause

    private def pushVal(v : CCExpr) = {
      val c = getFreshEvalVar
// println("push " + v + " -> " + c)

      addValue(v)
      // reserve a local variable, in case we need one later
      addLocalVar(c, v.typ)

      if (usingInitialPredicates) {
        import HornPreprocessor.VerifHintInitPred

        // if the pushed value refers to other variables,
        // add initial predicates that relate the values of
        // temporary variables with the original variables
        //
        // TODO: this is currently not very effective ...

        val varMapping =
          (for (d <- v.occurringConstants.iterator;
                index = lookupVarNoException(d.name))
           yield (d -> index)).toMap

        if (varMapping forall { case (_, ind) => ind >= 0 }) {
          val defTerm =
            ConstantSubstVisitor(v.toTerm,
                                 varMapping mapValues (IExpression.v(_)))
          val rhs = IExpression.v(variableHints.size - 1)

          if (defTerm != rhs) {
            val defEq = defTerm === rhs
            variableHints(variableHints.size - 1) =
              List(VerifHintInitPred(defEq))
          }
        }
      }
    }

    private def pushFormalVal(t : CCType) = {
      val c = getFreshEvalVar
      addLocalVar(c, t)
      addValue(CCTerm(c, t))
      addGuard(t rangePred c)
    }

    private def popVal = {
      val res = values.last
//println("pop " + res)
      values trimEnd 1
      popLocalVars(1)
      res
    }
    private def topVal = values.last

    private def outputClause : Unit = outputClause(newPred)

    def genClause(pred : Predicate) : Clause = {
      if (initAtom == null)
        throw new TranslationException("too complicated initialiser")
      Clause(asAtom(pred), List(initAtom), guard)
    }

    def outputClause(pred : Predicate,
                     sync : ParametricEncoder.Synchronisation =
                       ParametricEncoder.NoSync) : Unit = {
      val c = genClause(pred)
      if (!c.hasUnsatConstraint)
        output(c, sync)
      resetFields(pred)
    }

    def outputClause(headAtom : IAtom) : Unit = {
      val c = Clause(headAtom, List(initAtom), guard)
      if (!c.hasUnsatConstraint)
        output(c)
    }

    def resetFields(pred : Predicate) : Unit = {
      initAtom = atom(pred, allFormalVars)
      guard = true
      touchedGlobalState = false
      for ((e, i) <- allFormalExprs.iterator.zipWithIndex)
        values(i) = e
    }

    def outputITEClauses(cond : IFormula,
                         thenPred : Predicate, elsePred : Predicate) = {
      saveState
      addGuard(cond)
      outputClause(thenPred)
      restoreState
      addGuard(~cond)
      outputClause(elsePred)
    }

    def addValue(t : CCExpr) = {
      values += t
      touchedGlobalState = touchedGlobalState || !freeFromGlobal(t)
    }

    private def getValue(name : String) =
      values(lookupVar(name))
    private def setValue(name : String, t : CCExpr) = {
      val ind = lookupVar(name)
      values(ind) = t
      touchedGlobalState =
        touchedGlobalState || ind < globalVars.size || !freeFromGlobal(t)
    }

    def getVarType (name: String) = {
      val ind = lookupVar(name)
      if (ind < globalVars.size) globalVarTypes(ind)
      else localVarTypes(ind - globalVarTypes.size)
    }

    def getValues : Seq[CCExpr] =
      values.toList
    def getValuesAsTerms : Seq[ITerm] =
      for (expr <- values.toList) yield expr.toTerm

    def asAtom(pred : Predicate) = atom(pred, getValuesAsTerms)

    private def asLValue(exp : Exp) : String = exp match {
      case exp : Evar => exp.cident_
      case exp =>
        throw new TranslationException(
                    "Can only handle assignments to variables, not " +
                    (printer print exp))
    }

    private def isClockVariable(exp : Exp) : Boolean = exp match {
      case exp : Evar => getValue(exp.cident_).typ == CCClock
      case exp : Eselect => false
      case exp =>
        throw new TranslationException(
                    "Can only handle assignments to variables, not " +
                    (printer print exp))
    }

    private def isDurationVariable(exp : Exp) : Boolean = exp match {
      case exp : Evar => getValue(exp.cident_).typ == CCDuration
      case exp : Eselect => false //added case - zafer
      case exp =>
        throw new TranslationException(
                    "Can only handle assignments to variables, not " +
                    (printer print exp))
    }

    def eval(exp : Exp) : CCExpr = {
      val initSize = values.size
      evalHelp(exp)
      val res = popVal
      assert(initSize == values.size)
      res
    }

    def evalList(exp : Exp) : Seq[CCExpr] = {
      val res = new ArrayBuffer[CCExpr]

      var e = exp
      while (e.isInstanceOf[Ecomma]) {
        val ec = e.asInstanceOf[Ecomma]
        res += eval(ec.exp_2)
        e = ec.exp_1
      }

      res += eval(e)

      res.toList
    }

    def atomicEval(exp : Exp) : CCExpr = atomicEval(List(exp))

    def atomicEval(exps : Seq[Exp]) : CCExpr = {
      val currentClauseNum = clauses.size
      val initSize = values.size

      inAtomicMode {
        pushVal(CCFormula(true, CCVoid))
        for (exp <- exps) {
          popVal
          evalHelp(exp)
        }
      }

      if (currentClauseNum != clauses.size) {
        outputClause
        mergeClauses(currentClauseNum)
      }

      val res = popVal
      assert(initSize == values.size)
      res
    }

    private def evalHelp(exp : Exp) : Unit = exp match {
      case exp : Ecomma => {
        evalHelp(exp.exp_1)
        popVal
        maybeOutputClause
        evalHelp(exp.exp_2)
      }
      case exp : Eassign if (exp.assignment_op_.isInstanceOf[Assign] &&
                             isClockVariable(exp.exp_1)) => {
        evalHelp(exp.exp_2)
        maybeOutputClause
        setValue(asLValue(exp.exp_1), translateClockValue(topVal))
      }
      case exp : Eassign if (exp.assignment_op_.isInstanceOf[Assign] &&
                             isDurationVariable(exp.exp_1)) => {
        evalHelp(exp.exp_2)
        maybeOutputClause
        setValue(asLValue(exp.exp_1), translateDurationValue(topVal))
      }
      case exp : Eassign if (exp.assignment_op_.isInstanceOf[Assign]) => {
        eval(exp.exp_2) //this put 42 in stack
        maybeOutputClause
        evalHelp(exp.exp_1) //this should prepare rhs recursively
                // b(s) ---> c(b(s)) ---> S2

        val (actualLHS, fields) = {
          var lhs = exp.exp_1
          var fields = List[String]()

          while (lhs.isInstanceOf[Eselect]) {
            fields = lhs.asInstanceOf[Eselect].cident_ :: fields
            lhs = lhs.asInstanceOf[Eselect].exp_
          }
          (lhs, fields)
        }
        var rhs = topVal.toTerm //only if there is a select
        val lhsString = asLValue(actualLHS)
        val lhs = getValue(lhsString)
        var curType = getVarType(lhsString)

        for (field <- fields) {
          val structType = curType.asInstanceOf[CCStruct]
          val structADT = structType.adt
          val ind = structType.getFieldIndex(field)
          val ctorArgs =
            for (n <- structType.fields.indices) yield {
              if (n == ind) rhs
              else structType.getADTSelector(n)(lhs.toTerm)
            }
          rhs = structADT.constructors.head(ctorArgs:_*)
        }

        setValue(lhsString, CCTerm(rhs, getVarType(lhsString)))
      }
      case exp : Eassign => {
        evalHelp(exp.exp_1)
        maybeOutputClause
        evalHelp(exp.exp_2)
        maybeOutputClause
        val rhsE = popVal
        val rhs = rhsE.toTerm
        val lhsE = popVal
        val lhs = lhsE.toTerm
	if (lhsE.typ == CCClock || lhsE.typ == CCDuration)
          throw new TranslationException("unsupported assignment to clock")
        val newVal = CCTerm(lhsE.typ cast (exp.assignment_op_ match {
          case _ : AssignMul =>
            ap.theories.nia.GroebnerMultiplication.mult(lhs, rhs)
          case _ : AssignDiv =>
            ap.theories.nia.GroebnerMultiplication.tDiv(lhs, rhs)
          case _ : AssignMod =>
            ap.theories.nia.GroebnerMultiplication.tMod(lhs, rhs)
          case _ : AssignAdd =>
            lhs + rhs
          case _ : AssignSub =>
            lhs - rhs
          case _ : AssignLeft =>
            ModuloArithmetic.bvshl(lhsE.typ cast2Unsigned lhs,
                                   lhsE.typ cast2Unsigned rhs)
          case _ : AssignRight =>
            ModuloArithmetic.bvashr(lhsE.typ cast2Unsigned lhs,
                                    lhsE.typ cast2Unsigned rhs)
          case _ : AssignAnd =>
            ModuloArithmetic.bvand(lhsE.typ cast2Unsigned lhs,
                                   lhsE.typ cast2Unsigned rhs)
          case _ : AssignXor =>
            ModuloArithmetic.bvxor(lhsE.typ cast2Unsigned lhs,
                                   lhsE.typ cast2Unsigned rhs)
          case _ : AssignOr =>
            ModuloArithmetic.bvand(lhsE.typ cast2Unsigned lhs,
                                   lhsE.typ cast2Unsigned rhs)
        }), lhsE.typ)
        pushVal(newVal)
        setValue(asLValue(exp.exp_1), newVal)
      }
      case exp : Econdition => {
        val cond = eval(exp.exp_1).toFormula

        saveState
        addGuard(cond)
        evalHelp(exp.exp_2)
        outputClause
        val intermediatePred = initPred

        restoreState
        addGuard(~cond)
        evalHelp(exp.exp_3)
        outputClause(intermediatePred)
      }
      case exp : Elor => {
        evalHelp(exp.exp_1)
        maybeOutputClause
        val cond = popVal.toFormula

        saveState
        addGuard(~cond)
        val newGuard = guard
        evalHelp(exp.exp_2)
        maybeOutputClause

        // check whether the second expression had side-effects
        if ((guard eq newGuard) && atomValuesUnchanged) {
          val cond2 = popVal.toFormula
          restoreState
          pushVal(CCFormula(cond ||| cond2, CCInt))
        } else {
          outputClause
          val intermediatePred = initPred

          restoreState
          addGuard(cond)
          pushVal(CCFormula(true, CCInt))
          outputClause(intermediatePred)
        }
      }
      case exp : Eland => {
        evalHelp(exp.exp_1)
        maybeOutputClause
        val cond = popVal.toFormula

        saveState
        addGuard(cond)
        val newGuard = guard
        evalHelp(exp.exp_2)
        maybeOutputClause

        // check whether the second expression had side-effects
        if ((guard eq newGuard) && atomValuesUnchanged) {
          val cond2 = popVal.toFormula
          restoreState
          pushVal(CCFormula(cond &&& cond2, CCInt))
        } else {
          outputClause
          val intermediatePred = initPred

          restoreState
          addGuard(~cond)
          pushVal(CCFormula(false, CCInt))
          outputClause(intermediatePred)
        }
      }
      case exp : Ebitor =>
        strictUnsignedBinFun(exp.exp_1, exp.exp_2, ModuloArithmetic.bvor(_, _))
      case exp : Ebitexor =>
        strictUnsignedBinFun(exp.exp_1, exp.exp_2, ModuloArithmetic.bvxor(_, _))
      case exp : Ebitand =>
        strictUnsignedBinFun(exp.exp_1, exp.exp_2, ModuloArithmetic.bvand(_, _))
      case exp : Eeq =>
        strictBinPred(exp.exp_1, exp.exp_2, _ === _)
      case exp : Eneq =>
        strictBinPred(exp.exp_1, exp.exp_2, _ =/= _)
      case exp : Elthen =>
        strictBinPred(exp.exp_1, exp.exp_2, _ < _)
      case exp : Egrthen =>
        strictBinPred(exp.exp_1, exp.exp_2, _ > _)
      case exp : Ele =>
        strictBinPred(exp.exp_1, exp.exp_2, _ <= _)
      case exp : Ege =>
        strictBinPred(exp.exp_1, exp.exp_2, _ >= _)
      case exp : Eleft =>
        strictUnsignedBinFun(exp.exp_1, exp.exp_2, ModuloArithmetic.bvshl(_, _))
      case exp : Eright =>
        strictUnsignedBinFun(exp.exp_1, exp.exp_2, ModuloArithmetic.bvashr(_, _))
      case exp : Eplus =>
        strictBinFun(exp.exp_1, exp.exp_2, _ + _)
      case exp : Eminus =>
        strictBinFun(exp.exp_1, exp.exp_2, _ - _)
      case exp : Etimes =>
        strictBinFun(exp.exp_1, exp.exp_2, {
          (x : ITerm, y : ITerm) =>
            ap.theories.nia.GroebnerMultiplication.mult(x, y)
        })
      case exp : Ediv =>
        strictBinFun(exp.exp_1, exp.exp_2, {
          (x : ITerm, y : ITerm) =>
            ap.theories.nia.GroebnerMultiplication.tDiv(x, y)
        })
      case exp : Emod =>
        strictBinFun(exp.exp_1, exp.exp_2, {
          (x : ITerm, y : ITerm) =>
            ap.theories.nia.GroebnerMultiplication.tMod(x, y)
        })
      case exp : Etypeconv => {
        evalHelp(exp.exp_)
        pushVal(convertType(popVal, getType(exp.type_name_)))
      }
      case exp : Epreinc => {
        evalHelp(exp.exp_)
        maybeOutputClause
        pushVal(popVal mapTerm (_ + 1))
        setValue(asLValue(exp.exp_), topVal)
      }
      case exp : Epredec => {
        evalHelp(exp.exp_)
        maybeOutputClause
        pushVal(popVal mapTerm (_ - 1))
        setValue(asLValue(exp.exp_), topVal)
      }
      case exp : Epreop => {
        evalHelp(exp.exp_)
        exp.unary_operator_ match {
//          case _ : Address.     Unary_operator ::= "&" ;
//          case _ : Indirection. Unary_operator ::= "*" ;
          case _ : Plus       => // nothing
          case _ : Negative   => pushVal(popVal mapTerm (-(_)))
//          case _ : Complement.  Unary_operator ::= "~" ;
          case _ : Logicalneg => pushVal(CCFormula(~popVal.toFormula, CCInt))
        }
      }
//      case exp : Ebytesexpr.  Exp15 ::= "sizeof" Exp15;
//      case exp : Ebytestype.  Exp15 ::= "sizeof" "(" Type_name ")";
//      case exp : Earray.      Exp16 ::= Exp16 "[" Exp "]" ;

      case exp : Efunk => {
        // inline the called function
        val name = printer print exp.exp_
        outputClause
        callFunctionInlining(name, initPred)
      }

      case exp : Efunkpar => (printer print exp.exp_) match {
        case "__VERIFIER_error" if (exp.listexp_.isEmpty) => {
          import HornClauses._
          assertionClauses += (false :- (initAtom, guard))
          pushVal(CCFormula(true, CCInt))
        }
        case "assert" | "static_assert" | "__VERIFIER_assert"
                          if (exp.listexp_.size == 1) => {
          import HornClauses._
          val property = atomicEval(exp.listexp_.head).toFormula
          assertionClauses += (property :- (initAtom, guard))
          pushVal(CCFormula(true, CCInt))
        }
        case "assume" | "__VERIFIER_assume"
                          if (exp.listexp_.size == 1) => {
          addGuard(atomicEval(exp.listexp_.head).toFormula)
          pushVal(CCFormula(true, CCInt))
        }
        case cmd@("chan_send" | "chan_receive") if (exp.listexp_.size == 1) => {
          val name = printer print exp.listexp_.head
          (channels get name) match {
            case Some(chan) => {
              val sync = cmd match {
                case "chan_send" =>    ParametricEncoder.Send(chan)
                case "chan_receive" => ParametricEncoder.Receive(chan)
              }
              outputClause(newPred, sync)
              pushVal(CCFormula(true, CCInt))
            }
            case None =>
              throw new TranslationException(
                name + " is not a declared channel")
          }
        }
        case name => {
          // then we inline the called function

          // evaluate the arguments
          for (e <- exp.listexp_)
            evalHelp(e)
          outputClause

          val functionEntry = initPred

          // get rid of the local variables, which are later
          // replaced with the formal arguments
          for (e <- exp.listexp_)
            popVal

          callFunctionInlining(name, functionEntry)
        }
      }

      case exp : Eselect => { //Exp16 ::= Exp16 "." Ident;
        val subexpr = eval(exp.exp_)
        val field = exp.cident_
        subexpr.typ match {
          case structType: CCStruct => {
            val ind = structType.getFieldIndex(field)
            val fieldType = structType.fields(ind)._2
            val sel = structType.getADTSelector(ind)
            pushVal(CCTerm(sel(subexpr.toTerm), fieldType))
          }
          case _ =>
            throw new TranslationException("Eselect is currently " +
              "only implemented for structs")
        }
      }
//      case exp : Epoint.      Exp16 ::= Exp16 "->" Ident;
      case exp : Epostinc => {
        exp.exp_ match {
          case select: Eselect => {
            val subexpr = eval(exp.exp_)
            maybeOutputClause
            val field = select.cident_
            val (actualLHS, fields) = {
              var lhs: Exp = select
              var fields = List[String]()

              while (lhs.isInstanceOf[Eselect]) {
                fields = lhs.asInstanceOf[Eselect].cident_ :: fields
                lhs = lhs.asInstanceOf[Eselect].exp_
              }
              (lhs, fields)
            }
            var rhs = subexpr.toTerm // mapTerm (_ + 1)
            val lhsString = asLValue(actualLHS)
            val lhs = getValue(lhsString)
            val curType = getVarType(lhsString)

            for (field <- fields) {
              val structType = curType.asInstanceOf[CCStruct]
              val structADT = structType.adt
              val ind = structType.getFieldIndex(field)
              val ctorArgs =
                for (n <- structType.fields.indices) yield {
                  if (n == ind) rhs + 1
                  else structType.getADTSelector(n)(lhs.toTerm)
                }
              rhs = structADT.constructors.head(ctorArgs: _*)
            }

            pushVal(subexpr)
            setValue(lhsString, CCTerm(rhs, curType))
          }
          case _ =>
            evalHelp(exp.exp_)
            maybeOutputClause
            setValue(asLValue(exp.exp_), topVal mapTerm (_ + 1))
        }
      }
      case exp : Epostdec => {
        evalHelp(exp.exp_)
        maybeOutputClause
        setValue(asLValue(exp.exp_), topVal mapTerm (_ - 1))
      }
      case exp : Evar =>
        pushVal(getValue(exp.cident_))
      case exp : Econst =>
        evalHelp(exp.constant_)
//      case exp : Estring.     Exp17 ::= String;
    }

    private def callFunctionInlining(name : String,
                                     functionEntry : Predicate) = {
      val functionExit = newPred(1)

      (functionDefs get name) match {
        case Some(fundef) => {
          inlineFunction(fundef, functionEntry, functionExit)

          // reserve an argument for the function result
          pushFormalVal(getType(fundef))
          resetFields(functionExit)
        }
        case None => (functionDecls get name) match {
          case Some((fundecl, typ)) => {
            warn("no definition of function \"" + name + "\" available")
            pushFormalVal(typ)
          }
          case None =>
            throw new TranslationException(
              "Function " + name + " is not declared")
        }
      }
    }

    private def strictBinOp(left : Exp, right : Exp,
                            op : (CCExpr, CCExpr) => CCExpr) : Unit = {
      evalHelp(left)
      maybeOutputClause
      evalHelp(right)
      val rhs = popVal
      val lhs = popVal
      pushVal(op(lhs, rhs))
    }

    ////////////////////////////////////////////////////////////////////////////

    private def strictBinFun(left : Exp, right : Exp,
                             op : (ITerm, ITerm) => ITerm) : Unit = {
      strictBinOp(left, right,
                  (lhs : CCExpr, rhs : CCExpr) => {
                     val (promLhs, promRhs) = unifyTypes(lhs, rhs)
                     // TODO: correct type promotion
                     val typ = promLhs.typ
                     CCTerm(typ cast op(promLhs.toTerm, promRhs.toTerm), typ)
                   })
    }

    private def strictUnsignedBinFun(left : Exp, right : Exp,
                                     op : (ITerm, ITerm) => ITerm) : Unit = {
      strictBinOp(left, right,
                  (lhs : CCExpr, rhs : CCExpr) => {
                     val (promLhs, promRhs) = unifyTypes(lhs, rhs)
                     // TODO: correct type promotion
                     val typ = promLhs.typ
                     CCTerm(typ cast op(typ cast2Unsigned promLhs.toTerm,
                                        typ cast2Unsigned promRhs.toTerm),
                            typ)
                   })
    }

    private def strictBinPred(left : Exp, right : Exp,
                              op : (ITerm, ITerm) => IFormula) : Unit =
      strictBinOp(left, right,
                  (lhs : CCExpr, rhs : CCExpr) => (lhs.typ, rhs.typ) match {
                    case (CCClock, _ : CCArithType) =>
                      CCFormula(op(GT - lhs.toTerm,
                                   GTU * rhs.toTerm), CCInt)
                    case (_ : CCArithType, CCClock) =>
                      CCFormula(op(GTU * lhs.toTerm,
                                   GT - rhs.toTerm), CCInt)
                    case (CCClock, CCClock) =>
                      CCFormula(op(-lhs.toTerm, -rhs.toTerm), CCInt)

                    case (CCDuration, _ : CCArithType) =>
                      CCFormula(op(lhs.toTerm, GTU * rhs.toTerm), CCInt)
                    case (_ : CCArithType, CCDuration) =>
                      CCFormula(op(GTU * lhs.toTerm, rhs.toTerm), CCInt)
                    case (CCDuration, CCDuration) =>
                      CCFormula(op(lhs.toTerm, rhs.toTerm), CCInt)

                    case (CCClock, CCDuration) =>
                      CCFormula(op(GT - lhs.toTerm, rhs.toTerm), CCInt)
                    case (CCDuration, CCClock) =>
                      CCFormula(op(lhs.toTerm, GT - rhs.toTerm), CCInt)

                    case _ =>
                      CCFormula(op(lhs.toTerm, rhs.toTerm), CCInt)
                  })

    ////////////////////////////////////////////////////////////////////////////

    private def convertType(t : CCExpr, newType : CCType) : CCExpr =
      (t.typ, newType) match {
        case (oldType, newType)
          if (oldType == newType) =>
            t
        case (oldType : CCArithType, newType : CCArithType) =>
          newType cast t
        case (oldType : CCArithType, CCDuration) => {
          if (!useTime)
            throw NeedsTimeException
          CCTerm(GTU * t.toTerm, CCDuration)
        }
        case _ =>
          throw new TranslationException(
            "do not know how to convert " + t + " to " + newType)
      }

    private def unifyTypes(a : CCExpr, b : CCExpr) : (CCExpr, CCExpr) =
      (a.typ, b.typ) match {

        case (at, bt) if (at == bt) =>
          (a, b)

        case (at : CCArithType, bt : CCArithType) =>
          if ((at.UNSIGNED_RANGE > bt.UNSIGNED_RANGE) ||
              (at.UNSIGNED_RANGE == bt.UNSIGNED_RANGE && at.isUnsigned))
            (a, convertType(b, at))
          else
            (convertType(a, bt), b)

        case (at : CCArithType, CCDuration) =>
          (convertType(a, CCDuration), b)
        case (CCDuration, bt : CCArithType) =>
          (a, convertType(b, CCDuration))

        case _ =>
          throw new TranslationException("incompatible types")
      }

    ////////////////////////////////////////////////////////////////////////////

    private def evalHelp(constant : Constant) : Unit = constant match {
//      case constant : Efloat.        Constant ::= Double;
      case constant : Echar =>
        pushVal(CCTerm(IdealInt(constant.char_.toInt), CCInt))
      case constant : Eunsigned =>
        pushVal(CCTerm(IdealInt(
          constant.unsigned_.substring(0,
            constant.unsigned_.size - 1)), CCUInt))
      case constant : Elong =>
        pushVal(CCTerm(IdealInt(
          constant.long_.substring(0, constant.long_.size - 1)), CCLong))
      case constant : Eunsignlong =>
        pushVal(CCTerm(IdealInt(
          constant.unsignedlong_.substring(0,
            constant.unsignedlong_.size - 2)), CCULong))
      case constant : Ehexadec =>
        pushVal(CCTerm(IdealInt(constant.hexadecimal_ substring 2, 16), CCInt))
      case constant : Ehexaunsign =>
        pushVal(CCTerm(IdealInt(constant.hexunsigned_.substring(2,
                                  constant.hexunsigned_.size - 1), 16), CCUInt))
      case constant : Ehexalong =>
        pushVal(CCTerm(IdealInt(constant.hexlong_.substring(2,
                                  constant.hexlong_.size - 1), 16), CCLong))
      case constant : Ehexaunslong =>
        pushVal(CCTerm(IdealInt(constant.hexunslong_.substring(2,
                                  constant.hexunslong_.size - 2), 16), CCULong))
      case constant : Eoctal =>
        pushVal(CCTerm(IdealInt(constant.octal_, 8), CCInt))
//      case constant : Eoctalunsign.  Constant ::= OctalUnsigned;
      case constant : Eoctallong =>
        pushVal(CCTerm(IdealInt(constant.octallong_.substring(0,
                                  constant.octallong_.size - 1), 8), CCLong))
//      case constant : Eoctalunslong. Constant ::= OctalUnsLong;
//      case constant : Ecdouble.      Constant ::= CDouble;
//      case constant : Ecfloat.       Constant ::= CFloat;
//      case constant : Eclongdouble.  Constant ::= CLongDouble;
      case constant : Eint =>
        pushVal(CCTerm(i(IdealInt(constant.unboundedinteger_)), CCInt))
    }
  }

  //////////////////////////////////////////////////////////////////////////////

  private def inlineFunction(functionDef : Function_def,
                             entry : Predicate,
                             exit : Predicate) : Unit = {
    pushLocalFrame
    val stm = pushArguments(functionDef)

    assert(entry.arity == allFormalVars.size)

    val translator = FunctionTranslator(exit)
    translator.translateWithReturn(stm, entry)

    popLocalFrame
  }

  private def pushArguments(functionDef : Function_def) : Compound_stm = {
    val (declarator, stm) = functionDef match {
      case f : NewFunc    => (f.declarator_, f.compound_stm_)
      case f : NewFuncInt => (f.declarator_, f.compound_stm_)
    }

    declarator.asInstanceOf[NoPointer].direct_declarator_ match {
      case dec : NewFuncDec =>
        for (argDec <- dec.parameter_type_.asInstanceOf[AllSpec]
                          .listparameter_declaration_)
          argDec match {
            case argDec : OnlyType =>
              // ignore, a void argument implies that there are no arguments
            case argDec : TypeAndParam => {
              val typ = getType(argDec.listdeclaration_specifier_)
              addLocalVar(typ newConstant getName(argDec.declarator_), typ)
            }
            case argDec : TypeHintAndParam => {
              val typ = getType(argDec.listdeclaration_specifier_)
              addLocalVar(typ newConstant getName(argDec.declarator_), typ)
              processHints(argDec.listabs_hint_)
            }
//            case argDec : Abstract =>
          }
//      case dec : OldFuncDef =>
//        for (ident <- dec.listcident_)
//          localVars += new ConstantTerm(ident)
      case dec : OldFuncDec =>
        // arguments are not specified ...
    }

    stm
  }

  //////////////////////////////////////////////////////////////////////////////

  private object FunctionTranslator {
    def apply =
      new FunctionTranslator(None)
    def apply(returnPred : Predicate) =
      new FunctionTranslator(Some(returnPred))
  }

  private class FunctionTranslator private (returnPred : Option[Predicate]) {

    private def symexFor(initPred : Predicate,
                         stm : Expression_stm) : (Symex, Option[CCExpr]) = {
      val exprSymex = Symex(initPred)
      val res = stm match {
        case _ : SexprOne => None
        case stm : SexprTwo => Some(exprSymex eval stm.exp_)
      }
      (exprSymex, res)
    }

    def translateNoReturn(compound : Compound_stm) : Unit = {
      translateWithEntryClause(compound, newPred)
      postProcessClauses
    }

    def translateWithReturn(compound : Compound_stm) : Unit = {
      val finalPred = newPred
      translateWithEntryClause(compound, finalPred)
      // add a default return edge
      val rp = returnPred.get
      output(Clause(atom(rp, (allFormalVars take (rp.arity - 1)) ++
                             List(IConstant(new ConstantTerm("__result")))),
                    List(atom(finalPred, allFormalVars)),
                    true))
      postProcessClauses
    }

    def translateWithReturn(compound : Compound_stm,
                            entry : Predicate) : Unit = {
      val finalPred = newPred
      translate(compound, entry, finalPred)
      // add a default return edge
      val rp = returnPred.get
      output(Clause(atom(rp, (allFormalVars take (rp.arity - 1)) ++
                             List(IConstant(new ConstantTerm("__result")))),
                    List(atom(finalPred, allFormalVars)),
                    true))
      postProcessClauses
    }

    ////////////////////////////////////////////////////////////////////////////

    private def postProcessClauses : Unit = {
      connectJumps
      mergeAtomicBlocks
    }

    private def connectJumps : Unit =
      for ((label, jumpPred, jumpVars, position) <- jumpLocs)
        (labelledLocs get label) match {
          case Some((targetPred, targetVars)) => {
            val commonVars =
              (jumpVars zip targetVars).takeWhile({
                case (x, y) => x == y
              }).map(_._1)
            val jumpArgs = commonVars ++ (
              for (i <- 0 until (jumpPred.arity - commonVars.size))
              yield IConstant(new ConstantTerm("preArg_" + i)))
            val targetArgs = commonVars ++ (
              for (i <- 0 until (targetPred.arity - commonVars.size))
              yield IConstant(new ConstantTerm("postArg_" + i)))
            clauses(position) = (Clause(atom(targetPred, targetArgs),
                                        List(atom(jumpPred, jumpArgs)),
                                        true),
                                 ParametricEncoder.NoSync)
            usedJumpTargets.put(targetPred, label)
          }
          case None =>
            throw new TranslationException("cannot goto label " + label)
        }

    private def mergeAtomicBlocks : Unit = if (!atomicBlocks.isEmpty) {
      val sortedBlocks =
        atomicBlocks sortWith { case ((s1, e1), (s2, e2)) =>
                                  s1 < s2 || (s1 == s2 && e1 > e2) }

      val offset = sortedBlocks.head._1
      var concernedClauses = clauses.slice(offset, clauses.size).toList
      clauses reduceToSize offset

      var curPos = offset
      for ((bstart, bend) <- sortedBlocks)
        if (bstart >= curPos) {
          while (curPos < bend) {
            clauses += concernedClauses.head
            concernedClauses = concernedClauses.tail
            curPos = curPos + 1
          }
          mergeClauses(clauses.size - (bend - bstart))
        }

      clauses ++= concernedClauses

      val bodyPreds =
        (for ((c, _) <- clauses.iterator; p <- c.bodyPredicates.iterator)
         yield p).toSet

      for ((Clause(IAtom(pred, _), _, _), _) <- clauses.iterator)
        if (!(bodyPreds contains pred) && (usedJumpTargets contains pred))
          throw new TranslationException("cannot goto label " +
                                         usedJumpTargets(pred) +
                                         ", which was eliminated due to " +
                                         "atomic blocks")
    }

    private val jumpLocs =
      new ArrayBuffer[(String, Predicate, Seq[ITerm], Int)]
    private val labelledLocs =
      new MHashMap[String, (Predicate, Seq[ITerm])]
    private val usedJumpTargets =
      new MHashMap[Predicate, String]
    private val atomicBlocks =
      new ArrayBuffer[(Int, Int)]

    ////////////////////////////////////////////////////////////////////////////

    private def translate(stm : Stm,
                          entry : Predicate,
                          exit : Predicate) : Unit = stm match {
      case stm : LabelS =>
        translate(stm.labeled_stm_, entry, exit)
      case stm : CompS =>
        translate(stm.compound_stm_, entry, exit)
      case stm : ExprS =>
        symexFor(entry, stm.expression_stm_)._1 outputClause exit
      case stm : SelS =>
        translate(stm.selection_stm_, entry, exit)
      case stm : IterS =>
        translate(stm.iter_stm_, entry, exit)
      case stm : JumpS =>
        translate(stm.jump_stm_, entry, exit)
      case stm : AtomicS =>
        translate(stm.atomic_stm_, entry, exit)
    }

    private def translate(dec : Dec, entry : Predicate) : Predicate = {
      val decSymex = Symex(entry)
      collectVarDecls(dec, false, decSymex)
      val exit = newPred
      decSymex outputClause exit
      exit
    }

    private def translate(stm : Labeled_stm,
                          entry : Predicate,
                          exit : Predicate) : Unit = stm match {
      case stm : SlabelOne => { // Labeled_stm ::= CIdent ":" Stm ;
        if (labelledLocs contains stm.cident_)
          throw new TranslationException("multiple labels " + stm.cident_)
        labelledLocs.put(stm.cident_, (entry, allFormalVars))
        translate(stm.stm_, entry, exit)
      }
      //-- SlabelTwo.   Labeled_stm ::= "case" Constant_expression ":" Stm ;
      //SlabelThree. Labeled_stm ::= "default" ":" Stm;
    }

    private def translateWithEntryClause(
                          compound : Compound_stm,
                          exit : Predicate) : Unit = compound match {
      case compound : ScompOne =>
        output(Clause(atom(exit, allVarInits), List(), globalPreconditions))
      case compound : ScompTwo => {
        pushLocalFrame

        val stmsIt = ap.util.PeekIterator(compound.liststm_.iterator)

        // merge simple side-effect-free declarations with
        // the entry clause
        var entryPred = newPred
        var entryClause =
          Clause(atom(entryPred, allVarInits), List(), globalPreconditions)

        while (stmsIt.hasNext && isSEFDeclaration(stmsIt.peekNext)) {
          val decSymex = Symex(entryPred)
          collectVarDecls(stmsIt.next.asInstanceOf[DecS].dec_,
                          false, decSymex)
          entryPred = newPred
          entryClause = (decSymex genClause entryPred) mergeWith entryClause
        }

        output(entryClause)
        translateStmSeq(stmsIt, entryPred, exit)

        popLocalFrame
      }
    }

    private def isSEFDeclaration(stm : Stm) : Boolean = stm match {
      case stm : DecS => {
        stm.dec_ match {
          case _ : NoDeclarator => true
          case dec : Declarators =>
            dec.listinit_declarator_ forall {
              case _ : OnlyDecl => true
              case _ : HintDecl => true
              case decl : InitDecl =>
                decl.initializer_.asInstanceOf[InitExpr].exp_ match {
                  case _ : Econst => true
                  case _ => false
                }
              case decl : HintInitDecl =>
                decl.initializer_.asInstanceOf[InitExpr].exp_ match {
                  case _ : Econst => true
                  case _ => false
                }
            }
        }
      }
      case _ => false
    }

    private def translate(compound : Compound_stm,
                          entry : Predicate,
                          exit : Predicate) : Unit = compound match {
      case compound : ScompOne => {
        val vars = allFormalVars
        output(Clause(atom(exit, vars), List(atom(entry, vars)), true))
      }
      case compound : ScompTwo => {
        pushLocalFrame

        val stmsIt = compound.liststm_.iterator
        translateStmSeq(stmsIt, entry, exit)

        popLocalFrame
      }
    }

    private def translateStmSeq(stmsIt : Iterator[Stm],
                                entry : Predicate,
                                exit : Predicate) : Unit = {
      var prevPred = entry
      while (stmsIt.hasNext)
        stmsIt.next match {
          case stm : DecS => {
            prevPred = translate(stm.dec_, prevPred)
            if (!stmsIt.hasNext)
              output(Clause(atom(exit, allFormalVars),
                            List(atom(prevPred, allFormalVars)),
                            true))
          }
          case stm => {
            val nextPred = if (stmsIt.hasNext) newPred else exit
            translate(stm, prevPred, nextPred)
            prevPred = nextPred
          }
        }
    }

    var innermostLoopCont : Predicate = null
    var innermostLoopExit : Predicate = null

    private def withinLoop[A](
                     loopCont : Predicate, loopExit : Predicate)
                     (comp : => A) : A = {
      val oldCont = innermostLoopCont
      val oldExit = innermostLoopExit
      innermostLoopCont = loopCont
      innermostLoopExit = loopExit
      try {
        comp
      } finally {
        innermostLoopCont = oldCont
        innermostLoopExit = oldExit
      }
    }

    private def translate(stm : Iter_stm,
                          entry : Predicate,
                          exit : Predicate) : Unit = stm match {
      case stm : SiterOne => {
        // while loop

        val first = newPred
        val condSymex = Symex(entry)
        val cond = (condSymex eval stm.exp_).toFormula
        condSymex.outputITEClauses(cond, first, exit)
        withinLoop(entry, exit) { //continue,break handling
          translate(stm.stm_, first, entry)
        }
      }

      case stm : SiterTwo => {
        // do ... while loop

        val first = newPred
        withinLoop(first, exit) {
          translate(stm.stm_, entry, first)
        }

        val condSymex = Symex(first)
        val cond = (condSymex eval stm.exp_).toFormula
        condSymex.outputITEClauses(cond, entry, exit)
      }

      case _ : SiterThree | _ : SiterFour => {
        // for loop

        val first, second, third = newPred

        val (initStm, condStm, body) = stm match {
          case stm : SiterThree =>
            (stm.expression_stm_1, stm.expression_stm_2, stm.stm_)
          case stm : SiterFour  =>
            (stm.expression_stm_1, stm.expression_stm_2, stm.stm_)
        }

        symexFor(entry, initStm)._1 outputClause first

        val (condSymex, condExpr) = symexFor(first, condStm)
        val cond : IFormula = condExpr match {
          case Some(expr) => expr.toFormula
          case None       => true
        }

        condSymex.outputITEClauses(cond, second, exit)

        withinLoop(third, exit) {
          translate(body, second, third)
        }

        stm match {
          case stm : SiterThree =>
            output(Clause(atom(first, allFormalVars),
                          List(atom(third, allFormalVars)), true))
          case stm : SiterFour  => {
            val incSymex = Symex(third)
            incSymex eval stm.exp_
            incSymex outputClause first
          }
        }
      }
    }

    private def translate(stm : Selection_stm,
                          entry : Predicate,
                          exit : Predicate) : Unit = stm match {
      case _ : SselOne | _ : SselTwo => {
        val first, second = newPred
        val vars = allFormalVars
        val condSymex = Symex(entry)
        val cond = stm match {
          case stm : SselOne => (condSymex eval stm.exp_).toFormula
          case stm : SselTwo => (condSymex eval stm.exp_).toFormula
        }
        condSymex.outputITEClauses(cond, first, second)
        stm match {
          case stm : SselOne => {
            translate(stm.stm_, first, exit)
            output(Clause(atom(exit, vars), List(atom(second, vars)), true))
          }
          case stm : SselTwo => {
            translate(stm.stm_1, first, exit)
            translate(stm.stm_2, second, exit)
          }
        }
      }
//      case stm : SselThree.  Selection_stm ::= "switch" "(" Exp ")" Stm ;
    }

    private def translate(jump : Jump_stm,
                          entry : Predicate,
                          exit : Predicate) : Unit = jump match {
      case jump : SjumpOne => { // goto
        jumpLocs += ((jump.cident_, entry, allFormalVars, clauses.size))
        // reserve space for the later jump clause
        output(null)
      }
      case jump : SjumpTwo => { // continue
        if (innermostLoopCont == null)
          throw new TranslationException(
            "\"continue\" can only be used within loops")
        Symex(entry) outputClause innermostLoopCont
      }
      case jump : SjumpThree => { // break
        if (innermostLoopExit == null)
          throw new TranslationException(
            "\"break\" can only be used within loops")
        Symex(entry) outputClause innermostLoopExit
      }
      case jump : SjumpFour => // return
        returnPred match {
          case Some(rp) => {
            val args = (allFormalVars take (rp.arity - 1)) ++
                       List(IConstant(new ConstantTerm("__result")))
            output(Clause(atom(rp, args),
                          List(atom(entry, allFormalVars)),
                          true))
          }
          case None =>
            throw new TranslationException(
              "\"return\" can only be used within functions")
        }
      case jump : SjumpFive => { // return exp
        val symex = Symex(entry)
        val retValue = symex eval jump.exp_
        returnPred match {
          case Some(rp) => {
            val args = (symex.getValuesAsTerms take (rp.arity - 1)) ++
                       List(retValue.toTerm)
            symex outputClause atom(rp, args)
          }
          case None =>
            throw new TranslationException(
              "\"return\" can only be used within functions")
        }
      }
    }

    private def translate(aStm : Atomic_stm,
                          entry : Predicate,
                          exit : Predicate) : Unit = aStm match {
      case stm : SatomicOne => {
        val currentClauseNum = clauses.size
        inAtomicMode {
          // add a further state inside the block, to correctly
          // distinguish between loops within the block, and a loop
          // around the block
          val first = newPred
          val entrySymex = Symex(entry)
          entrySymex outputClause first
          translate(stm.stm_, first, exit)
        }
        atomicBlocks += ((currentClauseNum, clauses.size))
      }
      case stm : SatomicTwo => {
        val currentClauseNum = clauses.size
        inAtomicMode {
          val first = newPred
          val condSymex = Symex(entry)
          condSymex.saveState
          val cond = (condSymex eval stm.exp_).toFormula
          if (!condSymex.atomValuesUnchanged)
            throw new TranslationException(
              "expressions with side-effects are not supported in \"within\"")
          import HornClauses._
          timeInvariants += (cond :- atom(entry, allFormalVars))
          condSymex outputClause first
          translate(stm.stm_, first, exit)
        }
        atomicBlocks += ((currentClauseNum, clauses.size))
      }
    }
  }

  //////////////////////////////////////////////////////////////////////////////

  val system : ParametricEncoder.System = {
    translateProgram

    val singleThreaded =
      processes.size == 1 &&
      processes.head._2 == ParametricEncoder.Singleton

    val predHints =
      (for (p <- ParametricEncoder.processPreds(processes).iterator;
            preds = predicateHints(p);
            if (!preds.isEmpty))
       yield (p -> preds.toList)).toMap

    ParametricEncoder.System(processes.toList,
                             if (singleThreaded) {
                               if (useTime) 2 else 0
                             } else {
                               globalVars.size
                             },
                             None,
                             if (useTime)
                               ParametricEncoder.ContinuousTime(0, 1)
                             else
                               ParametricEncoder.NoTime,
                             timeInvariants,
                             assertionClauses.toList,
                             HornPreprocessor.VerificationHints(predHints))
  }

}
