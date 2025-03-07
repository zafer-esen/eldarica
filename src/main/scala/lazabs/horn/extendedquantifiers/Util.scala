/**
 * Copyright (c) 2024 Jesper Amilon, Zafer Esen, Philipp Ruemmer.
 * All rights reserved.
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

package lazabs.horn.extendedquantifiers

import ap.parser.IExpression.Eq
import ap.parser.{CollectingVisitor, IAtom, IExpression, IFormula, IFunApp, ITerm}
import ap.theories.ExtArray
import ap.types.{MonoSortedPredicate, Sort}
import lazabs.horn.bottomup.HornClauses.Clause
import lazabs.horn.extendedquantifiers.theories.AbstractExtendedQuantifier
import lazabs.horn.preprocessor.HornPreprocessor.Clauses

import scala.collection.mutable.ArrayBuffer

object Util {

  /**
   * For storing applications of [[AbstractExtendedQuantifier.morphism]].
   */
  case class ExtendedQuantifierApp(exTheory      : AbstractExtendedQuantifier,
                                   funApp        : IFunApp,
                                   arrayTerm     : ITerm,
                                   loTerm        : ITerm,
                                   hiTerm        : ITerm,
                                   aggregateTerm : ITerm,
                                   alienTerms    : Seq[ITerm],
                                   conjunct      : IFormula)

  case class SelectInfo(a: ITerm, i: ITerm, o: ITerm, theory: ExtArray)

  case class StoreInfo(oldA: ITerm, newA: ITerm, i: ITerm, o: ITerm,
                       theory: ExtArray)

  case class ConstInfo(newA: ITerm, o: ITerm, theory: ExtArray)

  def extractSelectInfo(conjunct: IFormula): SelectInfo = {
    val Eq(IFunApp(f@ExtArray.Select(theory), Seq(a, i)), o) = conjunct
    SelectInfo(a, i, o, theory)
  }

  def extractStoreInfo(conjunct: IFormula): StoreInfo = {
    val Eq(IFunApp(f@ExtArray.Store(theory), Seq(a1, i, o)), a2) = conjunct
    StoreInfo(a1, a2, i, o, theory)
  }

  def extractConstInfo(conjunct: IFormula): ConstInfo = {
    val Eq(IFunApp(f@ExtArray.Const(theory), Seq(o)), a) = conjunct
    ConstInfo(a, o, theory)
  }

  /**
   * Class for collecting the extended quantifier applications
   * occurring in an expression.
   */
  object ExtQuantifierFunctionApplicationCollector {
    def apply(t: IExpression): Seq[ExtendedQuantifierApp] = {
      val apps = new ArrayBuffer[ExtendedQuantifierApp]
      val c = new ExtQuantifierFunctionApplicationCollector(apps)
      c.visitWithoutResult(t, 0)
      apps
    }
  }

  class ExtQuantifierFunctionApplicationCollector(
    extQuantifierInfos: ArrayBuffer[ExtendedQuantifierApp])
    extends CollectingVisitor[Int, Unit] {
    def postVisit(t: IExpression, boundVars: Int, subres: Seq[Unit]): Unit =
      t match {
        case conj@Eq(app@IFunApp(
        AbstractExtendedQuantifier.Morphism(theory), args), o)
          if args.size > 2 => // args are: Seq(a, lo, hi, alienConstants)
          val a = args(0)
          val lo = args(1)
          val hi = args(2)
          val alienTerms = args.drop(3)
          extQuantifierInfos +=
            ExtendedQuantifierApp(theory, app, a, lo, hi, o, alienTerms, conj)
        case _ => // nothing
      }
  }

  def isSelect(conjunct: IFormula): Boolean = conjunct match {
    case Eq(IFunApp(ExtArray.Select(_), Seq(a, i)), o) => true
    case _ => false
  }

  def isStore(conjunct: IFormula): Boolean = conjunct match {
    case Eq(IFunApp(ExtArray.Store(_), Seq(a1, i, o)), a2) => true
    case _ => false
  }

  def isConst(conjunct: IFormula): Boolean = conjunct match {
    case Eq(IFunApp(ExtArray.Const(_), Seq(o)), a) => true
    case _ => false
  }

  def isAggregateFun(conjunct: IFormula): Boolean = conjunct match {
    case Eq(IFunApp(AbstractExtendedQuantifier.Morphism(_), _), _) => true
    case _                                                         => false
  }

  def getNewArrayTerm(conjunct: IFormula): (Seq[ITerm], Seq[Sort]) =
    conjunct match {
      case Eq(IFunApp(f@ExtArray.Const(theory), _), a) =>
        (Seq(a), Seq(theory.sort))
      case Eq(IFunApp(f@ExtArray.Store(theory), _), a) =>
        (Seq(a), Seq(theory.sort))
      case _ => (Nil, Nil)
    }

  def getOriginalArrayTerm(conjunct: IFormula): (Seq[ITerm], Seq[Sort]) =
    conjunct match {
      case Eq(IFunApp(f@ExtArray.Store(theory), Seq(a, _, _)), _) =>
        (Seq(a), Seq(theory.sort))
      case _ => (Nil, Nil)
    }

  def collectArgsSortsFromAtoms(atoms: Seq[IAtom]): (Seq[ITerm], Seq[Sort]) = {
    val sorts: Seq[Sort] =
      (for (atom <- atoms) yield {
        atom.pred match {
          case p: MonoSortedPredicate => p.argSorts
          case p => Seq.fill(p.arity)(Sort.Integer)
        }
      }).flatten
    (atoms.flatMap(_.args), sorts)
  }

  def gatherExtQuans(clauses: Clauses): Seq[ExtendedQuantifierApp] = {
    val allInfos = (for (Clause(head, body, constraint) <- clauses) yield {
      val infos: Seq[ExtendedQuantifierApp] =
        ExtQuantifierFunctionApplicationCollector(constraint)
      infos
    }).flatten.distinct
    allInfos
  }
}
