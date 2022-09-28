/**
 * Copyright (c) 2022 Jesper Amilon, Zafer Esen, Philipp Ruemmer.
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

import ap.parser.IExpression.Predicate
import ap.parser._
import ap.types.SortedConstantTerm
import lazabs.horn.bottomup.HornClauses.Clause
import Util._
import ap.parser.IExpression._
import GhostVariableAdder._

abstract class
ClauseInstrumenter(extendedQuantifier : ExtendedQuantifier) {
  protected def instrumentStore (storeInfo  : StoreInfo,
                                 bodyTerms  : GhostVariableTerms) : Seq[IFormula]
  protected def instrumentSelect(selectInfo : SelectInfo,
                                 bodyTerms  : GhostVariableTerms) : Seq[IFormula]
  protected def instrumentConst (constInfo  : ConstInfo,
                                 bodyTerms  : GhostVariableTerms) : Seq[IFormula]

  protected val arrayTheory = extendedQuantifier.arrayTheory
  protected val indexSort = arrayTheory.indexSorts.head  // todo: assuming 1-d array

  protected val (hlo, hhi, hres, harr) =
    (IConstant(new SortedConstantTerm("lo'", indexSort)),
      IConstant(new SortedConstantTerm("hi'", indexSort)),
      IConstant(new SortedConstantTerm("res'", arrayTheory.objSort)),
      IConstant(new SortedConstantTerm("arr'", arrayTheory.sort)))

  // returns all instrumentations of a clause
  def instrument (clause                 : Clause,
                  ghostVarInds           : Map[Predicate, Seq[GhostVariableInds]],
                  extendedQuantifierInfo : ExtendedQuantifierInfo) : Seq[Instrumentation] = {
    // todo: below code must be modified to track multiple ranges (with multiple ghost vars)
    val hInds = ghostVarInds(clause.head.pred).head
    val headTermMap : Map[Int, ITerm] = Map(
      hInds.lo -> hlo, hInds.hi -> hhi, hInds.res -> hres, hInds.arr -> harr)

    // returns instrumentations for body atom, EXCEPT the identity instrumentation
    def instrForBodyAtom(bAtom : IAtom) : Seq[Instrumentation] = {
      val GhostVariableInds(iblo, ibhi, ibres, ibarr) = ghostVarInds(bAtom.pred).head // todo: support multiple ghost var sets
      val bodyTerms = GhostVariableTerms(
        bAtom.args(iblo), bAtom.args(ibhi), bAtom.args(ibres), bAtom.args(ibarr))
      val conjuncts : Seq[IFormula] =
        LineariseVisitor(Transform2NNF(clause.constraint), IBinJunctor.And)

      val instrumentationConstraints : Seq[IFormula] = {
        val relevantConjuncts =
          conjuncts filter (c => isSelect(c) || isConst(c) || isStore(c))
        if(relevantConjuncts.length > 1)
          throw new Exception("More than one conjunct found for instrumentation," +
            " are the clauses normalized?\n" + clause.toPrologString)
        relevantConjuncts.headOption match {
          case Some(c) if isSelect(c) =>
            instrumentSelect(extractSelectInfo(c), bodyTerms)
          case Some(c) if isStore(c) =>
            instrumentStore(extractStoreInfo(c), bodyTerms)
          case Some(c) if isConst(c) =>
            instrumentConst(extractConstInfo(c), bodyTerms)
          case None => Nil
        }
      }

      for(instrumentationConstraint <- instrumentationConstraints) yield
        Instrumentation(instrumentationConstraint, headTermMap)
    }

    // returns the identity instrumentation for a body atom
    def identityInstrumentation (bAtom : IAtom) = {
      val GhostVariableInds(iblo, ibhi, ibres, ibarr) = ghostVarInds(bAtom.pred).head // todo: support multiple ghost var sets
      val bodyTerms = GhostVariableTerms(
        bAtom.args(iblo), bAtom.args(ibhi), bAtom.args(ibres), bAtom.args(ibarr))
      val newConjunct =
        (harr === bodyTerms.arr) &&&
          (hlo === bodyTerms.lo) &&&
          (hhi === bodyTerms.hi) &&&
          (hres === bodyTerms.res)
      Instrumentation(newConjunct, headTermMap)
    }

    val instrsForBodyAtoms : Seq[Seq[Instrumentation]] =
      clause.body map instrForBodyAtom
    val identityInstrsForBodyAtoms : Seq[Instrumentation] =
      clause.body map identityInstrumentation
    // todo: are ghost terms of each atom initially distinct?
    instrsForBodyAtoms.reduceOption((instrs1, instrs2) =>
      Instrumentation.product(instrs1, instrs2)).getOrElse(Nil) ++ identityInstrsForBodyAtoms
  }
}

// A simple instrumenter that works for all extended quantifiers, but is very
// general and thus imprecise.
// todo: add ghost array assertions
class SimpleClauseInstrumenter(extendedQuantifier : ExtendedQuantifier)
  extends ClauseInstrumenter(extendedQuantifier) {
  override protected
  def instrumentStore(storeInfo : StoreInfo,
                      bodyTerms : GhostVariableTerms): Seq[IFormula] = {
    val StoreInfo(a1, a2, i, o, arrayTheory2) = storeInfo
    if(arrayTheory != arrayTheory2)
      Nil
    else {
      import extendedQuantifier._
      import bodyTerms._
      import arrayTheory2._
      val instrConstraint1 =
        (harr === a2) &&& ite(bodyTerms.lo === bodyTerms.hi,
          (hlo === i) & (hhi === i + 1) & (hres === o),
          ite((lo - 1 === i),
            (hres === reduceOp(res, o)) & (hlo === i) & hhi === hi,
            ite(hi === i,
              (hres === reduceOp(res, o)) & (hhi === i + 1 & hlo === lo),
              ite(lo <= i & hi > i,
                invReduceOp match {
                  case Some(f) => hres === reduceOp(f(res, select(a1, i)), o) & hlo === lo & hhi === hi
                  case _ => (hlo === i) & (hhi === i + 1) & (hres === o) //??? //TODO: Implement non-cancellative case
                },
                //hres === ifInsideBounds_help(o, arrayTheory.select(a1, i), bres) & hlo === blo & hhi === bhi, //relate to prev val
                (hlo === i) & (hhi === i + 1) & (hres === o))))) // outside bounds, reset
      Seq(instrConstraint1)
    }
  }

  override protected
  def instrumentSelect(selectInfo : SelectInfo,
                       bodyTerms : GhostVariableTerms): Seq[IFormula] = {
    val SelectInfo(a, i, o, arrayTheory2) = selectInfo
    if (arrayTheory != arrayTheory2)
      Nil
    else {
      import extendedQuantifier._
      import bodyTerms._
      val instrConstraint1 =
        (harr === a) &&& ite(lo === hi,
          (hlo === i) & (hhi === i + 1) & (hres === o),
          ite((lo - 1 === i),
            (hres === reduceOp(res, o)) & (hlo === i) & hhi === hi,
            ite(hi === i,
              (hres === reduceOp(res, o)) & (hhi === i + 1 & hlo === lo),
              ite(lo <= i & hi > i,
                hres === res & hlo === lo & hhi === hi, // no change within bounds
                (hlo === i) & (hhi === i + 1) & (hres === o))))) // outside bounds, reset
      Seq(instrConstraint1)
    }
  }

  // todo: instrument const operation
  override protected
  def instrumentConst(constInfo : ConstInfo,
                      bodyTerms : GhostVariableTerms): Seq[IFormula] = Nil
}