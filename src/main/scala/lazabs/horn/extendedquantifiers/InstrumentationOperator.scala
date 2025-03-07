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

import ap.parser._
import ap.types.Sort
import lazabs.horn.extendedquantifiers.Util._
import lazabs.horn.extendedquantifiers.theories.AbstractExtendedQuantifier

object RewriteRules {
  /**
   * The result of a rewrite rule. Let `c` be the original conjunct that the
   * rewrite rule is applied to. Then the new formula  will be:
   * `subst(c &&& newConjunct, rewriteFormulas)` where `subst` is some method
   * that rewrites all formulas appearing in the keys of `rewriteFormulas` with
   * their values.
   * Each formula in `assertions` will also be asserted.
   */
  case class Result(newConjunct     : IFormula,
                    rewriteFormulas : Map[IFormula, IFormula],
                    assertions      : Seq[IFormula])
}

trait RewriteRules {
  // These rules are hardcoded as the array operations, but with some effort
  // the methods could also be generalized to a map from theory functions to
  // rewrite rules.

  import InstrumentationOperator.GhostVar

  /**
   * `oldGhostTerms` and `newGhostTerms` are the old and new values of ghost
   * variables defined in [[InstrumentationOperator.ghostVars]].
   * `otherConstants` contains other terms that might be relevant for the
   * rewriting, for instance alien terms which can appear in predicates.
   * All rewrite rules return a sequence of [[RewriteRules.Result]], which
   * contains information about which conjuncts to add, rewrite, and assert.
   */
  def rewriteStore(oldGhostTerms  : Map[GhostVar, ITerm],
                   newGhostTerms  : Map[GhostVar, ITerm],
                   otherConstants : Set[IConstant],
                   storeInfo      : StoreInfo) : Seq[RewriteRules.Result]
  def rewriteSelect(oldGhostTerms  : Map[GhostVar, ITerm],
                    newGhostTerms  : Map[GhostVar, ITerm],
                    otherConstants : Set[IConstant],
                    selectInfo     : SelectInfo) : Seq[RewriteRules.Result]
  def rewriteConst(oldGhostTerms  : Map[GhostVar, ITerm],
                   newGhostTerms  : Map[GhostVar, ITerm],
                   otherConstants : Set[IConstant],
                   constInfo      : ConstInfo) : Seq[RewriteRules.Result]

  /**
   * The rule for rewriting applications of [[AbstractExtendedQuantifier.morphism]].
   * @param ghostTerms A collection of [[InstrumentationOperator.ghostVars]].
   *                   There will be
   *                   [[InstrumentationOperatorApplier.numGhostRanges]] such
   *                   collections.
   * @param exqInfo Information extracted from the application of
   *                [[AbstractExtendedQuantifier.morphism]].
   */
  def rewriteAggregate(
    ghostTerms : Seq[Map[GhostVar, ITerm]],
    exqInfo    : ExtendedQuantifierApp) : Seq[RewriteRules.Result]
}

object InstrumentationOperator {
  class GhostVar(val sort : Sort, val name : String) {
    override def toString : String = name
  }
}

abstract class InstrumentationOperator(val exq : AbstractExtendedQuantifier)
  extends RewriteRules {
  import InstrumentationOperator.GhostVar

  /**
   * These are the ghost variables of the extended quantifier.
   * There will be [[InstrumentationOperatorApplier.numGhostRanges]] such
   * sequences of ghost variables.
   * Sometimes we might want additional ghost variables that are not directly
   * related to the extended quantifier (such as alien terms). For simplicity,
   * these should be declared as part of below ghostVars. As a result, these
   * terms will be needlessly duplicated when `numGhostRanges > 1`.
   *
   * @todo Check if Eldarica's other preprocessors slice away such copies.
   */
  val ghostVars : Seq[GhostVar]

  /**
   * Initial values for `ghostVars`.
   * If an initial value is not found for a GhostVar, it is left uninitialized.
   */
  val ghostVarInitialValues : Map[GhostVar, ITerm]

  /**
   * Each instrumentation operator is initially assigned one set of ghost
   * variables. If `maxSupportedGhostVarRanges` is set to a value other than 1,
   * if the result is `Inconclusive` the number of ghost variable sets is
   * incremented by one, at most until `maxSupportedGhostVarRanges`.
   * If a value other than `1` is specified,
   * [[InstrumentationOperator.rewriteAggregate]] should handle the combining
   * values coming from multiple sets of ghost variables. Other rewrite rules
   * do not require special treatment, as they each rule will automatically be
   * applied once per ghost variable set, per extended quantifier application.
   * @todo This is currently ignored, refactor to consider it.
   */
  val maxSupportedGhostVarRanges : Int = 1

  /**
   * Given a map from ghost variables to terms, this should construct a formula
   * using those terms and [[exq.morphism]]. This is later used when
   * back-translating solutions in [[GhostVariableAdder]] to eliminate
   * ghost variables.
   */
  def ghostVarsToAggregateFormula(ghostTerms : Map[GhostVar, ITerm]) : IFormula
}



