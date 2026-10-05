/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Probability.ComplementaryProductProjectionEntropy
import AlgebraicComplexity.Probability.PooledMarginalProjection

/-!
# Complementary conditional-product projection inequalities

An ordered recursive state `u` produces two labelled occurrences.  The left occurrence uses the
law pooled in the cell of `u`; the right occurrence uses the law pooled in the cell of
`complement u`.
Conditional on `u`, the two child symbols are independent.  This module exposes the resulting
pooled-parent projection inequality in nats, bits, and a rational quadratic form.

The definitions and marginal calculations live in smaller imported modules so downstream builds
do not need to elaborate one large proof file.  Repeated and self-complementary states remain
labelled twice throughout; no occurrence is deduplicated.
-/

open scoped BigOperators

namespace AlgebraicComplexity

universe u v w x

namespace ComplementaryProductProjectionModel

variable {State : Type u} {Cell : Type v} {Symbol : Type w}
variable [Fintype State] [Fintype Cell] [Fintype Symbol]

/-- **Pooled-occurrence parent projection, in nats.**

This is the direct probability form used by recursive constituent counting.  A competing law
need only preserve the ordered-state marginal and the sum of its two labelled occurrence
marginals.  Absolute continuity is derived internally, including at structural zeroes. -/
theorem conditionalEntropy_add_parentKl_le
    {Parent : Type x} [Fintype Parent] [DecidableEq Parent]
    [DecidableEq State] [DecidableEq Cell] [DecidableEq Symbol]
    (M : ComplementaryProductProjectionModel State Cell Symbol)
    (parent : State × (Symbol × Symbol) → Parent)
    (q : ProbabilityVector (State × (Symbol × Symbol)))
    (hcoarse : q.pushforward M.coarse = M.reference.pushforward M.coarse)
    (hpool : ∀ feature,
      (q.pushforward M.leftFeature).weight feature +
          (q.pushforward M.rightFeature).weight feature =
        (M.reference.pushforward M.leftFeature).weight feature +
          (M.reference.pushforward M.rightFeature).weight feature) :
    q.conditionalEntropy M.coarse +
        (q.pushforward parent).klDiv (M.reference.pushforward parent) ≤
      ∑ state, M.stateLaw.weight state *
        ((M.childLaw (M.cellOf state)).entropy +
          (M.childLaw (M.cellOf (M.complement state))).entropy) := by
  have hfeasible := M.isFeasible_of_coarse_eq_of_pooledFeature_eq q hcoarse hpool
  have hprojection :=
    M.toSparsePooledMarginalProjectionModel.conditionalEntropy_add_parentKl_le
      parent q hfeasible
  change q.conditionalEntropy M.coarse +
      (q.pushforward parent).klDiv (M.reference.pushforward parent) ≤
    M.reference.conditionalEntropy M.coarse at hprojection
  rw [reference_conditionalEntropy_coarse] at hprojection
  exact hprojection

/-- Paper-facing specialization in which the parent symbol is obtained by joining the two child
symbols.  The reference parent law is exposed as `M.parentLaw join`. -/
theorem pooledOccurrenceParentProjection
    {Parent : Type x} [Fintype Parent] [DecidableEq Parent]
    [DecidableEq State] [DecidableEq Cell] [DecidableEq Symbol]
    (M : ComplementaryProductProjectionModel State Cell Symbol)
    (join : Symbol × Symbol → Parent)
    (q : ProbabilityVector (State × (Symbol × Symbol)))
    (hcoarse : q.pushforward M.coarse = M.reference.pushforward M.coarse)
    (hpool : ∀ feature,
      (q.pushforward M.leftFeature).weight feature +
          (q.pushforward M.rightFeature).weight feature =
        (M.reference.pushforward M.leftFeature).weight feature +
          (M.reference.pushforward M.rightFeature).weight feature) :
    q.conditionalEntropy M.coarse +
        (q.pushforward (join ∘ Prod.snd)).klDiv (M.parentLaw join) ≤
      ∑ state, M.stateLaw.weight state *
        ((M.childLaw (M.cellOf state)).entropy +
          (M.childLaw (M.cellOf (M.complement state))).entropy) := by
  exact M.conditionalEntropy_add_parentKl_le (join ∘ Prod.snd) q hcoarse hpool

/-- Base-two form of `conditionalEntropy_add_parentKl_le`. -/
theorem conditionalEntropyBits_add_parentKlBits_le
    {Parent : Type x} [Fintype Parent] [DecidableEq Parent]
    [DecidableEq State] [DecidableEq Cell] [DecidableEq Symbol]
    (M : ComplementaryProductProjectionModel State Cell Symbol)
    (parent : State × (Symbol × Symbol) → Parent)
    (q : ProbabilityVector (State × (Symbol × Symbol)))
    (hcoarse : q.pushforward M.coarse = M.reference.pushforward M.coarse)
    (hpool : ∀ feature,
      (q.pushforward M.leftFeature).weight feature +
          (q.pushforward M.rightFeature).weight feature =
        (M.reference.pushforward M.leftFeature).weight feature +
          (M.reference.pushforward M.rightFeature).weight feature) :
    q.conditionalEntropyBits M.coarse +
        (q.pushforward parent).klDivBits (M.reference.pushforward parent) ≤
      ∑ state, M.stateLaw.weight state *
        ((M.childLaw (M.cellOf state)).entropyBits +
          (M.childLaw (M.cellOf (M.complement state))).entropyBits) := by
  have hfeasible := M.isFeasible_of_coarse_eq_of_pooledFeature_eq q hcoarse hpool
  have hprojection :=
    M.toSparsePooledMarginalProjectionModel.conditionalEntropyBits_add_parentKlBits_le
      parent q hfeasible
  change q.conditionalEntropyBits M.coarse +
      (q.pushforward parent).klDivBits (M.reference.pushforward parent) ≤
    M.reference.conditionalEntropyBits M.coarse at hprojection
  rw [reference_conditionalEntropyBits_coarse] at hprojection
  exact hprojection

/-- Fully rational-in-the-parent-laws form of the pooled-occurrence correction. -/
theorem conditionalEntropyBits_add_parentQuadratic_le
    {Parent : Type x} [Fintype Parent] [DecidableEq Parent]
    [DecidableEq State] [DecidableEq Cell] [DecidableEq Symbol]
    (M : ComplementaryProductProjectionModel State Cell Symbol)
    (parent : State × (Symbol × Symbol) → Parent)
    (q : ProbabilityVector (State × (Symbol × Symbol)))
    (hcoarse : q.pushforward M.coarse = M.reference.pushforward M.coarse)
    (hpool : ∀ feature,
      (q.pushforward M.leftFeature).weight feature +
          (q.pushforward M.rightFeature).weight feature =
        (M.reference.pushforward M.leftFeature).weight feature +
          (M.reference.pushforward M.rightFeature).weight feature) :
    q.conditionalEntropyBits M.coarse +
        (q.pushforward parent).quadraticKlLowerBits
          (M.reference.pushforward parent) ≤
      ∑ state, M.stateLaw.weight state *
        ((M.childLaw (M.cellOf state)).entropyBits +
          (M.childLaw (M.cellOf (M.complement state))).entropyBits) := by
  have hfeasible := M.isFeasible_of_coarse_eq_of_pooledFeature_eq q hcoarse hpool
  have hprojection :=
    M.toSparsePooledMarginalProjectionModel.conditionalEntropyBits_add_parentQuadratic_le
      parent q hfeasible
  change q.conditionalEntropyBits M.coarse +
      (q.pushforward parent).quadraticKlLowerBits
        (M.reference.pushforward parent) ≤
    M.reference.conditionalEntropyBits M.coarse at hprojection
  rw [reference_conditionalEntropyBits_coarse] at hprojection
  exact hprojection

end ComplementaryProductProjectionModel

end AlgebraicComplexity
