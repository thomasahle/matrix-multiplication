/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Probability.ComplementaryProductProjectionCore
import AlgebraicComplexity.Probability.JointMarginal

/-!
# Marginals of a complementary conditional-product reference

This module computes the coarse and labelled-occurrence marginals of a complementary-product
reference.  It also proves that preserving the coarse law and pooled occurrence law forces
absolute continuity, including structural zeroes and self-complementary states.
-/

open scoped BigOperators

namespace AlgebraicComplexity

universe u v w

namespace ComplementaryProductProjectionModel

variable {State : Type u} {Cell : Type v} {Symbol : Type w}
variable [Fintype State] [Fintype Cell] [Fintype Symbol]

/-- Revealing the ordered state in the reference recovers the prescribed state law. -/
@[simp] theorem reference_pushforward_coarse [DecidableEq State]
    (M : ComplementaryProductProjectionModel State Cell Symbol) :
    M.reference.pushforward M.coarse = M.stateLaw := by
  exact ProbabilityVector.pushforward_joint_fst M.stateLaw fun state ↦
    (M.childLaw (M.cellOf state)).product
      (M.childLaw (M.cellOf (M.complement state)))

/-- Left pooled-feature mass is the state-law mass of one cell times that cell's symbol mass. -/
theorem reference_leftFeature_weight
    [DecidableEq State] [DecidableEq Cell] [DecidableEq Symbol]
    (M : ComplementaryProductProjectionModel State Cell Symbol)
    (cell : Cell) (symbol : Symbol) :
    (M.reference.pushforward M.leftFeature).weight (cell, symbol) =
      (M.stateLaw.pushforward M.cellOf).weight cell *
        (M.childLaw cell).weight symbol := by
  classical
  rw [ProbabilityVector.pushforward_weight, Fintype.sum_prod_type]
  simp only [reference, leftFeature, ProbabilityVector.joint_weight]
  calc
    (∑ outer : State, ∑ pair : Symbol × Symbol,
        if (M.cellOf outer, pair.1) = (cell, symbol) then
          M.stateLaw.weight outer *
            ((M.childLaw (M.cellOf outer)).weight pair.1 *
              (M.childLaw (M.cellOf (M.complement outer))).weight pair.2)
        else 0) =
        ∑ outer,
          if M.cellOf outer = cell then
            M.stateLaw.weight outer * (M.childLaw cell).weight symbol
          else 0 := by
      apply Finset.sum_congr rfl
      intro outer _
      by_cases houter : M.cellOf outer = cell
      · simp only [Prod.mk.injEq, houter, true_and]
        simp only [if_true]
        calc
          (∑ pair : Symbol × Symbol,
              if pair.1 = symbol then
                M.stateLaw.weight outer *
                  ((M.childLaw cell).weight pair.1 *
                    (M.childLaw (M.cellOf (M.complement outer))).weight pair.2)
              else 0) =
              ∑ right,
                M.stateLaw.weight outer *
                  ((M.childLaw cell).weight symbol *
                    (M.childLaw (M.cellOf (M.complement outer))).weight right) := by
                rw [Fintype.sum_prod_type]
                simp
          _ = M.stateLaw.weight outer * (M.childLaw cell).weight symbol := by
                rw [← Finset.mul_sum, ← Finset.mul_sum,
                  (M.childLaw (M.cellOf (M.complement outer))).total]
                ring
      · simp [houter]
    _ = (M.stateLaw.pushforward M.cellOf).weight cell *
          (M.childLaw cell).weight symbol := by
      rw [ProbabilityVector.pushforward_weight, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro outer _
      by_cases houter : M.cellOf outer = cell <;> simp [houter]

/-- Right pooled-feature mass is the mass of states whose complementary child lies in the cell,
times that cell's symbol mass.  It is a separately labelled contribution even at fixed points. -/
theorem reference_rightFeature_weight
    [DecidableEq State] [DecidableEq Cell] [DecidableEq Symbol]
    (M : ComplementaryProductProjectionModel State Cell Symbol)
    (cell : Cell) (symbol : Symbol) :
    (M.reference.pushforward M.rightFeature).weight (cell, symbol) =
      (M.stateLaw.pushforward (M.cellOf ∘ M.complement)).weight cell *
        (M.childLaw cell).weight symbol := by
  classical
  rw [ProbabilityVector.pushforward_weight, Fintype.sum_prod_type]
  simp only [reference, rightFeature, ProbabilityVector.joint_weight]
  calc
    (∑ outer : State, ∑ pair : Symbol × Symbol,
        if (M.cellOf (M.complement outer), pair.2) = (cell, symbol) then
          M.stateLaw.weight outer *
            ((M.childLaw (M.cellOf outer)).weight pair.1 *
              (M.childLaw (M.cellOf (M.complement outer))).weight pair.2)
        else 0) =
        ∑ outer,
          if M.cellOf (M.complement outer) = cell then
            M.stateLaw.weight outer * (M.childLaw cell).weight symbol
          else 0 := by
      apply Finset.sum_congr rfl
      intro outer _
      by_cases houter : M.cellOf (M.complement outer) = cell
      · simp only [Prod.mk.injEq, houter, true_and]
        simp only [if_true]
        rw [Fintype.sum_prod_type]
        calc
          (∑ left, ∑ right,
              if right = symbol then
                M.stateLaw.weight outer *
                  ((M.childLaw (M.cellOf outer)).weight left *
                    (M.childLaw cell).weight right)
              else 0) =
              ∑ left,
                M.stateLaw.weight outer *
                  ((M.childLaw (M.cellOf outer)).weight left *
                    (M.childLaw cell).weight symbol) := by
                apply Finset.sum_congr rfl
                intro left _
                simp
          _ = M.stateLaw.weight outer * (M.childLaw cell).weight symbol := by
                rw [← Finset.mul_sum, ← Finset.sum_mul,
                  (M.childLaw (M.cellOf outer)).total]
                ring
      · simp [houter]
    _ = (M.stateLaw.pushforward (M.cellOf ∘ M.complement)).weight cell *
          (M.childLaw cell).weight symbol := by
      rw [ProbabilityVector.pushforward_weight, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro outer _
      by_cases houter : M.cellOf (M.complement outer) = cell <;> simp [houter]

/-- Closed form for the sum of the two labelled occurrence-feature marginals. -/
theorem reference_pooledFeature_weight
    [DecidableEq State] [DecidableEq Cell] [DecidableEq Symbol]
    (M : ComplementaryProductProjectionModel State Cell Symbol)
    (cell : Cell) (symbol : Symbol) :
    (M.reference.pushforward M.leftFeature).weight (cell, symbol) +
        (M.reference.pushforward M.rightFeature).weight (cell, symbol) =
      ((M.stateLaw.pushforward M.cellOf).weight cell +
          (M.stateLaw.pushforward (M.cellOf ∘ M.complement)).weight cell) *
        (M.childLaw cell).weight symbol := by
  rw [reference_leftFeature_weight, reference_rightFeature_weight]
  ring

/-- For a complementary-product reference, the coarse and pooled-feature equalities already
force absolute continuity.  A zero reference coordinate comes from either a zero state mass or a
zero child-symbol mass, and the corresponding pushforward fiber then has zero competing mass. -/
theorem isAbsolutelyContinuous_of_coarse_eq_of_pooledFeature_eq
    [DecidableEq State] [DecidableEq Cell] [DecidableEq Symbol]
    (M : ComplementaryProductProjectionModel State Cell Symbol)
    (q : ProbabilityVector (State × (Symbol × Symbol)))
    (hcoarse : q.pushforward M.coarse = M.reference.pushforward M.coarse)
    (hpool : ∀ feature,
      (q.pushforward M.leftFeature).weight feature +
          (q.pushforward M.rightFeature).weight feature =
        (M.reference.pushforward M.leftFeature).weight feature +
          (M.reference.pushforward M.rightFeature).weight feature) :
    q.IsAbsolutelyContinuous M.reference := by
  intro sample hrefzero
  have hfactor : M.stateLaw.weight sample.1 *
      ((M.childLaw (M.cellOf sample.1)).weight sample.2.1 *
        (M.childLaw (M.cellOf (M.complement sample.1))).weight sample.2.2) = 0 := by
    change M.stateLaw.weight sample.1 *
      ((M.childLaw (M.cellOf sample.1)).weight sample.2.1 *
        (M.childLaw (M.cellOf (M.complement sample.1))).weight sample.2.2) = 0 at hrefzero
    exact hrefzero
  rcases mul_eq_zero.mp hfactor with hstate | hchildren
  · have hfiber := ProbabilityVector.weight_le_pushforward_weight M.coarse q sample
    rw [hcoarse, reference_pushforward_coarse] at hfiber
    exact le_antisymm (by simpa [coarse, hstate] using hfiber) (q.nonneg sample)
  · rcases mul_eq_zero.mp hchildren with hleft | hright
    · have hpooled := hpool (M.cellOf sample.1, sample.2.1)
      rw [reference_pooledFeature_weight] at hpooled
      have hleftPush :
          (q.pushforward M.leftFeature).weight
              (M.cellOf sample.1, sample.2.1) = 0 := by
        have hleftNonneg :=
          (q.pushforward M.leftFeature).nonneg
            (M.cellOf sample.1, sample.2.1)
        have hrightNonneg :=
          (q.pushforward M.rightFeature).nonneg
            (M.cellOf sample.1, sample.2.1)
        simp only [hleft, mul_zero] at hpooled
        linarith
      have hfiber := ProbabilityVector.weight_le_pushforward_weight M.leftFeature q sample
      change q.weight sample ≤
        (q.pushforward M.leftFeature).weight
          (M.cellOf sample.1, sample.2.1) at hfiber
      rw [hleftPush] at hfiber
      exact le_antisymm hfiber (q.nonneg sample)
    · have hpooled := hpool
        (M.cellOf (M.complement sample.1), sample.2.2)
      rw [reference_pooledFeature_weight] at hpooled
      have hrightPush :
          (q.pushforward M.rightFeature).weight
              (M.cellOf (M.complement sample.1), sample.2.2) = 0 := by
        have hleftNonneg :=
          (q.pushforward M.leftFeature).nonneg
            (M.cellOf (M.complement sample.1), sample.2.2)
        have hrightNonneg :=
          (q.pushforward M.rightFeature).nonneg
            (M.cellOf (M.complement sample.1), sample.2.2)
        simp only [hright, mul_zero] at hpooled
        linarith
      have hfiber := ProbabilityVector.weight_le_pushforward_weight M.rightFeature q sample
      change q.weight sample ≤
        (q.pushforward M.rightFeature).weight
          (M.cellOf (M.complement sample.1), sample.2.2) at hfiber
      rw [hrightPush] at hfiber
      exact le_antisymm hfiber (q.nonneg sample)

/-- Coarse and pooled-feature equalities are therefore a complete feasibility interface for the
canonical sparse projection model. -/
theorem isFeasible_of_coarse_eq_of_pooledFeature_eq
    [DecidableEq State] [DecidableEq Cell] [DecidableEq Symbol]
    (M : ComplementaryProductProjectionModel State Cell Symbol)
    (q : ProbabilityVector (State × (Symbol × Symbol)))
    (hcoarse : q.pushforward M.coarse = M.reference.pushforward M.coarse)
    (hpool : ∀ feature,
      (q.pushforward M.leftFeature).weight feature +
          (q.pushforward M.rightFeature).weight feature =
        (M.reference.pushforward M.leftFeature).weight feature +
          (M.reference.pushforward M.rightFeature).weight feature) :
    M.toSparsePooledMarginalProjectionModel.IsFeasible q := by
  exact ⟨M.isAbsolutelyContinuous_of_coarse_eq_of_pooledFeature_eq q hcoarse hpool,
    hcoarse, hpool⟩

end ComplementaryProductProjectionModel

end AlgebraicComplexity
