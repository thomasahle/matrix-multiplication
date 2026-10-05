/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Probability.PooledMarginalProjectionCore

/-!
# Complementary conditional-product projection models: core definitions

An ordered recursive state produces two labelled occurrences.  The left occurrence uses the
law pooled in its compatibility cell; the right occurrence uses the law pooled in the cell of a
complementary state.  This file defines the resulting conditional-product reference law and its
sparse pooled information-projection model.  Marginal identities and the paper-facing inequalities
are split into later modules so each proof stays inexpensive to elaborate.
-/

namespace AlgebraicComplexity

universe u v w x

/-- A law on ordered states, a compatibility-cell quotient, one child-symbol law per cell, and a
permutation describing the right child state.  Recursive CW clients specialize the permutation
to an involution, but none of the information-projection arguments needs that stronger
hypothesis. -/
structure ComplementaryProductProjectionModel
    (State : Type u) (Cell : Type v) (Symbol : Type w)
    [Fintype State] [Fintype Cell] [Fintype Symbol] where
  stateLaw : ProbabilityVector State
  complement : Equiv.Perm State
  cellOf : State → Cell
  childLaw : Cell → ProbabilityVector Symbol

namespace ComplementaryProductProjectionModel

variable {State : Type u} {Cell : Type v} {Symbol : Type w}
variable [Fintype State] [Fintype Cell] [Fintype Symbol]

/-- Fine reference law: sample an ordered state, then sample the two child symbols independently
from the pooled laws of its left and complementary right cells. -/
def reference (M : ComplementaryProductProjectionModel State Cell Symbol) :
    ProbabilityVector (State × (Symbol × Symbol)) :=
  M.stateLaw.joint fun state ↦
    (M.childLaw (M.cellOf state)).product
      (M.childLaw (M.cellOf (M.complement state)))

/-- Ordered-state statistic of a fine sample. -/
def coarse (_M : ComplementaryProductProjectionModel State Cell Symbol) :
    State × (Symbol × Symbol) → State :=
  Prod.fst

/-- Labelled left occurrence, indexed by the cell of the ordered state. -/
def leftFeature (M : ComplementaryProductProjectionModel State Cell Symbol) :
    State × (Symbol × Symbol) → Cell × Symbol :=
  fun sample ↦ (M.cellOf sample.1, sample.2.1)

/-- Labelled right occurrence, indexed by the cell of the complementary state. -/
def rightFeature (M : ComplementaryProductProjectionModel State Cell Symbol) :
    State × (Symbol × Symbol) → Cell × Symbol :=
  fun sample ↦ (M.cellOf (M.complement sample.1), sample.2.2)

/-- Parent law induced by joining the two child symbols. -/
def parentLaw {Parent : Type x} [Fintype Parent] [DecidableEq Parent]
    (M : ComplementaryProductProjectionModel State Cell Symbol)
    (join : Symbol × Symbol → Parent) : ProbabilityVector Parent :=
  M.reference.pushforward (join ∘ Prod.snd)

/-- The complementary conditional-product reference is a sparse pooled-marginal projection. -/
noncomputable def toSparsePooledMarginalProjectionModel
    (M : ComplementaryProductProjectionModel State Cell Symbol) :
    SparsePooledMarginalProjectionModel
      (State × (Symbol × Symbol)) State (Cell × Symbol) where
  reference := M.reference
  coarse := M.coarse
  leftFeature := M.leftFeature
  rightFeature := M.rightFeature
  coarsePotential state := Real.log (M.stateLaw.weight state)
  featurePotential entry := Real.log ((M.childLaw entry.1).weight entry.2)
  log_reference_weight sample hpositive := by
    let state := sample.1
    let left := sample.2.1
    let right := sample.2.2
    have hstateNonneg : 0 ≤ M.stateLaw.weight state := M.stateLaw.nonneg state
    have hleftNonneg : 0 ≤ (M.childLaw (M.cellOf state)).weight left :=
      (M.childLaw (M.cellOf state)).nonneg left
    have hrightNonneg :
        0 ≤ (M.childLaw (M.cellOf (M.complement state))).weight right :=
      (M.childLaw (M.cellOf (M.complement state))).nonneg right
    have hproduct : 0 < M.stateLaw.weight state *
        ((M.childLaw (M.cellOf state)).weight left *
          (M.childLaw (M.cellOf (M.complement state))).weight right) := by
      change 0 < M.stateLaw.weight sample.1 *
        ((M.childLaw (M.cellOf sample.1)).weight sample.2.1 *
          (M.childLaw (M.cellOf (M.complement sample.1))).weight sample.2.2) at hpositive
      simpa only [state, left, right] using hpositive
    have hstate : 0 < M.stateLaw.weight state := by
      by_contra hnot
      have hzero : M.stateLaw.weight state = 0 :=
        le_antisymm (not_lt.mp hnot) hstateNonneg
      simp [hzero] at hproduct
    have hchildren : 0 < (M.childLaw (M.cellOf state)).weight left *
        (M.childLaw (M.cellOf (M.complement state))).weight right := by
      by_contra hnot
      have hzero : (M.childLaw (M.cellOf state)).weight left *
          (M.childLaw (M.cellOf (M.complement state))).weight right = 0 :=
        le_antisymm (not_lt.mp hnot) (mul_nonneg hleftNonneg hrightNonneg)
      simp [hzero] at hproduct
    have hleft : 0 < (M.childLaw (M.cellOf state)).weight left := by
      by_contra hnot
      have hzero : (M.childLaw (M.cellOf state)).weight left = 0 :=
        le_antisymm (not_lt.mp hnot) hleftNonneg
      simp [hzero] at hchildren
    have hright :
        0 < (M.childLaw (M.cellOf (M.complement state))).weight right := by
      by_contra hnot
      have hzero :
          (M.childLaw (M.cellOf (M.complement state))).weight right = 0 :=
        le_antisymm (not_lt.mp hnot) hrightNonneg
      simp [hzero] at hchildren
    change Real.log (M.stateLaw.weight state *
        ((M.childLaw (M.cellOf state)).weight left *
          (M.childLaw (M.cellOf (M.complement state))).weight right)) = _
    rw [Real.log_mul hstate.ne' hchildren.ne',
      Real.log_mul hleft.ne' hright.ne']
    rfl

@[simp] theorem toSparsePooledMarginalProjectionModel_reference
    (M : ComplementaryProductProjectionModel State Cell Symbol) :
    M.toSparsePooledMarginalProjectionModel.reference = M.reference :=
  rfl

@[simp] theorem toSparsePooledMarginalProjectionModel_coarse
    (M : ComplementaryProductProjectionModel State Cell Symbol) :
    M.toSparsePooledMarginalProjectionModel.coarse = Prod.fst :=
  rfl

@[simp] theorem toSparsePooledMarginalProjectionModel_leftFeature
    (M : ComplementaryProductProjectionModel State Cell Symbol) :
    M.toSparsePooledMarginalProjectionModel.leftFeature = M.leftFeature :=
  rfl

@[simp] theorem toSparsePooledMarginalProjectionModel_rightFeature
    (M : ComplementaryProductProjectionModel State Cell Symbol) :
    M.toSparsePooledMarginalProjectionModel.rightFeature = M.rightFeature :=
  rfl

end ComplementaryProductProjectionModel

end AlgebraicComplexity
