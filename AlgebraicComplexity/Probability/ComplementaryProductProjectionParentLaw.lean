/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.InterfaceTensor
import AlgebraicComplexity.Probability.ComplementaryOccurrenceProjection
import AlgebraicComplexity.Probability.ComplementaryProductProjectionCore

set_option autoImplicit false

/-!
# Parent laws of complementary conditional-product models

The parent law of a complementary-product projection model is a mixture of independent pairs of
child laws.  When the parent symbol is the canonical concatenation of two split words, its fiber
contains exactly the pair of consecutive halves.  This file records the resulting pointwise
formula independently of any Coppersmith--Winograd construction or certificate.
-/

open scoped BigOperators

namespace AlgebraicComplexity
namespace ComplementaryProductProjectionModel

universe u v

variable {State : Type u} {Cell : Type v}
variable [Fintype State] [Fintype Cell]

/-- The probability of a concatenated parent word is the state mixture of the two corresponding
child-word probabilities. -/
theorem parentLaw_concatSplitWords_weight
    {depth : ℕ}
    (M : ComplementaryProductProjectionModel State Cell (SplitWord depth))
    (word : SplitWord (depth + 1)) :
    (M.parentLaw (fun pair ↦ concatSplitWords pair.1 pair.2)).weight word =
      ∑ state,
        M.stateLaw.weight state *
          ((M.childLaw (M.cellOf state)).weight (splitWordSuccEquiv depth word).1 *
            (M.childLaw (M.cellOf (M.complement state))).weight
              (splitWordSuccEquiv depth word).2) := by
  classical
  unfold parentLaw
  rw [ProbabilityVector.pushforward_weight, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro state _
  simp only [reference, Function.comp_apply, ProbabilityVector.joint_weight]
  have hconcat (pair : SplitWord depth × SplitWord depth) :
      concatSplitWords pair.1 pair.2 = word ↔
        pair = splitWordSuccEquiv depth word := by
    constructor
    · intro h
      simpa only [splitWordSuccEquiv_concatSplitWords] using
        congrArg (splitWordSuccEquiv depth) h
    · rintro rfl
      exact (splitWordSuccEquiv depth).symm_apply_apply word
  simp only [hconcat]
  rw [Finset.sum_eq_single (splitWordSuccEquiv depth word)]
  · simp only
    rfl
  · intro other _ hother
    simp [hother]
  · simp

/-- An exact state-count law and exact normalized child rows identify the concatenated parent
law with the normalized weighted product of the two child count tables.  Child-row identities are
required only on states of positive outer count; zero outer states contribute nothing regardless
of the arbitrary law used to fill a zero pooled row. -/
theorem parentLaw_concatSplitWords_weight_eq_normalizedCounts
    {depth : ℕ}
    (M : ComplementaryProductProjectionModel State Cell (SplitWord depth))
    (stateCount : State → ℕ)
    (leftCount rightCount : State → SplitWord depth → ℕ)
    (stateSamples childSamples parentSamples : ℕ)
    (hstate : ∀ state,
      M.stateLaw.weight state = (stateCount state : ℝ) / stateSamples)
    (hleft : ∀ state word, stateCount state ≠ 0 →
      (M.childLaw (M.cellOf state)).weight word =
        (leftCount state word : ℝ) / childSamples)
    (hright : ∀ state word, stateCount state ≠ 0 →
      (M.childLaw (M.cellOf (M.complement state))).weight word =
        (rightCount state word : ℝ) / childSamples)
    (hparentSamples : parentSamples = stateSamples * (childSamples * childSamples))
    (word : SplitWord (depth + 1)) :
    (M.parentLaw (fun pair ↦ concatSplitWords pair.1 pair.2)).weight word =
      ((∑ state, stateCount state *
        (leftCount state (splitWordSuccEquiv depth word).1 *
          rightCount state (splitWordSuccEquiv depth word).2) : ℕ) : ℝ) /
        parentSamples := by
  rw [M.parentLaw_concatSplitWords_weight word]
  calc
    (∑ state,
        M.stateLaw.weight state *
          ((M.childLaw (M.cellOf state)).weight (splitWordSuccEquiv depth word).1 *
            (M.childLaw (M.cellOf (M.complement state))).weight
              (splitWordSuccEquiv depth word).2)) =
        ∑ state,
          ((stateCount state *
            (leftCount state (splitWordSuccEquiv depth word).1 *
              rightCount state (splitWordSuccEquiv depth word).2) : ℕ) : ℝ) /
            parentSamples := by
      apply Finset.sum_congr rfl
      intro state _
      rw [hstate state]
      by_cases hzero : stateCount state = 0
      · simp [hzero]
      · rw [hleft state _ hzero, hright state _ hzero, hparentSamples]
        simp only [Nat.cast_mul]
        rw [div_mul_div_comm
            (leftCount state (splitWordSuccEquiv depth word).1 : ℝ) childSamples
            (rightCount state (splitWordSuccEquiv depth word).2 : ℝ) childSamples,
          div_mul_div_comm
            (stateCount state : ℝ) stateSamples
            ((leftCount state (splitWordSuccEquiv depth word).1 : ℝ) *
              rightCount state (splitWordSuccEquiv depth word).2)
            ((childSamples : ℝ) * childSamples)]
    _ = ((∑ state, stateCount state *
          (leftCount state (splitWordSuccEquiv depth word).1 *
            rightCount state (splitWordSuccEquiv depth word).2) : ℕ) : ℝ) /
        parentSamples := by
      rw [Nat.cast_sum]
      simp only [div_eq_mul_inv, Finset.sum_mul]

end ComplementaryProductProjectionModel

namespace ComplementaryOccurrenceLaw

universe u v w

private theorem cancel_scaled_child_row
    (a samples count k : ℕ) (ha : 0 < a) (hsamples : 0 < samples) (hk : 0 < k) :
    (((a * samples * count * k : ℕ) : ℝ) /
        ((a * (samples * samples) * k : ℕ) : ℝ)) =
      (count : ℝ) / samples := by
  have hcommon : 0 < a * samples * k := by positivity
  rw [show a * samples * count * k = count * (a * samples * k) by ac_rfl,
    show a * (samples * samples) * k = samples * (a * samples * k) by ac_rfl]
  simp only [Nat.cast_mul]
  apply mul_div_mul_right
  exact_mod_cast hcommon.ne'

variable {State : Type u} [Fintype State] [DecidableEq State]
variable {Symbol : Type v} [Fintype Symbol] [DecidableEq Symbol] [Nonempty Symbol]
variable {profile : State → ℕ}

/-- If an exact pooled row and its mass have a common positive scaled-product factor, then its
normalized probability row is the remaining child profile divided by its sample size.  Keeping
the factorization abstract prevents certificate-specific count definitions from entering the
kernel term. -/
theorem normalizedChildLaw_weight_of_scaled_row
    (law : ComplementaryOccurrenceLaw profile Symbol)
    (complement : Equiv.Perm State) (state : State) (symbol : Symbol)
    (a samples count k : ℕ)
    (ha : 0 < a) (hsamples : 0 < samples) (hk : 0 < k)
    (hrow : law.cellJointProfile complement id (state, symbol) =
      a * samples * count * k)
    (hmass : childOccurrenceMass profile complement state =
      a * (samples * samples) * k) :
    (law.normalizedChildLaw complement state).weight symbol =
      (count : ℝ) / samples := by
  have hmassPos : 0 < childOccurrenceMass profile complement state := by
    rw [hmass]
    positivity
  rw [law.normalizedChildLaw_weight_of_pos complement state hmassPos, hrow, hmass]
  exact cancel_scaled_child_row a samples count k ha hsamples hk

end ComplementaryOccurrenceLaw
end AlgebraicComplexity
