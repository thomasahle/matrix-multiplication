/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Probability.Coupling
import AlgebraicComplexity.Probability.SupportRestrictionDataProcessing

/-!
# Conditional entropy after coarsening one coordinate

Let `joint` be a finite law on `S × T`, and let `coarse : T → C` be a deterministic statistic of
the second coordinate.  Deterministic data processing for KL divergence gives

`H(S,T) ≤ H(T) + H(S | coarse(T))`.

The main theorems below state this inequality directly for `ProbabilityVector`.  They are useful
when a type-counting argument fixes the joint `(source, coarse-target)` profile but allows the
full target type to vary: any separate upper bound on the target entropy can then be added to the
fixed conditional source entropy.  No tensor, word type, or certificate data appears here.
-/

namespace AlgebraicComplexity
namespace ProbabilityVector

universe u v w

variable {S : Type u} {T : Type v} {C : Type w}
variable [Fintype S] [Fintype T] [Fintype C]
variable [DecidableEq S] [DecidableEq T] [DecidableEq C]

/-- Coarsening the right coordinate can only increase the uncertainty of the left coordinate.

Equivalently,
`H(S,T) ≤ H(T) + H(S, coarse(T)) - H(coarse(T))`.

Proof sketch: regard `joint` as the canonical coupling of its two marginals.  Apply deterministic
data processing for KL divergence to the identity on `S` and `coarse` on `T`, rewrite divergence
from the product of the marginals as the entropy-subadditivity gap, and rearrange. -/
theorem entropy_le_right_add_conditionalEntropy_coarsenedRight
    (joint : ProbabilityVector (S × T)) (coarse : T → C) :
    joint.entropy ≤
      (joint.pushforward Prod.snd).entropy +
        (joint.pushforward fun st ↦ (st.1, coarse st.2)).conditionalEntropy Prod.snd := by
  let left : ProbabilityVector S := joint.pushforward Prod.fst
  let right : ProbabilityVector T := joint.pushforward Prod.snd
  let coarsened : ProbabilityVector (S × C) :=
    joint.pushforward fun st ↦ (st.1, coarse st.2)
  have hjoint : joint.IsCoupling left right := IsCoupling.marginals joint
  have hcoarsened : coarsened.IsCoupling
      (left.pushforward id) (right.pushforward coarse) :=
    hjoint.pushforward_prodMap id coarse
  have hid : left.pushforward id = left := by
    classical
    ext s
    simp only [pushforward_weight, id_eq]
    rw [Finset.sum_eq_single s]
    · simp
    · intro t _ hts
      simp [hts]
    · simp
  have hcoarsened' : coarsened.IsCoupling left (right.pushforward coarse) := by
    simpa only [hid] using hcoarsened
  have hreference :
      (left.product right).pushforward (fun st ↦ (st.1, coarse st.2)) =
        left.product (right.pushforward coarse) := by
    simpa only [id_eq, hid] using
      (pushforward_product_prodMap left right id coarse)
  have hdata := klDiv_pushforward_le_of_absoluteContinuity
    (fun st : S × T ↦ (st.1, coarse st.2)) joint (left.product right)
      hjoint.isAbsolutelyContinuous_product
  rw [hreference] at hdata
  change coarsened.klDiv (left.product (right.pushforward coarse)) ≤
    joint.klDiv (left.product right) at hdata
  rw [hcoarsened'.klDiv_product_eq_entropy_gap,
    hjoint.klDiv_product_eq_entropy_gap] at hdata
  unfold conditionalEntropy
  rw [hcoarsened'.2]
  dsimp only [left, right, coarsened] at hdata ⊢
  linarith

/-- Base-two form of `entropy_le_right_add_conditionalEntropy_coarsenedRight`. -/
theorem entropyBits_le_right_add_conditionalEntropyBits_coarsenedRight
    (joint : ProbabilityVector (S × T)) (coarse : T → C) :
    joint.entropyBits ≤
      (joint.pushforward Prod.snd).entropyBits +
        (joint.pushforward fun st ↦ (st.1, coarse st.2)).conditionalEntropyBits Prod.snd := by
  have h := entropy_le_right_add_conditionalEntropy_coarsenedRight joint coarse
  have hlogTwo : 0 ≤ Real.log 2 := (Real.log_pos (by norm_num)).le
  unfold entropyBits conditionalEntropyBits
  calc
    joint.entropy / Real.log 2 ≤
        ((joint.pushforward Prod.snd).entropy +
          (joint.pushforward fun st ↦ (st.1, coarse st.2)).conditionalEntropy Prod.snd) /
            Real.log 2 :=
      div_le_div_of_nonneg_right h hlogTwo
    _ = (joint.pushforward Prod.snd).entropy / Real.log 2 +
        (joint.pushforward fun st ↦ (st.1, coarse st.2)).conditionalEntropy Prod.snd /
          Real.log 2 := by rw [add_div]

/-- A target-entropy ceiling and a coarsened conditional-entropy ceiling add to a joint-entropy
ceiling.  This is the certificate-facing form of the data-processing inequality. -/
theorem entropyBits_le_add_of_right_le_of_coarsenedConditional_le
    (joint : ProbabilityVector (S × T)) (coarse : T → C)
    (targetUpper conditionalUpper : ℝ)
    (htarget : (joint.pushforward Prod.snd).entropyBits ≤ targetUpper)
    (hconditional :
      (joint.pushforward fun st ↦ (st.1, coarse st.2)).conditionalEntropyBits Prod.snd ≤
        conditionalUpper) :
    joint.entropyBits ≤ targetUpper + conditionalUpper := by
  exact (entropyBits_le_right_add_conditionalEntropyBits_coarsenedRight joint coarse).trans
    (add_le_add htarget hconditional)

end ProbabilityVector
end AlgebraicComplexity
