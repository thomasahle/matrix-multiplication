/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinograd112CyclicValue
import AlgebraicComplexity.Examples.CoppersmithWinograd112TypedLeaf

/-!
# Conventional entropy formula for the cyclic CW `112` value

The finite extraction theorem naturally produces factorial-entropy bases.  This module converts
those bases into the notation used in the Coppersmith--Winograd literature.  For the rational
profile `(L,L,G,G)`, put `μ = L / (2(L+G))`.  The two side marginals are uniform binary laws,
whereas the shared marginal is `(μ,μ,1-2μ)`.

The endpoint identifies the kernel-checked cyclic extraction rate with

`log 2 * (2 - H₂(μ,μ,1-2μ) + ω (2-2μ) log₂ q) / 3`.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor
open scoped BigOperators

universe u

private local instance : Nonempty CW112Side := ⟨.first⟩
private local instance : Nonempty CW112ZBlock := ⟨.firstCorner⟩

/-- The binary side profile has the expected total mass `2(L+G)`. -/
@[simp] theorem cw112SideMarginalType_profileMass (L G : ℕ) :
    WordType.profileMass (cw112SideMarginalType L G) = cw112CyclicStride L G := by
  unfold WordType.profileMass
  rw [show (Finset.univ : Finset CW112Side) = {.first, .second} by decide]
  simp [cw112SideMarginalType, cw112CyclicStride]
  omega

/-- The three-block shared-Z profile has the same total mass `2(L+G)`. -/
@[simp] theorem cw112ZMarginalType_profileMass (L G : ℕ) :
    WordType.profileMass (cw112ZMarginalType L G) = cw112CyclicStride L G := by
  unfold WordType.profileMass
  rw [show (Finset.univ : Finset CW112ZBlock) =
    {.firstCorner, .secondCorner, .grid} by decide]
  simp [cw112ZMarginalType, cw112CyclicStride]
  omega

/-- The entropy in nats of the balanced binary side profile is `log 2`.

Proof sketch: after dividing both equal counts `L+G` by their total `2(L+G)`, both normalized
weights are `1/2`; expanding `negMulLog` gives the claim. -/
theorem cw112SideMarginalType_profileEntropyNats
    {L G : ℕ} (hLG : 0 < L + G) :
    WordType.profileEntropyNats (cw112SideMarginalType L G) = Real.log 2 := by
  have hsum : (0 : ℝ) < L + G := by exact_mod_cast hLG
  have hhalf : ((L + G : ℕ) : ℝ) / (cw112CyclicStride L G : ℕ) = 1 / 2 := by
    simp only [cw112CyclicStride]
    push_cast
    field_simp [hsum.ne']
  unfold WordType.profileEntropyNats
  rw [show (Finset.univ : Finset CW112Side) = {.first, .second} by decide]
  simp only [Finset.sum_insert, Finset.mem_singleton, reduceCtorEq, not_false_eq_true,
    Finset.sum_singleton, cw112SideMarginalType, cw112SideMarginalType_profileMass]
  rw [hhalf, Real.negMulLog_eq_neg]
  have hlogHalf : Real.log (1 / 2 : ℝ) = -Real.log 2 := by
    rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num, Real.log_inv]
  change -((1 / 2 : ℝ) * Real.log (1 / 2)) +
      -((1 / 2 : ℝ) * Real.log (1 / 2)) = Real.log 2
  rw [hlogHalf]
  ring

/-- The entropy in nats of the shared-Z profile is `log 2` times its conventional base-two
entropy `H₂(μ,μ,1-2μ)`.

Proof sketch: normalize `(L,L,2G)` by `2(L+G)`, identify the resulting weights with
`(μ,μ,1-2μ)`, and unfold the base conversion. -/
theorem cw112ZMarginalType_profileEntropyNats
    {L G : ℕ} (hLG : 0 < L + G) :
    WordType.profileEntropyNats (cw112ZMarginalType L G) =
      Real.log 2 * cw112MuEntropyBits L G := by
  have hsum : (0 : ℝ) < L + G := by exact_mod_cast hLG
  have hfirst :
      (L : ℝ) / (cw112CyclicStride L G : ℕ) = cw112Mu L G := by
    simp only [cw112CyclicStride, cw112Mu]
  have hgrid :
      ((2 * G : ℕ) : ℝ) / (cw112CyclicStride L G : ℕ) =
        1 - 2 * cw112Mu L G := by
    simp only [cw112CyclicStride, cw112Mu]
    push_cast
    field_simp [hsum.ne']
    ring
  unfold WordType.profileEntropyNats
  rw [show (Finset.univ : Finset CW112ZBlock) =
    {.firstCorner, .secondCorner, .grid} by decide]
  simp only [Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton, reduceCtorEq,
    or_false, not_false_eq_true, Finset.sum_singleton, cw112ZMarginalType,
    cw112ZMarginalType_profileMass]
  rw [hfirst, hgrid]
  unfold cw112MuEntropyBits
  have hlogTwo : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num)).ne'
  field_simp [hlogTwo]
  ring

/-- The logarithm of the side method-of-types base is one bit for each source letter. -/
theorem log_cw112SideEntropyBase
    {L G : ℕ} (hLG : 0 < L + G) :
    Real.log (cw112SideEntropyBase L G) =
      (cw112CyclicStride L G : ℝ) * Real.log 2 := by
  have hprofile : ∀ b, 0 < cw112SideMarginalType L G b := by
    intro b
    cases b <;> simpa [cw112SideMarginalType] using hLG
  unfold cw112SideEntropyBase
  rw [WordType.log_proportionalEntropyBase _ hprofile,
    cw112SideMarginalType_profileMass,
    cw112SideMarginalType_profileEntropyNats hLG]

/-- The logarithm of the shared-Z method-of-types base is its ternary entropy times the source
stride. -/
theorem log_cw112ZEntropyBase
    {L G : ℕ} (hL : 0 < L) (hG : 0 < G) :
    Real.log (cw112ZEntropyBase L G) =
      (cw112CyclicStride L G : ℝ) *
        (Real.log 2 * cw112MuEntropyBits L G) := by
  have hprofile : ∀ b, 0 < cw112ZMarginalType L G b := by
    intro b
    cases b <;> simp [cw112ZMarginalType, hL, hG]
  unfold cw112ZEntropyBase
  rw [WordType.log_proportionalEntropyBase _ hprofile,
    cw112ZMarginalType_profileMass,
    cw112ZMarginalType_profileEntropyNats (Nat.add_pos_left hL G)]

/-- The cyclic copy exponent is the two binary marginal entropies minus the one shared-Z
entropy. -/
theorem log_cw112CyclicCopyBase
    {L G : ℕ} (hL : 0 < L) (hG : 0 < G) :
    Real.log (cw112CyclicCopyBase L G) =
      (cw112CyclicStride L G : ℝ) * Real.log 2 *
        (2 - cw112MuEntropyBits L G) := by
  have hsidePos := (cw112MarginalEntropyBases_pos L G).1
  have hzPos := (cw112MarginalEntropyBases_pos L G).2
  unfold cw112CyclicCopyBase
  rw [Real.log_div (pow_ne_zero 2 hsidePos.ne') hzPos.ne', Real.log_pow,
    log_cw112SideEntropyBase (Nat.add_pos_left hL G),
    log_cw112ZEntropyBase hL hG]
  ring

/-- The logarithm of the cyclic matrix-volume base is its defining integer exponent times
`log q`. -/
theorem log_cw112CyclicVolumeBase (q L G : ℕ) :
    Real.log (cw112CyclicVolumeBase q L G) =
      (3 * (4 * G + 2 * L) : ℕ) * Real.log q := by
  unfold cw112CyclicVolumeBase
  rw [Real.log_pow]

/-- The proved direct-sum cyclic rate has the displayed `μ`-entropy expression.

Proof sketch: substitute the preceding copy and volume logarithms.  The sole remaining identity
is `(4G+2L)/(2(L+G)) = 2-2μ`; changing from natural logarithms to bits supplies the common
factor `log 2`. -/
theorem cw112CyclicRate_eq_muEntropyFormula
    (K : Type u) [CommSemiring K]
    {q L G : ℕ} (hL : 0 < L) (hG : 0 < G) :
    ((Real.log (cw112CyclicCopyBase L G) +
          (omega K / 3) * Real.log (cw112CyclicVolumeBase q L G)) /
        (3 * cw112CyclicStride L G)) =
      Real.log 2 *
        ((2 - cw112MuEntropyBits L G +
            omega K * (2 - 2 * cw112Mu L G) * cw112LogQBits q) / 3) := by
  rw [log_cw112CyclicCopyBase hL hG, log_cw112CyclicVolumeBase]
  unfold cw112CyclicStride cw112Mu cw112LogQBits
  push_cast
  have hsum : (0 : ℝ) < L + G := by
    exact_mod_cast Nat.add_pos_left hL G
  have hlogTwo : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num)).ne'
  field_simp [hsum.ne', hlogTwo]
  ring

section

variable (K : Type u) [CommRing K]

/-- The unconditional direct-sum cyclic extraction theorem in `μ`-entropy notation.

The minus sign before `cw112MuEntropyBits` records the loss from flattening shared-Z groups.  The
historical optimized `112` lemma instead has the corresponding plus sign and still requires its
superadditive C-tensor-family aggregation proof. -/
theorem cw112_hasCyclicLaserExtractionRate_muEntropy
    (q L G : ℕ) (hq : 0 < q) (hL : 0 < L) (hG : 0 < G) :
    HasCyclicLaserExtractionRate K (cw112PartitionedTensor K q).realize
      (Real.log 2 *
        ((2 - cw112MuEntropyBits L G +
            omega K * (2 - 2 * cw112Mu L G) * cw112LogQBits q) / 3)) := by
  rw [← cw112CyclicRate_eq_muEntropyFormula K hL hG]
  exact cw112_hasCyclicLaserExtractionRate K q L G hq hL hG

end

end AlgebraicComplexity.Examples
