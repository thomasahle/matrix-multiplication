/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Analysis.Subexponential
import AlgebraicComplexity.MatrixMultiplication.Laser

/-!
# Volume-native laser extraction

The rectangular asymptotic sum inequality depends on a matrix-multiplication tensor
`\<m,n,p\>` only through its volume `m * n * p`.  Numerical laser certificates likewise often
certify the sum of the three logarithmic side exponents directly, without separate lower bounds
for each side.  This file provides the matching semantic interface.

`UniformLaserVolumeBaseExtraction` is the direct finite interface.  The second structure,
`SubexponentialLaserVolumeSequence`, is the form naturally produced by type counting, hashing,
and hole repair: every repetition is available, but the copy count may suffer a certified
subexponential multiplicative loss.  The main adapter absorbs that loss and produces the direct
interface without taking limits or choosing rounded side lengths.

The analytic step from a finite extraction to a logarithmic rate is *not* repeated here: both rate
theorems below reduce to the shared tail `HasLaserExtractionRate.of_uniformVolumeGrowth` of
`MatrixMultiplication/Laser.lean`.  The only content local to this file is the volume-native
packaging and the subexponential-loss absorption (`exists_pos_log_loss_le_mul`).
-/

namespace AlgebraicComplexity

open Tensor

universe u v w x

section Semiring

variable (K : Type u) [CommSemiring K]
variable {V : Leg → Type v}
variable [∀ c, AddCommMonoid (V c)] [∀ c, Module K (V c)]

/-- Assemble independently repaired groups into the matrix-multiplication direct sum consumed by
the laser interface.

This is the finite semantic bridge after grouped compatibility cleanup.  The first restriction
exhibits the cleaned tensor as an indexed direct sum of group tensors; the second family turns
each repaired group into its rectangular matrix-multiplication tensor.  Exact restrictions apply
componentwise, and hence also give a polynomial degeneration. -/
theorem PolynomialDegenerates.of_restricts_indexedDirectSum_matrixMultiplication
    {I : Type w} [Fintype I]
    {U : Leg → Type x}
    [∀ c, AddCommMonoid (U c)] [∀ c, Module K (U c)]
    {W : I → Leg → Type v}
    [∀ i c, AddCommMonoid (W i c)] [∀ i c, Module K (W i c)]
    {T : Tensor3 K U} {groups : ∀ i, Tensor3 K (W i)}
    {m n p : I → ℕ}
    (hgroups : Restricts T (Tensor.indexedDirectSum groups))
    (hleaves : ∀ i, Restricts (groups i)
      (matrixMultiplication (K := K) (m i) (n i) (p i))) :
    PolynomialDegenerates T (matrixMultiplicationDirectSum K m n p) := by
  apply PolynomialDegenerates.of_restricts
  exact hgroups.trans (Restricts.indexedDirectSum hleaves)

/-- Finite uniform extractions specified by a copy base and one rectangular-volume base.

At repetition `r`, the source is `T ^ (stride * r)`.  The output is a direct sum of `count`
copies of `\<m,n,p\>`.  The count is allowed an arbitrary logarithmic loss `eta * r`, while the
product `m*n*p` realizes the volume base exactly at the exponent level. -/
structure UniformLaserVolumeBaseExtraction (T : Tensor3 K V)
    (stride : ℕ) (copyBase volumeBase : ℝ) : Prop where
  stride_pos : 0 < stride
  copyBase_pos : 0 < copyBase
  volumeBase_pos : 0 < volumeBase
  extract : ∀ eta : ℝ, 0 < eta →
    ∃ (r count m n p : ℕ),
      0 < r ∧ 0 < count ∧ 0 < m ∧ 0 < n ∧ 0 < p ∧
        PolynomialDegenerates (Tensor.power T (stride * r))
          (matrixMultiplicationDirectSum (ι := Fin count) K
            (fun _ ↦ m) (fun _ ↦ n) (fun _ ↦ p)) ∧
        (r : ℝ) * (Real.log copyBase - eta) ≤ Real.log count ∧
        (r : ℝ) * Real.log volumeBase ≤
          Real.log (((m * n * p : ℕ) : ℝ))

namespace UniformLaserVolumeBaseExtraction

/-- A volume-native finite extraction gives its logarithmic laser rate.

This is exactly the shared tail `HasLaserExtractionRate.of_uniformVolumeGrowth` of
`MatrixMultiplication/Laser.lean` at `copyLog = log copyBase` and `volumeLog = log volumeBase`:
the `extract` field is already stated in the logarithmic form that lemma consumes, so no
individual side lower bounds are needed. -/
theorem hasLaserExtractionRate
    {T : Tensor3 K V} {stride : ℕ} {copyBase volumeBase : ℝ}
    (h : UniformLaserVolumeBaseExtraction K T stride copyBase volumeBase) :
    HasLaserExtractionRate K T
      ((Real.log copyBase + (omega K / 3) * Real.log volumeBase) / stride) :=
  HasLaserExtractionRate.of_uniformVolumeGrowth K h.stride_pos h.extract

/-- Base-two form used by numerical certificates.

If one stride has retained exponent `retained` and mean rectangular side exponent `volume`,
then its volume base is `2^(3 * stride * volume)`.  The resulting rate is exactly
`log 2 * (retained + omega * volume)`. -/
theorem hasLaserExtractionRate_bits
    {T : Tensor3 K V} {stride : ℕ} {retained volume : ℝ}
    (h : UniformLaserVolumeBaseExtraction K T stride
      ((2 : ℝ) ^ ((stride : ℝ) * retained))
      ((2 : ℝ) ^ (3 * (stride : ℝ) * volume))) :
    HasLaserExtractionRate K T
      (Real.log 2 * (retained + omega K * volume)) := by
  have hrate := h.hasLaserExtractionRate
  convert hrate using 1
  rw [Real.log_rpow (by norm_num : (0 : ℝ) < 2),
    Real.log_rpow (by norm_num : (0 : ℝ) < 2)]
  have hstride : (stride : ℝ) ≠ 0 := by exact_mod_cast h.stride_pos.ne'
  field_simp [hstride]

end UniformLaserVolumeBaseExtraction

/-! ## Absorbing a subexponential finite loss -/

/-- A uniform family of finite extractions whose copy count loses a subexponential factor.

This is the natural common target for concrete type-counting, hashing, compatibility cleanup,
and hole-repair theorems.  Every field is finite and directly checkable.  The only asymptotic
hypothesis is `loss_subexponential`; standard polynomial, Behrend, and repair losses already have
instances in the analysis library. -/
structure SubexponentialLaserVolumeSequence (T : Tensor3 K V)
    (stride : ℕ) (copyBase volumeBase : ℝ) where
  stride_pos : 0 < stride
  copyBase_pos : 0 < copyBase
  volumeBase_pos : 0 < volumeBase
  loss : ℕ → ℝ
  count : ℕ → ℕ
  xSize : ℕ → ℕ
  ySize : ℕ → ℕ
  zSize : ℕ → ℕ
  loss_subexponential : Growth.Subexponential loss
  loss_pos : ∀ r, 0 < r → 0 < loss r
  count_pos : ∀ r, 0 < r → 0 < count r
  xSize_pos : ∀ r, 0 < r → 0 < xSize r
  ySize_pos : ∀ r, 0 < r → 0 < ySize r
  zSize_pos : ∀ r, 0 < r → 0 < zSize r
  extract : ∀ r, 0 < r →
    PolynomialDegenerates (Tensor.power T (stride * r))
      (matrixMultiplicationDirectSum (ι := Fin (count r)) K
        (fun _ ↦ xSize r) (fun _ ↦ ySize r) (fun _ ↦ zSize r))
  copy_growth : ∀ r, 0 < r →
    copyBase ^ r ≤ loss r * (count r : ℝ)
  volume_growth : ∀ r, 0 < r →
    volumeBase ^ r ≤ (((xSize r * ySize r * zSize r : ℕ) : ℝ))

namespace SubexponentialLaserVolumeSequence

/-- A positive subexponential sequence has logarithm at most `eta * r` for some positive
repetition `r`.  This is the exact analytic step that absorbs all finite counting and repair
losses in the laser interface. -/
theorem exists_pos_log_loss_le_mul
    {loss : ℕ → ℝ} (hloss : Growth.Subexponential loss)
    (hlossPos : ∀ r, 0 < r → 0 < loss r)
    {eta : ℝ} (heta : 0 < eta) :
    ∃ r : ℕ, 0 < r ∧ Real.log (loss r) ≤ (r : ℝ) * eta := by
  let delta : ℝ := Real.exp (eta / 2)
  have hdelta : 1 < delta := by
    dsimp [delta]
    rw [Real.one_lt_exp_iff]
    linarith
  obtain ⟨C, hC, hbound⟩ := hloss.2 delta hdelta
  obtain ⟨N : ℕ, hN⟩ := exists_nat_ge (2 * Real.log C / eta)
  let r := N + 1
  have hr : 0 < r := by dsimp [r]; omega
  have hlogC : Real.log C ≤ (r : ℝ) * (eta / 2) := by
    have hNcast : 2 * Real.log C / eta ≤ (N : ℝ) := hN
    have hNleR : (N : ℝ) ≤ (r : ℝ) := by
      dsimp [r]
      norm_num
    have hetaNonzero : eta ≠ 0 := heta.ne'
    have := hNcast.trans hNleR
    field_simp [hetaNonzero] at this ⊢
    nlinarith
  have hlossUpper := hbound r
  have hlossLog :
      Real.log (loss r) ≤ Real.log C + (r : ℝ) * Real.log delta := by
    calc
      Real.log (loss r) ≤ Real.log (C * delta ^ r) :=
        Real.log_le_log (hlossPos r hr) hlossUpper
      _ = Real.log C + (r : ℝ) * Real.log delta := by
        rw [Real.log_mul hC.ne' (pow_ne_zero _ (ne_of_gt (zero_lt_one.trans hdelta))),
          Real.log_pow]
  have hlogDelta : Real.log delta = eta / 2 := by
    dsimp [delta]
    rw [Real.log_exp]
  refine ⟨r, hr, ?_⟩
  rw [hlogDelta] at hlossLog
  exact hlossLog.trans (by nlinarith [hlogC])

/-- A finite extraction sequence with subexponential copy loss realizes the corresponding
volume-native base extraction. -/
theorem toUniformLaserVolumeBaseExtraction
    {T : Tensor3 K V} {stride : ℕ} {copyBase volumeBase : ℝ}
    (h : SubexponentialLaserVolumeSequence K T stride copyBase volumeBase) :
    UniformLaserVolumeBaseExtraction K T stride copyBase volumeBase := by
  refine ⟨h.stride_pos, h.copyBase_pos, h.volumeBase_pos, ?_⟩
  intro eta heta
  obtain ⟨r, hr, hlossLog⟩ :=
    exists_pos_log_loss_le_mul h.loss_subexponential h.loss_pos heta
  refine ⟨r, h.count r, h.xSize r, h.ySize r, h.zSize r, hr,
    h.count_pos r hr, h.xSize_pos r hr, h.ySize_pos r hr, h.zSize_pos r hr,
    h.extract r hr, ?_, ?_⟩
  · have hcopyLog :
        Real.log (copyBase ^ r) ≤
          Real.log (h.loss r * (h.count r : ℝ)) :=
      Real.log_le_log (pow_pos h.copyBase_pos r) (h.copy_growth r hr)
    rw [Real.log_pow,
      Real.log_mul (h.loss_pos r hr).ne'
        (by exact_mod_cast (h.count_pos r hr).ne')] at hcopyLog
    nlinarith
  · have hvolumeLog :
        Real.log (volumeBase ^ r) ≤
          Real.log (((h.xSize r * h.ySize r * h.zSize r : ℕ) : ℝ)) :=
      Real.log_le_log (pow_pos h.volumeBase_pos r) (h.volume_growth r hr)
    rwa [Real.log_pow] at hvolumeLog

/-- Direct rate consequence of a subexponential finite extraction sequence. -/
theorem hasLaserExtractionRate
    {T : Tensor3 K V} {stride : ℕ} {copyBase volumeBase : ℝ}
    (h : SubexponentialLaserVolumeSequence K T stride copyBase volumeBase) :
    HasLaserExtractionRate K T
      ((Real.log copyBase + (omega K / 3) * Real.log volumeBase) / stride) :=
  h.toUniformLaserVolumeBaseExtraction.hasLaserExtractionRate

/-- Base-two rate consequence in retained-exponent and mean-volume coordinates. -/
theorem hasLaserExtractionRate_bits
    {T : Tensor3 K V} {stride : ℕ} {retained volume : ℝ}
    (h : SubexponentialLaserVolumeSequence K T stride
      ((2 : ℝ) ^ ((stride : ℝ) * retained))
      ((2 : ℝ) ^ (3 * (stride : ℝ) * volume))) :
    HasLaserExtractionRate K T
      (Real.log 2 * (retained + omega K * volume)) :=
  h.toUniformLaserVolumeBaseExtraction.hasLaserExtractionRate_bits

end SubexponentialLaserVolumeSequence

end Semiring

end AlgebraicComplexity
