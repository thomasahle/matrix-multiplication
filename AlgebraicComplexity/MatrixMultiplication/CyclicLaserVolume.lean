/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.LaserVolume
import AlgebraicComplexity.MatrixMultiplication.CyclicLaserRate

/-!
# Cyclic laser extraction with volume bounds

Exceptional constituents in recursive laser arguments need not individually degenerate to one
matrix-multiplication tensor.  Their standard value is instead witnessed after multiplying a
power by its two cyclic leg orientations.  This module records that semantic interface without
mentioning any Coppersmith--Winograd support or parameters.

The lightweight relation `HasCyclicLaserExtractionRate` and its ordinary-rate normalization live
in `CyclicLaserRate.lean`.  This file adds the certificate-friendly sequence form: every
proportional repetition has an exact degeneration, while its copy count may lose a proved
subexponential factor.  The final theorem absorbs that loss and exposes the cyclic logarithmic
rate used by downstream partitioned-tensor clients.
-/

namespace AlgebraicComplexity

open Tensor

universe u v

section Semiring

variable (K : Type u) [CommSemiring K]
variable {V : Leg → Type v}
variable [∀ c, AddCommMonoid (V c)] [∀ c, Module K (V c)]

/-- A cyclic finite extraction sequence with a subexponential copy-count loss.

At repetition `r`, the source contains the three orientations of `T^(stride*r)`.  The output is
`count r` copies of one rectangular matrix-multiplication tensor.  Only its total volume is
specified, because Schönhage's rectangular asymptotic sum inequality depends on the three side
lengths through their product. -/
structure SubexponentialCyclicLaserVolumeSequence (T : Tensor3 K V)
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
    PolynomialDegenerates (cyclicPowerProduct K T (stride * r))
      (matrixMultiplicationDirectSum (ι := Fin (count r)) K
        (fun _ ↦ xSize r) (fun _ ↦ ySize r) (fun _ ↦ zSize r))
  copy_growth : ∀ r, 0 < r →
    copyBase ^ r ≤ loss r * (count r : ℝ)
  volume_growth : ∀ r, 0 < r →
    volumeBase ^ r ≤ (((xSize r * ySize r * zSize r : ℕ) : ℝ))

namespace SubexponentialCyclicLaserVolumeSequence

/-- Regard a cyclic extraction sequence as an ordinary sequence for the single
three-orientation product tensor.

The numerical data is unchanged.  The only semantic work is source coherence: at every positive
exponent, `cyclicPowerProduct_positive` transports the supplied cyclic degeneration to a
degeneration from the corresponding ordinary power.  Keeping this adapter separate lets the
ordinary subexponential-loss theorem remain the sole analytic implementation. -/
noncomputable def toSubexponentialLaserVolumeSequence
    {T : Tensor3 K V} {stride : ℕ} {copyBase volumeBase : ℝ}
    (h : SubexponentialCyclicLaserVolumeSequence K T stride copyBase volumeBase) :
    SubexponentialLaserVolumeSequence K
      (Tensor.external
        (Tensor.external T (Tensor.permute cycle T))
        (Tensor.permute cycle.symm T))
      stride copyBase volumeBase where
  stride_pos := h.stride_pos
  copyBase_pos := h.copyBase_pos
  volumeBase_pos := h.volumeBase_pos
  loss := h.loss
  count := h.count
  xSize := h.xSize
  ySize := h.ySize
  zSize := h.zSize
  loss_subexponential := h.loss_subexponential
  loss_pos := h.loss_pos
  count_pos := h.count_pos
  xSize_pos := h.xSize_pos
  ySize_pos := h.ySize_pos
  zSize_pos := h.zSize_pos
  extract := by
    intro r hr
    obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero
      (Nat.mul_pos h.stride_pos hr).ne'
    have hextract := h.extract r hr
    rw [hj] at hextract ⊢
    exact
      (PolynomialDegenerates.of_restricts
        (Tensor.Isomorphic.cyclicPowerProduct_positive T j).symm.restricts).trans
          hextract
  copy_growth := h.copy_growth
  volume_growth := h.volume_growth

/-- A cyclic extraction sequence with subexponential loss achieves its normalized cyclic rate.

Proof sketch: transport the sequence to the ordinary three-orientation tensor with
`toSubexponentialLaserVolumeSequence`, invoke the shared ordinary subexponential-loss tail, and
then apply `HasLaserExtractionRate.toCyclic` to divide the rate by three. -/
theorem hasCyclicLaserExtractionRate
    {T : Tensor3 K V} {stride : ℕ} {copyBase volumeBase : ℝ}
    (h : SubexponentialCyclicLaserVolumeSequence K T stride copyBase volumeBase) :
    HasCyclicLaserExtractionRate K T
      ((Real.log copyBase + (omega K / 3) * Real.log volumeBase) /
        (3 * stride)) := by
  have hrate :=
    (h.toSubexponentialLaserVolumeSequence K).hasLaserExtractionRate.toCyclic K
  convert hrate using 1
  have hstrideNe : (stride : ℝ) ≠ 0 := by exact_mod_cast h.stride_pos.ne'
  field_simp [hstrideNe]

end SubexponentialCyclicLaserVolumeSequence

end Semiring

end AlgebraicComplexity
