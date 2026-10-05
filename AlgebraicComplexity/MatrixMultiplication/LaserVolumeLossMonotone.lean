/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.SubexponentialVolumeLoss

/-!
# Base monotonicity for loss-aware laser-volume sequences

`SubexponentialLaserVolumeLossSequence` is the loss-aware companion to
`SubexponentialLaserVolumeSequence`: besides a subexponential loss in the retained copy count, it
also permits a separate subexponential loss in the rectangular volume.  Its two bases occur only
through the inequalities

* `copyBase ^ r ≤ copyLoss r * count r`, and
* `volumeBase ^ r ≤ volumeLoss r * (xSize r * ySize r * zSize r)`.

Consequently the structure is antitone in either base.  A smaller positive copy or volume base is
witnessed by exactly the same finite extraction data, including both loss functions and all their
subexponentiality and positivity proofs.

This module also provides source transport.  If `S` restricts to `T`, then the restriction of the
corresponding tensor powers can be composed with every extraction from `T`.  Again no numerical
or loss data changes.

## Proof sketches

For source transport, power the given restriction at `stride * r` and compose it with the stored
polynomial degeneration.  For either base weakening, monotonicity of `x ↦ x ^ r` on the
nonnegative reals puts the new power below the old one; transitivity with the stored growth bound
finishes the proof.  Simultaneous weakening is the composition of the two one-base constructions.
-/

namespace AlgebraicComplexity

open Tensor

universe u v w

variable {K : Type u} [CommSemiring K]
variable {V : Leg → Type v}
variable [∀ c, AddCommMonoid (V c)] [∀ c, Module K (V c)]

namespace SubexponentialLaserVolumeLossSequence

/-- Transport a loss-aware laser-volume sequence backward along an exact restriction of source
tensors.

At repetition `r`, the powered restriction from `S` to `T` is composed with the extraction stored
by `h`.  The stride, bases, finite sizes, both loss functions, and every numerical proof are
inherited verbatim. -/
noncomputable def of_restricts
    {W : Leg → Type w} [∀ c, AddCommMonoid (W c)] [∀ c, Module K (W c)]
    {S : Tensor3 K W} {T : Tensor3 K V} {stride : ℕ}
    {copyBase volumeBase : ℝ}
    (hST : Restricts S T)
    (h : SubexponentialLaserVolumeLossSequence K T stride copyBase volumeBase) :
    SubexponentialLaserVolumeLossSequence K S stride copyBase volumeBase where
  stride_pos := h.stride_pos
  copyBase_pos := h.copyBase_pos
  volumeBase_pos := h.volumeBase_pos
  copyLoss := h.copyLoss
  volumeLoss := h.volumeLoss
  count := h.count
  xSize := h.xSize
  ySize := h.ySize
  zSize := h.zSize
  copyLoss_subexponential := h.copyLoss_subexponential
  volumeLoss_subexponential := h.volumeLoss_subexponential
  copyLoss_pos := h.copyLoss_pos
  volumeLoss_pos := h.volumeLoss_pos
  count_pos := h.count_pos
  xSize_pos := h.xSize_pos
  ySize_pos := h.ySize_pos
  zSize_pos := h.zSize_pos
  extract := fun r hr ↦
    (PolynomialDegenerates.of_restricts (hST.power (stride * r))).trans (h.extract r hr)
  copy_growth := h.copy_growth
  volume_growth := h.volume_growth

/-- Weaken the copy base of a loss-aware laser-volume sequence.

The old copy-growth bound remains valid after first applying monotonicity of the `r`th power.  All
finite extraction data and both loss witnesses are preserved unchanged. -/
noncomputable def mono_copyBase {T : Tensor3 K V} {stride : ℕ}
    {copyBase copyBase' volumeBase : ℝ}
    (hpos : 0 < copyBase') (hle : copyBase' ≤ copyBase)
    (h : SubexponentialLaserVolumeLossSequence K T stride copyBase volumeBase) :
    SubexponentialLaserVolumeLossSequence K T stride copyBase' volumeBase :=
  { h with
    copyBase_pos := hpos
    copy_growth := fun r hr ↦
      le_trans (pow_le_pow_left₀ hpos.le hle r) (h.copy_growth r hr) }

/-- Weaken the rectangular-volume base of a loss-aware laser-volume sequence.

This is the volume analogue of `mono_copyBase`: monotonicity of the `r`th power is composed with
the stored volume-growth inequality, while the copy loss and volume loss remain unchanged. -/
noncomputable def mono_volumeBase {T : Tensor3 K V} {stride : ℕ}
    {copyBase volumeBase volumeBase' : ℝ}
    (hpos : 0 < volumeBase') (hle : volumeBase' ≤ volumeBase)
    (h : SubexponentialLaserVolumeLossSequence K T stride copyBase volumeBase) :
    SubexponentialLaserVolumeLossSequence K T stride copyBase volumeBase' :=
  { h with
    volumeBase_pos := hpos
    volume_growth := fun r hr ↦
      le_trans (pow_le_pow_left₀ hpos.le hle r) (h.volume_growth r hr) }

/-- Simultaneously weaken the copy and rectangular-volume bases of a loss-aware sequence.

The construction first applies `mono_copyBase` and then `mono_volumeBase`, so both loss functions
and their proofs are the original fields of `h`. -/
noncomputable def mono {T : Tensor3 K V} {stride : ℕ}
    {copyBase copyBase' volumeBase volumeBase' : ℝ}
    (hcopyPos : 0 < copyBase') (hcopy : copyBase' ≤ copyBase)
    (hvolumePos : 0 < volumeBase') (hvolume : volumeBase' ≤ volumeBase)
    (h : SubexponentialLaserVolumeLossSequence K T stride copyBase volumeBase) :
    SubexponentialLaserVolumeLossSequence K T stride copyBase' volumeBase' :=
  mono_volumeBase hvolumePos hvolume (mono_copyBase hcopyPos hcopy h)

end SubexponentialLaserVolumeLossSequence

end AlgebraicComplexity
