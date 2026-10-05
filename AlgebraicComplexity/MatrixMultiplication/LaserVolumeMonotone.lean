/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.LaserVolume

/-!
# Base monotonicity for volume-native laser extraction sequences

`SubexponentialLaserVolumeSequence` (`MatrixMultiplication/LaserVolume.lean`) is indexed by two
*bases*: a copy base bounding the retained direct-sum multiplicity, and a rectangular-volume base
bounding the product of the three side lengths.  Both bases occur in the structure only through
the two inequalities

* `copyBase ^ r ≤ loss r * count r`, and
* `volumeBase ^ r ≤ xSize r * ySize r * zSize r`.

Consequently a sequence is *antitone* in each base: any smaller positive base is also witnessed by
the very same finite data.

These weakenings and the source-transport constructor are what glue concrete constructions to
published endpoints.  Concrete
constructors emit whatever base the construction actually realizes — a natural number such as
`5 ^ m`, a quotient of certificate counts, or a power of two with an unrounded exponent.  Endpoint
theorems, by contrast, demand the normalized certificate shape `2 ^ (stride * floor)` for an exact
rational `floor`.  The two agree only up to an inequality, and these lemmas absorb exactly that
inequality without touching any of the finite degeneration data.

Both proofs are one application of monotonicity of `x ↦ x ^ r` on the nonnegative reals followed
by transitivity; every other field of the structure is transported unchanged.

## Scope note

Analogous weakenings for the derived records `WholeConstituentLaserVolumeSequenceData`
(`MatrixMultiplication/WholeConstituentLaserVolume.lean`), `NestedLaserVolumeSequenceData`
(`MatrixMultiplication/NestedLaserVolume.lean`) and `OuterConstituentSequenceData`
(`MatrixMultiplication/NestedLaserVolumeComposition.lean`) are still not provided here, and they
are owed.  The original obstruction is gone: all three records are committed.  What remains is
that none of them is a wrapper around the two theorems below.  Each record carries its own base
fields and its own growth inequalities, so its weakening is a fresh `{ data with … }` construction
repeating the `pow_le_pow_left₀` step on that record's own fields.  The right home for each is
therefore the module that defines the record, not this one, which would otherwise have to import
all three.
-/

namespace AlgebraicComplexity

open Tensor

universe u v w

variable {K : Type u} [CommSemiring K]
variable {V : Leg → Type v}
variable [∀ c, AddCommMonoid (V c)] [∀ c, Module K (V c)]

namespace SubexponentialLaserVolumeSequence

/-- Transport a volume-native extraction sequence backward along an exact restriction of source
tensors.

If `S` restricts to `T`, then every power of `S` restricts to the corresponding power of `T`.
Composing that restriction with each finite extraction from `T` preserves the stride, copy and
volume bases, and all counting data.  This is the semantic adapter used when a certificate is
constructed on a selected or coarsened partition whose realization is itself obtained from the
original source tensor. -/
noncomputable def of_restricts
    {W : Leg → Type w} [∀ c, AddCommMonoid (W c)] [∀ c, Module K (W c)]
    {S : Tensor3 K W} {T : Tensor3 K V} {stride : ℕ}
    {copyBase volumeBase : ℝ}
    (hST : Restricts S T)
    (h : SubexponentialLaserVolumeSequence K T stride copyBase volumeBase) :
    SubexponentialLaserVolumeSequence K S stride copyBase volumeBase where
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
  extract := fun r hr ↦
    (PolynomialDegenerates.of_restricts (hST.power (stride * r))).trans (h.extract r hr)
  copy_growth := h.copy_growth
  volume_growth := h.volume_growth

/-- Weakening a volume-native extraction sequence along its **copy** base.

The same finite data (loss, counts, side lengths, and degenerations) witnesses every positive copy
base below the original one, because `copyBase` enters the structure only through the growth
inequality `copyBase ^ r ≤ loss r * count r` and `x ↦ x ^ r` is monotone on `[0, ∞)`. -/
noncomputable def mono_copyBase {T : Tensor3 K V} {stride : ℕ}
    {copyBase copyBase' volumeBase : ℝ}
    (hpos : 0 < copyBase') (hle : copyBase' ≤ copyBase)
    (h : SubexponentialLaserVolumeSequence K T stride copyBase volumeBase) :
    SubexponentialLaserVolumeSequence K T stride copyBase' volumeBase :=
  { h with
    copyBase_pos := hpos
    copy_growth := fun r hr =>
      le_trans (pow_le_pow_left₀ hpos.le hle r) (h.copy_growth r hr) }

/-- Weakening a volume-native extraction sequence along its **rectangular-volume** base.

Dual to `mono_copyBase`: `volumeBase` enters only through
`volumeBase ^ r ≤ xSize r * ySize r * zSize r`. -/
noncomputable def mono_volumeBase {T : Tensor3 K V} {stride : ℕ}
    {copyBase volumeBase volumeBase' : ℝ}
    (hpos : 0 < volumeBase') (hle : volumeBase' ≤ volumeBase)
    (h : SubexponentialLaserVolumeSequence K T stride copyBase volumeBase) :
    SubexponentialLaserVolumeSequence K T stride copyBase volumeBase' :=
  { h with
    volumeBase_pos := hpos
    volume_growth := fun r hr =>
      le_trans (pow_le_pow_left₀ hpos.le hle r) (h.volume_growth r hr) }

/-- Simultaneous weakening in both bases; the composite of `mono_copyBase` and
`mono_volumeBase`.  This is the form endpoint theorems consume, since a concrete construction
normally realizes both bases only up to an inequality. -/
noncomputable def mono {T : Tensor3 K V} {stride : ℕ}
    {copyBase copyBase' volumeBase volumeBase' : ℝ}
    (hcopyPos : 0 < copyBase') (hcopy : copyBase' ≤ copyBase)
    (hvolumePos : 0 < volumeBase') (hvolume : volumeBase' ≤ volumeBase)
    (h : SubexponentialLaserVolumeSequence K T stride copyBase volumeBase) :
    SubexponentialLaserVolumeSequence K T stride copyBase' volumeBase' :=
  mono_volumeBase hvolumePos hvolume (mono_copyBase hcopyPos hcopy h)

end SubexponentialLaserVolumeSequence

namespace UniformLaserVolumeBaseExtraction

/-- The same copy-base weakening for the finite interface `UniformLaserVolumeBaseExtraction`.

Here the copy base appears logarithmically, as `r * (log copyBase - eta) ≤ log count`, so the
monotonicity step is `Real.log_le_log` instead of `pow_le_pow_left`. -/
theorem mono_copyBase {T : Tensor3 K V} {stride : ℕ} {copyBase copyBase' volumeBase : ℝ}
    (hpos : 0 < copyBase') (hle : copyBase' ≤ copyBase)
    (h : UniformLaserVolumeBaseExtraction K T stride copyBase volumeBase) :
    UniformLaserVolumeBaseExtraction K T stride copyBase' volumeBase := by
  refine ⟨h.stride_pos, hpos, h.volumeBase_pos, ?_⟩
  intro eta heta
  obtain ⟨r, count, m, n, p, hr, hcount, hm, hn, hp, hdeg, hcopy, hvolume⟩ := h.extract eta heta
  refine ⟨r, count, m, n, p, hr, hcount, hm, hn, hp, hdeg, ?_, hvolume⟩
  have hlog : Real.log copyBase' ≤ Real.log copyBase := Real.log_le_log hpos hle
  have hrNonneg : (0 : ℝ) ≤ (r : ℝ) := Nat.cast_nonneg r
  nlinarith

/-- The same rectangular-volume weakening for the finite interface. -/
theorem mono_volumeBase {T : Tensor3 K V} {stride : ℕ} {copyBase volumeBase volumeBase' : ℝ}
    (hpos : 0 < volumeBase') (hle : volumeBase' ≤ volumeBase)
    (h : UniformLaserVolumeBaseExtraction K T stride copyBase volumeBase) :
    UniformLaserVolumeBaseExtraction K T stride copyBase volumeBase' := by
  refine ⟨h.stride_pos, h.copyBase_pos, hpos, ?_⟩
  intro eta heta
  obtain ⟨r, count, m, n, p, hr, hcount, hm, hn, hp, hdeg, hcopy, hvolume⟩ := h.extract eta heta
  refine ⟨r, count, m, n, p, hr, hcount, hm, hn, hp, hdeg, hcopy, ?_⟩
  have hlog : Real.log volumeBase' ≤ Real.log volumeBase := Real.log_le_log hpos hle
  have hrNonneg : (0 : ℝ) ≤ (r : ℝ) := Nat.cast_nonneg r
  nlinarith

end UniformLaserVolumeBaseExtraction

end AlgebraicComplexity
