/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinogradZeroOrientationOneSliceBase
import AlgebraicComplexity.Examples.CoppersmithWinogradZeroCoherentRestriction

set_option autoImplicit false

/-!
# Choice-free coherent one-slice bases in the rotated zero-`X` and zero-`Y` frames

Layer 4 (`AlgebraicComplexity/Examples/`).  `[DuanWuZhou2022]` section 6.3's leaf is the
localized segmented splitting power over the **fine** partition
`(cwPartitionedTensor K q).positivePower 1`, cut per segment to the split profile `alphatilde`.
Its value is *not* the weight of one fine word: a single word carries the bare product of its
per-pair matrix-multiplication volumes, while the paper's `V(T_{i,j,k}, alphatilde)` also carries
the **cardinality of the `alphatilde`-typical fibre** (`global_value.tex:336-346`,
`lem:non-rot-values`).  Recovering that cardinality is what the committed one-slice fusion stack
does, and this module supplies the one input it still lacks in the rotated frames.

## Why exactly twelve cells, and why they are the non-orbit ones

A level-two cell `(i,j,k)` has all its fine blocks sharing one **trivial** leg exactly when one of
`i, j, k` is zero: that leg's two level-one degrees are then both `0`, so every fine block carries
the same one-dimensional label there, and the blocks are pairwise distinct on the other two legs.
The fifteen cells of `cwSquareSupport` with a zero coordinate are precisely the twelve non-orbit
ones; `(1,1,2)`, `(1,2,1)` and `(2,1,1)` are exactly the cells with no zero coordinate, which is
the structural reason they are not matrix-multiplication tensors and need the three-symmetrized
`(112)` chain instead.

## What is proved here

`CoppersmithWinogradZeroCoherentRestriction.lean` supplies `cwZeroBaseCoherentRestriction`, the
**choice-free-payload** zero-`Z` base certificate: a supported base constituent's one-slice
restriction *bundled with* the proof that its shared-leg map is the canonical one.  That bundling
is what `CTensor.SharedOneSliceFiberData` needs, and it is why the convenience form
`cwZeroBaseRotatedOneSliceRestriction`
(`Examples/CoppersmithWinogradZeroOrientationOneSliceBase.lean`) cannot be used in its place: that
form's `legMap` is opaque, as its own docstring records.

The zero-`X` and zero-`Y` analogues did not exist.  This module adds them, assembled from the six
named rotated certificates of that same file, exactly as its docstring anticipates ("the zero-`X`
and zero-`Y` analogues of `cwZeroBaseCoherentRestriction` can be assembled from this module
without re-proving coherence in either orientation").  Nothing is re-proved in coordinates: the
rotation equivalence `cwBaseConstituentCycleSymmEquiv` is the identity on every leg, and the three
committed base maps already agree on the shared leg (`cwZeroBaseOneSliceMap_Z_coherent`, `rfl`).

Primary source: Ran Duan, Hongxun Wu and Renfei Zhou, *Faster Matrix Multiplication via Asymmetric
Hashing*, arXiv:2210.10173, `global_value.tex` section 6.3 and `lem:non-rot-values`.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor MoreAsymmetryCompatibility

universe u

variable (K : Type u) [CommRing K] (q : ℕ)

/-! ## The zero-`X` frame -/

/-- Canonical map on the shared zero-`X` block of one base CW constituent, read in the frame
`zeroOrientation .X = cycle.symm` that rotates `X` onto `Z`.  `CWPartitionBlockSpace` ignores its
leg argument, so this is the committed zero-`Z` canonical map at the same block label. -/
def cwZeroXBaseCanonicalZMap :
    CWPartitionBlockSpace K q .X .zero →ₗ[K] MMSpace K 1 1 1 .Z :=
  cw200OneSliceMap K q .Z

/-- **The zero-`X` coherent base certificate.**  A supported base constituent whose `X` label is
`.zero`, read in the frame that rotates `X` onto `Z`, together with its explicit one-slice
restriction and the retained proof that its shared-leg map is `cwZeroXBaseCanonicalZMap`. -/
noncomputable def cwZeroXBaseCoherentRestriction
    (support : cwBlockSupport) (hx : support.1 .X = .zero) :
    { C : OneSliceRestriction
        (Tensor.permute (K := K) cycle.symm (cwSupportedConstituent K q support))
        (cwBaseConstituentDimension q support (secondLiveLeg .X)) //
      HEq (C.legMap .Z) (cwZeroXBaseCanonicalZMap K q) } := by
  classical
  refine Classical.choice ?_
  rcases support with ⟨address, haddress⟩
  simp only [cwBlockSupport, Finset.mem_insert, Finset.mem_singleton] at haddress
  rcases haddress with rfl | rfl | rfl | rfl | rfl | rfl
  · simp [cw200, cwBlockAddress] at hx
  · exact ⟨⟨cw020ZeroXOneSliceRestriction K q, HEq.rfl⟩⟩
  · exact ⟨⟨cw002ZeroXOneSliceRestriction K q, HEq.rfl⟩⟩
  · exact ⟨⟨cw011ZeroXOneSliceRestriction K q, HEq.rfl⟩⟩
  · simp [cw101, cwBlockAddress] at hx
  · simp [cw110, cwBlockAddress] at hx

/-! ## The zero-`Y` frame -/

/-- Canonical map on the shared zero-`Y` block of one base CW constituent, read in the frame
`zeroOrientation .Y = cycle` that rotates `Y` onto `Z`. -/
def cwZeroYBaseCanonicalZMap :
    CWPartitionBlockSpace K q .Y .zero →ₗ[K] MMSpace K 1 1 1 .Z :=
  cw200OneSliceMap K q .Z

/-- **The zero-`Y` coherent base certificate**, the `cycle` analogue of
`cwZeroXBaseCoherentRestriction`. -/
noncomputable def cwZeroYBaseCoherentRestriction
    (support : cwBlockSupport) (hy : support.1 .Y = .zero) :
    { C : OneSliceRestriction
        (Tensor.permute (K := K) cycle (cwSupportedConstituent K q support))
        (cwBaseConstituentDimension q support (secondLiveLeg .Y)) //
      HEq (C.legMap .Z) (cwZeroYBaseCanonicalZMap K q) } := by
  classical
  refine Classical.choice ?_
  rcases support with ⟨address, haddress⟩
  simp only [cwBlockSupport, Finset.mem_insert, Finset.mem_singleton] at haddress
  rcases haddress with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨⟨cw200ZeroYOneSliceRestriction K q, HEq.rfl⟩⟩
  · simp [cw020, cwBlockAddress] at hy
  · exact ⟨⟨cw002ZeroYOneSliceRestriction K q, HEq.rfl⟩⟩
  · simp [cw011, cwBlockAddress] at hy
  · exact ⟨⟨cw101ZeroYOneSliceRestriction K q, HEq.rfl⟩⟩
  · simp [cw110, cwBlockAddress] at hy

end AlgebraicComplexity.Examples
