/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinogradZeroCTensor
import AlgebraicComplexity.Examples.CoppersmithWinogradZeroOrientation
import AlgebraicComplexity.MatrixMultiplication.ZeroCoordinateOrientationRetyping

/-!
# Retyping an exact zero-coordinate CW interface as a C-tensor, in every orientation

`CoppersmithWinogradZeroCTensor` turns the zero-`Z` support law into an explicit C-tensor
restriction with `support.card` constituents.  This module does the same for the zero-`X` and
zero-`Y` families, and re-derives the zero-`Z` one, from the orientation-indexed support law of
`CoppersmithWinogradZeroOrientation` and the generic leg-permutation transport of
`ZeroCoordinateOrientationRetyping`.

## The rotation is in the statement

`CTensor.FiberRetyping` requires the shared block on `Z`.  A zero-`X` family is therefore retyped
after rotating its legs by `MoreAsymmetryCompatibility.zeroOrientation .X = Tensor.cycle.symm`,
and a zero-`Y` family by `zeroOrientation .Y = Tensor.cycle`; the zero-`Z` rotation is the
identity, so the `Z` statement below is the committed one with a `Tensor.permute 1` in front.
Every conclusion names its rotation, so a client cannot pair a rotated tensor with an unrotated
leaf dimension by accident — the one failure mode the leg convention of
`better_bound/r4_scoping/OBLIGATIONS.md` §9.1 makes easy.

Rotating back is deliberately *not* done here: `Tensor.permute e.symm (Tensor.permute e T)` is only
isomorphic to `T`, and the rotation belongs with the leaf packaging, beside
`ZeroCoordinateMerge.mergeX` / `mergeY` / `mergeZ`.

## What is proved

For each orientation: an ambient `FiberRetyping` of the *rotated* selected family, whose target leg
spaces are the full permuted ambient partitioned spaces (so the only linear maps are block
inclusions), and the restriction of the rotated interface tensor onto its canonically enumerated
C-tensor.  No representative selection occurs and no local constituent restriction is hidden in a
constructor; the numerical one-slice identification is intentionally not assumed.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor MoreAsymmetryCompatibility

universe u

/-- The permuted ambient block spaces of one exact CW interface term, at the rotation that carries
a zero at leg `zero` onto `Z`. -/
abbrev CWRotatedInterfaceBlockSpace
    (K : Type u) [CommRing K] (q depth n : ℕ) (zero : Leg) :=
  PermutedBlockSpace (zeroOrientation zero) (CWExactInterfaceBlockSpace K q depth n)

/-! ## The zero-`X` orientation -/

/-- Canonical whole-support C-tensor retyping of a zero-`X` exact CW interface term, after the
rotation `zeroOrientation .X = Tensor.cycle.symm` that carries its shared `X` block onto `Z`. -/
noncomputable def cwSelectedExactInterfaceTerm_zeroX_ambientFiberRetyping
    (K : Type u) [CommRing K] (q : ℕ) {depth n : ℕ}
    (term : ExactInterfaceTermParameters depth)
    (hmultiplicity : term.multiplicity = n + 1)
    (hx : term.index.count .X = 0) :
    CTensor.FiberRetyping
      (X := PartitionedSpace K (CWRotatedInterfaceBlockSpace K q depth n .X) .X)
      (Y := PartitionedSpace K (CWRotatedInterfaceBlockSpace K q depth n .X) .Y)
      (Z := PartitionedSpace K (CWRotatedInterfaceBlockSpace K q depth n .X) .Z)
      ((cwSelectedExactInterfaceTerm K q term hmultiplicity).permute (zeroOrientation .X))
      ((cwSelectedExactInterfaceTerm K q term hmultiplicity).permute (zeroOrientation .X)).support
      ((cwSelectedExactInterfaceTerm K q term hmultiplicity).permute
        (zeroOrientation .X)).support.card := by
  have hsupport :=
    cwSelectedExactInterfaceTerm_zeroX_support_isSharedFiber K q term hmultiplicity hx
  exact CTensor.FiberRetyping.ofSharedSupportPermutedAmbient
    (cwSelectedExactInterfaceTerm K q term hmultiplicity) (zeroOrientation .X)
    hsupport.2.1 hsupport.2.2 (cwZeroInterfaceLegWord depth n) hsupport.1

/-- The rotated zero-`X` interface tensor restricts to its canonically enumerated C-tensor, which
has `support.card` constituents.  No representative selection occurs. -/
theorem cwSelectedExactInterfaceTerm_zeroX_restricts_rotatedAmbientCTensor
    (K : Type u) [CommRing K] (q : ℕ) {depth n : ℕ}
    (term : ExactInterfaceTermParameters depth)
    (hmultiplicity : term.multiplicity = n + 1)
    (hx : term.index.count .X = 0) :
    Restricts
      (Tensor.permute (zeroOrientation .X)
        (cwSelectedExactInterfaceTerm K q term hmultiplicity).realize)
      (CTensor.partitioned
        (cwSelectedExactInterfaceTerm_zeroX_ambientFiberRetyping
          K q term hmultiplicity hx).targetConstituent).realize := by
  have hsupport :=
    cwSelectedExactInterfaceTerm_zeroX_support_isSharedFiber K q term hmultiplicity hx
  exact CTensor.FiberRetyping.restricts_permute_ofSharedSupportPermutedAmbient
    (cwSelectedExactInterfaceTerm K q term hmultiplicity) (zeroOrientation .X)
    hsupport.2.1 hsupport.2.2 (cwZeroInterfaceLegWord depth n) hsupport.1

/-! ## The zero-`Y` orientation -/

/-- Canonical whole-support C-tensor retyping of a zero-`Y` exact CW interface term, after the
rotation `zeroOrientation .Y = Tensor.cycle` that carries its shared `Y` block onto `Z`. -/
noncomputable def cwSelectedExactInterfaceTerm_zeroY_ambientFiberRetyping
    (K : Type u) [CommRing K] (q : ℕ) {depth n : ℕ}
    (term : ExactInterfaceTermParameters depth)
    (hmultiplicity : term.multiplicity = n + 1)
    (hy : term.index.count .Y = 0) :
    CTensor.FiberRetyping
      (X := PartitionedSpace K (CWRotatedInterfaceBlockSpace K q depth n .Y) .X)
      (Y := PartitionedSpace K (CWRotatedInterfaceBlockSpace K q depth n .Y) .Y)
      (Z := PartitionedSpace K (CWRotatedInterfaceBlockSpace K q depth n .Y) .Z)
      ((cwSelectedExactInterfaceTerm K q term hmultiplicity).permute (zeroOrientation .Y))
      ((cwSelectedExactInterfaceTerm K q term hmultiplicity).permute (zeroOrientation .Y)).support
      ((cwSelectedExactInterfaceTerm K q term hmultiplicity).permute
        (zeroOrientation .Y)).support.card := by
  have hsupport :=
    cwSelectedExactInterfaceTerm_zero_support_isSharedFiber K q term hmultiplicity .Y hy
  exact CTensor.FiberRetyping.ofSharedSupportPermutedAmbient
    (cwSelectedExactInterfaceTerm K q term hmultiplicity) (zeroOrientation .Y)
    hsupport.2.1 hsupport.2.2 (cwZeroInterfaceLegWord depth n) hsupport.1

/-- The rotated zero-`Y` interface tensor restricts to its canonically enumerated C-tensor, which
has `support.card` constituents.  No representative selection occurs. -/
theorem cwSelectedExactInterfaceTerm_zeroY_restricts_rotatedAmbientCTensor
    (K : Type u) [CommRing K] (q : ℕ) {depth n : ℕ}
    (term : ExactInterfaceTermParameters depth)
    (hmultiplicity : term.multiplicity = n + 1)
    (hy : term.index.count .Y = 0) :
    Restricts
      (Tensor.permute (zeroOrientation .Y)
        (cwSelectedExactInterfaceTerm K q term hmultiplicity).realize)
      (CTensor.partitioned
        (cwSelectedExactInterfaceTerm_zeroY_ambientFiberRetyping
          K q term hmultiplicity hy).targetConstituent).realize := by
  have hsupport :=
    cwSelectedExactInterfaceTerm_zero_support_isSharedFiber K q term hmultiplicity .Y hy
  exact CTensor.FiberRetyping.restricts_permute_ofSharedSupportPermutedAmbient
    (cwSelectedExactInterfaceTerm K q term hmultiplicity) (zeroOrientation .Y)
    hsupport.2.1 hsupport.2.2 (cwZeroInterfaceLegWord depth n) hsupport.1

/-! ## The zero-`Z` orientation, at the identity rotation -/

/-- Canonical whole-support C-tensor retyping of a zero-`Z` exact CW interface term through the
same generic transport, at the identity rotation `zeroOrientation .Z = 1`.

The committed `cwSelectedExactInterfaceTerm_zeroZ_ambientFiberRetyping` is the same object without
the (inert) `permute 1`; it is untouched, and this one exists to certify that the transport
specializes correctly. -/
noncomputable def cwSelectedExactInterfaceTerm_zeroZ_rotatedAmbientFiberRetyping
    (K : Type u) [CommRing K] (q : ℕ) {depth n : ℕ}
    (term : ExactInterfaceTermParameters depth)
    (hmultiplicity : term.multiplicity = n + 1)
    (hz : term.index.count .Z = 0) :
    CTensor.FiberRetyping
      (X := PartitionedSpace K (CWRotatedInterfaceBlockSpace K q depth n .Z) .X)
      (Y := PartitionedSpace K (CWRotatedInterfaceBlockSpace K q depth n .Z) .Y)
      (Z := PartitionedSpace K (CWRotatedInterfaceBlockSpace K q depth n .Z) .Z)
      ((cwSelectedExactInterfaceTerm K q term hmultiplicity).permute (zeroOrientation .Z))
      ((cwSelectedExactInterfaceTerm K q term hmultiplicity).permute (zeroOrientation .Z)).support
      ((cwSelectedExactInterfaceTerm K q term hmultiplicity).permute
        (zeroOrientation .Z)).support.card := by
  have hsupport :=
    cwSelectedExactInterfaceTerm_zeroZ_support_isSharedFiber' K q term hmultiplicity hz
  exact CTensor.FiberRetyping.ofSharedSupportPermutedAmbient
    (cwSelectedExactInterfaceTerm K q term hmultiplicity) (zeroOrientation .Z)
    hsupport.2.1 hsupport.2.2 (cwZeroInterfaceLegWord depth n) hsupport.1

/-- The zero-`Z` interface tensor restricts to its canonically enumerated C-tensor through the
generic transport at the identity rotation. -/
theorem cwSelectedExactInterfaceTerm_zeroZ_restricts_rotatedAmbientCTensor
    (K : Type u) [CommRing K] (q : ℕ) {depth n : ℕ}
    (term : ExactInterfaceTermParameters depth)
    (hmultiplicity : term.multiplicity = n + 1)
    (hz : term.index.count .Z = 0) :
    Restricts
      (Tensor.permute (zeroOrientation .Z)
        (cwSelectedExactInterfaceTerm K q term hmultiplicity).realize)
      (CTensor.partitioned
        (cwSelectedExactInterfaceTerm_zeroZ_rotatedAmbientFiberRetyping
          K q term hmultiplicity hz).targetConstituent).realize := by
  have hsupport :=
    cwSelectedExactInterfaceTerm_zeroZ_support_isSharedFiber' K q term hmultiplicity hz
  exact CTensor.FiberRetyping.restricts_permute_ofSharedSupportPermutedAmbient
    (cwSelectedExactInterfaceTerm K q term hmultiplicity) (zeroOrientation .Z)
    hsupport.2.1 hsupport.2.2 (cwZeroInterfaceLegWord depth n) hsupport.1

end AlgebraicComplexity.Examples
