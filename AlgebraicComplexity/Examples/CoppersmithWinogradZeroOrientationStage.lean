/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinogradZeroOrientationFusion
import AlgebraicComplexity.MatrixMultiplication.ZeroCoordinateMerge

/-!
# Whole-stage packaging for an oriented zero-coordinate CW family

The exact zero-coordinate fusion is a theorem about the realization of a **whole selected
interface family**.  Its type-class cardinality is created by summing the distinct addresses in
that family and must therefore be absorbed at the same family level.  It is not a dimension of
one raw chunk-support constituent.

This module packages the proved arbitrary-orientation fusion as a one-copy
`WholeConstituentLaserVolumeStage` and composes it with an arbitrary residual stage.  The source
of the composite remains the explicit external product of the residual source and the rotated
selected family.  In particular, neither declaration assumes a degeneration of an assembled
source power or a per-letter zero-class factorization.

The later recursive client should obtain this external product from the exact interface-term
division theorem and then use `WholeConstituentLaserVolumeStage.precompose`.  Keeping that source
restriction out of this module prevents the family-level semantic step from being hidden in a
stage-shaped hypothesis.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor MoreAsymmetryCompatibility

universe u v z

/-- The complete selected zero-coordinate family as a one-copy whole-constituent stage.

The middle dimension contains the exact selected-support cardinality.  The source stays in the
rotated frame in which `zeroOrientation zero` carries the zero leg to the shared `Z` leg; this is
the same convention as `cwSelectedExactInterfaceTerm_zero_restricts_fusedOneSlice`. -/
noncomputable def cwSelectedExactInterfaceTerm_zero_fusedStage
    (K : Type u) [CommRing K] (q : ℕ) (zero : Leg)
    {depth n : ℕ} (term : ExactInterfaceTermParameters depth)
    (hmultiplicity : term.multiplicity = n + 1)
    (hzero : term.index.count zero = 0) :
    WholeConstituentLaserVolumeStage.{u, u, z} K
      (Tensor.permute (zeroOrientation zero)
        (cwSelectedExactInterfaceTerm K q term hmultiplicity).realize)
      1 1
      ((cwSelectedExactInterfaceTerm K q term hmultiplicity).support.card *
        q ^ cwZeroInterfaceQExponentOn (firstLiveLeg zero) term)
      1 :=
  ZeroCoordinateMerge.stageOfRestricts K
    (cwSelectedExactInterfaceTerm_zero_restricts_fusedOneSlice
      K q zero term hmultiplicity hzero)

/-- Absorb a whole selected zero-coordinate family into the middle dimension of an arbitrary
residual stage.

This is the faithful family-level counterpart of a merged leaf: the output copy count is exactly
the residual copy count, while the selected family's `|S| q^e` factor multiplies the `Y`
dimension.  The source explicitly contains the selected family as a separate external factor, so
the theorem cannot be misread as placing `|S|` inside one raw chunk constituent. -/
noncomputable def WholeConstituentLaserVolumeStage.mergeCWSelectedZeroFamily
    (K : Type u) [CommRing K]
    {V : Leg → Type v} [∀ c, AddCommMonoid (V c)] [∀ c, Module K (V c)]
    {residual : Tensor3 K V} {copies xSize ySize zSize : ℕ}
    (residualStage : WholeConstituentLaserVolumeStage.{u, v, z} K residual
      copies xSize ySize zSize)
    (q : ℕ) (zero : Leg) {depth n : ℕ}
    (term : ExactInterfaceTermParameters depth)
    (hmultiplicity : term.multiplicity = n + 1)
    (hzero : term.index.count zero = 0) :
    WholeConstituentLaserVolumeStage.{u, max v u, z} K
      (Tensor.external residual
        (Tensor.permute (zeroOrientation zero)
          (cwSelectedExactInterfaceTerm K q term hmultiplicity).realize))
      copies xSize
      (ySize *
        ((cwSelectedExactInterfaceTerm K q term hmultiplicity).support.card *
          q ^ cwZeroInterfaceQExponentOn (firstLiveLeg zero) term))
      zSize :=
  ZeroCoordinateMerge.mergeY K residualStage
    (cwSelectedExactInterfaceTerm_zero_fusedStage
      K q zero term hmultiplicity hzero)

end AlgebraicComplexity.Examples
