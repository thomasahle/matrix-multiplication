/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinogradZeroOrientationStage
import AlgebraicComplexity.MatrixMultiplication.WholeConstituentLaserVolumePermutation
import AlgebraicComplexity.Tensor.PermutationCoherence

/-!
# Native-frame stages for zero-coordinate CW families

The zero-coordinate fusion theorem is naturally proved after moving the zero leg to `Z`; in that
canonical frame its sole nontrivial matrix dimension is the `Y` dimension.  Recursive assembly,
however, needs each selected family in the source's original leg frame.

This module rotates the finite stage back.  The source permutation is cancelled by the general
tensor-permutation isomorphism, and the matrix dimensions are rotated by the proved finite-stage
transport.  Consequently the nontrivial dimension lands on `secondLiveLeg zero`: on `Z` for a
zero-`X` family, on `X` for a zero-`Y` family, and on `Y` for a zero-`Z` family.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor MoreAsymmetryCompatibility

universe u z

/-- The exact nontrivial dimension of a selected zero-coordinate interface family. -/
noncomputable def cwSelectedZeroFamilyDimension
    (K : Type u) [CommRing K] (q : ℕ) (zero : Leg)
    {depth n : ℕ} (term : ExactInterfaceTermParameters depth)
    (hmultiplicity : term.multiplicity = n + 1) : ℕ :=
  (cwSelectedExactInterfaceTerm K q term hmultiplicity).support.card *
    q ^ cwZeroInterfaceQExponentOn (firstLiveLeg zero) term

/-- **A selected zero-coordinate CW family as a stage in its native leg frame.**

The output dimension vector has one entry equal to the exact family dimension and two entries
equal to one.  The location of the nontrivial entry is `secondLiveLeg zero`, expressed below by
the three explicit cases so that downstream arithmetic sees ordinary natural-number dimensions. -/
noncomputable def cwSelectedExactInterfaceTerm_zero_nativeStage
    (K : Type u) [CommRing K] (q : ℕ) (zero : Leg)
    {depth n : ℕ} (term : ExactInterfaceTermParameters depth)
    (hmultiplicity : term.multiplicity = n + 1)
    (hzero : term.index.count zero = 0) :
    WholeConstituentLaserVolumeStage.{u, u, z} K
      (cwSelectedExactInterfaceTerm K q term hmultiplicity).realize
      1
      (match zero with
        | .X => 1
        | .Y => cwSelectedZeroFamilyDimension K q .Y term hmultiplicity
        | .Z => 1)
      (match zero with
        | .X => 1
        | .Y => 1
        | .Z => cwSelectedZeroFamilyDimension K q .Z term hmultiplicity)
      (match zero with
        | .X => cwSelectedZeroFamilyDimension K q .X term hmultiplicity
        | .Y => 1
        | .Z => 1) := by
  cases zero with
  | X =>
      let source := (cwSelectedExactInterfaceTerm K q term hmultiplicity).realize
      let familyDimension := cwSelectedZeroFamilyDimension K q .X term hmultiplicity
      let rotated : WholeConstituentLaserVolumeStage.{u, u, z} K
          (Tensor.permute cycle.symm source) 1 1 familyDimension 1 := by
        exact cwSelectedExactInterfaceTerm_zero_fusedStage
          K q .X term hmultiplicity hzero
      let nativeTarget := WholeConstituentLaserVolumeStage.permuteCycle K rotated
      exact WholeConstituentLaserVolumeStage.precompose K
        (Tensor.Isomorphic.cancel_permute_symm_left cycle.symm source).symm.restricts
        nativeTarget
  | Y =>
      let source := (cwSelectedExactInterfaceTerm K q term hmultiplicity).realize
      let familyDimension := cwSelectedZeroFamilyDimension K q .Y term hmultiplicity
      let rotated : WholeConstituentLaserVolumeStage.{u, u, z} K
          (Tensor.permute cycle source) 1 1 familyDimension 1 := by
        exact cwSelectedExactInterfaceTerm_zero_fusedStage
          K q .Y term hmultiplicity hzero
      let nativeTarget := WholeConstituentLaserVolumeStage.permuteCycleSymm K rotated
      exact WholeConstituentLaserVolumeStage.precompose K
        (Tensor.Isomorphic.cancel_permute_symm_left cycle source).symm.restricts
        nativeTarget
  | Z =>
      let source := (cwSelectedExactInterfaceTerm K q term hmultiplicity).realize
      let familyDimension := cwSelectedZeroFamilyDimension K q .Z term hmultiplicity
      let rotated : WholeConstituentLaserVolumeStage.{u, u, z} K
          (Tensor.permute (Equiv.refl Leg) source) 1 1 familyDimension 1 := by
        exact cwSelectedExactInterfaceTerm_zero_fusedStage
          K q .Z term hmultiplicity hzero
      exact WholeConstituentLaserVolumeStage.precompose K
        (Tensor.Isomorphic.cancel_permute_refl source).symm.restricts
        rotated

end AlgebraicComplexity.Examples
