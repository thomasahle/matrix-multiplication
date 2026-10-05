/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinogradTotalWeightIsolatedSupport
import AlgebraicComplexity.MatrixMultiplication.PermutedTwoLegIsolation

/-!
# Cyclic two-leg isolation for total-weight compatibility cleanup

The asymmetric hashing stage isolates the `X` and `Y` labels of a finite address family.  The
total-weight compatibility cleanup is naturally stated for isolated `Y` and `Z` labels.  A single
cyclic leg relabelling connects these interfaces: `X/Y` isolation becomes `Y/Z` isolation, so the
supported cleanup retains the entire relabelled family.

These are exact finite consequences of the generic permutation transport and the total-weight
rigidity theorem.  They assume neither a tensor restriction nor an asymptotic counting rate.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor MoreAsymmetryCompatibility

/-- After one cyclic relabelling, a supported total-weight compatibility cleanup deletes no member
of an X/Y-isolated address family. -/
theorem cwTotalWeightYZIsolatedSupport_cycle_permuted_eq_of_xy
    {Part : Type*} [DecidableEq Part] (depth n : ℕ)
    (partAt : Fin (n + 1) → Part) (rawTargets : CompatibilityTargets Part depth)
    (hsupported : rawTargets.IsWeightSupported)
    (family : Finset
      (BlockAddress (fun _c ↦ PositiveWord (CWCoarseDigit depth) n)))
    (hX : Set.InjOn
      (fun address : BlockAddress
        (fun _c ↦ PositiveWord (CWCoarseDigit depth) n) ↦ address .X) family)
    (hY : Set.InjOn
      (fun address : BlockAddress
        (fun _c ↦ PositiveWord (CWCoarseDigit depth) n) ↦ address .Y) family) :
    cwTotalWeightYZIsolatedSupport depth n partAt rawTargets
        (permutedAddressFamily cycle family) =
      permutedAddressFamily cycle family := by
  obtain ⟨hY', hZ'⟩ := yz_injectiveOn_cycle_permutedAddressFamily_of_xy family hX hY
  exact cwTotalWeightYZIsolatedSupport_eq_ambient_of_injOn
    depth n partAt rawTargets hsupported (permutedAddressFamily cycle family) hY' hZ'

/-- The corresponding directed `Y` competitor incidence is exactly zero. -/
theorem cwTotalWeightYCompetitorIncidence_cycle_permuted_eq_zero_of_xy
    {Part : Type*} [DecidableEq Part] (depth n : ℕ)
    (partAt : Fin (n + 1) → Part) (rawTargets : CompatibilityTargets Part depth)
    (hsupported : rawTargets.IsWeightSupported)
    (family : Finset
      (BlockAddress (fun _c ↦ PositiveWord (CWCoarseDigit depth) n)))
    (hX : Set.InjOn
      (fun address : BlockAddress
        (fun _c ↦ PositiveWord (CWCoarseDigit depth) n) ↦ address .X) family)
    (hY : Set.InjOn
      (fun address : BlockAddress
        (fun _c ↦ PositiveWord (CWCoarseDigit depth) n) ↦ address .Y) family) :
    cwTotalWeightYCompetitorIncidence depth n partAt rawTargets
        (permutedAddressFamily cycle family) = 0 := by
  obtain ⟨hY', _hZ'⟩ := yz_injectiveOn_cycle_permutedAddressFamily_of_xy family hX hY
  exact cwTotalWeightYCompetitorIncidence_eq_zero_of_injOn
    depth n partAt rawTargets hsupported.2.1 (permutedAddressFamily cycle family) hY'

/-- The post-`Y` directed `Z` competitor incidence is also exactly zero. -/
theorem cwTotalWeightZCompetitorIncidence_cycle_permuted_eq_zero_of_xy
    {Part : Type*} [DecidableEq Part] (depth n : ℕ)
    (partAt : Fin (n + 1) → Part) (rawTargets : CompatibilityTargets Part depth)
    (hsupported : rawTargets.IsWeightSupported)
    (family : Finset
      (BlockAddress (fun _c ↦ PositiveWord (CWCoarseDigit depth) n)))
    (hX : Set.InjOn
      (fun address : BlockAddress
        (fun _c ↦ PositiveWord (CWCoarseDigit depth) n) ↦ address .X) family)
    (hY : Set.InjOn
      (fun address : BlockAddress
        (fun _c ↦ PositiveWord (CWCoarseDigit depth) n) ↦ address .Y) family) :
    cwTotalWeightZCompetitorIncidence depth n partAt rawTargets
        (permutedAddressFamily cycle family) = 0 := by
  obtain ⟨hY', hZ'⟩ := yz_injectiveOn_cycle_permutedAddressFamily_of_xy family hX hY
  exact cwTotalWeightZCompetitorIncidence_eq_zero_of_injOn
    depth n partAt rawTargets hsupported (permutedAddressFamily cycle family) hY' hZ'

end AlgebraicComplexity.Examples
