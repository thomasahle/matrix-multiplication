/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinogradTotalWeightCyclicIsolation
import AlgebraicComplexity.MatrixMultiplication.MarkedXYPartitionedPowerHashing

/-!
# Marked affine hashing followed by total-weight cleanup

This file closes the finite interface between asymmetric affine hashing and total-weight
compatibility cleanup.  The marked hashing theorem derives X/Y isolation against the ambient
family.  After cycling the retained address family, that isolation is exactly the Y/Z isolation
required by the total-weight rigidity theorem, so compatibility cleanup loses no retained address.

The packaged existence theorems preserve the marked hashing count and ambient-containment
conclusions while replacing the two intermediate injectivity obligations by the final cleanup
identity.  No tensor restriction or asymptotic rate is introduced here.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor MoreAsymmetryCompatibility

universe u

/-- For every fixed seed, cycling a marked XY-isolated hashing family makes supported total-weight
compatibility cleanup lossless. -/
theorem cwTotalWeightYZIsolatedSupport_cycle_markedXY_eq
    {R : Type u} [Field R] [NeZero (2 : R)]
    {Part : Type*} [DecidableEq Part] (depth n : ℕ)
    {support : Finset (BlockAddress (fun _c ↦ CWCoarseDigit depth))}
    (H : PartitionHashEncoding (R := R) support)
    (ambientWords markedWords : Finset (PositiveWord support n))
    (hwords : markedWords ⊆ ambientWords) (B : Finset R) (hB : ThreeAPFree (B : Set R))
    (seed : ProgressionHash.Seed R (Fin (n + 1)))
    (partAt : Fin (n + 1) → Part) (rawTargets : CompatibilityTargets Part depth)
    (hsupported : rawTargets.IsWeightSupported) :
    cwTotalWeightYZIsolatedSupport depth n partAt rawTargets
        (permutedAddressFamily cycle
          (H.markedXYIsolatedPowerAddresses n ambientWords markedWords B seed)) =
      permutedAddressFamily cycle
        (H.markedXYIsolatedPowerAddresses n ambientWords markedWords B seed) := by
  apply cwTotalWeightYZIsolatedSupport_cycle_permuted_eq_of_xy
    depth n partAt rawTargets hsupported
  · exact H.x_injectiveOn_markedXYIsolatedPowerAddresses
      n ambientWords markedWords hwords B hB seed
  · exact H.y_injectiveOn_markedXYIsolatedPowerAddresses
      n ambientWords markedWords hwords B hB seed

/-- The marked good-seed count and ambient containment survive a subsequent cyclic total-weight
compatibility cleanup without any additional loss. -/
theorem exists_seed_many_cycle_markedXY_with_totalWeight_cleanup
    {R : Type u} [Field R] [Fintype R] [NeZero (2 : R)]
    {Part : Type*} [DecidableEq Part] (depth n : ℕ)
    {support : Finset (BlockAddress (fun _c ↦ CWCoarseDigit depth))}
    (H : PartitionHashEncoding (R := R) support)
    (ambientWords markedWords : Finset (PositiveWord support n))
    (hwords : markedWords ⊆ ambientWords) (B : Finset R) (hB : ThreeAPFree (B : Set R))
    (hquarter : ∀ triple ∈ H.legalTargets n markedWords,
      4 * (ProgressionHash.LegalTriple.xyCompetitorYIndices
        (H.legalTargets n ambientWords) triple).card ≤ Fintype.card R)
    (partAt : Fin (n + 1) → Part) (rawTargets : CompatibilityTargets Part depth)
    (hsupported : rawTargets.IsWeightSupported) :
    ∃ seed : ProgressionHash.Seed R (Fin (n + 1)),
      3 * markedWords.card * B.card ≤
          4 * (Fintype.card R * Fintype.card R) *
            (H.markedXYIsolatedPowerAddresses
              n ambientWords markedWords B seed).card ∧
        H.markedXYIsolatedPowerAddresses n ambientWords markedWords B seed ⊆
          H.filteredPowerAddresses n ambientWords B seed ∧
        cwTotalWeightYZIsolatedSupport depth n partAt rawTargets
            (permutedAddressFamily cycle
              (H.markedXYIsolatedPowerAddresses n ambientWords markedWords B seed)) =
          permutedAddressFamily cycle
            (H.markedXYIsolatedPowerAddresses n ambientWords markedWords B seed) := by
  obtain ⟨seed, hcount, hsubset, _hX, _hY⟩ :=
    H.exists_seed_many_markedXYIsolatedPowerAddresses
      n ambientWords markedWords hwords B hB hquarter
  exact ⟨seed, hcount, hsubset,
    cwTotalWeightYZIsolatedSupport_cycle_markedXY_eq
      depth n H ambientWords markedWords hwords B hB seed partAt rawTargets hsupported⟩

/-- Modulus-form good-seed theorem with the lossless total-weight cleanup already composed. -/
theorem exists_seed_many_cycle_markedXY_with_totalWeight_cleanup_of_modulus
    {R : Type u} [Field R] [Fintype R] [NeZero (2 : R)]
    {Part : Type*} [DecidableEq Part] (depth n : ℕ)
    {support : Finset (BlockAddress (fun _c ↦ CWCoarseDigit depth))}
    (H : PartitionHashEncoding (R := R) support)
    (ambientWords markedWords : Finset (PositiveWord support n))
    (hwords : markedWords ⊆ ambientWords) (B : Finset R) (hB : ThreeAPFree (B : Set R))
    (d : ℕ)
    (hX : ∀ triple ∈ H.legalTargets n markedWords,
      (ProgressionHash.LegalTriple.legFiber
        (H.legalTargets n ambientWords) triple .X).card ≤ d)
    (hY : ∀ triple ∈ H.legalTargets n markedWords,
      (ProgressionHash.LegalTriple.legFiber
        (H.legalTargets n ambientWords) triple .Y).card ≤ d)
    (hmodulus : 8 * d ≤ Fintype.card R)
    (partAt : Fin (n + 1) → Part) (rawTargets : CompatibilityTargets Part depth)
    (hsupported : rawTargets.IsWeightSupported) :
    ∃ seed : ProgressionHash.Seed R (Fin (n + 1)),
      3 * markedWords.card * B.card ≤
          4 * (Fintype.card R * Fintype.card R) *
            (H.markedXYIsolatedPowerAddresses
              n ambientWords markedWords B seed).card ∧
        H.markedXYIsolatedPowerAddresses n ambientWords markedWords B seed ⊆
          H.filteredPowerAddresses n ambientWords B seed ∧
        cwTotalWeightYZIsolatedSupport depth n partAt rawTargets
            (permutedAddressFamily cycle
              (H.markedXYIsolatedPowerAddresses n ambientWords markedWords B seed)) =
          permutedAddressFamily cycle
            (H.markedXYIsolatedPowerAddresses n ambientWords markedWords B seed) := by
  exact exists_seed_many_cycle_markedXY_with_totalWeight_cleanup
    depth n H ambientWords markedWords hwords B hB
      (ProgressionHash.LegalTriple.quarter_of_eight_mul_legFiber_le
        (H.legalTargets n ambientWords) (H.legalTargets n markedWords) d hX hY hmodulus)
      partAt rawTargets hsupported

end AlgebraicComplexity.Examples
