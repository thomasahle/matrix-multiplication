/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinogradTotalWeightMarkedHashCleanup

/-!
# Tensor extraction for cyclic marked total-weight hashing

The marked affine-hashing theorem already derives a tensor restriction to its selected X/Y-isolated
subpartition.  This file transports that restriction through the same cyclic leg relabelling used
by total-weight compatibility cleanup.  The resulting partition has the cycled marked family as
its literal support, so the good-seed count, lossless cleanup identity, and tensor restriction refer
to one and the same finite object.

No assembled-product restriction and no asymptotic rate are assumed.  The only semantic input is
the committed finite marked-hashing restriction.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor MoreAsymmetryCompatibility

universe u v w

/-- The marked hashing subpartition after cycling its tensor legs. -/
noncomputable def cwTotalWeightCycleMarkedPartition
    {R : Type u} [Field R] {K : Type v} [CommSemiring K]
    (depth n : ℕ) {support : Finset (BlockAddress (fun _c ↦ CWCoarseDigit depth))}
    (H : PartitionHashEncoding (R := R) support)
    (ambientWords markedWords : Finset (PositiveWord support n))
    (B : Finset R) (seed : ProgressionHash.Seed R (Fin (n + 1)))
    {V : ∀ _c, PositiveWord (CWCoarseDigit depth) n → Type w}
    [∀ _c a, AddCommMonoid (V _c a)] [∀ _c a, Module K (V _c a)]
    (P : PartitionedTensor (K := K)
      (A := fun _c ↦ PositiveWord (CWCoarseDigit depth) n) V) :
    PartitionedTensor (K := K)
      (A := PermutedBlockIndex cycle
        (fun _c ↦ PositiveWord (CWCoarseDigit depth) n))
      (PermutedBlockSpace cycle V) :=
  (P.withSupport
    (H.markedXYIsolatedPowerAddresses n ambientWords markedWords B seed)).permute cycle

/-- The extracted cyclic partition's support is literally the cycled marked address family. -/
@[simp] theorem cwTotalWeightCycleMarkedPartition_support
    {R : Type u} [Field R] {K : Type v} [CommSemiring K]
    (depth n : ℕ) {support : Finset (BlockAddress (fun _c ↦ CWCoarseDigit depth))}
    (H : PartitionHashEncoding (R := R) support)
    (ambientWords markedWords : Finset (PositiveWord support n))
    (B : Finset R) (seed : ProgressionHash.Seed R (Fin (n + 1)))
    {V : ∀ _c, PositiveWord (CWCoarseDigit depth) n → Type w}
    [∀ _c a, AddCommMonoid (V _c a)] [∀ _c a, Module K (V _c a)]
    (P : PartitionedTensor (K := K)
      (A := fun _c ↦ PositiveWord (CWCoarseDigit depth) n) V) :
    (cwTotalWeightCycleMarkedPartition
      depth n H ambientWords markedWords B seed P).support =
      permutedAddressFamily cycle
        (H.markedXYIsolatedPowerAddresses n ambientWords markedWords B seed) := rfl

/-- Cycling the finite marked-hashing restriction yields an actual restriction to the cyclic
marked partition used by total-weight cleanup. -/
theorem cwTotalWeightCycleModeledTargets_restricts_marked
    {R : Type u} [Field R] [NeZero (2 : R)]
    {K : Type v} [CommSemiring K] (depth n : ℕ)
    {support : Finset (BlockAddress (fun _c ↦ CWCoarseDigit depth))}
    (H : PartitionHashEncoding (R := R) support)
    (ambientWords markedWords : Finset (PositiveWord support n))
    (hwords : markedWords ⊆ ambientWords) (B : Finset R) (hB : ThreeAPFree (B : Set R))
    (seed : ProgressionHash.Seed R (Fin (n + 1)))
    {V : ∀ _c, PositiveWord (CWCoarseDigit depth) n → Type w}
    [∀ _c a, AddCommMonoid (V _c a)] [∀ _c a, Module K (V _c a)]
    (P : PartitionedTensor (K := K)
      (A := fun _c ↦ PositiveWord (CWCoarseDigit depth) n) V)
    (hsupport : P.support = H.modeledAddresses n (H.legalTargets n ambientWords)) :
    Restricts (P.permute cycle).realize
      (cwTotalWeightCycleMarkedPartition
        depth n H ambientWords markedWords B seed P).realize := by
  have hrestrict := Tensor.Restricts.modeledTargets_to_markedXYIsolated
    H ambientWords markedWords hwords B hB seed P hsupport
  simpa only [cwTotalWeightCycleMarkedPartition, PartitionedTensor.permute_realize] using
    hrestrict.permute cycle

/-- One seed simultaneously carries the marked count, lossless cyclic total-weight cleanup, and
the tensor restriction to that cleaned family. -/
theorem exists_seed_many_cycle_markedXY_totalWeight_extraction
    {R : Type u} [Field R] [Fintype R] [NeZero (2 : R)]
    {K : Type v} [CommSemiring K]
    {Part : Type*} [DecidableEq Part] (depth n : ℕ)
    {support : Finset (BlockAddress (fun _c ↦ CWCoarseDigit depth))}
    (H : PartitionHashEncoding (R := R) support)
    (ambientWords markedWords : Finset (PositiveWord support n))
    (hwords : markedWords ⊆ ambientWords) (B : Finset R) (hB : ThreeAPFree (B : Set R))
    (hquarter : ∀ triple ∈ H.legalTargets n markedWords,
      4 * (ProgressionHash.LegalTriple.xyCompetitorYIndices
        (H.legalTargets n ambientWords) triple).card ≤ Fintype.card R)
    (partAt : Fin (n + 1) → Part) (rawTargets : CompatibilityTargets Part depth)
    (hsupported : rawTargets.IsWeightSupported)
    {V : ∀ _c, PositiveWord (CWCoarseDigit depth) n → Type w}
    [∀ _c a, AddCommMonoid (V _c a)] [∀ _c a, Module K (V _c a)]
    (P : PartitionedTensor (K := K)
      (A := fun _c ↦ PositiveWord (CWCoarseDigit depth) n) V)
    (hsupport : P.support = H.modeledAddresses n (H.legalTargets n ambientWords)) :
    ∃ seed : ProgressionHash.Seed R (Fin (n + 1)),
      3 * markedWords.card * B.card ≤
          4 * (Fintype.card R * Fintype.card R) *
            (H.markedXYIsolatedPowerAddresses
              n ambientWords markedWords B seed).card ∧
        cwTotalWeightYZIsolatedSupport depth n partAt rawTargets
            (cwTotalWeightCycleMarkedPartition
              depth n H ambientWords markedWords B seed P).support =
          (cwTotalWeightCycleMarkedPartition
            depth n H ambientWords markedWords B seed P).support ∧
        Restricts (P.permute cycle).realize
          (cwTotalWeightCycleMarkedPartition
            depth n H ambientWords markedWords B seed P).realize := by
  obtain ⟨seed, hcount, _hsubset, hcleanup⟩ :=
    exists_seed_many_cycle_markedXY_with_totalWeight_cleanup
      depth n H ambientWords markedWords hwords B hB hquarter
        partAt rawTargets hsupported
  have hcleanup' :
      cwTotalWeightYZIsolatedSupport depth n partAt rawTargets
          (cwTotalWeightCycleMarkedPartition
            depth n H ambientWords markedWords B seed P).support =
        (cwTotalWeightCycleMarkedPartition
          depth n H ambientWords markedWords B seed P).support := by
    simpa only [cwTotalWeightCycleMarkedPartition_support] using hcleanup
  exact ⟨seed, hcount, hcleanup',
    cwTotalWeightCycleModeledTargets_restricts_marked
      depth n H ambientWords markedWords hwords B hB seed P hsupport⟩

/-- Modulus-form extraction theorem carrying count, cleanup, and restriction together. -/
theorem exists_seed_many_cycle_markedXY_totalWeight_extraction_of_modulus
    {R : Type u} [Field R] [Fintype R] [NeZero (2 : R)]
    {K : Type v} [CommSemiring K]
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
    (hsupported : rawTargets.IsWeightSupported)
    {V : ∀ _c, PositiveWord (CWCoarseDigit depth) n → Type w}
    [∀ _c a, AddCommMonoid (V _c a)] [∀ _c a, Module K (V _c a)]
    (P : PartitionedTensor (K := K)
      (A := fun _c ↦ PositiveWord (CWCoarseDigit depth) n) V)
    (hsupport : P.support = H.modeledAddresses n (H.legalTargets n ambientWords)) :
    ∃ seed : ProgressionHash.Seed R (Fin (n + 1)),
      3 * markedWords.card * B.card ≤
          4 * (Fintype.card R * Fintype.card R) *
            (H.markedXYIsolatedPowerAddresses
              n ambientWords markedWords B seed).card ∧
        cwTotalWeightYZIsolatedSupport depth n partAt rawTargets
            (cwTotalWeightCycleMarkedPartition
              depth n H ambientWords markedWords B seed P).support =
          (cwTotalWeightCycleMarkedPartition
            depth n H ambientWords markedWords B seed P).support ∧
        Restricts (P.permute cycle).realize
          (cwTotalWeightCycleMarkedPartition
            depth n H ambientWords markedWords B seed P).realize := by
  exact exists_seed_many_cycle_markedXY_totalWeight_extraction
    depth n H ambientWords markedWords hwords B hB
      (ProgressionHash.LegalTriple.quarter_of_eight_mul_legFiber_le
        (H.legalTargets n ambientWords) (H.legalTargets n markedWords) d hX hY hmodulus)
      partAt rawTargets hsupported P hsupport

end AlgebraicComplexity.Examples
