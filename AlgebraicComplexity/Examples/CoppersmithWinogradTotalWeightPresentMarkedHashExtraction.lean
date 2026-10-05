/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinogradTotalWeightMarkedHashCleanup
import AlgebraicComplexity.MatrixMultiplication.MarkedXYPresentPartitionExtraction

/-!
# Cyclic total-weight cleanup on the actually present marked hash family

The abstract marked hashing family may contain targets with no fine preimage in the selected
recursive parent.  This file applies the present-support extraction theorem before cyclic
total-weight cleanup.  Consequently the tensor restriction keeps every actually present fine
preimage of a selected abstract target, while absent targets remain an explicit missing family.

The affine count is not silently transferred to the present family.  Instead the conclusion uses
the exact decomposition

`abstract selected count = missing count + present count`.

Bounding the missing term is the later input-profile/compatibility concentration obligation.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor MoreAsymmetryCompatibility

universe u v w

/-- The actually present marked hashing subpartition after cycling its tensor legs. -/
noncomputable def cwTotalWeightCyclePresentMarkedPartition
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
    (H.presentMarkedXYIsolatedPowerAddresses ambientWords markedWords B seed P)).permute cycle

/-- The cyclic partition's support is literally the cycled actually present intersection. -/
@[simp] theorem cwTotalWeightCyclePresentMarkedPartition_support
    {R : Type u} [Field R] {K : Type v} [CommSemiring K]
    (depth n : ℕ) {support : Finset (BlockAddress (fun _c ↦ CWCoarseDigit depth))}
    (H : PartitionHashEncoding (R := R) support)
    (ambientWords markedWords : Finset (PositiveWord support n))
    (B : Finset R) (seed : ProgressionHash.Seed R (Fin (n + 1)))
    {V : ∀ _c, PositiveWord (CWCoarseDigit depth) n → Type w}
    [∀ _c a, AddCommMonoid (V _c a)] [∀ _c a, Module K (V _c a)]
    (P : PartitionedTensor (K := K)
      (A := fun _c ↦ PositiveWord (CWCoarseDigit depth) n) V) :
    (cwTotalWeightCyclePresentMarkedPartition
      depth n H ambientWords markedWords B seed P).support =
      permutedAddressFamily cycle
        (H.presentMarkedXYIsolatedPowerAddresses ambientWords markedWords B seed P) := rfl

/-- Cycling the present marked restriction yields an actual restriction to the cyclic partition
used by total-weight cleanup.  Only containment of the actual support in the abstract ambient
family is required. -/
theorem cwTotalWeightCyclePresentModeledTargets_restricts_marked
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
    (hsupport : P.support ⊆ H.modeledAddresses n (H.legalTargets n ambientWords)) :
    Restricts (P.permute cycle).realize
      (cwTotalWeightCyclePresentMarkedPartition
        depth n H ambientWords markedWords B seed P).realize := by
  have hrestrict := Tensor.Restricts.presentModeledTargets_to_presentMarkedXYIsolated
    H ambientWords markedWords hwords B hB seed P hsupport
  simpa only [cwTotalWeightCyclePresentMarkedPartition,
    PartitionedTensor.permute_realize] using hrestrict.permute cycle

/-- Supported total-weight compatibility cleanup loses none of the actually present cyclic
marked family. -/
theorem cwTotalWeightYZIsolatedSupport_cycle_presentMarkedXY_eq
    {R : Type u} [Field R] [NeZero (2 : R)]
    {K : Type v} [CommSemiring K]
    {Part : Type*} [DecidableEq Part] (depth n : ℕ)
    {support : Finset (BlockAddress (fun _c ↦ CWCoarseDigit depth))}
    (H : PartitionHashEncoding (R := R) support)
    (ambientWords markedWords : Finset (PositiveWord support n))
    (hwords : markedWords ⊆ ambientWords) (B : Finset R) (hB : ThreeAPFree (B : Set R))
    (seed : ProgressionHash.Seed R (Fin (n + 1)))
    (partAt : Fin (n + 1) → Part) (rawTargets : CompatibilityTargets Part depth)
    (hsupported : rawTargets.IsWeightSupported)
    {V : ∀ _c, PositiveWord (CWCoarseDigit depth) n → Type w}
    [∀ _c a, AddCommMonoid (V _c a)] [∀ _c a, Module K (V _c a)]
    (P : PartitionedTensor (K := K)
      (A := fun _c ↦ PositiveWord (CWCoarseDigit depth) n) V) :
    cwTotalWeightYZIsolatedSupport depth n partAt rawTargets
        (cwTotalWeightCyclePresentMarkedPartition
          depth n H ambientWords markedWords B seed P).support =
      (cwTotalWeightCyclePresentMarkedPartition
        depth n H ambientWords markedWords B seed P).support := by
  rw [cwTotalWeightCyclePresentMarkedPartition_support]
  apply cwTotalWeightYZIsolatedSupport_cycle_permuted_eq_of_xy
    depth n partAt rawTargets hsupported
  · exact H.x_injectiveOn_presentMarkedXYIsolatedPowerAddresses
      ambientWords markedWords hwords B hB seed P
  · exact H.y_injectiveOn_presentMarkedXYIsolatedPowerAddresses
      ambientWords markedWords hwords B hB seed P

/-- One seed supplies the abstract marked count, its exact present/missing decomposition, lossless
cleanup of every present target, and the tensor restriction to the present cleaned family. -/
theorem exists_seed_many_cycle_presentMarkedXY_totalWeight_extraction
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
    (hsupport : P.support ⊆ H.modeledAddresses n (H.legalTargets n ambientWords)) :
    ∃ seed : ProgressionHash.Seed R (Fin (n + 1)),
      3 * markedWords.card * B.card ≤
          4 * (Fintype.card R * Fintype.card R) *
            ((H.missingMarkedXYIsolatedPowerAddresses
                ambientWords markedWords B seed P).card +
              (H.presentMarkedXYIsolatedPowerAddresses
                ambientWords markedWords B seed P).card) ∧
        cwTotalWeightYZIsolatedSupport depth n partAt rawTargets
            (cwTotalWeightCyclePresentMarkedPartition
              depth n H ambientWords markedWords B seed P).support =
          (cwTotalWeightCyclePresentMarkedPartition
            depth n H ambientWords markedWords B seed P).support ∧
        Restricts (P.permute cycle).realize
          (cwTotalWeightCyclePresentMarkedPartition
            depth n H ambientWords markedWords B seed P).realize := by
  obtain ⟨seed, hcount, _hsubset, _hX, _hY⟩ :=
    H.exists_seed_many_markedXYIsolatedPowerAddresses
      n ambientWords markedWords hwords B hB hquarter
  have hcount' := hcount
  rw [← H.card_missing_add_card_presentMarkedXYIsolatedPowerAddresses
    ambientWords markedWords B seed P] at hcount'
  exact ⟨seed, hcount',
    cwTotalWeightYZIsolatedSupport_cycle_presentMarkedXY_eq
      depth n H ambientWords markedWords hwords B hB seed
        partAt rawTargets hsupported P,
    cwTotalWeightCyclePresentModeledTargets_restricts_marked
      depth n H ambientWords markedWords hwords B hB seed P hsupport⟩

/-- Modulus-form present-support extraction theorem. -/
theorem exists_seed_many_cycle_presentMarkedXY_totalWeight_extraction_of_modulus
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
    (hsupport : P.support ⊆ H.modeledAddresses n (H.legalTargets n ambientWords)) :
    ∃ seed : ProgressionHash.Seed R (Fin (n + 1)),
      3 * markedWords.card * B.card ≤
          4 * (Fintype.card R * Fintype.card R) *
            ((H.missingMarkedXYIsolatedPowerAddresses
                ambientWords markedWords B seed P).card +
              (H.presentMarkedXYIsolatedPowerAddresses
                ambientWords markedWords B seed P).card) ∧
        cwTotalWeightYZIsolatedSupport depth n partAt rawTargets
            (cwTotalWeightCyclePresentMarkedPartition
              depth n H ambientWords markedWords B seed P).support =
          (cwTotalWeightCyclePresentMarkedPartition
            depth n H ambientWords markedWords B seed P).support ∧
        Restricts (P.permute cycle).realize
          (cwTotalWeightCyclePresentMarkedPartition
            depth n H ambientWords markedWords B seed P).realize := by
  exact exists_seed_many_cycle_presentMarkedXY_totalWeight_extraction
    depth n H ambientWords markedWords hwords B hB
      (ProgressionHash.LegalTriple.quarter_of_eight_mul_legFiber_le
        (H.legalTargets n ambientWords) (H.legalTargets n markedWords) d hX hY hmodulus)
      partAt rawTargets hsupported P hsupport

end AlgebraicComplexity.Examples
