/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoFineReferenceProfiles
import AlgebraicComplexity.MatrixMultiplication.MarkedXYPartitionedPowerHashing

/-!
# Marked hashing clients for the Duan--Wu--Zhou fine cleanup

This file composes the marked section 6.3 hashing family with the fine total-weight reference
profiles.  Every retained marked address lies in the actual depth-one quotient positive power,
marked hashing supplies the required `X`-injectivity, and the full tagged cell type of a retained
reference inherits all four compatibility profiles from its recovered marked source word.

The resulting restriction begins at that fixed-type selected tensor.  Choosing and counting such
types is the subsequent stage-assembly obligation; no good-seed estimate or extraction count is
assumed here.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor MoreAsymmetryCompatibility

universe u v

noncomputable section

/-- Every retained marked address is an address of the actual depth-one total-weight quotient
positive power. -/
theorem dwz63MarkedXYIsolatedPowerAddresses_subset_totalWeightPowerSupport
    {R : Type u} [Field R]
    (K : Type v) [CommRing K] (q n : ℕ)
    (hinjective : Function.Injective (cwSquareFieldValue (R := R)))
    (ambientWords markedWords : Finset (PositiveWord CWSquareSupport n))
    (B : Finset R) (seed : ProgressionHash.Seed R (Fin (n + 1))) :
    let H := dwz63PartitionHashEncoding hinjective
    H.markedXYIsolatedPowerAddresses n ambientWords markedWords B seed ⊆
      (((cwChunkPartitionedTensor K q 1).coarsen
        (cwTotalWeightChunkCoarsening 1)).positivePower n).support := by
  classical
  dsimp only
  let H := dwz63PartitionHashEncoding hinjective
  intro address haddress
  obtain ⟨word, _hword, hwordAddress⟩ :=
    H.exists_markedSourceWord_of_mem_markedXYIsolatedPowerAddresses
      n ambientWords markedWords B seed haddress
  rw [← hwordAddress]
  rw [PartitionedTensor.positivePower_support_eq_image_positiveSupportWordBlockAddress,
    cwTotalWeightCoarseSupport_one_eq_cwSquareSupport]
  exact Finset.mem_image.mpr ⟨word, Finset.mem_univ _, rfl⟩

/-- **C2 above-cutoff client.**  The full tagged cell type of any retained marked reference
restricts to the indexed direct sum surviving the two fine total-weight compatibility passes.

The hashing family discharges `hambient` and `hX`; the sole fine-configuration premise supplies
the reference type, hence both client pass equations. -/
theorem dwz63FineMarkedXYFixedTargetCleanup_to_indexedDirectSum
    {R : Type u} [Field R] [NeZero (2 : R)]
    (K : Type v) [CommRing K] (q n k : ℕ)
    (hinjective : Function.Injective (cwSquareFieldValue (R := R)))
    {fineCount : CWDepthOneFineLetter → ℕ}
    (hconfiguration : Dwz63FineConfiguration fineCount)
    (B : Finset R) (hB : ThreeAPFree (B : Set R))
    (seed : ProgressionHash.Seed R (Fin (n + 1)))
    (reference : BlockAddress
      (fun _c ↦ PositiveWord (CWCoarseDigit 1) n))
    (hreference :
      let H := dwz63PartitionHashEncoding hinjective
      let ambientWords := dwz63AmbientWords n
        (WordType.proportionalCounts dwz63AlphaX (200000000 * k))
        (WordType.proportionalCounts dwz63AlphaX (200000000 * k))
        (WordType.proportionalCounts dwz63AlphaZ (200000000 * k))
      let markedWords := dwz63MarkedWords n
        (WordType.proportionalCounts dwz63Alpha (200000000 * k))
      reference ∈ H.markedXYIsolatedPowerAddresses
        n ambientWords markedWords B seed) :
    let H := dwz63PartitionHashEncoding hinjective
    let ambientWords := dwz63AmbientWords n
      (WordType.proportionalCounts dwz63AlphaX (200000000 * k))
      (WordType.proportionalCounts dwz63AlphaX (200000000 * k))
      (WordType.proportionalCounts dwz63AlphaZ (200000000 * k))
    let markedWords := dwz63MarkedWords n
      (WordType.proportionalCounts dwz63Alpha (200000000 * k))
    let coarseKept := H.markedXYIsolatedPowerAddresses
      n ambientWords markedWords B seed
    let rawTargets := dwz63FineCompatibilityTargets fineCount k
    let ambient := cwFixedTargetCellTypeCoarseSupport
      1 n (fun _ : Fin (n + 1) ↦ (PUnit.unit : PUnit.{1}))
        (Equiv.refl Leg) coarseKept reference
    let Q := (cwChunkPartitionedTensor K q 1).coarsen
      (cwTotalWeightChunkCoarsening 1)
    let P := (Q.positivePower n).withSupport ambient
    let model := cwTotalWeightFeatureCompatibilityModel 1 n
      (fun _ : Fin (n + 1) ↦ (PUnit.unit : PUnit.{1}))
    let targets := cwTotalWeightPushforwardTargets rawTargets
    let ySupport := compatibilityIsolatedSupport ambient .Y
      (model.FeatureCompatibleY targets)
    let zSupport := compatibilityIsolatedSupport ySupport .Z
      (model.FeatureCompatibleZ targets)
    Restricts P.realize
      (Tensor.indexedDirectSum
        (fun address : zSupport ↦ P.constituent address.1)) := by
  classical
  dsimp only at hreference ⊢
  let H := dwz63PartitionHashEncoding hinjective
  let ambientWords := dwz63AmbientWords n
    (WordType.proportionalCounts dwz63AlphaX (200000000 * k))
    (WordType.proportionalCounts dwz63AlphaX (200000000 * k))
    (WordType.proportionalCounts dwz63AlphaZ (200000000 * k))
  let markedWords := dwz63MarkedWords n
    (WordType.proportionalCounts dwz63Alpha (200000000 * k))
  let coarseKept := H.markedXYIsolatedPowerAddresses
    n ambientWords markedWords B seed
  let rawTargets := dwz63FineCompatibilityTargets fineCount k
  have hwords : markedWords ⊆ ambientWords := by
    exact dwz63MarkedWords_subset_ambientWords_proportional n (200000000 * k)
  have hambient : coarseKept ⊆
      (((cwChunkPartitionedTensor K q 1).coarsen
        (cwTotalWeightChunkCoarsening 1)).positivePower n).support := by
    exact dwz63MarkedXYIsolatedPowerAddresses_subset_totalWeightPowerSupport
      K q n hinjective ambientWords markedWords B seed
  have hX : Set.InjOn
      (fun address : BlockAddress
        (fun _c ↦ PositiveWord (CWCoarseDigit 1) n) ↦ address .X) coarseKept := by
    exact H.x_injectiveOn_markedXYIsolatedPowerAddresses
      n ambientWords markedWords hwords B hB seed
  have hreference' : reference ∈ coarseKept := hreference
  obtain ⟨referenceWord, hreferenceWord, hreferenceAddress⟩ :=
    H.exists_markedSourceWord_of_mem_markedXYIsolatedPowerAddresses
      n ambientWords markedWords B seed hreference'
  have hprofiles : CWTotalWeightReferenceProfiles
      1 n (fun _ : Fin (n + 1) ↦ (PUnit.unit : PUnit.{1})) rawTargets reference := by
    rw [← hreferenceAddress]
    exact dwz63FineReferenceProfiles_of_mem_dwz63MarkedWords
      hconfiguration k n referenceWord hreferenceWord
  simpa only [H, ambientWords, markedWords, coarseKept, rawTargets] using
    (cwTotalWeightFixedTargetCellTypeYZCompatibilityCleanup_to_indexedDirectSum
      K q 1 n (fun _ : Fin (n + 1) ↦ (PUnit.unit : PUnit.{1}))
        rawTargets coarseKept hambient hX reference hprofiles)

end

end AlgebraicComplexity.Examples
