/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoAssembly
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoStepOneCutAssemblyMarked
import AlgebraicComplexity.MatrixMultiplication.PositiveWordTypeTransport
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoMarkedWitness
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoReferenceWord
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoPlainBatchedEndpointMarked

set_option autoImplicit false

/-!
# The section 6.3 assembly at the joint-type marked family

Layer 4 (`AlgebraicComplexity/Examples/`).  `[duan2023faster]`'s §6.2 assembly
(`papers/sources/2210.10173/global_value.tex:270-305`) at §6.3's level-two parameters (`:332-378`),
whose marked family is the joint type class `N_α` rather than the marginal `N_triple` (`:132-134`).
With the endpoint re-parameterised by its marked family
(`omega_lt_2374631_of_plainBatchedStageAndLeaf_margin_marked`), the assembly can be taken at

`markedWords j := dwz63MarkedWords (len j) (proportionalCounts dwz63Alpha (scale j))`,

the paper's `N_alpha`.  Against `Examples/DuanWuZhouLevelTwoAssemblyResidual.lean` this discharges
the whole **reference frame**:

* `hmarked` --- `dwz63_marked_subset_marginal`.
* `wRef` and its cell profile (`R2`) --- `dwz63_exists_referenceWord`, and its membership in the
  marked family --- `dwz63_referenceWord_mem_markedWords`.
* `perm`, `hperm` and even `hwitness` --- **gone**.  `dwz63_hwitness_of_markedWords` is a theorem
  once `wRef` lies in the marked family, and `exists_perm_positiveSupportWordBlockAddress` turns it
  into the frame inside the proof.

What remains is the hole side (`a₀`, `hpos`, `haggregate`, `hbatches`, `hfit`), the 112 lane's
`hcut` and its period lattice, the endpoint's own batching bookkeeping, and `hbranch` --- carried
verbatim as the count lane's binder until the Behrend bound is re-calibrated at
`#(dwz63MarkedWords)`.

Primary source: Ran Duan, Hongxun Wu and Renfei Zhou, *Faster Matrix Multiplication via Asymmetric
Hashing*, arXiv:2210.10173, section 6.3.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor

universe u v

noncomputable section

/-- Abbreviation for the retained family of copy `j` at a Behrend set and seed. -/
local notation "RetainedM" K ", " hinj ", " n ", " t ", " B ", " seed =>
  dwz63PlainJointRetainedSupport K hinj n t
    (dwz63MarkedWords n (WordType.proportionalCounts dwz63Alpha t)) B seed

/-! ## The reference word, inside the marked family -/

/-- **`R2` and marked membership together.**  `dwz63_exists_referenceWord` at the joined period,
packaged with `dwz63_referenceWord_mem_markedWords`. -/
theorem dwz63_exists_referenceWord_marked (K : Type u) [CommRing K] (n scale s : ℕ)
    (hscale : scale = 200000000 * s) (hn : n + 1 = 100000000 * scale) :
    ∃ wRef : PositiveWord ((cwSquarePartitionedTensor K dwz63Q).support) n,
      (∀ t : Fin 15,
        WordType.multiplicity (dwz63Seg K n wRef) t = 200000000 * (dwz63Alpha t * s)) ∧
      wRef ∈ dwz63MarkedWords n (WordType.proportionalCounts dwz63Alpha scale) := by
  have hn' : n + 1 = 20000000000000000 * s := by rw [hn, hscale]; ring
  obtain ⟨wRef, hwRef⟩ := dwz63_exists_referenceWord K n s hn'
  refine ⟨wRef, hwRef, dwz63_referenceWord_mem_markedWords K n _ wRef ?_⟩
  funext t
  rw [hwRef t, hscale]
  show 200000000 * (dwz63Alpha t * s) = dwz63Alpha t * (200000000 * s)
  ring


/-! ## The telescope -/

section Telescope

/-- **`omega < 2.374631` at the joint-type marked family, with the reference frame discharged.**

Against `omega_lt_2374631_of_referenceLeafWeight_margin'` the binders `R2`, `hwitness` (and with it
`perm`/`hperm`) are gone: the reference word is produced here and its marked membership makes
`dwz63_hwitness_of_markedWords` a theorem.  `hbranch` is the count lane's binder, carried verbatim
until the Behrend bound is re-calibrated at `#(dwz63MarkedWords)`.

Proof sketch: the cutoff is the one `dwz63_referenceLeafAssembly_leafWeight` returns at
`margin := dwz63LeafMargin`; `choose` turns `dwz63_exists_referenceWord_marked` into the reference
word family with its fifteen-cell profile and its marked membership.  The marked endpoint variant
is then applied with `leaf`, `weight` and `markedWords` instantiated at that word, `hstage` from
`dwz63_cutReferenceLeafAssembly_stage_marked` (the Step-1 cut family), `hleafWeight` from the
leaf-weight half, and `hleafValue` by `dwz63_exp_pow_six_eq`. -/
theorem omega_lt_2374631_of_referenceLeafWeight_marked (K : Type u) [Field K] :
    ∃ N : ℕ, ∀ (len scale s batches : ℕ → ℕ),
      (∀ j : ℕ, scale j = 200000000 * s j) →
      (∀ j : ℕ, len j + 1 = 100000000 * scale j) →
      (∀ cutoff : ℕ, ∃ j : ℕ, cutoff ≤ len j + 1) →
      (∀ j : ℕ, N ≤ s j) →
      -- the 112 lane's period lattice
      (∀ j : ℕ, 40000000000000 ∣ s j ∧ 312500000000000000000 ∣ s j) →
      ∃ wRef : ∀ j : ℕ, PositiveWord ((cwSquarePartitionedTensor K dwz63Q).support) (len j),
        (∀ (j : ℕ) (t : Fin 15),
          WordType.multiplicity (dwz63Seg K (len j) (wRef j)) t
            = 200000000 * (dwz63Alpha t * s j)) ∧
        (-- `R3`: image 109's orbit premise, at the leaf margin.
         (∀ (j : ℕ) (o : Fin 3) (m : ℕ),
            m + 1 = 200000000 * (dwz63Alpha (dwz63OrbitRow o) * s j) →
            HasTauWeight K (symThree K (dwz63OrbitRegion K dwz63Q o (dwz63OrbitRow o) m
              (dwz63Alpha (dwz63OrbitRow o) * s j)).realize) dwz63Tau
              (Real.exp ((200000000 : ℝ) * ((dwz63Alpha (dwz63OrbitRow o) * s j : ℕ) : ℝ)
                * (dwz63OrbitLogVal o - dwz63LeafMargin)) ^ 3)) →
         -- `R6`
         ∀ a₀ : ∀ (j : ℕ)
             (B : Finset (dwz63SharpHashField (dwz63PlainSharpDegree K (len j) (scale j))))
             (seed : ProgressionHash.Seed
               (dwz63SharpHashField (dwz63PlainSharpDegree K (len j) (scale j)))
               (Fin (len j + 1))),
             (RetainedM K, (dwz63_cwSquareFieldValue_sharpHashField_injective
               (dwz63PlainSharpDegree K (len j) (scale j))), (len j), (scale j), B, seed),
           -- `R7`
           (∀ j : ℕ, 0 < Fintype.card
             (SegmentedAvailableWord (dwz63Seg K (len j) (wRef j))
               (dwz63JoinedAlphaTilde (s j)))) →
           -- `R8`, for every frame
           (∀ (j : ℕ)
             (B : Finset (dwz63SharpHashField (dwz63PlainSharpDegree K (len j) (scale j))))
             (seed : ProgressionHash.Seed
               (dwz63SharpHashField (dwz63PlainSharpDegree K (len j) (scale j)))
               (Fin (len j + 1)))
             (perm : (RetainedM K, (dwz63_cwSquareFieldValue_sharpHashField_injective
               (dwz63PlainSharpDegree K (len j) (scale j))), (len j), (scale j), B, seed) →
               Equiv.Perm (Fin (len j + 1))),
             (∀ a, positiveSupportWordBlockAddress
                 ((cwSquarePartitionedTensor K dwz63Q).support) (len j)
                 (positiveWordPositionEquiv
                   ((cwSquarePartitionedTensor K dwz63Q).support) (len j) (perm a) (wRef j)) =
               (a : BlockAddress fun _ : Leg ↦ PositiveWord (Fin 5) (len j))) →
             Dwz63AggregateHoleFraction (dwz63Seg K (len j) (wRef j))
               (dwz63JoinedAlphaTilde (s j))
               (RetainedM K, (dwz63_cwSquareFieldValue_sharpHashField_injective
                 (dwz63PlainSharpDegree K (len j) (scale j))), (len j), (scale j), B, seed)
               (fun a ↦ dwz63CutReferenceHoles K _ (a₀ j B seed) (s j)
                 (dwz63JoinedAlphaTilde (s j)) (wRef j) perm a)) →
           -- `R9`, `R10`
           (∀ j : ℕ, 0 < batches j) →
           (∀ (j : ℕ)
             (B : Finset (dwz63SharpHashField (dwz63PlainSharpDegree K (len j) (scale j))))
             (seed : ProgressionHash.Seed
               (dwz63SharpHashField (dwz63PlainSharpDegree K (len j) (scale j)))
               (Fin (len j + 1))),
             2 * (batches j * dwz63GoodBatchSize (len j)) ≤
               (dwz63PlainJointRetainedSupport K
                 (dwz63_cwSquareFieldValue_sharpHashField_injective
                   (dwz63PlainSharpDegree K (len j) (scale j)))
                 (len j) (scale j)
                 (dwz63MarkedWords (len j)
                   (WordType.proportionalCounts dwz63Alpha (scale j))) B seed).card) →
           -- the endpoint's bookkeeping, and the count lane's branch binder
           ∀ batchLoss : ℕ → ℝ, Growth.Subexponential batchLoss →
             (∀ (j : ℕ)
               (B : Finset (dwz63SharpHashField (dwz63PlainSharpDegree K (len j) (scale j))))
               (seed : ProgressionHash.Seed
                 (dwz63SharpHashField (dwz63PlainSharpDegree K (len j) (scale j)))
                 (Fin (len j + 1))),
               ThreeAPFree (B : Set (dwz63SharpHashField
                 (dwz63PlainSharpDegree K (len j) (scale j)))) →
               (((dwz63PlainJointRetainedSupport K
                   (dwz63_cwSquareFieldValue_sharpHashField_injective
                     (dwz63PlainSharpDegree K (len j) (scale j)))
                   (len j) (scale j)
                   (dwz63MarkedWords (len j)
                     (WordType.proportionalCounts dwz63Alpha (scale j))) B seed).card : ℝ)) ≤
                 batchLoss (len j + 1) * (Fintype.card (Fin (batches j)) : ℝ)) →
             (∀ j : ℕ, ∃ B : Finset (dwz63SharpHashField
                 (dwz63PlainSharpDegree K (len j) (scale j))),
               ThreeAPFree (B : Set (dwz63SharpHashField
                 (dwz63PlainSharpDegree K (len j) (scale j)))) ∧
               dwz63HashingBranch ^ (len j + 1) *
                   (4 * ((Fintype.card (dwz63SharpHashField
                       (dwz63PlainSharpDegree K (len j) (scale j))) : ℝ) *
                     (Fintype.card (dwz63SharpHashField
                       (dwz63PlainSharpDegree K (len j) (scale j))) : ℝ))) ≤
                 dwz63PlainMarkedLossHash K (len j + 1) *
                   (3 * ((dwz63MarkedWords (len j)
                     (WordType.proportionalCounts dwz63Alpha (scale j))).card : ℝ) *
                     (B.card : ℝ))) →
             omega K < (2374631 / 1000000 : ℝ)) := by
  obtain ⟨N, hN⟩ :=
    dwz63_referenceLeafAssembly_leafWeight K dwz63LeafMargin dwz63LeafMargin_pos
  refine ⟨N, fun len scale s batches hscale hlen hcofinal hs _hlattice ↦ ?_⟩
  choose wRef hmu hmark using fun j : ℕ ↦
    dwz63_exists_referenceWord_marked K (len j) (scale j) (s j) (hscale j) (hlen j)
  refine ⟨wRef, hmu, fun hcut a₀ hpos haggregate hbatches hfit
    batchLoss hbatchLoss hbatchCard hbranch ↦ ?_⟩
  exact omega_lt_2374631_of_plainBatchedStageAndLeaf_margin_marked
    (len := len) (scale := scale) (hlen := hlen) (hcofinal := hcofinal)
    (markedWords := fun j ↦ dwz63MarkedWords (len j)
      (WordType.proportionalCounts dwz63Alpha (scale j)))
    (hmarked := fun j ↦ dwz63_marked_subset_marginal K (len j) (scale j))
    (leaf := fun j ↦
      (dwz63ReferenceLeaf K (len j) (dwz63JoinedAlphaTilde (s j)) (wRef j)).realize)
    (weight := fun j ↦
      Real.exp (((len j : ℝ) + 1) * (dwz63LogVal - dwz63LeafMargin)) ^ 6)
    (batchLoss := batchLoss) (hbatchLoss := hbatchLoss)
    (hstage := fun j B seed hB ↦ by
      obtain ⟨perm, hperm⟩ :=
        exists_perm_positiveSupportWordBlockAddress
          ((cwSquarePartitionedTensor K dwz63Q).support) (len j) (wRef j) _
          (fun a ↦ dwz63_hwitness_of_markedWords K
            (dwz63_cwSquareFieldValue_sharpHashField_injective
              (dwz63PlainSharpDegree K (len j) (scale j)))
            (len j) (scale j)
            (WordType.proportionalCounts dwz63Alpha (scale j)) B seed (wRef j) (hmark j) a)
      exact dwz63_cutReferenceLeafAssembly_stage_marked K
        (dwz63_cwSquareFieldValue_sharpHashField_injective
          (dwz63PlainSharpDegree K (len j) (scale j)))
        (len j) (scale j) (s j) B hB seed (wRef j) (a₀ j B seed) perm hperm (hpos j)
        (haggregate j B seed perm hperm) (hbatches j) (hfit j B seed))
    (hbatchCard := hbatchCard)
    (hleafWeight := hN len s hs wRef hmu hcut)
    (hleafValue := fun j ↦
      le_of_eq (dwz63_exp_pow_six_eq (dwz63LogVal - dwz63LeafMargin) (len j)).symm)
    (hbranch := hbranch)

end Telescope

end

end AlgebraicComplexity.Examples
