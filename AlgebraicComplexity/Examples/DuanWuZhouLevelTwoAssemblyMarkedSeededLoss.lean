/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoAssemblyMarked
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoPlainBatchedEndpointSeededLoss
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoMarkedHashBranch

set_option autoImplicit false

/-!
# The section 6.3 assembly against the seeded endpoint, at the joint hash loss

Layer 4 (`AlgebraicComplexity/Examples/`).  `[duan2023faster]`'s §6.2 assembles the retained
count, the Hole Lemma and the leaf value into the value bound
(`papers/sources/2210.10173/global_value.tex:270-305`), instantiated at §6.3's level-two parameters
(`:332-378`).  `omega_lt_2374631_of_referenceLeafWeight_marked`
inherits the unseeded endpoint's quantification over every Behrend set and every seed, which the
hole side cannot supply: its stage and its batching bound hold only at a *good* seed, and the batch
count depends on the retained family, hence on the seed.

This module re-issues the telescope against
`omega_lt_2374631_of_plainBatchedStageAndLeaf_margin_seeded_loss`.  The effect on the residual
list is large: `a₀`, `hpos`, `haggregate`, `hbatches`, `hfit` and the batch count `batches` all
disappear into the single hypothesis `hseeded`, whose conjuncts are written in the spelling that
`dwz63_exists_seed_stage_marked`
(`Examples/DuanWuZhouLevelTwoHoleIntegrationStage.lean`) concludes in, and `hbranch` disappears
with them.

What is left: the 112 lane's `hcut`, the hole lane's `hseeded`, and the endpoint's own
`batchLoss` bookkeeping.  The reference word and the whole reference frame remain discharged, as in
`…AssemblyMarked.lean`.

The period-lattice premise is a **separate** binder and is *unused* by this theorem (it appears as
`_hlattice`).  It does not prove `hcut`: `hcut` remains an explicit residual supplied on its own.
The lattice is carried only as an upstream obligation, because the 112 lane states its orbit-row
certificates on it.

The hash loss is `dwz63PlainMarkedLossHashJoint`
(`Examples/DuanWuZhouLevelTwoMarkedHashBranch.lean`), the enlarged loss the joint type class costs,
which is what `exists_behrend_dwz63_plainHashBranch_marked` supplies and what
`dwz63_exists_seed_stage_marked` --- already generic in its `lossHash` parameter --- then carries
into its copy-count conjunct as `4 * lossHash`.  So `hseeded`'s third conjunct is written in that
lane's spelling.

`hseeded` is **not** supplied today.  `dwz63_exists_seed_stage_marked` takes `B` and
`ThreeAPFree B` as *inputs* and does not conclude the outer `∃ B` conjunct written here --- the
Behrend theorem supplies that wrapper --- and it remains conditional on its `hdom` premise, which
the current coarse-`Z` reference-hole isolation cannot establish.  The interface therefore composes
only after a compatibility-sensitive isolation repair.  Its dependency
`Examples/DuanWuZhouLevelTwoMarkedHashBranch.lean` also carries its own open module-hygiene
reissue.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor

universe u

noncomputable section

/-- **`omega < 2.374631` at the reference leaf, against the seeded endpoint.**

The reference word is produced here together with its marked membership (which is what the hole
lane's `dwz63_exists_seed_stage_marked` needs of it), `R2` is proved, and the reference frame is
gone.  Three residuals remain: `hcut`, `batchLoss`/`hbatchLoss`, and `hseeded`.

Proof sketch: the cutoff comes from `dwz63_referenceLeafAssembly_leafWeight` at
`margin := dwz63LeafMargin`; `choose` turns `dwz63_exists_referenceWord_marked` into the reference
word family together with its fifteen-cell profile and its membership in the marked family.  The
seeded endpoint is then applied with `leaf` and `markedWords` instantiated at that word,
`lossHash := dwz63PlainMarkedLossHashJoint K`, `hleafWeight` from the leaf-weight half, and
`hleafValue` by `dwz63_exp_pow_six_eq`, which is an equality rather than a slack. -/
theorem omega_lt_2374631_of_referenceLeafWeight_marked_seeded_loss (K : Type u) [Field K] :
    ∃ N : ℕ, ∀ (len scale s : ℕ → ℕ),
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
        (∀ j : ℕ, wRef j ∈
          dwz63MarkedWords (len j) (WordType.proportionalCounts dwz63Alpha (scale j))) ∧
        (-- `R3`: image 109's orbit premise, at the leaf margin.
         (∀ (j : ℕ) (o : Fin 3) (m : ℕ),
            m + 1 = 200000000 * (dwz63Alpha (dwz63OrbitRow o) * s j) →
            HasTauWeight K (symThree K (dwz63OrbitRegion K dwz63Q o (dwz63OrbitRow o) m
              (dwz63Alpha (dwz63OrbitRow o) * s j)).realize) dwz63Tau
              (Real.exp ((200000000 : ℝ) * ((dwz63Alpha (dwz63OrbitRow o) * s j : ℕ) : ℝ)
                * (dwz63OrbitLogVal o - dwz63LeafMargin)) ^ 3)) →
         ∀ batchLoss : ℕ → ℝ, Growth.Subexponential batchLoss →
           -- the hole lane's joint seed selection, in `dwz63_exists_seed_stage_marked`'s shape
           (∀ j : ℕ,
             ∃ (B : Finset (dwz63SharpHashField (dwz63PlainSharpDegree K (len j) (scale j))))
               (seed : ProgressionHash.Seed
                 (dwz63SharpHashField (dwz63PlainSharpDegree K (len j) (scale j)))
                 (Fin (len j + 1)))
               (batches : ℕ),
               ThreeAPFree (B : Set (dwz63SharpHashField
                 (dwz63PlainSharpDegree K (len j) (scale j)))) ∧
               Restricts
                 (Tensor.power (symSix K (cwSquarePartitionedTensor K dwz63Q).realize)
                   (len j + 1))
                 (Tensor.indexedDirectSum
                   (fun _ : dwz63SymSixIndex (Fin batches) ↦
                     symSix K (dwz63ReferenceLeaf K (len j) (dwz63JoinedAlphaTilde (s j))
                       (wRef j)).realize)) ∧
               dwz63TrueCopyRate ^ (6 * (len j + 1)) ≤
                 (4 * dwz63PlainMarkedLossHashJoint K (len j + 1)) ^ 6 *
                   ((Fintype.card (dwz63PlainJointRetainedSupport K
                     (dwz63_cwSquareFieldValue_sharpHashField_injective
                       (dwz63PlainSharpDegree K (len j) (scale j)))
                     (len j) (scale j)
                     (dwz63MarkedWords (len j)
                       (WordType.proportionalCounts dwz63Alpha (scale j)))
                     B seed) : ℝ) ^ 6) ∧
               ((dwz63PlainJointRetainedSupport K
                   (dwz63_cwSquareFieldValue_sharpHashField_injective
                     (dwz63PlainSharpDegree K (len j) (scale j)))
                   (len j) (scale j)
                   (dwz63MarkedWords (len j)
                     (WordType.proportionalCounts dwz63Alpha (scale j)))
                   B seed).card : ℝ) ≤
                 batchLoss (len j + 1) * (Fintype.card (Fin batches) : ℝ)) →
           omega K < (2374631 / 1000000 : ℝ)) := by
  obtain ⟨N, hN⟩ :=
    dwz63_referenceLeafAssembly_leafWeight K dwz63LeafMargin dwz63LeafMargin_pos
  refine ⟨N, fun len scale s hscale hlen hcofinal hs _hlattice ↦ ?_⟩
  choose wRef hmu hmark using fun j : ℕ ↦
    dwz63_exists_referenceWord_marked K (len j) (scale j) (s j) (hscale j) (hlen j)
  refine ⟨wRef, hmu, hmark, fun hcut batchLoss hbatchLoss hseeded ↦ ?_⟩
  exact omega_lt_2374631_of_plainBatchedStageAndLeaf_margin_seeded_loss
    (len := len) (scale := scale) (hcofinal := hcofinal)
    (leaf := fun j ↦
      (dwz63ReferenceLeaf K (len j) (dwz63JoinedAlphaTilde (s j)) (wRef j)).realize)
    (weight := fun j ↦
      Real.exp (((len j : ℝ) + 1) * (dwz63LogVal - dwz63LeafMargin)) ^ 6)
    (lossHash := dwz63PlainMarkedLossHashJoint K)
    (hlossNonneg := dwz63PlainMarkedLossHashJoint_nonneg K)
    (hlossSub := subexponential_dwz63PlainMarkedLossHashJoint K)
    (batchLoss := batchLoss) (hbatchLoss := hbatchLoss)
    (markedWords := fun j ↦ dwz63MarkedWords (len j)
      (WordType.proportionalCounts dwz63Alpha (scale j)))
    (hseeded := hseeded)
    (hleafWeight := hN len s hs wRef hmu hcut)
    (hleafValue := fun j ↦
      le_of_eq (dwz63_exp_pow_six_eq (dwz63LogVal - dwz63LeafMargin) (len j)).symm)

end

end AlgebraicComplexity.Examples
