/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoStepOneCutAssemblyMarked
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoStepOneCutDomination
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoHoleIntegrationSeedJoin
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoHoleIntegrationAvailability
import AlgebraicComplexity.MatrixMultiplication.PositiveWordTypeTransport

set_option autoImplicit false

/-!
# The section 6.3 stage over `𝒯^{(1)}` at the seed the hole side selects

Layer 4 (`AlgebraicComplexity/Examples/`).  The R1 re-issue of
`dwz63_exists_seed_stage_marked` (`Examples/DuanWuZhouLevelTwoHoleIntegrationStage.lean`, image
131), over the Step-1 cut and with that theorem's one residual **discharged**.

Image 131 had to leave the domination of the hole family as the binder `hdom`, because the
coarse-`Z` isolation it used tests only that a competitor *carries* the same `Z`-word, whereas
`[duan2023faster]` defines a hole through *compatibility*
(`papers/sources/2210.10173/global_value.tex:247-268`, necessary condition at `:255`).  Over the
Step-1 cut that condition is available, and `dwz63_card_cutReferenceHoles_le_seedSharedHoles`
proves it; this module instantiates the compatibility relation at the canonical frame
`dwz63FrameOf`, which is what makes the relation and the hole family speak of the same transported
word, and applies it.

So the output is image 131's three conjuncts --- the six-orientation stage, the sixth power of the
copy count, and the batching-loss bound --- with no hole-side residual left.

Primary source `[duan2023faster]`: Ran Duan, Hongxun Wu and Renfei Zhou, *Faster Matrix
Multiplication via Asymmetric Hashing*, arXiv:2210.10173, section 6.1 `sec:global-algo`,
`papers/sources/2210.10173/global_value.tex:98-121, 247-268`, with `hole_lemma.tex:159-168`, at the
section 6.3 instance (`global_value.tex:332-378`).
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor ProgressionHash
open scoped BigOperators

universe u v

noncomputable section

section Stage

variable {R : Type v} [Field R] [Fintype R] [NeZero (2 : R)]

/-- **The component word of a legal triple at the section 6.3 instance**: the segmentation of its
source word, which by `global_value.tex:32` is the word of level-two components `(I_t, J_t, K_t)`
of the large triple it models. -/
def dwz63CutComponent (K : Type u) [CommRing K] (n : ℕ)
    (hinj : Function.Injective (cwSquareFieldValue (R := R)))
    (x : LegalTriple R (Fin (n + 1)) (cwSquarePartitionHashEncoding hinj).target) :
    Fin (n + 1) → Fin 15 :=
  dwz63Seg K n ((cwSquarePartitionHashEncoding hinj).sourceWordOfLegalTriple n x)

/-- **The section 6.3 stage over `𝒯^{(1)}` at the jointly selected seed, with no hole-side
residual.**

One seed carries all three things the endpoint needs of it: the stage restriction at
`β := Fin batches`, the sixth power of the copy count, and the batching-loss bound on the retained
count.  Unlike image 131, the domination premise is not a binder: it is
`dwz63_card_cutReferenceHoles_le_seedSharedHoles` at the canonical frame.

Proof sketch: image 129's seed join selects the seed at the committed relation
`dwz63SplitCompatTyped` over `dwz63SplitPair s`, read through `dwz63CutComponent` and
`dwz63CanonicalRead`; `dwz63_hwitness_of_markedWords` supplies a frame for every retained address,
so `dwz63_frameOf_spec` makes `dwz63FrameOf` one; the aggregate hole fraction then follows from the
domination, and `dwz63_cutReferenceLeafAssembly_stage_marked` runs the four degeneration steps at
that same frame. -/
theorem dwz63_exists_seed_cutStage_marked
    (K : Type u) [CommRing K] (hinj : Function.Injective (cwSquareFieldValue (R := R)))
    (n t s : ℕ)
    (B : Finset R) (hB : ThreeAPFree (B : Set R))
    (wRef : PositiveWord ((cwSquarePartitionedTensor K dwz63Q).support) n)
    (hwRef : wRef ∈ dwz63MarkedWords n (WordType.proportionalCounts dwz63Alpha t))
    (hmu : ∀ u : Fin 15,
      WordType.multiplicity (dwz63Seg K n wRef) u = 200000000 * (dwz63Alpha u * s))
    (V : ℕ)
    (hquarter : ∀ a ∈ (cwSquarePartitionHashEncoding hinj).legalTargets n
        (dwz63MarkedWords n (WordType.proportionalCounts dwz63Alpha t)),
      4 * (LegalTriple.xyCompetitorYIndices
        ((cwSquarePartitionHashEncoding hinj).legalTargets n
          (dwz63PlainMarginalWords K n t)) a).card ≤ Fintype.card R)
    (hzIndex : ∀ a ∈ (cwSquarePartitionHashEncoding hinj).legalTargets n
        (dwz63MarkedWords n (WordType.proportionalCounts dwz63Alpha t)),
      ∀ w : SegmentedAvailableWord (dwz63Seg K n wRef) (dwz63JoinedAlphaTilde s),
      ∀ c ∈ dwz63FineCompetitors
        ((cwSquarePartitionHashEncoding hinj).legalTargets n
          (dwz63PlainMarginalWords K n t))
        (dwz63SplitCompatTyped (dwz63SplitPair s) (dwz63CutComponent K n hinj)
          (dwz63CanonicalRead K n hinj wRef (dwz63JoinedAlphaTilde s))
          (WordType.proportionalCounts dwz63Alpha t)) a w, c.zIndex = a.zIndex)
    (hcompetitors : ∀ a ∈ (cwSquarePartitionHashEncoding hinj).legalTargets n
        (dwz63MarkedWords n (WordType.proportionalCounts dwz63Alpha t)),
      ∀ w : SegmentedAvailableWord (dwz63Seg K n wRef) (dwz63JoinedAlphaTilde s),
      (dwz63FineCompetitors
        ((cwSquarePartitionHashEncoding hinj).legalTargets n
          (dwz63PlainMarginalWords K n t))
        (dwz63SplitCompatTyped (dwz63SplitPair s) (dwz63CutComponent K n hinj)
          (dwz63CanonicalRead K n hinj wRef (dwz63JoinedAlphaTilde s))
          (WordType.proportionalCounts dwz63Alpha t)) a w).card ≤ V)
    (hmodulus : 256 * V ≤ 3 * Fintype.card R)
    (useless : LegalTriple R (Fin (n + 1)) (cwSquarePartitionHashEncoding hinj).target → ℕ)
    (huseless : ∀ a, 32 * useless a ≤
      Fintype.card (SegmentedAvailableWord (dwz63Seg K n wRef) (dwz63JoinedAlphaTilde s)))
    (hlarge : 2 * dwz63GoodBatchSize n ≤
      dwz63JointSeedCount
        (dwz63MarkedWords n (WordType.proportionalCounts dwz63Alpha t)).card B.card
        (Fintype.card R))
    {lossHash : ℝ} (hlossHash : 0 ≤ lossHash)
    (hbranch : dwz63HashingBranch ^ (n + 1) *
        (4 * ((Fintype.card R : ℝ) * (Fintype.card R : ℝ))) ≤
      lossHash * (3 *
        ((dwz63MarkedWords n (WordType.proportionalCounts dwz63Alpha t)).card : ℝ) *
        (B.card : ℝ))) :
    ∃ (seed : ProgressionHash.Seed R (Fin (n + 1))) (batches : ℕ),
      Restricts
        (Tensor.power (symSix K (cwSquarePartitionedTensor K dwz63Q).realize) (n + 1))
        (Tensor.indexedDirectSum
          (fun _ : dwz63SymSixIndex (Fin batches) ↦
            symSix K (dwz63ReferenceLeaf K n (dwz63JoinedAlphaTilde s) wRef).realize)) ∧
      dwz63TrueCopyRate ^ (6 * (n + 1)) ≤
        (4 * lossHash) ^ 6 *
          ((Fintype.card (dwz63PlainJointRetainedSupport K hinj n t
            (dwz63MarkedWords n (WordType.proportionalCounts dwz63Alpha t)) B seed) : ℝ) ^ 6) ∧
      ((dwz63PlainJointRetainedSupport K hinj n t
          (dwz63MarkedWords n (WordType.proportionalCounts dwz63Alpha t)) B seed).card : ℝ) ≤
        ((4 * dwz63GoodBatchSize n : ℕ) : ℝ) * (Fintype.card (Fin batches) : ℝ) := by
  classical
  have hpos : 0 < Fintype.card
      (SegmentedAvailableWord (dwz63Seg K n wRef) (dwz63JoinedAlphaTilde s)) :=
    dwz63_card_segmentedAvailableWord_pos K n s wRef hmu
  obtain ⟨seed, hret, hagg, hcopy⟩ :=
    dwz63_exists_seed_holeFraction_and_copyCount K hinj n t
      (dwz63Seg K n wRef) (dwz63JoinedAlphaTilde s)
      (dwz63MarkedWords n (WordType.proportionalCounts dwz63Alpha t))
      (dwz63_marked_subset_marginal K n t) B
      (dwz63SplitCompatTyped (dwz63SplitPair s) (dwz63CutComponent K n hinj)
        (dwz63CanonicalRead K n hinj wRef (dwz63JoinedAlphaTilde s))
        (WordType.proportionalCounts dwz63Alpha t))
      V hquarter hzIndex hcompetitors hmodulus hpos useless huseless hlarge hlossHash hbranch
  obtain ⟨a₀⟩ := dwz63_nonempty_plainJointRetainedSupport K hinj n t
    (dwz63MarkedWords n (WordType.proportionalCounts dwz63Alpha t)) B seed hret
  -- the canonical frame is a frame, for every retained address
  have hex : ∀ a : dwz63PlainJointRetainedSupport K hinj n t
      (dwz63MarkedWords n (WordType.proportionalCounts dwz63Alpha t)) B seed,
      ∃ σ : Equiv.Perm (Fin (n + 1)),
        positiveSupportWordBlockAddress ((cwSquarePartitionedTensor K dwz63Q).support) n
            (positiveWordPositionEquiv ((cwSquarePartitionedTensor K dwz63Q).support) n σ wRef) =
          (a : BlockAddress fun _ : Leg ↦ PositiveWord (Fin 5) n) := by
    obtain ⟨perm', hperm'⟩ := exists_perm_positiveSupportWordBlockAddress
      ((cwSquarePartitionedTensor K dwz63Q).support) n wRef _
      (fun a ↦ dwz63_hwitness_of_markedWords K hinj n t
        (WordType.proportionalCounts dwz63Alpha t) B seed wRef hwRef a)
    exact fun a ↦ ⟨perm' a, hperm' a⟩
  have hperm : ∀ a : dwz63PlainJointRetainedSupport K hinj n t
      (dwz63MarkedWords n (WordType.proportionalCounts dwz63Alpha t)) B seed,
      positiveSupportWordBlockAddress ((cwSquarePartitionedTensor K dwz63Q).support) n
          (positiveWordPositionEquiv ((cwSquarePartitionedTensor K dwz63Q).support) n
            (dwz63FrameOf K n wRef
              (a : BlockAddress fun _ : Leg ↦ PositiveWord (Fin 5) n)) wRef) =
        (a : BlockAddress fun _ : Leg ↦ PositiveWord (Fin 5) n) :=
    fun a ↦ dwz63_frameOf_spec K n wRef _ (hex a)
  refine ⟨seed,
    dwz63GoodBatchCount (dwz63PlainJointRetainedSupport K hinj n t
      (dwz63MarkedWords n (WordType.proportionalCounts dwz63Alpha t)) B seed).card n, ?_,
    hcopy, ?_⟩
  · refine dwz63_cutReferenceLeafAssembly_stage_marked K hinj n t s B hB seed wRef a₀ _ hperm
      hpos ?_ (dwz63GoodBatchCount_pos hret) (dwz63GoodBatchCount_fit _ n)
    refine hagg _ fun a c hc hca ↦ ?_
    exact dwz63_card_cutReferenceHoles_le_seedSharedHoles K hinj
      (dwz63_marked_subset_marginal K n t) B hB seed a₀ rfl
      (dwz63_joinedAlphaTilde_zDegree s) wRef _ hperm (dwz63CutComponent K n hinj)
      (fun _ ↦ rfl) (dwz63CanonicalRead K n hinj wRef (dwz63JoinedAlphaTilde s))
      (fun b x hx z ↦ by
        show positiveWordEquiv (PositiveWord CWBlock 1) n
            (positiveWordPositionEquiv (PositiveWord CWBlock 1) n
              (dwz63FrameOf K n wRef
                ((cwSquarePartitionHashEncoding hinj).modeledAddress n x)) z.1) = _
        rw [hx]) a c hc hca useless
  · have hnat := card_le_four_mul_batchSize_mul_batchCount (n := n) hret
    rw [Fintype.card_fin]
    exact_mod_cast hnat

end Stage

end

end AlgebraicComplexity.Examples
