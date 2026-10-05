/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoStepOneCutSeedStage
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoCompetitorBound
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoPlainSharpDegree

set_option autoImplicit false

/-!
# The counting inputs of the seed selection, at the canonical relation

Layer 4 (`AlgebraicComplexity/Examples/`).  `[duan2023faster]`, section 6.1 `sec:global-algo`,
paragraph "Asymmetric Hashing", `papers/sources/2210.10173/global_value.tex:130-140`:

> We let `M_0 = 8 · max{N_triple/N_X, N_α · p_comp/N_Z}` and let `M ∈ [M_0, 2 M_0]` be a prime.
> Applying the asymmetric hashing according to `sec:hashing` with modulus `M`, we know the number
> of retained triples is `E[N_retain] ≥ N_α/M · 2^{-o(n)}`.  (`:137-139`)

Two of the seed selection's hypotheses are that paragraph's arithmetic, and this module discharges
them at the compatibility relation the Step-1 cut uses.

`dwz63_cut_hquarter` is the **first branch of `M_0`** (`:137`).  `N_triple/N_X` is the average size
of an `X`-fibre of the marginally consistent family, which the tree transcribes as
`dwz63PlainSharpDegree = ⌊N_triple/N_X⌋ + 1`
(`Examples/DuanWuZhouLevelTwoPlainSharpDegree.lean:51`).  The committed `dwz63_plain_hXfiber` and
`dwz63_plain_hYfiber` (`:92`, `:105`) bound each fibre by it;
`card_xyCompetitorYIndices_le_two_mul` (`Combinatorics/TwoLegHashingExtraction.lean:75`) bounds the
two-leg collision proxy by twice a common fibre bound; and the paper's factor `8` is the one
carried by `dwz63SharpHashModulus_requirement`
(`Examples/DuanWuZhouLevelTwoSharpDegree.lean:179`).  So `4 · #proxy ≤ 8 · d ≤ M = #R`:
the quarter rule is `M_0`'s first branch, with room to spare.

`dwz63_cut_hzIndex` is `def:global-compatible`'s standing hypothesis `Z_K̂ ∈ Z_K` (`:45`) read
through the encoding: a competitor of `a` carries `a`'s large `Z`-block, hence its hash `Z`-word.

Primary source `[duan2023faster]`: Ran Duan, Hongxun Wu and Renfei Zhou, *Faster Matrix
Multiplication via Asymmetric Hashing*, arXiv:2210.10173, section 6.1 `sec:global-algo`,
`papers/sources/2210.10173/global_value.tex:44-50, 130-140`.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor ProgressionHash CompatibleSplit
open scoped BigOperators

universe u

noncomputable section

/-- **The quarter rule** (`global_value.tex:137`, the first branch of `M_0`).

Four times the two-leg collision proxy of any marked triple fits in the hashing field, because the
proxy is at most twice a leg fibre, a leg fibre is at most the sharp degree, and the modulus is at
least eight times that degree --- the paper's own factor `8`.

Proof sketch: `card_xyCompetitorYIndices_le_two_mul` against the two committed fibre bounds, then
`dwz63SharpHashModulus_requirement` through `card_dwz63SharpHashField`. -/
theorem dwz63_cut_hquarter (K : Type u) [CommRing K] {n t : ℕ}
    (hn : n + 1 = 100000000 * t)
    {markedWords : Finset (PositiveWord ((cwSquarePartitionedTensor K dwz63Q).support) n)}
    (hmarked : markedWords ⊆ dwz63PlainMarginalWords K n t) :
    ∀ a ∈ (cwSquarePartitionHashEncoding
        (dwz63_cwSquareFieldValue_sharpHashField_injective
          (dwz63PlainSharpDegree K n t))).legalTargets n markedWords,
      4 * (LegalTriple.xyCompetitorYIndices
        ((cwSquarePartitionHashEncoding
          (dwz63_cwSquareFieldValue_sharpHashField_injective
            (dwz63PlainSharpDegree K n t))).legalTargets n
          (dwz63PlainMarginalWords K n t)) a).card ≤
        Fintype.card (dwz63SharpHashField (dwz63PlainSharpDegree K n t)) := by
  intro a ha
  have hproxy := LegalTriple.card_xyCompetitorYIndices_le_two_mul
    ((cwSquarePartitionHashEncoding
      (dwz63_cwSquareFieldValue_sharpHashField_injective
        (dwz63PlainSharpDegree K n t))).legalTargets n (dwz63PlainMarginalWords K n t))
    a (dwz63PlainSharpDegree K n t)
    (dwz63_plain_hXfiber K _ hn hmarked a ha)
    (dwz63_plain_hYfiber K _ hn hmarked a ha)
  have hreq := dwz63SharpHashModulus_requirement (dwz63PlainSharpDegree K n t)
  rw [card_dwz63SharpHashField]
  omega

/-! ## The competitor count (`global_value.tex:135`, `lemma:pcomp_g`) -/

section Competitors

variable {K : Type u} [CommRing K]

/-- **Every marked triple's own frame exists.**

A marked legal triple's source word lies in the same exact type class as the reference word, so a
position relabelling carries one onto the other; `dwz63FrameOf` is then a genuine frame for that
triple's address. -/
theorem dwz63_cut_frame (K : Type u) [CommRing K] {n t : ℕ}
    (hinj : Function.Injective (cwSquareFieldValue
      (R := dwz63SharpHashField (dwz63PlainSharpDegree K n t))))
    (wRef : PositiveWord ((cwSquarePartitionedTensor K dwz63Q).support) n)
    (hwRef : wRef ∈ dwz63MarkedWords n (WordType.proportionalCounts dwz63Alpha t))
    (a : LegalTriple (dwz63SharpHashField (dwz63PlainSharpDegree K n t)) (Fin (n + 1))
      (cwSquarePartitionHashEncoding hinj).target)
    (ha : a ∈ (cwSquarePartitionHashEncoding hinj).legalTargets n
      (dwz63MarkedWords n (WordType.proportionalCounts dwz63Alpha t))) :
    positiveSupportWordBlockAddress ((cwSquarePartitionedTensor K dwz63Q).support) n
        (positiveWordPositionEquiv ((cwSquarePartitionedTensor K dwz63Q).support) n
          (dwz63FrameOf K n wRef ((cwSquarePartitionHashEncoding hinj).modeledAddress n a))
          wRef) =
      (cwSquarePartitionHashEncoding hinj).modeledAddress n a := by
  classical
  refine dwz63_frameOf_spec K n wRef _ ?_
  have hsrc : (cwSquarePartitionHashEncoding hinj).sourceWordOfLegalTriple n a ∈
      dwz63MarkedWords n (WordType.proportionalCounts dwz63Alpha t) :=
    (cwSquarePartitionHashEncoding hinj).sourceWordOfLegalTriple_mem_of_mem n _ ha
  obtain ⟨σ, hσ⟩ := exists_positiveWordPositionEquiv_of_multiplicity_eq wRef
    ((cwSquarePartitionHashEncoding hinj).sourceWordOfLegalTriple n a)
    ((mem_positiveTypeClass.1 hwRef).trans (mem_positiveTypeClass.1 hsrc).symm)
  exact ⟨σ, by rw [hσ]; rfl⟩

/-- **Usefulness at the owner's own frame** (`def:useful_g`, `global_value.tex:75-82`).

The canonical read transports an available word into the owner's frame, where the owner's component
word is the segmentation the word is available for; `isUseful_of_segmentedAvailableWord` then
applies with `hS := rfl`. -/
theorem dwz63_cut_huseful (K : Type u) [CommRing K] {n t : ℕ} (s : ℕ)
    (hinj : Function.Injective (cwSquareFieldValue
      (R := dwz63SharpHashField (dwz63PlainSharpDegree K n t))))
    (wRef : PositiveWord ((cwSquarePartitionedTensor K dwz63Q).support) n)
    (hwRef : wRef ∈ dwz63MarkedWords n (WordType.proportionalCounts dwz63Alpha t)) :
    ∀ a ∈ (cwSquarePartitionHashEncoding hinj).legalTargets n
        (dwz63MarkedWords n (WordType.proportionalCounts dwz63Alpha t)),
      ∀ w : SegmentedAvailableWord (dwz63Seg K n wRef) (dwz63JoinedAlphaTilde s),
        (dwz63SplitPair s).IsUseful (dwz63CutComponent K n hinj a)
          (dwz63CanonicalRead K n hinj wRef (dwz63JoinedAlphaTilde s) a w) := by
  classical
  intro a ha w
  have hframe := dwz63_cut_frame K hinj wRef hwRef a ha
  have hcomp : dwz63CutComponent K n hinj a =
      dwz63Seg K n (positiveWordPositionEquiv
        ((cwSquarePartitionedTensor K dwz63Q).support) n
        (dwz63FrameOf K n wRef ((cwSquarePartitionHashEncoding hinj).modeledAddress n a))
        wRef) := by
    have e1 := dwz63Seg_eq_cellWordOfAddress K
      ((cwSquarePartitionHashEncoding hinj).sourceWordOfLegalTriple n a)
    have e2 := dwz63Seg_eq_cellWordOfAddress K
      (positiveWordPositionEquiv ((cwSquarePartitionedTensor K dwz63Q).support) n
        (dwz63FrameOf K n wRef ((cwSquarePartitionHashEncoding hinj).modeledAddress n a)) wRef)
    show dwz63Seg K n ((cwSquarePartitionHashEncoding hinj).sourceWordOfLegalTriple n a) = _
    rw [e1, e2, hframe]
    rfl
  rw [hcomp]
  exact isUseful_of_segmentedAvailableWord (dwz63SplitPair s) _ (dwz63JoinedAlphaTilde s) rfl
    ⟨positiveWordPositionEquiv (PositiveWord CWBlock 1) n
      (dwz63FrameOf K n wRef ((cwSquarePartitionHashEncoding hinj).modeledAddress n a)) w.1,
      dwz63_segmentedAvailable_frameTransport K (dwz63JoinedAlphaTilde s) wRef _ w⟩

/-- **The component word determines the legal triple on the ambient family.** -/
theorem dwz63_cut_componentInjOn (K : Type u) [CommRing K] {n t : ℕ}
    (hinj : Function.Injective (cwSquareFieldValue
      (R := dwz63SharpHashField (dwz63PlainSharpDegree K n t)))) :
    ∀ x ∈ (cwSquarePartitionHashEncoding hinj).legalTargets n (dwz63PlainMarginalWords K n t),
      ∀ y ∈ (cwSquarePartitionHashEncoding hinj).legalTargets n (dwz63PlainMarginalWords K n t),
        dwz63CutComponent K n hinj x = dwz63CutComponent K n hinj y → x = y := by
  intro x hx y hy hxy
  have hword := dwz63Seg_injective K n hxy
  calc x = (cwSquarePartitionHashEncoding hinj).legalTriple n
        ((cwSquarePartitionHashEncoding hinj).sourceWordOfLegalTriple n x) :=
        ((cwSquarePartitionHashEncoding hinj).legalTriple_sourceWordOfLegalTriple_eq_of_mem n
          _ hx).symm
    _ = (cwSquarePartitionHashEncoding hinj).legalTriple n
        ((cwSquarePartitionHashEncoding hinj).sourceWordOfLegalTriple n y) := by rw [hword]
    _ = y := (cwSquarePartitionHashEncoding hinj).legalTriple_sourceWordOfLegalTriple_eq_of_mem n
        _ hy

/-- **The marked family is one joint type class**, read through the component word. -/
theorem dwz63_cut_hcompType (K : Type u) [CommRing K] {n t : ℕ}
    (hinj : Function.Injective (cwSquareFieldValue
      (R := dwz63SharpHashField (dwz63PlainSharpDegree K n t)))) :
    ∀ a ∈ (cwSquarePartitionHashEncoding hinj).legalTargets n
        (dwz63MarkedWords n (WordType.proportionalCounts dwz63Alpha t)),
      WordType.multiplicity (dwz63CutComponent K n hinj a) =
        WordType.proportionalCounts dwz63Alpha t := fun _a ha ↦
  dwz63_multiplicity_dwz63Seg_of_mem_markedWords K _ _
    ((cwSquarePartitionHashEncoding hinj).sourceWordOfLegalTriple_mem_of_mem n _ ha)

/-- **The typical set of a marked owner is nonempty**, witnessed by any available word. -/
theorem dwz63_cut_hTypical (K : Type u) [CommRing K] {n t : ℕ} (s : ℕ)
    (hinj : Function.Injective (cwSquareFieldValue
      (R := dwz63SharpHashField (dwz63PlainSharpDegree K n t))))
    (wRef : PositiveWord ((cwSquarePartitionedTensor K dwz63Q).support) n)
    (hwRef : wRef ∈ dwz63MarkedWords n (WordType.proportionalCounts dwz63Alpha t))
    (hpos : 0 < Fintype.card
      (SegmentedAvailableWord (dwz63Seg K n wRef) (dwz63JoinedAlphaTilde s))) :
    ∀ a ∈ (cwSquarePartitionHashEncoding hinj).legalTargets n
        (dwz63MarkedWords n (WordType.proportionalCounts dwz63Alpha t)),
      0 < ((dwz63SplitPair s).typicalSet
        ((dwz63SplitPair s).zIndex ∘ dwz63CutComponent K n hinj a)).card := by
  classical
  intro a ha
  obtain ⟨w⟩ := Fintype.card_pos_iff.mp hpos
  refine Finset.card_pos.mpr
    ⟨dwz63CanonicalRead K n hinj wRef (dwz63JoinedAlphaTilde s) a w, ?_⟩
  exact (dwz63SplitPair s).mem_typicalSet_of_mem_compatibleSet
    ((dwz63SplitPair s).mem_compatibleSet_of_mem_usefulSet
      ((dwz63SplitPair s).mem_usefulSet.2 (dwz63_cut_huseful K s hinj wRef hwRef a ha w)))

/-- **`hV` at the canonical relation** (`global_value.tex:135`, `lemma:pcomp_g`): the
competitor count is bounded by the uniform competitor bound, with no numeric certificate
left to supply. -/
theorem dwz63_cut_hV (K : Type u) [CommRing K] {n t : ℕ} (s : ℕ)
    (hinj : Function.Injective (cwSquareFieldValue
      (R := dwz63SharpHashField (dwz63PlainSharpDegree K n t))))
    (wRef : PositiveWord ((cwSquarePartitionedTensor K dwz63Q).support) n)
    (hwRef : wRef ∈ dwz63MarkedWords n (WordType.proportionalCounts dwz63Alpha t))
    (hpos : 0 < Fintype.card
      (SegmentedAvailableWord (dwz63Seg K n wRef) (dwz63JoinedAlphaTilde s))) :
    ∀ a ∈ (cwSquarePartitionHashEncoding hinj).legalTargets n
        (dwz63MarkedWords n (WordType.proportionalCounts dwz63Alpha t)),
      ∀ w : SegmentedAvailableWord (dwz63Seg K n wRef) (dwz63JoinedAlphaTilde s),
        ((dwz63SplitPair s).matchableCompatible (WordType.proportionalCounts dwz63Alpha t)
          ((dwz63SplitPair s).zIndex ∘ dwz63CutComponent K n hinj a)
          (dwz63CanonicalRead K n hinj wRef (dwz63JoinedAlphaTilde s) a w)).card ≤
          dwz63UniformCompetitorBound (dwz63SplitPair s) (dwz63CutComponent K n hinj)
            (WordType.proportionalCounts dwz63Alpha t)
            ((cwSquarePartitionHashEncoding hinj).legalTargets n
              (dwz63MarkedWords n (WordType.proportionalCounts dwz63Alpha t))) :=
  dwz63_hV_uniform (dwz63SplitPair s) (dwz63CutComponent K n hinj)
    (dwz63CanonicalRead K n hinj wRef (dwz63JoinedAlphaTilde s)) _ _
    (dwz63_cut_huseful K s hinj wRef hwRef) (dwz63_cut_hcompType K hinj)
    (dwz63_cut_hTypical K s hinj wRef hwRef hpos)

/-- **`hcompetitors` at the canonical relation**, in the shape the seed selection binds. -/
theorem dwz63_cut_hcompetitors (K : Type u) [CommRing K] {n t : ℕ} (s : ℕ)
    (hinj : Function.Injective (cwSquareFieldValue
      (R := dwz63SharpHashField (dwz63PlainSharpDegree K n t))))
    (wRef : PositiveWord ((cwSquarePartitionedTensor K dwz63Q).support) n)
    (hwRef : wRef ∈ dwz63MarkedWords n (WordType.proportionalCounts dwz63Alpha t))
    (hpos : 0 < Fintype.card
      (SegmentedAvailableWord (dwz63Seg K n wRef) (dwz63JoinedAlphaTilde s))) :
    ∀ a ∈ (cwSquarePartitionHashEncoding hinj).legalTargets n
        (dwz63MarkedWords n (WordType.proportionalCounts dwz63Alpha t)),
      ∀ w : SegmentedAvailableWord (dwz63Seg K n wRef) (dwz63JoinedAlphaTilde s),
        (dwz63FineCompetitors
          ((cwSquarePartitionHashEncoding hinj).legalTargets n
            (dwz63PlainMarginalWords K n t))
          (dwz63SplitCompatTyped (dwz63SplitPair s) (dwz63CutComponent K n hinj)
            (dwz63CanonicalRead K n hinj wRef (dwz63JoinedAlphaTilde s))
            (WordType.proportionalCounts dwz63Alpha t)) a w).card ≤
          dwz63UniformCompetitorBound (dwz63SplitPair s) (dwz63CutComponent K n hinj)
            (WordType.proportionalCounts dwz63Alpha t)
            ((cwSquarePartitionHashEncoding hinj).legalTargets n
              (dwz63MarkedWords n (WordType.proportionalCounts dwz63Alpha t))) :=
  dwz63_hcompetitorsTyped (dwz63SplitPair s) (dwz63CutComponent K n hinj)
    (dwz63CanonicalRead K n hinj wRef (dwz63JoinedAlphaTilde s)) _ _ _ _
    (dwz63_cut_componentInjOn K hinj) (dwz63_cut_hV K s hinj wRef hwRef hpos)

/-- **`hzIndex` at the canonical relation** (`def:global-compatible`'s `Z_K̂ ∈ Z_K`, `:45`).

A competitor of `a` shares `a`'s large `Z`-block, so through the encoding it shares `a`'s hash
`Z`-word.

Proof sketch: `dwz63_hzIndexTyped` reduces it to the encoding fact `hzHash`, and that is
`dwz63_zIndex_eq_of_componentWord` once the component word's `Z` leg is identified with the modelled
address's `Z` word by `dwz63_zIndex_dwz63Seg` and
`PartitionHashEncoding.positiveWordEquiv_supportWordAddress`. -/
theorem dwz63_cut_hzIndex (K : Type u) [CommRing K] {n t : ℕ} (s : ℕ)
    (hinj : Function.Injective (cwSquareFieldValue
      (R := dwz63SharpHashField (dwz63PlainSharpDegree K n t))))
    (wRef : PositiveWord ((cwSquarePartitionedTensor K dwz63Q).support) n)
    (hmarked : dwz63MarkedWords n (WordType.proportionalCounts dwz63Alpha t) ⊆
      dwz63PlainMarginalWords K n t) :
    ∀ a ∈ (cwSquarePartitionHashEncoding hinj).legalTargets n
        (dwz63MarkedWords n (WordType.proportionalCounts dwz63Alpha t)),
      ∀ w : SegmentedAvailableWord (dwz63Seg K n wRef) (dwz63JoinedAlphaTilde s),
        ∀ c ∈ dwz63FineCompetitors
          ((cwSquarePartitionHashEncoding hinj).legalTargets n
            (dwz63PlainMarginalWords K n t))
          (dwz63SplitCompatTyped (dwz63SplitPair s) (dwz63CutComponent K n hinj)
            (dwz63CanonicalRead K n hinj wRef (dwz63JoinedAlphaTilde s))
            (WordType.proportionalCounts dwz63Alpha t)) a w, c.zIndex = a.zIndex := by
  classical
  refine dwz63_hzIndexTyped (dwz63SplitPair s) (dwz63CutComponent K n hinj)
    (dwz63CanonicalRead K n hinj wRef (dwz63JoinedAlphaTilde s)) _ _ _ ?_
  intro x hx y hy hz
  refine dwz63_zIndex_eq_of_componentWord (cwSquarePartitionHashEncoding hinj) n
    (dwz63PlainMarginalWords K n t) hx
    ((cwSquarePartitionHashEncoding hinj).legalTargets_mono n hmarked hy) ?_
  funext i
  have hx' := dwz63_zIndex_dwz63Seg K
    ((cwSquarePartitionHashEncoding hinj).sourceWordOfLegalTriple n x) i
  have hy' := dwz63_zIndex_dwz63Seg K
    ((cwSquarePartitionHashEncoding hinj).sourceWordOfLegalTriple n y) i
  have e1 := congrFun (PartitionHashEncoding.positiveWordEquiv_supportWordAddress n
    ((cwSquarePartitionHashEncoding hinj).sourceWordOfLegalTriple n x) Leg.Z) i
  have e2 := congrFun (PartitionHashEncoding.positiveWordEquiv_supportWordAddress n
    ((cwSquarePartitionHashEncoding hinj).sourceWordOfLegalTriple n y) Leg.Z) i
  have hzi : dwz63ZIndex (dwz63CutComponent K n hinj x i) =
      dwz63ZIndex (dwz63CutComponent K n hinj y i) := congrFun hz i
  exact (e1.symm.trans (hx'.symm.trans (hzi.trans hy'))).trans e2

end Competitors

end

end AlgebraicComplexity.Examples
