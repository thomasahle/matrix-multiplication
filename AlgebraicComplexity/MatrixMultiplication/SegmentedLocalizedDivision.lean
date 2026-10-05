/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.SegmentedLocalizedHoleRepair

set_option autoImplicit false

/-!
# Dividing a localized segmented leaf across consecutive position regions

Layer 3 (`AlgebraicComplexity/MatrixMultiplication/`).  `RestrictedSplittingPower.lean:224`'s
`SplitRestriction.keeps_append` is the combinatorial half of `[duan2023faster]`'s `claim:degen`:
a concatenated word carries the parent's *pooled* split type as soon as its two consecutive
regions carry types that add.  That statement does not reach the leaf section 6.3 actually
produces, which is the **localized segmented** one
(`MatrixMultiplication/SegmentedLocalizedHoleRepair.lean`), whose keep predicate is a conjunction

`positiveWordMap f n word = target c`  and  `profile.Keeps n seg c word`,

i.e. "lies over the fixed coarse address" together with a type *per segment* rather than one
pooled type.  This module supplies the analogue: **both** conjuncts split across a concatenation.

* The coarsening conjunct splits because letterwise mapping commutes with concatenation
  (`Tensor.positiveWordMap_positiveWordAppend`) — so it suffices that the parent coarse target is
  the concatenation of the two regional targets.
* The segment-type conjunct splits because segment multiplicities add
  (`segmentMultiplicity_positiveWordAppend`), exactly as pooled multiplicities do.  The
  segmentation of a region is the parent segmentation restricted to that region's positions,
  which is what `segmentationLeft` / `segmentationRight` name.

The `hsum` hypothesis is the segmented analogue of `claim:degen`'s: it is asked **per segment**
`t`, because a segmented profile prescribes one type per segment.  In the section 6.3 use the two
regions are "one segment" and "all the others", so on the left region every segment other than the
peeled one is asked for the zero type — a condition its sub-word satisfies vacuously, since none
of its positions lie in those segments.

Nothing here is about `[duan2023faster]`'s alphabet, arity or values: the statements are generic in
the partition, the coarsening and the number of segments.

Primary source: Ran Duan, Hongxun Wu and Renfei Zhou, *Faster Matrix Multiplication via Asymmetric
Hashing*, arXiv:2210.10173, `hole_lemma.tex` and `global_value.tex` section 6.3.

Exact source lines: `papers/sources/2210.10173/global_value.tex:332-378` (§6.3),
`papers/sources/2210.10173/component_value.tex:18-24` (`claim:degen`),
`papers/sources/2210.10173/hole_lemma.tex:1-168` (whole file).
-/

namespace AlgebraicComplexity

open Tensor
open scoped BigOperators

universe u v w x

/-! ## Letterwise mapping commutes with concatenation -/

namespace Tensor

/-- **Mapping a concatenated positive word letterwise is the concatenation of the mapped
regions.**  The word-level content of the coarsening conjunct of `segmentedLocalizedKeep`. -/
theorem positiveWordMap_positiveWordAppend {I : Type w} {J : Type x} (f : I → J) {n : ℕ} :
    ∀ (m : ℕ) (left : PositiveWord I n) (right : PositiveWord I m),
      positiveWordMap f (n + m + 1) (positiveWordAppend left m right) =
        positiveWordAppend (positiveWordMap f n left) m (positiveWordMap f m right)
  | 0, _, _ => rfl
  | m + 1, left, right => by
      have ih := positiveWordMap_positiveWordAppend f m left right.1
      show (positiveWordMap f (n + m + 1) (positiveWordAppend left m right.1), f right.2) = _
      rw [ih]
      rfl

end Tensor

/-! ## Segment multiplicities add across a concatenation -/

section SegmentMultiplicity

variable {I : Type w} [DecidableEq I]

/-- The segment multiplicity as the cardinality of a fibre, with the decidability instance
normalized.  The segmented counterpart of `WordType.multiplicity_eq_card_fiber`. -/
theorem segmentMultiplicity_eq_card_fiber {N M : ℕ}
    (seg : Fin N → Fin M) (word : Fin N → I) (t : Fin M) (x : I) :
    segmentMultiplicity seg word t x = Fintype.card {i // seg i = t ∧ word i = x} := by
  classical
  rw [Fintype.card_subtype]
  unfold segmentMultiplicity
  congr 1

/-- **Segment multiplicities add under concatenation**, when the segmentation is concatenated
alongside the word.  The segmented analogue of `WordType.multiplicity_append`. -/
theorem segmentMultiplicity_append {a b M : ℕ}
    (segLeft : Fin a → Fin M) (segRight : Fin b → Fin M)
    (left : Fin a → I) (right : Fin b → I) (t : Fin M) :
    segmentMultiplicity (Fin.append segLeft segRight) (Fin.append left right) t =
      segmentMultiplicity segLeft left t + segmentMultiplicity segRight right t := by
  classical
  funext x
  rw [Pi.add_apply, segmentMultiplicity_eq_card_fiber, segmentMultiplicity_eq_card_fiber,
    segmentMultiplicity_eq_card_fiber, ← Fintype.card_sum]
  have hseg : ∀ i : Fin (a + b),
      Sum.elim segLeft segRight (finSumFinEquiv.symm i) = Fin.append segLeft segRight i := by
    intro i
    refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) i <;> simp
  have hword : ∀ i : Fin (a + b),
      Sum.elim left right (finSumFinEquiv.symm i) = Fin.append left right i := by
    intro i
    refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) i <;> simp
  refine Fintype.card_congr ?_
  refine Equiv.trans (β := {s : Fin a ⊕ Fin b //
      Sum.elim segLeft segRight s = t ∧ Sum.elim left right s = x})
    (finSumFinEquiv.symm.subtypeEquiv fun i ↦ by rw [hseg i, hword i]) Equiv.subtypeSum

/-- **A region all of whose positions lie in one segment has that segment's multiplicity equal to
its pooled multiplicity.**  The committed `segmentMultiplicity_one` is the case `M = 1`; the peeled
region of the section 6.3 factorisation needs it at a general segment of a general `Fin M`. -/
theorem segmentMultiplicity_const_self {N M : ℕ} (t : Fin M) (word : Fin N → I) :
    segmentMultiplicity (fun _ ↦ t) word t = WordType.multiplicity word := by
  funext a
  unfold segmentMultiplicity WordType.multiplicity
  congr 1
  ext i
  simp

/-- The same region has multiplicity zero on every other segment, so the types prescribed there
are met vacuously as soon as they are zero. -/
theorem segmentMultiplicity_const_of_ne {N M : ℕ} (t₀ t : Fin M) (h : t ≠ t₀)
    (word : Fin N → I) :
    segmentMultiplicity (fun _ ↦ t₀) word t = 0 := by
  funext a
  unfold segmentMultiplicity
  simp [Ne.symm h]

/-- Transporting the length of a word and its segmentation along an equality of lengths does not
change any segment multiplicity. -/
theorem segmentMultiplicity_cast {N N' M : ℕ} (h : N = N')
    (seg : Fin N' → Fin M) (word : Fin N' → I) (t : Fin M) :
    segmentMultiplicity (seg ∘ Fin.cast h) (word ∘ Fin.cast h) t =
      segmentMultiplicity seg word t := by
  subst h
  have hseg : seg ∘ Fin.cast (rfl : N = N) = seg := by funext i; simp
  have hword : word ∘ Fin.cast (rfl : N = N) = word := by funext i; simp
  rw [hseg, hword]

end SegmentMultiplicity

/-! ## The segmentation of a region -/

section Segmentation

variable {M : ℕ}

/-- **The segmentation induced on the left region** of a split of `n + p + 2` positions into a
left region of `n + 1` and a right region of `p + 1`. -/
def segmentationLeft (n p : ℕ) (seg : Fin (n + p + 1 + 1) → Fin M) : Fin (n + 1) → Fin M :=
  fun i ↦ seg (Fin.cast (by omega) (Fin.castAdd (p + 1) i))

/-- **The segmentation induced on the right region** of the same split. -/
def segmentationRight (n p : ℕ) (seg : Fin (n + p + 1 + 1) → Fin M) : Fin (p + 1) → Fin M :=
  fun j ↦ seg (Fin.cast (by omega) (Fin.natAdd (n + 1) j))

/-- The two regional segmentations concatenate back to the parent segmentation. -/
theorem append_segmentationLeft_segmentationRight (n p : ℕ)
    (seg : Fin (n + p + 1 + 1) → Fin M) :
    Fin.append (segmentationLeft n p seg) (segmentationRight n p seg) =
      seg ∘ Fin.cast (by omega : n + 1 + (p + 1) = n + p + 1 + 1) := by
  funext i
  refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) i
  · simp [segmentationLeft]
  · simp [segmentationRight]

variable {I : Type w} [DecidableEq I]

/-- **Segment multiplicities of a concatenated positive word.**  The segmented analogue of
`WordType.multiplicity_positiveWordAppend`. -/
theorem segmentMultiplicity_positiveWordAppend {n p : ℕ}
    (seg : Fin (n + p + 1 + 1) → Fin M)
    (left : PositiveWord I n) (right : PositiveWord I p) (t : Fin M) :
    segmentMultiplicity seg
        (positiveWordEquiv I (n + p + 1) (positiveWordAppend left p right)) t =
      segmentMultiplicity (segmentationLeft n p seg) (positiveWordEquiv I n left) t +
        segmentMultiplicity (segmentationRight n p seg) (positiveWordEquiv I p right) t := by
  have hcast : n + p + 1 + 1 = n + 1 + (p + 1) := by omega
  rw [positiveWordEquiv_append, ← segmentMultiplicity_append (segmentationLeft n p seg)
    (segmentationRight n p seg) (positiveWordEquiv I n left) (positiveWordEquiv I p right) t,
    ← segmentMultiplicity_cast hcast (Fin.append (segmentationLeft n p seg)
      (segmentationRight n p seg)) (Fin.append (positiveWordEquiv I n left)
        (positiveWordEquiv I p right)) t]
  congr 1
  rw [append_segmentationLeft_segmentationRight]
  funext i
  simp

end Segmentation

/-! ## The segmented keep predicate splits -/

section Keeps

variable {A : Leg → Type w} [∀ c, DecidableEq (A c)] {M : ℕ}

/-- The segmented keep predicate, phrased as an implication over the constrained segments.  This
is the working form: the `match` in `SegmentedSplitRestriction.Keeps` is awkward to case on
directly, and the committed `keeps_iff_of_some` asks *every* segment to be constrained. -/
theorem SegmentedSplitRestriction.keeps_iff (profile : SegmentedSplitRestriction A M) (n : ℕ)
    (seg : Fin (n + 1) → Fin M) (c : Leg) (word : PositiveWord (A c) n) :
    profile.Keeps n seg c word ↔
      ∀ (t : Fin M) (α : A c → ℕ), profile c t = some α →
        segmentMultiplicity seg (positiveWordEquiv (A c) n word) t = α := by
  constructor
  · intro h t α hα
    have ht := h t
    rw [hα] at ht
    exact ht
  · intro h t
    cases hp : profile c t with
    | none => trivial
    | some α => exact h t α hp

/-- **`SplitRestriction.keeps_append`, segmented.**

A concatenated word has the prescribed *per-segment* parent types as soon as its two consecutive
regions have the prescribed per-segment regional types, segment by segment, and the types add
segment by segment.  The regional segmentations are the parent segmentation restricted to the
regions. -/
theorem SegmentedSplitRestriction.keeps_append {n p : ℕ}
    {parent left right : SegmentedSplitRestriction A M}
    (seg : Fin (n + p + 1 + 1) → Fin M)
    (hsum : ∀ c t α, parent c t = some α →
      ∃ β γ, left c t = some β ∧ right c t = some γ ∧ α = β + γ)
    (c : Leg) (word : PositiveWord (A c) (n + p + 1))
    (hleft : left.Keeps n (segmentationLeft n p seg) c
      ((positiveWordAppendEquiv (A c) n p).symm word).1)
    (hright : right.Keeps p (segmentationRight n p seg) c
      ((positiveWordAppendEquiv (A c) n p).symm word).2) :
    parent.Keeps (n + p + 1) seg c word := by
  rw [SegmentedSplitRestriction.keeps_iff] at hleft hright ⊢
  intro t α hα
  obtain ⟨β, γ, hβ, hγ, hαβγ⟩ := hsum c t α hα
  set pieces := (positiveWordAppendEquiv (A c) n p).symm word with hpieces
  have happend : positiveWordAppend pieces.1 p pieces.2 = word := by
    rw [← positiveWordAppendEquiv_apply]
    exact (positiveWordAppendEquiv (A c) n p).apply_symm_apply word
  rw [← happend, segmentMultiplicity_positiveWordAppend, hleft t β hβ, hright t γ hγ, hαβγ]

/-- **On a region confined to one segment the segmented keep predicate is the pooled one.**

This is what identifies a factor of the section 6.3 factorisation with the *one-segment* fine cell
power the fusion `dwz63_fineCellPower_restricts_matrixMultiplication` consumes: on the peeled
region every other segment is asked for the zero type, and that is met vacuously. -/
theorem SegmentedSplitRestriction.keeps_const_seg_iff (profile : SegmentedSplitRestriction A M)
    (n : ℕ) (t₀ : Fin M) (c : Leg)
    (hother : ∀ t, t ≠ t₀ → profile c t = none ∨ profile c t = some 0)
    (word : PositiveWord (A c) n) :
    profile.Keeps n (fun _ ↦ t₀) c word ↔
      ∀ α, profile c t₀ = some α →
        WordType.multiplicity (positiveWordEquiv (A c) n word) = α := by
  rw [SegmentedSplitRestriction.keeps_iff]
  constructor
  · intro h α hα
    have ht := h t₀ α hα
    rwa [segmentMultiplicity_const_self] at ht
  · intro h t α hα
    by_cases ht : t = t₀
    · subst ht
      rw [segmentMultiplicity_const_self]
      exact h α hα
    · rcases hother t ht with hnone | hzero
      · rw [hnone] at hα
        simp at hα
      · rw [hzero] at hα
        have h0 : (0 : A c → ℕ) = α := Option.some.inj hα
        subst h0
        exact segmentMultiplicity_const_of_ne t₀ t ht _

omit [∀ c, DecidableEq (A c)] in
/-- **The `ofLeg` instance of the segmented `claim:degen` hypothesis.**  A single constrained leg
with per-segment types splits as soon as the types themselves split segment by segment. -/
theorem SegmentedSplitRestriction.ofLeg_sum (c₀ : Leg) (α β γ : Fin M → A c₀ → ℕ)
    (h : ∀ t, α t = β t + γ t) (c : Leg) (t : Fin M) (a : A c → ℕ)
    (ha : SegmentedSplitRestriction.ofLeg (A := A) c₀ α c t = some a) :
    ∃ b g, SegmentedSplitRestriction.ofLeg (A := A) c₀ β c t = some b ∧
      SegmentedSplitRestriction.ofLeg (A := A) c₀ γ c t = some g ∧ a = b + g := by
  by_cases hc : c₀ = c
  · subst hc
    rw [SegmentedSplitRestriction.ofLeg_self] at ha
    refine ⟨β t, γ t, SegmentedSplitRestriction.ofLeg_self c₀ β t,
      SegmentedSplitRestriction.ofLeg_self c₀ γ t, ?_⟩
    rw [← Option.some.inj ha, h t]
  · rw [SegmentedSplitRestriction.ofLeg_of_ne α hc] at ha
    simp at ha

end Keeps

/-! ## The localized segmented keep predicate splits -/

section LocalizedKeep

variable {A : Leg → Type w} {B : Leg → Type x}
variable [∀ c, DecidableEq (A c)] [∀ c, Fintype (B c)] [∀ c, DecidableEq (B c)]
variable {M : ℕ}

omit [∀ c, Fintype (B c)] [∀ c, DecidableEq (B c)] in
/-- **The localized segmented keep predicate splits across a concatenation.**

Increment (i) of the section 6.3 segment factorisation: both conjuncts of
`segmentedLocalizedKeep` --- coarsening onto the fixed target, and the per-segment types --- are
implied by their regional counterparts, provided the parent coarse target is the concatenation of
the two regional coarse targets and the prescribed types add segment by segment.

This is the legality step of `claim:degen` on the localized leaf: it says the regionwise selection
is again a leg-local selection *of the parent leaf*, so the parent restricts onto it. -/
theorem segmentedLocalizedKeep_append {n p : ℕ}
    (f : ∀ c, A c → B c)
    (seg : Fin (n + p + 1 + 1) → Fin M)
    {parent left right : SegmentedSplitRestriction A M}
    (hsum : ∀ c t α, parent c t = some α →
      ∃ β γ, left c t = some β ∧ right c t = some γ ∧ α = β + γ)
    (target : BlockAddress (fun c ↦ PositiveWord (B c) (n + p + 1)))
    (targetLeft : BlockAddress (fun c ↦ PositiveWord (B c) n))
    (targetRight : BlockAddress (fun c ↦ PositiveWord (B c) p))
    (htarget : ∀ c, target c = positiveWordAppend (targetLeft c) p (targetRight c))
    (c : Leg) (word : PositiveWord (A c) (n + p + 1))
    (hleft : segmentedLocalizedKeep f (segmentationLeft n p seg) left targetLeft c
      ((positiveWordAppendEquiv (A c) n p).symm word).1)
    (hright : segmentedLocalizedKeep f (segmentationRight n p seg) right targetRight c
      ((positiveWordAppendEquiv (A c) n p).symm word).2) :
    segmentedLocalizedKeep f seg parent target c word := by
  refine ⟨?_, SegmentedSplitRestriction.keeps_append seg hsum c word hleft.2 hright.2⟩
  set pieces := (positiveWordAppendEquiv (A c) n p).symm word with hpieces
  have happend : positiveWordAppend pieces.1 p pieces.2 = word := by
    rw [← positiveWordAppendEquiv_apply]
    exact (positiveWordAppendEquiv (A c) n p).apply_symm_apply word
  rw [← happend, Tensor.positiveWordMap_positiveWordAppend, hleft.1, hright.1, htarget c]

end LocalizedKeep

/-! ## `claim:degen` on the localized segmented leaf -/

section Division

variable {K : Type u} [CommSemiring K]
variable {A : Leg → Type w} {B : Leg → Type x}
variable [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]
variable [∀ c, Fintype (B c)] [∀ c, DecidableEq (B c)]
variable {V : ∀ c, A c → Type (max u v)}
variable [∀ c a, AddCommMonoid (V c a)] [∀ c a, Module K (V c a)]
variable {M : ℕ}

omit [∀ c, Fintype (B c)] [∀ c, DecidableEq (B c)] in
/-- **`[duan2023faster]`'s `claim:degen` on the localized segmented leaf, binary form.**

The leaf over `n + p + 2` positions restricts onto the external product of the two regional
leaves, provided

* the parent coarse target is the concatenation of the two regional coarse targets, and
* segment by segment, the parent's prescribed type is the sum of the two regional types.

Every region carries the parent segmentation restricted to it, so the two factors are again
localized segmented leaves of the *same* ambient partition --- no second object is introduced.
The proof is `Tensor.Restricts.restrictedSplittingPower_binaryDivision`
(`MatrixMultiplication/RestrictedSplittingPower.lean:250`) line for line, with the pooled keep
predicate replaced by `segmentedLocalizedKeep` and its legality step by
`segmentedLocalizedKeep_append`; the identification of the regionwise selection with the external
product is unchanged, being `PartitionedTensor.appendPositiveWordPartitions_select` together with
`PartitionedTensor.appendPositiveWordPartitions_positivePowers`. -/
theorem Tensor.Restricts.segmentedLocalizedSplittingPower_binaryDivision
    (P : PartitionedTensor (K := K) (A := A) V) (f : ∀ c, A c → B c) {n p : ℕ}
    (seg : Fin (n + p + 1 + 1) → Fin M)
    (parent left right : SegmentedSplitRestriction A M)
    (hsum : ∀ c t α, parent c t = some α →
      ∃ β γ, left c t = some β ∧ right c t = some γ ∧ α = β + γ)
    (target : BlockAddress (fun c ↦ PositiveWord (B c) (n + p + 1)))
    (targetLeft : BlockAddress (fun c ↦ PositiveWord (B c) n))
    (targetRight : BlockAddress (fun c ↦ PositiveWord (B c) p))
    (htarget : ∀ c, target c = positiveWordAppend (targetLeft c) p (targetRight c)) :
    Restricts
      (P.segmentedLocalizedSplittingPower f (n + p + 1) M seg parent target).realize
      (Tensor.external
        (P.segmentedLocalizedSplittingPower f n M (segmentationLeft n p seg) left
          targetLeft).realize
        (P.segmentedLocalizedSplittingPower f p M (segmentationRight n p seg) right
          targetRight).realize) := by
  classical
  set leftKeep : ∀ c, PositiveWord (A c) n → Prop :=
    segmentedLocalizedKeep f (segmentationLeft n p seg) left targetLeft with hleftKeep
  set rightKeep : ∀ c, PositiveWord (A c) p → Prop :=
    segmentedLocalizedKeep f (segmentationRight n p seg) right targetRight with hrightKeep
  set segmentKeep : ∀ c, PositiveWord (A c) (n + p + 1) → Prop :=
    fun c word ↦
      leftKeep c ((positiveWordAppendEquiv (A c) n p).symm word).1 ∧
      rightKeep c ((positiveWordAppendEquiv (A c) n p).symm word).2 with hsegmentKeep
  set parentSelected :=
    P.segmentedLocalizedSplittingPower f (n + p + 1) M seg parent target with hparentSelected
  set leftSelected :=
    P.segmentedLocalizedSplittingPower f n M (segmentationLeft n p seg) left targetLeft
      with hleftSelected
  set rightSelected :=
    P.segmentedLocalizedSplittingPower f p M (segmentationRight n p seg) right targetRight
      with hrightSelected
  set segmentSelected := (P.positivePower (n + p + 1)).select segmentKeep with hsegmentSelected
  have hsegment_parent : ∀ c word, segmentKeep c word →
      segmentedLocalizedKeep f seg parent target c word := by
    intro c word hword
    exact segmentedLocalizedKeep_append f seg hsum target targetLeft targetRight htarget c word
      hword.1 hword.2
  have hparent_select : parentSelected.select segmentKeep = segmentSelected := by
    apply PartitionedTensor.ext
    · apply Finset.ext
      intro address
      rw [PartitionedTensor.mem_select_support, hparentSelected,
        PartitionedTensor.segmentedLocalizedSplittingPower,
        PartitionedTensor.mem_select_support, hsegmentSelected,
        PartitionedTensor.mem_select_support]
      constructor
      · rintro ⟨⟨hsupport, -⟩, hsegment⟩
        exact ⟨hsupport, hsegment⟩
      · rintro ⟨hsupport, hsegment⟩
        exact ⟨⟨hsupport, fun c ↦ hsegment_parent c (address c) (hsegment c)⟩, hsegment⟩
    · rfl
  have hparent_segment : Restricts parentSelected.realize segmentSelected.realize :=
    (Tensor.Restricts.partitionedSelect parentSelected segmentKeep).trans
      (Tensor.Restricts.of_eq (congrArg PartitionedTensor.realize hparent_select))
  have happend_selected :
      PartitionedTensor.appendPositiveWordPartitions leftSelected rightSelected =
        segmentSelected := by
    calc
      PartitionedTensor.appendPositiveWordPartitions leftSelected rightSelected =
          (PartitionedTensor.appendPositiveWordPartitions
            (P.positivePower n) (P.positivePower p)).select segmentKeep :=
        PartitionedTensor.appendPositiveWordPartitions_select
          (P.positivePower n) (P.positivePower p) leftKeep rightKeep
      _ = segmentSelected := by
        rw [P.appendPositiveWordPartitions_positivePowers n p]
  have hexternal_append :
      Isomorphic (Tensor.external leftSelected.realize rightSelected.realize)
        (PartitionedTensor.appendPositiveWordPartitions leftSelected rightSelected).realize :=
    (Tensor.Isomorphic.partitionedExternal leftSelected rightSelected).trans
      (Tensor.Isomorphic.partitionedReindex
        (leftSelected.external rightSelected)
        (fun c ↦ positiveWordAppendEquiv (A c) n p)
        (positivePowerBlockAppendEquivAt (K := K) (V := V) n p))
  refine hparent_segment.trans ?_
  have hsegment_append :
      Isomorphic segmentSelected.realize
        (PartitionedTensor.appendPositiveWordPartitions leftSelected rightSelected).realize := by
    rw [happend_selected]
    exact Tensor.Isomorphic.refl _
  exact (hsegment_append.trans hexternal_append.symm).restricts

end Division

end AlgebraicComplexity
