/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithMixedPowerType
import AlgebraicComplexity.Examples.CoppersmithWinogradRectangularHashing

/-!
# Hashing extraction for Coppersmith's mixed `CW_7`/`CW_6` power

This module is stage 2 of Coppersmith's [Cop97] `α > 0.294`: it hashes the mixed power of
`Examples/CoppersmithMixedPowerType.lean` and delivers the extraction predicate
`RectangularScheduleExtraction` of `MatrixMultiplication/RectangularSchedule.lean`, from which the
schedule produces the rate and master inequalities with no further work.

## The obstruction, and why it dissolves

Stage 1 expected the hard part to be the *pruning* step of [Cop97, §5, p. 47] over a two-region
position set, and predicted a wide refactor of the zeroing layer, whose lemmas are phrased for
block addresses that are words over one alphabet while a mixed address is a *pair* of words.

Neither refactor is needed, and no lemma of `MatrixMultiplication/PartitionedPowerHashing.lean`
or of the zeroing layer changes.  The reason is that the two halves of Coppersmith's construction
share their block-address alphabet: `cwPartitionedTensor K 7` and `cwPartitionedTensor K 6` have
the *same* `Leg → Type` of block labels (`CWBlock`) and the *same* support `cwBlockSupport`; only
the block *spaces* `CWPartitionBlockSpace K q` differ, and the hashing interface is already
completely generic in those.  Concretely:

* `PartitionHashEncoding` is a structure on a support `Finset (BlockAddress A)`, carrying an
  injective field encoding of `A c` and a constant-sum legality condition.  Nothing in it mentions
  a tensor, so `cwPartitionHashEncoding` serves the mixed power verbatim.
* `Tensor.Restricts.modeledTargets_to_legwiseIsolatedIndexedDirectSum` -- the entire zeroing and
  pruning pass -- consumes an *arbitrary* `PartitionedTensor` whose block index is
  `fun c ↦ PositiveWord (A c) n` and whose block spaces `V : ∀ c, PositiveWord (A c) n → Type _`
  are arbitrary, subject only to `P.support = H.modeledAddresses n (H.legalTargets n words)`.  It
  never sees a tensor power.

So the only thing to supply is a *presentation* of the mixed power as such a partitioned tensor.
That is `cwMixedAppendPower`: reindex `cwMixedPower` along `positiveWordAppendEquiv CWBlock n₇ n₆`,
turning the pair-of-words block address `ProductBlockIndex` into a genuine word of length
`(n₇ + 1) + (n₆ + 1)` over `CWBlock`.  The reindexing is by an equivalence and transports every
block space unchanged, so it is faithful: `Isomorphic.partitionedReindex` identifies the two
realizations, and `positiveWordAppendEquiv` is a bijection, so no address is created, merged or
lost.  After it, every existing zeroing lemma applies unchanged, and the "duplicate pruning over
pairs of words" of [Cop97, p. 47] is literally the single-alphabet pruning already formalized.

The real content of stage 2 is therefore not the zeroing layer but the **competitor count**.
`card_legFiber_legalTargets_le_card_typedWordMapFiber` bounds a hashing leg fiber by the fiber of
one *joint* multiplicity type; a concatenated mixed word does have a joint type on the common
alphabet (the sum of the two halves' profiles), but that type also admits words that trade letters
between the two halves, and the resulting bound is exponentially too weak.  What is needed instead
is the *positional* split: the exact equality
`PartitionHashEncoding.card_legFiber_legalTargets_eq_card_sourceWordLegFiber` -- already public and
already stated for an arbitrary source-word family -- followed by
`card_sourceWordLegFiber_cwMixedTypeAppendWords`, which factorizes the source-word leg fiber of a
concatenated family into the product of the two halves' leg fibers.  That product is
`cwRectLegTypedFiber ... * cwRectLegTypedFiber ...`, i.e. exactly the count that stage 1 recorded
as `card_cwMixedTypedFiber`.

## Main definitions and results

* `cwMixedTypeAppendWords`, `card_cwMixedTypeAppendWords` -- the concatenated mixed word family
  and its cardinality, a product of two `cwRectTypeWords` counts;
* `cwMixedKeepBlock`, `mem_cwMixedTypeAppendWords_iff_keepBlocks` -- the leg-local selection
  predicate and the proof that its conjunction over the three legs is exactly the mixed type
  class, one half at a time;
* `cwMixedAppendPower`, `cwMixedAppendPower_support`,
  `cwMixedAppendPower_constituent_restricts_rectangular` -- the word-addressed presentation of the
  mixed power, its support (which is that of a *single* `q₇` power, because both halves share
  `cwBlockSupport`), and the fact that every selected constituent restricts to
  `⟨q₇^{b₇}q₆^{b₆}, q₇^{b₇}q₆^{b₆}, q₇^{a₇}q₆^{a₆}⟩`;
* `card_sourceWordLegFiber_cwMixedTypeAppendWords`, `cwMixedTypedFiberBound`,
  `card_cwMixedTypeAppendTarget_legFiber_le`, `cwMixedType_competitorQuarter_of_fieldCard` -- the
  positional split of the competitor count, the resulting uniform bound, and the field-size
  condition of the one-pass isolation theorem.

The finite extraction, the schedule input `cwMixed_scheduleExtraction`, and the rate and master
inequalities are assembled from these in `Examples/CoppersmithMixedPowerRate.lean`.

## References

* [Cop97] D. Coppersmith, *Rectangular matrix multiplication revisited*, J. Complexity **13**
  (1997), 42--49; Sections 4--5.
* [HP98] X. Huang and V. Y. Pan, *Fast rectangular matrix multiplication and applications*,
  J. Complexity **14** (1998), 257--299, Sections 5--7.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor

universe u

/-! ## Concatenation of positive words -/

theorem positiveWordAppendEquiv_symm_append {I : Type*} (n m : ℕ)
    (x : PositiveWord I n) (y : PositiveWord I m) :
    (positiveWordAppendEquiv I n m).symm (positiveWordAppend x m y) = (x, y) := by
  rw [← positiveWordAppendEquiv_apply, Equiv.symm_apply_apply]

theorem positiveWordAppend_symm_fst_snd {I : Type*} (n m : ℕ)
    (w : PositiveWord I (n + m + 1)) :
    positiveWordAppend ((positiveWordAppendEquiv I n m).symm w).1 m
        ((positiveWordAppendEquiv I n m).symm w).2 = w := by
  rw [← positiveWordAppendEquiv_apply]
  exact (positiveWordAppendEquiv I n m).apply_symm_apply w

/-! ## The concatenated mixed word family -/

/-- The positive-word depth of a mixed power: the two halves occupy
`(a₇ + 2b₇ + 2e₇ + f₇) + (a₆ + 2b₆ + 2e₆ + f₆)` consecutive positions. -/
abbrev cwMixedDepth (a₇ b₇ e₇ f₇ a₆ b₆ e₆ f₆ : ℕ) : ℕ :=
  cwRectDepth a₇ b₇ e₇ f₇ + cwRectDepth a₆ b₆ e₆ f₆ + 1

theorem cwMixedDepth_add_one {a₇ b₇ e₇ f₇ a₆ b₆ e₆ f₆ : ℕ}
    (h₇ : 0 < a₇ + 2 * b₇ + 2 * e₇ + f₇) (h₆ : 0 < a₆ + 2 * b₆ + 2 * e₆ + f₆) :
    cwMixedDepth a₇ b₇ e₇ f₇ a₆ b₆ e₆ f₆ + 1 =
      (a₇ + 2 * b₇ + 2 * e₇ + f₇) + (a₆ + 2 * b₆ + 2 * e₆ + f₆) := by
  have h1 := cwRectDepth_add_one h₇
  have h2 := cwRectDepth_add_one h₆
  simp only [cwMixedDepth]
  omega

/-- **The mixed word family, as words over one alphabet.**  A mixed address is a *pair* of
`cwBlockSupport` words; concatenating the pair along `positiveWordAppendEquiv` presents it as one
word of the total length, which is the form every zeroing and hashing lemma consumes.
Concatenation is an equivalence, so the presentation is faithful. -/
noncomputable def cwMixedTypeAppendWords (a₇ b₇ e₇ f₇ a₆ b₆ e₆ f₆ : ℕ) :
    Finset (PositiveWord cwBlockSupport (cwMixedDepth a₇ b₇ e₇ f₇ a₆ b₆ e₆ f₆)) :=
  (cwRectTypeWords a₇ b₇ e₇ f₇ ×ˢ cwRectTypeWords a₆ b₆ e₆ f₆).map
    (positiveWordAppendEquiv cwBlockSupport
      (cwRectDepth a₇ b₇ e₇ f₇) (cwRectDepth a₆ b₆ e₆ f₆)).toEmbedding

theorem mem_cwMixedTypeAppendWords {a₇ b₇ e₇ f₇ a₆ b₆ e₆ f₆ : ℕ}
    (w : PositiveWord cwBlockSupport (cwMixedDepth a₇ b₇ e₇ f₇ a₆ b₆ e₆ f₆)) :
    w ∈ cwMixedTypeAppendWords a₇ b₇ e₇ f₇ a₆ b₆ e₆ f₆ ↔
      ((positiveWordAppendEquiv cwBlockSupport
            (cwRectDepth a₇ b₇ e₇ f₇) (cwRectDepth a₆ b₆ e₆ f₆)).symm w).1 ∈
          cwRectTypeWords a₇ b₇ e₇ f₇ ∧
        ((positiveWordAppendEquiv cwBlockSupport
            (cwRectDepth a₇ b₇ e₇ f₇) (cwRectDepth a₆ b₆ e₆ f₆)).symm w).2 ∈
          cwRectTypeWords a₆ b₆ e₆ f₆ := by
  rw [cwMixedTypeAppendWords, Finset.mem_map_equiv, Finset.mem_product]

/-- **The mixed word count is a product of two single-`q` counts.**  This is the concatenated form
of `card_cwMixedTypeWords`, i.e. Coppersmith's `(9a; a, 7a, a)·(8b; b, 6b, b)`. -/
@[simp] theorem card_cwMixedTypeAppendWords (a₇ b₇ e₇ f₇ a₆ b₆ e₆ f₆ : ℕ) :
    (cwMixedTypeAppendWords a₇ b₇ e₇ f₇ a₆ b₆ e₆ f₆).card =
      (cwRectTypeWords a₇ b₇ e₇ f₇).card * (cwRectTypeWords a₆ b₆ e₆ f₆).card := by
  rw [cwMixedTypeAppendWords, Finset.card_map, Finset.card_product]

/-- **Faithfulness to stage 1.**  Concatenation does not change the number of selected addresses:
the concatenated family has exactly as many elements as the pair-of-words family
`cwMixedTypeWords` of `Examples/CoppersmithMixedPowerType.lean`, namely
`Nat.multinomial g₇ · Nat.multinomial g₆`. -/
theorem card_cwMixedTypeAppendWords_eq_card_cwMixedTypeWords {a₇ b₇ e₇ f₇ a₆ b₆ e₆ f₆ : ℕ}
    (h₇ : 0 < a₇ + 2 * b₇ + 2 * e₇ + f₇) (h₆ : 0 < a₆ + 2 * b₆ + 2 * e₆ + f₆) :
    (cwMixedTypeAppendWords a₇ b₇ e₇ f₇ a₆ b₆ e₆ f₆).card =
      (cwMixedTypeWords (cwRectType a₇ b₇ e₇ f₇) (cwRectType a₆ b₆ e₆ f₆)
        (a₇ + 2 * b₇ + 2 * e₇ + f₇) (a₆ + 2 * b₆ + 2 * e₆ + f₆)).card := by
  rw [card_cwMixedTypeAppendWords, card_cwRectTypeWords h₇, card_cwRectTypeWords h₆,
    card_cwMixedTypeWords (sum_cwRectType a₇ b₇ e₇ f₇) (sum_cwRectType a₆ b₆ e₆ f₆)]

theorem cwMixedTypeAppendWords_nonempty {a₇ b₇ e₇ f₇ a₆ b₆ e₆ f₆ : ℕ}
    (h₇ : 0 < a₇ + 2 * b₇ + 2 * e₇ + f₇) (h₆ : 0 < a₆ + 2 * b₆ + 2 * e₆ + f₆) :
    (cwMixedTypeAppendWords a₇ b₇ e₇ f₇ a₆ b₆ e₆ f₆).Nonempty := by
  rw [← Finset.card_pos, card_cwMixedTypeAppendWords]
  exact Nat.mul_pos
    (Finset.card_pos.mpr (cwRectTypeWords_nonempty h₇))
    (Finset.card_pos.mpr (cwRectTypeWords_nonempty h₆))

/-! ## The positional split of a concatenated leg word -/

/-- Transposing a concatenated support word to a leg concatenates the two transposed halves. -/
theorem supportWordAddress_positiveWordAppend (d₇ d₆ : ℕ)
    (w₇ : PositiveWord cwBlockSupport d₇) (w₆ : PositiveWord cwBlockSupport d₆) (c : Leg) :
    PartitionHashEncoding.supportWordAddress
        (A := fun _ : Leg ↦ CWBlock) (support := cwBlockSupport) (d₇ + d₆ + 1)
        (positiveWordAppend w₇ d₆ w₆) c =
      positiveWordAppend
        (PartitionHashEncoding.supportWordAddress
          (A := fun _ : Leg ↦ CWBlock) (support := cwBlockSupport) d₇ w₇ c) d₆
        (PartitionHashEncoding.supportWordAddress
          (A := fun _ : Leg ↦ CWBlock) (support := cwBlockSupport) d₆ w₆ c) :=
  congrFun (positiveSupportWordBlockAddress_append cwBlockSupport w₇ w₆) c

/-- **The positional split of a leg-word equation.**  A concatenated support word has a prescribed
leg word exactly when each half has the corresponding half of it.  This is what makes the mixed
competitor count factorize, and it is the step that the joint-multiplicity bound
`card_legFiber_legalTargets_le_card_typedWordMapFiber` cannot see. -/
theorem supportWordAddress_append_eq_iff (d₇ d₆ : ℕ)
    (w₇ : PositiveWord cwBlockSupport d₇) (w₆ : PositiveWord cwBlockSupport d₆) (c : Leg)
    (t : PositiveWord CWBlock (d₇ + d₆ + 1)) :
    PartitionHashEncoding.supportWordAddress
        (A := fun _ : Leg ↦ CWBlock) (support := cwBlockSupport) (d₇ + d₆ + 1)
        (positiveWordAppend w₇ d₆ w₆) c = t ↔
      (PartitionHashEncoding.supportWordAddress
            (A := fun _ : Leg ↦ CWBlock) (support := cwBlockSupport) d₇ w₇ c =
          ((positiveWordAppendEquiv CWBlock d₇ d₆).symm t).1 ∧
        PartitionHashEncoding.supportWordAddress
            (A := fun _ : Leg ↦ CWBlock) (support := cwBlockSupport) d₆ w₆ c =
          ((positiveWordAppendEquiv CWBlock d₇ d₆).symm t).2) := by
  rw [supportWordAddress_positiveWordAppend]
  constructor
  · rintro rfl
    rw [positiveWordAppendEquiv_symm_append]
    exact ⟨rfl, rfl⟩
  · rintro ⟨h₇, h₆⟩
    rw [h₇, h₆, positiveWordAppend_symm_fst_snd]

/-! ## Leg-local selection at the mixed type -/

/-- Keep the leg words whose two halves have the two halves' rectangular leg marginals.  Unlike
the single-`q` predicate this is not a condition on the multiplicity type of the whole leg word:
the two halves are constrained separately, which is exactly Coppersmith's independent selection
on the `9a` and the `8b` positions. -/
noncomputable def cwMixedKeepBlock (a₇ b₇ e₇ f₇ a₆ b₆ e₆ f₆ : ℕ) (c : Leg)
    (word : PositiveWord CWBlock (cwMixedDepth a₇ b₇ e₇ f₇ a₆ b₆ e₆ f₆)) : Prop :=
  cwRectKeepBlock a₇ b₇ e₇ f₇ c
      ((positiveWordAppendEquiv CWBlock
        (cwRectDepth a₇ b₇ e₇ f₇) (cwRectDepth a₆ b₆ e₆ f₆)).symm word).1 ∧
    cwRectKeepBlock a₆ b₆ e₆ f₆ c
      ((positiveWordAppendEquiv CWBlock
        (cwRectDepth a₇ b₇ e₇ f₇) (cwRectDepth a₆ b₆ e₆ f₆)).symm word).2

noncomputable instance cwMixedKeepBlock_decidable (a₇ b₇ e₇ f₇ a₆ b₆ e₆ f₆ : ℕ) (c : Leg)
    (word : PositiveWord CWBlock (cwMixedDepth a₇ b₇ e₇ f₇ a₆ b₆ e₆ f₆)) :
    Decidable (cwMixedKeepBlock a₇ b₇ e₇ f₇ a₆ b₆ e₆ f₆ c word) := by
  classical
  unfold cwMixedKeepBlock
  infer_instance

/-- **The mixed type class is the conjunction of six leg-local marginal conditions**, three per
half.  This is the mixed form of `mem_cwRectTypeWords_iff_keepBlocks`, and it is what lets the
generic type-selection bridge `filter_modeledLegalTargets_eq_of_mem_iff` apply unchanged. -/
theorem mem_cwMixedTypeAppendWords_iff_keepBlocks (a₇ b₇ e₇ f₇ a₆ b₆ e₆ f₆ : ℕ)
    (w : PositiveWord cwBlockSupport (cwMixedDepth a₇ b₇ e₇ f₇ a₆ b₆ e₆ f₆)) :
    w ∈ cwMixedTypeAppendWords a₇ b₇ e₇ f₇ a₆ b₆ e₆ f₆ ↔
      ∀ c, cwMixedKeepBlock a₇ b₇ e₇ f₇ a₆ b₆ e₆ f₆ c
        (PartitionHashEncoding.supportWordAddress
          (A := fun _ : Leg ↦ CWBlock) (support := cwBlockSupport)
          (cwMixedDepth a₇ b₇ e₇ f₇ a₆ b₆ e₆ f₆) w c) := by
  classical
  set d₇ := cwRectDepth a₇ b₇ e₇ f₇ with hd₇
  set d₆ := cwRectDepth a₆ b₆ e₆ f₆ with hd₆
  set w₇ := ((positiveWordAppendEquiv cwBlockSupport d₇ d₆).symm w).1 with hw₇
  set w₆ := ((positiveWordAppendEquiv cwBlockSupport d₇ d₆).symm w).2 with hw₆
  have hsplit : positiveWordAppend w₇ d₆ w₆ = w :=
    positiveWordAppend_symm_fst_snd d₇ d₆ w
  have hleg : ∀ c, PartitionHashEncoding.supportWordAddress
      (A := fun _ : Leg ↦ CWBlock) (support := cwBlockSupport) (d₇ + d₆ + 1) w c =
      positiveWordAppend
        (PartitionHashEncoding.supportWordAddress
          (A := fun _ : Leg ↦ CWBlock) (support := cwBlockSupport) d₇ w₇ c) d₆
        (PartitionHashEncoding.supportWordAddress
          (A := fun _ : Leg ↦ CWBlock) (support := cwBlockSupport) d₆ w₆ c) := by
    intro c
    rw [← hsplit]
    exact supportWordAddress_positiveWordAppend d₇ d₆ w₇ w₆ c
  have hkeep : ∀ c, cwMixedKeepBlock a₇ b₇ e₇ f₇ a₆ b₆ e₆ f₆ c
      (PartitionHashEncoding.supportWordAddress
        (A := fun _ : Leg ↦ CWBlock) (support := cwBlockSupport) (d₇ + d₆ + 1) w c) ↔
      (cwRectKeepBlock a₇ b₇ e₇ f₇ c
          (PartitionHashEncoding.supportWordAddress
            (A := fun _ : Leg ↦ CWBlock) (support := cwBlockSupport) d₇ w₇ c) ∧
        cwRectKeepBlock a₆ b₆ e₆ f₆ c
          (PartitionHashEncoding.supportWordAddress
            (A := fun _ : Leg ↦ CWBlock) (support := cwBlockSupport) d₆ w₆ c)) := by
    intro c
    rw [cwMixedKeepBlock, hleg c, positiveWordAppendEquiv_symm_append]
  rw [mem_cwMixedTypeAppendWords, ← hw₇, ← hw₆,
    mem_cwRectTypeWords_iff_keepBlocks, mem_cwRectTypeWords_iff_keepBlocks]
  constructor
  · rintro ⟨h₇, h₆⟩ c
    exact (hkeep c).mpr ⟨h₇ c, h₆ c⟩
  · intro h
    exact ⟨fun c ↦ ((hkeep c).mp (h c)).1, fun c ↦ ((hkeep c).mp (h c)).2⟩

/-! ## The mixed power, presented over a single alphabet -/

section AppendPower

variable (K : Type u) [CommRing K]

/-- **The mixed power with concatenated block addresses.**  Reindexing `cwMixedPower` along
`positiveWordAppendEquiv` replaces the pair-of-words block address by a single word of the total
length, without touching a constituent: the block spaces are transported by the identity.  This is
the presentation on which the existing hashing and zeroing layer operates verbatim. -/
noncomputable def cwMixedAppendPower (q₇ q₆ n₇ n₆ : ℕ) :
    PartitionedTensor (K := K) (A := fun _ : Leg ↦ PositiveWord CWBlock (n₇ + n₆ + 1))
      (fun c w ↦ ProductBlockSpace K
        (PositivePowerBlockSpace K (CWPartitionBlockSpace K q₇) n₇)
        (PositivePowerBlockSpace K (CWPartitionBlockSpace K q₆) n₆) c
        ((positiveWordAppendEquiv CWBlock n₇ n₆).symm w)) :=
  (cwMixedPower K q₇ q₆ n₇ n₆).reindex
    (fun _ ↦ positiveWordAppendEquiv CWBlock n₇ n₆)
    (fun _ _ ↦ LinearEquiv.refl K _)

/-- Constituents are unchanged by the concatenation of block addresses. -/
theorem cwMixedAppendPower_constituent (q₇ q₆ n₇ n₆ : ℕ)
    (address : BlockAddress (fun _ : Leg ↦ PositiveWord CWBlock (n₇ + n₆ + 1))) :
    (cwMixedAppendPower K q₇ q₆ n₇ n₆).constituent address =
      (cwMixedPower K q₇ q₆ n₇ n₆).constituent
        (fun c ↦ (positiveWordAppendEquiv CWBlock n₇ n₆).symm (address c)) := by
  change Tensor.map (fun _ ↦ (LinearEquiv.refl K _).toLinearMap) _ = _
  exact LinearMap.congr_fun Tensor.map_id _

/-- **The concatenated mixed support is the support of a single `q₇` power.**  Both halves of the
mixed power carry the same block-address support `cwBlockSupport`; the block *spaces* differ but
supports do not, so concatenating the two regional word supports produces exactly the complete
word support of one homogeneous power.  This is the identity that lets `cwPartitionHashEncoding`
and `positivePower_support_eq_modeledLegalTargets` apply to the mixed power unchanged. -/
theorem cwMixedAppendPower_support (q₇ q₆ n₇ n₆ : ℕ) :
    (cwMixedAppendPower K q₇ q₆ n₇ n₆).support =
      ((cwPartitionedTensor K q₇).positivePower (n₇ + n₆ + 1)).support := by
  classical
  have hsupp : ((cwPartitionedTensor K q₆).positivePower n₆).support =
      ((cwPartitionedTensor K q₇).positivePower n₆).support := by
    rw [PartitionedTensor.positivePower_support_eq_map_positiveSupportWords,
      PartitionedTensor.positivePower_support_eq_map_positiveSupportWords]
    rfl
  have hext : (cwMixedPower K q₇ q₆ n₇ n₆).support =
      (((cwPartitionedTensor K q₇).positivePower n₇).external
        ((cwPartitionedTensor K q₇).positivePower n₆)).support := by
    ext address
    rw [mem_cwMixedPower_support, PartitionedTensor.mem_external_support, hsupp]
  change (cwMixedPower K q₇ q₆ n₇ n₆).support.map
    (positiveWordBlockAppendEquiv (fun _ : Leg ↦ CWBlock) n₇ n₆).toEmbedding = _
  rw [hext]
  exact PartitionedTensor.positivePower_external_support_map_append
    (cwPartitionedTensor K q₇) n₇ n₆

/-- **Every mixed-type constituent is the same rectangular product**
`⟨q₇^{b₇}q₆^{b₆}, q₇^{b₇}q₆^{b₆}, q₇^{a₇}q₆^{a₆}⟩`.  At Coppersmith's parameters this is
`⟨M, M, P⟩` with `M = 7^{7a/2}6^{3b}` and `P = 7^{a-2s}6^{b-2t}` [Cop97, pp. 45, 47]. -/
theorem cwMixedAppendPower_constituent_restricts_rectangular
    (q₇ q₆ a₇ b₇ e₇ f₇ a₆ b₆ e₆ f₆ : ℕ)
    {w : PositiveWord cwBlockSupport (cwMixedDepth a₇ b₇ e₇ f₇ a₆ b₆ e₆ f₆)}
    (hw : w ∈ cwMixedTypeAppendWords a₇ b₇ e₇ f₇ a₆ b₆ e₆ f₆) :
    Restricts
      ((cwMixedAppendPower K q₇ q₆
          (cwRectDepth a₇ b₇ e₇ f₇) (cwRectDepth a₆ b₆ e₆ f₆)).constituent
        (positiveSupportWordBlockAddress cwBlockSupport
          (cwMixedDepth a₇ b₇ e₇ f₇ a₆ b₆ e₆ f₆) w))
      (matrixMultiplication (K := K)
        (q₇ ^ b₇ * q₆ ^ b₆) (q₇ ^ b₇ * q₆ ^ b₆) (q₇ ^ a₇ * q₆ ^ a₆)) := by
  classical
  set d₇ := cwRectDepth a₇ b₇ e₇ f₇ with hd₇
  set d₆ := cwRectDepth a₆ b₆ e₆ f₆ with hd₆
  set w₇ := ((positiveWordAppendEquiv cwBlockSupport d₇ d₆).symm w).1 with hw₇def
  set w₆ := ((positiveWordAppendEquiv cwBlockSupport d₇ d₆).symm w).2 with hw₆def
  obtain ⟨hmem₇, hmem₆⟩ := (mem_cwMixedTypeAppendWords w).mp hw
  have hsplit : positiveWordAppend w₇ d₆ w₆ = w :=
    positiveWordAppend_symm_fst_snd d₇ d₆ w
  -- the concatenated address splits into the two regional addresses
  have haddress : (fun c ↦ (positiveWordAppendEquiv CWBlock d₇ d₆).symm
        (positiveSupportWordBlockAddress cwBlockSupport (d₇ + d₆ + 1) w c)) =
      (fun c ↦ (positiveSupportWordBlockAddress cwBlockSupport d₇ w₇ c,
        positiveSupportWordBlockAddress cwBlockSupport d₆ w₆ c)) := by
    funext c
    have h := supportWordAddress_positiveWordAppend d₇ d₆ w₇ w₆ c
    rw [hsplit] at h
    change (positiveWordAppendEquiv CWBlock d₇ d₆).symm
      (positiveSupportWordBlockAddress cwBlockSupport (d₇ + d₆ + 1) w c) = _
    rw [show positiveSupportWordBlockAddress cwBlockSupport (d₇ + d₆ + 1) w c =
        positiveWordAppend (positiveSupportWordBlockAddress cwBlockSupport d₇ w₇ c) d₆
          (positiveSupportWordBlockAddress cwBlockSupport d₆ w₆ c) from h,
      positiveWordAppendEquiv_symm_append]
  rw [cwMixedAppendPower_constituent]
  -- the two regional constituents
  have hr₇ := Tensor.Restricts.positivePower_constituent_matrixMultiplication
    (cwPartitionedTensor K q₇) (cwTensorConstituentM K q₇) (cwTensorConstituentN K q₇)
    (cwTensorConstituentP K q₇) (cwSupportedConstituent_restricts K q₇) d₇ w₇
  have hr₆ := Tensor.Restricts.positivePower_constituent_matrixMultiplication
    (cwPartitionedTensor K q₆) (cwTensorConstituentM K q₆) (cwTensorConstituentN K q₆)
    (cwTensorConstituentP K q₆) (cwSupportedConstituent_restricts K q₆) d₆ w₆
  rw [cwRect_positiveWordProduct_m K q₇ a₇ b₇ e₇ f₇ d₇ hmem₇,
    cwRect_positiveWordProduct_n K q₇ a₇ b₇ e₇ f₇ d₇ hmem₇,
    cwRect_positiveWordProduct_p K q₇ a₇ b₇ e₇ f₇ d₇ hmem₇] at hr₇
  rw [cwRect_positiveWordProduct_m K q₆ a₆ b₆ e₆ f₆ d₆ hmem₆,
    cwRect_positiveWordProduct_n K q₆ a₆ b₆ e₆ f₆ d₆ hmem₆,
    cwRect_positiveWordProduct_p K q₆ a₆ b₆ e₆ f₆ d₆ hmem₆] at hr₆
  -- the block address of the constituent is type dependent, so it is substituted rather than
  -- rewritten
  have key : ∀ addr : BlockAddress (ProductBlockIndex
        (fun _ : Leg ↦ PositiveWord CWBlock d₇) (fun _ : Leg ↦ PositiveWord CWBlock d₆)),
      addr = (fun c ↦ (positiveSupportWordBlockAddress cwBlockSupport d₇ w₇ c,
        positiveSupportWordBlockAddress cwBlockSupport d₆ w₆ c)) →
      Restricts ((cwMixedPower K q₇ q₆ d₇ d₆).constituent addr)
        (matrixMultiplication (K := K)
          (q₇ ^ b₇ * q₆ ^ b₆) (q₇ ^ b₇ * q₆ ^ b₆) (q₇ ^ a₇ * q₆ ^ a₆)) := by
    rintro addr rfl
    exact (hr₇.external hr₆).trans
      (Isomorphic.matrixMultiplication_external (K := K) _ _ _ _ _ _).restricts
  exact key _ haddress

end AppendPower

/-! ## Type selection on the concatenated power -/

section TypeSelection

variable (K : Type u) [CommRing K]

/-- The mixed-type subpartition of the concatenated mixed power. -/
noncomputable def cwMixedTypeAppendPower (q₇ q₆ a₇ b₇ e₇ f₇ a₆ b₆ e₆ f₆ : ℕ) :
    PartitionedTensor (K := K)
      (A := fun _ : Leg ↦ PositiveWord CWBlock (cwMixedDepth a₇ b₇ e₇ f₇ a₆ b₆ e₆ f₆))
      (fun c w ↦ ProductBlockSpace K
        (PositivePowerBlockSpace K (CWPartitionBlockSpace K q₇) (cwRectDepth a₇ b₇ e₇ f₇))
        (PositivePowerBlockSpace K (CWPartitionBlockSpace K q₆) (cwRectDepth a₆ b₆ e₆ f₆)) c
        ((positiveWordAppendEquiv CWBlock
          (cwRectDepth a₇ b₇ e₇ f₇) (cwRectDepth a₆ b₆ e₆ f₆)).symm w)) :=
  (cwMixedAppendPower K q₇ q₆ (cwRectDepth a₇ b₇ e₇ f₇) (cwRectDepth a₆ b₆ e₆ f₆)).select
    (cwMixedKeepBlock a₇ b₇ e₇ f₇ a₆ b₆ e₆ f₆)

/-- Legal affine-hashing targets representing the mixed-type words. -/
noncomputable def cwMixedTypeAppendTargets
    {R : Type*} [Field R] [NeZero (2 : R)] (a₇ b₇ e₇ f₇ a₆ b₆ e₆ f₆ : ℕ) :
    Finset (ProgressionHash.LegalTriple R
      (Fin (cwMixedDepth a₇ b₇ e₇ f₇ a₆ b₆ e₆ f₆ + 1)) 2) :=
  (cwPartitionHashEncoding (R := R)).legalTargets
    (cwMixedDepth a₇ b₇ e₇ f₇ a₆ b₆ e₆ f₆) (cwMixedTypeAppendWords a₇ b₇ e₇ f₇ a₆ b₆ e₆ f₆)

@[simp] theorem card_cwMixedTypeAppendTargets
    {R : Type*} [Field R] [NeZero (2 : R)] (a₇ b₇ e₇ f₇ a₆ b₆ e₆ f₆ : ℕ) :
    (cwMixedTypeAppendTargets (R := R) a₇ b₇ e₇ f₇ a₆ b₆ e₆ f₆).card =
      (cwMixedTypeAppendWords a₇ b₇ e₇ f₇ a₆ b₆ e₆ f₆).card :=
  PartitionHashEncoding.card_legalTargets _ _ _

/-- The selected partition support is exactly the modeled mixed-type legal-target family. -/
theorem cwMixedTypeAppendPower_support
    {R : Type*} [Field R] [NeZero (2 : R)] (q₇ q₆ a₇ b₇ e₇ f₇ a₆ b₆ e₆ f₆ : ℕ) :
    (cwMixedTypeAppendPower K q₇ q₆ a₇ b₇ e₇ f₇ a₆ b₆ e₆ f₆).support =
      (cwPartitionHashEncoding (R := R)).modeledAddresses
        (cwMixedDepth a₇ b₇ e₇ f₇ a₆ b₆ e₆ f₆)
        (cwMixedTypeAppendTargets (R := R) a₇ b₇ e₇ f₇ a₆ b₆ e₆ f₆) := by
  classical
  unfold cwMixedTypeAppendPower cwMixedTypeAppendTargets
  change (cwMixedAppendPower K q₇ q₆ (cwRectDepth a₇ b₇ e₇ f₇)
      (cwRectDepth a₆ b₆ e₆ f₆)).support.filter
      (fun s ↦ ∀ c, cwMixedKeepBlock a₇ b₇ e₇ f₇ a₆ b₆ e₆ f₆ c (s c)) = _
  rw [cwMixedAppendPower_support,
    (cwPartitionHashEncoding (R := R)).positivePower_support_eq_modeledLegalTargets
      (cwPartitionedTensor K q₇) (cwMixedDepth a₇ b₇ e₇ f₇ a₆ b₆ e₆ f₆)]
  exact (cwPartitionHashEncoding (R := R)).filter_modeledLegalTargets_eq_of_mem_iff
    (cwMixedDepth a₇ b₇ e₇ f₇ a₆ b₆ e₆ f₆) (cwMixedTypeAppendWords a₇ b₇ e₇ f₇ a₆ b₆ e₆ f₆)
    (cwMixedKeepBlock a₇ b₇ e₇ f₇ a₆ b₆ e₆ f₆)
    (mem_cwMixedTypeAppendWords_iff_keepBlocks a₇ b₇ e₇ f₇ a₆ b₆ e₆ f₆)

end TypeSelection

/-! ## The competitor count, split by position -/

/-- The source-word leg fiber of a *concatenated* family is the product of the two halves' leg
fibers.  This is the sharp mixed competitor count; the joint-multiplicity bound of
`card_legFiber_legalTargets_le_card_typedWordMapFiber` would instead allow letters to migrate
between the two halves and is exponentially weaker. -/
theorem card_sourceWordLegFiber_cwMixedTypeAppendWords (a₇ b₇ e₇ f₇ a₆ b₆ e₆ f₆ : ℕ) (c : Leg)
    (t : PositiveWord CWBlock (cwMixedDepth a₇ b₇ e₇ f₇ a₆ b₆ e₆ f₆)) :
    (PartitionHashEncoding.sourceWordLegFiber
        (A := fun _ : Leg ↦ CWBlock) (support := cwBlockSupport)
        (cwMixedDepth a₇ b₇ e₇ f₇ a₆ b₆ e₆ f₆)
        (cwMixedTypeAppendWords a₇ b₇ e₇ f₇ a₆ b₆ e₆ f₆) c t).card =
      (PartitionHashEncoding.sourceWordLegFiber
          (A := fun _ : Leg ↦ CWBlock) (support := cwBlockSupport)
          (cwRectDepth a₇ b₇ e₇ f₇) (cwRectTypeWords a₇ b₇ e₇ f₇) c
          ((positiveWordAppendEquiv CWBlock
            (cwRectDepth a₇ b₇ e₇ f₇) (cwRectDepth a₆ b₆ e₆ f₆)).symm t).1).card *
        (PartitionHashEncoding.sourceWordLegFiber
          (A := fun _ : Leg ↦ CWBlock) (support := cwBlockSupport)
          (cwRectDepth a₆ b₆ e₆ f₆) (cwRectTypeWords a₆ b₆ e₆ f₆) c
          ((positiveWordAppendEquiv CWBlock
            (cwRectDepth a₇ b₇ e₇ f₇) (cwRectDepth a₆ b₆ e₆ f₆)).symm t).2).card := by
  classical
  set d₇ := cwRectDepth a₇ b₇ e₇ f₇ with hd₇
  set d₆ := cwRectDepth a₆ b₆ e₆ f₆ with hd₆
  have hset : PartitionHashEncoding.sourceWordLegFiber
      (A := fun _ : Leg ↦ CWBlock) (support := cwBlockSupport) (d₇ + d₆ + 1)
      (cwMixedTypeAppendWords a₇ b₇ e₇ f₇ a₆ b₆ e₆ f₆) c t =
      ((PartitionHashEncoding.sourceWordLegFiber
          (A := fun _ : Leg ↦ CWBlock) (support := cwBlockSupport)
          d₇ (cwRectTypeWords a₇ b₇ e₇ f₇) c
          ((positiveWordAppendEquiv CWBlock d₇ d₆).symm t).1) ×ˢ
        (PartitionHashEncoding.sourceWordLegFiber
          (A := fun _ : Leg ↦ CWBlock) (support := cwBlockSupport)
          d₆ (cwRectTypeWords a₆ b₆ e₆ f₆) c
          ((positiveWordAppendEquiv CWBlock d₇ d₆).symm t).2)).map
        (positiveWordAppendEquiv cwBlockSupport d₇ d₆).toEmbedding := by
    ext w
    have hsplit : positiveWordAppend
        ((positiveWordAppendEquiv cwBlockSupport d₇ d₆).symm w).1 d₆
        ((positiveWordAppendEquiv cwBlockSupport d₇ d₆).symm w).2 = w :=
      positiveWordAppend_symm_fst_snd d₇ d₆ w
    have hleg := supportWordAddress_append_eq_iff d₇ d₆
      ((positiveWordAppendEquiv cwBlockSupport d₇ d₆).symm w).1
      ((positiveWordAppendEquiv cwBlockSupport d₇ d₆).symm w).2 c t
    rw [hsplit] at hleg
    rw [PartitionHashEncoding.sourceWordLegFiber, Finset.mem_filter,
      mem_cwMixedTypeAppendWords, Finset.mem_map_equiv, Finset.mem_product,
      PartitionHashEncoding.sourceWordLegFiber, PartitionHashEncoding.sourceWordLegFiber,
      Finset.mem_filter, Finset.mem_filter, hleg]
    tauto
  rw [hset, Finset.card_map, Finset.card_product]

/-- The source-word leg fiber of a rectangular type class injects into the type-restricted word
map fiber, so `card_cwRectTypedWordMapFiber` bounds it. -/
theorem card_sourceWordLegFiber_cwRectTypeWords_le (a b e f : ℕ) (c : Leg)
    (t : PositiveWord CWBlock (cwRectDepth a b e f)) :
    (PartitionHashEncoding.sourceWordLegFiber
        (A := fun _ : Leg ↦ CWBlock) (support := cwBlockSupport)
        (cwRectDepth a b e f) (cwRectTypeWords a b e f) c t).card ≤
      (WordType.typedWordMapFiber (fun s : cwBlockSupport ↦ s.1 c) (cwRectType a b e f)
        (positiveWordEquiv CWBlock (cwRectDepth a b e f) t)).card := by
  classical
  refine Finset.card_le_card_of_injOn
    (fun word ↦ positiveWordEquiv cwBlockSupport (cwRectDepth a b e f) word) ?_ ?_
  · intro word hword
    simp only [Finset.mem_coe] at hword ⊢
    rw [PartitionHashEncoding.sourceWordLegFiber, Finset.mem_filter] at hword
    obtain ⟨hmem, htarget⟩ := hword
    rw [WordType.mem_typedWordMapFiber]
    refine ⟨mem_positiveTypeClass.mp hmem, ?_⟩
    have h := PartitionHashEncoding.positiveWordEquiv_supportWordAddress
      (A := fun _ : Leg ↦ CWBlock) (support := cwBlockSupport) (cwRectDepth a b e f) word c
    rw [htarget] at h
    exact h.symm
  · intro left _ right _ heq
    exact (positiveWordEquiv cwBlockSupport (cwRectDepth a b e f)).injective heq

/-- The uniform-over-legs mixed competitor bound: on each leg the mixed count is the *product* of
the two halves' counts (`card_cwMixedTypedFiber`), and the bound is their maximum. -/
def cwMixedTypedFiberBound (a₇ b₇ e₇ f₇ a₆ b₆ e₆ f₆ : ℕ) : ℕ :=
  max (cwRectLegTypedFiber a₇ b₇ e₇ f₇ .X * cwRectLegTypedFiber a₆ b₆ e₆ f₆ .X)
    (cwRectLegTypedFiber a₇ b₇ e₇ f₇ .Y * cwRectLegTypedFiber a₆ b₆ e₆ f₆ .Y)

theorem cwMixedTypedFiberBound_pos (a₇ b₇ e₇ f₇ a₆ b₆ e₆ f₆ : ℕ) :
    0 < cwMixedTypedFiberBound a₇ b₇ e₇ f₇ a₆ b₆ e₆ f₆ :=
  lt_of_lt_of_le
    (Nat.mul_pos (cwRectLegTypedFiber_pos a₇ b₇ e₇ f₇ .X)
      (cwRectLegTypedFiber_pos a₆ b₆ e₆ f₆ .X))
    (le_max_left _ _)

theorem cwMixedLegTypedFiber_le_bound (a₇ b₇ e₇ f₇ a₆ b₆ e₆ f₆ : ℕ) (c : Leg) :
    cwRectLegTypedFiber a₇ b₇ e₇ f₇ c * cwRectLegTypedFiber a₆ b₆ e₆ f₆ c ≤
      cwMixedTypedFiberBound a₇ b₇ e₇ f₇ a₆ b₆ e₆ f₆ := by
  cases c
  · exact le_max_left _ _
  · exact le_max_right _ _
  · exact le_max_right _ _

section Competitors

variable {R : Type*} [Field R] [NeZero (2 : R)]

/-- Every fixed-leg fiber of mixed-type hashing targets is bounded by the *product* of the two
halves' type-restricted competitor counts. -/
theorem card_cwMixedTypeAppendTarget_legFiber_le
    {a₇ b₇ e₇ f₇ a₆ b₆ e₆ f₆ : ℕ}
    (h₇ : 0 < a₇ + 2 * b₇ + 2 * e₇ + f₇) (h₆ : 0 < a₆ + 2 * b₆ + 2 * e₆ + f₆)
    {triple : ProgressionHash.LegalTriple R
      (Fin (cwMixedDepth a₇ b₇ e₇ f₇ a₆ b₆ e₆ f₆ + 1)) 2}
    (htriple : triple ∈ cwMixedTypeAppendTargets (R := R) a₇ b₇ e₇ f₇ a₆ b₆ e₆ f₆) (c : Leg) :
    (ProgressionHash.LegalTriple.legFiber
        (cwMixedTypeAppendTargets (R := R) a₇ b₇ e₇ f₇ a₆ b₆ e₆ f₆) triple c).card ≤
      cwMixedTypedFiberBound a₇ b₇ e₇ f₇ a₆ b₆ e₆ f₆ := by
  classical
  have htriple' : triple ∈ (cwPartitionHashEncoding (R := R)).legalTargets
      (cwMixedDepth a₇ b₇ e₇ f₇ a₆ b₆ e₆ f₆)
      (cwMixedTypeAppendWords a₇ b₇ e₇ f₇ a₆ b₆ e₆ f₆) := htriple
  -- the modeled leg word of a represented target is the transposed leg word of a selected word
  obtain ⟨source, hsourceMem, hmodeled⟩ :
      ∃ source ∈ cwMixedTypeAppendWords a₇ b₇ e₇ f₇ a₆ b₆ e₆ f₆,
        (cwPartitionHashEncoding (R := R)).modeledAddress
            (cwMixedDepth a₇ b₇ e₇ f₇ a₆ b₆ e₆ f₆) triple c =
          PartitionHashEncoding.supportWordAddress
            (A := fun _ : Leg ↦ CWBlock) (support := cwBlockSupport)
            (cwMixedDepth a₇ b₇ e₇ f₇ a₆ b₆ e₆ f₆) source c :=
    ⟨_, (cwPartitionHashEncoding (R := R)).sourceWordOfLegalTriple_mem_of_mem
      (cwMixedDepth a₇ b₇ e₇ f₇ a₆ b₆ e₆ f₆) (cwMixedTypeAppendWords a₇ b₇ e₇ f₇ a₆ b₆ e₆ f₆)
      htriple', rfl⟩
  obtain ⟨s₇, s₆, hmem₇, hmem₆, hsplit⟩ :
      ∃ (s₇ : PositiveWord cwBlockSupport (cwRectDepth a₇ b₇ e₇ f₇))
        (s₆ : PositiveWord cwBlockSupport (cwRectDepth a₆ b₆ e₆ f₆)),
        s₇ ∈ cwRectTypeWords a₇ b₇ e₇ f₇ ∧ s₆ ∈ cwRectTypeWords a₆ b₆ e₆ f₆ ∧
          positiveWordAppend s₇ (cwRectDepth a₆ b₆ e₆ f₆) s₆ = source := by
    obtain ⟨hleft, hright⟩ := (mem_cwMixedTypeAppendWords source).mp hsourceMem
    exact ⟨_, _, hleft, hright,
      positiveWordAppend_symm_fst_snd
        (cwRectDepth a₇ b₇ e₇ f₇) (cwRectDepth a₆ b₆ e₆ f₆) source⟩
  -- the two halves have the two rectangular leg marginals
  have hmarg₇ : WordType.multiplicity
      (positiveWordEquiv CWBlock (cwRectDepth a₇ b₇ e₇ f₇)
        (PartitionHashEncoding.supportWordAddress
          (A := fun _ : Leg ↦ CWBlock) (support := cwBlockSupport)
          (cwRectDepth a₇ b₇ e₇ f₇) s₇ c)) =
      cwRectMarginalType a₇ b₇ e₇ f₇ c :=
    cwRectLegWord_multiplicity a₇ b₇ e₇ f₇ (cwRectDepth a₇ b₇ e₇ f₇) s₇ hmem₇ c
  have hmarg₆ : WordType.multiplicity
      (positiveWordEquiv CWBlock (cwRectDepth a₆ b₆ e₆ f₆)
        (PartitionHashEncoding.supportWordAddress
          (A := fun _ : Leg ↦ CWBlock) (support := cwBlockSupport)
          (cwRectDepth a₆ b₆ e₆ f₆) s₆ c)) =
      cwRectMarginalType a₆ b₆ e₆ f₆ c :=
    cwRectLegWord_multiplicity a₆ b₆ e₆ f₆ (cwRectDepth a₆ b₆ e₆ f₆) s₆ hmem₆ c
  -- the exact source-word form of the leg fiber, and its positional split
  have hkey : (ProgressionHash.LegalTriple.legFiber
        (cwMixedTypeAppendTargets (R := R) a₇ b₇ e₇ f₇ a₆ b₆ e₆ f₆) triple c).card =
      (PartitionHashEncoding.sourceWordLegFiber
        (A := fun _ : Leg ↦ CWBlock) (support := cwBlockSupport)
        (cwMixedDepth a₇ b₇ e₇ f₇ a₆ b₆ e₆ f₆)
        (cwMixedTypeAppendWords a₇ b₇ e₇ f₇ a₆ b₆ e₆ f₆) c
        ((cwPartitionHashEncoding (R := R)).modeledAddress
          (cwMixedDepth a₇ b₇ e₇ f₇ a₆ b₆ e₆ f₆) triple c)).card :=
    (cwPartitionHashEncoding (R := R)).card_legFiber_legalTargets_eq_card_sourceWordLegFiber
      (cwMixedDepth a₇ b₇ e₇ f₇ a₆ b₆ e₆ f₆) (cwMixedTypeAppendWords a₇ b₇ e₇ f₇ a₆ b₆ e₆ f₆)
      htriple' c
  have haddr : (cwPartitionHashEncoding (R := R)).modeledAddress
        (cwMixedDepth a₇ b₇ e₇ f₇ a₆ b₆ e₆ f₆) triple c =
      positiveWordAppend
        (PartitionHashEncoding.supportWordAddress
          (A := fun _ : Leg ↦ CWBlock) (support := cwBlockSupport)
          (cwRectDepth a₇ b₇ e₇ f₇) s₇ c) (cwRectDepth a₆ b₆ e₆ f₆)
        (PartitionHashEncoding.supportWordAddress
          (A := fun _ : Leg ↦ CWBlock) (support := cwBlockSupport)
          (cwRectDepth a₆ b₆ e₆ f₆) s₆ c) := by
    rw [hmodeled, ← hsplit, supportWordAddress_positiveWordAppend]
  rw [hkey, haddr, card_sourceWordLegFiber_cwMixedTypeAppendWords,
    positiveWordAppendEquiv_symm_append]
  refine le_trans (Nat.mul_le_mul ?_ ?_) (cwMixedLegTypedFiber_le_bound a₇ b₇ e₇ f₇ a₆ b₆ e₆ f₆ c)
  · refine le_trans (card_sourceWordLegFiber_cwRectTypeWords_le a₇ b₇ e₇ f₇ c _) ?_
    exact le_of_eq (card_cwRectTypedWordMapFiber (cwRectDepth_add_one h₇) c _ hmarg₇)
  · refine le_trans (card_sourceWordLegFiber_cwRectTypeWords_le a₆ b₆ e₆ f₆ c _) ?_
    exact le_of_eq (card_cwRectTypedWordMapFiber (cwRectDepth_add_one h₆) c _ hmarg₆)

/-- The all-leg competitor list for a mixed-type target has size at most
`3 · cwMixedTypedFiberBound`. -/
theorem card_cwMixedTypeAppendTarget_legwiseCompetitors_le
    {a₇ b₇ e₇ f₇ a₆ b₆ e₆ f₆ : ℕ}
    (h₇ : 0 < a₇ + 2 * b₇ + 2 * e₇ + f₇) (h₆ : 0 < a₆ + 2 * b₆ + 2 * e₆ + f₆)
    {triple : ProgressionHash.LegalTriple R
      (Fin (cwMixedDepth a₇ b₇ e₇ f₇ a₆ b₆ e₆ f₆ + 1)) 2}
    (htriple : triple ∈ cwMixedTypeAppendTargets (R := R) a₇ b₇ e₇ f₇ a₆ b₆ e₆ f₆) :
    (ProgressionHash.LegalTriple.legwiseCompetitorYIndices
        (cwMixedTypeAppendTargets (R := R) a₇ b₇ e₇ f₇ a₆ b₆ e₆ f₆) triple).card ≤
      3 * cwMixedTypedFiberBound a₇ b₇ e₇ f₇ a₆ b₆ e₆ f₆ := by
  apply ProgressionHash.LegalTriple.card_legwiseCompetitorYIndices_le_three_mul
  intro c
  exact card_cwMixedTypeAppendTarget_legFiber_le h₇ h₆ htriple c

/-- A hashing field of size at least `12 · cwMixedTypedFiberBound` satisfies the quarter-degree
condition of the one-pass all-leg isolation theorem. -/
theorem cwMixedType_competitorQuarter_of_fieldCard [Fintype R]
    {a₇ b₇ e₇ f₇ a₆ b₆ e₆ f₆ : ℕ}
    (h₇ : 0 < a₇ + 2 * b₇ + 2 * e₇ + f₇) (h₆ : 0 < a₆ + 2 * b₆ + 2 * e₆ + f₆)
    (hcard : 12 * cwMixedTypedFiberBound a₇ b₇ e₇ f₇ a₆ b₆ e₆ f₆ ≤ Fintype.card R) :
    ∀ triple ∈ cwMixedTypeAppendTargets (R := R) a₇ b₇ e₇ f₇ a₆ b₆ e₆ f₆,
      4 * (ProgressionHash.LegalTriple.legwiseCompetitorYIndices
        (cwMixedTypeAppendTargets (R := R) a₇ b₇ e₇ f₇ a₆ b₆ e₆ f₆) triple).card ≤
          Fintype.card R := by
  intro triple htriple
  calc
    4 * (ProgressionHash.LegalTriple.legwiseCompetitorYIndices
        (cwMixedTypeAppendTargets (R := R) a₇ b₇ e₇ f₇ a₆ b₆ e₆ f₆) triple).card ≤
          4 * (3 * cwMixedTypedFiberBound a₇ b₇ e₇ f₇ a₆ b₆ e₆ f₆) :=
      Nat.mul_le_mul_left 4 (card_cwMixedTypeAppendTarget_legwiseCompetitors_le h₇ h₆ htriple)
    _ = 12 * cwMixedTypedFiberBound a₇ b₇ e₇ f₇ a₆ b₆ e₆ f₆ := by ring
    _ ≤ Fintype.card R := hcard

end Competitors

end AlgebraicComplexity.Examples
