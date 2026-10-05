/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Combinatorics.WordTypeMultiplicityFilter
import AlgebraicComplexity.MatrixMultiplication.WordTensorSplitAuto
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoOrbitTag
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoSixOrientationDigits
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoOrbitCounting
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoOrientationTypical
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoTensorSideEndpoint

/-!
# The value-side assembly of the level-two six-orientation stage

Layer 4 (`AlgebraicComplexity/Examples/`).  `[DuanWuZhou2022]` section 6.3's leaf value is a
statement about *one retained constituent* of the six-orientation positive power, and
`Examples/DuanWuZhouLevelTwoTensorSideEndpoint.lean` consumes it as `hconstituent`.  This module
is the tensor-side road from the endpoint's hypothesis down to the per-cell certificates: it
takes a retained constituent apart into its `6 (n+1)` oriented coarse letters, regroups those
letters so that every one of them meets a certificate it is eligible for, and multiplies the
weights back up.

## The three moves

* **Split by orientation.** `Isomorphic.positiveSupportWordTensor_external` says a word tensor
  over a partitioned *external product* is the external product of the two componentwise word
  tensors; five applications give
  `Isomorphic.positiveSupportWordTensor_symSixPartition`, which reads a six-orientation word
  tensor as the product of six word tensors over the six *coarse* partitions `P`,
  `P.permute cycle`, ..., in the association of `symSix_eq_sixOrientationProduct`.  The six
  oriented sub-words are `PartitionedTensor.symSixWord0 … symSixWord5`, and
  `symSixWord0_letter … symSixWord5_letter` read one of their letters.

  Note what is *not* done: the leg permutation is never carried outside the word tensor.  A word
  tensor over `P.permute e` stays a word tensor over a partition, so every word-level tool
  applies to it unchanged.  Transporting it to `Tensor.permute e (word tensor over P)` is
  provable but its `whnf` does not terminate within two million heartbeats, so the whole
  development is arranged to avoid needing it.

* **Peel the orbit letters.** `exists_positiveWord_extract_const` produces, from nothing but a
  multiplicity, the complementary block of a word: a word in which `s` occurs `k + 1` times is,
  typewise, some other word followed by `s^(k+1)`.  `Isomorphic.positiveSupportWordTensor_peel`
  and `..._peel3` are the tensor-level forms; three peels leave one oriented sub-word tensor as a
  bulk block followed by the three constant orbit blocks.

  This is the piece `MatrixMultiplication/WordTensorReindex.lean` deliberately left to clients
  ("a client exhibits the two intended blocks"): an orbit regrouping knows the counts but not the
  complementary word, so the complementary word has to be constructed.

* **Regroup across orientations.** The three orientations of one `C₃`-coset are exactly the three
  factors of one half of `symSixPartition`, so no letter ever has to cross between the two
  cosets.  Within a half, `Isomorphic.deinterleave3` (two middle-four interchanges) separates the
  three bulks from the nine orbit blocks and then transposes the `3 × 3` array of orbit blocks
  into three per-tag blocks; `Isomorphic.mergePower3` merges each; and
  `Isomorphic.power_permute_symThree_external`, read backwards, turns three *equal* per-tag
  powers into one power of `permute π (sym₃ T)` --- which is the object
  `dwz63_hasTauWeight_power_permute_symThree_112` and `..._121` bound.
  `Isomorphic.symSixHalf_regroup` is the whole half in one statement and
  `hasTauWeight_symSixHalf` its weight-level form.

  The equality of the three per-tag exponents is the *only* combinatorial input the regrouping
  needs, and it is exactly the tag count of `Examples/DuanWuZhouLevelTwoOrbitTag.lean`:
  `dwz63_rawTag_existsUnique` gives one orientation per (tag, orbit cell) pair, so each of the
  three tags of a coset collects the same number of oriented letters.

## The hashing interface

`dwz63_hconstituent_of_markedWordTensor` discharges the endpoint's `hconstituent` from a
statement about *marked words only*: the hashing lane's
`exists_markedSourceWord_of_mem_markedXYIsolatedPowerAddresses` recovers the marked word
underlying a retained address exactly, and `PartitionedTensor.withSupport` keeps the positive
power's constituents untouched, so a retained constituent *is* the word tensor of a marked word.
After this theorem no hashing notion occurs anywhere in the value lane.

## The typicality interface

`dwz63_multiplicity_symSixWord0 … 5` convert the count lane's target-coordinate typicality
(`Dwz63TargetTypical` of `Examples/DuanWuZhouLevelTwoTargetTypical.lean`, reached here through
`Examples/DuanWuZhouLevelTwoSixOrientationDigits.lean` --- the import direction is
`SixOrientationDigits` imports `TargetTypical`, never the reverse) into the multiplicities
`Isomorphic.positiveSupportWordTensor_peel3` consumes: the underlying word of the `o`-th oriented
sub-word *is* the count lane's `dwz63TargetWord K n o q`, so the bridge is one application of
`multiplicity_of_injective` at `Subtype.val`.

`dwz63_hasTauWeight_permuted_constituent` and `dwz63_isomorphic_permuted_orbitConstituent`
convert the letters: a non-rotational oriented letter carries its source constituent's weight
(`HasTauWeight.permute`, free in both directions), and an oriented orbit letter is
`permute (dwz63RawTag e s) T_(1,1,2)`, the tag being `Examples/DuanWuZhouLevelTwoOrbitTag.lean`'s.

## What is still owed

Everything here is tensor-semantic and unconditional.  What remains between these theorems and
`hconstituent` at a numerical weight is arithmetic, in three pieces, and none of it touches a
tensor:

1. **The oriented multiplicities.** Under target-coordinate typicality the source-cell counts over
   the `6 n` oriented letters are orbit-symmetrised.  Feeding them to `..._peel3` needs the three
   orbit multiplicities per orientation and the length identity
   `n = m + k_a + k_b + k_c + 3`.
2. **The tag counts.** The three per-tag exponents of each coset must be shown equal, which is
   `dwz63_rawTag_existsUnique` plus the multiplicities of 1.
3. **The value identity.** The assembled weight must be shown to dominate
   `Real.exp dwz63LogVal ^ (6 * (n + 1))`.  With orbit-maximal per-cell values this is an
   orbitwise "weighted mean at most maximum" estimate against the equality
   `dwz63_exp_logVal_pow_eq_prod`.  **It cannot be done with per-cell values on the `(1,1,2)`
   orbit**: with `a = alpha(1,1,2)`, `c = alpha(1,2,1)` the orbit-symmetrised count gives
   `2 (a - c) (log V_(1,2,1) - log V_(1,1,2))` of slack, and `a < c` while
   `V_(1,2,1) > V_(1,1,2)`, so that slack is *negative*.  The `(0,2,2)` orbit is the opposite
   case and per-cell values do suffice there.

Primary source: Ran Duan, Hongxun Wu and Renfei Zhou, *Faster Matrix Multiplication via
Asymmetric Hashing*, arXiv:2210.10173, `global_value.tex` section 6.3.
-/

namespace AlgebraicComplexity.Tensor

universe u v w z x₀ x₁ x₂ y₀ y₁ y₂ z₀ z₁ z₂

/-! ## A word tensor over an external partition splits

The middle-four interchange this section needs is the committed
`Tensor.Isomorphic.external_interchange` (`Tensor/Product.lean`, beside
`Isomorphic.external_swapRight`).  It used to be restated here as
`Isomorphic.external_middleFour` because the statement existed only in three private or
cone-heavy copies; that consolidation has since happened and `Tensor/Product.lean` is in this
module's import cone, so the restatement is gone and its uses point at the committed lemma. -/

section ExternalWord

variable {K : Type u} [CommSemiring K]
variable {A : Leg → Type w} [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]
variable {B : Leg → Type w} [∀ c, Fintype (B c)] [∀ c, DecidableEq (B c)]
variable {V : ∀ c, A c → Type (max u v)}
variable [∀ c a, AddCommMonoid (V c a)] [∀ c a, Module K (V c a)]
variable {W : ∀ c, B c → Type (max u v)}
variable [∀ c b, AddCommMonoid (W c b)] [∀ c b, Module K (W c b)]

/-- The left component of a supported letter of a partitioned external product. -/
noncomputable def PartitionedTensor.externalSupportFst
    (P : PartitionedTensor (K := K) (A := A) V)
    (Q : PartitionedTensor (K := K) (A := B) W) :
    (P.external Q).support → P.support :=
  fun s ↦ ⟨fun c ↦ (s.1 c).1,
    ((PartitionedTensor.mem_external_support P Q s.1).mp s.2).1⟩

/-- The right component of a supported letter of a partitioned external product. -/
noncomputable def PartitionedTensor.externalSupportSnd
    (P : PartitionedTensor (K := K) (A := A) V)
    (Q : PartitionedTensor (K := K) (A := B) W) :
    (P.external Q).support → Q.support :=
  fun s ↦ ⟨fun c ↦ (s.1 c).2,
    ((PartitionedTensor.mem_external_support P Q s.1).mp s.2).2⟩

-- ELABORATION RISK: the sibling statement "a word tensor over `P.permute e` is `Tensor.permute e`
-- of the source word tensor" is true and provable by the same induction, but its elaboration does
-- not terminate: at 2000000 heartbeats it still times out in `whnf`, because the successor step
-- has to unify a `PositivePowerBlockSpace` over `PermutedBlockSpace` with the leg permutation of a
-- `PositivePowerBlockSpace`.  FALLBACK, adopted here: never move the leg permutation outside a
-- word tensor.  A word tensor over `P.permute e` is a word tensor over a partition, so every
-- word-level tool applies to it directly, and the permutation is only ever unwound one
-- *constituent* at a time (`dwz63_hasTauWeight_permuted_constituent`,
-- `dwz63_isomorphic_permuted_orbitConstituent`), which is cheap.
/-- **A word tensor over a partitioned external product is the external product of the two
componentwise word tensors.**

This is the move that turns one word of six-orientation letters into six words of coarse letters:
the six orientations are independent factors of `symSixPartition`, and each factor's letters are
read off the corresponding component of the block label.  The isomorphism is an iterated
middle-four interchange, one per position. -/
theorem Isomorphic.positiveSupportWordTensor_external
    (P : PartitionedTensor (K := K) (A := A) V)
    (Q : PartitionedTensor (K := K) (A := B) W) :
    ∀ (n : ℕ) (q : PositiveWord (P.external Q).support n),
      Isomorphic (PartitionedTensor.positiveSupportWordTensor (P.external Q) n q)
        (Tensor.external
          (PartitionedTensor.positiveSupportWordTensor P n
            (positiveWordMap (P.externalSupportFst Q) n q))
          (PartitionedTensor.positiveSupportWordTensor Q n
            (positiveWordMap (P.externalSupportSnd Q) n q)))
  | 0, _ => Isomorphic.refl _
  | n + 1, q =>
      ((Isomorphic.positiveSupportWordTensor_external P Q n q.1).external
          (Isomorphic.refl ((P.external Q).constituent q.2.1))).trans
        (Isomorphic.external_interchange _ _ _ _)

end ExternalWord

/-! ## Peeling a constant block off a word

`MatrixMultiplication/WordTensorReindex.lean` splits a word tensor into two blocks provided the
client *exhibits* both blocks.  An orbit regrouping knows only the multiplicities, so it needs the
complementary block to be produced for it.  `exists_positiveWord_extract_const` does that: a word
in which the letter `s` occurs `k + 1` times is, up to reordering, a word of the remaining letters
followed by a constant block of `k + 1` copies of `s`.
-/

section Extract

variable {I : Type w} [Fintype I] [DecidableEq I]

/-- A word in which one letter occupies every position is the constant word, typewise. -/
theorem multiplicity_eq_of_full {N : ℕ} (f : Fin N → I) (s : I)
    (h : WordType.multiplicity f s = N) (j : I) :
    WordType.multiplicity f j = if j = s then N else 0 := by
  classical
  by_cases hj : j = s
  · subst hj; simp [h]
  · have hsum := WordType.sum_multiplicity f
    have hpair : ∑ i ∈ ({s, j} : Finset I), WordType.multiplicity f i =
        WordType.multiplicity f s + WordType.multiplicity f j :=
      Finset.sum_pair (Ne.symm hj)
    have hle : ∑ i ∈ ({s, j} : Finset I), WordType.multiplicity f i ≤
        ∑ i : I, WordType.multiplicity f i :=
      Finset.sum_le_sum_of_subset (Finset.subset_univ _)
    rw [if_neg hj]
    omega

/-- The multiplicity vector of a constant positive word, pointwise. -/
theorem multiplicity_const_word (s : I) (k : ℕ) (j : I) :
    WordType.multiplicity (positiveWordEquiv I k (positiveWordConst s k)) j =
      if j = s then k + 1 else 0 :=
  congrFun (WordType.multiplicity_positiveWordConst s k) j

/-- The multiplicity vector of a one-letter positive word, pointwise. -/
theorem multiplicity_zero_word (x : I) (j : I) :
    WordType.multiplicity (positiveWordEquiv I 0 x) j = if j = x then 1 else 0 :=
  multiplicity_const_word (I := I) x 0 j

/-- Splitting off the final letter of a positive word, at the level of multiplicities. -/
theorem multiplicity_positiveWord_pair {n : ℕ} (w : PositiveWord I n) (x : I) (j : I) :
    WordType.multiplicity
        (positiveWordEquiv I (n + 1) ((w, x) : PositiveWord I (n + 1))) j =
      WordType.multiplicity (positiveWordEquiv I n w) j + (if j = x then 1 else 0) := by
  have h := congrFun (WordType.multiplicity_positiveWordAppend (I := I) (n := n) (m := 0) w x) j
  rw [Pi.add_apply, multiplicity_zero_word (I := I) x j] at h
  exact h

omit [Fintype I] in
/-- Multiplicities are read through an injective relabeling of the alphabet. -/
theorem multiplicity_of_injective {J : Type w} [Fintype J] [DecidableEq J]
    (f : I → J) (hf : Function.Injective f) {N : ℕ} (word : Fin N → I) (i : I) :
    WordType.multiplicity word i = WordType.multiplicity (f ∘ word) (f i) := by
  classical
  rw [WordType.multiplicity_eq_card_filter, WordType.multiplicity_eq_card_filter]
  congr 1
  apply Finset.filter_congr
  intro j _
  exact ⟨fun h ↦ by rw [Function.comp_apply, h], fun h ↦ hf h⟩

/-- **Every word splits, typewise, into a constant block and the rest.**

If the letter `s` occupies exactly `k + 1` of the `m + k + 2` positions of `w`, there is a word
`u` on the remaining `m + 1` positions whose multiplicities, together with those of the constant
block `s^(k+1)`, reproduce those of `w`.  Reordering is then free
(`Isomorphic.positiveSupportWordTensor_of_same_type`), so a client may treat `w` as
`u ++ s^(k+1)`. -/
theorem exists_positiveWord_extract_const :
    ∀ (n : ℕ) (w : PositiveWord I n) (s : I) (k m : ℕ), n = m + k + 1 →
      WordType.multiplicity (positiveWordEquiv I n w) s = k + 1 →
      ∃ u : PositiveWord I m, ∀ j : I,
        WordType.multiplicity (positiveWordEquiv I n w) j =
          WordType.multiplicity (positiveWordEquiv I m u) j + (if j = s then k + 1 else 0) := by
  classical
  intro n
  induction n with
  | zero => intro _ _ k m hn _; omega
  | succ n ih =>
      rintro ⟨w, x⟩ s k m hn hmult
      have hstep := multiplicity_positiveWord_pair (I := I) w x
      by_cases hs : x = s
      · subst hs
        match k, hn, hmult with
        | 0, hn, hmult =>
            obtain rfl : m = n := by omega
            exact ⟨w, fun j ↦ hstep j⟩
        | (k + 1), hn, hmult =>
            have hn' : n = m + k + 1 := by omega
            have hm1 : WordType.multiplicity (positiveWordEquiv I n w) x = k + 1 := by
              have h := hstep x
              rw [if_pos rfl] at h
              omega
            obtain ⟨u, hu⟩ := ih w x k m hn' hm1
            refine ⟨u, fun j ↦ ?_⟩
            rw [hstep j, hu j]
            by_cases hj : j = x
            · rw [if_pos hj, if_pos hj, if_pos hj]; omega
            · rw [if_neg hj, if_neg hj, if_neg hj]
      · have hsx : ¬ (s = x) := fun h ↦ hs h.symm
        have hm1 : WordType.multiplicity (positiveWordEquiv I n w) s = k + 1 := by
          have h := hstep s
          rw [if_neg hsx] at h
          omega
        match m, hn with
        | 0, hn =>
            have hfull : WordType.multiplicity (positiveWordEquiv I n w) s = n + 1 := by omega
            refine ⟨x, fun j ↦ ?_⟩
            rw [hstep j, multiplicity_eq_of_full (positiveWordEquiv I n w) s hfull j,
              multiplicity_zero_word (I := I) x j]
            by_cases hj : j = s
            · have hjx : ¬ (j = x) := fun h ↦ hs (h.symm.trans hj)
              rw [if_pos hj, if_pos hj, if_neg hjx]
              omega
            · rw [if_neg hj, if_neg hj]
              omega
        | (m + 1), hn =>
            have hn' : n = m + k + 1 := by omega
            obtain ⟨u, hu⟩ := ih w s k m hn' hm1
            refine ⟨(u, x), fun j ↦ ?_⟩
            rw [hstep j, hu j, multiplicity_positiveWord_pair (I := I) u x j]
            omega

end Extract

/-! ## The split with the complementary block produced -/

section Split

variable {K : Type u} [CommSemiring K]
variable {A : Leg → Type w} [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]
variable {V : ∀ c, A c → Type (max u v)}
variable [∀ c a, AddCommMonoid (V c a)] [∀ c a, Module K (V c a)]

/-- The word split with the multiplicity side condition in additive form, as an isomorphism. -/
theorem Isomorphic.positiveSupportWordTensor_split_add
    (P : PartitionedTensor (K := K) (A := A) V) {n m : ℕ}
    (q : PositiveWord P.support (n + m + 1))
    (left : PositiveWord P.support n) (right : PositiveWord P.support m)
    (hmult : ∀ j, WordType.multiplicity (positiveWordEquiv P.support (n + m + 1) q) j =
      WordType.multiplicity (positiveWordEquiv P.support n left) j +
        WordType.multiplicity (positiveWordEquiv P.support m right) j) :
    Isomorphic (PartitionedTensor.positiveSupportWordTensor P (n + m + 1) q)
      (Tensor.external (PartitionedTensor.positiveSupportWordTensor P n left)
        (PartitionedTensor.positiveSupportWordTensor P m right)) :=
  AlgebraicComplexity.Tensor.Isomorphic.positiveSupportWordTensor_split P q left right
    ((funext hmult).trans (WordType.multiplicity_positiveWordAppend left right).symm)

/-- **Peeling a constant block off a word tensor.**

If the supported letter `s` occurs `k + 1` times in `q`, the word tensor of `q` is the external
product of a word tensor on the remaining positions with the `(k+1)`-st power of the constituent
at `s`.  This is the only shape the orbit regrouping needs: repeated application peels the three
orbit cells off each oriented sub-word and leaves the non-rotational bulk. -/
theorem Isomorphic.positiveSupportWordTensor_peel
    (P : PartitionedTensor (K := K) (A := A) V) {n m k : ℕ} (hn : n = m + k + 1)
    (q : PositiveWord P.support n) (s : P.support)
    (hmult : WordType.multiplicity (positiveWordEquiv P.support n q) s = k + 1) :
    ∃ u : PositiveWord P.support m,
      (∀ j : P.support, WordType.multiplicity (positiveWordEquiv P.support n q) j =
        WordType.multiplicity (positiveWordEquiv P.support m u) j +
          (if j = s then k + 1 else 0)) ∧
      Isomorphic (PartitionedTensor.positiveSupportWordTensor P n q)
        (Tensor.external (PartitionedTensor.positiveSupportWordTensor P m u)
          (Tensor.power (P.constituent s.1) (k + 1))) := by
  classical
  obtain ⟨u, hu⟩ := exists_positiveWord_extract_const (I := P.support) n q s k m hn hmult
  refine ⟨u, ?_, ?_⟩
  · subst hn; exact hu
  subst hn
  have hu' : ∀ j, WordType.multiplicity (positiveWordEquiv P.support (m + k + 1) q) j =
      WordType.multiplicity (positiveWordEquiv P.support m u) j +
        WordType.multiplicity (positiveWordEquiv P.support k (positiveWordConst s k)) j := by
    intro j
    rw [hu j, multiplicity_const_word (I := P.support) s k j]
  exact (Isomorphic.positiveSupportWordTensor_split_add P q u
      (positiveWordConst s k) hu').trans
    ((Isomorphic.refl _).external (PartitionedTensor.Isomorphic.positiveSupportWordTensor_const_power P s k))

-- ELABORATION RISK: three nested `positiveSupportWordTensor_peel` applications carry three
-- different word lengths through dependent block spaces.  FALLBACK if the limit is ever exceeded:
-- state the three peels as three separate `have`s with explicit `(m := _) (k := _)` and compose
-- the isomorphisms in a final `exact`, which is what the proof below already does.
set_option maxHeartbeats 1000000 in
/-- **Peeling three constant blocks off a word tensor.**

The shape one oriented sub-word of a six-orientation word takes once its three orbit letters have
been separated: a bulk word tensor followed by three constant powers, in the tag order the orbit
regrouping consumes.  The residual multiplicities of the bulk agree with those of the original
word away from the three peeled letters, which is what a bulk value computation reads. -/
theorem Isomorphic.positiveSupportWordTensor_peel3
    (P : PartitionedTensor (K := K) (A := A) V) {n m ka kb kc : ℕ}
    (q : PositiveWord P.support n) (sa sb sc : P.support)
    (hab : sa ≠ sb) (hac : sa ≠ sc) (hbc : sb ≠ sc)
    (hn : n = m + ka + kb + kc + 3)
    (hma : WordType.multiplicity (positiveWordEquiv P.support n q) sa = ka + 1)
    (hmb : WordType.multiplicity (positiveWordEquiv P.support n q) sb = kb + 1)
    (hmc : WordType.multiplicity (positiveWordEquiv P.support n q) sc = kc + 1) :
    ∃ u : PositiveWord P.support m,
      (∀ j : P.support, j ≠ sa → j ≠ sb → j ≠ sc →
        WordType.multiplicity (positiveWordEquiv P.support m u) j =
          WordType.multiplicity (positiveWordEquiv P.support n q) j) ∧
      Isomorphic (PartitionedTensor.positiveSupportWordTensor P n q)
        (Tensor.external
          (Tensor.external
            (Tensor.external (PartitionedTensor.positiveSupportWordTensor P m u)
              (Tensor.power (P.constituent sa.1) (ka + 1)))
            (Tensor.power (P.constituent sb.1) (kb + 1)))
          (Tensor.power (P.constituent sc.1) (kc + 1))) := by
  obtain ⟨u₁, h₁m, h₁i⟩ := Isomorphic.positiveSupportWordTensor_peel P
    (m := m + ka + kb + 2) (k := kc) (by omega) q sc hmc
  have hmb₁ : WordType.multiplicity
      (positiveWordEquiv P.support (m + ka + kb + 2) u₁) sb = kb + 1 := by
    have h := h₁m sb
    rw [if_neg hbc] at h
    omega
  obtain ⟨u₂, h₂m, h₂i⟩ := Isomorphic.positiveSupportWordTensor_peel P
    (m := m + ka + 1) (k := kb) (by omega) u₁ sb hmb₁
  have hma₂ : WordType.multiplicity
      (positiveWordEquiv P.support (m + ka + 1) u₂) sa = ka + 1 := by
    have h1 := h₁m sa
    have h2 := h₂m sa
    rw [if_neg hac] at h1
    rw [if_neg hab] at h2
    omega
  obtain ⟨u₃, h₃m, h₃i⟩ := Isomorphic.positiveSupportWordTensor_peel P
    (m := m) (k := ka) (by omega) u₂ sa hma₂
  refine ⟨u₃, ?_, ?_⟩
  · intro j hja hjb hjc
    have h1 := h₁m j
    have h2 := h₂m j
    have h3 := h₃m j
    rw [if_neg hjc] at h1
    rw [if_neg hjb] at h2
    rw [if_neg hja] at h3
    omega
  · exact h₁i.trans ((h₂i.trans (h₃i.external (Isomorphic.refl _))).external
      (Isomorphic.refl _))

end Split

/-! ## The six oriented sub-words of a six-orientation word -/

section SymSix

variable {K : Type u} [CommSemiring K]
variable {A : Leg → Type w} [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]
variable {V : ∀ c, A c → Type (max u v)}
variable [∀ c a, AddCommMonoid (V c a)] [∀ c a, Module K (V c a)]

namespace PartitionedTensor

variable (P : PartitionedTensor (K := K) (A := A) V)

/-- The three-orientation partitioned product, spelled out.  Reducible, so that the block-label
types of its two factors unify syntactically with the ones the sub-word extractors produce. -/
@[reducible] noncomputable def symThreeExt :=
  (P.external (P.permute cycle)).external (P.permute cycle.symm)

/-- The swapped three-orientation partitioned product, spelled out. -/
@[reducible] noncomputable def swapSymThreeExt :=
  ((P.permute swapXY).external (P.permute (cycle.trans swapXY))).external
    (P.permute (cycle.symm.trans swapXY))

/-- The six-orientation partitioned product, spelled out. -/
@[reducible] noncomputable def symSixExt :=
  P.symThreeExt.external P.swapSymThreeExt

theorem symSixExt_eq : P.symSixExt = P.symSixPartition := rfl

/-- The identity-orientation sub-word of a six-orientation word. -/
noncomputable def symSixWord0 (n : ℕ) (q : PositiveWord P.symSixExt.support n) :
    PositiveWord P.support n :=
  positiveWordMap (P.externalSupportFst (P.permute cycle)) n
    (positiveWordMap ((P.external (P.permute cycle)).externalSupportFst
        (P.permute cycle.symm)) n
      (positiveWordMap (P.symThreeExt.externalSupportFst P.swapSymThreeExt) n q))

/-- The `cycle` sub-word of a six-orientation word. -/
noncomputable def symSixWord1 (n : ℕ) (q : PositiveWord P.symSixExt.support n) :
    PositiveWord (P.permute cycle).support n :=
  positiveWordMap (P.externalSupportSnd (P.permute cycle)) n
    (positiveWordMap ((P.external (P.permute cycle)).externalSupportFst
        (P.permute cycle.symm)) n
      (positiveWordMap (P.symThreeExt.externalSupportFst P.swapSymThreeExt) n q))

/-- The `cycle⁻¹` sub-word of a six-orientation word. -/
noncomputable def symSixWord2 (n : ℕ) (q : PositiveWord P.symSixExt.support n) :
    PositiveWord (P.permute cycle.symm).support n :=
  positiveWordMap ((P.external (P.permute cycle)).externalSupportSnd
      (P.permute cycle.symm)) n
    (positiveWordMap (P.symThreeExt.externalSupportFst P.swapSymThreeExt) n q)

/-- The `swapXY` sub-word of a six-orientation word. -/
noncomputable def symSixWord3 (n : ℕ) (q : PositiveWord P.symSixExt.support n) :
    PositiveWord (P.permute swapXY).support n :=
  positiveWordMap ((P.permute swapXY).externalSupportFst
      (P.permute (cycle.trans swapXY))) n
    (positiveWordMap (((P.permute swapXY).external
        (P.permute (cycle.trans swapXY))).externalSupportFst
          (P.permute (cycle.symm.trans swapXY))) n
      (positiveWordMap (P.symThreeExt.externalSupportSnd P.swapSymThreeExt) n q))

/-- The `cycle · swapXY` sub-word of a six-orientation word. -/
noncomputable def symSixWord4 (n : ℕ) (q : PositiveWord P.symSixExt.support n) :
    PositiveWord (P.permute (cycle.trans swapXY)).support n :=
  positiveWordMap ((P.permute swapXY).externalSupportSnd
      (P.permute (cycle.trans swapXY))) n
    (positiveWordMap (((P.permute swapXY).external
        (P.permute (cycle.trans swapXY))).externalSupportFst
          (P.permute (cycle.symm.trans swapXY))) n
      (positiveWordMap (P.symThreeExt.externalSupportSnd P.swapSymThreeExt) n q))

/-- The `cycle⁻¹ · swapXY` sub-word of a six-orientation word. -/
noncomputable def symSixWord5 (n : ℕ) (q : PositiveWord P.symSixExt.support n) :
    PositiveWord (P.permute (cycle.symm.trans swapXY)).support n :=
  positiveWordMap (((P.permute swapXY).external
      (P.permute (cycle.trans swapXY))).externalSupportSnd
        (P.permute (cycle.symm.trans swapXY))) n
    (positiveWordMap (P.symThreeExt.externalSupportSnd P.swapSymThreeExt) n q)

end PartitionedTensor

/-- **A six-orientation word tensor is the external product of its six oriented sub-word
tensors.**

The six leg permutations are independent factors of `symSixPartition`, so five applications of
`Isomorphic.positiveSupportWordTensor_external` separate them, in the association of
`symSix_eq_sixOrientationProduct`.  Each factor is a word tensor over one *coarse* partition ---
`P` itself for the identity orientation and `P.permute e` for the other five --- so every
word-level tool (`positiveSupportWordTensor_peel`, `hasTauWeight_wordTensor`) applies to it
directly, with no leg permutation left to carry. -/
theorem Isomorphic.positiveSupportWordTensor_symSixPartition
    (P : PartitionedTensor (K := K) (A := A) V) (n : ℕ)
    (q : PositiveWord P.symSixExt.support n) :
    Isomorphic (PartitionedTensor.positiveSupportWordTensor P.symSixExt n q)
      (Tensor.external
        (Tensor.external
          (Tensor.external
            (PartitionedTensor.positiveSupportWordTensor P n (P.symSixWord0 n q))
            (PartitionedTensor.positiveSupportWordTensor (P.permute cycle) n
              (P.symSixWord1 n q)))
          (PartitionedTensor.positiveSupportWordTensor (P.permute cycle.symm) n
            (P.symSixWord2 n q)))
        (Tensor.external
          (Tensor.external
            (PartitionedTensor.positiveSupportWordTensor (P.permute swapXY) n
              (P.symSixWord3 n q))
            (PartitionedTensor.positiveSupportWordTensor (P.permute (cycle.trans swapXY)) n
              (P.symSixWord4 n q)))
          (PartitionedTensor.positiveSupportWordTensor
            (P.permute (cycle.symm.trans swapXY)) n (P.symSixWord5 n q)))) := by
  refine (Isomorphic.positiveSupportWordTensor_external
    P.symThreeExt P.swapSymThreeExt n q).trans ?_
  refine Isomorphic.external ?_ ?_
  · refine (Isomorphic.positiveSupportWordTensor_external
      (P.external (P.permute cycle)) (P.permute cycle.symm) n _).trans ?_
    exact (Isomorphic.positiveSupportWordTensor_external
      P (P.permute cycle) n _).external (Isomorphic.refl _)
  · refine (Isomorphic.positiveSupportWordTensor_external
      ((P.permute swapXY).external (P.permute (cycle.trans swapXY)))
      (P.permute (cycle.symm.trans swapXY)) n _).trans ?_
    exact (Isomorphic.positiveSupportWordTensor_external
      (P.permute swapXY) (P.permute (cycle.trans swapXY)) n _).external (Isomorphic.refl _)

/-! ## Reading a letter of an oriented sub-word -/

/-- Reading one position of a letterwise-relabeled word. -/
theorem positiveWordEquiv_positiveWordMap_apply {I J : Type w} (f : I → J) (n : ℕ)
    (q : PositiveWord I n) (j : Fin (n + 1)) :
    positiveWordEquiv J n (positiveWordMap f n q) j = f (positiveWordEquiv I n q j) := by
  rw [positiveWordEquiv_map]
  rfl

namespace PartitionedTensor

variable (P : PartitionedTensor (K := K) (A := A) V)

theorem symSixWord0_letter (n : ℕ)
    (q : PositiveWord P.symSixExt.support n) (j : Fin (n + 1)) :
    ((positiveWordEquiv P.support n (P.symSixWord0 n q) j : P.support) : BlockAddress A) =
      fun c ↦ ((positiveWordEquiv P.symSixExt.support n q j : _).1 c).1.1.1 := by
  unfold symSixWord0
  rw [positiveWordEquiv_positiveWordMap_apply, positiveWordEquiv_positiveWordMap_apply,
    positiveWordEquiv_positiveWordMap_apply]
  rfl

theorem symSixWord1_letter (n : ℕ)
    (q : PositiveWord P.symSixExt.support n) (j : Fin (n + 1)) :
    ((positiveWordEquiv (P.permute cycle).support n (P.symSixWord1 n q) j :
        (P.permute cycle).support) : BlockAddress (PermutedBlockIndex cycle A)) =
      fun c ↦ ((positiveWordEquiv P.symSixExt.support n q j : _).1 c).1.1.2 := by
  unfold symSixWord1
  rw [positiveWordEquiv_positiveWordMap_apply, positiveWordEquiv_positiveWordMap_apply,
    positiveWordEquiv_positiveWordMap_apply]
  rfl

theorem symSixWord2_letter (n : ℕ)
    (q : PositiveWord P.symSixExt.support n) (j : Fin (n + 1)) :
    ((positiveWordEquiv (P.permute cycle.symm).support n (P.symSixWord2 n q) j :
        (P.permute cycle.symm).support) :
        BlockAddress (PermutedBlockIndex cycle.symm A)) =
      fun c ↦ ((positiveWordEquiv P.symSixExt.support n q j : _).1 c).1.2 := by
  unfold symSixWord2
  rw [positiveWordEquiv_positiveWordMap_apply, positiveWordEquiv_positiveWordMap_apply]
  rfl

theorem symSixWord3_letter (n : ℕ)
    (q : PositiveWord P.symSixExt.support n) (j : Fin (n + 1)) :
    ((positiveWordEquiv (P.permute swapXY).support n (P.symSixWord3 n q) j :
        (P.permute swapXY).support) : BlockAddress (PermutedBlockIndex swapXY A)) =
      fun c ↦ ((positiveWordEquiv P.symSixExt.support n q j : _).1 c).2.1.1 := by
  unfold symSixWord3
  rw [positiveWordEquiv_positiveWordMap_apply, positiveWordEquiv_positiveWordMap_apply,
    positiveWordEquiv_positiveWordMap_apply]
  rfl

theorem symSixWord4_letter (n : ℕ)
    (q : PositiveWord P.symSixExt.support n) (j : Fin (n + 1)) :
    ((positiveWordEquiv (P.permute (cycle.trans swapXY)).support n (P.symSixWord4 n q) j :
        (P.permute (cycle.trans swapXY)).support) :
        BlockAddress (PermutedBlockIndex (cycle.trans swapXY) A)) =
      fun c ↦ ((positiveWordEquiv P.symSixExt.support n q j : _).1 c).2.1.2 := by
  unfold symSixWord4
  rw [positiveWordEquiv_positiveWordMap_apply, positiveWordEquiv_positiveWordMap_apply,
    positiveWordEquiv_positiveWordMap_apply]
  rfl

theorem symSixWord5_letter (n : ℕ)
    (q : PositiveWord P.symSixExt.support n) (j : Fin (n + 1)) :
    ((positiveWordEquiv (P.permute (cycle.symm.trans swapXY)).support n
        (P.symSixWord5 n q) j : (P.permute (cycle.symm.trans swapXY)).support) :
        BlockAddress (PermutedBlockIndex (cycle.symm.trans swapXY) A)) =
      fun c ↦ ((positiveWordEquiv P.symSixExt.support n q j : _).1 c).2.2 := by
  unfold symSixWord5
  rw [positiveWordEquiv_positiveWordMap_apply, positiveWordEquiv_positiveWordMap_apply]
  rfl

end PartitionedTensor

end SymSix

/-! ## Regrouping toolkit -/

section Regroup

variable {K : Type u} [CommSemiring K]
variable {V₀ : Leg → Type x₀} [∀ c, AddCommMonoid (V₀ c)] [∀ c, Module K (V₀ c)]
variable {V₁ : Leg → Type x₁} [∀ c, AddCommMonoid (V₁ c)] [∀ c, Module K (V₁ c)]
variable {V₂ : Leg → Type x₂} [∀ c, AddCommMonoid (V₂ c)] [∀ c, Module K (V₂ c)]
variable {W₀ : Leg → Type y₀} [∀ c, AddCommMonoid (W₀ c)] [∀ c, Module K (W₀ c)]
variable {W₁ : Leg → Type y₁} [∀ c, AddCommMonoid (W₁ c)] [∀ c, Module K (W₁ c)]
variable {W₂ : Leg → Type y₂} [∀ c, AddCommMonoid (W₂ c)] [∀ c, Module K (W₂ c)]

-- ELABORATION RISK: the six type families below must live in six *independent* universes.  With
-- all of them declared in one `Type v` the bulk families (which are `Type v`) and the power
-- families (which are `Type (max u v)`) generate an unsatisfiable universe constraint, and
-- `hasTauWeight_symSixHalf` then times out in `isDefEq` at 1000000 heartbeats with no useful
-- diagnostic.  FALLBACK, adopted here: one universe variable per family.
/-- **De-interleaving three pairs.**

`(B₀ ⊗ O₀) ⊗ (B₁ ⊗ O₁) ⊗ (B₂ ⊗ O₂) ≅ (B₀ ⊗ B₁ ⊗ B₂) ⊗ (O₀ ⊗ O₁ ⊗ O₂)`, in the
left-associated reading throughout.  Two middle-four interchanges.  This is the only cross-factor
move the orbit regrouping makes: the three orientations of one `C₃`-coset each contribute a bulk
part and an orbit part, and the orbit parts have to be brought together before any cyclic triple
can be formed. -/
theorem Isomorphic.deinterleave3
    (B₀ : Tensor3 K V₀) (O₀ : Tensor3 K W₀)
    (B₁ : Tensor3 K V₁) (O₁ : Tensor3 K W₁)
    (B₂ : Tensor3 K V₂) (O₂ : Tensor3 K W₂) :
    Isomorphic
      (Tensor.external
        (Tensor.external (Tensor.external B₀ O₀) (Tensor.external B₁ O₁))
        (Tensor.external B₂ O₂))
      (Tensor.external
        (Tensor.external (Tensor.external B₀ B₁) B₂)
        (Tensor.external (Tensor.external O₀ O₁) O₂)) :=
  ((Isomorphic.external_interchange B₀ O₀ B₁ O₁).external (Isomorphic.refl _)).trans
    (Isomorphic.external_interchange (Tensor.external B₀ B₁)
      (Tensor.external O₀ O₁) B₂ O₂)

/-- **Pulling three peeled blocks out of a prefix.**

Three applications of `positiveSupportWordTensor_peel` leave `((X ⊗ A) ⊗ B) ⊗ C`; the bulk `X`
has to be separated from the three peeled blocks before the de-interleaving. -/
theorem Isomorphic.regroupPeel3
    (X : Tensor3 K V₀) (A : Tensor3 K V₁) (B : Tensor3 K V₂) (C : Tensor3 K W₀) :
    Isomorphic
      (Tensor.external (Tensor.external (Tensor.external X A) B) C)
      (Tensor.external X (Tensor.external (Tensor.external A B) C)) :=
  ((Isomorphic.external_assoc (Tensor.external X A) B C).trans
      (Isomorphic.external_assoc X A (Tensor.external B C))).trans
    ((Isomorphic.refl X).external (Isomorphic.external_assoc_symm A B C))

variable {V : Leg → Type v} [∀ c, AddCommMonoid (V c)] [∀ c, Module K (V c)]

/-- Three consecutive powers of one tensor merge into a single power. -/
theorem Isomorphic.mergePower3 (X : Tensor3 K V) (a b c : ℕ) :
    Isomorphic
      (Tensor.external (Tensor.external (Tensor.power X a) (Tensor.power X b))
        (Tensor.power X c))
      (Tensor.power X (a + b + c)) :=
  ((isomorphic_external_power X a b).external (Isomorphic.refl _)).trans
    (isomorphic_external_power X (a + b) c)

/-- **A block of `m + 1` cyclic triples at tag `π`.**

`permute π (sym₃ T)` is the external product of the three `C₃`-coset rotations
(`permute_symThree_eq`), so its positive power splits factorwise into three equal powers, one per
tag of the coset.  Read backwards --- which is how the orbit regrouping uses it --- three equal
powers at the three tags of one coset assemble into a power of `permute π (sym₃ T)`, which is
exactly what the orbit certificates bound. -/
theorem Isomorphic.power_permute_symThree_external
    (T : Tensor3 K V) (π : Orientation) (m : ℕ) :
    Isomorphic
      (Tensor.power (Tensor.permute π (symThree K T)) (m + 1))
      (Tensor.external
        (Tensor.external (Tensor.power (Tensor.permute π T) (m + 1))
          (Tensor.power (Tensor.permute (cycle.trans π) T) (m + 1)))
        (Tensor.power (Tensor.permute (cycle.symm.trans π) T) (m + 1))) := by
  rw [Examples.permute_symThree_eq]
  exact (Isomorphic.power_external_positive _ _ m).trans
    ((Isomorphic.power_external_positive _ _ m).external (Isomorphic.refl _))

end Regroup

/-! ## Weights of a six-orientation word tensor -/

section SymSixWeight

variable {K : Type u} [CommSemiring K]
variable {A : Leg → Type w} [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]
variable {V : ∀ c, A c → Type (max u v)}
variable [∀ c a, AddCommMonoid (V c a)] [∀ c a, Module K (V c a)]

/-- **The weight of a six-orientation word tensor from the six oriented sub-word weights.**

This is the shape a client uses when the six orientations can be weighed independently --- i.e.
when no letter needs a cyclic regrouping.  When some letters do, the client instead uses
`Isomorphic.positiveSupportWordTensor_symSixPartition` directly, splits each factor, and
regroups with `Isomorphic.deinterleave3`. -/
theorem hasTauWeight_positiveSupportWordTensor_symSix
    (P : PartitionedTensor (K := K) (A := A) V) {τ : ℝ} (n : ℕ)
    (q : PositiveWord P.symSixExt.support n)
    {a₀ a₁ a₂ a₃ a₄ a₅ : ℝ}
    (h₀ : HasTauWeight K (PartitionedTensor.positiveSupportWordTensor P n
      (P.symSixWord0 n q)) τ a₀)
    (h₁ : HasTauWeight K (PartitionedTensor.positiveSupportWordTensor (P.permute cycle) n
      (P.symSixWord1 n q)) τ a₁)
    (h₂ : HasTauWeight K (PartitionedTensor.positiveSupportWordTensor (P.permute cycle.symm) n
      (P.symSixWord2 n q)) τ a₂)
    (h₃ : HasTauWeight K (PartitionedTensor.positiveSupportWordTensor (P.permute swapXY) n
      (P.symSixWord3 n q)) τ a₃)
    (h₄ : HasTauWeight K (PartitionedTensor.positiveSupportWordTensor
      (P.permute (cycle.trans swapXY)) n (P.symSixWord4 n q)) τ a₄)
    (h₅ : HasTauWeight K (PartitionedTensor.positiveSupportWordTensor
      (P.permute (cycle.symm.trans swapXY)) n (P.symSixWord5 n q)) τ a₅)
    (n₀ : 0 ≤ a₀) (n₁ : 0 ≤ a₁) (n₂ : 0 ≤ a₂) (n₃ : 0 ≤ a₃) (n₄ : 0 ≤ a₄) (n₅ : 0 ≤ a₅) :
    HasTauWeight K (PartitionedTensor.positiveSupportWordTensor P.symSixExt n q) τ
      (a₀ * a₁ * a₂ * (a₃ * a₄ * a₅)) :=
  HasTauWeight.of_restricts
    (Isomorphic.positiveSupportWordTensor_symSixPartition P n q).restricts
    (HasTauWeight.external
      (HasTauWeight.external (HasTauWeight.external h₀ h₁ n₀ n₁) h₂ (mul_nonneg n₀ n₁) n₂)
      (HasTauWeight.external (HasTauWeight.external h₃ h₄ n₃ n₄) h₅ (mul_nonneg n₃ n₄) n₅)
      (mul_nonneg (mul_nonneg n₀ n₁) n₂) (mul_nonneg (mul_nonneg n₃ n₄) n₅))

end SymSixWeight

/-! ## One `C₃`-coset half of a six-orientation word -/

section Half

variable {K : Type u} [CommSemiring K]
variable {V₀ : Leg → Type x₀} [∀ c, AddCommMonoid (V₀ c)] [∀ c, Module K (V₀ c)]
variable {V₁ : Leg → Type x₁} [∀ c, AddCommMonoid (V₁ c)] [∀ c, Module K (V₁ c)]
variable {V₂ : Leg → Type x₂} [∀ c, AddCommMonoid (V₂ c)] [∀ c, Module K (V₂ c)]
variable {W : Leg → Type v} [∀ c, AddCommMonoid (W c)] [∀ c, Module K (W c)]

-- ELABORATION RISK: `rw [ha, hb, hc]` at the end of this proof rewrites *exponents of powers*,
-- whose block spaces depend on them, and it did not terminate at 1000000 heartbeats.  FALLBACK,
-- adopted here: transport the exponents with `Isomorphic.power_congr` instead of rewriting.
set_option maxHeartbeats 1000000 in
/-- **Nine per-tag orbit blocks merge into one block of cyclic triples.**

The three orientations of one `C₃`-coset each contribute three constant blocks, one per tag of
the coset, in the order `π`, `cycle · π`, `cycle⁻¹ · π`.  Transposing the `3 × 3` array
(`deinterleave3` twice), merging each row (`mergePower3`) and reading `permute_symThree_eq`
backwards turns them into a single power of `permute π (sym₃ T)` --- which is what the orbit
certificates bound.  The three row sums must agree; that equality is the content of the tag
count. -/
theorem Isomorphic.orbitTriple_merge
    (T : Tensor3 K W) (π : Orientation)
    (a₀ a₁ a₂ b₀ b₁ b₂ c₀ c₁ c₂ m : ℕ)
    (ha : a₀ + a₁ + a₂ = m + 1) (hb : b₀ + b₁ + b₂ = m + 1) (hc : c₀ + c₁ + c₂ = m + 1) :
    Isomorphic
      (Tensor.external
        (Tensor.external
          (Tensor.external
            (Tensor.external (Tensor.power (Tensor.permute π T) a₀)
              (Tensor.power (Tensor.permute (cycle.trans π) T) b₀))
            (Tensor.power (Tensor.permute (cycle.symm.trans π) T) c₀))
          (Tensor.external
            (Tensor.external (Tensor.power (Tensor.permute π T) a₁)
              (Tensor.power (Tensor.permute (cycle.trans π) T) b₁))
            (Tensor.power (Tensor.permute (cycle.symm.trans π) T) c₁)))
        (Tensor.external
          (Tensor.external (Tensor.power (Tensor.permute π T) a₂)
            (Tensor.power (Tensor.permute (cycle.trans π) T) b₂))
          (Tensor.power (Tensor.permute (cycle.symm.trans π) T) c₂)))
      (Tensor.power (Tensor.permute π (symThree K T)) (m + 1)) := by
  refine (Isomorphic.deinterleave3 _ _ _ _ _ _).trans ?_
  refine ((Isomorphic.deinterleave3 _ _ _ _ _ _).external (Isomorphic.refl _)).trans ?_
  refine (((Isomorphic.mergePower3 (Tensor.permute π T) a₀ a₁ a₂).external
      (Isomorphic.mergePower3 (Tensor.permute (cycle.trans π) T) b₀ b₁ b₂)).external
    (Isomorphic.mergePower3 (Tensor.permute (cycle.symm.trans π) T) c₀ c₁ c₂)).trans ?_
  refine (((Isomorphic.power_congr (Tensor.permute π T) ha).external
      (Isomorphic.power_congr (Tensor.permute (cycle.trans π) T) hb)).external
    (Isomorphic.power_congr (Tensor.permute (cycle.symm.trans π) T) hc)).trans ?_
  exact (Isomorphic.power_permute_symThree_external T π m).symm

-- ELABORATION RISK: an earlier version bundled the three `regroupPeel3` applications into a local
-- `have` with its own `[AddCommMonoid]`/`[Module]` binders; that form did not elaborate at 2000000
-- heartbeats.  FALLBACK, adopted here: three explicit applications with all four arguments given.
set_option maxHeartbeats 1000000 in
/-- **The three orientations of one `C₃`-coset assemble into a bulk block and a block of cyclic
triples.**

Each oriented sub-word tensor of one coset has already been peeled into a bulk part and three
constant orbit blocks, one per tag of the coset.  The three bulks are brought together and the
nine orbit blocks become one power of `permute π (sym₃ T)`. -/
theorem Isomorphic.symSixHalf_regroup
    (T : Tensor3 K W) (π : Orientation)
    (B₀ : Tensor3 K V₀) (B₁ : Tensor3 K V₁) (B₂ : Tensor3 K V₂)
    (a₀ a₁ a₂ b₀ b₁ b₂ c₀ c₁ c₂ m : ℕ)
    (ha : a₀ + a₁ + a₂ = m + 1) (hb : b₀ + b₁ + b₂ = m + 1) (hc : c₀ + c₁ + c₂ = m + 1) :
    Isomorphic
      (Tensor.external
        (Tensor.external
          (Tensor.external
            (Tensor.external
              (Tensor.external B₀ (Tensor.power (Tensor.permute π T) a₀))
              (Tensor.power (Tensor.permute (cycle.trans π) T) b₀))
            (Tensor.power (Tensor.permute (cycle.symm.trans π) T) c₀))
          (Tensor.external
            (Tensor.external
              (Tensor.external B₁ (Tensor.power (Tensor.permute π T) a₁))
              (Tensor.power (Tensor.permute (cycle.trans π) T) b₁))
            (Tensor.power (Tensor.permute (cycle.symm.trans π) T) c₁)))
        (Tensor.external
          (Tensor.external
            (Tensor.external B₂ (Tensor.power (Tensor.permute π T) a₂))
            (Tensor.power (Tensor.permute (cycle.trans π) T) b₂))
          (Tensor.power (Tensor.permute (cycle.symm.trans π) T) c₂)))
      (Tensor.external (Tensor.external (Tensor.external B₀ B₁) B₂)
        (Tensor.power (Tensor.permute π (symThree K T)) (m + 1))) := by
  refine (((Isomorphic.regroupPeel3 B₀ (Tensor.power (Tensor.permute π T) a₀)
        (Tensor.power (Tensor.permute (cycle.trans π) T) b₀)
        (Tensor.power (Tensor.permute (cycle.symm.trans π) T) c₀)).external
      (Isomorphic.regroupPeel3 B₁ (Tensor.power (Tensor.permute π T) a₁)
        (Tensor.power (Tensor.permute (cycle.trans π) T) b₁)
        (Tensor.power (Tensor.permute (cycle.symm.trans π) T) c₁))).external
    (Isomorphic.regroupPeel3 B₂ (Tensor.power (Tensor.permute π T) a₂)
      (Tensor.power (Tensor.permute (cycle.trans π) T) b₂)
      (Tensor.power (Tensor.permute (cycle.symm.trans π) T) c₂))).trans ?_
  refine (Isomorphic.deinterleave3 B₀ _ B₁ _ B₂ _).trans ?_
  exact (Isomorphic.refl _).external
    (Isomorphic.orbitTriple_merge T π a₀ a₁ a₂ b₀ b₁ b₂ c₀ c₁ c₂ m ha hb hc)

end Half

/-! ## The weight of one `C₃`-coset half -/

section HalfWeight

variable {K : Type u} [CommSemiring K]
variable {U₀ : Leg → Type z₀} [∀ c, AddCommMonoid (U₀ c)] [∀ c, Module K (U₀ c)]
variable {U₁ : Leg → Type z₁} [∀ c, AddCommMonoid (U₁ c)] [∀ c, Module K (U₁ c)]
variable {U₂ : Leg → Type z₂} [∀ c, AddCommMonoid (U₂ c)] [∀ c, Module K (U₂ c)]
variable {V₀ : Leg → Type x₀} [∀ c, AddCommMonoid (V₀ c)] [∀ c, Module K (V₀ c)]
variable {V₁ : Leg → Type x₁} [∀ c, AddCommMonoid (V₁ c)] [∀ c, Module K (V₁ c)]
variable {V₂ : Leg → Type x₂} [∀ c, AddCommMonoid (V₂ c)] [∀ c, Module K (V₂ c)]
variable {W : Leg → Type v} [∀ c, AddCommMonoid (W c)] [∀ c, Module K (W c)]

set_option maxHeartbeats 1000000 in
/-- **The weight of one `C₃`-coset half of a six-orientation word tensor.**

Three oriented factors `Y₀, Y₁, Y₂` --- the three orientations of one coset --- each split into a
bulk part and three constant orbit blocks, one per tag of the coset.  The nine orbit blocks
transpose and merge into a single power of `permute π (sym₃ T)`, whose weight is what an orbit
certificate supplies; the three bulks keep their own weights.  Nothing about `T` is used, so the
same statement serves the even and the odd coset.

The three exponent sums must agree --- `a₀ + a₁ + a₂ = b₀ + b₁ + b₂ = c₀ + c₁ + c₂` --- and that
is exactly the statement that the three tags of the coset receive equally many oriented letters.
-/
theorem hasTauWeight_symSixHalf
    (T : Tensor3 K W) (π : Orientation) {τ : ℝ}
    (Y₀ : Tensor3 K U₀) (Y₁ : Tensor3 K U₁) (Y₂ : Tensor3 K U₂)
    (B₀ : Tensor3 K V₀) (B₁ : Tensor3 K V₁) (B₂ : Tensor3 K V₂)
    {a₀ a₁ a₂ b₀ b₁ b₂ c₀ c₁ c₂ M : ℕ}
    (hd₀ : Isomorphic Y₀
      (Tensor.external
        (Tensor.external (Tensor.external B₀ (Tensor.power (Tensor.permute π T) a₀))
          (Tensor.power (Tensor.permute (cycle.trans π) T) b₀))
        (Tensor.power (Tensor.permute (cycle.symm.trans π) T) c₀)))
    (hd₁ : Isomorphic Y₁
      (Tensor.external
        (Tensor.external (Tensor.external B₁ (Tensor.power (Tensor.permute π T) a₁))
          (Tensor.power (Tensor.permute (cycle.trans π) T) b₁))
        (Tensor.power (Tensor.permute (cycle.symm.trans π) T) c₁)))
    (hd₂ : Isomorphic Y₂
      (Tensor.external
        (Tensor.external (Tensor.external B₂ (Tensor.power (Tensor.permute π T) a₂))
          (Tensor.power (Tensor.permute (cycle.trans π) T) b₂))
        (Tensor.power (Tensor.permute (cycle.symm.trans π) T) c₂)))
    (ha : a₀ + a₁ + a₂ = M + 1) (hb : b₀ + b₁ + b₂ = M + 1) (hc : c₀ + c₁ + c₂ = M + 1)
    {bulk₀ bulk₁ bulk₂ orbitValue : ℝ}
    (hw₀ : HasTauWeight K B₀ τ bulk₀) (hw₁ : HasTauWeight K B₁ τ bulk₁)
    (hw₂ : HasTauWeight K B₂ τ bulk₂)
    (horbit : HasTauWeight K
      (Tensor.power (Tensor.permute π (symThree K T)) (M + 1)) τ orbitValue)
    (n₀ : 0 ≤ bulk₀) (n₁ : 0 ≤ bulk₁) (n₂ : 0 ≤ bulk₂) (nv : 0 ≤ orbitValue) :
    HasTauWeight K (Tensor.external (Tensor.external Y₀ Y₁) Y₂) τ
      (bulk₀ * bulk₁ * bulk₂ * orbitValue) :=
  HasTauWeight.of_restricts
    (((hd₀.external hd₁).external hd₂).trans
      (Isomorphic.symSixHalf_regroup T π B₀ B₁ B₂
        a₀ a₁ a₂ b₀ b₁ b₂ c₀ c₁ c₂ M ha hb hc)).restricts
    (HasTauWeight.external
      (HasTauWeight.external (HasTauWeight.external hw₀ hw₁ n₀ n₁) hw₂ (mul_nonneg n₀ n₁) n₂)
      horbit (mul_nonneg (mul_nonneg n₀ n₁) n₂) nv)

end HalfWeight

/-! ## The two halves -/

section Halves

variable {K : Type u} [CommSemiring K]
variable {A : Leg → Type w} [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]
variable {V : ∀ c, A c → Type (max u v)}
variable [∀ c a, AddCommMonoid (V c a)] [∀ c a, Module K (V c a)]

/-- **The weight of a six-orientation word tensor from the two `C₃`-coset halves.**

The even orientations `1, cycle, cycle⁻¹` are the left factor of `symSixPartition` and the odd
ones `s, cycle · s, cycle⁻¹ · s` the right factor, so the two cosets never have to be
interleaved: each is weighed by `hasTauWeight_symSixHalf` and the two weights multiply. -/
theorem hasTauWeight_positiveSupportWordTensor_symSix_of_halves
    (P : PartitionedTensor (K := K) (A := A) V) {τ left right : ℝ} (n : ℕ)
    (q : PositiveWord P.symSixExt.support n)
    (hleft : HasTauWeight K
      (Tensor.external
        (Tensor.external
          (PartitionedTensor.positiveSupportWordTensor P n (P.symSixWord0 n q))
          (PartitionedTensor.positiveSupportWordTensor (P.permute cycle) n
            (P.symSixWord1 n q)))
        (PartitionedTensor.positiveSupportWordTensor (P.permute cycle.symm) n
          (P.symSixWord2 n q))) τ left)
    (hright : HasTauWeight K
      (Tensor.external
        (Tensor.external
          (PartitionedTensor.positiveSupportWordTensor (P.permute swapXY) n
            (P.symSixWord3 n q))
          (PartitionedTensor.positiveSupportWordTensor (P.permute (cycle.trans swapXY)) n
            (P.symSixWord4 n q)))
        (PartitionedTensor.positiveSupportWordTensor (P.permute (cycle.symm.trans swapXY)) n
          (P.symSixWord5 n q))) τ right)
    (hl : 0 ≤ left) (hr : 0 ≤ right) :
    HasTauWeight K (PartitionedTensor.positiveSupportWordTensor P.symSixExt n q) τ
      (left * right) :=
  HasTauWeight.of_restricts
    (Isomorphic.positiveSupportWordTensor_symSixPartition P n q).restricts
    (HasTauWeight.external hleft hright hl hr)

end Halves

end AlgebraicComplexity.Tensor

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor
open scoped BigOperators

universe u v

/-! ## The retained constituent is a marked word tensor

`Examples/DuanWuZhouLevelTwoTensorSideEndpoint.lean` states `hconstituent` about
`(dwz63JointRetained …).constituent a.1` for a doubly compatibility-isolated address `a`.  The
hashing lane's `exists_markedSourceWord_of_mem_markedXYIsolatedPowerAddresses` recovers the
*marked* word underlying such an address --- exactly, not merely up to marginal type --- so the
value lane never has to reason about hashing at all: it only has to weigh the word tensor of an
arbitrary marked word.
-/

section Bridge

variable {R : Type v} [Field R] {p : ℕ} [CharP R p]

/-- The doubly compatibility-isolated support sits inside the retained support: both zero-outs are
`Finset.filter`s. -/
theorem dwz63JointIsolatedSupport_subset_retained (K : Type u) [CommRing K] (hp : 15625 ≤ p)
    (n : ℕ) (markedWords : Finset (PositiveWord ((dwz63SymSixPartition K).support) n))
    (B : Finset R) (seed : ProgressionHash.Seed R (Fin (n + 1)))
    (compat : ∀ _leg : Leg, Fin 5 → CWSquareAddress → Prop) :
    dwz63JointIsolatedSupport K hp n markedWords B seed compat ⊆
      dwz63JointRetainedSupport K hp n markedWords B seed :=
  (compatibilityIsolatedSupport_subset _ _ _).trans (compatibilityIsolatedSupport_subset _ _ _)

/-- **Every retained constituent carries whatever weight all marked word tensors carry.**

The hashing lane recovers the marked word `q` with `supportWordAddress n q = address`, and the
retained subpartition keeps the positive power's constituents untouched, so the constituent at
that address *is* `positiveSupportWordTensor (dwz63SymSixPartition K) n q`. -/
theorem dwz63_hasTauWeight_jointRetained_constituent
    (K : Type u) [CommRing K] (hp : 15625 ≤ p) (n : ℕ)
    (markedWords : Finset (PositiveWord ((dwz63SymSixPartition K).support) n))
    (B : Finset R) (seed : ProgressionHash.Seed R (Fin (n + 1))) {value : ℝ}
    (hword : ∀ q ∈ markedWords, HasTauWeight K
      (PartitionedTensor.positiveSupportWordTensor (dwz63SymSixPartition K) n q)
      dwz63Tau value)
    {address : BlockAddress fun c ↦ PositiveWord (DwzSymSixBlock c) n}
    (haddress : address ∈ dwz63JointRetainedSupport K hp n markedWords B seed) :
    HasTauWeight K ((dwz63JointRetained K hp n markedWords B seed).constituent address)
      dwz63Tau value := by
  obtain ⟨q, hq, hqa⟩ :=
    PartitionHashEncoding.exists_markedSourceWord_of_mem_markedXYIsolatedPowerAddresses
      (dwz63SymSixHashEncoding K R hp) n Finset.univ markedWords B seed haddress
  subst hqa
  show HasTauWeight K
    ((((dwz63SymSixPartition K).positivePower n).withSupport
      (dwz63JointRetainedSupport K hp n markedWords B seed)).constituent
        (positiveSupportWordBlockAddress _ n q)) dwz63Tau value
  rw [PartitionedTensor.withSupport_constituent,
    PartitionedTensor.positivePower_constituent_positiveSupportWordBlockAddress]
  exact hword q hq

/-- **The endpoint's `hconstituent`, reduced to a statement about marked words.**

This is the interface between the hashing lane and the value lane: whatever weight the value lane
can prove for the word tensor of every marked word, the endpoint's per-constituent hypothesis
holds at that weight. -/
theorem dwz63_hconstituent_of_markedWordTensor
    (K : Type u) [CommRing K] (hp : 15625 ≤ p) (n : ℕ)
    (markedWords : Finset (PositiveWord ((dwz63SymSixPartition K).support) n))
    (B : Finset R) (seed : ProgressionHash.Seed R (Fin (n + 1)))
    (compat : ∀ _leg : Leg, Fin 5 → CWSquareAddress → Prop) {value : ℝ}
    (hword : ∀ q ∈ markedWords, HasTauWeight K
      (PartitionedTensor.positiveSupportWordTensor (dwz63SymSixPartition K) n q)
      dwz63Tau value)
    (a : dwz63JointIsolatedSupport K hp n markedWords B seed compat) :
    HasTauWeight K ((dwz63JointRetained K hp n markedWords B seed).constituent a.1)
      dwz63Tau value :=
  dwz63_hasTauWeight_jointRetained_constituent K hp n markedWords B seed hword
    (dwz63JointIsolatedSupport_subset_retained K hp n markedWords B seed compat a.2)

end Bridge

/-! ## Oriented letters of the level-two coarse partition

The six oriented sub-words of `Examples/DuanWuZhouLevelTwoOrientationTypical.lean` are words over
the *permuted* coarse partitions `(cwSquarePartitionedTensor K dwz63Q).permute e`.  Their letters
are the permuted coarse addresses, and their constituents differ from the source ones by a leg
permutation --- which is free for the twelve non-rotational cells
(`hasTauWeight_permute_iff`) and is exactly the orbit tag for the three cells of the `(1,1,2)`
orbit (`dwz63RawTag`).
-/

section OrientedLetters

variable (K : Type u) [CommRing K]

/-- **A non-rotational oriented letter carries the source constituent's weight.**

`HasTauWeight.permute` is free in both directions, so the leg permutation of a six-orientation
letter costs nothing for a cell whose value is non-rotational. -/
theorem dwz63_hasTauWeight_permuted_constituent (e : Orientation) (s : CWSquareAddress)
    {value : ℝ}
    (h : HasTauWeight K ((cwSquarePartitionedTensor K dwz63Q).constituent s) dwz63Tau value) :
    HasTauWeight K
      (((cwSquarePartitionedTensor K dwz63Q).permute e).constituent
        (permuteBlockAddress e s)) dwz63Tau value :=
  (h.permute e).of_restricts
    (isomorphic_permute_partitionedPermute_constituent_apply
      (cwSquarePartitionedTensor K dwz63Q) e s).symm.restricts

/-- **An oriented orbit letter is the tag rotation of `T_(1,1,2)`.**

This is `isomorphic_permute_dwz63OrbitConstituent` read inside the permuted partition: the letter
`permuteBlockAddress e s` of `(cwSquarePartitionedTensor K dwz63Q).permute e` has constituent
isomorphic to `permute (dwz63RawTag e s) T_(1,1,2)`.  It is the form
`Isomorphic.positiveSupportWordTensor_peel3` hands to `hasTauWeight_symSixHalf`. -/
theorem dwz63_isomorphic_permuted_orbitConstituent (e : Orientation) (s : CWSquareAddress)
    (h : Isomorphic ((cwSquarePartitionedTensor K dwz63Q).constituent s)
      (Tensor.permute (dwz63OrbitRotation s)
        ((cwSquarePartitionedTensor K dwz63Q).constituent cwSquare112))) :
    Isomorphic
      (((cwSquarePartitionedTensor K dwz63Q).permute e).constituent
        (permuteBlockAddress e s))
      (Tensor.permute (dwz63RawTag e s)
        ((cwSquarePartitionedTensor K dwz63Q).constituent cwSquare112)) :=
  (isomorphic_permute_partitionedPermute_constituent_apply
      (cwSquarePartitionedTensor K dwz63Q) e s).symm.trans
    (isomorphic_permute_dwz63OrbitConstituent K e s h)

/-- The `(1,1,2)` oriented letter, at tag `dwz63RawTag e cwSquare112`. -/
theorem dwz63_isomorphic_permuted_orbitConstituent_112 (e : Orientation) :
    Isomorphic
      (((cwSquarePartitionedTensor K dwz63Q).permute e).constituent
        (permuteBlockAddress e cwSquare112))
      (Tensor.permute (dwz63RawTag e cwSquare112)
        ((cwSquarePartitionedTensor K dwz63Q).constituent cwSquare112)) :=
  dwz63_isomorphic_permuted_orbitConstituent K e cwSquare112
    (isomorphic_dwz63OrbitConstituent_112 K)

/-- The `(1,2,1)` oriented letter, at tag `dwz63RawTag e cwSquare121`. -/
theorem dwz63_isomorphic_permuted_orbitConstituent_121 (e : Orientation) :
    Isomorphic
      (((cwSquarePartitionedTensor K dwz63Q).permute e).constituent
        (permuteBlockAddress e cwSquare121))
      (Tensor.permute (dwz63RawTag e cwSquare121)
        ((cwSquarePartitionedTensor K dwz63Q).constituent cwSquare112)) :=
  dwz63_isomorphic_permuted_orbitConstituent K e cwSquare121
    (isomorphic_dwz63OrbitConstituent_121 K)

/-- The `(2,1,1)` oriented letter, at tag `dwz63RawTag e cwSquare211`. -/
theorem dwz63_isomorphic_permuted_orbitConstituent_211 (e : Orientation) :
    Isomorphic
      (((cwSquarePartitionedTensor K dwz63Q).permute e).constituent
        (permuteBlockAddress e cwSquare211))
      (Tensor.permute (dwz63RawTag e cwSquare211)
        ((cwSquarePartitionedTensor K dwz63Q).constituent cwSquare112)) :=
  dwz63_isomorphic_permuted_orbitConstituent K e cwSquare211
    (isomorphic_dwz63OrbitConstituent_211 K)

/-- **The weight of a marked word's constituent from the two `C₃`-coset halves**, at the level-two
six-orientation partition.

The DWZ-facing form of `hasTauWeight_positiveSupportWordTensor_symSix_of_halves`: the endpoint's
partition is `dwz63SymSixPartition K`, and the two halves are the even and the odd coset of leg
permutations. -/
theorem dwz63_hasTauWeight_symSixWordTensor_of_halves {left right : ℝ} (n : ℕ)
    (q : PositiveWord ((dwz63SymSixPartition K).support) n)
    (hleft : HasTauWeight K
      (Tensor.external
        (Tensor.external
          (PartitionedTensor.positiveSupportWordTensor (cwSquarePartitionedTensor K dwz63Q) n
            ((cwSquarePartitionedTensor K dwz63Q).symSixWord0 n q))
          (PartitionedTensor.positiveSupportWordTensor
            ((cwSquarePartitionedTensor K dwz63Q).permute cycle) n
            ((cwSquarePartitionedTensor K dwz63Q).symSixWord1 n q)))
        (PartitionedTensor.positiveSupportWordTensor
          ((cwSquarePartitionedTensor K dwz63Q).permute cycle.symm) n
          ((cwSquarePartitionedTensor K dwz63Q).symSixWord2 n q))) dwz63Tau left)
    (hright : HasTauWeight K
      (Tensor.external
        (Tensor.external
          (PartitionedTensor.positiveSupportWordTensor
            ((cwSquarePartitionedTensor K dwz63Q).permute swapXY) n
            ((cwSquarePartitionedTensor K dwz63Q).symSixWord3 n q))
          (PartitionedTensor.positiveSupportWordTensor
            ((cwSquarePartitionedTensor K dwz63Q).permute (cycle.trans swapXY)) n
            ((cwSquarePartitionedTensor K dwz63Q).symSixWord4 n q)))
        (PartitionedTensor.positiveSupportWordTensor
          ((cwSquarePartitionedTensor K dwz63Q).permute (cycle.symm.trans swapXY)) n
          ((cwSquarePartitionedTensor K dwz63Q).symSixWord5 n q))) dwz63Tau right)
    (hl : 0 ≤ left) (hr : 0 ≤ right) :
    HasTauWeight K
      (PartitionedTensor.positiveSupportWordTensor (dwz63SymSixPartition K) n q)
      dwz63Tau (left * right) :=
  hasTauWeight_positiveSupportWordTensor_symSix_of_halves
    (cwSquarePartitionedTensor K dwz63Q) n q hleft hright hl hr

end OrientedLetters

/-! ## Target-coordinate sub-words and their multiplicities

Under the target-coordinate typicality convention the count lane measures the `o`-th component of
a `symSixPartition` block label *as it sits* in `PermutedBlockIndex e_o` --- no transport back to
the source address space.  Those six words are exactly the underlying words of the six oriented
sub-words `symSixWord0 … symSixWord5`, so the multiplicity bridge is a single application of
`multiplicity_of_injective` at `Subtype.val`.
-/

section TargetWords

variable {K : Type u} [CommRing K]

-- ELABORATION RISK: the six bridges below reduce the count lane's `dwz63TargetLetter o` at a
-- `Fin 6` literal, which is a `Matrix.cons` chain; the last three cost more than the default
-- heartbeat budget.  FALLBACK if raising the limit stops working: use
-- `dwz63TargetLetter_apply` of `Examples/DuanWuZhouLevelTwoSixOrientationDigits.lean`, which
-- states the reduction at a general `o` through `dwz63SymSixDigit`.
set_option maxHeartbeats 1000000 in
/-- Multiplicities of the identity-orientation sub-word are those of the `0`-th target word. -/
theorem dwz63_multiplicity_symSixWord0 (n : ℕ)
    (q : PositiveWord ((dwz63SymSixPartition K).support) n)
    (s : (cwSquarePartitionedTensor K dwz63Q).support) :
    WordType.multiplicity (positiveWordEquiv _ n
        ((cwSquarePartitionedTensor K dwz63Q).symSixWord0 n q)) s =
      WordType.multiplicity (dwz63TargetWord K n 0 q) s.1 := by
  have hword : (Subtype.val ∘ positiveWordEquiv _ n
      ((cwSquarePartitionedTensor K dwz63Q).symSixWord0 n q)) =
      dwz63TargetWord K n 0 q := by
    funext j
    exact PartitionedTensor.symSixWord0_letter (cwSquarePartitionedTensor K dwz63Q) n q j
  rw [Tensor.multiplicity_of_injective Subtype.val Subtype.val_injective _ s, hword]

set_option maxHeartbeats 1000000 in
/-- Multiplicities of the `cycle` sub-word are those of the `1`-st target word. -/
theorem dwz63_multiplicity_symSixWord1 (n : ℕ)
    (q : PositiveWord ((dwz63SymSixPartition K).support) n)
    (s : ((cwSquarePartitionedTensor K dwz63Q).permute cycle).support) :
    WordType.multiplicity (positiveWordEquiv _ n
        ((cwSquarePartitionedTensor K dwz63Q).symSixWord1 n q)) s =
      WordType.multiplicity (dwz63TargetWord K n 1 q) s.1 := by
  have hword : (Subtype.val ∘ positiveWordEquiv _ n
      ((cwSquarePartitionedTensor K dwz63Q).symSixWord1 n q)) =
      dwz63TargetWord K n 1 q := by
    funext j
    exact PartitionedTensor.symSixWord1_letter (cwSquarePartitionedTensor K dwz63Q) n q j
  rw [Tensor.multiplicity_of_injective Subtype.val Subtype.val_injective _ s, hword]

set_option maxHeartbeats 1000000 in
/-- Multiplicities of the `cycle⁻¹` sub-word are those of the `2`-nd target word. -/
theorem dwz63_multiplicity_symSixWord2 (n : ℕ)
    (q : PositiveWord ((dwz63SymSixPartition K).support) n)
    (s : ((cwSquarePartitionedTensor K dwz63Q).permute cycle.symm).support) :
    WordType.multiplicity (positiveWordEquiv _ n
        ((cwSquarePartitionedTensor K dwz63Q).symSixWord2 n q)) s =
      WordType.multiplicity (dwz63TargetWord K n 2 q) s.1 := by
  have hword : (Subtype.val ∘ positiveWordEquiv _ n
      ((cwSquarePartitionedTensor K dwz63Q).symSixWord2 n q)) =
      dwz63TargetWord K n 2 q := by
    funext j
    exact PartitionedTensor.symSixWord2_letter (cwSquarePartitionedTensor K dwz63Q) n q j
  rw [Tensor.multiplicity_of_injective Subtype.val Subtype.val_injective _ s, hword]

set_option maxHeartbeats 1000000 in
/-- Multiplicities of the `swapXY` sub-word are those of the `3`-rd target word. -/
theorem dwz63_multiplicity_symSixWord3 (n : ℕ)
    (q : PositiveWord ((dwz63SymSixPartition K).support) n)
    (s : ((cwSquarePartitionedTensor K dwz63Q).permute swapXY).support) :
    WordType.multiplicity (positiveWordEquiv _ n
        ((cwSquarePartitionedTensor K dwz63Q).symSixWord3 n q)) s =
      WordType.multiplicity (dwz63TargetWord K n 3 q) s.1 := by
  have hword : (Subtype.val ∘ positiveWordEquiv _ n
      ((cwSquarePartitionedTensor K dwz63Q).symSixWord3 n q)) =
      dwz63TargetWord K n 3 q := by
    funext j
    exact PartitionedTensor.symSixWord3_letter (cwSquarePartitionedTensor K dwz63Q) n q j
  rw [Tensor.multiplicity_of_injective Subtype.val Subtype.val_injective _ s, hword]

set_option maxHeartbeats 1000000 in
/-- Multiplicities of the `cycle · swapXY` sub-word are those of the `4`-th target word. -/
theorem dwz63_multiplicity_symSixWord4 (n : ℕ)
    (q : PositiveWord ((dwz63SymSixPartition K).support) n)
    (s : ((cwSquarePartitionedTensor K dwz63Q).permute (cycle.trans swapXY)).support) :
    WordType.multiplicity (positiveWordEquiv _ n
        ((cwSquarePartitionedTensor K dwz63Q).symSixWord4 n q)) s =
      WordType.multiplicity (dwz63TargetWord K n 4 q) s.1 := by
  have hword : (Subtype.val ∘ positiveWordEquiv _ n
      ((cwSquarePartitionedTensor K dwz63Q).symSixWord4 n q)) =
      dwz63TargetWord K n 4 q := by
    funext j
    exact PartitionedTensor.symSixWord4_letter (cwSquarePartitionedTensor K dwz63Q) n q j
  rw [Tensor.multiplicity_of_injective Subtype.val Subtype.val_injective _ s, hword]

set_option maxHeartbeats 1000000 in
/-- Multiplicities of the `cycle⁻¹ · swapXY` sub-word are those of the `5`-th target word. -/
theorem dwz63_multiplicity_symSixWord5 (n : ℕ)
    (q : PositiveWord ((dwz63SymSixPartition K).support) n)
    (s : ((cwSquarePartitionedTensor K dwz63Q).permute (cycle.symm.trans swapXY)).support) :
    WordType.multiplicity (positiveWordEquiv _ n
        ((cwSquarePartitionedTensor K dwz63Q).symSixWord5 n q)) s =
      WordType.multiplicity (dwz63TargetWord K n 5 q) s.1 := by
  have hword : (Subtype.val ∘ positiveWordEquiv _ n
      ((cwSquarePartitionedTensor K dwz63Q).symSixWord5 n q)) =
      dwz63TargetWord K n 5 q := by
    funext j
    exact PartitionedTensor.symSixWord5_letter (cwSquarePartitionedTensor K dwz63Q) n q j
  rw [Tensor.multiplicity_of_injective Subtype.val Subtype.val_injective _ s, hword]

end TargetWords

end AlgebraicComplexity.Examples
