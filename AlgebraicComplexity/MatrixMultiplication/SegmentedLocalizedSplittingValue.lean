/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.RestrictedSplittingValue
import AlgebraicComplexity.MatrixMultiplication.SegmentedLocalizedHoleRepair
import AlgebraicComplexity.MatrixMultiplication.SymSixUniformLeaf

set_option autoImplicit false

/-!
# The value law for segmented localized splitting powers

Layer 3 (`AlgebraicComplexity/MatrixMultiplication/`).  `RestrictedSplittingValue.lean` proves the
value law for `restrictedSplittingPower`: one `tau`-weight on the iterated external product of a
word's constituents transports to the realization of the split power.
`MatrixMultiplication/SegmentedLocalizedHoleRepair.lean` introduces a **sibling** cut of the same
ambient positive power,

`segmentedLocalizedSplittingPower f n m seg profile target
   = (P.positivePower n).select (segmentedLocalizedKeep f seg profile target)`,

whose keep predicate is "lies over the coarse address `target`" **and** "meets the per-segment
types", against `restrictedSplittingPower`'s single pooled type.  No value law was stated for it,
and none of `restrictedSplittingPower`'s transfers across: the two are different `select`s, related
by no lemma.

This module supplies the missing law.  Nothing new is proved --- every ingredient is already
generic --- and the proof is `hasTauWeight_restrictedSplittingPower_of_wordTensor`
(`RestrictedSplittingValue.lean:183`) line for line, with

* `mem_restrictedSplittingPower_support` replaced by
  `mem_segmentedLocalizedSplittingPower_support`, and
* `restrictedSplittingPower_constituent` replaced by `rfl`, since
  `PartitionedTensor.select` keeps the ambient `constituent` field untouched.

## Why the `sym₆` form is here too

`[DuanWuZhou2022]`'s value functional is `V^{(6)}`, so a client weighing a localized leaf needs the
weight of `sym₆` of the realization, not of the realization.  `Restricts.symSix_congr`
(`MatrixMultiplication/SymSixUniformLeaf.lean`) makes `sym₆` functorial for restrictions, so the
same block extraction serves both: the leaf's `sym₆`-weight is the `sym₆`-weight of the word
tensor, with no extra hypothesis.

## What this does **not** supply

The hypothesis is still a weight of the *word tensor over the base partition* `P`.  For
`[DuanWuZhou2022]`'s reference leaf that base partition is the **raw** square
`(cwPartitionedTensor K q).positivePower 1`, whose blocks are fine letters `PositiveWord CWBlock 1`
--- not the coarse square, whose fifteen cell values are what
`Examples/DuanWuZhouLevelTwoConstituentValues.lean` computes.  Supplying that word weight is
**not** a route to `[DuanWuZhou2022]`'s restricted-splitting values, and this is not a gap that a
better choice of word can close.  A weight of the word tensor over the base partition delivers at
most the product of the letters' matrix-multiplication volumes; it loses the split entropies of
Definition 2.14, the `(4 * 2 ^ H₂) ^ (1/3)` count factors of `lem:non-rot-values` (d), and the
shared-leg merges that turn `q ^ τ` into `(2q) ^ τ` and `(q²) ^ τ` into `(q² + 2) ^ τ`.  The
one-word floor falls short of the paper's values by roughly **0.35 to 0.40 nats per letter**,
depending on how the split entropy, the orbit count factor and the shared-leg merges are
attributed; two independent computations agree the shortfall exceeds section 6.3's slack of about
`1.7 * 10 ^ (-7)` nats by six orders of magnitude, and it is independent of which word is chosen.
The values must come from `Examples/DuanWuZhouLevelTwoConstituentValues.lean`.

Primary source: Ran Duan, Hongxun Wu and Renfei Zhou, *Faster Matrix Multiplication via Asymmetric
Hashing*, arXiv:2210.10173, section 6 and `hole_lemma.tex`.
-/

namespace AlgebraicComplexity

open Tensor

universe u v w x

section SegmentedLocalizedValue

variable {K : Type u} [CommSemiring K]
variable {A : Leg → Type w} {B : Leg → Type x}
variable [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]
variable [∀ c, Fintype (B c)] [∀ c, DecidableEq (B c)]
variable {V : ∀ c, A c → Type (max u v)}
variable [∀ c a, AddCommMonoid (V c a)] [∀ c a, Module K (V c a)]

omit [∀ c, Fintype (B c)] [∀ c, DecidableEq (B c)] in
/-- **The word address of a localized split power is supported.**  The two halves of
`segmentedLocalizedKeep`, plus membership in the ambient positive power. -/
theorem mem_segmentedLocalizedSplittingPower_support_of_word
    (P : PartitionedTensor (K := K) (A := A) V)
    (f : ∀ c, A c → B c) (n m : ℕ) (seg : Fin (n + 1) → Fin m)
    (profile : SegmentedSplitRestriction A m)
    (target : BlockAddress (fun c ↦ PositiveWord (B c) n))
    (q : PositiveWord P.support n)
    (hkeeps : ∀ c,
      positiveWordMap (f c) n (positiveSupportWordBlockAddress P.support n q c) = target c ∧
        profile.Keeps n seg c (positiveSupportWordBlockAddress P.support n q c)) :
    positiveSupportWordBlockAddress P.support n q ∈
      (P.segmentedLocalizedSplittingPower f n m seg profile target).support := by
  classical
  have hpower : positiveSupportWordBlockAddress P.support n q ∈ (P.positivePower n).support := by
    rw [P.positivePower_support_eq_image_positiveSupportWordBlockAddress n]
    exact Finset.mem_image_of_mem _ (Finset.mem_univ q)
  rw [PartitionedTensor.mem_segmentedLocalizedSplittingPower_support]
  exact ⟨hpower, hkeeps⟩

/-- **The value law for segmented localized splitting powers.**

The exact analogue of `hasTauWeight_restrictedSplittingPower_of_wordTensor`: one weight on the
iterated external product of the word's constituents, transported by block extraction.  The
hypothesis absorbs every way a client may group the letters --- letterwise, in blocks, or as a
`Tensor.power` of a repeated letter --- because it is stated on the word tensor itself. -/
theorem hasTauWeight_segmentedLocalizedSplittingPower_of_wordTensor
    (P : PartitionedTensor (K := K) (A := A) V) {τ weight : ℝ}
    (f : ∀ c, A c → B c) (n m : ℕ) (seg : Fin (n + 1) → Fin m)
    (profile : SegmentedSplitRestriction A m)
    (target : BlockAddress (fun c ↦ PositiveWord (B c) n))
    (q : PositiveWord P.support n)
    (hkeeps : ∀ c,
      positiveWordMap (f c) n (positiveSupportWordBlockAddress P.support n q c) = target c ∧
        profile.Keeps n seg c (positiveSupportWordBlockAddress P.support n q c))
    (hword : HasTauWeight K (PartitionedTensor.positiveSupportWordTensor P n q) τ weight) :
    HasTauWeight K
      (P.segmentedLocalizedSplittingPower f n m seg profile target).realize τ weight := by
  classical
  refine HasTauWeight.of_restricts
    (Tensor.Restricts.partitionedConstituent
      (P.segmentedLocalizedSplittingPower f n m seg profile target) _
      (mem_segmentedLocalizedSplittingPower_support_of_word P f n m seg profile target q
        hkeeps)) ?_
  rw [show (P.segmentedLocalizedSplittingPower f n m seg profile target).constituent =
      (P.positivePower n).constituent from rfl,
    P.positivePower_constituent_positiveSupportWordBlockAddress n q]
  exact hword

/-- **The `sym₆` form**, which is what `[DuanWuZhou2022]`'s value functional `V^{(6)}` needs.

`Restricts.symSix_congr` transports the block extraction under `sym₆`, so no hypothesis beyond the
`sym₆`-weight of the word tensor is required. -/
theorem hasTauWeight_symSix_segmentedLocalizedSplittingPower_of_wordTensor
    (P : PartitionedTensor (K := K) (A := A) V) {τ weight : ℝ}
    (f : ∀ c, A c → B c) (n m : ℕ) (seg : Fin (n + 1) → Fin m)
    (profile : SegmentedSplitRestriction A m)
    (target : BlockAddress (fun c ↦ PositiveWord (B c) n))
    (q : PositiveWord P.support n)
    (hkeeps : ∀ c,
      positiveWordMap (f c) n (positiveSupportWordBlockAddress P.support n q c) = target c ∧
        profile.Keeps n seg c (positiveSupportWordBlockAddress P.support n q c))
    (hword : HasTauWeight K
      (symSix K (PartitionedTensor.positiveSupportWordTensor P n q)) τ weight) :
    HasTauWeight K
      (symSix K (P.segmentedLocalizedSplittingPower f n m seg profile target).realize)
      τ weight := by
  classical
  refine HasTauWeight.of_restricts
    (Tensor.Restricts.symSix_congr
      (Tensor.Restricts.partitionedConstituent
        (P.segmentedLocalizedSplittingPower f n m seg profile target) _
        (mem_segmentedLocalizedSplittingPower_support_of_word P f n m seg profile target q
          hkeeps))) ?_
  rw [show (P.segmentedLocalizedSplittingPower f n m seg profile target).constituent =
      (P.positivePower n).constituent from rfl,
    P.positivePower_constituent_positiveSupportWordBlockAddress n q]
  exact hword

/-- **The value law from per-constituent weights.**  The analogue of
`hasTauWeight_restrictedSplittingPower`: the product weight along the word. -/
theorem hasTauWeight_segmentedLocalizedSplittingPower
    (P : PartitionedTensor (K := K) (A := A) V) {τ : ℝ} {value : P.support → ℝ}
    (hvalue : ∀ s, 0 ≤ value s)
    (h : ∀ s : P.support, HasTauWeight K (P.constituent s.1) τ (value s))
    (f : ∀ c, A c → B c) (n m : ℕ) (seg : Fin (n + 1) → Fin m)
    (profile : SegmentedSplitRestriction A m)
    (target : BlockAddress (fun c ↦ PositiveWord (B c) n))
    (q : PositiveWord P.support n)
    (hkeeps : ∀ c,
      positiveWordMap (f c) n (positiveSupportWordBlockAddress P.support n q c) = target c ∧
        profile.Keeps n seg c (positiveSupportWordBlockAddress P.support n q c)) :
    HasTauWeight K
      (P.segmentedLocalizedSplittingPower f n m seg profile target).realize τ
      (positiveSupportWordWeight value n q) :=
  hasTauWeight_segmentedLocalizedSplittingPower_of_wordTensor P f n m seg profile target q hkeeps
    (hasTauWeight_wordTensor P hvalue h n q)

end SegmentedLocalizedValue

end AlgebraicComplexity
