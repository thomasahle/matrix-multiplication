/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.PartitionedTypeAssembly
import AlgebraicComplexity.MatrixMultiplication.TauValueDirectSum

/-!
# Splitting and reordering a word of constituents

Layer 3 (`AlgebraicComplexity/MatrixMultiplication/`).  A retained block of a partitioned positive
power is `PartitionedTensor.positiveSupportWordTensor P r q`, the iterated external product of the
constituents named by the word `q`.  A values client rarely has a weight for a *single* letter: it
has certificates for *groups* --- three cyclically related letters assembling into `sym_3` of one
constituent, or `M` copies of one letter assembling into a power.  Using them requires two moves
this module supplies.

* **Split.** The committed `PartitionedTensor.Isomorphic.positiveSupportWordTensor_append`
  (`Tensor/PartitionedPower.lean`) --- a word that is a concatenation splits, as an isomorphism,
  into the external product of its two parts.  This is not an equality: the recursive word tensor
  is left-associated, so each step costs one reassociation.  It is stated there in the direction
  `external ... ≅ wordTensor ...`, so the weight-level forms below apply it through `.symm`.
* **Reorder.** `Tensor.Isomorphic.positiveSupportWordTensor_of_same_type` --- two words with the
  same letter multiplicities have isomorphic word tensors, so a client may permute positions freely
  before splitting.  The underlying position relabeling is the committed
  `Tensor.Isomorphic.positivePower_constituent_of_same_type`; all that is added here is its
  transport across `positivePower_constituent_positiveSupportWordBlockAddress`.

Together: rearrange the word so that each intended group occupies a consecutive block, then split
repeatedly, then apply the group certificates.  `hasTauWeight_wordTensor_append` and
`hasTauWeight_wordTensor_of_sameType` are the weight-level forms, and
`hasTauWeight_wordTensor_append_three` is the three-block convenience.

## Non-goals

No distribution, no counting, and no claim that a word of a prescribed type exists.  The `k`-fold
assembly is left to the client as an iteration of the binary split: the lengths of `k` groups sum
dependently, and packaging that sum costs more than the two-line induction it saves.
-/

namespace AlgebraicComplexity

open Tensor

universe u v w

variable {K : Type u} [CommSemiring K]
variable {A : Leg → Type w} [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]
variable {V : ∀ c, A c → Type (max u v)}
variable [∀ c a, AddCommMonoid (V c a)] [∀ c a, Module K (V c a)]

/-! ## Splitting a concatenated word

The isomorphism itself is committed as
`Tensor.PartitionedTensor.Isomorphic.positiveSupportWordTensor_append`
(`Tensor/PartitionedPower.lean`), stated as `external ... ≅ wordTensor ...`; this module supplies
only the weight-level consequences, applying it through `.symm`. -/

/-- **Weights multiply across a concatenation.** -/
theorem hasTauWeight_wordTensor_append
    (P : PartitionedTensor (K := K) (A := A) V) {τ a b : ℝ} {n m : ℕ}
    (left : PositiveWord P.support n) (right : PositiveWord P.support m)
    (hleft : HasTauWeight K (PartitionedTensor.positiveSupportWordTensor P n left) τ a)
    (hright : HasTauWeight K (PartitionedTensor.positiveSupportWordTensor P m right) τ b)
    (ha : 0 ≤ a) (hb : 0 ≤ b) :
    HasTauWeight K
      (PartitionedTensor.positiveSupportWordTensor P (n + m + 1)
        (positiveWordAppend left m right)) τ (a * b) :=
  HasTauWeight.of_restricts
    (PartitionedTensor.Isomorphic.positiveSupportWordTensor_append P left right).symm.restricts
    (HasTauWeight.external hleft hright ha hb)

/-- Three consecutive blocks, the shape an orbit regrouping produces: a bulk of ungrouped letters
followed by two certificate classes. -/
theorem hasTauWeight_wordTensor_append_three
    (P : PartitionedTensor (K := K) (A := A) V) {τ a b c : ℝ} {n m l : ℕ}
    (first : PositiveWord P.support n) (second : PositiveWord P.support m)
    (third : PositiveWord P.support l)
    (hfirst : HasTauWeight K (PartitionedTensor.positiveSupportWordTensor P n first) τ a)
    (hsecond : HasTauWeight K (PartitionedTensor.positiveSupportWordTensor P m second) τ b)
    (hthird : HasTauWeight K (PartitionedTensor.positiveSupportWordTensor P l third) τ c)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    HasTauWeight K
      (PartitionedTensor.positiveSupportWordTensor P (n + (m + l + 1) + 1)
        (positiveWordAppend first (m + l + 1) (positiveWordAppend second l third))) τ
      (a * (b * c)) :=
  hasTauWeight_wordTensor_append P first (positiveWordAppend second l third) hfirst
    (hasTauWeight_wordTensor_append P second third hsecond hthird hb hc) ha (mul_nonneg hb hc)

/-! ## Reordering a word -/

namespace Tensor

/-- **Words with the same letter multiplicities have isomorphic word tensors.**

So a client may permute the positions of a retained block freely --- in particular, gather the
letters intended for one group certificate into a consecutive run --- before splitting. -/
theorem Isomorphic.positiveSupportWordTensor_of_same_type
    (P : PartitionedTensor (K := K) (A := A) V) (r : ℕ)
    (left right : PositiveWord P.support r)
    (htype : WordType.multiplicity (positiveWordEquiv P.support r left) =
      WordType.multiplicity (positiveWordEquiv P.support r right)) :
    Isomorphic (PartitionedTensor.positiveSupportWordTensor P r left)
      (PartitionedTensor.positiveSupportWordTensor P r right) := by
  have h := Tensor.Isomorphic.positivePower_constituent_of_same_type P r left right htype
  rwa [P.positivePower_constituent_positiveSupportWordBlockAddress r left,
    P.positivePower_constituent_positiveSupportWordBlockAddress r right] at h

end Tensor

/-- **A weight transports along a reordering of the word.** -/
theorem hasTauWeight_wordTensor_of_sameType
    (P : PartitionedTensor (K := K) (A := A) V) {τ value : ℝ} (r : ℕ)
    (left right : PositiveWord P.support r)
    (htype : WordType.multiplicity (positiveWordEquiv P.support r left) =
      WordType.multiplicity (positiveWordEquiv P.support r right))
    (h : HasTauWeight K (PartitionedTensor.positiveSupportWordTensor P r right) τ value) :
    HasTauWeight K (PartitionedTensor.positiveSupportWordTensor P r left) τ value :=
  HasTauWeight.of_restricts
    (Tensor.Isomorphic.positiveSupportWordTensor_of_same_type P r left right htype).restricts h


/-! ## Splitting a word along any rearrangement -/

namespace Tensor

/-- **Split a word into two blocks along any rearrangement of its letters.**

The hypothesis is the whole content of "split by a predicate": exhibit the two intended blocks and
check that their concatenation has the same letter multiset as the original word.  Reordering is
then free (`Isomorphic.positiveSupportWordTensor_of_same_type`) and the concatenation splits
(the committed `PartitionedTensor.Isomorphic.positiveSupportWordTensor_append`, applied through
`.symm`).

Stating it this way avoids building the symmetric-monoidal coherence for an abstract family
`Fin m -> Tensor3 K (V ·)`: the letters of a retained block are drawn from a partition's support,
and for those the committed `Tensor.Isomorphic.positivePower_constituent_of_same_type` already
supplies every position permutation. -/
theorem Isomorphic.positiveSupportWordTensor_split
    (P : PartitionedTensor (K := K) (A := A) V) {n m : ℕ}
    (q : PositiveWord P.support (n + m + 1))
    (left : PositiveWord P.support n) (right : PositiveWord P.support m)
    (hmult : WordType.multiplicity (positiveWordEquiv P.support (n + m + 1) q) =
      WordType.multiplicity
        (positiveWordEquiv P.support (n + m + 1) (positiveWordAppend left m right))) :
    Isomorphic (PartitionedTensor.positiveSupportWordTensor P (n + m + 1) q)
      (Tensor.external (PartitionedTensor.positiveSupportWordTensor P n left)
        (PartitionedTensor.positiveSupportWordTensor P m right)) :=
  (Isomorphic.positiveSupportWordTensor_of_same_type P (n + m + 1) q
      (positiveWordAppend left m right) hmult).trans
    (PartitionedTensor.Isomorphic.positiveSupportWordTensor_append P left right).symm

end Tensor

/-- **Weights multiply across any rearrangement into two blocks.**  This is the form an orbit
regrouping uses: gather the letters of one certificate class anywhere in the word, check the
multiset, and multiply the two weights. -/
theorem hasTauWeight_wordTensor_split
    (P : PartitionedTensor (K := K) (A := A) V) {τ a b : ℝ} {n m : ℕ}
    (q : PositiveWord P.support (n + m + 1))
    (left : PositiveWord P.support n) (right : PositiveWord P.support m)
    (hmult : WordType.multiplicity (positiveWordEquiv P.support (n + m + 1) q) =
      WordType.multiplicity
        (positiveWordEquiv P.support (n + m + 1) (positiveWordAppend left m right)))
    (hleft : HasTauWeight K (PartitionedTensor.positiveSupportWordTensor P n left) τ a)
    (hright : HasTauWeight K (PartitionedTensor.positiveSupportWordTensor P m right) τ b)
    (ha : 0 ≤ a) (hb : 0 ≤ b) :
    HasTauWeight K (PartitionedTensor.positiveSupportWordTensor P (n + m + 1) q) τ (a * b) :=
  HasTauWeight.of_restricts
    (Tensor.Isomorphic.positiveSupportWordTensor_split P q left right hmult).restricts
    (HasTauWeight.external hleft hright ha hb)


end AlgebraicComplexity