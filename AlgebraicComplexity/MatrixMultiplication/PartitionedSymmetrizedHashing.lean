/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.MarkedXYPartitionedPowerHashing
import AlgebraicComplexity.Tensor.PartitionedPermutation

/-!
# One hashing seed for a product of permuted partitions

Layer 3 (`AlgebraicComplexity/MatrixMultiplication/`).  `MatrixMultiplication/PartitionedPowerHashing.lean`
hashes a partitioned tensor power through a `PartitionHashEncoding`: an injective field labelling
of each leg's block alphabet whose three labels add up to one constant on every supported address.
`MatrixMultiplication/MarkedXYPartitionedPowerHashing.lean` then selects, for one affine seed, a
marked family of block-word addresses isolated on the `X` and `Y` legs.

Both are stated for an *arbitrary* block-label family `A : Leg → Type w`, so they already apply to
a product family `ProductBlockIndex A B` or a permuted family `PermutedBlockIndex e A`.  What was
missing is the *input*: nothing produced a `PartitionHashEncoding` for such a composite support out
of encodings of its factors, and without one the six orientations of `[DuanWuZhou2022]`'s §6
cannot be hashed by a single seed.

## The mixed-radix construction

A field-valued encoding cannot be composed directly: a sum of six field labels is not injective in
the six-tuple.  `NatBlockEncoding` therefore carries the encoding in `ℕ` together with the radix
bound it respects,

* `code c a < alphabet` on every leg, and
* `code .X (s .X) + code .Y (s .Y) + code .Z (s .Z) = natTarget` on every supported address,

which is exactly enough structure to *compose*:

* `NatBlockEncoding.permute` relabels the legs by an orientation.  The alphabet, the radix bound
  and the constant target are unchanged, because the legality condition is a sum over all three
  legs and is therefore permutation invariant (`leg_add_three_comp_equiv`).
* `NatBlockEncoding.external` reads the pair `(a, b)` as the two digits `a + alphabet · b` of one
  mixed-radix numeral.  Injectivity is the uniqueness of base-`alphabet` digits, and the target
  adds in the same mixed-radix way.

`NatBlockEncoding.toPartitionHashEncoding` then casts into any field whose characteristic is at
least the composite alphabet size, so a six-fold composite needs `alphabet₀ ^ 6 ≤ p` — a constant
in the word length, which the prime-field sizing of `Combinatorics/PrimeFieldSizing.lean` absorbs.

## What the seed then buys

`PartitionHashEncoding.restricts_positivePower_to_markedXYIsolated` and
`PartitionHashEncoding.exists_seed_markedXYIsolated_positivePower` package the marked two-leg
extraction for the positive power of *any* partitioned tensor whose support carries an encoding:
one seed produces a retained subpartition together with the `X`-injectivity certificate consumed
as `hX` by
`AsymmetricGlobal.Tensor.Restricts.partitionedYZCompatibilityCleanup_to_repairedRestrictedSplittingDirectSum`,
and a lower bound on the retained count against the *marked* family.  Applied to a six-orientation
product partition this is `[DuanWuZhou2022]` §6's joint hash; nothing in this module mentions a
distribution, a numerical parameter, or a Coppersmith--Winograd datum.

## Uniform batching

`uniformBatch` cuts a finite index type into `m` batches of at least `k` elements each.  It is the
generic producer of the engine's `batch`/`hbatch` pair, and the fiber lower bound
`le_card_uniformBatch_fiber` is what turns `AsymmetricGlobal.holeBudget_of_eight_mul_card_le`'s
copy condition `8(ℓ(n+1) + 1) ≤ 7s` into a statement about batches.

Primary source: Ran Duan, Hongxun Wu and Renfei Zhou, *Faster Matrix Multiplication via Asymmetric
Hashing*, arXiv:2210.10173, §6.
-/

namespace AlgebraicComplexity

open Tensor
open scoped BigOperators

universe u v w x

/-! ## Sums over the three legs

The three-leg sum is the committed `Tensor.sum_leg` (`Tensor/Basic.lean`), stated in the
direction `∑ c, f c = f .X + f .Y + f .Z`; it is used below through `←`. -/

/-- **The three-leg sum is orientation invariant.**  This is the whole reason a leg permutation
transports a hashing encoding without changing its constant target. -/
theorem leg_add_three_comp_equiv {M : Type*} [AddCommMonoid M] (e : Orientation) (f : Leg → M) :
    f (e .X) + f (e .Y) + f (e .Z) = f .X + f .Y + f .Z := by
  rw [← Tensor.sum_leg (fun c ↦ f (e c)), ← Tensor.sum_leg f]
  exact Equiv.sum_comp e f

/-! ## Natural-number block encodings -/

/-- **A mixed-radix natural-number encoding of a finite partition support.**

`code` labels each leg's block alphabet injectively by naturals below the common radix
`alphabet`, and the three labels of a supported address add up to the constant `natTarget`.  This
is the composable form of `PartitionHashEncoding`: the field-valued version cannot be composed
because a sum of field labels is not injective in its summands, while base-`alphabet` digits
are. -/
structure NatBlockEncoding {A : Leg → Type w} (support : Finset (BlockAddress A)) where
  /-- The natural-number label of a block on each leg. -/
  code : ∀ c, A c → ℕ
  /-- The common radix: every label is strictly below it. -/
  alphabet : ℕ
  /-- The constant coordinate sum of the three labels of a supported address. -/
  natTarget : ℕ
  /-- The support is nonempty, as `PartitionHashEncoding` requires. -/
  support_nonempty : support.Nonempty
  /-- Labels respect the radix. -/
  code_lt : ∀ c a, code c a < alphabet
  /-- Labels separate blocks. -/
  code_injective : ∀ c, Function.Injective (code c)
  /-- Supported addresses have the constant label sum. -/
  code_sum : ∀ s ∈ support, code .X (s .X) + code .Y (s .Y) + code .Z (s .Z) = natTarget

namespace NatBlockEncoding

variable {A : Leg → Type w} [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]
variable {B : Leg → Type w} [∀ c, Fintype (B c)] [∀ c, DecidableEq (B c)]
variable {support : Finset (BlockAddress A)} {supportB : Finset (BlockAddress B)}

/-- Transport an encoding along an equality of supports.  This is the safety valve for clients
whose support is only propositionally the expression the construction produces. -/
def copy (E : NatBlockEncoding support) {support' : Finset (BlockAddress A)}
    (h : support = support') : NatBlockEncoding support' where
  code := E.code
  alphabet := E.alphabet
  natTarget := E.natTarget
  support_nonempty := h ▸ E.support_nonempty
  code_lt := E.code_lt
  code_injective := E.code_injective
  code_sum := by
    intro s hs
    exact E.code_sum s (h ▸ hs)

omit [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)] in
@[simp] theorem copy_code (E : NatBlockEncoding support)
    {support' : Finset (BlockAddress A)} (h : support = support') :
    (E.copy h).code = E.code := rfl

omit [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)] in
@[simp] theorem copy_alphabet (E : NatBlockEncoding support)
    {support' : Finset (BlockAddress A)} (h : support = support') :
    (E.copy h).alphabet = E.alphabet := rfl

omit [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)] in
@[simp] theorem copy_natTarget (E : NatBlockEncoding support)
    {support' : Finset (BlockAddress A)} (h : support = support') :
    (E.copy h).natTarget = E.natTarget := rfl

/-- **A leg permutation transports an encoding.**  The support is the permuted support --- exactly
`PartitionedTensor.permute`'s --- and neither the radix nor the constant target moves, because the
legality condition is a sum over all three legs. -/
def permute (E : NatBlockEncoding support) (e : Orientation) :
    NatBlockEncoding (support.map (permuteBlockAddress (A := A) e).toEmbedding) where
  code c a := E.code (e.symm c) a
  alphabet := E.alphabet
  natTarget := E.natTarget
  support_nonempty := by
    obtain ⟨s, hs⟩ := E.support_nonempty
    exact ⟨_, Finset.mem_map_of_mem _ hs⟩
  code_lt c a := E.code_lt (e.symm c) a
  code_injective c := E.code_injective (e.symm c)
  code_sum := by
    intro s hs
    obtain ⟨t, ht, rfl⟩ := Finset.mem_map.mp hs
    have hread : ∀ c : Leg,
        (permuteBlockAddress (A := A) e).toEmbedding t c = t (e.symm c) := fun c ↦ rfl
    rw [hread .X, hread .Y, hread .Z]
    exact (leg_add_three_comp_equiv e.symm (fun d ↦ E.code d (t d))).trans (E.code_sum t ht)

omit [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)] in
@[simp] theorem permute_alphabet (E : NatBlockEncoding support) (e : Orientation) :
    (E.permute e).alphabet = E.alphabet := rfl

omit [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)] in
@[simp] theorem permute_natTarget (E : NatBlockEncoding support) (e : Orientation) :
    (E.permute e).natTarget = E.natTarget := rfl

/-- **Two encodings compose into one, as the two digits of a mixed-radix numeral.**  The support is
the product support --- exactly `PartitionedTensor.external`'s --- the radix is the product of the
two radices, and the constant target is the numeral built from the two constant targets.

This is the step that makes a *joint* hash of several factors expressible: after composing, the
whole product is addressed by a single alphabet and hashed by a single seed. -/
def external (E : NatBlockEncoding support) (F : NatBlockEncoding supportB) :
    NatBlockEncoding ((support.product supportB).map
      (blockAddressProductEquiv (A := A) (B := B)).toEmbedding) where
  code c q := E.code c q.1 + E.alphabet * F.code c q.2
  alphabet := E.alphabet * F.alphabet
  natTarget := E.natTarget + E.alphabet * F.natTarget
  support_nonempty := by
    obtain ⟨s, hs⟩ := E.support_nonempty
    obtain ⟨t, ht⟩ := F.support_nonempty
    have hpair : (s, t) ∈ support.product supportB := Finset.mem_product.mpr ⟨hs, ht⟩
    exact ⟨_, Finset.mem_map_of_mem _ hpair⟩
  code_lt c q := by
    have h1 := E.code_lt c q.1
    have h2 := F.code_lt c q.2
    calc E.code c q.1 + E.alphabet * F.code c q.2
        < E.alphabet + E.alphabet * F.code c q.2 := by omega
      _ = E.alphabet * (F.code c q.2 + 1) := by ring
      _ ≤ E.alphabet * F.alphabet := Nat.mul_le_mul_left _ h2
  code_injective c := by
    rintro ⟨a, b⟩ ⟨a', b'⟩ h
    have hcode : E.code c a + E.alphabet * F.code c b
        = E.code c a' + E.alphabet * F.code c b' := h
    have hpos : 0 < E.alphabet := Nat.lt_of_le_of_lt (Nat.zero_le _) (E.code_lt c a)
    have hlow : E.code c a = E.code c a' := by
      have hmod := congrArg (fun value : ℕ ↦ value % E.alphabet) hcode
      simp only [Nat.add_mul_mod_self_left] at hmod
      rwa [Nat.mod_eq_of_lt (E.code_lt c a), Nat.mod_eq_of_lt (E.code_lt c a')] at hmod
    have hhigh : E.alphabet * F.code c b = E.alphabet * F.code c b' := by omega
    obtain rfl := E.code_injective c hlow
    obtain rfl := F.code_injective c (Nat.eq_of_mul_eq_mul_left hpos hhigh)
    rfl
  code_sum := by
    intro s hs
    obtain ⟨⟨left, right⟩, hpair, rfl⟩ := Finset.mem_map.mp hs
    obtain ⟨hleft, hright⟩ := Finset.mem_product.mp hpair
    have hfst : ∀ c : Leg,
        ((blockAddressProductEquiv (A := A) (B := B)).toEmbedding (left, right) c).1
          = left c := fun c ↦ rfl
    have hsnd : ∀ c : Leg,
        ((blockAddressProductEquiv (A := A) (B := B)).toEmbedding (left, right) c).2
          = right c := fun c ↦ rfl
    show E.code .X _ + E.alphabet * F.code .X _
        + (E.code .Y _ + E.alphabet * F.code .Y _)
        + (E.code .Z _ + E.alphabet * F.code .Z _) = _
    rw [hfst .X, hfst .Y, hfst .Z, hsnd .X, hsnd .Y, hsnd .Z]
    have hkey : E.code .X (left .X) + E.alphabet * F.code .X (right .X)
          + (E.code .Y (left .Y) + E.alphabet * F.code .Y (right .Y))
          + (E.code .Z (left .Z) + E.alphabet * F.code .Z (right .Z))
        = (E.code .X (left .X) + E.code .Y (left .Y) + E.code .Z (left .Z))
          + E.alphabet * (F.code .X (right .X) + F.code .Y (right .Y)
            + F.code .Z (right .Z)) := by ring
    rw [hkey, E.code_sum left hleft, F.code_sum right hright]

omit [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)] [∀ c, Fintype (B c)] [∀ c, DecidableEq (B c)] in
@[simp] theorem external_alphabet (E : NatBlockEncoding support) (F : NatBlockEncoding supportB) :
    (E.external F).alphabet = E.alphabet * F.alphabet := rfl

omit [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)] [∀ c, Fintype (B c)] [∀ c, DecidableEq (B c)] in
@[simp] theorem external_natTarget
    (E : NatBlockEncoding support) (F : NatBlockEncoding supportB) :
    (E.external F).natTarget = E.natTarget + E.alphabet * F.natTarget := rfl

/-- **The field-valued hashing encoding of a mixed-radix encoding.**  Any field whose
characteristic is at least the radix sends the natural labels injectively, and the constant label
sum is a cast of the natural one. -/
def toPartitionHashEncoding {R : Type u} [Field R] {p : ℕ} [CharP R p]
    (E : NatBlockEncoding (A := A) support) (hp : E.alphabet ≤ p) :
    PartitionHashEncoding (R := R) support where
  encode c a := (E.code c a : R)
  target := (E.natTarget : R)
  support_nonempty := E.support_nonempty
  encode_injective c := by
    intro a b h
    refine E.code_injective c ?_
    refine CharP.natCast_injOn_Iio R p ?_ ?_ h
    · exact (E.code_lt c a).trans_le hp
    · exact (E.code_lt c b).trans_le hp
  legal := by
    intro s hs
    have h := congrArg (fun value : ℕ ↦ (value : R)) (E.code_sum s hs)
    push_cast at h
    exact h

omit [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)] in
@[simp] theorem toPartitionHashEncoding_target {R : Type u} [Field R] {p : ℕ} [CharP R p]
    (E : NatBlockEncoding (A := A) support) (hp : E.alphabet ≤ p) :
    (E.toPartitionHashEncoding (R := R) (p := p) hp).target = (E.natTarget : R) := rfl

omit [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)] in
@[simp] theorem toPartitionHashEncoding_encode {R : Type u} [Field R] {p : ℕ} [CharP R p]
    (E : NatBlockEncoding (A := A) support) (hp : E.alphabet ≤ p) (c : Leg) (a : A c) :
    (E.toPartitionHashEncoding (R := R) (p := p) hp).encode c a = (E.code c a : R) := rfl

end NatBlockEncoding

/-! ## Uniform batching of a finite index type -/

section UniformBatch

variable {ι : Type*} [Fintype ι]

/-- The batch of an index: its position in a fixed enumeration, divided by the batch size and
clamped to the last batch. -/
noncomputable def uniformBatchIndex (k m : ℕ) (i : ι) : ℕ :=
  min ((Fintype.equivFin ι i : ℕ) / k) (m - 1)

/-- **Uniform batching into `m` batches.**  Every batch is nonempty, and --- once `m · k` fits in
the index type --- has at least `k` elements, which is the copy count `[DuanWuZhou2022]`'s Hole
Lemma consumes. -/
noncomputable def uniformBatch (k : ℕ) {m : ℕ} (hm : 0 < m) (i : ι) : Fin m :=
  ⟨uniformBatchIndex k m i, by
    have h : uniformBatchIndex k m i ≤ m - 1 := Nat.min_le_right _ _
    omega⟩

theorem uniformBatch_val (k : ℕ) {m : ℕ} (hm : 0 < m) (i : ι) :
    (uniformBatch k hm i : ℕ) = min ((Fintype.equivFin ι i : ℕ) / k) (m - 1) := rfl

/-- The enumeration index `b · k + j` lies in the type whenever `m · k` does. -/
private theorem uniformBatch_bound {k m : ℕ}
    (hmk : m * k ≤ Fintype.card ι) {b j : ℕ} (hb : b < m) (hj : j < k) :
    b * k + j < Fintype.card ι := by
  have hstep : (b + 1) * k ≤ m * k := Nat.mul_le_mul_right k hb
  have : b * k + j < (b + 1) * k := by
    have : (b + 1) * k = b * k + k := by ring
    omega
  omega

/-- **Every batch is hit.** -/
theorem uniformBatch_surjective {k m : ℕ} (hk : 0 < k) (hm : 0 < m)
    (hmk : m * k ≤ Fintype.card ι) :
    Function.Surjective (uniformBatch (ι := ι) k hm) := by
  intro b
  have hb : (b : ℕ) < m := b.isLt
  have hlt : (b : ℕ) * k + 0 < Fintype.card ι := uniformBatch_bound hmk hb hk
  refine ⟨(Fintype.equivFin ι).symm ⟨(b : ℕ) * k, by simpa using hlt⟩, ?_⟩
  apply Fin.ext
  rw [uniformBatch_val]
  have hpos : ((Fintype.equivFin ι) ((Fintype.equivFin ι).symm
      ⟨(b : ℕ) * k, by simpa using hlt⟩) : ℕ) = (b : ℕ) * k := by
    rw [Equiv.apply_symm_apply]
  rw [hpos, Nat.mul_div_cancel _ hk]
  omega

/-- **Every batch has at least `k` elements**, by the explicit injection `j ↦ b · k + j`. -/
theorem le_card_uniformBatch_fiber {k m : ℕ} (hk : 0 < k) (hm : 0 < m)
    (hmk : m * k ≤ Fintype.card ι) (b : Fin m) :
    k ≤ Fintype.card {i : ι // uniformBatch k hm i = b} := by
  classical
  have hb : (b : ℕ) < m := b.isLt
  have hmem : ∀ j : Fin k, (b : ℕ) * k + (j : ℕ) < Fintype.card ι := fun j ↦
    uniformBatch_bound hmk hb j.isLt
  have hbatch : ∀ j : Fin k,
      uniformBatch (ι := ι) k hm
        ((Fintype.equivFin ι).symm ⟨(b : ℕ) * k + (j : ℕ), hmem j⟩) = b := by
    intro j
    apply Fin.ext
    rw [uniformBatch_val]
    have hpos : ((Fintype.equivFin ι) ((Fintype.equivFin ι).symm
        ⟨(b : ℕ) * k + (j : ℕ), hmem j⟩) : ℕ) = (b : ℕ) * k + (j : ℕ) := by
      rw [Equiv.apply_symm_apply]
    have hdiv : ((b : ℕ) * k + (j : ℕ)) / k = (b : ℕ) := by
      rw [mul_comm, Nat.mul_add_div hk, Nat.div_eq_of_lt j.isLt, Nat.add_zero]
    rw [hpos, hdiv]
    omega
  have hinj : Function.Injective
      (fun j : Fin k ↦ (⟨(Fintype.equivFin ι).symm ⟨(b : ℕ) * k + (j : ℕ), hmem j⟩,
        hbatch j⟩ : {i : ι // uniformBatch k hm i = b})) := by
    intro j j' h
    have hval := congrArg Subtype.val h
    have hindex := congrArg (Fintype.equivFin ι) hval
    simp only [Equiv.apply_symm_apply] at hindex
    have : (b : ℕ) * k + (j : ℕ) = (b : ℕ) * k + (j' : ℕ) := congrArg Fin.val hindex
    exact Fin.ext (by omega)
  simpa using Fintype.card_le_of_injective _ hinj

end UniformBatch

/-! ## The seeded extraction for a positive power -/

namespace PartitionHashEncoding

variable {R : Type u} [Field R]
variable {A : Leg → Type w} [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]
variable {support : Finset (BlockAddress A)}
variable {K : Type v} [CommSemiring K]
variable {V : ∀ c, A c → Type (max v x)}
variable [∀ c a, AddCommMonoid (V c a)] [∀ c a, Module K (V c a)]

/-- **`hselect` for a positive power, from one marked two-leg hashing seed.**

The positive power of any partitioned tensor whose base support carries a hashing encoding
restricts onto the subpartition retained by marked `XY` isolation.  Repeated `Z` block words are
untouched, so the two compatibility zero-outs downstream still see them.

Applied to a product of permuted copies of one partition --- whose encoding is built by
`NatBlockEncoding.external` and `NatBlockEncoding.permute` --- this is a *joint* hash: all factors
are addressed by the one alphabet and selected by the one seed. -/
theorem restricts_positivePower_to_markedXYIsolated [NeZero (2 : R)]
    (P : PartitionedTensor (K := K) (A := A) V)
    (H : PartitionHashEncoding (R := R) P.support) (n : ℕ)
    (markedWords : Finset (PositiveWord P.support n))
    (B : Finset R) (hB : ThreeAPFree (B : Set R))
    (seed : ProgressionHash.Seed R (Fin (n + 1))) :
    Restricts (P.positivePower n).realize
      ((P.positivePower n).withSupport
        (H.markedXYIsolatedPowerAddresses n Finset.univ markedWords B seed)).realize :=
  Tensor.Restricts.modeledTargets_to_markedXYIsolated H Finset.univ markedWords
    (Finset.subset_univ _) B hB seed (P.positivePower n)
    (H.positivePower_support_eq_modeledLegalTargets P n)

/-- **The retained family is a sub-support of the power it was selected from.**

Hashing only ever discards addresses, so the retained family sits inside the positive power's own
support.  Clients that must transport a property of the ambient partition --- a compatibility
soundness statement, say --- down to the retained family consume exactly this. -/
theorem markedXYIsolatedPowerAddresses_subset_positivePower_support [NeZero (2 : R)]
    (P : PartitionedTensor (K := K) (A := A) V)
    (H : PartitionHashEncoding (R := R) P.support) (n : ℕ)
    (markedWords : Finset (PositiveWord P.support n))
    (B : Finset R) (seed : ProgressionHash.Seed R (Fin (n + 1))) :
    H.markedXYIsolatedPowerAddresses n Finset.univ markedWords B seed ⊆
      (P.positivePower n).support := by
  classical
  rw [H.positivePower_support_eq_modeledLegalTargets P n]
  refine (H.markedXYIsolatedPowerAddresses_subset_filteredPowerAddresses n Finset.univ
    markedWords (Finset.subset_univ _) B seed).trans ?_
  unfold filteredPowerAddresses modeledAddresses
  exact Finset.image_mono _ (ProgressionHash.LegalTriple.filteredTargets_subset
    (H.legalTargets n Finset.univ) B seed)

omit [∀ c, Fintype (A c)] in
/-- **`hX` for a positive power.**  The retained marked family has pairwise distinct `X` block
words; this is the `Set.InjOn` premise of
`AsymmetricGlobal.Tensor.Restricts.partitionedYZCompatibilityCleanup_to_repairedRestrictedSplittingDirectSum`,
read at the retained subpartition's own support. -/
theorem x_injOn_markedXYIsolated_positivePower [NeZero (2 : R)]
    (H : PartitionHashEncoding (R := R) support) (n : ℕ)
    (markedWords : Finset (PositiveWord support n))
    (B : Finset R) (hB : ThreeAPFree (B : Set R))
    (seed : ProgressionHash.Seed R (Fin (n + 1))) :
    Set.InjOn (fun s : BlockAddress (fun c ↦ PositiveWord (A c) n) ↦ s .X)
      (H.markedXYIsolatedPowerAddresses n Finset.univ markedWords B seed : Set _) :=
  H.x_injectiveOn_markedXYIsolatedPowerAddresses n Finset.univ markedWords
    (Finset.subset_univ _) B hB seed

/-- **The packaged joint-hashing input of `[DuanWuZhou2022]` §6.**

One affine seed simultaneously delivers

* the retained subpartition and the restriction onto it (`hselect`),
* the `X`-injectivity certificate (`hX`), and
* the retained-count lower bound against the *marked* family, which is the copy count the rate
  arithmetic consumes,

for the positive power of any partitioned tensor whose support carries a hashing encoding.  The
modulus hypothesis is `[DuanWuZhou2022]`'s `8 · d ≤ |R|` on the common ambient leg-fiber degree
`d` of the marked targets. -/
theorem exists_seed_markedXYIsolated_positivePower [Fintype R] [NeZero (2 : R)]
    (P : PartitionedTensor (K := K) (A := A) V)
    (H : PartitionHashEncoding (R := R) P.support) (n : ℕ)
    (markedWords : Finset (PositiveWord P.support n))
    (B : Finset R) (hB : ThreeAPFree (B : Set R)) (d : ℕ)
    (hXfiber : ∀ triple ∈ H.legalTargets n markedWords,
      (ProgressionHash.LegalTriple.legFiber
        (H.legalTargets n Finset.univ) triple .X).card ≤ d)
    (hYfiber : ∀ triple ∈ H.legalTargets n markedWords,
      (ProgressionHash.LegalTriple.legFiber
        (H.legalTargets n Finset.univ) triple .Y).card ≤ d)
    (hmodulus : 8 * d ≤ Fintype.card R) :
    ∃ selected : Finset (BlockAddress (fun c ↦ PositiveWord (A c) n)),
      3 * markedWords.card * B.card ≤
          4 * (Fintype.card R * Fintype.card R) * selected.card ∧
        Restricts (P.positivePower n).realize
          ((P.positivePower n).withSupport selected).realize ∧
        Set.InjOn (fun s : BlockAddress (fun c ↦ PositiveWord (A c) n) ↦ s .X)
          (selected : Set _) := by
  obtain ⟨seed, hcount, _hsubset, _hinjX, _hinjY⟩ :=
    H.exists_seed_many_markedXYIsolatedPowerAddresses_of_modulus n Finset.univ markedWords
      (Finset.subset_univ _) B hB d hXfiber hYfiber hmodulus
  refine ⟨H.markedXYIsolatedPowerAddresses n Finset.univ markedWords B seed, hcount, ?_, ?_⟩
  · exact restricts_positivePower_to_markedXYIsolated P H n markedWords B hB seed
  · exact x_injOn_markedXYIsolated_positivePower H n markedWords B hB seed

end PartitionHashEncoding

end AlgebraicComplexity
