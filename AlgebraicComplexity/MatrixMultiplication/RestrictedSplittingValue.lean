/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Combinatorics.WordTypeCore
import AlgebraicComplexity.MatrixMultiplication.RestrictedSplittingPower
import AlgebraicComplexity.MatrixMultiplication.TauValueDirectSum

/-!
# The value of a restricted-splitting power, from its constituents' values

Layer 3 (`AlgebraicComplexity/MatrixMultiplication/`).  `[DuanWuZhou2022]`'s inter-level interface
is the *pair* `(V^{(6)}(T_{i,j,k}, alphatilde), alphatilde_{i,j,k})`: a laser stage's leaf is the
restricted-splitting power `Q^{tensor (n+1)}[alphatilde]` of Definition 2.14, and its value is the
product of the constituents' values weighted by the split.  In rate form that product is exactly
section 6.3's `alphabar_val`.

Until now the repository had the leaf *object* (`PartitionedTensor.restrictedSplittingPower`) and
the value *vocabulary* (`HasTauWeight`) but no law connecting them: no result anywhere mentioned
both.  This module supplies it.

## The law

`hasTauWeight_restrictedSplittingPower`: if every supported constituent of `Q` carries `tau`-weight
`value s`, and `w` is a word of supported addresses whose transposed block address meets the split,
then the *realization* of `Q^{tensor (n+1)}[alphatilde]` carries `tau`-weight `∏_i value (w i)`.

`positiveSupportWordWeight_eq_prod_pow` regroups that product by letter multiplicity into

`∏_{s in Q.support} value s ^ (multiplicity of s in w)`,

which is the form a distribution-indexed client uses: with `w` of empirical type `alpha`, the
weight is `∏_s value s ^ alpha s`.

## The step that was missing generically: extracting one block

`Tensor/Partitioned.lean` has the *filter* `blockFilter`, which zeroes unselected blocks but keeps
the result inside the ambient partitioned space.  What a value argument needs is the *projection*
onto a single block, landing in that block's own three spaces.  `blockProject` is that map and
`Tensor.Restricts.partitionedConstituent` is the resulting restriction

`s in P.support -> Restricts P.realize (P.constituent s)`.

No legwise injectivity is required --- unlike
`Restricts.partitionedLegwiseInjective_to_indexedDirectSum`, which extracts *all* blocks at once
and does need it.  Projecting to one block always works, because the projection annihilates every
other supported block on at least one leg.

## Non-goals

No distribution, no entropy, no method-of-types count, and no named tensor.  In particular this
module does not say that a word of the prescribed type exists; that is a counting statement, and a
client supplies the word.

**The block-extraction hypothesis is insufficient for the paper's values, not merely absent.**
Extracting one block gives that block's matrix-multiplication volume and nothing else, so
iterating it over a word reaches only the product of the letters' volumes.  Definition 2.14's
restricted-splitting values and `lem:non-rot-values` additionally carry the split entropy, the
orbit count factor and the shared-leg merges.  The one-word floor falls short of the paper's
values by roughly **0.35 to 0.40 nats per letter**, depending on how those three are attributed;
two independent computations agree the shortfall exceeds section 6.3's slack of about
`1.7 * 10 ^ (-7)` nats by six orders of magnitude, and it is independent of which word is chosen.
A client wanting those values needs the per-constituent value law, not a longer word.
-/

namespace AlgebraicComplexity

open Tensor
open scoped BigOperators

universe u v w

section BlockExtraction

variable {K : Type u} [CommSemiring K]
variable {A : Leg → Type w} [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]
variable {V : ∀ c, A c → Type (max u v)}
variable [∀ c a, AddCommMonoid (V c a)] [∀ c a, Module K (V c a)]

/-- Project the ambient partitioned spaces onto the three spaces at one block address. -/
noncomputable def Tensor.blockProject (s : BlockAddress A) :
    ∀ c, PartitionedSpace K V c →ₗ[K] V c (s c) :=
  fun c ↦ DirectSum.component K (A c) (V c) (s c)

omit [∀ c, Fintype (A c)] in
theorem Tensor.blockProject_comp_blockInclude (s : BlockAddress A) (c : Leg) :
    (Tensor.blockProject (K := K) (V := V) s c).comp
        (Tensor.blockInclude (K := K) (V := V) s c) = LinearMap.id := by
  ext x
  simp [Tensor.blockProject, Tensor.blockInclude]

/-- **Extracting one supported block of a partitioned tensor.**

The realization restricts onto any single supported constituent.  Zeroing every other block on all
three legs is `Restricts.partitionedSelect`; the remaining step is the projection
`blockProject`, which is a left inverse of `blockInclude`.  No legwise injectivity hypothesis is
needed. -/
theorem Tensor.Restricts.partitionedConstituent
    (P : PartitionedTensor (K := K) (A := A) V) (s : BlockAddress A) (hs : s ∈ P.support) :
    Restricts P.realize (P.constituent s) := by
  have hsupport : (P.select (fun c a ↦ a = s c)).support = {s} := by
    ext t
    rw [PartitionedTensor.mem_select_support, Finset.mem_singleton]
    constructor
    · rintro ⟨_, ht⟩
      exact funext ht
    · rintro rfl
      exact ⟨hs, fun _ ↦ rfl⟩
  have hrealize : (P.select (fun c a ↦ a = s c)).realize =
      Tensor.map (Tensor.blockInclude (K := K) (V := V) s) (P.constituent s) := by
    unfold PartitionedTensor.realize realizePartition
    rw [hsupport]
    exact Finset.sum_singleton _ _
  refine (Tensor.Restricts.partitionedSelect P (fun c a ↦ a = s c)).trans ?_
  rw [hrealize]
  refine ⟨Tensor.blockProject (K := K) (V := V) s, ?_⟩
  change (Tensor.map (Tensor.blockProject (K := K) (V := V) s) ∘ₗ
    Tensor.map (Tensor.blockInclude (K := K) (V := V) s)) (P.constituent s) = P.constituent s
  rw [← Tensor.map_comp]
  simp_rw [Tensor.blockProject_comp_blockInclude]
  simp

end BlockExtraction

/-! ## The weight of a word of constituents -/

section WordWeight

variable {K : Type u} [CommSemiring K]
variable {A : Leg → Type w} [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]
variable {V : ∀ c, A c → Type (max u v)}
variable [∀ c a, AddCommMonoid (V c a)] [∀ c a, Module K (V c a)]

/-- The product of the per-constituent weights along a word of supported addresses. -/
noncomputable def positiveSupportWordWeight
    {P : PartitionedTensor (K := K) (A := A) V} (value : P.support → ℝ) :
    (n : ℕ) → PositiveWord P.support n → ℝ
  | 0, q => value q
  | n + 1, q => positiveSupportWordWeight value n q.1 * value q.2

theorem positiveSupportWordWeight_nonneg
    {P : PartitionedTensor (K := K) (A := A) V} {value : P.support → ℝ}
    (hvalue : ∀ s, 0 ≤ value s) :
    ∀ (n : ℕ) (q : PositiveWord P.support n), 0 ≤ positiveSupportWordWeight value n q
  | 0, q => hvalue q
  | n + 1, q =>
      mul_nonneg (positiveSupportWordWeight_nonneg hvalue n q.1) (hvalue q.2)

/-- **The iterated external product of a word of constituents carries the product weight.** -/
theorem hasTauWeight_wordTensor
    (P : PartitionedTensor (K := K) (A := A) V) {τ : ℝ} {value : P.support → ℝ}
    (hvalue : ∀ s, 0 ≤ value s)
    (h : ∀ s : P.support, HasTauWeight K (P.constituent s.1) τ (value s)) :
    ∀ (n : ℕ) (q : PositiveWord P.support n),
      HasTauWeight K (PartitionedTensor.positiveSupportWordTensor P n q) τ
        (positiveSupportWordWeight value n q)
  | 0, q => h q
  | n + 1, q => by
      rw [PartitionedTensor.positiveSupportWordTensor_succ]
      exact HasTauWeight.external
        (hasTauWeight_wordTensor P hvalue h n q.1) (h q.2)
        (positiveSupportWordWeight_nonneg hvalue n q.1) (hvalue q.2)

/-- The constituent of the positive power at a word address carries the product weight. -/
theorem hasTauWeight_positivePower_constituent
    (P : PartitionedTensor (K := K) (A := A) V) {τ : ℝ} {value : P.support → ℝ}
    (hvalue : ∀ s, 0 ≤ value s)
    (h : ∀ s : P.support, HasTauWeight K (P.constituent s.1) τ (value s))
    (n : ℕ) (q : PositiveWord P.support n) :
    HasTauWeight K
      ((P.positivePower n).constituent (positiveSupportWordBlockAddress P.support n q)) τ
      (positiveSupportWordWeight value n q) := by
  rw [P.positivePower_constituent_positiveSupportWordBlockAddress n q]
  exact hasTauWeight_wordTensor P hvalue h n q

/-- **The value law for restricted-splitting powers, in its general form.**

The hypothesis is a single `tau`-weight on the iterated external product of the word's
constituents.  Nothing is assumed about how that weight was obtained, which is what makes this
form absorb every way a client may group the letters:

* letterwise, via `hasTauWeight_wordTensor` below;
* a group of letters at once --- for instance three cyclically related constituents, whose
  external product is `sym_3` of one of them (`cyclicPowerProduct_eq_symThree_power`), so a
  `sym_3` certificate is directly a group weight;
* a repeated letter, whose external product over a group of `N` positions is
  `Tensor.power` of that constituent, so a powered weight is directly a group weight.

In each case the client assembles the word weight with the committed `HasTauWeight.external` and
hands it here.  No root extraction and no divisibility bookkeeping occurs on this side. -/
theorem hasTauWeight_restrictedSplittingPower_of_wordTensor
    (P : PartitionedTensor (K := K) (A := A) V) {τ weight : ℝ}
    (n : ℕ) (split : SplitRestriction A) (q : PositiveWord P.support n)
    (hkeeps : ∀ c, split.Keeps n c (positiveSupportWordBlockAddress P.support n q c))
    (hword : HasTauWeight K (PartitionedTensor.positiveSupportWordTensor P n q) τ weight) :
    HasTauWeight K (P.restrictedSplittingPower n split).realize τ weight := by
  classical
  have hpower : positiveSupportWordBlockAddress P.support n q ∈ (P.positivePower n).support := by
    rw [P.positivePower_support_eq_image_positiveSupportWordBlockAddress n]
    exact Finset.mem_image_of_mem _ (Finset.mem_univ q)
  have hmem : positiveSupportWordBlockAddress P.support n q ∈
      (P.restrictedSplittingPower n split).support := by
    rw [PartitionedTensor.mem_restrictedSplittingPower_support]
    exact ⟨hpower, hkeeps⟩
  refine HasTauWeight.of_restricts
    (Tensor.Restricts.partitionedConstituent (P.restrictedSplittingPower n split) _ hmem) ?_
  rw [PartitionedTensor.restrictedSplittingPower_constituent,
    P.positivePower_constituent_positiveSupportWordBlockAddress n q]
  exact hword

/-- **The value law for restricted-splitting powers.**

If every supported constituent of `Q` carries `tau`-weight `value s`, and `q` is a word of
supported addresses whose transposed block address meets the split, then the realization of
`Q^{tensor (n+1)}[alphatilde]` carries the product weight.  The word is an input: no counting
statement is made here. -/
theorem hasTauWeight_restrictedSplittingPower
    (P : PartitionedTensor (K := K) (A := A) V) {τ : ℝ} {value : P.support → ℝ}
    (hvalue : ∀ s, 0 ≤ value s)
    (h : ∀ s : P.support, HasTauWeight K (P.constituent s.1) τ (value s))
    (n : ℕ) (split : SplitRestriction A) (q : PositiveWord P.support n)
    (hkeeps : ∀ c, split.Keeps n c (positiveSupportWordBlockAddress P.support n q c)) :
    HasTauWeight K (P.restrictedSplittingPower n split).realize τ
      (positiveSupportWordWeight value n q) :=
  hasTauWeight_restrictedSplittingPower_of_wordTensor P n split q hkeeps
    (hasTauWeight_wordTensor P hvalue h n q)

end WordWeight

/-! ## Regrouping the product by letter multiplicity -/

section Regroup

variable {K : Type u} [CommSemiring K]
variable {A : Leg → Type w} [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]
variable {V : ∀ c, A c → Type (max u v)}
variable [∀ c a, AddCommMonoid (V c a)] [∀ c a, Module K (V c a)]

/-- The word weight is the product of the letter values along the word, read as a function on
`Fin (n + 1)`. -/
theorem positiveSupportWordWeight_eq_prod
    {P : PartitionedTensor (K := K) (A := A) V} (value : P.support → ℝ) :
    ∀ (n : ℕ) (q : PositiveWord P.support n),
      positiveSupportWordWeight value n q =
        ∏ j : Fin (n + 1), value (positiveWordEquiv P.support n q j)
  | 0, q => by
      simp [positiveSupportWordWeight]
  | n + 1, q => by
      rw [positiveSupportWordWeight, positiveSupportWordWeight_eq_prod value n q.1]
      conv_rhs => rw [positiveWordEquiv_succ_apply, Fin.prod_univ_castSucc]
      simp

/-- **The word weight, regrouped by empirical type.**  This is the form a distribution-indexed
client uses: a word of empirical type `alpha` has weight `∏_s value s ^ alpha s`. -/
theorem positiveSupportWordWeight_eq_prod_pow
    {P : PartitionedTensor (K := K) (A := A) V} (value : P.support → ℝ)
    (n : ℕ) (q : PositiveWord P.support n) :
    positiveSupportWordWeight value n q =
      ∏ s : P.support,
        value s ^ WordType.multiplicity (positiveWordEquiv P.support n q) s := by
  classical
  rw [positiveSupportWordWeight_eq_prod value n q]
  have hmaps : ∀ j ∈ (Finset.univ : Finset (Fin (n + 1))),
      positiveWordEquiv P.support n q j ∈ (Finset.univ : Finset P.support) :=
    fun _ _ ↦ Finset.mem_univ _
  rw [← Finset.prod_fiberwise_of_maps_to hmaps
    (fun j ↦ value (positiveWordEquiv P.support n q j))]
  refine Finset.prod_congr rfl fun s _ ↦ ?_
  have hconst : ∀ j ∈ (Finset.univ : Finset (Fin (n + 1))).filter
      (fun j ↦ positiveWordEquiv P.support n q j = s),
      value (positiveWordEquiv P.support n q j) = value s := by
    intro j hj
    rw [(Finset.mem_filter.mp hj).2]
  rw [Finset.prod_congr rfl hconst, Finset.prod_const]
  unfold WordType.multiplicity
  congr 3


/-! ## The proportional form: an `alpha`-typical word of scale `t` -/

/-- Regrouping a product of powers whose exponents are a common multiple. -/
theorem prod_pow_mul {ι : Type*} [Fintype ι] (value : ι → ℝ) (α : ι → ℕ) (t : ℕ) :
    ∏ s : ι, value s ^ (α s * t) = (∏ s : ι, value s ^ α s) ^ t := by
  rw [← Finset.prod_pow]
  exact Finset.prod_congr rfl fun s _ ↦ pow_mul (value s) (α s) t

/-- **The value law in the form a distribution-indexed client uses.**

If the word is `alpha`-typical at scale `t` --- every letter `s` occurs exactly `alpha s * t`
times, so the word length is `(∑ alpha) * t` --- then the leaf carries the `t`-th power of the
one-period base `∏_s value s ^ alpha s`.

This is the exponent bookkeeping in its only sound form: the scale `t` is *determined* by the word
length, `(n + 1) = (∑ alpha) * t`.  A client that needs the base raised to a target exponent `E`
must therefore choose the word length to be `(∑ alpha) * E`; there is no freedom left once the
distribution and the length are fixed. -/
theorem hasTauWeight_restrictedSplittingPower_pow
    (P : PartitionedTensor (K := K) (A := A) V) {τ : ℝ} {value : P.support → ℝ}
    (hvalue : ∀ s, 0 ≤ value s)
    (h : ∀ s : P.support, HasTauWeight K (P.constituent s.1) τ (value s))
    (n : ℕ) (split : SplitRestriction A) (q : PositiveWord P.support n)
    (α : P.support → ℕ) (t : ℕ)
    (hmult : WordType.multiplicity (positiveWordEquiv P.support n q) = fun s ↦ α s * t)
    (hkeeps : ∀ c, split.Keeps n c (positiveSupportWordBlockAddress P.support n q c)) :
    HasTauWeight K (P.restrictedSplittingPower n split).realize τ
      ((∏ s : P.support, value s ^ α s) ^ t) := by
  have hbase := hasTauWeight_restrictedSplittingPower P hvalue h n split q hkeeps
  rwa [positiveSupportWordWeight_eq_prod_pow value n q, hmult, prod_pow_mul] at hbase

/-- The word length of an `alpha`-typical word of scale `t` is `(∑ alpha) * t`.  This is the
identity that fixes the scale, and hence the exponent, once the length is chosen. -/
theorem sum_multiplicity_eq_of_proportional
    {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ} {word : Fin (n + 1) → ι}
    {α : ι → ℕ} {t : ℕ} (hmult : WordType.multiplicity word = fun s ↦ α s * t) :
    (∑ s : ι, α s) * t = n + 1 := by
  have hsum := WordType.sum_multiplicity word
  rw [hmult] at hsum
  rw [← hsum, Finset.sum_mul]


end Regroup

end AlgebraicComplexity