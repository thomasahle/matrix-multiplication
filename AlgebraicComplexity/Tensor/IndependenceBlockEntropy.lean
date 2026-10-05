/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Analysis.Subexponential
import AlgebraicComplexity.Combinatorics.WordType
import AlgebraicComplexity.Probability.EntropyValue
import AlgebraicComplexity.Probability.Finite
import AlgebraicComplexity.Tensor.AsymptoticIndependenceNumber
import AlgebraicComplexity.Tensor.CoordinateBlockWord

/-!
# The block-partition entropy bound for the asymptotic independence number

This file formalizes, for the asymptotic independence number `Ī`, the block-partition tool of

> J. Alman, *Limits on the Universal Method for Matrix Multiplication*, PhD thesis, MIT 2019,
> Section 5.3.2, Theorem 5.3 [Alman2019].

Alman states the tool for asymptotic slice rank `S̃`; the same counting argument bounds `Ī`,
because an independent set of `T^{⊗n}` injects into the leg-`c` variables of `T^{⊗n}` for each
leg `c` (`Tensor.IndependentSet.injOn`), exactly as the slice rank along leg `c` is bounded by the
number of leg-`c` variables.

## The set-up transcribed

Fix a coefficient table `T` and a **block labelling** `blk c : κ c → A c` of the variables of each
leg, as in `Tensor/CoordinateBlockWord.lean`; this is Alman's partition
`X = X₁ ∪ ⋯ ∪ X_{k_X}`, `Y = ⋯`, `Z = ⋯` written as a labelling rather than as a family of
subsets.  Alman's set `L` of *non-zero blocks* is transcribed as a finite type `ι` of labels
together with `β : ι → BlockAddress A` and the covering hypothesis

```
hcover : ∀ p, T p ≠ 0 → ∃ j, ∀ c, blk c (p c) = β j c,
```

which says that every term of `T` lies in one of the listed blocks.  Neither injectivity of `β`
nor non-vanishing of the corresponding blocks is needed: listing a block that does not occur only
weakens the conclusion, which is the right monotonicity for a barrier statement.

For a probability vector `p` on `ι` and a leg `c`, Alman's marginal `p(X_i)` is the pushforward
`p.pushforward (fun j ↦ β j c)` and his quantity

```
p_X = ∏_i (|X_i| / p(X_i))^{p(X_i)} = 2^{H(p(X))} · ∏_i |X_i|^{p(X_i)}
```

is `blockLegValue (blockFiberCard blk c) (p.pushforward (fun j ↦ β j c))`, where
`blockFiberCard blk c a` is the number of leg-`c` variables carrying the block label `a`.

## Main definitions

* `blockFiberCard blk c a`: the size `|X_a|` of the block `a` on leg `c`.

The entropy value `blockLegValue F p = ∏ a, (F a / p a) ^ p a` itself is Alman's `p_X` written for
an arbitrary finite alphabet; being a pure finite-probability quantity it lives one layer down, in
`Probability/EntropyValue.lean`, together with its two convexity inputs `blockLegValue_le_sum`
(Jensen for `log`) and `blockLegValue_le_prod_rpow` (the reference-vector, Gibbs form).

## Main results

The counting, in increasing generality:

* `card_filter_multiplicity_coordinateBlockLegWord`: **the exact leg count.**  The number of
  leg-`c` words of length `n` whose block word has multiplicity profile `σ` is
  `|typeClass n σ| · ∏ a |X_a|^{σ a}`; this is the displayed count in Alman's proof.
* `typeClass_card_mul_prod_pow_le_blockLegValue_pow`: **the method of types, with no loss at all.**
  `|typeClass n σ| · ∏ a (F a)^{σ a} ≤ blockLegValue F (σ / n)^n`.  The multinomial coefficient is
  bounded by the entropy base through one term of the multinomial expansion of
  `(∑ a σ a / n)^n = 1` (`WordType.pow_sum_eq_sum_type_class`), which needs neither Stirling's
  formula nor a positivity hypothesis on `σ`.
* `IndependentSet.card_le_mul_pow_of_blockEntropy`: **the finite form of Theorem 5.3.**  If every
  block value is at most `M` for every probability vector on `ι`, then every independent set of
  `T^{⊗n}` has at most `|types ι n| · M^n ≤ (n+1)^{|ι|} · M^n` elements.
* `asymptoticIndependenceNumber_le_of_blockEntropy` (**Theorem 5.3 for `Ī`**):
  consequently `Ī(T) ≤ M`.
* `asymptoticIndependenceNumber_le_sum_blockFiberCard`: the sanity check, `Ī(T) ≤ ∑_a |X_a|`,
  obtained from `blockLegValue_le_sum` on one fixed leg; it recovers
  `asymptoticIndependenceNumber_le_card`.

## Deviations from the thesis, and what is *not* proved here

* **The polynomial loss is removed by supermultiplicativity, not by a limit.**  Alman writes
  `S(T^{⊗n}) ≤ poly(n) · maxₚ min{p_X,p_Y,p_Z}^{n+o(n)}` and passes to the limit.  Here the
  finite bound is `I(T^{⊗n}) ≤ (n+1)^{|ι|} · M^n` with an explicit polynomial, and the block-free
  bridge `asymptoticIndependenceNumber_le_of_subexponential_mul_pow` of
  `Tensor/AsymptoticIndependenceNumber.lean` removes it using the supermultiplicativity of
  `n ↦ I(T^{⊗n})` (`Tensor.independenceNumber_coordinatePower_pow_le`); this is where
  `NoZeroDivisors` and `Nontrivial` enter, and nowhere else.
* **The optimization over the simplex is a hypothesis, not a supremum.**  `M` is any real that
  dominates `min_c p_c` for every `p ∈ P(L)`.  This is the "explicit finite certificate over
  unattained optimizer functions" convention of `DESIGN.md`: no `sSup` over the simplex, no
  compactness, and clients supply the certificate they actually have.
* **Alman's Proposition 5.4 (symmetrization) is not needed and is not proved.**  Its purpose is to
  restrict the optimization to `T`-symmetric `p`.  The reference-vector form
  `blockLegValue_le_prod_rpow` makes that restriction unnecessary: applied on all three legs with
  one common reference vector and multiplied, it bounds `∏_c p_c` by a quantity depending only on
  the *total* mass Alman's symmetrization would average, so the one-parameter symmetric family is
  reached without symmetrizing.  See
  `Examples/GeneralizedCoppersmithWinogradIndependenceUpper.lean`.
* **Relation to the AVW partition bound** `Ī(T) ≤ ∑_j μ(P_j)^{1/3}`
  (`asymptoticIndependenceNumber_le_sum_rpow_coordinateMeasure`, `Tensor/IndependenceMeasure.lean`).
  On the *same* block partition the bound of this file is never weaker.  Indeed, with
  `μ_j = ∏_c |X_{β j c}|`, `Z = ∑_j μ_j^{1/3}` and the reference vector
  `r_c(a) = (∑_{j : β j c = a} μ_j^{1/3})/Z`, the reference form gives
  `∏_c p_c ≤ Z³ · ∏_j (μ_j / ∏_c s_c(β j c))^{p_j}` with `s_c(a) = Z · r_c(a)`, and every factor is
  at most `1` because `s_c(β j c) ≥ μ_j^{1/3}`; hence `min_c p_c ≤ Z`.  The gap can be large: for
  the six-block partition of `CW_6^σ` the AVW bound is `3 + 3·36^{1/3} = 12.9…` and Theorem 5.3
  gives `6.45`.  The uniform `p` is *not* the special case that recovers the AVW bound --- the
  distribution proportional to `μ_j^{1/3}` is --- and neither statement is formalized here.
* Alman's Theorem 5.6 (tightness of these bounds) and the universal exponent `ω_u` are separate
  developments; this file proves an upper bound on `Ī` and nothing about `S̃`.

## Position in the library

Layer 1.  Besides the tensor layer (`Tensor/AsymptoticIndependenceNumber.lean` and
`Tensor/CoordinateBlockWord.lean`) it imports four Mathlib-only leaves --- the word-type
combinatorics of `Combinatorics/WordType.lean`, the finite probability vectors of
`Probability/Finite.lean`, the entropy value of `Probability/EntropyValue.lean` and the
subexponential-loss calculus of `Analysis/Subexponential.lean`.
The same dependency on the lower leaves already occurs in `Tensor/IndexedPower.lean` and
`Tensor/Relation.lean`.  Nothing here mentions a named matrix-multiplication construction or a
numerical bound.
-/

namespace AlgebraicComplexity.Tensor

open scoped BigOperators

universe u v w

/-! ## The method of types with no loss -/

section MethodOfTypes

variable {α : Type*} [Fintype α]

/-- **The multinomial coefficient is bounded by the entropy base, with no loss at all.**  For a
multiplicity profile `σ` of total mass `n > 0` and nonnegative weights `F`,

```
|{words of type σ}| · ∏ₐ F(a)^{σ(a)} ≤ blockLegValue F (σ/n)^n.
```

This is the method-of-types estimate `multinomial(n; σ) ≤ 2^{n·H(σ/n)}` in the form the counting
argument needs.  Alman quotes it with a subexponential loss (his Proposition 2.5); the loss is in
fact unnecessary.

Proof sketch: put `p = σ/n`, a probability vector.  Expanding `1 = (∑ₐ p a)^n` by the multinomial
theorem grouped by word classes (`WordType.pow_sum_eq_sum_type_class`) exhibits
`|typeClass n σ| · ∏ₐ p a^{σ a}` as *one* of its nonnegative terms, so that product is at most `1`.
On the other hand `blockLegValue F p ^ n = (∏ₐ F a^{σ a}) / (∏ₐ p a^{σ a})`, because raising the
`a`-th factor to the `n`-th power turns the real exponent `p a` into the natural exponent
`n · p a = σ a`; the denominator is positive since `p a > 0` whenever `σ a > 0`.  Multiplying the
first inequality by `∏ₐ F a^{σ a} ≥ 0` and dividing by the positive denominator is the claim. -/
theorem typeClass_card_mul_prod_pow_le_blockLegValue_pow {n : ℕ} (hn : 0 < n) {F : α → ℝ}
    (hF : ∀ a, 0 ≤ F a) {σ : α → ℕ} (hσ : ∑ a, σ a = n) :
    ((WordType.typeClass n σ).card : ℝ) * ∏ a, F a ^ σ a ≤
      blockLegValue F (fun a ↦ (σ a : ℝ) / n) ^ n := by
  classical
  set p : α → ℝ := fun a ↦ (σ a : ℝ) / n with hpdef
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hpnonneg : ∀ a, 0 ≤ p a := fun a ↦ by positivity
  have hpsum : ∑ a, p a = 1 := by
    rw [hpdef, ← Finset.sum_div]
    rw [show ∑ a, ((σ a : ℕ) : ℝ) = ((n : ℕ) : ℝ) by exact_mod_cast hσ]
    field_simp
  -- One term of the multinomial expansion of `1 = (∑ p)^n`.
  have hone : ((WordType.typeClass n σ).card : ℝ) * ∏ a, p a ^ σ a ≤ 1 := by
    have hexp := WordType.pow_sum_eq_sum_type_class (ι := α) p n
    rw [hpsum, one_pow] at hexp
    rw [hexp]
    refine Finset.single_le_sum (f := fun b ↦ ((WordType.typeClass n b).card : ℝ) * ∏ a, p a ^ b a)
      (fun b _ ↦ by positivity) ?_
    exact WordType.mem_types.mpr hσ
  -- The denominator is positive.
  have hden : 0 < ∏ a, p a ^ σ a := by
    refine Finset.prod_pos fun a _ ↦ ?_
    rcases Nat.eq_zero_or_pos (σ a) with h | h
    · rw [h]; norm_num
    · have : (0 : ℝ) < (σ a : ℝ) := by exact_mod_cast h
      exact pow_pos (by positivity) _
  -- The `n`-th power of the block value in closed form.
  have hpow : blockLegValue F p ^ n = (∏ a, F a ^ σ a) / ∏ a, p a ^ σ a := by
    unfold blockLegValue
    rw [← Finset.prod_pow, ← Finset.prod_div_distrib]
    refine Finset.prod_congr rfl fun a _ ↦ ?_
    have hbase : (0 : ℝ) ≤ F a / p a := div_nonneg (hF a) (hpnonneg a)
    rw [← Real.rpow_natCast ((F a / p a) ^ (p a)) n, ← Real.rpow_mul hbase]
    have hexp : p a * (n : ℝ) = (σ a : ℝ) := by
      rw [hpdef]; field_simp
    rw [hexp, Real.rpow_natCast, div_pow]
  rw [hpow, le_div_iff₀ hden]
  calc ((WordType.typeClass n σ).card : ℝ) * (∏ a, F a ^ σ a) * ∏ a, p a ^ σ a
      = (((WordType.typeClass n σ).card : ℝ) * ∏ a, p a ^ σ a) * ∏ a, F a ^ σ a := by ring
    _ ≤ 1 * ∏ a, F a ^ σ a :=
        mul_le_mul_of_nonneg_right hone (Finset.prod_nonneg fun a _ ↦ pow_nonneg (hF a) _)
    _ = ∏ a, F a ^ σ a := one_mul _

end MethodOfTypes

/-! ## The exact leg count of a block profile -/

section Counting

variable {K : Type u} [CommSemiring K] {κ : Leg → Type v} {A : Leg → Type v}
variable [∀ i, Fintype (κ i)] [∀ i, DecidableEq (κ i)]
variable [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]

/-- **The size `|X_a|` of a block on one leg**: the number of leg-`c` variables carrying the block
label `a`.  This is Alman's `|X_i|`, `|Y_i|`, `|Z_i|` for the partition described by the block
labelling `blk`. -/
noncomputable def blockFiberCard (blk : ∀ i, κ i → A i) (c : Leg) (a : A c) : ℕ :=
  (WordType.letterFiber (blk c) a).card

omit [∀ i, Fintype (κ i)] [∀ i, DecidableEq (κ i)] [∀ i, Fintype (A i)]
  [∀ i, DecidableEq (A i)] in
/-- The block word of a leg word is the block labelling composed with it. -/
theorem coordinateBlockLegWord_eq_comp (blk : ∀ i, κ i → A i) (c : Leg) {n : ℕ}
    (w : Fin n → κ c) : coordinateBlockLegWord blk c w = blk c ∘ w := rfl

omit [∀ i, DecidableEq (κ i)] in
/-- **The exact count in Alman's proof of Theorem 5.3.**  The number of leg-`c` words of length
`n` whose block word has the multiplicity profile `σ` is

```
(number of block words of type σ) · ∏ₐ |X_a|^{σ a},
```

that is, a multinomial coefficient times a product of block sizes.  No hypothesis on `σ` is
needed: if `σ` is not a type of length `n` both sides vanish.

Proof sketch: fiber the words over their block words (`Finset.card_eq_sum_card_fiberwise`).  A
word lies over the block word `v` exactly when it is a coordinatewise lift of `v`, so its fiber is
`WordType.wordMapFiber (blk c) v`, of size `∏_pos |X_{v pos}|`; and a product over the positions of
`v` depends only on the multiplicities of `v` (`WordType.prod_word_eq_prod_pow`), which are `σ`. -/
theorem card_filter_multiplicity_coordinateBlockLegWord (blk : ∀ i, κ i → A i) (c : Leg) {n : ℕ}
    (σ : A c → ℕ) :
    ((Finset.univ : Finset (Fin n → κ c)).filter
        fun w ↦ WordType.multiplicity (coordinateBlockLegWord blk c w) = σ).card =
      (WordType.typeClass n σ).card * ∏ a, blockFiberCard blk c a ^ σ a := by
  classical
  set s := (Finset.univ : Finset (Fin n → κ c)).filter
    fun w ↦ WordType.multiplicity (coordinateBlockLegWord blk c w) = σ with hsdef
  have hmaps : ∀ w ∈ s, coordinateBlockLegWord blk c w ∈ WordType.typeClass n σ := by
    intro w hw
    exact WordType.mem_typeClass.mpr (Finset.mem_filter.mp hw).2
  rw [Finset.card_eq_sum_card_fiberwise hmaps]
  have hfib : ∀ v ∈ WordType.typeClass n σ,
      (s.filter fun w ↦ coordinateBlockLegWord blk c w = v).card =
        ∏ a, blockFiberCard blk c a ^ σ a := by
    intro v hv
    have hv' : WordType.multiplicity v = σ := WordType.mem_typeClass.mp hv
    have hset : (s.filter fun w ↦ coordinateBlockLegWord blk c w = v) =
        WordType.wordMapFiber (blk c) v := by
      ext w
      constructor
      · intro hw
        exact WordType.mem_wordMapFiber.mpr (Finset.mem_filter.mp hw).2
      · intro hw
        have h : coordinateBlockLegWord blk c w = v := WordType.mem_wordMapFiber.mp hw
        refine Finset.mem_filter.mpr ⟨?_, h⟩
        rw [hsdef]
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ w, by rw [h]; exact hv'⟩
    rw [hset, WordType.card_wordMapFiber,
      WordType.prod_word_eq_prod_pow (fun a ↦ (WordType.letterFiber (blk c) a).card) v, hv']
    rfl
  rw [Finset.sum_congr rfl hfib, Finset.sum_const, smul_eq_mul]

end Counting

/-! ## Theorem 5.3 for the asymptotic independence number -/

section BlockEntropy

variable {K : Type u} [CommSemiring K] {κ : Leg → Type v} {A : Leg → Type v}
variable [∀ i, Fintype (κ i)] [∀ i, DecidableEq (κ i)]
variable [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]

/-- The marginal of the normalized profile `τ/n` on a leg is the normalized pushed-forward
profile. -/
theorem pushforward_weight_eq {ι : Type w} [Fintype ι] {α : Type*} [Fintype α] [DecidableEq α]
    (f : ι → α) (τ : ι → ℕ) (n : ℕ)
    (p : ProbabilityVector ι) (hp : p.weight = fun j ↦ (τ j : ℝ) / n) (a : α) :
    (p.pushforward f).weight a = (WordType.mappedType f τ a : ℝ) / n := by
  classical
  rw [ProbabilityVector.pushforward_weight, hp, WordType.mappedType_eq_sum_ite]
  push_cast
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  by_cases h : f j = a <;> simp [h]

/-- **The finite form of Alman's Theorem 5.3 for the independence number.**  Suppose every term of
`T` lies in one of the blocks listed by `β : ι → BlockAddress A`, and suppose the real `M`
dominates, for *every* probability distribution `p` on the listed blocks, the block value
`p_c = ∏_a (|X_a| / p(X_a))^{p(X_a)}` of *at least one* leg `c` --- that is, `M` dominates
`min{p_X, p_Y, p_Z}` for every `p ∈ P(L)`.  Then every independent set of `T^{⊗n}` has at most

```
|types ι n| · M^n ≤ (n+1)^{|ι|} · M^n
```

elements.

Proof sketch.  Every letter of every element `p` of the independent set `S` is a term of `T`
(a nonzero product has no zero factor), hence lies in a listed block; choosing one block per
letter attaches to `p` a *block word* `w : Fin n → ι`, and `S` is covered by the classes `cls τ`
of elements admitting a block word of multiplicity type `τ`.  There are only `|types ι n|` classes.

Fix `τ` and choose, by hypothesis, a leg `c` with `p_c ≤ M` for the distribution `τ/n`.  The
projection `p ↦ p c` is injective on `S` (`Tensor.IndependentSet.injOn`) and maps `cls τ` into the
leg-`c` words whose block word has the pushed-forward profile `σ = mappedType (β · c) τ`, of which
there are exactly `|typeClass n σ| · ∏_a |X_a|^{σ a}`
(`card_filter_multiplicity_coordinateBlockLegWord`).  By the loss-free method of types
(`typeClass_card_mul_prod_pow_le_blockLegValue_pow`) that count is at most `p_c^n ≤ M^n`. -/
theorem IndependentSet.card_le_mul_pow_of_blockEntropy
    {T : (∀ i, κ i) → K} {blk : ∀ i, κ i → A i}
    {ι : Type w} [Fintype ι] [DecidableEq ι] {β : ι → BlockAddress A}
    (hcover : ∀ q : ∀ i, κ i, T q ≠ 0 → ∃ j : ι, ∀ i, blk i (q i) = β j i)
    {M : ℝ}
    (hbound : ∀ p : ProbabilityVector ι, ∃ c : Leg,
      blockLegValue (fun a ↦ (blockFiberCard blk c a : ℝ))
        ((p.pushforward fun j ↦ β j c).weight) ≤ M)
    {n : ℕ} (hn : 0 < n) {S : Finset (∀ i, Fin n → κ i)}
    (hS : IndependentSet (coordinatePower T n) S) :
    (S.card : ℝ) ≤ ((WordType.types ι n).card : ℝ) * M ^ n := by
  classical
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  set cls : (ι → ℕ) → Finset (∀ i, Fin n → κ i) := fun τ ↦
    S.filter fun p ↦ ∃ w : Fin n → ι, WordType.multiplicity w = τ ∧
      ∀ pos i, blk i (p i pos) = β (w pos) i with hclsdef
  -- Every element of `S` lies in the class of the type of one of its block words.
  have hcov : S ⊆ (WordType.types ι n).biUnion cls := by
    intro p hp
    have hletter : ∀ pos : Fin n, T (fun i ↦ p i pos) ≠ 0 := by
      intro pos h0
      refine hS.ne_zero p hp ?_
      rw [coordinatePower_apply]
      exact Finset.prod_eq_zero (Finset.mem_univ pos) h0
    choose w hw using fun pos ↦ hcover _ (hletter pos)
    refine Finset.mem_biUnion.mpr ⟨WordType.multiplicity w, WordType.multiplicity_mem_types w, ?_⟩
    exact Finset.mem_filter.mpr ⟨hp, ⟨w, rfl, fun pos i ↦ hw pos i⟩⟩
  -- Each class is small.
  have hclass : ∀ τ ∈ WordType.types ι n, ((cls τ).card : ℝ) ≤ M ^ n := by
    intro τ hτ
    have hτsum : ∑ j, τ j = n := WordType.mem_types.mp hτ
    set pτ : ProbabilityVector ι :=
      { weight := fun j ↦ (τ j : ℝ) / n
        nonneg := fun j ↦ by positivity
        total := by
          rw [← Finset.sum_div, show ∑ j, ((τ j : ℕ) : ℝ) = ((n : ℕ) : ℝ) by exact_mod_cast hτsum]
          field_simp } with hpτdef
    obtain ⟨c, hc⟩ := hbound pτ
    set σ : A c → ℕ := WordType.mappedType (fun j ↦ β j c) τ with hσdef
    have hσsum : ∑ a, σ a = n := by
      rw [hσdef, WordType.sum_mappedType, hτsum]
    have hmarg : (pτ.pushforward fun j ↦ β j c).weight = fun a ↦ (σ a : ℝ) / n := by
      funext a
      exact pushforward_weight_eq _ τ n pτ rfl a
    -- The leg-`c` projection injects the class into the words of block profile `σ`.
    have hcard : (cls τ).card ≤ ((Finset.univ : Finset (Fin n → κ c)).filter
        fun w ↦ WordType.multiplicity (coordinateBlockLegWord blk c w) = σ).card := by
      refine Finset.card_le_card_of_injOn (fun p ↦ p c) (fun p hp ↦ ?_) ?_
      · obtain ⟨w, hwτ, hwblk⟩ := (Finset.mem_filter.mp hp).2
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
        have hcomp : coordinateBlockLegWord blk c (p c) = (fun j ↦ β j c) ∘ w := by
          funext pos
          exact hwblk pos c
        rw [hcomp, WordType.multiplicity_comp_eq_mappedType, hwτ]
      · exact (hS.injOn c).mono (Finset.coe_subset.mpr (Finset.filter_subset _ _))
    rw [card_filter_multiplicity_coordinateBlockLegWord] at hcard
    have hcardR : ((cls τ).card : ℝ) ≤
        ((WordType.typeClass n σ).card : ℝ) * ∏ a, ((blockFiberCard blk c a : ℕ) : ℝ) ^ σ a := by
      have := (Nat.cast_le (α := ℝ)).mpr hcard
      simpa [Nat.cast_mul, Nat.cast_prod, Nat.cast_pow] using this
    refine hcardR.trans (le_trans (typeClass_card_mul_prod_pow_le_blockLegValue_pow hn
      (F := fun a ↦ ((blockFiberCard blk c a : ℕ) : ℝ)) (fun a ↦ by positivity) hσsum) ?_)
    refine pow_le_pow_left₀ (blockLegValue_nonneg (fun a ↦ by positivity)
      (fun a ↦ by positivity)) ?_ n
    rw [← hmarg] at *
    exact hc
  calc (S.card : ℝ) ≤ (((WordType.types ι n).biUnion cls).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hcov
    _ ≤ ((∑ τ ∈ WordType.types ι n, (cls τ).card : ℕ) : ℝ) := by
        exact_mod_cast Finset.card_biUnion_le
    _ = ∑ τ ∈ WordType.types ι n, ((cls τ).card : ℝ) := by push_cast; ring
    _ ≤ ∑ _τ ∈ WordType.types ι n, M ^ n := Finset.sum_le_sum hclass
    _ = ((WordType.types ι n).card : ℝ) * M ^ n := by
        rw [Finset.sum_const, nsmul_eq_mul]

end BlockEntropy

/-! ## Removing the polynomial loss -/

section Asymptotic

variable {K : Type u} [CommSemiring K] {κ : Leg → Type v} {A : Leg → Type v}
variable [∀ i, Fintype (κ i)] [∀ i, DecidableEq (κ i)]
variable [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]

/-- **Alman's Theorem 5.3 for the asymptotic independence number** [Alman2019, Theorem 5.3].

Let `blk` be a block labelling of the variables of each leg of the coefficient table `T`, let
`β : ι → BlockAddress A` list a set of blocks covering the support of `T`, and let `M` be a real
that dominates `min{p_X, p_Y, p_Z}` for *every* probability distribution `p` on `ι` --- where
`p_c = ∏_a (|X_a| / p(X_a))^{p(X_a)}` is Alman's block value of leg `c` at the marginal of `p`.
Then

```
Ī(T) ≤ M.
```

Alman's statement is `S̃(T) ≤ limsup_{p ∈ P(L)} min{p_X, p_Y, p_Z}` for the asymptotic slice rank;
the same counting argument gives the same bound for `Ī`, and the supremum over the simplex is
replaced by an arbitrary dominating constant, so that no compactness or attainment is needed.

Proof sketch: `IndependentSet.card_le_mul_pow_of_blockEntropy` gives
`I(T^{⊗n}) ≤ |types ι n| · M^n ≤ (n+1)^{|ι|} · M^n` for every `n ≥ 1`, and
`asymptoticIndependenceNumber_le_of_subexponential_mul_pow` removes the polynomial factor. -/
theorem asymptoticIndependenceNumber_le_of_blockEntropy
    [NoZeroDivisors K] [Nontrivial K] {T : (∀ i, κ i) → K} {blk : ∀ i, κ i → A i}
    {ι : Type w} [Fintype ι] [DecidableEq ι] {β : ι → BlockAddress A}
    (hcover : ∀ q : ∀ i, κ i, T q ≠ 0 → ∃ j : ι, ∀ i, blk i (q i) = β j i)
    {M : ℝ} (hM : 0 ≤ M)
    (hbound : ∀ p : ProbabilityVector ι, ∃ c : Leg,
      blockLegValue (fun a ↦ (blockFiberCard blk c a : ℝ))
        ((p.pushforward fun j ↦ β j c).weight) ≤ M) :
    asymptoticIndependenceNumber T ≤ M := by
  refine asymptoticIndependenceNumber_le_of_subexponential_mul_pow hM
    (Growth.Subexponential.natCast_succ_pow (Fintype.card ι)) fun n hn ↦ ?_
  obtain ⟨S, hS, hcard⟩ := exists_independentSet_card_eq (coordinatePower T n)
  rw [← hcard]
  refine le_trans (IndependentSet.card_le_mul_pow_of_blockEntropy hcover hbound hn hS) ?_
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast WordType.card_types_le ι n) (by positivity)

/-- **The trivial case of Theorem 5.3**, Alman's remark that `p_X ≤ q` always: taking the block
value bound `blockLegValue_le_sum` on one fixed leg recovers `Ī(T) ≤ ∑_a |X_a| = |κ c|`, the bound
`asymptoticIndependenceNumber_le_card`.  It is recorded as a consistency check on the statement of
`asymptoticIndependenceNumber_le_of_blockEntropy`. -/
theorem asymptoticIndependenceNumber_le_sum_blockFiberCard
    [NoZeroDivisors K] [Nontrivial K] {T : (∀ i, κ i) → K} {blk : ∀ i, κ i → A i}
    {ι : Type w} [Fintype ι] [DecidableEq ι] {β : ι → BlockAddress A}
    (hcover : ∀ q : ∀ i, κ i, T q ≠ 0 → ∃ j : ι, ∀ i, blk i (q i) = β j i) (c : Leg) :
    asymptoticIndependenceNumber T ≤ ∑ a, (blockFiberCard blk c a : ℝ) := by
  refine asymptoticIndependenceNumber_le_of_blockEntropy hcover
    (Finset.sum_nonneg fun a _ ↦ by positivity) fun p ↦ ⟨c, ?_⟩
  exact blockLegValue_le_sum (fun a ↦ by positivity)
    (fun a ↦ (p.pushforward fun j ↦ β j c).nonneg a) (p.pushforward fun j ↦ β j c).total

end Asymptotic

end AlgebraicComplexity.Tensor
