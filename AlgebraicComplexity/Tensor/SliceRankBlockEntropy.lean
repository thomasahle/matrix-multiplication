/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Tensor.AsymptoticSliceRank
import AlgebraicComplexity.Tensor.IndependenceBlockEntropy

/-!
# The block-partition entropy bound for the asymptotic slice rank

This file proves, for the asymptotic slice rank `S̃`, the block-partition tool of

> J. Alman, *Limits on the Universal Method for Matrix Multiplication*, PhD thesis, MIT 2019,
> Section 5.3.2, Theorem 5.3 [Alman2019],

in the form in which Alman states it.  `Tensor/IndependenceBlockEntropy.lean` proves the same
bound for the asymptotic independence number `Ī`; the set-up (block labelling `blk`, list of
non-zero blocks `β : ι → BlockAddress A`, covering hypothesis `hcover`, block value
`blockLegValue` --- the entropy value of `Probability/EntropyValue.lean` --- and block sizes
`blockFiberCard`) is shared verbatim with that file, and so is the
counting: the exact leg count `card_filter_multiplicity_coordinateBlockLegWord` and the loss-free
method of types `typeClass_card_mul_prod_pow_le_blockLegValue_pow`.

Only the *use* of the count differs.  For `Ī` one injects an independent set into the leg-`c`
variables of `T^{⊗n}`; here one splits the tensor itself.

## The proof, in Alman's words and here

Alman writes `T^{⊗n} = ∑_τ T_τ`, the sum over the multiplicity types `τ` of the block words, and
observes that `T_τ` is supported on triples of words whose leg-`c` block word has the pushed
forward profile `τ_c`; hence `T_τ` is a sum of `#{leg-c words of profile τ_c}` slices along leg
`c`, and slice rank is subadditive.  Since there are only `|types ι n| ≤ (n+1)^{|ι|}` types, the
bound `S(T^{⊗n}) ≤ poly(n)·max_τ min_c #{leg-c words of profile τ_c}` follows, and the count is at
most `M^n` by the method of types.

The formalization follows this exactly, with two care points.

* **The splitting must be a genuine partition of the support, not a cover.**  `hcover` only says
  that every term of `T` lies in *some* listed block, so a choice function `pick` selects one
  block per term (`Classical.choose`), and the classes are the fibres of the resulting block word.
  A listed block that does not occur, or two labels with the same address, are therefore harmless,
  exactly as in the `Ī` version.  When `ι` is empty the hypothesis forces `T = 0` and the statement
  is trivial; that case is dispatched separately rather than by requiring `Nonempty ι`.
* **Slice rank of a coordinate table with restricted support.**
  `sliceRankAlong_coordinateTensor_le_card_of_support` is the reusable form of "`T_τ` is a sum of
  `|E|` slices": if every non-zero coefficient of a coefficient table has its leg-`c` variable in a
  finite set `E`, the leg-`c` slice rank of the tensor is at most `|E|`.  This is *not* an instance
  of `sliceRankAlong_le_card_of_span`, which needs a family spanning the whole leg space; here `E`
  spans only a subspace, and the point is that the tensor lives in that subspace.

## Main results

* `sliceRank_sum_le`: subadditivity of slice rank over a finite sum (the `Finset` form of
  `sliceRank_add_le`).
* `sliceRankAlong_coordinateTensor_le_card_of_support`: the support bound described above.
* `sliceRank_coordinateTensor_coordinatePower_le_of_blockEntropy`: **the finite form of Theorem
  5.3**, `S(T^{⊗n}) ≤ |types ι n| · M^n`, with the same hypothesis `hbound` as
  `IndependentSet.card_le_mul_pow_of_blockEntropy`.
* `asymptoticSliceRank_le_of_subexponential_mul_pow`: a subexponential multiplicative loss does not
  affect `S̃`.  Unlike its `Ī` twin this needs no supermultiplicativity --- and hence no
  `NoZeroDivisors` --- because `Growth.exponentialRate` is by definition tolerant of constants.
* `asymptoticSliceRank_coordinateTensor_le_of_blockEntropy` (**Theorem 5.3 for `S̃`**):
  `S̃(T) ≤ M` under the hypotheses of `asymptoticIndependenceNumber_le_of_blockEntropy`.
  Together with `asymptoticIndependenceNumber_le_asymptoticSliceRank` it *implies* the latter, but
  the two are kept separate: the `Ī` statement is available over an arbitrary commutative semiring
  without zero divisors and does not mention the abstract tensor.

## Deviations from the thesis

The deviations of `Tensor/IndependenceBlockEntropy.lean` apply verbatim: the polynomial loss is
explicit rather than hidden in `o(n)`, the multinomial estimate is loss-free, the optimization over
the simplex is replaced by an arbitrary dominating constant `M`, and Alman's symmetrization
(Proposition 5.4) is not needed.  In addition, no hypothesis on `K` beyond `CommSemiring` is used:
the argument is a decomposition of a tensor, not a lower-bound argument.

## Position in the library

Layer 1.  It imports `Tensor/AsymptoticSliceRank.lean` and `Tensor/IndependenceBlockEntropy.lean`
and nothing else; through the latter it inherits the same three Mathlib-only leaves
(`Combinatorics/WordType.lean`, `Probability/Finite.lean`, `Analysis/Subexponential.lean`).
Nothing here mentions a named matrix-multiplication construction or a numerical bound.
-/

namespace AlgebraicComplexity.Tensor

open scoped BigOperators

universe u v w

/-! ## Subadditivity of slice rank over a finite sum -/

section Subadditive

variable {K : Type u} [CommSemiring K]
variable {V : Leg → Type v} [∀ c, AddCommMonoid (V c)] [∀ c, Module K (V c)]

/-- **Slice rank is subadditive over a finite sum**, the `Finset` form of `sliceRank_add_le`. -/
theorem sliceRank_sum_le {ι : Type*} (s : Finset ι) (f : ι → Tensor3 K V) :
    sliceRank (∑ i ∈ s, f i) ≤ ∑ i ∈ s, sliceRank (f i) := by
  classical
  induction s using Finset.cons_induction with
  | empty => simp
  | cons i s hi ih =>
      rw [Finset.sum_cons, Finset.sum_cons]
      exact (sliceRank_add_le _ _).trans (Nat.add_le_add_left ih _)

end Subadditive

/-! ## Slice rank of a coefficient table with restricted support -/

section CoordinateSupport

variable {K : Type u} [CommSemiring K]
variable {V : Leg → Type v} [∀ c, AddCommMonoid (V c)] [∀ c, Module K (V c)]

/-- Helper: a scalar multiple of a pure tensor is again a pure tensor, with the scalar absorbed
into its leg-`d` component.  (A private copy of the same helper in `Tensor/SliceRank.lean`.) -/
private theorem smul_pure_eq_pure_update_aux (d : Leg) (a : K) (y : ∀ j, V j) :
    a • pure (K := K) y = pure (K := K) (Function.update y d (a • y d)) := by
  calc a • pure (K := K) y
      = a • pure (K := K) (Function.update y d (y d)) := by rw [Function.update_eq_self]
    _ = pure (K := K) (Function.update y d (a • y d)) :=
        ((PiTensorProduct.tprod K).map_update_smul y d a (y d)).symm

/-- A scalar multiple of a pure tensor is a slice term with the *unchanged* leg-`c` vector: park
the scalar on the leg `cycle c ≠ c`. -/
private theorem sliceTermWith_smul_pure {c : Leg} (a : K) (x : ∀ i, V i) :
    SliceTermWith c (x c) (a • pure (K := K) x) := by
  have hne : c ≠ cycle c := by cases c <;> decide
  rw [smul_pure_eq_pure_update_aux (cycle c) a x]
  exact SliceTermWith.pure_tensor _ (Function.update_of_ne hne _ _)

/-- Slice terms with a common leg-`c` vector are closed under finite sums. -/
private theorem sliceTermWith_finset_sum {ι : Type*} {c : Leg} {v : V c} (s : Finset ι)
    (f : ι → Tensor3 K V) (h : ∀ i ∈ s, SliceTermWith c v (f i)) :
    SliceTermWith c v (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.cons_induction with
  | empty => simpa using SliceTermWith.zero c v
  | cons i s hi ih =>
      rw [Finset.sum_cons]
      exact (h i (Finset.mem_cons_self i s)).add
        (ih fun j hj ↦ h j (Finset.mem_cons_of_mem hj))

variable {μ : Leg → Type v} [∀ i, Fintype (μ i)] [∀ i, DecidableEq (μ i)]

/-- **The support bound for a single-leg slice rank.**  If every non-zero coefficient of the
coefficient table `S` has its leg-`c` variable in the finite set `E`, then

```
S_c (coordinateTensor S) ≤ |E|.
```

This is the estimate behind Alman's "`T_τ` is a sum of `#{leg-c words of profile τ_c}` slices"
(Theorem 5.3) and, for `E = univ`, of thesis Lemma 5.1(5).

Proof sketch: write `coordinateTensor S = ∑_q S q · e_{q X} ⊗ e_{q Y} ⊗ e_{q Z}`
(`coordinateTensor_eq_sum`), drop the terms with `q c ∉ E` (they vanish by hypothesis) and group
the rest by the value of `q c` (`Finset.sum_fiberwise_of_maps_to`).  The group attached to `x ∈ E`
is a sum of scalar multiples of pure tensors all of whose leg-`c` component is the basis vector
`e_x`, hence a slice term along `c` with that common vector. -/
theorem sliceRankAlong_coordinateTensor_le_card_of_support (S : (∀ i, μ i) → K) (c : Leg)
    (E : Finset (μ c)) (hsupp : ∀ q, S q ≠ 0 → q c ∈ E) :
    sliceRankAlong c (coordinateTensor S) ≤ E.card := by
  classical
  set g : (∀ i, μ i) → Tensor3 K (CoordinateSpace K μ) :=
    fun q ↦ S q • pure (K := K) (fun i ↦ Pi.single (q i) (1 : K)) with hgdef
  set s : Finset (∀ i, μ i) := Finset.univ.filter fun q ↦ q c ∈ E with hsdef
  refine sliceRankAlong_le_iff.mpr
    ⟨E.toList.map fun x ↦ ∑ q ∈ s.filter fun q ↦ q c = x, g q, by simp, ?_, ?_⟩
  · intro R hR
    obtain ⟨x, -, rfl⟩ := List.mem_map.mp hR
    refine SliceTermWith.sliceTermAlong (v := Pi.single x (1 : K)) ?_
    refine sliceTermWith_finset_sum _ _ fun q hq ↦ ?_
    have hqx : q c = x := (Finset.mem_filter.mp hq).2
    have := sliceTermWith_smul_pure (V := CoordinateSpace K μ) (c := c) (S q)
      (fun i ↦ Pi.single (q i) (1 : K))
    rwa [hqx] at this
  · rw [Finset.sum_map_toList, coordinateTensor_eq_sum]
    rw [Finset.sum_fiberwise_of_maps_to (fun q hq ↦ (Finset.mem_filter.mp hq).2) g]
    refine (Finset.sum_filter_of_ne fun q _ hne ↦ hsupp q ?_).symm
    intro h0
    exact hne (by simp [h0])

end CoordinateSupport

/-! ## Removing a subexponential loss from an asymptotic slice rank bound -/

section Loss

variable {K : Type u} [CommSemiring K]
variable {V : Leg → Type v} [∀ c, AddCommMonoid (V c)] [∀ c, Module K (V c)]

/-- **A subexponential multiplicative loss does not affect `S̃`.**  If

```
S(T^{⊗n}) ≤ loss(n) · M^n   for every n ≥ 1
```

with `loss` subexponential, then `S̃(T) ≤ M`.  This is the rate-level replacement for Alman's
"and the desired result follows" after a bound with a `poly(n)` factor.

Unlike its twin `asymptoticIndependenceNumber_le_of_subexponential_mul_pow` for `Ī`, this needs no
supermultiplicativity of the underlying sequence --- slice rank has none --- because
`Growth.exponentialRate` is an infimum over *constant-tolerant* exponential bounds by definition.

Proof sketch: for `ε > 0` put `δ = (M+ε)/(M+ε/2) > 1`; then `loss(n) ≤ C·δ^n` for some `C > 0` and
`δ·M ≤ M+ε`, so `M+ε` is an admissible exponential base with constant `C+1`; the value at `n = 0`
is `S(T^{⊗0}) ≤ 1`, absorbed by the `+1`. -/
theorem asymptoticSliceRank_le_of_subexponential_mul_pow {T : Tensor3 K V} {M : ℝ} {loss : ℕ → ℝ}
    (hM : 0 ≤ M) (hloss : Growth.Subexponential loss)
    (h : ∀ n, 0 < n → ((sliceRank (power T n) : ℕ) : ℝ) ≤ loss n * M ^ n) :
    asymptoticSliceRank T ≤ M := by
  refine le_of_forall_pos_le_add fun ε hε ↦ ?_
  have hpos2 : 0 < M + ε / 2 := by linarith
  set δ : ℝ := (M + ε) / (M + ε / 2) with hδdef
  have hδ : 1 < δ := by
    rw [hδdef, lt_div_iff₀ hpos2]; linarith
  obtain ⟨C, hC, hlossC⟩ := hloss.2 δ hδ
  have hδM : δ * M ≤ M + ε := by
    rw [hδdef, div_mul_eq_mul_div, div_le_iff₀ hpos2]
    nlinarith
  refine asymptoticSliceRank_le ⟨by linarith, C + 1, by linarith, fun n ↦ ?_⟩
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have h0 : sliceRankPowerSequence T 0 ≤ 1 := by
      have := sliceRank_power_le_maxSliceRankAlong_pow T 0
      simpa [sliceRankPowerSequence] using this
    have h0R : ((sliceRankPowerSequence T 0 : ℕ) : ℝ) ≤ 1 := by exact_mod_cast h0
    rw [pow_zero, mul_one]
    linarith
  · calc ((sliceRankPowerSequence T n : ℕ) : ℝ) ≤ loss n * M ^ n := h n hn
      _ ≤ (C * δ ^ n) * M ^ n := mul_le_mul_of_nonneg_right (hlossC n) (by positivity)
      _ = C * (δ * M) ^ n := by rw [mul_pow]; ring
      _ ≤ C * (M + ε) ^ n :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hδM n) hC.le
      _ ≤ (C + 1) * (M + ε) ^ n :=
          mul_le_mul_of_nonneg_right (by linarith) (by positivity)

end Loss

/-! ## Theorem 5.3 for the slice rank -/

section BlockEntropy

variable {K : Type u} [CommSemiring K] {κ : Leg → Type v} {A : Leg → Type v}
variable [∀ i, Fintype (κ i)] [∀ i, DecidableEq (κ i)]
variable [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]

/-- **The finite form of Alman's Theorem 5.3 for the slice rank.**  Suppose every term of `T` lies
in one of the blocks listed by `β : ι → BlockAddress A`, and suppose the real `M` dominates, for
*every* probability distribution `p` on the listed blocks, the block value
`p_c = ∏_a (|X_a| / p(X_a))^{p(X_a)}` of *at least one* leg `c` --- that is, `M` dominates
`min{p_X, p_Y, p_Z}` for every `p ∈ P(L)`.  Then, for every `n ≥ 1`,

```
S(T^{⊗n}) ≤ |types ι n| · M^n ≤ (n+1)^{|ι|} · M^n.
```

The hypotheses are literally those of `IndependentSet.card_le_mul_pow_of_blockEntropy`, so a client
proves them once and gets both bounds.

Proof sketch.  Choosing one listed block per term of `T` (`hcover` plus `Classical.choose`)
attaches to every triple of length-`n` words a *block word* `w : Fin n → ι`, and splitting
`T^{⊗n}` according to the multiplicity type `τ` of that block word writes it as a sum of
`|types ι n|` coefficient tables `T_τ`.  Slice rank is subadditive
(`sliceRank_sum_le`), so it suffices to bound each `S(T_τ)`.

Fix `τ` and choose, by hypothesis, a leg `c` with `p_c ≤ M` for the distribution `τ/n`.  Every
non-zero coefficient of `T_τ` has all of its letters in listed blocks, so its leg-`c` word has
block profile `σ = mappedType (β · c) τ`; there are exactly
`|typeClass n σ| · ∏_a |X_a|^{σ a}` such words
(`card_filter_multiplicity_coordinateBlockLegWord`), whence
`S(T_τ) ≤ S_c(T_τ) ≤ |typeClass n σ| · ∏_a |X_a|^{σ a}`
(`sliceRankAlong_coordinateTensor_le_card_of_support`).  By the loss-free method of types
(`typeClass_card_mul_prod_pow_le_blockLegValue_pow`) that count is at most `p_c^n ≤ M^n`. -/
theorem sliceRank_coordinateTensor_coordinatePower_le_of_blockEntropy
    {T : (∀ i, κ i) → K} {blk : ∀ i, κ i → A i}
    {ι : Type w} [Fintype ι] [DecidableEq ι] {β : ι → BlockAddress A}
    (hcover : ∀ q : ∀ i, κ i, T q ≠ 0 → ∃ j : ι, ∀ i, blk i (q i) = β j i)
    {M : ℝ} (hM : 0 ≤ M)
    (hbound : ∀ p : ProbabilityVector ι, ∃ c : Leg,
      blockLegValue (fun a ↦ (blockFiberCard blk c a : ℝ))
        ((p.pushforward fun j ↦ β j c).weight) ≤ M)
    {n : ℕ} (hn : 0 < n) :
    ((sliceRank (coordinateTensor (coordinatePower T n)) : ℕ) : ℝ) ≤
      ((WordType.types ι n).card : ℝ) * M ^ n := by
  classical
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hRHS : 0 ≤ ((WordType.types ι n).card : ℝ) * M ^ n :=
    mul_nonneg (by positivity) (pow_nonneg hM n)
  rcases isEmpty_or_nonempty ι with hι | hι
  · -- No listed blocks: the covering hypothesis forces `T = 0`.
    have hT : ∀ q : ∀ i, κ i, T q = 0 := by
      intro q
      by_contra h
      obtain ⟨j, -⟩ := hcover q h
      exact hι.false j
    have hpow : coordinatePower T n = 0 := by
      funext p
      rw [coordinatePower_apply]
      exact Finset.prod_eq_zero (Finset.mem_univ ⟨0, hn⟩) (hT _)
    have hzero : coordinateTensor (coordinatePower T n) = 0 := by
      rw [hpow]
      refine standardCoordinate_ext (K := K) fun q ↦ ?_
      rw [standardCoordinateEquiv_coordinateTensor]
      simp
    rw [hzero, sliceRank_zero]
    simpa using hRHS
  · obtain ⟨j₀⟩ := hι
    -- One listed block per term of `T`.
    set pick : (∀ i, κ i) → ι := fun q ↦
      if h : ∃ j : ι, ∀ i, blk i (q i) = β j i then h.choose else j₀ with hpickdef
    have hpick : ∀ q : ∀ i, κ i, T q ≠ 0 → ∀ i, blk i (q i) = β (pick q) i := by
      intro q hq i
      have h : ∃ j : ι, ∀ i, blk i (q i) = β j i := hcover q hq
      rw [hpickdef]
      simp only [dif_pos h]
      exact h.choose_spec i
    -- The block word of a triple of length-`n` words, and the resulting splitting.
    set bword : (∀ i, Fin n → κ i) → (Fin n → ι) :=
      fun p pos ↦ pick fun i ↦ p i pos with hbworddef
    set part : (ι → ℕ) → ((∀ i, Fin n → κ i) → K) := fun τ p ↦
      if WordType.multiplicity (bword p) = τ then coordinatePower T n p else 0 with hpartdef
    have hpartapp : ∀ (τ' : ι → ℕ) (p : ∀ i, Fin n → κ i),
        part τ' p =
          if WordType.multiplicity (bword p) = τ' then coordinatePower T n p else 0 :=
      fun _ _ ↦ rfl
    have hsplit : coordinatePower T n = ∑ τ ∈ WordType.types ι n, part τ := by
      funext p
      rw [Finset.sum_apply,
        Finset.sum_eq_single_of_mem (WordType.multiplicity (bword p))
          (WordType.multiplicity_mem_types _)]
      · rw [hpartapp]
        simp
      · intro τ _ hne
        rw [hpartapp, if_neg (Ne.symm hne)]
    have hten : coordinateTensor (coordinatePower T n) =
        ∑ τ ∈ WordType.types ι n, coordinateTensor (part τ) := by
      rw [hsplit]
      exact map_sum (standardCoordinateEquiv (K := K) (κ := fun i ↦ Fin n → κ i)).symm _ _
    -- Each class of the splitting has small slice rank.
    have hclass : ∀ τ ∈ WordType.types ι n,
        ((sliceRank (coordinateTensor (part τ)) : ℕ) : ℝ) ≤ M ^ n := by
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
      have hσsum : ∑ a, σ a = n := by rw [hσdef, WordType.sum_mappedType, hτsum]
      have hmarg : (pτ.pushforward fun j ↦ β j c).weight = fun a ↦ (σ a : ℝ) / n := by
        funext a
        exact pushforward_weight_eq _ τ n pτ rfl a
      set E : Finset (Fin n → κ c) := Finset.univ.filter
        fun w ↦ WordType.multiplicity (coordinateBlockLegWord blk c w) = σ with hEdef
      -- The class is supported on leg-`c` words of block profile `σ`.
      have hsupp : ∀ p : ∀ i, Fin n → κ i, part τ p ≠ 0 → p c ∈ E := by
        intro p hp
        have hcond : WordType.multiplicity (bword p) = τ := by
          by_contra hne
          exact hp (by rw [hpartapp, if_neg hne])
        have hne : coordinatePower T n p ≠ 0 := by
          intro h0
          exact hp (by rw [hpartapp, h0, ite_self])
        have hletter : ∀ pos : Fin n, T (fun i ↦ p i pos) ≠ 0 := by
          intro pos h0
          exact hne (Finset.prod_eq_zero (Finset.mem_univ pos) h0)
        have hcomp : coordinateBlockLegWord blk c (p c) = (fun j ↦ β j c) ∘ bword p := by
          funext pos
          exact hpick _ (hletter pos) c
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
        rw [hcomp, WordType.multiplicity_comp_eq_mappedType, hcond]
      have hcard : sliceRank (coordinateTensor (part τ)) ≤ E.card :=
        (sliceRank_le_sliceRankAlong c _).trans
          (sliceRankAlong_coordinateTensor_le_card_of_support (part τ) c E hsupp)
      have hEcount : E.card =
          (WordType.typeClass n σ).card * ∏ a, blockFiberCard blk c a ^ σ a :=
        card_filter_multiplicity_coordinateBlockLegWord blk c σ
      have hcardR : ((sliceRank (coordinateTensor (part τ)) : ℕ) : ℝ) ≤
          ((WordType.typeClass n σ).card : ℝ) *
            ∏ a, ((blockFiberCard blk c a : ℕ) : ℝ) ^ σ a := by
        have h := (Nat.cast_le (α := ℝ)).mpr (hcard.trans_eq hEcount)
        simpa [Nat.cast_mul, Nat.cast_prod, Nat.cast_pow] using h
      refine hcardR.trans (le_trans (typeClass_card_mul_prod_pow_le_blockLegValue_pow hn
        (F := fun a ↦ ((blockFiberCard blk c a : ℕ) : ℝ)) (fun a ↦ by positivity) hσsum) ?_)
      refine pow_le_pow_left₀ (blockLegValue_nonneg (fun a ↦ by positivity)
        (fun a ↦ by positivity)) ?_ n
      rw [← hmarg]
      exact hc
    calc ((sliceRank (coordinateTensor (coordinatePower T n)) : ℕ) : ℝ)
        ≤ ((∑ τ ∈ WordType.types ι n, sliceRank (coordinateTensor (part τ)) : ℕ) : ℝ) := by
          rw [hten]
          exact_mod_cast sliceRank_sum_le _ _
      _ = ∑ τ ∈ WordType.types ι n, ((sliceRank (coordinateTensor (part τ)) : ℕ) : ℝ) := by
          push_cast
          ring
      _ ≤ ∑ _τ ∈ WordType.types ι n, M ^ n := Finset.sum_le_sum hclass
      _ = ((WordType.types ι n).card : ℝ) * M ^ n := by
          rw [Finset.sum_const, nsmul_eq_mul]

/-- **Alman's Theorem 5.3** [Alman2019, Theorem 5.3], in the form he states it.

Let `blk` be a block labelling of the variables of each leg of the coefficient table `T`, let
`β : ι → BlockAddress A` list a set of blocks covering the support of `T`, and let `M` be a real
that dominates `min{p_X, p_Y, p_Z}` for *every* probability distribution `p` on `ι` --- where
`p_c = ∏_a (|X_a| / p(X_a))^{p(X_a)}` is Alman's block value of leg `c` at the marginal of `p`.
Then

```
S̃(T) ≤ M.
```

The supremum over the simplex of Alman's statement is replaced by an arbitrary dominating
constant, so that no compactness or attainment is needed.

Proof sketch: `sliceRank_coordinateTensor_coordinatePower_le_of_blockEntropy` gives
`S(T^{⊗n}) ≤ |types ι n| · M^n ≤ (n+1)^{|ι|} · M^n` for every `n ≥ 1` --- after transporting the
word-indexed Kronecker power to the canonical tensor power along
`Isomorphic.coordinateTensor_coordinatePower` --- and
`asymptoticSliceRank_le_of_subexponential_mul_pow` removes the polynomial factor. -/
theorem asymptoticSliceRank_coordinateTensor_le_of_blockEntropy
    {T : (∀ i, κ i) → K} {blk : ∀ i, κ i → A i}
    {ι : Type w} [Fintype ι] [DecidableEq ι] {β : ι → BlockAddress A}
    (hcover : ∀ q : ∀ i, κ i, T q ≠ 0 → ∃ j : ι, ∀ i, blk i (q i) = β j i)
    {M : ℝ} (hM : 0 ≤ M)
    (hbound : ∀ p : ProbabilityVector ι, ∃ c : Leg,
      blockLegValue (fun a ↦ (blockFiberCard blk c a : ℝ))
        ((p.pushforward fun j ↦ β j c).weight) ≤ M) :
    asymptoticSliceRank (coordinateTensor T) ≤ M := by
  refine asymptoticSliceRank_le_of_subexponential_mul_pow hM
    (Growth.Subexponential.natCast_succ_pow (Fintype.card ι)) fun n hn ↦ ?_
  have hiso : sliceRank (power (coordinateTensor T) n) =
      sliceRank (coordinateTensor (coordinatePower T n)) :=
    (sliceRank_isomorphic (Isomorphic.coordinateTensor_coordinatePower T n)).symm
  rw [hiso]
  refine le_trans (sliceRank_coordinateTensor_coordinatePower_le_of_blockEntropy hcover hM
    hbound hn) ?_
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast WordType.card_types_le ι n)
    (pow_nonneg hM n)

/-- **The trivial case of Theorem 5.3 for `S̃`**, Alman's remark that `p_X ≤ q` always: on one
fixed leg the block value bound `blockLegValue_le_sum` recovers `S̃(T) ≤ ∑_a |X_a| = |κ c|`.  It is
recorded as a consistency check on the statement of
`asymptoticSliceRank_coordinateTensor_le_of_blockEntropy`, mirroring
`asymptoticIndependenceNumber_le_sum_blockFiberCard`. -/
theorem asymptoticSliceRank_coordinateTensor_le_sum_blockFiberCard
    {T : (∀ i, κ i) → K} {blk : ∀ i, κ i → A i}
    {ι : Type w} [Fintype ι] [DecidableEq ι] {β : ι → BlockAddress A}
    (hcover : ∀ q : ∀ i, κ i, T q ≠ 0 → ∃ j : ι, ∀ i, blk i (q i) = β j i) (c : Leg) :
    asymptoticSliceRank (coordinateTensor T) ≤ ∑ a, (blockFiberCard blk c a : ℝ) := by
  refine asymptoticSliceRank_coordinateTensor_le_of_blockEntropy hcover
    (Finset.sum_nonneg fun a _ ↦ by positivity) fun p ↦ ⟨c, ?_⟩
  exact blockLegValue_le_sum (fun a ↦ by positivity)
    (fun a ↦ (p.pushforward fun j ↦ β j c).nonneg a) (p.pushforward fun j ↦ β j c).total

end BlockEntropy

end AlgebraicComplexity.Tensor
