/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import Mathlib.Analysis.MeanInequalities

/-!
# The entropy value of a finite weight vector

For nonnegative weights `F : α → ℝ` on a finite alphabet and a probability vector `p` on the same
alphabet, the **entropy value**

```
blockLegValue F p = ∏ₐ (F a / p a) ^ (p a) = 2^{H(p)} · ∏ₐ F a ^ {p a}
```

measures how much mass the weights carry when they are read at the "rate" `p`.  It is the quantity
Alman calls `p_X` in the block-partition bounds for asymptotic slice rank and the asymptotic
independence number, but nothing in this file mentions tensors, blocks or legs: the statements are
pure finite-probability convexity facts about an arbitrary finite alphabet.

The exponent is a real `rpow`, whose convention `x ^ (0 : ℝ) = 1` is exactly the convention
`p_a^{p_a} = 1` at `p_a = 0`; letters of zero mass therefore contribute the factor `1` with no side
condition anywhere in this file.

## Main definitions

* `blockLegValue F p`: the entropy value above.

## Main results

* `blockLegValue_nonneg`: the entropy value is nonnegative.
* `blockLegValue_le_sum`: `∏ₐ (F a / p a)^{p a} ≤ ∑ₐ F a`, Jensen's inequality for `log`.  For
  weights that are block sizes on a leg carrying `q` variables the right-hand side is `q`.
* `blockLegValue_le_prod_rpow`: **the reference-vector (Gibbs) form**,
  `blockLegValue F p ≤ ∏ₐ (F a / r a)^{p a}` for *every* full-support probability vector `r`.  The
  right-hand side is log-linear in `p`, which is what turns an optimization over the simplex into a
  finite check; it is the workhorse of the numerical clients.

## Position in the library

Layer 2 (`AlgebraicComplexity/Probability/`).  It imports only Mathlib's mean inequalities and is
independent of `Probability/Finite.lean`: the statements take the weight functions and the
probability vector as bare functions together with the hypotheses they need, so that clients can
apply them to marginals, pushforwards and normalized multiplicity profiles alike.

Clients: `Tensor/IndependenceBlockEntropy.lean` (Alman's Theorem 5.3 for `Ī`) and
`Tensor/SliceRankBlockEntropy.lean` (the same theorem for `S̃`).
-/

namespace AlgebraicComplexity

open scoped BigOperators

variable {α : Type*} [Fintype α]

/-- **The entropy value** of a nonnegative weight vector `F` read at a probability vector `p`:

```
blockLegValue F p = ∏ₐ (F a / p a)^{p a} = 2^{H(p)} · ∏ₐ F a^{p a}.
```

The exponent is a real `rpow`, whose convention `x ^ (0 : ℝ) = 1` is exactly the convention
`p_a^{p_a} = 1` at `p_a = 0`; letters of zero mass therefore contribute the factor `1` with no side
condition. -/
noncomputable def blockLegValue (F p : α → ℝ) : ℝ :=
  ∏ a : α, (F a / p a) ^ (p a)

/-- The entropy value is nonnegative. -/
theorem blockLegValue_nonneg {F p : α → ℝ} (hF : ∀ a, 0 ≤ F a) (hp : ∀ a, 0 ≤ p a) :
    0 ≤ blockLegValue F p :=
  Finset.prod_nonneg fun a _ ↦ Real.rpow_nonneg (div_nonneg (hF a) (hp a)) _

/-- **Jensen's inequality for `log`**: `blockLegValue F p ≤ ∑ₐ F a`.  When the weights are the
block sizes on a leg carrying `q` variables the right-hand side is `q`, which is the remark that
`p_X ≤ q` always, with equality only for the proportional marginal.

Proof sketch: `Real.geom_mean_le_arith_mean_weighted` with weights `p` and values `F/p` gives
`∏ (F a / p a)^{p a} ≤ ∑ p a · (F a / p a)`, and each summand is `F a` when `p a ≠ 0` and `0`
otherwise. -/
theorem blockLegValue_le_sum {F p : α → ℝ} (hF : ∀ a, 0 ≤ F a) (hp : ∀ a, 0 ≤ p a)
    (hsum : ∑ a, p a = 1) : blockLegValue F p ≤ ∑ a, F a := by
  refine le_trans (Real.geom_mean_le_arith_mean_weighted Finset.univ p (fun a ↦ F a / p a)
    (fun a _ ↦ hp a) hsum (fun a _ ↦ div_nonneg (hF a) (hp a))) ?_
  refine Finset.sum_le_sum fun a _ ↦ ?_
  rcases eq_or_lt_of_le (hp a) with h | h
  · simp [← h, hF a]
  · rw [mul_div_cancel₀ _ h.ne']

/-- **The reference-vector form of the entropy value bound.**  For *every* full-support
probability vector `r` on the alphabet,

```
∏ₐ (F a / p a)^{p a} ≤ ∏ₐ (F a / r a)^{p a}.
```

This is Gibbs' inequality `-KL(p ‖ r) ≤ 0` in multiplicative form.  Its point is that the
right-hand side is *log-linear* in `p`: a supremum of the left-hand side over a polytope of
probability vectors becomes a linear program, and a single well-chosen `r` certifies it at its
vertices.

Proof sketch: split `F a / p a = (F a / r a) · (r a / p a)` (legitimate also when `p a = 0`, where
both sides carry the exponent `0`), and apply `blockLegValue_le_sum` to the weights `r`, whose
total mass is `1`. -/
theorem blockLegValue_le_prod_rpow {F p r : α → ℝ} (hF : ∀ a, 0 ≤ F a) (hp : ∀ a, 0 ≤ p a)
    (hsum : ∑ a, p a = 1) (hr : ∀ a, 0 < r a) (hrsum : ∑ a, r a = 1) :
    blockLegValue F p ≤ ∏ a, (F a / r a) ^ (p a) := by
  have hsplit : blockLegValue F p =
      (∏ a, (F a / r a) ^ (p a)) * blockLegValue r p := by
    unfold blockLegValue
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun a _ ↦ ?_
    rw [← Real.mul_rpow (div_nonneg (hF a) (hr a).le) (div_nonneg (hr a).le (hp a))]
    rcases eq_or_lt_of_le (hp a) with h | h
    · rw [← h]
      simp
    · have hra : r a ≠ 0 := (hr a).ne'
      congr 1
      field_simp
  have hgibbs : blockLegValue r p ≤ 1 := by
    refine le_trans (blockLegValue_le_sum (fun a ↦ (hr a).le) hp hsum) ?_
    exact hrsum.le
  calc blockLegValue F p = (∏ a, (F a / r a) ^ (p a)) * blockLegValue r p := hsplit
    _ ≤ (∏ a, (F a / r a) ^ (p a)) * 1 :=
        mul_le_mul_of_nonneg_left hgibbs
          (Finset.prod_nonneg fun a _ ↦ Real.rpow_nonneg (div_nonneg (hF a) (hr a).le) _)
    _ = ∏ a, (F a / r a) ^ (p a) := mul_one _

end AlgebraicComplexity
