import AlgebraicComplexity.Analysis.Subexponential

/-!
# Finite products of exponential growth bounds

Recursive tensor certificates assemble a fixed finite collection of regional and constituent
families by Cartesian product.  Their exact counts, exponential bases, and subexponential losses
therefore multiply.  This file packages that elementary passage independently of any particular
tensor construction.
-/

open scoped BigOperators

namespace AlgebraicComplexity.Growth

universe u

variable {I : Type u}

/-- A finite product of pointwise positive loss sequences is pointwise positive. -/
theorem finset_prod_pos
    (s : Finset I) (loss : I → ℕ → ℝ)
    (hloss : ∀ i ∈ s, ∀ r, 0 < r → 0 < loss i r)
    (r : ℕ) (hr : 0 < r) :
    0 < ∏ i ∈ s, loss i r := by
  exact Finset.prod_pos fun i hi ↦ hloss i hi r hr

/-- A finite product of subexponential loss sequences remains subexponential. -/
theorem finset_prod_subexponential
    [DecidableEq I]
    (s : Finset I) (loss : I → ℕ → ℝ)
    (hloss : ∀ i ∈ s, Subexponential (loss i)) :
    Subexponential (fun r ↦ ∏ i ∈ s, loss i r) :=
  Subexponential.finset_prod s loss hloss

/-- Multiply a fixed finite family of one-sided exponential growth bounds.

This form keeps exact counts in `ℕ`, matching Cartesian-product cardinalities, while bases and
losses live in `ℝ`.  The empty family is handled by the empty-product convention. -/
theorem finset_prod_base_pow_le_prod_loss_mul_prod_count
    (s : Finset I) (base : I → ℝ)
    (loss : I → ℕ → ℝ) (count : I → ℕ → ℕ)
    (r : ℕ)
    (hbase : ∀ i ∈ s, 0 ≤ base i)
    (hgrowth : ∀ i ∈ s,
      base i ^ r ≤ loss i r * (count i r : ℝ)) :
    (∏ i ∈ s, base i) ^ r ≤
      (∏ i ∈ s, loss i r) * ((∏ i ∈ s, count i r : ℕ) : ℝ) := by
  rw [← Finset.prod_pow]
  calc
    ∏ i ∈ s, base i ^ r ≤
        ∏ i ∈ s, loss i r * (count i r : ℝ) := by
      apply Finset.prod_le_prod
      · intro i hi
        exact pow_nonneg (hbase i hi) r
      · intro i hi
        exact hgrowth i hi
    _ = (∏ i ∈ s, loss i r) * (∏ i ∈ s, (count i r : ℝ)) := by
      rw [Finset.prod_mul_distrib]
    _ = (∏ i ∈ s, loss i r) * ((∏ i ∈ s, count i r : ℕ) : ℝ) := by
      rw [Nat.cast_prod]

section Fintype

variable [Fintype I] [DecidableEq I]

omit [DecidableEq I] in
/-- Fixed-finite-type specialization of `finset_prod_pos`. -/
theorem fintype_prod_pos
    (loss : I → ℕ → ℝ)
    (hloss : ∀ i r, 0 < r → 0 < loss i r)
    (r : ℕ) (hr : 0 < r) :
    0 < ∏ i, loss i r := by
  exact finset_prod_pos Finset.univ loss (fun i _ ↦ hloss i) r hr

/-- Fixed-finite-type specialization of finite-product subexponential closure. -/
theorem fintype_prod_subexponential
    (loss : I → ℕ → ℝ)
    (hloss : ∀ i, Subexponential (loss i)) :
    Subexponential (fun r ↦ ∏ i, loss i r) :=
  Subexponential.fintype_prod loss hloss

omit [DecidableEq I] in
/-- Fixed-finite-type specialization of the product growth theorem. -/
theorem fintype_prod_base_pow_le_prod_loss_mul_prod_count
    (base : I → ℝ) (loss : I → ℕ → ℝ)
    (count : I → ℕ → ℕ) (r : ℕ)
    (hbase : ∀ i, 0 ≤ base i)
    (hgrowth : ∀ i, base i ^ r ≤ loss i r * (count i r : ℝ)) :
    (∏ i, base i) ^ r ≤
      (∏ i, loss i r) * ((∏ i, count i r : ℕ) : ℝ) := by
  exact finset_prod_base_pow_le_prod_loss_mul_prod_count
    Finset.univ base loss count r (fun i _ ↦ hbase i) (fun i _ ↦ hgrowth i)

end Fintype

end AlgebraicComplexity.Growth
