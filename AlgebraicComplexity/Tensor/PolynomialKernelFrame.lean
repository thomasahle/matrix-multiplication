/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import Mathlib.Algebra.Polynomial.Degree.TrailingDegree
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Localization.Integer

/-!
# Kernel frames of polynomial matrices

Let `P` be an `n × N` matrix over the polynomial ring `K[X]` of a field.  Over the fraction field
its kernel has dimension at least `N − n`, so it contains `m ≤ N − n` linearly independent
vectors, and those have a left inverse.  Clearing denominators turns this into a statement about
polynomials only:

```text
P · δ = 0,        αᵀ · δ = q · 1_m,        q ≠ 0,
```

for polynomial matrices `δ, α` of shape `N × m` and a single nonzero polynomial `q`.  Multiplying
`α` by a unit times a power of `X` then normalizes `q` to `X^D + O(X^(D+1))` for any prescribed
`D` at least the trailing degree of the original `q`.

This is the whole of the "linear algebra over the function field `F(λ)`" that the border-rank
form of the one-slice speedup ([AlmanLi2026, Theorem 6.1, p. 19]) needs.  No base change of the
tensor layer to `RatFunc K` is involved: the fraction field appears only inside the proof of
`exists_polynomial_kernel_frame`, and its conclusion is stated over `K[X]`.

## Main results

* `exists_mul_coeff_eq_one_of_ne_zero`: a nonzero polynomial has a multiple of the form
  `X^D + O(X^(D+1))` for every `D` at least its trailing degree;
* `exists_polynomial_kernel_frame`: the kernel frame `(δ, α, q)` over a finite index type;
* `exists_polynomial_kernel_frame_finset`: the same over a finite subset of an index type, with
  `q` normalized to any sufficiently large trailing degree.  This is the form consumed by
  `Tensor/OneSliceBorderSpeedup.lean`, once per group of certificate terms.

## References

* J. Alman and B. Li, *Asymptotic rank speedup theorems, revisited*, arXiv:2605.21738
  ([AlmanLi2026]), Section 6.
-/

namespace AlgebraicComplexity.Tensor

open scoped Polynomial

open Module

universe u

variable {K : Type u} [Field K]

/-- A nonzero polynomial over a field has a multiple whose lowest term is exactly `X^D`, for
every `D` at least its trailing degree. -/
theorem exists_mul_coeff_eq_one_of_ne_zero {q : K[X]} (hq : q ≠ 0) {D : ℕ}
    (hD : q.natTrailingDegree ≤ D) :
    ∃ c : K[X], (c * q).coeff D = 1 ∧ ∀ e < D, (c * q).coeff e = 0 := by
  refine ⟨Polynomial.C (q.trailingCoeff)⁻¹ * Polynomial.X ^ (D - q.natTrailingDegree), ?_,
    fun e he ↦ ?_⟩
  · rw [mul_assoc, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow_mul',
      if_pos (Nat.sub_le _ _), Nat.sub_sub_self hD]
    exact inv_mul_cancel₀ (Polynomial.trailingCoeff_nonzero_iff_nonzero.mpr hq)
  · rw [mul_assoc, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow_mul']
    split_ifs with h
    · rw [Polynomial.coeff_eq_zero_of_lt_natTrailingDegree (by omega), mul_zero]
    · rw [mul_zero]

/-- **Kernel frame of a polynomial matrix.**  For an `n × ι` matrix `P` over `K[X]` and
`m ≤ |ι| − n`, there are polynomial matrices `δ, α : ι × m` and a nonzero polynomial `q` with
`P · δ = 0` and `αᵀ · δ = q · 1`.

Proof sketch: over the fraction field the kernel of `P` has dimension at least `|ι| − n` by
rank–nullity, so it contains `m` linearly independent vectors `w_k`.  The map
`e_k ↦ w_k` is injective, hence has a left inverse `g`.  Take `δ` to be the matrix of the `w_k`
and `α` the matrix of `g`, and clear the two sets of denominators. -/
theorem exists_polynomial_kernel_frame {ι : Type*} [Fintype ι] [DecidableEq ι] (n m : ℕ)
    (P : Fin n → ι → K[X]) (hm : m ≤ Fintype.card ι - n) :
    ∃ (δ α : ι → Fin m → K[X]) (q : K[X]), q ≠ 0 ∧
      (∀ j k, ∑ i, P j i * δ i k = 0) ∧
      ∀ l k, ∑ i, α i l * δ i k = if l = k then q else 0 := by
  classical
  let F := FractionRing K[X]
  let φ : (ι → F) →ₗ[F] (Fin n → F) :=
    LinearMap.pi fun j ↦ ∑ i, algebraMap K[X] F (P j i) • LinearMap.proj i
  have hφ : ∀ v j, φ v j = ∑ i, algebraMap K[X] F (P j i) * v i := by
    intro v j
    simp [φ, LinearMap.sum_apply, Algebra.smul_def]
  have hker : m ≤ finrank F (LinearMap.ker φ) := by
    have h1 := LinearMap.finrank_range_add_finrank_ker φ
    have h2 : finrank F (LinearMap.range φ) ≤ n := by
      calc finrank F (LinearMap.range φ) ≤ finrank F (Fin n → F) := Submodule.finrank_le _
        _ = n := by simp
    have h3 : finrank F (ι → F) = Fintype.card ι := Module.finrank_fintype_fun_eq_card F
    omega
  obtain ⟨w, hw⟩ := exists_linearIndependent_of_le_finrank hker
  let w' : Fin m → ι → F := fun k ↦ (w k : ι → F)
  have hw' : LinearIndependent F w' :=
    hw.map' (LinearMap.ker φ).subtype (Submodule.ker_subtype _)
  have hinj : LinearMap.ker (Fintype.linearCombination F w') = ⊥ :=
    LinearMap.ker_eq_bot.mpr (linearIndependent_iff_injective_fintypeLinearCombination.mp hw')
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective _ hinj
  -- The frame over the fraction field.
  have hPδ : ∀ j k, ∑ i, algebraMap K[X] F (P j i) * w' k i = 0 := by
    intro j k
    rw [← hφ]
    have hk : φ (w' k) = 0 := LinearMap.mem_ker.mp (w k).2
    rw [hk]
    rfl
  have hαδ : ∀ l k,
      ∑ i, g (fun j ↦ if i = j then 1 else 0) l * w' k i = if l = k then 1 else 0 := by
    intro l k
    have h1 : g (w' k) = Pi.single k 1 := by
      have h := LinearMap.congr_fun hg (Pi.single k 1)
      rw [LinearMap.comp_apply, Fintype.linearCombination_apply_single, one_smul,
        LinearMap.id_apply] at h
      exact h
    have h2 := LinearMap.pi_apply_eq_sum_univ g (w' k)
    rw [h1] at h2
    have h3 := congrFun h2 l
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply] at h3
    rw [h3]
    exact Finset.sum_congr rfl fun i _ ↦ mul_comm _ _
  -- Clear denominators.
  obtain ⟨b₁, hb₁⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors K[X])
    (fun p : ι × Fin m ↦ w' p.2 p.1)
  obtain ⟨b₂, hb₂⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors K[X])
    (fun p : ι × Fin m ↦ g (fun j ↦ if p.1 = j then 1 else 0) p.2)
  have hδex : ∀ i k, ∃ y : K[X],
      algebraMap K[X] F y = algebraMap K[X] F (b₁ : K[X]) * w' k i := fun i k ↦ by
    obtain ⟨y, hy⟩ := hb₁ (i, k)
    exact ⟨y, by rw [hy, Algebra.smul_def]⟩
  have hαex : ∀ i l, ∃ y : K[X],
      algebraMap K[X] F y =
        algebraMap K[X] F (b₂ : K[X]) * g (fun j ↦ if i = j then 1 else 0) l := fun i l ↦ by
    obtain ⟨y, hy⟩ := hb₂ (i, l)
    exact ⟨y, by rw [hy, Algebra.smul_def]⟩
  choose δ hδ using hδex
  choose α hα using hαex
  have hinjF : Function.Injective (algebraMap K[X] F) := IsFractionRing.injective K[X] F
  refine ⟨δ, α, (b₂ : K[X]) * (b₁ : K[X]), ?_, ?_, ?_⟩
  · exact mul_ne_zero (nonZeroDivisors.ne_zero b₂.2) (nonZeroDivisors.ne_zero b₁.2)
  · intro j k
    apply hinjF
    rw [map_sum, map_zero]
    calc ∑ i, algebraMap K[X] F (P j i * δ i k)
        = algebraMap K[X] F (b₁ : K[X]) * ∑ i, algebraMap K[X] F (P j i) * w' k i := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ ↦ ?_
          rw [map_mul, hδ]
          ring
      _ = 0 := by rw [hPδ, mul_zero]
  · intro l k
    apply hinjF
    rw [map_sum]
    calc ∑ i, algebraMap K[X] F (α i l * δ i k)
        = algebraMap K[X] F (b₂ : K[X]) * algebraMap K[X] F (b₁ : K[X]) *
            ∑ i, g (fun j ↦ if i = j then 1 else 0) l * w' k i := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ ↦ ?_
          rw [map_mul, hδ, hα]
          ring
      _ = algebraMap K[X] F (if l = k then (b₂ : K[X]) * (b₁ : K[X]) else 0) := by
          rw [hαδ]
          split_ifs
          · rw [mul_one, map_mul]
          · rw [mul_zero, map_zero]

/-- **Kernel frame over a finite subset, with normalized pivot.**  For a matrix `P : n × ι` over
`K[X]`, a finite set `s` of columns and `m ≤ |s| − n`, there is a polynomial matrix `δ` with
`∑_{i ∈ s} P j i · δ i k = 0`, and — for every `D` beyond a threshold — a polynomial matrix `α`
and a polynomial `q = X^D + O(X^(D+1))` with `∑_{i ∈ s} α i l · δ i k = q · [l = k]`.

The threshold is what lets several independent frames (one per group of a grouped certificate)
be brought to a common leading degree. -/
theorem exists_polynomial_kernel_frame_finset {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (n m : ℕ) (P : Fin n → ι → K[X]) (hm : m ≤ s.card - n) :
    ∃ δ : ι → Fin m → K[X], (∀ j k, ∑ i ∈ s, P j i * δ i k = 0) ∧
      ∃ d₀ : ℕ, ∀ D, d₀ ≤ D → ∃ (α : ι → Fin m → K[X]) (q : K[X]),
        (∀ l k, ∑ i ∈ s, α i l * δ i k = if l = k then q else 0) ∧
          q.coeff D = 1 ∧ ∀ e < D, q.coeff e = 0 := by
  classical
  have hcard : m ≤ Fintype.card s - n := by rwa [Fintype.card_coe]
  obtain ⟨δ', α', q₀, hq₀, hPδ, hαδ⟩ :=
    exists_polynomial_kernel_frame n m (fun j (i : s) ↦ P j i) hcard
  -- Extend the two frames by zero outside `s`.
  let ext : (s → Fin m → K[X]) → ι → Fin m → K[X] :=
    fun f i ↦ if h : i ∈ s then f ⟨i, h⟩ else 0
  have hext : ∀ (f : s → Fin m → K[X]) (i : s), ext f i = f i := by
    intro f i
    simp [ext]
  refine ⟨ext δ', fun j k ↦ ?_, q₀.natTrailingDegree, fun D hD ↦ ?_⟩
  · rw [← Finset.sum_coe_sort s (fun i ↦ P j i * ext δ' i k)]
    simp only [hext]
    exact hPδ j k
  · obtain ⟨c, hc1, hclow⟩ := exists_mul_coeff_eq_one_of_ne_zero hq₀ hD
    refine ⟨fun i l ↦ c * ext α' i l, c * q₀, fun l k ↦ ?_, hc1, hclow⟩
    rw [← Finset.sum_coe_sort s (fun i ↦ c * ext α' i l * ext δ' i k)]
    simp only [hext, mul_assoc]
    rw [← Finset.mul_sum, hαδ l k]
    split_ifs <;> simp

end AlgebraicComplexity.Tensor
