/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Analysis.ProportionalTypeClassGrowth
import AlgebraicComplexity.Examples.SchonhageSecondDesign
import AlgebraicComplexity.MatrixMultiplication.Transpose

/-!
# Coppersmith's 1982 rectangular certificates

This module builds the explicit family of rectangular matrix-multiplication algorithms of
D. Coppersmith, *Rapid multiplication of rectangular matrices*, SIAM Journal on Computing
**11**(3), 467–471 (1982).  The companion module
`AlgebraicComplexity/Examples/CoppersmithRectangular1982.lean` feeds the family to the
rectangular-exponent packager and derives the paper's headline `α > 0`.

## The area idea

The starting identity is Schönhage's second design at `k = q = 2`
(`AlgebraicComplexity/Examples/SchonhageSecondDesign.lean`), which Coppersmith displays on
p. 467: a partial `2 × 3` by `3 × 2` product whose left factor carries `k = (1, 2, 2)` variables
in its three columns and whose right factor carries `n = (2, 1, 1)` variables in its three rows,
with an approximate decomposition of length `5 = ∑_j k_j` and order `2`.

Schönhage's filling lemma turns the `s`-th Kronecker power of that pattern, for any multiplicity
type `a : Fin 3 → ℕ` of word length `s`, into a **total** rectangular product

`⟨K, |Y|, N⟩`,  `K = ∏_j k_j ^ a_j`,  `N = ∏_j n_j ^ a_j`,  `Y = ` the type class of `a`,

of border rank at most `5 ^ s` in degree `2 s`
(`borderRankLEAt_matrixMultiplication_of_type`).  Schönhage chooses `a` to maximize the
**volume** `K · |Y| · N`.  Coppersmith's one new step (p. 468) is to maximize the **area**
`K · |Y|` instead, deliberately unbalancing `K` against `N`:

`K · |Y| = |Y| · ∏_j k_j ^ a_j` is exactly the term of type `a` in the multinomial expansion of
`(∑_j k_j) ^ s = 5 ^ s`,

so the area is maximized at the type proportional to the column counts themselves,
`a = (t, 2t, 2t)` with `s = 5t`, and it is then within a subexponential factor of the whole sum
`5 ^ s`.  For this type the two dimensions are *exact* powers of two,

`K = 1 ^ t · 2 ^ {2t} · 2 ^ {2t} = 2 ^ {4t}`  and  `N = 2 ^ t · 1 ^ {2t} · 1 ^ {2t} = 2 ^ t`,

so no estimate is needed for them; the only asymptotics in the whole construction is the
method-of-types sandwich for `|Y|`.

`crAreaProfile` is therefore *defined* to be the column-count vector of the pattern, which is
what makes `crAreaProfile_mass` a restatement of Schönhage's count `∑_j k_j = k q + 1 = 5`.

## Principal results

* `crAreaProfile`, `crWords`, `crArea`: Coppersmith's area type, the size `|Y|` of its type
  class, and the area `A_t = K · |Y| = 2 ^ {4t} · |Y|`.
* `crArea_le` : `A_t ≤ 5 ^ {5t}`, the exact multinomial inequality above — a *single term* of
  the expansion of `(∑_j k_j) ^ {5t}` never exceeds the sum.
* `crArea_ge` : `5 ^ {5t} ≤ loss t · A_t` with `loss` the explicit subexponential
  method-of-types loss, from the entropy base `∏_j (1/p_j)^{p_j} = 5 / 2^{4/5}` of the
  proportions `(1/5, 2/5, 2/5)` (`crEntropyBase`: `proportionalEntropyBase = 5^5 / 2^4`).
* `cr_borderRankLEAt_rectangular` : `R̲(⟨2^{4t}, |Y|, 2^t⟩) ≤ 5^{5t}` in degree `10 t`.
* `cr_rankLE` : the squared certificate of p. 469, `R(⟨A_t, 2^{2t}, A_t⟩) ≤ 5^{10t} (20t+1)^3`.
  Coppersmith tensors the certificate with its first-two-legs-reversed copy — the transposition
  law `Tensor.BorderRankLEAt.matrixMultiplication_swapYZ` — so that both outer dimensions become
  the large area `A_t` while the middle dimension is the small `N² = 2^{2t}`, and then converts
  the border-rank certificate to an exact one by polynomial interpolation.

## References

* D. Coppersmith, *Rapid multiplication of rectangular matrices*, SIAM J. Comput. **11**(3),
  467–471 (1982).
* A. Schönhage, *Partial and total matrix multiplication*, SIAM J. Comput. **10**(3), 434–455
  (1981), §4–§5.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor WordType

universe u

/-! ## Coppersmith's area type -/

/-- **Coppersmith's area profile** (1982, p. 468): the multiplicity profile of the inner index of
Schönhage's second design at `k = q = 2` is the *column-count vector* `(1, 2, 2)` of its left
factor.  Repeating it `t` times gives the type `a = (t, 2t, 2t)` of word length `5t`.

Defining the profile as the column counts rather than as the literal vector `![1, 2, 2]` records
Coppersmith's reason for the choice: the area `∏_j k_j^{a_j} · |Y_a|` is the multinomial term of
type `a` in `(∑_j k_j)^s`, and a multinomial term is maximized at the proportional type. -/
def crAreaProfile : Fin 3 → ℕ := fun j ↦ (pmmColumn (sdLeftPositions 2 2) j).card

/-- The area profile is Schönhage's column-count vector `k = (1, 2, 2)`. -/
theorem crAreaProfile_apply (j : Fin 3) :
    crAreaProfile j = if (j : ℕ) = 0 then 1 else 2 :=
  card_pmmColumn_sdLeftPositions (by norm_num) j

@[simp] theorem crAreaProfile_zero : crAreaProfile 0 = 1 := by
  rw [crAreaProfile_apply]; decide

@[simp] theorem crAreaProfile_one : crAreaProfile 1 = 2 := by
  rw [crAreaProfile_apply]; decide

@[simp] theorem crAreaProfile_two : crAreaProfile 2 = 2 := by
  rw [crAreaProfile_apply]; decide

/-- The row-count vector `n = (2, 1, 1)` of the right factor of Schönhage's second design at
`k = q = 2`. -/
theorem crRowCount (j : Fin 3) :
    (pmmRow (sdRightPositions 2 2) j).card = if (j : ℕ) = 0 then 2 else 1 :=
  card_pmmRow_sdRightPositions (by norm_num) j

@[simp] theorem crRowCount_zero : (pmmRow (sdRightPositions 2 2) 0).card = 2 := by
  rw [crRowCount]; decide

@[simp] theorem crRowCount_one : (pmmRow (sdRightPositions 2 2) 1).card = 1 := by
  rw [crRowCount]; decide

@[simp] theorem crRowCount_two : (pmmRow (sdRightPositions 2 2) 2).card = 1 := by
  rw [crRowCount]; decide

/-- **Schönhage's length count is the total area mass**: `∑_j k_j = k q + 1 = 5`, which is both
the length of the approximate decomposition and the base of Coppersmith's multinomial
expansion. -/
theorem crAreaProfile_mass : profileMass crAreaProfile = 5 := by
  have h := sum_pmmColumn_card_sd (k := 2) (q := 2) (by norm_num)
  simpa [profileMass, crAreaProfile] using h

/-- The word length of the `t`-th member of Coppersmith's family is `s = 5 t`. -/
theorem crLength (t : ℕ) : profileMass crAreaProfile * t = 5 * t := by
  rw [crAreaProfile_mass]

/-! ## The two exact dimensions -/

/-- The left dimension of the filled product at Coppersmith's type is exactly `K = 2 ^ {4t}`:
`1 ^ t · 2 ^ {2t} · 2 ^ {2t}`. -/
theorem crProd_column (t : ℕ) :
    (∏ j, (pmmColumn (sdLeftPositions 2 2) j).card ^ proportionalCounts crAreaProfile t j) =
      2 ^ (4 * t) := by
  have hexpand :
      (∏ j, (pmmColumn (sdLeftPositions 2 2) j).card ^ proportionalCounts crAreaProfile t j) =
        crAreaProfile 0 ^ (crAreaProfile 0 * t) * crAreaProfile 1 ^ (crAreaProfile 1 * t) *
          crAreaProfile 2 ^ (crAreaProfile 2 * t) :=
    Fin.prod_univ_three _
  rw [hexpand, crAreaProfile_zero, crAreaProfile_one, crAreaProfile_two]
  ring

/-- The right dimension of the filled product at Coppersmith's type is exactly `N = 2 ^ t`:
`2 ^ t · 1 ^ {2t} · 1 ^ {2t}`. -/
theorem crProd_row (t : ℕ) :
    (∏ j, (pmmRow (sdRightPositions 2 2) j).card ^ proportionalCounts crAreaProfile t j) =
      2 ^ t := by
  have hexpand :
      (∏ j, (pmmRow (sdRightPositions 2 2) j).card ^ proportionalCounts crAreaProfile t j) =
        (pmmRow (sdRightPositions 2 2) 0).card ^ (crAreaProfile 0 * t) *
          (pmmRow (sdRightPositions 2 2) 1).card ^ (crAreaProfile 1 * t) *
            (pmmRow (sdRightPositions 2 2) 2).card ^ (crAreaProfile 2 * t) :=
    Fin.prod_univ_three _
  rw [hexpand, crRowCount_zero, crRowCount_one, crRowCount_two, crAreaProfile_zero,
    crAreaProfile_one, crAreaProfile_two]
  ring

/-! ## The area -/

/-- The number `|Y_t|` of inner multi-indices of Coppersmith's type: words of length `5 t` over
the three inner indices in which the first occurs `t` times and each of the others `2 t` times. -/
noncomputable def crWords (t : ℕ) : ℕ :=
  (typeClass (profileMass crAreaProfile * t) (proportionalCounts crAreaProfile t)).card

/-- Coppersmith's type is realizable, so its class is nonempty. -/
theorem crWords_pos (t : ℕ) : 0 < crWords t :=
  card_proportionalTypeClass_pos crAreaProfile t

/-- **Coppersmith's area** `A_t = K · |Y_t| = 2 ^ {4t} · |Y_t|`: the product of the two dimensions
of the filled rectangular product that his construction makes large. -/
noncomputable def crArea (t : ℕ) : ℕ := 2 ^ (4 * t) * crWords t

theorem crArea_pos (t : ℕ) : 0 < crArea t :=
  Nat.mul_pos (pow_pos (by norm_num : (0 : ℕ) < 2) (4 * t)) (crWords_pos t)

/-- Every scale is reached: `n ≤ A_n`, because `A_t ≥ 2 ^ {4t} ≥ 2 ^ t > t`. -/
theorem le_crArea (n : ℕ) : n ≤ crArea n := by
  have h1 : n < 2 ^ n := Nat.lt_two_pow_self
  have h2 : (2 : ℕ) ^ n ≤ 2 ^ (4 * n) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h3 : (2 : ℕ) ^ (4 * n) ≤ crArea n :=
    Nat.le_mul_of_pos_right _ (crWords_pos n)
  omega

/-- **The area never exceeds the whole multinomial sum**: `A_t ≤ 5 ^ {5t}`.

This is the exact inequality that makes Coppersmith's `κ` correct with no rounding: `A_t` is
literally the term of type `a = (t, 2t, 2t)` in the expansion of
`(∑_j k_j) ^ {5t} = 5 ^ {5t}`, and every term of a sum of naturals is at most the sum. -/
theorem crArea_le (t : ℕ) : crArea t ≤ 5 ^ (5 * t) := by
  classical
  have hexp := pow_sum_eq_sum_type_class (R := ℕ)
    (fun j : Fin 3 ↦ (pmmColumn (sdLeftPositions 2 2) j).card)
    (profileMass crAreaProfile * t)
  have hsum : (∑ j : Fin 3, (pmmColumn (sdLeftPositions 2 2) j).card) = 5 := crAreaProfile_mass
  have hterm := Finset.single_le_sum
    (f := fun a : Fin 3 → ℕ ↦
      (typeClass (profileMass crAreaProfile * t) a).card *
        ∏ j, (pmmColumn (sdLeftPositions 2 2) j).card ^ a j)
    (fun a _ ↦ Nat.zero_le _) (proportionalCounts_mem_types crAreaProfile t)
  rw [hsum] at hexp
  simp only [Nat.cast_id] at hexp
  rw [← hexp] at hterm
  rw [crProd_column] at hterm
  rw [crLength] at hterm
  calc crArea t = crWords t * 2 ^ (4 * t) := Nat.mul_comm _ _
    _ ≤ 5 ^ (5 * t) := hterm

/-! ## The method-of-types lower bound on the area -/

/-- The explicit subexponential method-of-types loss of Coppersmith's type. -/
noncomputable def crLoss : ℕ → ℝ := structuralZeroMultinomialLoss crAreaProfile

theorem crLoss_pos (t : ℕ) : 0 < crLoss t :=
  structuralZeroMultinomialLoss_pos crAreaProfile t

theorem crLoss_subexponential : Growth.Subexponential crLoss :=
  structuralZeroMultinomialLoss_subexponential crAreaProfile

/-- The loss is at least one, at every repetition count including `t = 0`. -/
theorem one_le_crLoss (t : ℕ) : 1 ≤ crLoss t := by
  have hexp : (1 : ℝ) ≤ Real.exp 1 := by
    have := Real.add_one_le_exp (1 : ℝ)
    linarith
  have h1 : (1 : ℝ) ≤ Real.exp 1 ^ Fintype.card (Fin 3) := one_le_pow₀ hexp
  have hp : ∀ i : Fin 3, (1 : ℝ) ≤ ((crAreaProfile i * t + 1 : ℕ) : ℝ) := by
    intro i
    have h : (1 : ℕ) ≤ crAreaProfile i * t + 1 := Nat.le_add_left 1 _
    exact_mod_cast h
  have h2 : (1 : ℝ) ≤ ∏ i : Fin 3, ((crAreaProfile i * t + 1 : ℕ) : ℝ) := by
    rw [Fin.prod_univ_three]
    have h01 : (1 : ℝ) ≤ ((crAreaProfile 0 * t + 1 : ℕ) : ℝ) *
        ((crAreaProfile 1 * t + 1 : ℕ) : ℝ) := by nlinarith [hp 0, hp 1]
    nlinarith [h01, hp 2]
  have : (1 : ℝ) * 1 ≤ Real.exp 1 ^ Fintype.card (Fin 3) *
      ∏ i : Fin 3, ((crAreaProfile i * t + 1 : ℕ) : ℝ) :=
    mul_le_mul h1 h2 zero_le_one (by positivity)
  simpa [crLoss, structuralZeroMultinomialLoss] using this

/-- **The entropy base of Coppersmith's proportions** `(1/5, 2/5, 2/5)` is
`∏_j (1/p_j)^{p_j·5} = 5 ^ 5 / 2 ^ 4 = 3125 / 16`.  Multiplying it by the left dimension
`K = 2 ^ {4t}` gives exactly `5 ^ {5t}`, which is why the area saturates the multinomial sum up
to a subexponential factor. -/
theorem crEntropyBase : proportionalEntropyBase crAreaProfile = 3125 / 16 := by
  have he : Real.exp 1 ≠ 0 := Real.exp_ne_zero 1
  unfold proportionalEntropyBase
  rw [crAreaProfile_mass]
  simp only [Fin.prod_univ_three, crAreaProfile_zero, crAreaProfile_one, crAreaProfile_two,
    factorialEntropyTerm]
  push_cast
  field_simp
  ring

/-- **Method-of-types lower bound on the area**: `5 ^ {5t} ≤ loss t · A_t`.

The `t`-fold proportional type class has at least `(5^5/2^4)^t` elements up to the explicit
polynomial loss, and multiplying that estimate by `K = 2 ^ {4t}` clears the denominator. -/
theorem crArea_ge (t : ℕ) : (5 : ℝ) ^ (5 * t) ≤ crLoss t * (crArea t : ℝ) := by
  have hbase :=
    proportionalEntropyBase_pow_le_structuralZeroLoss_mul_card_typeClass crAreaProfile t
  rw [crEntropyBase] at hbase
  have hbase' : (3125 / 16 : ℝ) ^ t ≤ crLoss t * (crWords t : ℝ) := hbase
  have h16 : (0 : ℝ) ≤ (16 : ℝ) ^ t := by positivity
  have hmul := mul_le_mul_of_nonneg_right hbase' h16
  have hleft : (3125 / 16 : ℝ) ^ t * (16 : ℝ) ^ t = (5 : ℝ) ^ (5 * t) := by
    rw [← mul_pow, pow_mul]
    norm_num
  have hright : crLoss t * (crWords t : ℝ) * (16 : ℝ) ^ t = crLoss t * (crArea t : ℝ) := by
    have h2 : (16 : ℝ) ^ t = (2 : ℝ) ^ (4 * t) := by
      rw [pow_mul]; norm_num
    rw [h2, crArea]
    push_cast
    ring
  rw [hleft, hright] at hmul
  exact hmul

/-! ## The certificates -/

section Certificate

variable (F : Type u) [Field F] [Infinite F]

/-- **Coppersmith's basic rectangular certificate** (1982, p. 468): the `5t`-th Kronecker power
of Schönhage's second design at `k = q = 2`, filled at the area type `(t, 2t, 2t)`, gives an
approximate algorithm of length `5 ^ {5t}` and order `10 t` for the very unbalanced product
`⟨2 ^ {4t}, |Y_t|, 2 ^ t⟩`. -/
theorem cr_borderRankLEAt_rectangular (t : ℕ) :
    BorderRankLEAt (5 ^ (5 * t)) (10 * t)
      (matrixMultiplication (K := F) (2 ^ (4 * t)) (crWords t) (2 ^ t)) := by
  have h := borderRankLEAt_matrixMultiplication_of_type F
    (sdLeftPositions 2 2) (sdRightPositions 2 2) (sd_borderRankLEAt F)
    (profileMass crAreaProfile * t) (proportionalCounts crAreaProfile t)
  rw [crProd_column, crProd_row] at h
  have hsize : (5 : ℕ) ^ (profileMass crAreaProfile * t) = 5 ^ (5 * t) := by
    rw [crLength]
  have hdeg : profileMass crAreaProfile * t * 2 = 10 * t := by
    rw [crAreaProfile_mass]; ring
  rw [hsize, hdeg] at h
  exact h

/-- **Coppersmith's squared certificate** (1982, p. 469).

Tensoring the basic certificate with its first-two-legs-reversed copy makes both outer dimensions
equal to the area `A_t = 2 ^ {4t} · |Y_t|` and the middle dimension equal to `N² = 2 ^ {2t}`;
polynomial interpolation then turns the order-`20t` approximate algorithm into an exact one at
the cost of the factor `(20t + 1)³`. -/
theorem cr_rankLE (t : ℕ) :
    RankLE (5 ^ (10 * t) * (20 * t + 1) ^ 3)
      (matrixMultiplication (K := F) (crArea t) (2 ^ (2 * t)) (crArea t)) := by
  have h := cr_borderRankLEAt_rectangular F t
  have hmul := h.matrixMultiplication_mul h.matrixMultiplication_swapYZ
  have e1 : 2 ^ (4 * t) * crWords t = crArea t := rfl
  have e2 : crWords t * 2 ^ (4 * t) = crArea t := Nat.mul_comm _ _
  have e3 : (2 : ℕ) ^ t * 2 ^ t = 2 ^ (2 * t) := by ring
  have e4 : (5 : ℕ) ^ (5 * t) * 5 ^ (5 * t) = 5 ^ (10 * t) := by ring
  have e5 : 10 * t + 10 * t = 20 * t := by ring
  rw [e1, e2, e3, e4, e5] at hmul
  exact hmul.matrixMultiplication_swapXZ.toRankLE

end Certificate

end AlgebraicComplexity.Examples
