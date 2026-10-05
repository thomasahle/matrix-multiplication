/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.CTensor
import Mathlib.Algebra.Order.Chebyshev

/-!
# Cardinality bounds for C-tensor antidiagonals

This leaf module contains the quantitative combinatorics of the C-tensor antidiagonal.  The
structural restriction and degeneration API remains in `CTensor.lean`; separating the two keeps
counting changes from invalidating downstream finite tensor-extraction clients.

The main bounds are division-free:

* `half_sq_le_card_antidiagonal`: the elementary floor-based estimate
  `⌊h/2⌋² ≤ |A_h|`;
* `sq_le_two_mul_card_antidiagonal`: `h² ≤ 2 |A_h|` for one C-tensor;
* `sq_sum_le_two_mul_card_mul_sum_card_antidiagonal`: the corresponding finite-family estimate
  obtained by Cauchy--Schwarz.
-/

namespace AlgebraicComplexity.CTensor

open Tensor

universe u v

/-- Include the first half of the indices into the full C-tensor index set. -/
def halfIndexEmbedding (h : ℕ) : Fin (h / 2) ↪ Fin h where
  toFun i := ⟨i.val, i.isLt.trans_le (Nat.div_le_self h 2)⟩
  inj' := by
    intro i j hij
    apply Fin.ext
    exact congrArg (fun x : Fin h ↦ x.val) hij

/-- The sum of two first-half indices is still a valid full index. -/
def halfIndexSum {h : ℕ} (i j : Fin (h / 2)) : Fin h :=
  ⟨i.val + j.val, by
    have hi := i.isLt
    have hj := j.isLt
    have hhalf : 2 * (h / 2) ≤ h := Nat.mul_div_le h 2
    omega⟩

/-- The sum index has the expected natural value. -/
@[simp] theorem halfIndexSum_val {h : ℕ} (i j : Fin (h / 2)) :
    (halfIndexSum i j).val = i.val + j.val := rfl

/-- Pairs from the first half inject into the minimum-weight antidiagonal.  This explicit
quadratic subfamily is sufficient for the asymptotic C-tensor value; the omitted triangular half
would change only a constant factor. -/
noncomputable def antidiagonalPairEmbedding
    {K : Type u} [CommSemiring K]
    {X Y Z : Type v} [AddCommMonoid X] [Module K X]
    [AddCommMonoid Y] [Module K Y] [AddCommMonoid Z] [Module K Z]
    {h : ℕ} (T : Fin h → Tensor3 K (ConstituentSpace X Y Z)) :
    Fin (h / 2) × Fin (h / 2) ↪ (antidiagonal T).support where
  toFun ij := by
    let i := halfIndexEmbedding h ij.1
    let j := halfIndexEmbedding h ij.2
    let k := halfIndexSum ij.1 ij.2
    refine ⟨tripleAddress i j k, ?_⟩
    change tripleAddress i j k ∈
      ((cyclicTriple T).selectAddresses
        (fun s ↦ blockAddressTotalWeight (antidiagonalWeight h) s =
          antidiagonalDegree h)).support
    rw [PartitionedTensor.mem_selectAddresses_support]
    constructor
    · exact (mem_cyclicTriple_support_iff T _).2 ⟨i, j, k, rfl⟩
    · apply (totalWeight_eq_antidiagonalDegree_iff i j k).2
      rfl
  inj' := by
    intro a b hab
    have haddress := congrArg Subtype.val hab
    have hx := congrFun haddress .X
    have hy := congrFun haddress .Y
    have hiFull : halfIndexEmbedding h a.1 = halfIndexEmbedding h b.1 :=
      congrArg (fun q ↦ q.1.1) hx
    have hjFull : halfIndexEmbedding h a.2 = halfIndexEmbedding h b.2 :=
      congrArg (fun q ↦ q.1.2) hy
    apply Prod.ext
    · exact (halfIndexEmbedding h).injective hiFull
    · exact (halfIndexEmbedding h).injective hjFull

/-- The selected antidiagonal contains quadratically many addresses: at least
`⌊h/2⌋ * ⌊h/2⌋`.

Proof sketch: embed a pair of first-half indices as the antidiagonal address `(i,j,i+j)` and
compare finite cardinalities. -/
theorem half_sq_le_card_antidiagonal
    {K : Type u} [CommSemiring K]
    {X Y Z : Type v} [AddCommMonoid X] [Module K X]
    [AddCommMonoid Y] [Module K Y] [AddCommMonoid Z] [Module K Z]
    {h : ℕ} (T : Fin h → Tensor3 K (ConstituentSpace X Y Z)) :
    (h / 2) ^ 2 ≤ (antidiagonal T).support.card := by
  simpa [pow_two] using
    (Fintype.card_le_of_injective (antidiagonalPairEmbedding T)
      (antidiagonalPairEmbedding T).injective)

/-- Sum two indices when their sum is known to remain below the common bound. -/
def boundedIndexSum {h : ℕ} (i j : Fin h) (hij : i.val + j.val < h) : Fin h :=
  ⟨i.val + j.val, hij⟩

/-- The bounded index sum has the expected value. -/
@[simp] theorem boundedIndexSum_val {h : ℕ} (i j : Fin h) (hij : i.val + j.val < h) :
    (boundedIndexSum i j hij).val = i.val + j.val := rfl

/-- Reverse a finite index across the interval `0, ..., h-1`. -/
def reverseIndex {h : ℕ} (i : Fin h) : Fin h :=
  ⟨h - 1 - i.val, by omega⟩

/-- Reversal has the expected natural value. -/
@[simp] theorem reverseIndex_val {h : ℕ} (i : Fin h) :
    (reverseIndex i).val = h - 1 - i.val := rfl

/-- Reversal of finite indices is injective. -/
theorem reverseIndex_injective {h : ℕ} : Function.Injective (@reverseIndex h) := by
  intro i j hij
  apply Fin.ext
  have := congrArg Fin.val hij
  simp only [reverseIndex_val] at this
  omega

/-- A pair whose index sum is below `h` determines a minimum-weight antidiagonal address. -/
noncomputable def antidiagonalPairElement
    {K : Type u} [CommSemiring K]
    {X Y Z : Type v} [AddCommMonoid X] [Module K X]
    [AddCommMonoid Y] [Module K Y] [AddCommMonoid Z] [Module K Z]
    {h : ℕ} (T : Fin h → Tensor3 K (ConstituentSpace X Y Z))
    (i j : Fin h) (hij : i.val + j.val < h) : (antidiagonal T).support := by
  let k := boundedIndexSum i j hij
  refine ⟨tripleAddress i j k, ?_⟩
  change tripleAddress i j k ∈
    ((cyclicTriple T).selectAddresses
      (fun s ↦ blockAddressTotalWeight (antidiagonalWeight h) s =
        antidiagonalDegree h)).support
  rw [PartitionedTensor.mem_selectAddresses_support]
  constructor
  · exact (mem_cyclicTriple_support_iff T _).2 ⟨i, j, k, rfl⟩
  · apply (totalWeight_eq_antidiagonalDegree_iff i j k).2
    rfl

/-- The address underlying `antidiagonalPairElement` is the expected cyclic triple. -/
@[simp] theorem antidiagonalPairElement_val
    {K : Type u} [CommSemiring K]
    {X Y Z : Type v} [AddCommMonoid X] [Module K X]
    [AddCommMonoid Y] [Module K Y] [AddCommMonoid Z] [Module K Z]
    {h : ℕ} (T : Fin h → Tensor3 K (ConstituentSpace X Y Z))
    (i j : Fin h) (hij : i.val + j.val < h) :
    (antidiagonalPairElement T i j hij).1 =
      tripleAddress i j (boundedIndexSum i j hij) := by
  unfold antidiagonalPairElement
  rfl

/-- Every pair of indices embeds into one of two copies of the antidiagonal support.

Pairs below the antidiagonal are sent directly to the `false` copy.  A pair on or above the
antidiagonal is reflected through `(h-1-i,h-1-j)` and sent to the `true` copy; the reflected sum
is below `h`.  The tag separates the two cases, and reflection is injective within the second.
-/
noncomputable def squareToTwoAntidiagonalsEmbedding
    {K : Type u} [CommSemiring K]
    {X Y Z : Type v} [AddCommMonoid X] [Module K X]
    [AddCommMonoid Y] [Module K Y] [AddCommMonoid Z] [Module K Z]
    {h : ℕ} (T : Fin h → Tensor3 K (ConstituentSpace X Y Z)) :
    Fin h × Fin h ↪ Bool × (antidiagonal T).support where
  toFun ij := if hij : ij.1.val + ij.2.val < h then
      (false, antidiagonalPairElement T ij.1 ij.2 hij)
    else
      let i := reverseIndex ij.1
      let j := reverseIndex ij.2
      have hreflected : i.val + j.val < h := by
        dsimp [i, j]
        omega
      (true, antidiagonalPairElement T i j hreflected)
  inj' := by
    intro a b hab
    by_cases ha : a.1.val + a.2.val < h
    · by_cases hb : b.1.val + b.2.val < h
      · apply Prod.ext
        · have hx := congrArg (fun q ↦ (q.2.1 .X).1.1) hab
          simpa [ha, hb, tripleAddress_X] using hx
        · have hy := congrArg (fun q ↦ (q.2.1 .Y).1.2) hab
          simp only [dif_pos ha, dif_pos hb, antidiagonalPairElement_val,
            tripleAddress_Y] at hy
          change a.2 = b.2 at hy
          exact hy
      · have htag := congrArg Prod.fst hab
        simp [ha, hb] at htag
    · by_cases hb : b.1.val + b.2.val < h
      · have htag := congrArg Prod.fst hab
        simp [ha, hb] at htag
      · apply Prod.ext
        · apply reverseIndex_injective
          have hx := congrArg (fun q ↦ (q.2.1 .X).1.1) hab
          simpa [ha, hb, tripleAddress_X] using hx
        · apply reverseIndex_injective
          have hy := congrArg (fun q ↦ (q.2.1 .Y).1.2) hab
          simp only [dif_neg ha, dif_neg hb, antidiagonalPairElement_val,
            tripleAddress_Y] at hy
          change reverseIndex a.2 = reverseIndex b.2 at hy
          exact hy

/-- The antidiagonal has at least half the square of the original C-tensor size:
`h^2 ≤ 2 * |antidiagonal|`.

Proof sketch: take cardinalities in `squareToTwoAntidiagonalsEmbedding`. -/
theorem sq_le_two_mul_card_antidiagonal
    {K : Type u} [CommSemiring K]
    {X Y Z : Type v} [AddCommMonoid X] [Module K X]
    [AddCommMonoid Y] [Module K Y] [AddCommMonoid Z] [Module K Z]
    {h : ℕ} (T : Fin h → Tensor3 K (ConstituentSpace X Y Z)) :
    h ^ 2 ≤ 2 * (antidiagonal T).support.card := by
  simpa [Fintype.card_prod, pow_two] using
    (Fintype.card_le_of_injective (squareToTwoAntidiagonalsEmbedding T)
      (squareToTwoAntidiagonalsEmbedding T).injective)

/-- Aggregate C-tensor antidiagonal bound for a finite family with varying constituent counts:
the square of the total number of constituents is at most twice the number of groups times the
total number of selected antidiagonal addresses.

Proof sketch: Cauchy--Schwarz bounds the square of `∑ hᵢ` by the number of indices times
`∑ hᵢ²`.  Apply `sq_le_two_mul_card_antidiagonal` in every component and sum. -/
theorem sq_sum_le_two_mul_card_mul_sum_card_antidiagonal
    {K : Type u} [CommSemiring K]
    {I : Type*} [Fintype I]
    {X Y Z : I → Type v}
    [∀ i, AddCommMonoid (X i)] [∀ i, Module K (X i)]
    [∀ i, AddCommMonoid (Y i)] [∀ i, Module K (Y i)]
    [∀ i, AddCommMonoid (Z i)] [∀ i, Module K (Z i)]
    (h : I → ℕ)
    (T : ∀ i, Fin (h i) → Tensor3 K (ConstituentSpace (X i) (Y i) (Z i))) :
    (∑ i, h i) ^ 2 ≤
      2 * Fintype.card I * ∑ i, (antidiagonal (T i)).support.card := by
  classical
  have hcauchy : (∑ i, h i) ^ 2 ≤
      Fintype.card I * ∑ i, (h i) ^ 2 := by
    simpa using
      (sq_sum_le_card_mul_sum_sq
        (s := (Finset.univ : Finset I)) (f := h))
  have hpoint : (∑ i, (h i) ^ 2) ≤
      2 * ∑ i, (antidiagonal (T i)).support.card := by
    calc
      (∑ i, (h i) ^ 2) ≤
          ∑ i, 2 * (antidiagonal (T i)).support.card :=
        Finset.sum_le_sum fun i _hi ↦ sq_le_two_mul_card_antidiagonal (T i)
      _ = 2 * ∑ i, (antidiagonal (T i)).support.card := by
        rw [Finset.mul_sum]
  calc
    (∑ i, h i) ^ 2 ≤ Fintype.card I * ∑ i, (h i) ^ 2 := hcauchy
    _ ≤ Fintype.card I * (2 * ∑ i, (antidiagonal (T i)).support.card) :=
      Nat.mul_le_mul_left (Fintype.card I) hpoint
    _ = 2 * Fintype.card I * ∑ i, (antidiagonal (T i)).support.card := by
      ac_rfl

end AlgebraicComplexity.CTensor
