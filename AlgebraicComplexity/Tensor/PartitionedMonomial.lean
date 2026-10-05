/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Tensor.Partitioned
import AlgebraicComplexity.Tensor.Degeneration

/-!
# Monomial degenerations by partition-block weights

Laser-method arguments often assign one natural-number weight to an entire variable block rather
than to each basis coordinate.  This module constructs the corresponding polynomial diagonal
maps directly on Mathlib direct sums.  It is therefore basis-free and works for arbitrary module
valued blocks.

The main theorem says that if every supported address has total weight at least `d`, applying the
block-weight families makes the degree-`d` leading tensor exactly the realization of those
addresses whose total weight equals `d`.  Unlike ordinary block zeroing, this can select an
induced antidiagonal even when every individual block label occurs in both selected and rejected
addresses.  That distinction is needed by Strassen's matrix-to-scalar and C-tensor constructions.
-/

namespace AlgebraicComplexity.Tensor

open scoped DirectSum

universe u v w

variable {K : Type u} [CommSemiring K]
variable {A : Leg → Type w} [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]
variable {V : ∀ c, A c → Type v}
variable [∀ c a, AddCommMonoid (V c a)] [∀ c a, Module K (V c a)]

/-- Keep only full addresses satisfying an arbitrary predicate.  This operation records a
subfamily of a partition certificate; by itself it does not assert that variable zeroing realizes
the subfamily. -/
def PartitionedTensor.selectAddresses
    (P : PartitionedTensor (K := K) (A := A) V)
    (keep : BlockAddress A → Prop) [DecidablePred keep] :
    PartitionedTensor (K := K) (A := A) V where
  support := P.support.filter keep
  constituent := P.constituent

/-- Membership in an address-selected partition is membership in the original support together
with the selection predicate. -/
@[simp] theorem PartitionedTensor.mem_selectAddresses_support
    (P : PartitionedTensor (K := K) (A := A) V)
    (keep : BlockAddress A → Prop) [DecidablePred keep]
    (s : BlockAddress A) :
    s ∈ (P.selectAddresses keep).support ↔ s ∈ P.support ∧ keep s := by
  exact Finset.mem_filter

/-- Degree-`d` coefficient of the diagonal family that assigns weight `weight a` to block `a`. -/
noncomputable def blockWeightCoefficient
    (weight : ∀ c, A c → ℕ) (c : Leg) (d : ℕ) :
    PartitionedSpace K V c →ₗ[K] PartitionedSpace K V c :=
  DirectSum.lmap fun a ↦
    if weight c a = d then LinearMap.id else 0

/-- The finitely supported polynomial diagonal map that sends block `a` to
`ε^(weight a) · block a`. -/
noncomputable def blockWeightFamily
    (weight : ∀ c, A c → ℕ) (c : Leg) :
    PolynomialLinearMap K (PartitionedSpace K V c) (PartitionedSpace K V c) := by
  classical
  refine Finsupp.onFinset (Finset.univ.image (weight c))
    (blockWeightCoefficient (K := K) (V := V) weight c) ?_
  intro d hd
  by_contra hmem
  apply hd
  ext a x
  have hweight : weight c a ≠ d := by
    intro h
    apply hmem
    rw [← h]
    exact Finset.mem_image_of_mem (weight c) (Finset.mem_univ a)
  simp [blockWeightCoefficient, hweight]

/-- Coefficient lookup in a partition-block weight family. -/
@[simp] theorem blockWeightFamily_coeff
    (weight : ∀ c, A c → ℕ) (c : Leg) (d : ℕ) :
    blockWeightFamily (K := K) (V := V) weight c d =
      blockWeightCoefficient (K := K) (V := V) weight c d := by
  classical
  simp [blockWeightFamily]

omit [∀ c, Fintype (A c)] in
/-- A coefficient map either preserves an included vector in a block of that degree or kills it. -/
theorem blockWeightCoefficient_comp_blockInclude
    (weight : ∀ c, A c → ℕ) (s : BlockAddress A) (c : Leg) (d : ℕ) :
    blockWeightCoefficient (K := K) (V := V) weight c d ∘ₗ
        blockInclude (K := K) (V := V) s c =
      if weight c (s c) = d then blockInclude (K := K) (V := V) s c else 0 := by
  classical
  ext x
  by_cases h : weight c (s c) = d
  · simp [blockWeightCoefficient, blockInclude, h]
  · simp [blockWeightCoefficient, blockInclude, h]

/-- Applying the polynomial block family to an included vector produces one vector-valued
monomial in the block's assigned degree. -/
theorem applyVector_blockWeightFamily_blockInclude
    (weight : ∀ c, A c → ℕ) (s : BlockAddress A) (c : Leg)
    (x : V c (s c)) :
    PolynomialLinearMap.applyVector
        (blockWeightFamily (K := K) (V := V) weight c)
        (blockInclude (K := K) (V := V) s c x) =
      PolynomialVector.monomial (weight c (s c))
        (blockInclude (K := K) (V := V) s c x) := by
  classical
  apply Finsupp.ext
  intro d
  rw [PolynomialLinearMap.applyVector_coeff, blockWeightFamily_coeff]
  have hcomp := LinearMap.congr_fun
    (blockWeightCoefficient_comp_blockInclude
      (K := K) (V := V) weight s c d) x
  simp only [LinearMap.comp_apply] at hcomp
  by_cases h : weight c (s c) = d
  · subst d
    simpa [PolynomialVector.monomial] using hcomp
  · simp [PolynomialVector.monomial, h, hcomp]

/-- Sum of the three block weights at one full address. -/
def blockAddressTotalWeight
    (weight : ∀ c, A c → ℕ) (s : BlockAddress A) : ℕ :=
  weight .X (s .X) + weight .Y (s .Y) + weight .Z (s .Z)

/-- One embedded constituent becomes a tensor-valued monomial whose degree is the total weight
of its three blocks.  Proof sketch: first prove the claim on pure tensors using the three
vector-valued monomials, then extend by linearity of `PiTensorProduct`. -/
theorem polynomialTransform_blockWeightFamily_block
    (weight : ∀ c, A c → ℕ) (s : BlockAddress A)
    (T : Tensor3 K (fun c ↦ V c (s c))) :
    polynomialTransform
        (blockWeightFamily (K := K) (V := V) weight)
        (map (blockInclude (K := K) (V := V) s) T) =
      PolynomialVector.monomial (blockAddressTotalWeight weight s)
        (map (blockInclude (K := K) (V := V) s) T) := by
  classical
  refine PiTensorProduct.induction_on T ?_ ?_
  · intro r x
    simp only [LinearMap.map_smul, polynomialTransform_smul,
      PolynomialVector.monomial_smul]
    congr 1
    rw [map_pure, polynomialTransform_pure]
    have hfamily :
        (fun c ↦ PolynomialLinearMap.applyVector
          (blockWeightFamily (K := K) (V := V) weight c)
          (blockInclude (K := K) (V := V) s c (x c))) =
        ofLegs
          (PolynomialVector.monomial (weight .X (s .X))
            (blockInclude (K := K) (V := V) s .X (x .X)))
          (PolynomialVector.monomial (weight .Y (s .Y))
            (blockInclude (K := K) (V := V) s .Y (x .Y)))
          (PolynomialVector.monomial (weight .Z (s .Z))
            (blockInclude (K := K) (V := V) s .Z (x .Z))) := by
      funext c
      cases c <;>
        simp [applyVector_blockWeightFamily_blockInclude]
    rw [hfamily, polynomialPure_monomial]
    unfold blockAddressTotalWeight
    congr 2
    funext c
    cases c <;> rfl
  · intro T S hT hS
    simp only [LinearMap.map_add, polynomialTransform_add,
      PolynomialVector.monomial_add, hT, hS]

/-- The block-weight transform of a whole partition is the sum of the monomially weighted
embedded constituents. -/
theorem polynomialTransform_blockWeightFamily_realize
    (weight : ∀ c, A c → ℕ)
    (P : PartitionedTensor (K := K) (A := A) V) :
    polynomialTransform (blockWeightFamily (K := K) (V := V) weight) P.realize =
      ∑ s ∈ P.support,
        PolynomialVector.monomial (blockAddressTotalWeight weight s)
          (map (blockInclude (K := K) (V := V) s) (P.constituent s)) := by
  classical
  unfold PartitionedTensor.realize realizePartition
  have hsum (support : Finset (BlockAddress A)) :
      polynomialTransform (blockWeightFamily (K := K) (V := V) weight)
          (∑ s ∈ support,
            map (blockInclude (K := K) (V := V) s) (P.constituent s)) =
        ∑ s ∈ support,
          PolynomialVector.monomial (blockAddressTotalWeight weight s)
            (map (blockInclude (K := K) (V := V) s) (P.constituent s)) := by
    induction support using Finset.induction_on with
    | empty => simp
    | @insert s support hnot ih =>
        rw [Finset.sum_insert hnot, polynomialTransform_add,
          Finset.sum_insert hnot,
          polynomialTransform_blockWeightFamily_block, ih]
  exact hsum P.support

/-- Minimum-weight selection theorem.  If all supported addresses have total weight at least
`d`, the degree-`d` leading coefficient is exactly the realization of the addresses of weight
`d`. -/
theorem blockWeightFamily_hasLeadingTerm
    (weight : ∀ c, A c → ℕ)
    (P : PartitionedTensor (K := K) (A := A) V) (d : ℕ)
    (hmin : ∀ s ∈ P.support, d ≤ blockAddressTotalWeight weight s) :
    HasLeadingTerm
      (polynomialTransform (blockWeightFamily (K := K) (V := V) weight) P.realize)
      d
      (P.selectAddresses (fun s ↦ blockAddressTotalWeight weight s = d)).realize := by
  classical
  rw [polynomialTransform_blockWeightFamily_realize]
  constructor
  · rw [Finsupp.finsetSum_apply]
    unfold PartitionedTensor.realize realizePartition PartitionedTensor.selectAddresses
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro s hs
    by_cases hweight : blockAddressTotalWeight weight s = d
    · subst d
      simp [PolynomialVector.monomial]
    · have hne : blockAddressTotalWeight weight s ≠ d := hweight
      simp [PolynomialVector.monomial, hne, Ne.symm hne]
  · intro e he
    rw [Finsupp.finsetSum_apply]
    apply Finset.sum_eq_zero
    intro s hs
    have hne : e ≠ blockAddressTotalWeight weight s :=
      Nat.ne_of_lt (he.trans_le (hmin s hs))
    exact PolynomialVector.monomial_coeff_of_ne hne _

/-- A minimum-weight address selection is a constructive polynomial degeneration at the stated
leading degree. -/
theorem PolynomialDegeneratesAt.partitionedSelectAddresses
    (weight : ∀ c, A c → ℕ)
    (P : PartitionedTensor (K := K) (A := A) V) (d : ℕ)
    (hmin : ∀ s ∈ P.support, d ≤ blockAddressTotalWeight weight s) :
    PolynomialDegeneratesAt d P.realize
      (P.selectAddresses (fun s ↦ blockAddressTotalWeight weight s = d)).realize :=
  ⟨blockWeightFamily (K := K) (V := V) weight,
    blockWeightFamily_hasLeadingTerm weight P d hmin⟩

/-- Degree-forgetting form of the partition-block monomial selection theorem. -/
theorem PolynomialDegenerates.partitionedSelectAddresses
    (weight : ∀ c, A c → ℕ)
    (P : PartitionedTensor (K := K) (A := A) V) (d : ℕ)
    (hmin : ∀ s ∈ P.support, d ≤ blockAddressTotalWeight weight s) :
    PolynomialDegenerates P.realize
      (P.selectAddresses (fun s ↦ blockAddressTotalWeight weight s = d)).realize :=
  (PolynomialDegeneratesAt.partitionedSelectAddresses weight P d hmin).toPolynomialDegenerates

end AlgebraicComplexity.Tensor
