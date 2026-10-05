/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Analysis.MaximumEntropyProduct
import AlgebraicComplexity.MatrixMultiplication.RationalTypedLeaf

/-!
# Products and orientations of rational typed leaves

`RationalTypedLeaf` is the common data model for a finite typed extraction: an integral source
profile, one visible coordinate map on each leg, and one positive matrix dimension on each leg.
This file adds the two structural operations needed by value arguments:

* `PositiveIntegralProfile.product` and `RationalTypedLeaf.product` form an independent product of
  two leaves;
* `RationalTypedLeaf.permute` transports one leaf along a permutation of the three legs.

The operations are deliberately generic.  The cyclic construction used by Coppersmith--Winograd
is obtained by taking the product of a leaf with its two rotated copies; the named API in
`CyclicTypedLeaf.lean` is therefore a convenient specialization, not a separate notion of typed
leaf.  Entropy maximality and the exact dimension products are proved once here and inherited by
all iterated or oriented products.
-/

namespace AlgebraicComplexity

open Tensor
open scoped BigOperators

universe u v w x

namespace PositiveIntegralProfile

variable {I : Type u} {J : Type v}
variable [Fintype I] [Nonempty I] [Fintype J] [Nonempty J]

/-- Independent product of two positive integral profiles. -/
def product (left : PositiveIntegralProfile I) (right : PositiveIntegralProfile J) :
    PositiveIntegralProfile (I × J) where
  alphabet := Finset.univ
  complete := by simp
  count ij := left.count ij.1 * right.count ij.2
  count_pos ij := mul_pos (left.count_pos ij.1) (right.count_pos ij.2)

/-- The mass of an independent product profile is the product of the two masses. -/
@[simp] theorem mass_product
    (left : PositiveIntegralProfile I) (right : PositiveIntegralProfile J) :
    (left.product right).mass = left.mass * right.mass := by
  unfold product mass WordType.profileMass
  rw [Fintype.sum_prod_type]
  simp_rw [← Finset.mul_sum]
  exact (Finset.sum_mul (Finset.univ : Finset I) left.count
    (∑ j, right.count j)).symm

/-- Normalizing an independent product profile gives the product probability law. -/
theorem probability_product
    (left : PositiveIntegralProfile I) (right : PositiveIntegralProfile J) :
    (left.product right).probability = left.probability.product right.probability := by
  apply ProbabilityVector.ext
  funext ij
  rw [probability_weight, ProbabilityVector.product_weight, probability_weight,
    probability_weight, mass_product]
  have hleft : (left.mass : ℝ) ≠ 0 := by exact_mod_cast left.mass_pos.ne'
  have hright : (right.mass : ℝ) ≠ 0 := by exact_mod_cast right.mass_pos.ne'
  change ((left.count ij.1 * right.count ij.2 : ℕ) : ℝ) /
      ((left.mass * right.mass : ℕ) : ℝ) =
    ((left.count ij.1 : ℝ) / (left.mass : ℝ)) *
      ((right.count ij.2 : ℝ) / (right.mass : ℝ))
  push_cast
  field_simp [hleft, hright]

end PositiveIntegralProfile

namespace RationalTypedLeaf

variable {I : Type u} {J : Type v}
variable [Fintype I] [Nonempty I] [Fintype J] [Nonempty J]
variable {A : Leg → Type w} {B : Leg → Type x}
variable [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]
variable [∀ c, Fintype (B c)] [∀ c, DecidableEq (B c)]

/-- Transport a typed leaf by a permutation of its three visible legs.

The convention agrees with `Tensor.permute`: the new leg `c` reads the old leg `sigma.symm c`.
The source profile is unchanged, while coordinates and dimensions are reindexed. -/
def permute (leaf : RationalTypedLeaf I A) (sigma : Orientation) :
    RationalTypedLeaf I (fun c ↦ A (sigma.symm c)) where
  profile := leaf.profile
  coordinate c i := leaf.coordinate (sigma.symm c) i
  dimension i c := leaf.dimension i (sigma.symm c)
  dimension_pos i c := leaf.dimension_pos i (sigma.symm c)

@[simp] theorem permute_profile (leaf : RationalTypedLeaf I A) (sigma : Orientation) :
    (leaf.permute sigma).profile = leaf.profile := rfl

@[simp] theorem permute_coordinate (leaf : RationalTypedLeaf I A)
    (sigma : Orientation) (c : Leg) (i : I) :
    (leaf.permute sigma).coordinate c i = leaf.coordinate (sigma.symm c) i := rfl

@[simp] theorem permute_dimension (leaf : RationalTypedLeaf I A)
    (sigma : Orientation) (i : I) (c : Leg) :
    (leaf.permute sigma).dimension i c = leaf.dimension i (sigma.symm c) := rfl

/-- The profile-weighted dimension product is reindexed in the same way as the individual
dimensions.  This is the multiplicative coordinate law used by iterated orientation products. -/
@[simp] theorem permute_dimensionProduct (leaf : RationalTypedLeaf I A)
    (sigma : Orientation) (c : Leg) :
    (leaf.permute sigma).dimensionProduct c = leaf.dimensionProduct (sigma.symm c) := by
  rfl

@[simp] theorem permute_distribution (leaf : RationalTypedLeaf I A) (sigma : Orientation) :
    (leaf.permute sigma).distribution = leaf.distribution := rfl

@[simp] theorem permute_marginal (leaf : RationalTypedLeaf I A)
    (sigma : Orientation) (c : Leg) :
    (leaf.permute sigma).marginal c = leaf.marginal (sigma.symm c) := rfl

/-- Maximum entropy in a typed leaf's three-marginal fiber is invariant under reordering the legs.

The source law is unchanged.  To compare a competitor in the permuted fiber with the original
fiber, evaluate its constraint at the leg `sigma c`; the inverse permutation then recovers the
original constraint at `c`. -/
theorem IsMaximumEntropyBits.permute
    {leaf : RationalTypedLeaf I A} (sigma : Orientation)
    (h : leaf.IsMaximumEntropyBits leaf.distribution) :
    (leaf.permute sigma).IsMaximumEntropyBits (leaf.permute sigma).distribution := by
  intro competitor hcompetitor
  apply h
  intro c
  have hc := hcompetitor (sigma c)
  change leaf.distribution.pushforward (leaf.coordinate
      (sigma.symm (sigma c))) =
    competitor.pushforward (leaf.coordinate (sigma.symm (sigma c))) at hc
  rw [Equiv.symm_apply_apply] at hc
  exact hc

/-- Product of two typed leaves on a common three-leg interface.

The source alphabet is the Cartesian product, the visible coordinate is paired componentwise,
and each constituent dimension is multiplied.  This is the typed-leaf counterpart of
`Tensor.external`. -/
def product (left : RationalTypedLeaf I A) (right : RationalTypedLeaf J B) :
    RationalTypedLeaf (I × J) (fun c ↦ A c × B c) where
  profile := left.profile.product right.profile
  coordinate c ij := (left.coordinate c ij.1, right.coordinate c ij.2)
  dimension ij c := left.dimension ij.1 c * right.dimension ij.2 c
  dimension_pos ij c := mul_pos (left.dimension_pos ij.1 c) (right.dimension_pos ij.2 c)

@[simp] theorem product_profile (left : RationalTypedLeaf I A)
    (right : RationalTypedLeaf J B) :
    (left.product right).profile = left.profile.product right.profile := rfl

@[simp] theorem product_coordinate (left : RationalTypedLeaf I A)
    (right : RationalTypedLeaf J B) (c : Leg) (ij : I × J) :
    (left.product right).coordinate c ij =
      (left.coordinate c ij.1, right.coordinate c ij.2) := rfl

@[simp] theorem product_dimension (left : RationalTypedLeaf I A)
    (right : RationalTypedLeaf J B) (ij : I × J) (c : Leg) :
    (left.product right).dimension ij c =
      left.dimension ij.1 c * right.dimension ij.2 c := rfl

/-- The product leaf carries the independent product probability law. -/
theorem product_distribution (left : RationalTypedLeaf I A)
    (right : RationalTypedLeaf J B) :
    (left.product right).distribution = left.distribution.product right.distribution := by
  exact left.profile.probability_product right.profile

/-- The product coordinate is the generic paired coordinate from the probability layer. -/
theorem product_coordinate_eq_productCoordinate (left : RationalTypedLeaf I A)
    (right : RationalTypedLeaf J B) :
    (left.product right).coordinate =
      WordType.productCoordinate left.coordinate right.coordinate := by
  rfl

/-- Exact dimension product of an independent product leaf.

Each left dimension is repeated once for every unit of the right profile mass, and conversely. -/
theorem product_dimensionProduct (left : RationalTypedLeaf I A)
    (right : RationalTypedLeaf J B) (c : Leg) :
    (left.product right).dimensionProduct c =
      left.dimensionProduct c ^ right.profile.mass *
        right.dimensionProduct c ^ left.profile.mass := by
  classical
  change (∏ ij : I × J,
      (left.dimension ij.1 c * right.dimension ij.2 c) ^
        (left.profile.count ij.1 * right.profile.count ij.2)) = _
  rw [Fintype.prod_prod_type]
  calc
    (∏ i, ∏ j,
      (left.dimension i c * right.dimension j c) ^
        (left.profile.count i * right.profile.count j)) =
        (∏ i, ∏ j, left.dimension i c ^
          (left.profile.count i * right.profile.count j)) *
        (∏ i, ∏ j, right.dimension j c ^
          (left.profile.count i * right.profile.count j)) := by
      simp_rw [mul_pow, Finset.prod_mul_distrib]
    _ = (∏ i, left.dimension i c ^
          (left.profile.count i * right.profile.mass)) *
        (∏ j, right.dimension j c ^
          (right.profile.count j * left.profile.mass)) := by
      have hleft (i : I) :
          (∏ j, left.dimension i c ^
              (left.profile.count i * right.profile.count j)) =
            left.dimension i c ^ (left.profile.count i * right.profile.mass) := by
        rw [Finset.prod_pow_eq_pow_sum]
        congr 1
        simpa [PositiveIntegralProfile.mass, WordType.profileMass] using
          (Finset.mul_sum (Finset.univ : Finset J) right.profile.count
            (left.profile.count i)).symm
      have hright (j : J) :
          (∏ i, right.dimension j c ^
              (left.profile.count i * right.profile.count j)) =
            right.dimension j c ^ (right.profile.count j * left.profile.mass) := by
        rw [Finset.prod_pow_eq_pow_sum]
        congr 1
        simpa [PositiveIntegralProfile.mass, WordType.profileMass, mul_comm] using
          (Finset.sum_mul (Finset.univ : Finset I) left.profile.count
            (right.profile.count j)).symm
      congr 1
      · apply Finset.prod_congr rfl
        intro i hi
        exact hleft i
      · calc
          (∏ i, ∏ j, right.dimension j c ^
              (left.profile.count i * right.profile.count j)) =
              ∏ j, ∏ i, right.dimension j c ^
                (left.profile.count i * right.profile.count j) := by
            let f : I → J → ℕ := fun i j ↦
              right.dimension j c ^ (left.profile.count i * right.profile.count j)
            calc
              (∏ i, ∏ j, f i j) = ∏ ij : I × J, f ij.1 ij.2 := by
                symm
                exact Fintype.prod_prod_type' f
              _ = ∏ j, ∏ i, f i j := Fintype.prod_prod_type_right' f
          _ = ∏ j, right.dimension j c ^
                (right.profile.count j * left.profile.mass) := by
            apply Finset.prod_congr rfl
            intro j hj
            exact hright j
    _ = (∏ i, (left.dimension i c ^ left.profile.count i) ^
          right.profile.mass) *
        (∏ j, (right.dimension j c ^ right.profile.count j) ^
          left.profile.mass) := by
      simp_rw [← pow_mul]
    _ = left.dimensionProduct c ^ right.profile.mass *
        right.dimensionProduct c ^ left.profile.mass := by
      have hleftProd :
          (∏ i, left.dimension i c ^ left.profile.count i) =
            left.dimensionProduct c := by
        unfold dimensionProduct
        rw [left.profile.alphabet_eq_univ]
      have hrightProd :
          (∏ j, right.dimension j c ^ right.profile.count j) =
            right.dimensionProduct c := by
        unfold dimensionProduct
        rw [right.profile.alphabet_eq_univ]
      have hpowLeft :
          (∏ i, (left.dimension i c ^ left.profile.count i) ^ right.profile.mass) =
            (∏ i, left.dimension i c ^ left.profile.count i) ^ right.profile.mass := by
        simpa using (Finset.prod_pow (Finset.univ : Finset I)
          right.profile.mass (fun i ↦ left.dimension i c ^ left.profile.count i))
      have hpowRight :
          (∏ j, (right.dimension j c ^ right.profile.count j) ^ left.profile.mass) =
            (∏ j, right.dimension j c ^ right.profile.count j) ^ left.profile.mass := by
        simpa using (Finset.prod_pow (Finset.univ : Finset J)
          left.profile.mass (fun j ↦ right.dimension j c ^ right.profile.count j))
      calc
        (∏ i, (left.dimension i c ^ left.profile.count i) ^ right.profile.mass) *
            (∏ j, (right.dimension j c ^ right.profile.count j) ^ left.profile.mass) =
          (∏ i, left.dimension i c ^ left.profile.count i) ^ right.profile.mass *
            (∏ j, right.dimension j c ^ right.profile.count j) ^ left.profile.mass := by
              rw [hpowLeft, hpowRight]
        _ = left.dimensionProduct c ^ right.profile.mass *
            right.dimensionProduct c ^ left.profile.mass := by
              rw [hleftProd, hrightProd]

/-- Independent products preserve maximum entropy in the paired visible-coordinate fiber. -/
theorem IsMaximumEntropyBits.product
    {left : RationalTypedLeaf I A} {right : RationalTypedLeaf J B}
    (hleft : left.IsMaximumEntropyBits left.distribution)
    (hright : right.IsMaximumEntropyBits right.distribution) :
    (left.product right).IsMaximumEntropyBits (left.product right).distribution := by
  classical
  have hleft' := IsMaximumEntropyBits.isMaximumEntropyInMappedFiber hleft
  have hright' := IsMaximumEntropyBits.isMaximumEntropyInMappedFiber hright
  have hproduct := WordType.IsMaximumEntropyInMappedFiber.product
    left.coordinate right.coordinate left.distribution right.distribution hleft' hright'
  intro competitor hcompetitor
  have hdist := left.product_distribution right
  have hcoord := left.product_coordinate_eq_productCoordinate right
  have hnat : competitor.entropy ≤
      (left.distribution.product right.distribution).entropy := by
    apply hproduct competitor
    intro c
    rw [← hcoord, ← hdist]
    exact (hcompetitor c).symm
  unfold ProbabilityVector.entropyBits at hnat ⊢
  have hbits := (div_le_div_iff_of_pos_right
    (Real.log_pos (by norm_num : (1 : ℝ) < 2))).2 hnat
  simpa only [hdist] using hbits

end RationalTypedLeaf

end AlgebraicComplexity
