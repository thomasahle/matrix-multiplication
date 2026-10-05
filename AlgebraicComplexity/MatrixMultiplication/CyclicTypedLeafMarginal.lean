/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.CyclicTypedLeaf
import AlgebraicComplexity.MatrixMultiplication.RationalTypedLeafGrowth

set_option autoImplicit false

/-!
# The three marginals of a cyclic product leaf

Layer 3 (`AlgebraicComplexity/MatrixMultiplication/`).  `RationalTypedLeaf.cyclicProduct` gives a
leaf the independent product of itself with its two cyclic orientations; on a fixed tensor leg its
interface coordinate is a *triple* of source coordinates, one per orientation.  This module reads
each of the three components off the product marginal: projecting the product marginal to one
component recovers the corresponding source marginal, scaled by the square of the profile mass ---
the mass summed out of the other two independent components.

## Why a client needs it

A symmetrized laser client's value certificate constrains the *joint* three-orientation marginal
of a leg (`RationalTypedLeaf.KeepsMarginal`), while the leaf it must be compared with constrains
the letter type of a single orientation.  These three identities are what converts one into the
other; without them the two conditions are stated over different alphabets and cannot be compared.

This is a Lean bridge, not a step of any paper: it is the bookkeeping of an independent product
measure, and the scaling factor is exactly the mass the paper never writes because it normalizes.

Primary source: none; this is typed-leaf infrastructure.
-/

namespace AlgebraicComplexity

open Tensor
open scoped BigOperators

universe u v

namespace RationalTypedLeaf

variable {I : Type u} [Fintype I] [Nonempty I]
variable {A : Leg → Type v} [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]

omit [Nonempty I] [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)] in
/-- A triple sum of a product of three one-variable factors is the product of the three sums. -/
private theorem triple_sum_factor (count g : I → ℕ) :
    (∑ i, ∑ j, ∑ l, g i * count j * count l) =
      (∑ i, g i) * (∑ j, count j) * (∑ l, count l) := by
  calc (∑ i, ∑ j, ∑ l, g i * count j * count l)
      = ∑ i, ∑ j, g i * count j * (∑ l, count l) := by
        refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
        rw [Finset.mul_sum]
    _ = ∑ i, g i * (∑ j, count j) * (∑ l, count l) := by
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        rw [← Finset.sum_mul, ← Finset.mul_sum]
    _ = (∑ i, g i) * (∑ j, count j) * (∑ l, count l) := by
        rw [← Finset.sum_mul, ← Finset.sum_mul]

omit [Nonempty I] [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)] in
/-- The independent triple sum factors when the indicator sits on the first component. -/
private theorem cyclic_sum_fst_fst (count : I → ℕ) (p : I → Prop) [DecidablePred p] :
    (∑ x : (I × I) × I, if p x.1.1 then count x.1.1 * count x.1.2 * count x.2 else 0) =
      (∑ i, if p i then count i else 0) * (∑ j, count j) * (∑ l, count l) := by
  classical
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
  refine Eq.trans ?_ (triple_sum_factor count (fun i ↦ if p i then count i else 0))
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦
    Finset.sum_congr rfl fun l _ ↦ ?_
  by_cases h : p i
  · simp [h]
  · simp [h]

omit [Nonempty I] [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)] in
/-- The same with the indicator on the second component, by swapping the first two factors. -/
private theorem cyclic_sum_fst_snd (count : I → ℕ) (p : I → Prop) [DecidablePred p] :
    (∑ x : (I × I) × I, if p x.1.2 then count x.1.1 * count x.1.2 * count x.2 else 0) =
      (∑ i, if p i then count i else 0) * (∑ j, count j) * (∑ l, count l) := by
  classical
  rw [← cyclic_sum_fst_fst count p]
  refine Fintype.sum_equiv (Equiv.prodCongr (Equiv.prodComm I I) (Equiv.refl I)) _ _ ?_
  rintro ⟨⟨i, j⟩, l⟩
  show (if p j then count i * count j * count l else 0) =
    (if p j then count j * count i * count l else 0)
  by_cases h : p j
  · simp only [if_pos h]
    ring
  · simp only [if_neg h]

omit [Nonempty I] [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)] in
/-- The same with the indicator on the third component, by swapping the outer two factors. -/
private theorem cyclic_sum_snd (count : I → ℕ) (p : I → Prop) [DecidablePred p] :
    (∑ x : (I × I) × I, if p x.2 then count x.1.1 * count x.1.2 * count x.2 else 0) =
      (∑ i, if p i then count i else 0) * (∑ j, count j) * (∑ l, count l) := by
  classical
  rw [← cyclic_sum_fst_fst count p]
  refine Fintype.sum_equiv
    ⟨fun x ↦ ((x.2, x.1.2), x.1.1), fun x ↦ ((x.2, x.1.2), x.1.1),
      fun x ↦ rfl, fun x ↦ rfl⟩ _ _ ?_
  rintro ⟨⟨i, j⟩, l⟩
  show (if p l then count i * count j * count l else 0) =
    (if p l then count l * count j * count i else 0)
  by_cases h : p l
  · simp only [if_pos h]
    ring
  · simp only [if_neg h]

omit [Nonempty I] in
/-- **The first component of a cyclic product marginal is the source marginal at the same leg**,
scaled by the square of the profile mass. -/
theorem marginalProfile_cyclicProduct_fst_fst
    (leaf : RationalTypedLeaf I A) (c : Leg) :
    WordType.mappedType (fun t : CyclicTypedLeafCoordinate A c ↦ t.1.1)
        (leaf.cyclicProduct.marginalProfile c) =
      fun a ↦ leaf.marginalProfile c a * leaf.profile.mass ^ 2 := by
  classical
  funext b
  rw [marginalProfile, WordType.mappedType_comp, WordType.mappedType_eq_sum_ite]
  show (∑ x : (I × I) × I, if leaf.coordinate c x.1.1 = b then
      leaf.profile.count x.1.1 * leaf.profile.count x.1.2 * leaf.profile.count x.2 else 0) = _
  rw [cyclic_sum_fst_fst leaf.profile.count (fun i ↦ leaf.coordinate c i = b)]
  rw [marginalProfile, WordType.mappedType_eq_sum_ite]
  show _ = (∑ i, if leaf.coordinate c i = b then leaf.profile.count i else 0) *
    leaf.profile.mass ^ 2
  unfold PositiveIntegralProfile.mass WordType.profileMass
  ring

omit [Nonempty I] in
/-- **The second component of a cyclic product marginal is the source marginal at the
inverse-cyclic leg**, scaled by the square of the profile mass. -/
theorem marginalProfile_cyclicProduct_fst_snd
    (leaf : RationalTypedLeaf I A) (c : Leg) :
    WordType.mappedType (fun t : CyclicTypedLeafCoordinate A c ↦ t.1.2)
        (leaf.cyclicProduct.marginalProfile c) =
      fun a ↦ leaf.marginalProfile (cycle.symm c) a * leaf.profile.mass ^ 2 := by
  classical
  funext b
  rw [marginalProfile, WordType.mappedType_comp, WordType.mappedType_eq_sum_ite]
  show (∑ x : (I × I) × I, if leaf.coordinate (cycle.symm c) x.1.2 = b then
      leaf.profile.count x.1.1 * leaf.profile.count x.1.2 * leaf.profile.count x.2 else 0) = _
  rw [cyclic_sum_fst_snd leaf.profile.count (fun i ↦ leaf.coordinate (cycle.symm c) i = b)]
  rw [marginalProfile, WordType.mappedType_eq_sum_ite]
  show _ = (∑ i, if leaf.coordinate (cycle.symm c) i = b then leaf.profile.count i else 0) *
    leaf.profile.mass ^ 2
  unfold PositiveIntegralProfile.mass WordType.profileMass
  ring

omit [Nonempty I] in
/-- **The third component of a cyclic product marginal is the source marginal at the cyclic
leg**, scaled by the square of the profile mass. -/
theorem marginalProfile_cyclicProduct_snd
    (leaf : RationalTypedLeaf I A) (c : Leg) :
    WordType.mappedType (fun t : CyclicTypedLeafCoordinate A c ↦ t.2)
        (leaf.cyclicProduct.marginalProfile c) =
      fun a ↦ leaf.marginalProfile (cycle c) a * leaf.profile.mass ^ 2 := by
  classical
  funext b
  rw [marginalProfile, WordType.mappedType_comp, WordType.mappedType_eq_sum_ite]
  show (∑ x : (I × I) × I, if leaf.coordinate (cycle c) x.2 = b then
      leaf.profile.count x.1.1 * leaf.profile.count x.1.2 * leaf.profile.count x.2 else 0) = _
  rw [cyclic_sum_snd leaf.profile.count (fun i ↦ leaf.coordinate (cycle c) i = b)]
  rw [marginalProfile, WordType.mappedType_eq_sum_ite]
  show _ = (∑ i, if leaf.coordinate (cycle c) i = b then leaf.profile.count i else 0) *
    leaf.profile.mass ^ 2
  unfold PositiveIntegralProfile.mass WordType.profileMass
  ring

end RationalTypedLeaf

end AlgebraicComplexity
