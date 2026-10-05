/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Tensor.GroupTensor
import AlgebraicComplexity.Tensor.IndependenceNumber

/-!
# The coefficient table of a group tensor

The independence-number API of `Tensor/IndependenceNumber.lean` is a calculus of *coefficient
tables* `T : (∀ i, κ i) → K`, not of abstract tensors, because the independence number is
basis-dependent.  This file supplies the coefficient table of the group tensor `T_G` of
`Tensor/GroupTensor.lean`, in the symmetric convention: the coefficient of a triple `a` is the
indicator of `a_X · a_Y · a_Z = 1`.

## Main definitions and results

* `groupCoefficients K G`: the table itself, and `groupCoefficients_ne_zero_iff`: its support is
  exactly the compatibility locus `a_X · a_Y · a_Z = 1`.
* `coordinateTensor_groupCoefficients`: the abstract tensor of the table is `groupTensor K G`, so
  every table-level statement really is a statement about `Tensor.groupTensor`.
* `coordinatePower_groupCoefficients`: `T_G^{⊗n} = T_{Gⁿ}` **on the nose** --- the `n`-th Kronecker
  power of the table of `G` is the table of the product group `Gⁿ = Fin n → G`, as the *same
  function*, so no relabelling is ever needed.

## Position in the library

Layer 1.  Paper-independent: it mentions no matrix-multiplication construction and no numerical
bound.  It is a leaf over `Tensor/GroupTensor.lean` and `Tensor/IndependenceNumber.lean`, kept
apart from the former so that clients of the group tensor which never mention coefficient tables
do not acquire the independence-number calculus.
-/

namespace AlgebraicComplexity.Tensor

universe u v

section Table

variable {K : Type u} [CommSemiring K] {G : Type v} [Group G] [DecidableEq G]

/-- **The coefficient table of the group tensor `T_G`**, in the symmetric convention of
`Tensor/GroupTensor.lean`: the coefficient of the triple `a` is `1` when `a_X · a_Y · a_Z = 1` and
`0` otherwise. -/
def groupCoefficients (K : Type u) [CommSemiring K] (G : Type v) [Group G] [DecidableEq G] :
    (∀ i, GroupIndex G i) → K :=
  fun a ↦ if GroupCompatible a then 1 else 0

/-- Evaluating the table of `T_G`: the indicator of `a_X · a_Y · a_Z = 1`. -/
theorem groupCoefficients_apply (a : ∀ i, GroupIndex G i) :
    groupCoefficients K G a = if a .X * a .Y * a .Z = 1 then 1 else 0 := rfl

/-- The coefficient at a compatible triple is `1`. -/
theorem groupCoefficients_of_mul_eq_one {a : ∀ i, GroupIndex G i}
    (h : a .X * a .Y * a .Z = 1) : groupCoefficients K G a = 1 :=
  if_pos h

/-- **The support of the table of `T_G` is the compatibility locus** `a_X · a_Y · a_Z = 1`.  This
is the only property of `T_G` used by the whole Lemma 6.1 correspondence. -/
theorem groupCoefficients_ne_zero_iff [Nontrivial K] (a : ∀ i, GroupIndex G i) :
    groupCoefficients K G a ≠ 0 ↔ a .X * a .Y * a .Z = 1 := by
  constructor
  · intro hne
    by_contra hc
    exact hne (if_neg hc)
  · intro hc
    rw [groupCoefficients_of_mul_eq_one hc]
    exact one_ne_zero

variable [Fintype G]

/-- The abstract tensor of the table `groupCoefficients K G` is the group tensor `T_G`, so every
statement below about the table really is a statement about `Tensor.groupTensor`. -/
theorem coordinateTensor_groupCoefficients :
    coordinateTensor (groupCoefficients K G) = groupTensor K G := by
  refine standardCoordinate_ext (K := K) (κ := GroupIndex G) fun a ↦ ?_
  rw [standardCoordinateEquiv_coordinateTensor, standardCoordinateEquiv_groupTensor]
  rfl

end Table
/-! ## The group-power identification

A variable of leg `i` of `T_G^{⊗n}` is a word `Fin n → G`, and a word is exactly an element of the
product group `Gⁿ = Fin n → G`.  The coefficient of a triple of words is the product of the `n`
letterwise coefficients, which is `1` exactly when every letter triple multiplies to `1`, i.e.
exactly when the triple of words multiplies to `1` in `Gⁿ`.  So the two tables are *the same
function*, and no relabelling is needed anywhere below. -/

section Power

variable {K : Type u} [CommSemiring K] {G : Type v} [Group G] [DecidableEq G]

/-- **`T_G^{⊗n}` is `T_{Gⁿ}`, on the nose.**  The `n`-th Kronecker power of the table of the group
tensor of `G` is the table of the group tensor of the product group `Gⁿ = Fin n → G`; both sides
are functions on triples of words, and they agree pointwise.

Proof sketch: multiplication in `Gⁿ` is letterwise, so the triple of words `p` satisfies
`p_X · p_Y · p_Z = 1` iff every letter triple does.  If it does, all `n` factors of the Kronecker
coefficient are `1`; if some letter fails, that factor is `0` and kills the product. -/
theorem coordinatePower_groupCoefficients (n : ℕ) :
    coordinatePower (groupCoefficients K G) n = groupCoefficients K (Fin n → G) := by
  funext p
  by_cases h : ∀ k : Fin n, p .X k * p .Y k * p .Z k = 1
  · have hall : (p .X * p .Y * p .Z : Fin n → G) = 1 := by
      funext k
      simpa using h k
    rw [groupCoefficients_of_mul_eq_one hall, coordinatePower_apply]
    refine Finset.prod_eq_one fun k _ ↦ ?_
    exact groupCoefficients_of_mul_eq_one (h k)
  · obtain ⟨k, hk⟩ := not_forall.mp h
    have hzero : (p .X * p .Y * p .Z : Fin n → G) ≠ 1 := by
      intro hcon
      exact hk (by simpa using congrFun hcon k)
    rw [groupCoefficients_apply, if_neg hzero, coordinatePower_apply]
    refine Finset.prod_eq_zero (Finset.mem_univ k) ?_
    exact if_neg hk

end Power

end AlgebraicComplexity.Tensor
