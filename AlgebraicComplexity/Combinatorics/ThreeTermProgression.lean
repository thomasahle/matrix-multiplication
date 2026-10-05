/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import Mathlib.Algebra.BigOperators.Field
import Mathlib.Combinatorics.Additive.AP.Three.Defs
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Progression-free hashing

This file isolates the deterministic algebraic step shared by Coppersmith--Winograd hashing and
the more-asymmetric hashing theorem: the three hash values of a legal block triple form a
three-term arithmetic progression.  Restricting every hash to a progression-free bucket set
therefore forces all three values to agree.

The existence and size of Salem--Spencer/Behrend sets and the probabilistic isolation count are
separate theorems.  Keeping them separate lets this elementary step be reused over any field (in
particular an odd prime field) without importing asymptotics or probability.
-/

open scoped BigOperators

namespace AlgebraicComplexity

universe u v

namespace ThreeAPFree

variable {G : Type u} [AddCancelCommMonoid G] {B : Set G}

/-- Membership in a progression-free set turns the progression equation into equality of all
three entries. -/
theorem eq_and_eq (hB : ThreeAPFree B) {a b c : G}
    (ha : a ∈ B) (hb : b ∈ B) (hc : c ∈ B) (hprogression : a + b = c + c) :
    a = b ∧ b = c := by
  have hac : a = c := hB ha hc hb hprogression
  subst c
  have hba : b = a := add_left_cancel hprogression
  exact ⟨hba.symm, hba⟩

end ThreeAPFree

namespace ProgressionHash

variable {R : Type u} [Field R]
variable {ι : Type v} [Fintype ι]

/-- Linear part of the standard laser-method hash. -/
noncomputable def linear (weights input : ι → R) : R :=
  ∑ t, weights t * input t

/-- Hash of an `X`-block. -/
noncomputable def hashX (offset : R) (weights input : ι → R) : R :=
  offset + linear weights input

/-- Hash of a `Y`-block. -/
noncomputable def hashY (offset shift : R) (weights input : ι → R) : R :=
  offset + shift + linear weights input

/-- Hash of a `Z`-block.  The inverse of two is available because the hashing field has odd
characteristic. -/
noncomputable def hashZ
    (offset shift target : R) (weights input : ι → R) : R :=
  offset + (2 : R)⁻¹ * (shift + ∑ t, weights t * (target - input t))

/-- Coordinatewise legality `I_t + J_t + K_t = target` implies the linear-sum identity used in
the hash calculation. -/
theorem linear_add_eq_complement
    (weights I J K : ι → R) (target : R)
    (hlegal : ∀ t, I t + J t + K t = target) :
    linear weights I + linear weights J =
      ∑ t, weights t * (target - K t) := by
  classical
  rw [linear, linear, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro t _
  rw [← mul_add]
  congr 1
  rw [eq_sub_iff_add_eq]
  exact hlegal t

/-- The hashes of every legal block triple form a three-term arithmetic progression. -/
theorem hash_progression
    [NeZero (2 : R)]
    (offset shift target : R) (weights I J K : ι → R)
    (hlegal : ∀ t, I t + J t + K t = target) :
    hashX offset weights I + hashY offset shift weights J =
      hashZ offset shift target weights K + hashZ offset shift target weights K := by
  have hsum := linear_add_eq_complement weights I J K target hlegal
  unfold hashX hashY hashZ
  calc
    offset + linear weights I + (offset + shift + linear weights J) =
        offset + offset + (shift + (linear weights I + linear weights J)) := by ring
    _ = offset + offset + (shift + ∑ t, weights t * (target - K t)) := by rw [hsum]
    _ = offset + (2 : R)⁻¹ * (shift + ∑ t, weights t * (target - K t)) +
        (offset + (2 : R)⁻¹ * (shift + ∑ t, weights t * (target - K t))) := by
      field_simp
      ring

/-- After the Salem--Spencer zero-out, every surviving legal triple lies in one common bucket. -/
theorem surviving_hashes_equal
    [NeZero (2 : R)] {B : Set R} (hB : ThreeAPFree B)
    (offset shift target : R) (weights I J K : ι → R)
    (hlegal : ∀ t, I t + J t + K t = target)
    (hX : hashX offset weights I ∈ B)
    (hY : hashY offset shift weights J ∈ B)
    (hZ : hashZ offset shift target weights K ∈ B) :
    hashX offset weights I = hashY offset shift weights J ∧
      hashY offset shift weights J = hashZ offset shift target weights K :=
  ThreeAPFree.eq_and_eq hB hX hY hZ
    (hash_progression offset shift target weights I J K hlegal)

end ProgressionHash

end AlgebraicComplexity
