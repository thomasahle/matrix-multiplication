/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Combinatorics.HoleRepair
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.GroupAction.Transitive

/-!
# Uniform finite relabelings from transitive group actions

The hole-repair API deliberately asks only for a finite family of permutations satisfying an
exact pointwise counting identity.  A transitive finite group action supplies such a family:
every fiber of `g ↦ g • a` is a coset of the stabilizer of `a`, and orbit--stabilizer gives the
required division-free cardinality formula.
-/

namespace AlgebraicComplexity.HoleRepair

universe u v

/-- The group elements carrying `a` to `b` are in bijection with the stabilizer of `a`. -/
noncomputable def actionFiberEquivStabilizer
    {G : Type u} {A : Type v} [Group G] [MulAction G A]
    [MulAction.IsPretransitive G A] (a b : A) :
    {g : G // g • a = b} ≃ MulAction.stabilizer G a := by
  choose h hh using MulAction.exists_smul_eq G a b
  exact
    { toFun := fun g ↦ ⟨h⁻¹ * g.1, by
          rw [MulAction.mem_stabilizer_iff, mul_smul, g.2, ← hh]
          exact inv_smul_smul h a⟩
      invFun := fun s ↦ ⟨h * s.1, by
          rw [mul_smul, s.2, hh]⟩
      left_inv := by
        intro g
        apply Subtype.ext
        simp
      right_inv := by
        intro s
        apply Subtype.ext
        simp }

/-- A finite transitive group action is exactly uniform in the sense required by hole repair. -/
noncomputable def UniformOnParts.ofPretransitiveMulAction
    {G : Type u} {A : Type v}
    [Group G] [Fintype G] [DecidableEq G]
    [Fintype A] [DecidableEq A] [MulAction G A]
    [MulAction.IsPretransitive G A] : UniformOnParts G A :=
  UniformOnParts.ofPointwise (fun g ↦ MulAction.toPermHom G A g) (by
    classical
    intro a b
    have hfiber :
        (Finset.univ.filter fun g : G ↦ g • a = b).card =
          Fintype.card {g : G // g • a = b} := by
      rw [Fintype.card_subtype]
    have hstabilizer :
        Fintype.card {g : G // g • a = b} =
          Fintype.card (MulAction.stabilizer G a) :=
      Fintype.card_congr (actionFiberEquivStabilizer a b)
    have horbit : MulAction.orbit G a = Set.univ :=
      MulAction.orbit_eq_univ G a
    have hcardOrbit : Fintype.card (MulAction.orbit G a) = Fintype.card A := by
      rw [horbit]
      exact Fintype.card_setUniv
    have horbitStabilizer :=
      MulAction.card_orbit_mul_card_stabilizer_eq_card_group G a
    change Fintype.card A *
        (Finset.univ.filter fun g : G ↦ g • a = b).card = Fintype.card G
    rw [hfiber, hstabilizer, ← hcardOrbit]
    exact horbitStabilizer)

@[simp] theorem UniformOnParts.ofPretransitiveMulAction_relabel
    {G : Type u} {A : Type v}
    [Group G] [Fintype G] [DecidableEq G]
    [Fintype A] [DecidableEq A] [MulAction G A]
    [MulAction.IsPretransitive G A] (g : G) :
    (UniformOnParts.ofPretransitiveMulAction (G := G) (A := A)).relabel g =
      MulAction.toPermHom G A g :=
  rfl

end AlgebraicComplexity.HoleRepair
