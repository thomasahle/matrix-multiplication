/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Tensor.PartitionedGrouping
import AlgebraicComplexity.Tensor.HoleRepair

/-!
# Group fibers as explicit damaged boxes

A `PartitionedTensor.LegGrouping` makes the group of every supported constituent readable from
each individual leg label.  Consequently one group fiber has no hidden non-Cartesian deletion:
it is exactly the ambient partitioned tensor restricted to the leg labels that occur in that
fiber.  Equivalently, it is the box obtained by deleting the complementary `fiberHoles`.

This is the semantic bridge from compatibility-cleaned group fibers to varying-pattern hole
repair.
-/

namespace AlgebraicComplexity.Tensor

universe u v w x

variable {K : Type u} [CommSemiring K]
variable {A : Leg → Type w} [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]
variable {V : ∀ c, A c → Type v}
variable [∀ c a, AddCommMonoid (V c a)] [∀ c a, Module K (V c a)]
variable {P : PartitionedTensor (K := K) (A := A) V}
variable {Γ : Type x} [DecidableEq Γ]

omit [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)] in
/-- Sequential legwise zero-outs compose: projection closure on `left`, followed by projection
closure on `right`, is projection closure from the original ambient support on `left ∪ right`.

This formulation is useful for cleanup pipelines because each stage normally acts on a singleton
leg, while the final damaged-box statement needs closure on all three legs at once. -/
theorem IsProjectionClosed.trans_union
    {ambient middle selected : Finset (BlockAddress A)}
    {left right : Finset Leg}
    (hleft : IsProjectionClosed ambient middle left)
    (hright : IsProjectionClosed middle selected right) :
    IsProjectionClosed ambient selected (left ∪ right) := by
  refine ⟨hright.1.trans hleft.1, ?_⟩
  intro address haddress hprojected
  have hmiddle : address ∈ middle := by
    apply hleft.2 address haddress
    intro c hc
    obtain ⟨witness, hwitness, heq⟩ :=
      hprojected c (Finset.mem_union.mpr (Or.inl hc))
    exact ⟨witness, hright.1 hwitness, heq⟩
  apply hright.2 address hmiddle
  intro c hc
  exact hprojected c (Finset.mem_union.mpr (Or.inr hc))

/-- Any ordinary legwise `PartitionedTensor.select` is projection-closed in its source support.
We state closure on all three legs, which is the convenient form for composing a cleanup pipeline
before interpreting its output as a damaged Cartesian box. -/
theorem PartitionedTensor.select_support_isProjectionClosed_univ
    (P : PartitionedTensor (K := K) (A := A) V)
    (keep : ∀ c, A c → Prop) [∀ c a, Decidable (keep c a)] :
    IsProjectionClosed P.support (P.select keep).support Finset.univ := by
  classical
  refine ⟨?_, ?_⟩
  · intro address haddress
    exact (PartitionedTensor.mem_select_support P keep address).mp haddress |>.1
  · intro address haddress hprojected
    apply (PartitionedTensor.mem_select_support P keep address).mpr
    refine ⟨haddress, ?_⟩
    intro c
    obtain ⟨witness, hwitness, heq⟩ := hprojected c (Finset.mem_univ c)
    have hwitnessKeep :=
      (PartitionedTensor.mem_select_support P keep witness).mp hwitness |>.2 c
    simpa [heq] using hwitnessKeep

namespace PartitionedTensor.LegGrouping

/-- Block labels on one leg that occur in a given group fiber. -/
noncomputable def fiberParts (G : P.LegGrouping Γ) (γ : Γ) (c : Leg) : Finset (A c) := by
  classical
  exact (G.fiberSupport γ).image (fun address ↦ address c)

@[simp] theorem mem_fiberParts_iff (G : P.LegGrouping Γ) (γ : Γ)
    (c : Leg) (a : A c) :
    a ∈ G.fiberParts γ c ↔
      ∃ address ∈ P.support, G.group address = γ ∧ address c = a := by
  classical
  simp [fiberParts, fiberSupport, and_assoc]

/-- Missing block labels of one group fiber, relative to the full ambient block-label types. -/
noncomputable def fiberHoles (G : P.LegGrouping Γ) (γ : Γ) (c : Leg) : Finset (A c) :=
  Finset.univ \ G.fiberParts γ c

@[simp] theorem mem_fiberHoles_iff (G : P.LegGrouping Γ) (γ : Γ)
    (c : Leg) (a : A c) :
    a ∈ G.fiberHoles γ c ↔ a ∉ G.fiberParts γ c := by
  classical
  simp [fiberHoles]

/-- A leg-readable group fiber is exactly the Cartesian block-label restriction induced by the
labels occurring in that fiber. -/
theorem fiber_eq_box_fiberParts (G : P.LegGrouping Γ) (γ : Γ) :
    G.fiber γ = P.box (G.fiberParts γ) := by
  classical
  apply PartitionedTensor.ext
  · ext address
    simp only [fiber, PartitionedTensor.withSupport_support,
      PartitionedTensor.mem_box_support, fiberSupport, Finset.mem_filter]
    constructor
    · rintro ⟨haddress, hgroup⟩
      refine ⟨haddress, ?_⟩
      intro c
      exact (G.mem_fiberParts_iff γ c (address c)).2
        ⟨address, haddress, hgroup, rfl⟩
    · rintro ⟨haddress, hparts⟩
      have hpartX := hparts .X
      obtain ⟨witness, hwitness, hwitnessGroup, hwitnessX⟩ :=
        (G.mem_fiberParts_iff γ .X (address .X)).1 hpartX
      refine ⟨haddress, ?_⟩
      calc
        G.group address = G.blockGroup .X (address .X) :=
          (G.compatible address haddress .X).symm
        _ = G.blockGroup .X (witness .X) := by rw [hwitnessX]
        _ = G.group witness := G.compatible witness hwitness .X
        _ = γ := hwitnessGroup
  · rfl

@[simp] theorem univ_sdiff_fiberHoles (G : P.LegGrouping Γ) (γ : Γ) (c : Leg) :
    Finset.univ \ G.fiberHoles γ c = G.fiberParts γ c := by
  classical
  ext a
  simp [fiberHoles]

/-- Paper-facing damaged-box form of a cleaned group fiber.  Its explicit hole triple consists
precisely of the ambient block labels absent from the fiber. -/
theorem fiber_eq_box_compl_fiberHoles (G : P.LegGrouping Γ) (γ : Γ) :
    G.fiber γ = P.box (fun c ↦ Finset.univ \ G.fiberHoles γ c) := by
  rw [G.fiber_eq_box_fiberParts]
  congr 1
  funext c
  exact G.univ_sdiff_fiberHoles γ c |>.symm

/-- Restriction-facing form used by `RepairPlan.indexedDirectSum_repairPlans`. -/
theorem fiber_restricts_box_compl_fiberHoles (G : P.LegGrouping Γ) (γ : Γ) :
    Restricts (G.fiber γ).realize
      (P.box (fun c ↦ Finset.univ \ G.fiberHoles γ c)).realize :=
  Restricts.of_eq (congrArg PartitionedTensor.realize
    (G.fiber_eq_box_compl_fiberHoles γ))

/-! ## Fibers of a projection-closed cleanup relative to an ideal ambient tensor -/

/-- If `selected` is obtained from an ideal ambient support by independent variable zero-outs on
all three legs, a leg-readable group fiber of the cleaned tensor is exactly a box of the *ideal
ambient tensor*.  Thus no non-Cartesian deletion is hidden inside the cleaned fiber.

This is stronger than `fiber_eq_box_fiberParts`: there the box is taken inside the already-cleaned
tensor, whereas here it is taken inside the unbroken tensor `P`. -/
theorem fiber_eq_ambientBox_fiberParts
    (selected : Finset (BlockAddress A))
    (hclosed : IsProjectionClosed P.support selected Finset.univ)
    (G : (P.withSupport selected).LegGrouping Γ) (γ : Γ) :
    G.fiber γ = P.box (G.fiberParts γ) := by
  classical
  apply PartitionedTensor.ext
  · ext address
    simp only [fiber, PartitionedTensor.withSupport_support,
      PartitionedTensor.mem_box_support, fiberSupport, Finset.mem_filter]
    constructor
    · rintro ⟨hselected, hgroup⟩
      refine ⟨hclosed.1 hselected, ?_⟩
      intro c
      exact (G.mem_fiberParts_iff γ c (address c)).2
        ⟨address, hselected, hgroup, rfl⟩
    · rintro ⟨hambient, hparts⟩
      have hselected : address ∈ selected := by
        apply hclosed.2 address hambient
        intro c _hc
        obtain ⟨witness, hwitness, _hwitnessGroup, hwitnessLabel⟩ :=
          (G.mem_fiberParts_iff γ c (address c)).1 (hparts c)
        exact ⟨witness, hwitness, hwitnessLabel.symm⟩
      have hpartX := hparts .X
      obtain ⟨witness, hwitness, hwitnessGroup, hwitnessX⟩ :=
        (G.mem_fiberParts_iff γ .X (address .X)).1 hpartX
      refine ⟨hselected, ?_⟩
      calc
        G.group address = G.blockGroup .X (address .X) :=
          (G.compatible address hselected .X).symm
        _ = G.blockGroup .X (witness .X) := by rw [hwitnessX]
        _ = G.group witness := G.compatible witness hwitness .X
        _ = γ := hwitnessGroup
  · rfl

/-- Missing labels of a cleaned fiber, now interpreted relative to the ideal ambient tensor. -/
theorem fiber_eq_ambientBox_compl_fiberHoles
    (selected : Finset (BlockAddress A))
    (hclosed : IsProjectionClosed P.support selected Finset.univ)
    (G : (P.withSupport selected).LegGrouping Γ) (γ : Γ) :
    G.fiber γ =
      P.box (fun c ↦ Finset.univ \ G.fiberHoles γ c) := by
  rw [G.fiber_eq_ambientBox_fiberParts selected hclosed]
  congr 1
  funext c
  exact G.univ_sdiff_fiberHoles γ c |>.symm

/-- Restriction-facing form of `fiber_eq_ambientBox_compl_fiberHoles`. -/
theorem fiber_restricts_ambientBox_compl_fiberHoles
    (selected : Finset (BlockAddress A))
    (hclosed : IsProjectionClosed P.support selected Finset.univ)
    (G : (P.withSupport selected).LegGrouping Γ) (γ : Γ) :
    Restricts (G.fiber γ).realize
      (P.box (fun c ↦ Finset.univ \ G.fiberHoles γ c)).realize :=
  Restricts.of_eq (congrArg PartitionedTensor.realize
    (G.fiber_eq_ambientBox_compl_fiberHoles selected hclosed γ))

end PartitionedTensor.LegGrouping

end AlgebraicComplexity.Tensor
