/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Combinatorics.HoleRepair
import AlgebraicComplexity.MatrixMultiplication.InterfaceHoleRepairDepth
import AlgebraicComplexity.Tensor.HoleRepairTree

/-!
# Constructing recursive interface hole-repair plans

`Tensor.HoleRepairTree` proves the semantic seven-branch repair theorem for a supplied finite
plan, while `Combinatorics.HoleRepair` proves that a uniformly random relabelling simultaneously
shrinks the holes on all three legs.  This module joins those two reusable results.

The principal certificate is a finite family of structure-preserving relabellings whose action
on every leg is uniform.  If the holes occupy at most a `1 / (4 * base)` fraction of each leg,
one member shrinks every target-hole intersection by the factor `base`.  Recursing on the sum of
the three ceiling-log depths constructs an actual `RepairPlan`; no repair stage is assumed.
-/

namespace AlgebraicComplexity.HoleRepair

open AlgebraicComplexity.Tensor
open scoped BigOperators

universe u

variable {K : Type u} [CommSemiring K]
variable {A : Leg → Type u} [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]
variable {V : ∀ c, A c → Type u}
variable [∀ c a, AddCommMonoid (V c a)] [∀ c a, Module K (V c a)]
variable {G : Type u} [Fintype G] [DecidableEq G] [Nonempty G]

/-- A finite family of tensor-structure relabellings which is uniform on the block labels of
each leg.  The same family element acts simultaneously on all three legs. -/
structure UniformStructureRelabelings
    (P : PartitionedTensor (K := K) (A := A) V) where
  relabeling : G → P.StructureRelabeling
  uniform : ∀ c, UniformOnParts G (A c)
  uniform_eq : ∀ g c, (uniform c).relabel g = (relabeling g).partEquiv c

namespace UniformStructureRelabelings

variable {P : PartitionedTensor (K := K) (A := A) V}

/-- One structure-preserving relabelling simultaneously has the paper's four-times-mean overlap
bound on all three legs. -/
theorem exists_small_movedHoles
    (family : UniformStructureRelabelings (G := G) P)
    (target holes : ∀ c, Finset (A c)) :
    ∃ g : G, ∀ c,
      Fintype.card (A c) *
          (target c ∩ relabelParts (family.relabeling g).partEquiv holes c).card ≤
        4 * (target c).card * (holes c).card := by
  obtain ⟨g, hX, hY, hZ⟩ := exists_simultaneously_small_overlap
    (family.uniform .X) (family.uniform .Y) (family.uniform .Z)
    (target .X) (holes .X) (target .Y) (holes .Y) (target .Z) (holes .Z)
  refine ⟨g, ?_⟩
  intro c
  have hoverlap (d : Leg) :
      (family.uniform d).overlapCard (target d) (holes d) g =
        (target d ∩
          relabelParts (family.relabeling g).partEquiv holes d).card := by
    rw [(family.uniform d).overlapCard_eq_card_inter_image]
    unfold relabelParts
    rw [family.uniform_eq]
  cases c with
  | X => simpa [hoverlap .X] using hX
  | Y => simpa [hoverlap .Y] using hY
  | Z => simpa [hoverlap .Z] using hZ

/-- Under the standard hole-density hypothesis, one relabelling shrinks every moved-hole
intersection by the prescribed integer factor. -/
theorem exists_simultaneously_shrinking
    (family : UniformStructureRelabelings (G := G) P)
    (base : ℕ) (target holes : ∀ c, Finset (A c))
    (hsparse : ∀ c,
      base * (4 * (holes c).card) ≤ Fintype.card (A c)) :
    ∃ g : G, ∀ c,
      base *
          (target c ∩ relabelParts (family.relabeling g).partEquiv holes c).card ≤
        (target c).card := by
  obtain ⟨g, hsmall⟩ := family.exists_small_movedHoles target holes
  refine ⟨g, ?_⟩
  intro c
  let overlap :=
    (target c ∩ relabelParts (family.relabeling g).partEquiv holes c).card
  let density := 4 * (holes c).card
  have htargetLe : (target c).card ≤ Fintype.card (A c) := Finset.card_le_univ _
  by_cases hcardZero : Fintype.card (A c) = 0
  · have htargetZero : (target c).card = 0 := Nat.eq_zero_of_le_zero (by
      simpa [hcardZero] using htargetLe)
    have htargetEmpty : target c = ∅ := Finset.card_eq_zero.mp htargetZero
    simp [htargetEmpty]
  have hcardPos : 0 < Fintype.card (A c) := Nat.pos_of_ne_zero hcardZero
  have hsmall' : Fintype.card (A c) * overlap ≤ density * (target c).card := by
    calc
      Fintype.card (A c) * overlap ≤
          4 * (target c).card * (holes c).card := by
        simpa [overlap] using hsmall c
      _ = density * (target c).card := by
        dsimp [density]
        ring
  have hsparse' : base * density ≤ Fintype.card (A c) := by
    simpa [density] using hsparse c
  by_cases hdensity : density = 0
  · have hoverlap : overlap = 0 := by
      have : Fintype.card (A c) * overlap = 0 := by
        apply Nat.eq_zero_of_le_zero
        simpa [hdensity] using hsmall'
      exact (Nat.mul_eq_zero.mp this).resolve_left hcardPos.ne'
    change base * overlap ≤ (target c).card
    simp [hoverlap]
  · have hdensityPos : 0 < density := Nat.pos_of_ne_zero hdensity
    have hcombined : (base * overlap) * density ≤ (target c).card * density := by
      calc
        (base * overlap) * density = (base * density) * overlap := by ring
        _ ≤ Fintype.card (A c) * overlap :=
          Nat.mul_le_mul_right overlap hsparse'
        _ ≤ density * (target c).card := hsmall'
        _ = (target c).card * density := Nat.mul_comm _ _
    exact le_of_mul_le_mul_right hcombined hdensityPos

end UniformStructureRelabelings

omit [∀ c, Fintype (A c)] in
private theorem splitBoxParts_subset
    (target holes : ∀ c, Finset (A c)) (mask : Leg → Bool) (c : Leg) :
    splitBoxParts target holes mask c ⊆ target c := by
  intro part hpart
  cases hmask : mask c <;>
    simp [splitBoxParts, splitPart, hmask] at hpart ⊢ <;> exact hpart.1

private theorem recursiveRepairMask_has_false (mask : RecursiveRepairMask) :
    ∃ c, mask.1 c = false := by
  by_contra hfalse
  push Not at hfalse
  apply mask.property
  funext c
  have hc := hfalse c
  cases h : mask.1 c
  · exact (hc h).elim
  · rfl

omit [∀ c, Fintype (A c)] in
/-- Every nonempty recursive child decreases the logarithmic repair depth by at least one when
all three moved-hole intersections shrink by `base`. -/
theorem logarithmicRepairDepth_splitBoxParts_add_one_le
    {base : ℕ} (hbase : 1 < base)
    (target movedHoles : ∀ c, Finset (A c))
    (hshrink : ∀ c,
      base * (target c ∩ movedHoles c).card ≤ (target c).card)
    (mask : RecursiveRepairMask)
    (hnonempty : ∀ c, (splitBoxParts target movedHoles mask.1 c).Nonempty) :
    logarithmicRepairDepth base (splitBoxParts target movedHoles mask.1) + 1 ≤
      logarithmicRepairDepth base target := by
  obtain ⟨pivot, hpivot⟩ := recursiveRepairMask_has_false mask
  have hsubset (c : Leg) :
      (splitBoxParts target movedHoles mask.1 c).card ≤ (target c).card :=
    Finset.card_le_card (splitBoxParts_subset target movedHoles mask.1 c)
  have hclog (c : Leg) :
      Nat.clog base (splitBoxParts target movedHoles mask.1 c).card ≤
        Nat.clog base (target c).card :=
    Nat.clog_mono_right base (hsubset c)
  have hpivotCard :
      base * (splitBoxParts target movedHoles mask.1 pivot).card ≤
        (target pivot).card := by
    simpa [splitBoxParts, splitPart, hpivot] using hshrink pivot
  have hpivotPositive :
      0 < (splitBoxParts target movedHoles mask.1 pivot).card :=
    Finset.card_pos.mpr (hnonempty pivot)
  have hpivotClog :
      Nat.clog base (splitBoxParts target movedHoles mask.1 pivot).card + 1 ≤
        Nat.clog base (target pivot).card :=
    clog_add_one_le_of_mul_le hbase hpivotPositive hpivotCard
  have hX := hclog .X
  have hY := hclog .Y
  have hZ := hclog .Z
  unfold logarithmicRepairDepth
  simp only [Tensor.sum_leg]
  fin_cases pivot <;> omega

/-- Uniform structure relabellings and the paper's hole-density inequality construct a complete
finite repair plan.  Its height is at most one plus the sum of the three ceiling-log part counts.

The proof is strong induction on `logarithmicRepairDepth`.  At a nonempty node, simultaneous
shuffling chooses one relabelling that shrinks all three moved-hole intersections.  Each of the
seven recursive masks contains a hole on at least one leg, so every nonempty child decreases the
measure.  A child with an empty leg is discharged by `RepairPlan.empty`. -/
theorem exists_repairPlan_height_le
    {P : PartitionedTensor (K := K) (A := A) V}
    (family : UniformStructureRelabelings (G := G) P)
    {base : ℕ} (hbase : 1 < base)
    (holes : ∀ c, Finset (A c))
    (hsparse : ∀ c,
      base * (4 * (holes c).card) ≤ Fintype.card (A c))
    (target : ∀ c, Finset (A c)) :
    ∃ plan : RepairPlan P target,
      plan.height ≤ logarithmicRepairDepth base target + 1 := by
  classical
  generalize hdepth : logarithmicRepairDepth base target = depth
  induction depth using Nat.strong_induction_on generalizing target with
  | h depth ih =>
      by_cases hX : target .X = ∅
      · refine ⟨RepairPlan.empty target .X hX, ?_⟩
        simp [RepairPlan.height]
      by_cases hY : target .Y = ∅
      · refine ⟨RepairPlan.empty target .Y hY, ?_⟩
        simp [RepairPlan.height]
      by_cases hZ : target .Z = ∅
      · refine ⟨RepairPlan.empty target .Z hZ, ?_⟩
        simp [RepairPlan.height]
      obtain ⟨g, hshrink⟩ :=
        family.exists_simultaneously_shrinking base target holes hsparse
      let movedHoles : ∀ c, Finset (A c) :=
        relabelParts (family.relabeling g).partEquiv holes
      have hshrinkMoved : ∀ c,
          base * (target c ∩ movedHoles c).card ≤ (target c).card := by
        intro c
        simpa [movedHoles] using hshrink c
      have childWitness : ∀ mask : RecursiveRepairMask,
          ∃ plan : RepairPlan P (splitBoxParts target movedHoles mask.1),
            plan.height ≤ logarithmicRepairDepth base target := by
        intro mask
        let child : ∀ c, Finset (A c) := splitBoxParts target movedHoles mask.1
        by_cases hchildX : child .X = ∅
        · refine ⟨RepairPlan.empty child .X hchildX, ?_⟩
          change 0 ≤ logarithmicRepairDepth base target
          omega
        by_cases hchildY : child .Y = ∅
        · refine ⟨RepairPlan.empty child .Y hchildY, ?_⟩
          change 0 ≤ logarithmicRepairDepth base target
          omega
        by_cases hchildZ : child .Z = ∅
        · refine ⟨RepairPlan.empty child .Z hchildZ, ?_⟩
          change 0 ≤ logarithmicRepairDepth base target
          omega
        have hchildNonempty : ∀ c, (child c).Nonempty := by
          intro c
          fin_cases c
          · exact Finset.nonempty_iff_ne_empty.mpr hchildX
          · exact Finset.nonempty_iff_ne_empty.mpr hchildY
          · exact Finset.nonempty_iff_ne_empty.mpr hchildZ
        have hdecrease :
            logarithmicRepairDepth base child + 1 ≤
              logarithmicRepairDepth base target := by
          exact logarithmicRepairDepth_splitBoxParts_add_one_le hbase
            target movedHoles hshrinkMoved mask hchildNonempty
        have hchildLt : logarithmicRepairDepth base child < depth := by
          rw [← hdepth]
          omega
        obtain ⟨plan, hplan⟩ :=
          ih (logarithmicRepairDepth base child) hchildLt child rfl
        exact ⟨plan, hplan.trans hdecrease⟩
      choose children hchildren using childWitness
      let plan : RepairPlan P target :=
        RepairPlan.node target holes (family.relabeling g) children
      refine ⟨plan, ?_⟩
      rw [← hdepth]
      change 1 + Finset.univ.sup
          (fun mask : RecursiveRepairMask ↦
            RepairPlan.height (children mask)) ≤
        logarithmicRepairDepth base target + 1
      have hsup : Finset.univ.sup
          (fun mask : RecursiveRepairMask ↦ RepairPlan.height (children mask)) ≤
          logarithmicRepairDepth base target := by
        apply Finset.sup_le
        intro mask _hmask
        exact hchildren mask
      omega

/-- Paper-facing finite repair certificate: an explicitly constructed plan has a semantically
valid source tensor and consumes at most the complete seven-ary tree budget at the proved
logarithmic depth. -/
theorem exists_repairPlan_with_copyBound
    {P : PartitionedTensor (K := K) (A := A) V}
    (family : UniformStructureRelabelings (G := G) P)
    {base : ℕ} (hbase : 1 < base)
    (holes : ∀ c, Finset (A c))
    (hsparse : ∀ c,
      base * (4 * (holes c).card) ≤ Fintype.card (A c))
    (target : ∀ c, Finset (A c)) :
    ∃ plan : RepairPlan P target,
      Restricts plan.sourceTensor (P.box target).realize ∧
      plan.copyCount ≤
        7 ^ (logarithmicRepairDepth base target + 1) := by
  obtain ⟨plan, hheight⟩ :=
    exists_repairPlan_height_le family hbase holes hsparse target
  refine ⟨plan, plan.source_restricts, ?_⟩
  exact plan.copyCount_le_pow_height.trans
    (Nat.pow_le_pow_right (by norm_num : 0 < 7) hheight)

/-- Counted form of the constructed repair plan.  The source is a flat direct sum indexed by
`Fin plan.copyCount`, so the numerical copy bound can be composed directly with a finite
extraction theorem. -/
theorem exists_repairPlan_flatCopies_with_copyBound
    {P : PartitionedTensor (K := K) (A := A) V}
    (family : UniformStructureRelabelings (G := G) P)
    {base : ℕ} (hbase : 1 < base)
    (holes : ∀ c, Finset (A c))
    (hsparse : ∀ c,
      base * (4 * (holes c).card) ≤ Fintype.card (A c))
    (target : ∀ c, Finset (A c)) :
    ∃ plan : RepairPlan P target,
      Restricts plan.flatCopies (P.box target).realize ∧
      plan.copyCount ≤
        7 ^ (logarithmicRepairDepth base target + 1) := by
  obtain ⟨plan, hheight⟩ :=
    exists_repairPlan_height_le family hbase holes hsparse target
  refine ⟨plan, plan.flatCopies_restricts, ?_⟩
  exact plan.copyCount_le_pow_height.trans
    (Nat.pow_le_pow_right (by norm_num : 0 < 7) hheight)

end AlgebraicComplexity.HoleRepair
