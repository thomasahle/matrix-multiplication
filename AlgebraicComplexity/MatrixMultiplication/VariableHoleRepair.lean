/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.InterfaceHoleRepair

/-!
# Repairing from a finite supply of differently damaged copies

The recursive hole lemma consumes a fresh broken tensor at every internal node.  Different
copies produced by compatibility cleanup generally have different missing-part sets, so the
fixed-pattern construction in `InterfaceHoleRepair` is not by itself the paper's finite theorem.

This module indexes a complete seven-branch supply tree and constructs a `RepairPlan` whose
every occurrence is assigned injectively to that supply.  Each supplied copy may have its own
hole pattern, subject only to the same density bound.  Together with
`RepairPlan.indexedDirectSum_repairPlans`, this is the exact adapter from a large family of sparse
cleaned fibers to intact interface tensors.
-/

namespace AlgebraicComplexity.HoleRepair

open AlgebraicComplexity.Tensor

universe u

/-- Positions in a complete seven-branch repair supply of depth `d`.

Depth zero contains just the root.  At positive depth there is one root and one recursively
indexed supply below each of the seven non-all-non-hole masks. -/
def RepairSupplyIndex : ℕ → Type
  | 0 => Unit
  | d + 1 => Option (RecursiveRepairMask × RepairSupplyIndex d)

instance repairSupplyIndexFintype (d : ℕ) : Fintype (RepairSupplyIndex d) := by
  induction d with
  | zero =>
      change Fintype Unit
      exact inferInstance
  | succ d ih =>
      letI : Fintype (RepairSupplyIndex d) := ih
      change Fintype (Option (RecursiveRepairMask × RepairSupplyIndex d))
      exact inferInstance

instance repairSupplyIndexDecidableEq (d : ℕ) : DecidableEq (RepairSupplyIndex d) := by
  induction d with
  | zero =>
      change DecidableEq Unit
      exact inferInstance
  | succ d ih =>
      letI : DecidableEq (RepairSupplyIndex d) := ih
      change DecidableEq (Option (RecursiveRepairMask × RepairSupplyIndex d))
      exact inferInstance

/-- Root position of a repair supply. -/
def RepairSupplyIndex.root : (d : ℕ) → RepairSupplyIndex d
  | 0 => ()
  | _d + 1 => none

/-- Embed a child supply below one recursive repair mask. -/
def RepairSupplyIndex.child (d : ℕ) (mask : RecursiveRepairMask) :
    RepairSupplyIndex d ↪ RepairSupplyIndex (d + 1) where
  toFun position := some (mask, position)
  inj' := by
    intro left right heq
    exact congrArg Prod.snd (Option.some.inj heq)

/-- The supply contains the complete seven-branch tree budget. -/
theorem card_repairSupplyIndex (d : ℕ) :
    Fintype.card (RepairSupplyIndex d) = sevenBranchBudget d := by
  induction d with
  | zero =>
      change Fintype.card Unit = 1
      simp
  | succ d ih =>
      change Fintype.card (Option (RecursiveRepairMask × RepairSupplyIndex d)) =
        sevenBranchBudget (d + 1)
      rw [Fintype.card_option, Fintype.card_prod,
        Tensor.RepairPlan.card_recursiveRepairMask, ih]
      rw [sevenBranchBudget_succ]
      omega

/-- Coarse power bound for the number of supplied damaged copies. -/
theorem card_repairSupplyIndex_le_pow (d : ℕ) :
    Fintype.card (RepairSupplyIndex d) ≤ 7 ^ (d + 1) := by
  rw [card_repairSupplyIndex]
  exact sevenBranchBudget_le_pow d

variable {K : Type u} [CommSemiring K]
variable {A : Leg → Type u} [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]
variable {V : ∀ c, A c → Type u}
variable [∀ c a, AddCommMonoid (V c a)] [∀ c a, Module K (V c a)]
variable {P : PartitionedTensor (K := K) (A := A) V}

/-- A repair plan whose every consumed occurrence is assigned to a distinct member of a finite
varying-hole supply. -/
structure VariableRepairCertificate
    {target : ∀ c, Finset (A c)} {d : ℕ}
    (holes : RepairSupplyIndex d → ∀ c, Finset (A c)) where
  plan : RepairPlan P target
  pick : plan.Copy ↪ RepairSupplyIndex d
  holesAt_eq : ∀ occurrence,
    plan.holesAt occurrence = holes (pick occurrence)
  height_le : plan.height ≤ d + 1

/-- An empty target needs no supplied damaged copy. -/
noncomputable def VariableRepairCertificate.empty
    {target : ∀ c, Finset (A c)} {d : ℕ}
    (holes : RepairSupplyIndex d → ∀ c, Finset (A c))
    (leg : Leg) (hempty : target leg = ∅) :
    VariableRepairCertificate (P := P) (target := target) holes := by
  let plan : RepairPlan P target := RepairPlan.empty target leg hempty
  let pick : plan.Copy ↪ RepairSupplyIndex d :=
    { toFun := fun occurrence ↦ Fin.elim0 occurrence
      inj' := fun occurrence ↦ Fin.elim0 occurrence }
  exact
    { plan := plan
      pick := pick
      holesAt_eq := fun occurrence ↦ Fin.elim0 occurrence
      height_le := by simp [plan, RepairPlan.height] }

namespace VariableRepairCertificate

/-- A depth-zero supply contains only its root.  If every recursive child box is empty, that one
supplied damaged copy completes the repair plan. -/
noncomputable def root
    {target : ∀ c, Finset (A c)}
    (holes : RepairSupplyIndex 0 → ∀ c, Finset (A c))
    (relabeling : P.StructureRelabeling)
    (emptyLeg : ∀ mask : RecursiveRepairMask, Leg)
    (hempty : ∀ mask,
      splitBoxParts target
        (relabelParts relabeling.partEquiv
          (holes (RepairSupplyIndex.root 0))) mask.1 (emptyLeg mask) = ∅) :
    VariableRepairCertificate (P := P) (target := target) holes := by
  let childTarget (mask : RecursiveRepairMask) :=
    splitBoxParts target
      (relabelParts relabeling.partEquiv
        (holes (RepairSupplyIndex.root 0))) mask.1
  let childPlan (mask : RecursiveRepairMask) : RepairPlan P (childTarget mask) :=
    RepairPlan.empty (childTarget mask) (emptyLeg mask) (hempty mask)
  let plan : RepairPlan P target := RepairPlan.node target
    (holes (RepairSupplyIndex.root 0)) relabeling childPlan
  have hcopyCount : plan.copyCount = 1 := by
    change 1 + ∑ mask, (childPlan mask).copyCount = 1
    have hchild (mask : RecursiveRepairMask) : (childPlan mask).copyCount = 0 := by
      rfl
    simp_rw [hchild]
    simp
  let pickEquiv : plan.Copy ≃ RepairSupplyIndex 0 :=
    Fintype.equivOfCardEq (by
      rw [RepairPlan.card_copy, hcopyCount]
      simp [RepairSupplyIndex])
  let pick : plan.Copy ↪ RepairSupplyIndex 0 := pickEquiv.toEmbedding
  refine
    { plan := plan
      pick := pick
      holesAt_eq := ?_
      height_le := ?_ }
  · intro occurrence
    have hpick : pick occurrence = RepairSupplyIndex.root 0 := by
      change pick occurrence = ()
      cases pick occurrence
      rfl
    rw [hpick]
    cases hbranch : RepairPlan.nodeCopyEquiv childPlan occurrence with
    | mk branch branchOccurrence =>
        cases branch with
        | none =>
            have hoccurrence : occurrence =
                (RepairPlan.nodeCopyEquiv childPlan).symm ⟨none, branchOccurrence⟩ := by
              apply (RepairPlan.nodeCopyEquiv childPlan).injective
              simpa [hbranch]
            subst occurrence
            cases branchOccurrence
            simpa [plan] using RepairPlan.holesAt_node_current childPlan
        | some mask =>
            have hzero : (childPlan mask).copyCount = 0 := by rfl
            exact Fin.elim0 (Fin.cast hzero branchOccurrence)
  · change RepairPlan.height plan ≤ 1
    rw [show plan = RepairPlan.node target
      (holes (RepairSupplyIndex.root 0)) relabeling childPlan by rfl,
      RepairPlan.height]
    have hchild (mask : RecursiveRepairMask) : (childPlan mask).height = 0 := by
      rfl
    simp_rw [hchild]
    simp

/-- Assemble one nonempty repair node above seven already supplied child certificates. -/
noncomputable def node
    {target : ∀ c, Finset (A c)} {d : ℕ}
    (holes : RepairSupplyIndex (d + 1) → ∀ c, Finset (A c))
    (relabeling : P.StructureRelabeling)
    (children : ∀ mask : RecursiveRepairMask,
      VariableRepairCertificate (P := P)
        (target := splitBoxParts target
          (relabelParts relabeling.partEquiv
            (holes (RepairSupplyIndex.root (d + 1)))) mask.1)
        (fun position ↦ holes (RepairSupplyIndex.child d mask position))) :
    VariableRepairCertificate (P := P) (target := target) holes := by
  let childPlan (mask : RecursiveRepairMask) := (children mask).plan
  let plan : RepairPlan P target := RepairPlan.node target
    (holes (RepairSupplyIndex.root (d + 1))) relabeling childPlan
  let branchPick :
      (Σ branch, RepairPlan.NodeBranchCopy childPlan branch) ↪
        RepairSupplyIndex (d + 1) :=
    { toFun := fun occurrence ↦
        match occurrence with
        | ⟨none, _current⟩ => RepairSupplyIndex.root (d + 1)
        | ⟨some mask, childOccurrence⟩ =>
            RepairSupplyIndex.child d mask ((children mask).pick childOccurrence)
      inj' := by
        rintro ⟨leftBranch, leftOccurrence⟩ ⟨rightBranch, rightOccurrence⟩ heq
        cases leftBranch with
        | none =>
            cases rightBranch with
            | none =>
                cases leftOccurrence
                cases rightOccurrence
                rfl
            | some rightMask =>
                simp [RepairSupplyIndex.root, RepairSupplyIndex.child] at heq
        | some leftMask =>
            cases rightBranch with
            | none =>
                simp [RepairSupplyIndex.root, RepairSupplyIndex.child] at heq
            | some rightMask =>
                change some (leftMask, (children leftMask).pick leftOccurrence) =
                  some (rightMask, (children rightMask).pick rightOccurrence) at heq
                have hpair := Option.some.inj heq
                have hmask : leftMask = rightMask := congrArg Prod.fst hpair
                subst rightMask
                have hoccurrence : leftOccurrence = rightOccurrence :=
                  (children leftMask).pick.injective (congrArg Prod.snd hpair)
                subst rightOccurrence
                rfl }
  let pick : plan.Copy ↪ RepairSupplyIndex (d + 1) :=
    (RepairPlan.nodeCopyEquiv childPlan).toEmbedding.trans branchPick
  refine
    { plan := plan
      pick := pick
      holesAt_eq := ?_
      height_le := ?_ }
  · intro occurrence
    change RepairPlan.holesAt plan occurrence = holes (pick occurrence)
    cases hbranch : RepairPlan.nodeCopyEquiv childPlan occurrence with
    | mk branch branchOccurrence =>
        cases branch with
        | none =>
            have hoccurrence : occurrence =
                (RepairPlan.nodeCopyEquiv childPlan).symm ⟨none, branchOccurrence⟩ := by
              apply (RepairPlan.nodeCopyEquiv childPlan).injective
              simpa [hbranch]
            subst occurrence
            cases branchOccurrence
            calc
              RepairPlan.holesAt plan
                  ((RepairPlan.nodeCopyEquiv childPlan).symm ⟨none, ()⟩) =
                  holes (RepairSupplyIndex.root (d + 1)) := by
                simpa [plan] using
                  (RepairPlan.holesAt_node_current childPlan)
              _ = holes
                  (pick ((RepairPlan.nodeCopyEquiv childPlan).symm ⟨none, ()⟩)) := by
                congr 1
                change RepairSupplyIndex.root (d + 1) =
                  branchPick (RepairPlan.nodeCopyEquiv childPlan
                    ((RepairPlan.nodeCopyEquiv childPlan).symm ⟨none, ()⟩))
                rw [Equiv.apply_symm_apply]
                rfl
        | some mask =>
            have hoccurrence : occurrence =
                (RepairPlan.nodeCopyEquiv childPlan).symm ⟨some mask, branchOccurrence⟩ := by
              apply (RepairPlan.nodeCopyEquiv childPlan).injective
              simpa [hbranch]
            subst occurrence
            calc
              RepairPlan.holesAt plan
                  ((RepairPlan.nodeCopyEquiv childPlan).symm
                    ⟨some mask, branchOccurrence⟩) =
                  RepairPlan.holesAt (childPlan mask) branchOccurrence := by
                simpa [plan] using
                  (RepairPlan.holesAt_node_child childPlan mask branchOccurrence)
              _ = holes (RepairSupplyIndex.child d mask
                    ((children mask).pick branchOccurrence)) := by
                simpa [childPlan] using
                  (children mask).holesAt_eq branchOccurrence
              _ = holes
                  (pick ((RepairPlan.nodeCopyEquiv childPlan).symm
                    ⟨some mask, branchOccurrence⟩)) := by
                congr 1
                change RepairSupplyIndex.child d mask
                    ((children mask).pick branchOccurrence) =
                  branchPick (RepairPlan.nodeCopyEquiv childPlan
                    ((RepairPlan.nodeCopyEquiv childPlan).symm
                      ⟨some mask, branchOccurrence⟩))
                rw [Equiv.apply_symm_apply]
                rfl
  · change RepairPlan.height plan ≤ d + 1 + 1
    rw [show plan = RepairPlan.node target
      (holes (RepairSupplyIndex.root (d + 1))) relabeling childPlan by rfl,
      RepairPlan.height]
    have hsup : Finset.univ.sup
        (fun mask : RecursiveRepairMask ↦ RepairPlan.height (childPlan mask)) ≤ d + 1 := by
      apply Finset.sup_le
      intro mask _hmask
      exact (children mask).height_le
    omega

end VariableRepairCertificate

/-- A complete finite supply of independently sparse broken copies constructs a repair plan using
distinct supplied copies, even when every copy has a different hole pattern.

The supply depth is the logarithmic repair depth.  Thus its cardinality is the exact complete
seven-branch budget `sevenBranchBudget d`, bounded above by `7^(d+1)`. -/
theorem exists_variableRepairCertificate
    {G : Type u} [Fintype G] [DecidableEq G] [Nonempty G]
    (family : UniformStructureRelabelings (G := G) P)
    {base : ℕ} (hbase : 1 < base)
    (d : ℕ) (holes : RepairSupplyIndex d → ∀ c, Finset (A c))
    (hsparse : ∀ position c,
      base * (4 * (holes position c).card) ≤ Fintype.card (A c))
    (target : ∀ c, Finset (A c))
    (hdepth : logarithmicRepairDepth base target ≤ d) :
    Nonempty (VariableRepairCertificate (P := P) (target := target) holes) := by
  induction d generalizing target with
  | zero =>
      by_cases hX : target .X = ∅
      · exact ⟨VariableRepairCertificate.empty holes .X hX⟩
      by_cases hY : target .Y = ∅
      · exact ⟨VariableRepairCertificate.empty holes .Y hY⟩
      by_cases hZ : target .Z = ∅
      · exact ⟨VariableRepairCertificate.empty holes .Z hZ⟩
      let rootHoles := holes (RepairSupplyIndex.root 0)
      obtain ⟨g, hshrink⟩ := family.exists_simultaneously_shrinking
        base target rootHoles (hsparse (RepairSupplyIndex.root 0))
      let relabeling := family.relabeling g
      let movedHoles : ∀ c, Finset (A c) :=
        relabelParts relabeling.partEquiv rootHoles
      have hshrinkMoved : ∀ c,
          base * (target c ∩ movedHoles c).card ≤ (target c).card := by
        intro c
        simpa [movedHoles, relabeling, rootHoles] using hshrink c
      have childEmpty (mask : RecursiveRepairMask) :
          ∃ c, splitBoxParts target movedHoles mask.1 c = ∅ := by
        by_contra hnoEmpty
        push Not at hnoEmpty
        have hnonempty : ∀ c, (splitBoxParts target movedHoles mask.1 c).Nonempty := by
          intro c
          exact hnoEmpty c
        have hdecrease := logarithmicRepairDepth_splitBoxParts_add_one_le
          hbase target movedHoles hshrinkMoved mask hnonempty
        omega
      choose emptyLeg hempty using childEmpty
      exact ⟨VariableRepairCertificate.root holes relabeling emptyLeg (by
        intro mask
        simpa [movedHoles, relabeling, rootHoles] using hempty mask)⟩
  | succ d ih =>
      by_cases hX : target .X = ∅
      · exact ⟨VariableRepairCertificate.empty holes .X hX⟩
      by_cases hY : target .Y = ∅
      · exact ⟨VariableRepairCertificate.empty holes .Y hY⟩
      by_cases hZ : target .Z = ∅
      · exact ⟨VariableRepairCertificate.empty holes .Z hZ⟩
      let rootHoles := holes (RepairSupplyIndex.root (d + 1))
      obtain ⟨g, hshrink⟩ := family.exists_simultaneously_shrinking
        base target rootHoles (hsparse (RepairSupplyIndex.root (d + 1)))
      let relabeling := family.relabeling g
      let movedHoles : ∀ c, Finset (A c) :=
        relabelParts relabeling.partEquiv rootHoles
      have hshrinkMoved : ∀ c,
          base * (target c ∩ movedHoles c).card ≤ (target c).card := by
        intro c
        simpa [movedHoles, relabeling, rootHoles] using hshrink c
      let childTarget (mask : RecursiveRepairMask) : ∀ c, Finset (A c) :=
        splitBoxParts target movedHoles mask.1
      let childHoles (mask : RecursiveRepairMask) :=
        fun position : RepairSupplyIndex d ↦
          holes (RepairSupplyIndex.child d mask position)
      have childCertificate (mask : RecursiveRepairMask) :
          Nonempty (VariableRepairCertificate (P := P)
            (target := childTarget mask) (childHoles mask)) := by
        by_cases hchildX : childTarget mask .X = ∅
        · exact ⟨VariableRepairCertificate.empty (childHoles mask) .X hchildX⟩
        by_cases hchildY : childTarget mask .Y = ∅
        · exact ⟨VariableRepairCertificate.empty (childHoles mask) .Y hchildY⟩
        by_cases hchildZ : childTarget mask .Z = ∅
        · exact ⟨VariableRepairCertificate.empty (childHoles mask) .Z hchildZ⟩
        have hchildNonempty : ∀ c, (childTarget mask c).Nonempty := by
          intro c
          fin_cases c
          · exact Finset.nonempty_iff_ne_empty.mpr hchildX
          · exact Finset.nonempty_iff_ne_empty.mpr hchildY
          · exact Finset.nonempty_iff_ne_empty.mpr hchildZ
        have hdecrease :
            logarithmicRepairDepth base (childTarget mask) + 1 ≤
              logarithmicRepairDepth base target := by
          exact logarithmicRepairDepth_splitBoxParts_add_one_le
            hbase target movedHoles hshrinkMoved mask hchildNonempty
        have hchildDepth : logarithmicRepairDepth base (childTarget mask) ≤ d := by
          omega
        apply ih (childHoles mask)
        · intro position c
          exact hsparse (RepairSupplyIndex.child d mask position) c
        · exact hchildDepth
      let children (mask : RecursiveRepairMask) := Classical.choice (childCertificate mask)
      exact ⟨VariableRepairCertificate.node holes relabeling (by
        intro mask
        simpa [childTarget, childHoles, movedHoles, relabeling, rootHoles] using
          children mask)⟩

end AlgebraicComplexity.HoleRepair
