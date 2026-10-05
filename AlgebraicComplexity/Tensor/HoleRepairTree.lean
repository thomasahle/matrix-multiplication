/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Tensor.HoleRepair
import AlgebraicComplexity.Tensor.IndexedSubfamily

/-!
# Full recursive tensor repair trees

This module packages the seven recursive subproblems of hole repair into one finite inductive
certificate.  Every internal node consumes one broken copy, chooses a structure-preserving
relabeling, and delegates the seven boxes other than the all-non-hole box to its children.  Empty
target boxes are leaves and consume no copy.

The main theorem, `RepairPlan.source_restricts`, states that the nested indexed direct sum of all
broken copies named by a plan restricts to its unbroken target box.  Thus the recursion is proved
at the tensor level rather than represented by a stage-shaped assumption.
-/

namespace AlgebraicComplexity.Tensor

open scoped DirectSum

universe u

variable {K : Type u} [CommSemiring K]
variable {A : Leg → Type u} [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]
variable {V : ∀ c, A c → Type u}
variable [∀ c a, AddCommMonoid (V c a)] [∀ c a, Module K (V c a)]

/-- A small bundle used when recursive branches have different semimodule types.  Unlike
Mathlib's `ModuleCat`, this works over semirings and only requires additive commutative monoids. -/
structure SemimoduleObject (K : Type u) [Semiring K] where
  carrier : Type u
  [addCommMonoid : AddCommMonoid carrier]
  [module : Module K carrier]

attribute [instance] SemimoduleObject.addCommMonoid SemimoduleObject.module

namespace SemimoduleObject

instance : CoeSort (SemimoduleObject K) (Type u) :=
  ⟨SemimoduleObject.carrier⟩

/-- Bundle an existing semimodule. -/
abbrev of (K : Type u) [Semiring K] (X : Type u)
    [AddCommMonoid X] [Module K X] : SemimoduleObject K :=
  ⟨X⟩

end SemimoduleObject

/-- A tensor together with bundled semimodule structures on its three leg spaces. -/
structure SemimoduleTensor (K : Type u) [CommSemiring K] where
  space : Leg → SemimoduleObject K
  tensor : Tensor3 K (fun c ↦ (space c).carrier)

/-- The seven masks whose box contains at least one hole coordinate. -/
abbrev RecursiveRepairMask :=
  {mask : Leg → Bool // mask ≠ allNonHoleMask}

/-- The current all-non-hole branch together with the seven recursive masks is exactly the set
of all eight Boolean masks. -/
noncomputable def repairBranchEquiv :
    Option RecursiveRepairMask ≃ (Leg → Bool) := by
  classical
  refine
    { toFun := fun branch ↦ match branch with
        | none => allNonHoleMask
        | some mask => mask.1
      invFun := fun mask ↦
        if h : mask = allNonHoleMask then none else some ⟨mask, h⟩
      left_inv := ?_
      right_inv := ?_ }
  · intro branch
    cases branch with
    | none => simp
    | some mask => simp [mask.property]
  · intro mask
    by_cases hmask : mask = allNonHoleMask
    · simp [hmask]
    · simp [hmask]

/-- A finite recursive certificate for repairing one target box.

At an internal node, `holes` describes the next broken copy before relabeling, `relabeling`
preserves the intact tensor, and `children` certifies the seven remaining hole boxes. -/
inductive RepairPlan (P : PartitionedTensor (K := K) (A := A) V) :
    (∀ c, Finset (A c)) → Type u
  | empty (target : ∀ c, Finset (A c)) (leg : Leg) (empty_leg : target leg = ∅) :
      RepairPlan P target
  | node (target holes : ∀ c, Finset (A c))
      (relabeling : P.StructureRelabeling)
      (children : ∀ mask : RecursiveRepairMask,
        RepairPlan P (splitBoxParts target
          (relabelParts relabeling.partEquiv holes) mask.1)) :
      RepairPlan P target

namespace RepairPlan

variable {P : PartitionedTensor (K := K) (A := A) V}

/-- Number of broken copies consumed by a repair plan. -/
def copyCount : {target : ∀ c, Finset (A c)} → RepairPlan P target → ℕ
  | _, .empty _ _ _ => 0
  | _, .node _ _ _ children => 1 + ∑ mask, copyCount (children mask)

/-- The canonical finite type indexing the broken copies consumed by a repair plan.  Using
`Fin copyCount` makes the counted interface exact and avoids any hidden enumeration choice. -/
abbrev Copy {target : ∀ c, Finset (A c)} (plan : RepairPlan P target) :=
  Fin plan.copyCount

/-- Copy indices belonging to one branch of a repair node: one current copy at `none`, and the
child plan's flat indices at `some mask`. -/
abbrev NodeBranchCopy
    {target holes : ∀ c, Finset (A c)} {relabeling : P.StructureRelabeling}
    (children : ∀ mask : RecursiveRepairMask,
      RepairPlan P (splitBoxParts target
        (relabelParts relabeling.partEquiv holes) mask.1)) :
    Option RecursiveRepairMask → Type
  | none => Unit
  | some mask => (children mask).Copy

/-- The canonical occurrence type has exactly `copyCount` elements. -/
@[simp] theorem card_copy {target : ∀ c, Finset (A c)} (plan : RepairPlan P target) :
    Fintype.card plan.Copy = plan.copyCount :=
  Fintype.card_fin _

/-- Canonical finite equivalence between the flat copy indices of a repair node and its current
copy followed by the flat indices of the seven child plans.  The equivalence need not expose a
particular enumeration; all semantic statements use it together with `holesAt`. -/
noncomputable def nodeCopyEquiv
    {target holes : ∀ c, Finset (A c)}
    {relabeling : P.StructureRelabeling}
    (children : ∀ mask : RecursiveRepairMask,
      RepairPlan P (splitBoxParts target
        (relabelParts relabeling.partEquiv holes) mask.1)) :
    (RepairPlan.node target holes relabeling children).Copy ≃
      (Σ branch, NodeBranchCopy children branch) := by
  classical
  letI : ∀ branch, Fintype (NodeBranchCopy children branch) := fun branch ↦
    match branch with
    | none => inferInstance
    | some _mask => inferInstance
  apply Fintype.equivOfCardEq
  rw [card_copy, Fintype.card_sigma, Fintype.sum_option, copyCount]
  simp only [NodeBranchCopy, Fintype.card_unique, card_copy]

/-- The missing-part pattern belonging to one flat occurrence in a repair plan.

At a node the distinguished current occurrence has the node's `holes`; all other occurrences
inherit the pattern stored at their recursive child node.  Empty plans have no occurrences. -/
noncomputable def holesAt :
    {target : ∀ c, Finset (A c)} → (plan : RepairPlan P target) →
      plan.Copy → (∀ c, Finset (A c))
  | _, .empty _target _leg _emptyLeg, occurrence => Fin.elim0 occurrence
  | _, .node target holes _relabeling children, occurrence =>
      match nodeCopyEquiv children occurrence with
      | ⟨none, _current⟩ => holes
      | ⟨some mask, childOccurrence⟩ => holesAt (children mask) childOccurrence

@[simp] theorem holesAt_node_current
    {target holes : ∀ c, Finset (A c)}
    {_relabeling : P.StructureRelabeling}
    (children : ∀ mask : RecursiveRepairMask,
      RepairPlan P (splitBoxParts target
        (relabelParts _relabeling.partEquiv holes) mask.1)) :
    holesAt (RepairPlan.node target holes _relabeling children)
        ((nodeCopyEquiv children).symm ⟨none, ()⟩) = holes := by
  simp [holesAt]

@[simp] theorem holesAt_node_child
    {target holes : ∀ c, Finset (A c)}
    {_relabeling : P.StructureRelabeling}
    (children : ∀ mask : RecursiveRepairMask,
      RepairPlan P (splitBoxParts target
        (relabelParts _relabeling.partEquiv holes) mask.1))
    (mask : RecursiveRepairMask) (occurrence : (children mask).Copy) :
    holesAt (RepairPlan.node target holes _relabeling children)
        ((nodeCopyEquiv children).symm ⟨some mask, occurrence⟩) =
      holesAt (children mask) occurrence := by
  simp [holesAt]

/-- Height of a finite repair plan.  Empty target boxes have height zero; a node has height one
more than the maximum height of its seven recursive subproblems. -/
def height : {target : ∀ c, Finset (A c)} → RepairPlan P target → ℕ
  | _, .empty _ _ _ => 0
  | _, .node _ _ _ children =>
      1 + Finset.univ.sup
        (fun mask : RecursiveRepairMask ↦ height (children mask))

/-- There are exactly seven recursive masks: all Boolean triples except the all-non-hole mask. -/
theorem card_recursiveRepairMask : Fintype.card RecursiveRepairMask = 7 := by
  have h := Fintype.card_congr repairBranchEquiv
  have hcard : Fintype.card RecursiveRepairMask + 1 = 8 := by
    calc
      Fintype.card RecursiveRepairMask + 1 =
          Fintype.card (Option RecursiveRepairMask) := Fintype.card_option.symm
      _ = Fintype.card (Leg → Bool) := h
      _ = 8 := by
        rw [Fintype.card_fun, Fintype.card_bool,
          show Fintype.card Leg = 3 by rfl]
        norm_num
  omega

/-- Exact node budget for a complete seven-ary repair tree of a given height. -/
def repairTreeBudget : ℕ → ℕ
  | 0 => 0
  | d + 1 => 1 + 7 * repairTreeBudget d

/-- The complete seven-ary tree budget is monotone in its height. -/
theorem repairTreeBudget_monotone : Monotone repairTreeBudget := by
  apply monotone_nat_of_le_succ
  intro d
  rw [repairTreeBudget]
  omega

/-- Division-free closed form for the complete seven-ary tree budget. -/
theorem six_mul_repairTreeBudget_add_one (d : ℕ) :
    6 * repairTreeBudget d + 1 = 7 ^ d := by
  induction d with
  | zero => rfl
  | succ d ih =>
      rw [repairTreeBudget, pow_succ]
      omega

/-- Coarse power bound used by the asymptotic hole-repair argument. -/
theorem repairTreeBudget_le_pow (d : ℕ) :
    repairTreeBudget d ≤ 7 ^ d := by
  have h := six_mul_repairTreeBudget_add_one d
  omega

/-- The number of broken copies actually named by a repair plan is bounded by the complete
seven-ary tree of the same height. -/
theorem copyCount_le_repairTreeBudget_height :
    {target : ∀ c, Finset (A c)} → (plan : RepairPlan P target) →
      copyCount plan ≤ repairTreeBudget (height plan)
  | _, .empty _ _ _ => by simp [copyCount, height]
  | _, .node _target _holes _relabeling children => by
      rw [copyCount, height]
      let d := Finset.univ.sup
        (fun mask : RecursiveRepairMask ↦ height (children mask))
      have hchild (mask : RecursiveRepairMask) :
          copyCount (children mask) ≤ repairTreeBudget d := by
        exact (copyCount_le_repairTreeBudget_height (children mask)).trans
          (repairTreeBudget_monotone
            (Finset.le_sup
              (f := fun m : RecursiveRepairMask ↦ height (children m))
              (Finset.mem_univ mask)))
      calc
        1 + ∑ mask, copyCount (children mask) ≤
            1 + ∑ _mask : RecursiveRepairMask, repairTreeBudget d := by
          gcongr with mask
          exact hchild mask
        _ = 1 + 7 * repairTreeBudget d := by
          rw [Finset.sum_const, Finset.card_univ, card_recursiveRepairMask]
          simp
        _ = repairTreeBudget (1 + d) := by
          rw [show 1 + d = d + 1 by omega]
          rfl

/-- Paper-facing form: a height-`d` repair plan consumes at most `7^d` broken copies. -/
theorem copyCount_le_pow_height
    {target : ∀ c, Finset (A c)} (plan : RepairPlan P target) :
    copyCount plan ≤ 7 ^ height plan :=
  (copyCount_le_repairTreeBudget_height plan).trans
    (repairTreeBudget_le_pow (height plan))

/-- A box with an empty part set on one leg realizes to the zero tensor. -/
theorem box_realize_eq_zero_of_empty_leg
    (P : PartitionedTensor (K := K) (A := A) V)
    (target : ∀ c, Finset (A c)) (leg : Leg) (hempty : target leg = ∅) :
    (P.box target).realize = 0 := by
  classical
  have hsupport : (P.box target).support = ∅ := by
    ext address
    simp only [Finset.notMem_empty, iff_false]
    intro haddress
    have hleg := (P.mem_box_support target address).1 haddress |>.2 leg
    simp [hempty] at hleg
  unfold PartitionedTensor.realize realizePartition
  rw [hsupport]
  simp

/-- The result of compiling a repair plan: a source tensor together with its semantic proof.

Bundling the proof with the source is important here because different recursive branches have
different source spaces.  It prevents later unfolding from having to transport a restriction
proof across dependent equalities between those spaces. -/
structure Result (P : PartitionedTensor (K := K) (A := A) V)
    (target : ∀ c, Finset (A c)) where
  source : SemimoduleTensor K
  valid : Restricts source.tensor (P.box target).realize

/-- Compile a finite repair plan to the nested indexed direct sum of its broken copies, proving
the restriction invariant at every recursive node. -/
noncomputable def result :
    {target : ∀ c, Finset (A c)} →
      (plan : RepairPlan P target) → Result P target
  | _, .empty target leg hempty =>
      { source :=
          { space := fun c ↦ SemimoduleObject.of K (PartitionedSpace K V c)
            tensor := 0 }
        valid := Restricts.of_eq
          (box_realize_eq_zero_of_empty_leg P target leg hempty).symm }
  | _, .node target holes relabeling children => by
      let branchObject : Option RecursiveRepairMask → SemimoduleTensor K
        | none =>
            { space := fun c ↦ SemimoduleObject.of K (PartitionedSpace K V c)
              tensor := (P.box (fun c ↦ Finset.univ \ holes c)).realize }
        | some mask => (result (children mask)).source
      let source : SemimoduleTensor K :=
        { space := fun c ↦ SemimoduleObject.of K
            (⨁ branch : Option RecursiveRepairMask,
              ((branchObject branch).space c).carrier)
          tensor := by
            change Tensor3 K
              (IndexedDirectSumSpace K (fun branch : Option RecursiveRepairMask ↦
                fun c ↦ ((branchObject branch).space c).carrier))
            exact Tensor.indexedDirectSum
              (V := fun branch : Option RecursiveRepairMask ↦
                fun c ↦ ((branchObject branch).space c).carrier)
              (fun branch ↦ (branchObject branch).tensor) }
      refine { source := source, valid := ?_ }
      change Restricts
        (Tensor.indexedDirectSum (V := fun branch : Option RecursiveRepairMask ↦
          fun c ↦ ((branchObject branch).space c).carrier)
          (fun branch ↦ (branchObject branch).tensor))
        (P.box target).realize
      let movedHoles : ∀ c, Finset (A c) :=
        relabelParts relabeling.partEquiv holes
      apply Restricts.indexedDirectSum_splitBoxes_to_box_equiv
        repairBranchEquiv P target movedHoles
        (fun branch ↦ (branchObject branch).tensor)
      intro branch
      cases branch with
      | none =>
          simpa [branchObject, repairBranchEquiv, movedHoles] using
            Restricts.brokenBox_to_allNonHole_splitBox
              P relabeling target holes
      | some mask =>
          simpa [branchObject, repairBranchEquiv, movedHoles] using
            (result (children mask)).valid

/-- The nested indexed direct sum of all broken copies in a plan. -/
noncomputable abbrev sourceObject
    {target : ∀ c, Finset (A c)} (plan : RepairPlan P target) :
    SemimoduleTensor K :=
  plan.result.source

/-- Underlying leg space of `sourceObject`. -/
abbrev SourceSpace {target : ∀ c, Finset (A c)} (plan : RepairPlan P target)
    (c : Leg) : Type _ :=
  (plan.sourceObject.space c).carrier

/-- The nested indexed direct sum of all broken tensors consumed by a repair plan. -/
noncomputable abbrev sourceTensor
    {target : ∀ c, Finset (A c)} (plan : RepairPlan P target) :
    Tensor3 K plan.SourceSpace :=
  plan.sourceObject.tensor

/-- The full recursive hole-repair theorem for a supplied finite plan. -/
theorem source_restricts
    {target : ∀ c, Finset (A c)} (plan : RepairPlan P target) :
    Restricts plan.sourceTensor (P.box target).realize :=
  plan.result.valid

/-! ## Flat copy families -/

/-- The flat indexed direct sum of the genuinely broken tensor occurrences named by a repair
plan.  The occurrence `i` supplies exactly the box obtained by deleting `plan.holesAt i` from
the intact partitioned tensor `P`.

This is distinct from `flatCopies` below: `flatCopies` contains intact copies of `P`, whereas
`flatBrokenCopies` is the interface needed for compatibility cleanup, whose output fibers may
have different missing-part patterns. -/
noncomputable def flatBrokenCopies
    {target : ∀ c, Finset (A c)} (plan : RepairPlan P target) :
    Tensor3 K (IndexedDirectSumSpace K
      (fun _ : plan.Copy ↦ fun c ↦ PartitionedSpace K V c)) :=
  Tensor.indexedDirectSum (fun occurrence : plan.Copy ↦
    (P.box (fun c ↦ Finset.univ \ plan.holesAt occurrence c)).realize)

/-- A flat family containing exactly the varying broken occurrences of a repair plan restricts
to the intact target box.

The proof reorganizes the flat occurrence index into the current node and its seven dependent
child families, recursively repairs the children, and applies the exact eight-box identity.
Thus no assumption of identical hole patterns is made. -/
theorem flatBrokenCopies_restricts :
    {target : ∀ c, Finset (A c)} → (plan : RepairPlan P target) →
      Restricts plan.flatBrokenCopies (P.box target).realize
  | _, .empty target leg hempty => by
      rw [box_realize_eq_zero_of_empty_leg P target leg hempty]
      exact ⟨fun _ ↦ 0, map_eq_zero_of_coord _ _ Leg.X rfl⟩
  | _, .node target holes relabeling children => by
      classical
      letI : ∀ branch, Fintype (NodeBranchCopy children branch) := fun branch ↦
        match branch with
        | none => inferInstance
        | some _mask => inferInstance
      let occurrenceTensor (ij : Σ branch, NodeBranchCopy children branch) :
          Tensor3 K (fun c ↦ PartitionedSpace K V c) :=
        match ij with
        | ⟨none, _current⟩ =>
            (P.box (fun c ↦ Finset.univ \ holes c)).realize
        | ⟨some mask, childOccurrence⟩ =>
            (P.box (fun c ↦ Finset.univ \
              (children mask).holesAt childOccurrence c)).realize
      let branchTensor (branch : Option RecursiveRepairMask) :
          Tensor3 K (IndexedDirectSumSpace K
            (fun _ : NodeBranchCopy children branch ↦
              fun c ↦ PartitionedSpace K V c)) :=
        Tensor.indexedDirectSum
          (fun occurrence : NodeBranchCopy children branch ↦
            occurrenceTensor ⟨branch, occurrence⟩)
      have hreindex : Restricts
          (flatBrokenCopies (RepairPlan.node target holes relabeling children))
          (Tensor.indexedDirectSum occurrenceTensor) := by
        apply Restricts.indexedDirectSum_equiv (nodeCopyEquiv children)
        intro occurrence
        exact Restricts.of_eq (by
          change
            (P.box (fun c ↦ Finset.univ \
              holesAt (RepairPlan.node target holes relabeling children) occurrence c)).realize =
                occurrenceTensor ((nodeCopyEquiv children) occurrence)
          cases hbranch : nodeCopyEquiv children occurrence with
          | mk branch branchOccurrence =>
              cases branch <;>
                simp [holesAt, occurrenceTensor, hbranch])
      have hcurry : Restricts
          (Tensor.indexedDirectSum occurrenceTensor)
          (Tensor.indexedDirectSum branchTensor) := by
        have h := Restricts.indexedDirectSum_sigma
          (K := K)
          (ι := Option RecursiveRepairMask)
          (J := fun branch ↦ NodeBranchCopy children branch)
          (S := fun _branch _occurrence c ↦ PartitionedSpace K V c)
          occurrenceTensor
        simpa only [branchTensor] using h
      apply (hreindex.trans hcurry).trans
      let movedHoles : ∀ c, Finset (A c) :=
        relabelParts relabeling.partEquiv holes
      apply Restricts.indexedDirectSum_splitBoxes_to_box_equiv
        repairBranchEquiv P target movedHoles branchTensor
      intro branch
      cases branch with
      | none =>
          have hsingle : Restricts (branchTensor none)
              (P.box (fun c ↦ Finset.univ \ holes c)).realize := by
            have hsum := Restricts.indexedDirectSum_to_sum
              (K := K)
              (V := fun _ : Unit ↦ fun c ↦ PartitionedSpace K V c)
              (T := fun _ : Unit ↦
                (P.box (fun c ↦ Finset.univ \ holes c)).realize)
              (S := fun _ : Unit ↦
                (P.box (fun c ↦ Finset.univ \ holes c)).realize)
              (fun _ ↦ Restricts.refl _)
            simpa [branchTensor, occurrenceTensor, NodeBranchCopy] using hsum
          exact hsingle.trans (by
            simpa [movedHoles, repairBranchEquiv] using
              Restricts.brokenBox_to_allNonHole_splitBox
                P relabeling target holes)
      | some mask =>
          have hchild := flatBrokenCopies_restricts (children mask)
          simpa [flatBrokenCopies, branchTensor, occurrenceTensor,
            NodeBranchCopy, movedHoles, repairBranchEquiv] using hchild

/-- Select from an ambient indexed family the varying broken occurrences named by a repair plan
and repair them into one intact target box.

The embedding `pick` is the entire bookkeeping obligation: distinct repair occurrences must be
supplied by distinct ambient fibers.  Each selected fiber may merely restrict to its occurrence's
own damaged box; neither identical hole patterns nor intact source copies are assumed. -/
theorem indexedDirectSum_repairPlan
    {target : ∀ c, Finset (A c)} (plan : RepairPlan P target)
    {I : Type*} [Fintype I] [DecidableEq I]
    {U : Leg → Type*}
    [∀ c, AddCommMonoid (U c)] [∀ c, Module K (U c)]
    (family : I → Tensor3 K U) (pick : plan.Copy ↪ I)
    (hbroken : ∀ occurrence,
      Restricts (family (pick occurrence))
        (P.box (fun c ↦ Finset.univ \ plan.holesAt occurrence c)).realize) :
    Restricts (Tensor.indexedDirectSum family) (P.box target).realize := by
  classical
  let selected : Finset I := Finset.univ.map pick
  let intoSelected : plan.Copy → selected := fun occurrence ↦
    ⟨pick occurrence, by
      exact Finset.mem_map.mpr
        ⟨occurrence, Finset.mem_univ occurrence, rfl⟩⟩
  have hIntoSelectedInjective : Function.Injective intoSelected := by
    intro left right heq
    apply pick.injective
    exact congrArg Subtype.val heq
  have hIntoSelectedSurjective : Function.Surjective intoSelected := by
    intro chosen
    have hmem : chosen.1 ∈ Finset.univ.map pick := chosen.2
    obtain ⟨occurrence, _hoccurrence, hvalue⟩ := Finset.mem_map.mp hmem
    refine ⟨occurrence, Subtype.ext ?_⟩
    exact hvalue
  let selectedEquiv : selected ≃ plan.Copy :=
    (Equiv.ofBijective intoSelected
      ⟨hIntoSelectedInjective, hIntoSelectedSurjective⟩).symm
  have hselect : Restricts (Tensor.indexedDirectSum family)
      (Tensor.indexedDirectSum
        (V := IndexedSubfamily (V := fun _ : I ↦ U) selected)
        (fun chosen : selected ↦ family chosen.1)) :=
    Restricts.indexedDirectSum_subfamily family selected
  have hreindex : Restricts
      (Tensor.indexedDirectSum
        (V := IndexedSubfamily (V := fun _ : I ↦ U) selected)
        (fun chosen : selected ↦ family chosen.1))
      plan.flatBrokenCopies := by
    apply Restricts.indexedDirectSum_equiv selectedEquiv
    intro chosen
    have hinverse : intoSelected (selectedEquiv chosen) = chosen := by
      exact (Equiv.ofBijective intoSelected
        ⟨hIntoSelectedInjective, hIntoSelectedSurjective⟩).apply_symm_apply chosen
    have hvalue : pick (selectedEquiv chosen) = chosen.1 :=
      congrArg Subtype.val hinverse
    simpa only [flatBrokenCopies, hvalue] using hbroken (selectedEquiv chosen)
  exact hselect.trans (hreindex.trans plan.flatBrokenCopies_restricts)

/-- Simultaneously repair a finite family of target copies from disjoint occurrences in one
ambient indexed tensor family.

Each output may use its own repair plan and hence its own collection of hole patterns.  The
single embedding from the dependent sum of occurrences guarantees that no cleaned source fiber
is reused by two outputs.  This is the finite counted interface used before converting the
repaired targets to a matrix-multiplication direct sum. -/
theorem indexedDirectSum_repairPlans
    {target : ∀ c, Finset (A c)}
    {O : Type*} [Fintype O] [DecidableEq O]
    (plans : O → RepairPlan P target)
    {I : Type*} [Fintype I] [DecidableEq I]
    {U : Leg → Type*}
    [∀ c, AddCommMonoid (U c)] [∀ c, Module K (U c)]
    (family : I → Tensor3 K U)
    (pick : (Σ output, (plans output).Copy) ↪ I)
    (hbroken : ∀ occurrence : Σ output, (plans output).Copy,
      Restricts (family (pick occurrence))
        (P.box (fun c ↦ Finset.univ \
          (plans occurrence.1).holesAt occurrence.2 c)).realize) :
    Restricts (Tensor.indexedDirectSum family)
      (Tensor.indexedDirectSum (fun _output : O ↦ (P.box target).realize)) := by
  classical
  let Occurrence := Σ output, (plans output).Copy
  let selected : Finset I := Finset.univ.map pick
  let intoSelected : Occurrence → selected := fun occurrence ↦
    ⟨pick occurrence, by
      exact Finset.mem_map.mpr
        ⟨occurrence, Finset.mem_univ occurrence, rfl⟩⟩
  have hIntoSelectedInjective : Function.Injective intoSelected := by
    intro left right heq
    apply pick.injective
    exact congrArg Subtype.val heq
  have hIntoSelectedSurjective : Function.Surjective intoSelected := by
    intro chosen
    have hmem : chosen.1 ∈ Finset.univ.map pick := chosen.2
    obtain ⟨occurrence, _hoccurrence, hvalue⟩ := Finset.mem_map.mp hmem
    refine ⟨occurrence, Subtype.ext ?_⟩
    exact hvalue
  let selectedEquiv : selected ≃ Occurrence :=
    (Equiv.ofBijective intoSelected
      ⟨hIntoSelectedInjective, hIntoSelectedSurjective⟩).symm
  let occurrenceTensor (occurrence : Occurrence) :
      Tensor3 K (fun c ↦ PartitionedSpace K V c) :=
    (P.box (fun c ↦ Finset.univ \
      (plans occurrence.1).holesAt occurrence.2 c)).realize
  have hselect : Restricts (Tensor.indexedDirectSum family)
      (Tensor.indexedDirectSum
        (V := IndexedSubfamily (V := fun _ : I ↦ U) selected)
        (fun chosen : selected ↦ family chosen.1)) :=
    Restricts.indexedDirectSum_subfamily family selected
  have hreindex : Restricts
      (Tensor.indexedDirectSum
        (V := IndexedSubfamily (V := fun _ : I ↦ U) selected)
        (fun chosen : selected ↦ family chosen.1))
      (Tensor.indexedDirectSum occurrenceTensor) := by
    apply Restricts.indexedDirectSum_equiv selectedEquiv
    intro chosen
    have hinverse : intoSelected (selectedEquiv chosen) = chosen := by
      exact (Equiv.ofBijective intoSelected
        ⟨hIntoSelectedInjective, hIntoSelectedSurjective⟩).apply_symm_apply chosen
    have hvalue : pick (selectedEquiv chosen) = chosen.1 :=
      congrArg Subtype.val hinverse
    simpa only [occurrenceTensor, hvalue] using hbroken (selectedEquiv chosen)
  have hcurry : Restricts (Tensor.indexedDirectSum occurrenceTensor)
      (Tensor.indexedDirectSum (fun output ↦ (plans output).flatBrokenCopies)) := by
    have h := Restricts.indexedDirectSum_sigma
      (K := K)
      (ι := O)
      (J := fun output ↦ (plans output).Copy)
      (S := fun _output _occurrence c ↦ PartitionedSpace K V c)
      occurrenceTensor
    simpa only [Occurrence, occurrenceTensor, flatBrokenCopies] using h
  have hrepair : Restricts
      (Tensor.indexedDirectSum (fun output ↦ (plans output).flatBrokenCopies))
      (Tensor.indexedDirectSum (fun _output : O ↦ (P.box target).realize)) :=
    Restricts.indexedDirectSum (fun output ↦ (plans output).flatBrokenCopies_restricts)
  exact hselect.trans (hreindex.trans (hcurry.trans hrepair))

/-- The ordinary indexed direct sum containing one full copy of `P.realize` for every copy
occurrence in a repair plan. -/
noncomputable def flatCopies
    {target : ∀ c, Finset (A c)} (plan : RepairPlan P target) :
    Tensor3 K (IndexedDirectSumSpace K
      (fun _ : plan.Copy ↦ fun c ↦ PartitionedSpace K V c)) :=
  Tensor.indexedDirectSum (fun _ : plan.Copy ↦ P.realize)

/-- A flat direct sum of the full tensor copies named by a repair plan restricts to the repaired
target box.

This is the counted semantic form of recursive hole repair.  The proof first curries the flat
dependent sum into the current copy and the seven recursive families, then uses exact box
zeroing on the current copy, the induction hypotheses on the children, and the eight-way box
assembly theorem. -/
theorem flatCopies_restricts :
    {target : ∀ c, Finset (A c)} → (plan : RepairPlan P target) →
      Restricts plan.flatCopies (P.box target).realize
  | _, .empty target leg hempty => by
      rw [box_realize_eq_zero_of_empty_leg P target leg hempty]
      exact ⟨fun _ ↦ 0, map_eq_zero_of_coord _ _ Leg.X rfl⟩
  | _, .node target holes relabeling children => by
      classical
      letI : ∀ branch, Fintype (NodeBranchCopy children branch) := fun branch ↦
        match branch with
        | none => inferInstance
        | some _mask => inferInstance
      let branchTensor (branch : Option RecursiveRepairMask) :
          Tensor3 K (IndexedDirectSumSpace K
            (fun _ : NodeBranchCopy children branch ↦
              fun c ↦ PartitionedSpace K V c)) :=
        Tensor.indexedDirectSum
          (fun _ : NodeBranchCopy children branch ↦ P.realize)
      have hbranchCard :
          Fintype.card (Σ branch, NodeBranchCopy children branch) =
            (RepairPlan.node target holes relabeling children).copyCount := by
        rw [Fintype.card_sigma, Fintype.sum_option, copyCount]
        simp only [NodeBranchCopy, Fintype.card_unique, card_copy]
      let branchEquiv :
          (RepairPlan.node target holes relabeling children).Copy ≃
            (Σ branch, NodeBranchCopy children branch) :=
        Fintype.equivOfCardEq (by simpa using hbranchCard.symm)
      have hflatten : Restricts
          (flatCopies (RepairPlan.node target holes relabeling children))
          (Tensor.indexedDirectSum branchTensor) := by
        have hreindex := Restricts.indexedDirectSum_const_equiv
          (K := K) branchEquiv P.realize
        have hcurry := Restricts.indexedDirectSum_sigma
          (K := K)
          (S := fun branch (_copy : NodeBranchCopy children branch) c ↦
            PartitionedSpace K V c)
          (fun _ij ↦ P.realize)
        have hreindex' : Restricts
            (flatCopies (RepairPlan.node target holes relabeling children))
            (Tensor.indexedDirectSum
              (fun _ : Σ branch, NodeBranchCopy children branch ↦ P.realize)) := by
          simpa only [flatCopies] using hreindex
        have hcurry' : Restricts
            (Tensor.indexedDirectSum
              (fun _ : Σ branch, NodeBranchCopy children branch ↦ P.realize))
            (Tensor.indexedDirectSum branchTensor) := by
          simpa only [branchTensor] using hcurry
        exact hreindex'.trans hcurry'
      apply hflatten.trans
      let movedHoles : ∀ c, Finset (A c) :=
        relabelParts relabeling.partEquiv holes
      apply Restricts.indexedDirectSum_splitBoxes_to_box_equiv
        repairBranchEquiv P target movedHoles branchTensor
      intro branch
      cases branch with
      | none =>
          have hsingle : Restricts (branchTensor none) P.realize := by
            have hsum := Restricts.indexedDirectSum_to_sum
              (K := K) (V := fun _ : Unit ↦ fun c ↦ PartitionedSpace K V c)
              (T := fun _ : Unit ↦ P.realize)
              (S := fun _ : Unit ↦ P.realize)
              (fun _ ↦ Restricts.refl P.realize)
            simpa [branchTensor, NodeBranchCopy] using hsum
          exact hsingle.trans
            ((Restricts.partitionedBox P (fun c ↦ Finset.univ \ holes c)).trans
              (by
                simpa [movedHoles, repairBranchEquiv] using
                  Restricts.brokenBox_to_allNonHole_splitBox
                    P relabeling target holes))
      | some mask =>
          have hchild := flatCopies_restricts (children mask)
          unfold flatCopies at hchild
          simpa [branchTensor, NodeBranchCopy, movedHoles, repairBranchEquiv] using hchild

/-- Padding form of flat hole repair: any family containing at least `copyCount` full copies
restricts to the repaired target box. -/
theorem flatCopies_restricts_of_copyCount_le
    {target : ∀ c, Finset (A c)} (plan : RepairPlan P target)
    {N : ℕ} (hcount : plan.copyCount ≤ N) :
    Restricts
      (Tensor.indexedDirectSum (V := fun _ : Fin N ↦ fun c ↦ PartitionedSpace K V c)
        (fun _ ↦ P.realize))
      (P.box target).realize := by
  classical
  let embedding : Fin plan.copyCount ↪ Fin N := Fin.castLEEmb hcount
  let selected : Finset (Fin N) := Finset.univ.map embedding
  have hselectedCard : Fintype.card selected = plan.copyCount := by
    rw [Fintype.card_coe]
    dsimp [selected]
    rw [Finset.card_map, Finset.card_univ, Fintype.card_fin]
  let selectedEquiv : selected ≃ Fin plan.copyCount :=
    Fintype.equivOfCardEq (by simpa using hselectedCard)
  have hselect := Restricts.indexedDirectSum_subfamily
    (K := K)
    (V := fun _ : Fin N ↦ fun c ↦ PartitionedSpace K V c)
    (fun _ : Fin N ↦ P.realize) selected
  have hreindex := Restricts.indexedDirectSum_const_equiv
    (K := K) selectedEquiv P.realize
  have hflat : Restricts
      (Tensor.indexedDirectSum
        (V := fun _ : Fin plan.copyCount ↦ fun c ↦ PartitionedSpace K V c)
        (fun _ ↦ P.realize))
      (P.box target).realize := by
    simpa only [flatCopies] using plan.flatCopies_restricts
  exact hselect.trans (hreindex.trans hflat)

end RepairPlan

end AlgebraicComplexity.Tensor
