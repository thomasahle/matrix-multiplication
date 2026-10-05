/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Combinatorics.ConditionalWordTypeCore
import AlgebraicComplexity.Examples.CoppersmithWinogradChunkSplitWordEquivCore
import AlgebraicComplexity.Examples.CoppersmithWinogradOrientedFiniteCellCore
import AlgebraicComplexity.Examples.CoppersmithWinogradRecursiveChildWordCore
import AlgebraicComplexity.Examples.CoppersmithWinogradRecursiveTargetFiberCore
import AlgebraicComplexity.MatrixMultiplication.CompatibilityTargetCore
import AlgebraicComplexity.MatrixMultiplication.RecursiveChildCompatibilityInjectiveCore
import Lean.Elab.Tactic.Omega

set_option autoImplicit false

/-!
# Recursive CW exact targets as conditional type classes

A native recursive Coppersmith--Winograd parent label is equivalent to the word of its two
labelled complete-split children.  After bounding the tagged coarse cells, this equivalence
identifies one exact recursive target alphabet with a finite conditional type class.

This is the finite fixed-cell step used in the proof of Claim 6.18 of [alman2025more],
`papers/sources/2404.16349/constituent.tex:376-440`, especially lines 404--429.  It also supplies
the exact target interface for the Total-Weight segmented family
`better_bound/paper.tex:1658-1694,1720-1744,1771-1802`.  Occurrence-derived support and the final
product-of-multinomials count remain in `CoppersmithWinogradRecursiveTargetCounting`; no hashing,
tensor restriction, asymptotic estimate, or certificate arithmetic occurs here.

## References

- [alman2025more] Josh Alman, Ran Duan, Virginia Vassilevska Williams, Yinzhan Xu, Zixuan Xu,
  and Renfei Zhou, *More Asymmetry Yields Faster Matrix Multiplication*.
- *Total-Weight Hashing and Rectangular Volume in the Coppersmith--Winograd Method*.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor MoreAsymmetryCompatibility

universe v

/-! ## Every labelled child word has a unique native parent label -/

/-- Splitting every native parent chunk into its two labelled children is surjective onto the
full doubled child-word alphabet.  The inverse joins the two child words at each parent position
and then applies the inverse native ternary encoding. -/
theorem cwRecursiveLabelledChildren_surjective (depth n : ℕ) :
    Function.Surjective
      (positiveWordLabelledChildren (n := n) (cwChunkSplitWord (depth + 1))) := by
  intro children
  let pairAt : Fin (n + 1) → SplitWord depth × SplitWord depth := fun sample ↦
    (children (Fin.castAdd (n + 1) sample),
      children (Fin.natAdd (n + 1) sample))
  let parentAt : Fin (n + 1) →
      PositiveWord CWBlock (2 ^ (depth + 1) - 1) := fun sample ↦
    (cwChunkSplitWordEquiv (depth + 1)).symm
      ((splitWordSuccEquiv depth).symm (pairAt sample))
  let parent : PositiveWord
      (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n :=
    (positiveWordEquiv _ n).symm parentAt
  refine ⟨parent, ?_⟩
  funext occurrence
  refine Fin.addCases ?_ ?_ occurrence <;> intro sample
  · rw [positiveWordLabelledChildren_left,
      leftChildHalf_eq_splitWordSuccEquiv]
    have hparent :
        cwChunkSplitWord (depth + 1)
            (positiveWordEquiv _ n parent sample) =
          (splitWordSuccEquiv depth).symm (pairAt sample) := by
      change cwChunkSplitWordEquiv (depth + 1)
          (positiveWordEquiv _ n parent sample) = _
      rw [show positiveWordEquiv _ n parent = parentAt by
        simp [parent]]
      exact (cwChunkSplitWordEquiv (depth + 1)).apply_symm_apply _
    rw [hparent, (splitWordSuccEquiv depth).apply_symm_apply]
  · rw [positiveWordLabelledChildren_right,
      rightChildHalf_eq_splitWordSuccEquiv]
    have hparent :
        cwChunkSplitWord (depth + 1)
            (positiveWordEquiv _ n parent sample) =
          (splitWordSuccEquiv depth).symm (pairAt sample) := by
      change cwChunkSplitWordEquiv (depth + 1)
          (positiveWordEquiv _ n parent sample) = _
      rw [show positiveWordEquiv _ n parent = parentAt by
        simp [parent]]
      exact (cwChunkSplitWordEquiv (depth + 1)).apply_symm_apply _
    rw [hparent, (splitWordSuccEquiv depth).apply_symm_apply]

/-- Native parent labels are equivalent to arbitrary words of their two labelled child chunks. -/
noncomputable def cwRecursiveLabelledChildrenEquiv (depth n : ℕ) :
    PositiveWord (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n ≃
      (Fin ((n + 1) + (n + 1)) → SplitWord depth) :=
  Equiv.ofBijective
    (positiveWordLabelledChildren (n := n) (cwChunkSplitWord (depth + 1)))
    ⟨positiveWordLabelledChildren_injective
      (cwChunkSplitWord (depth + 1)) (cwChunkSplitWord_injective (depth + 1)),
      cwRecursiveLabelledChildren_surjective depth n⟩

/-- The labelled-children equivalence acts by literally taking a parent's two labelled complete
split children, in that order. -/
@[simp] theorem cwRecursiveLabelledChildrenEquiv_apply
    (depth n : ℕ)
    (parent : PositiveWord
      (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n) :
    cwRecursiveLabelledChildrenEquiv depth n parent =
      positiveWordLabelledChildren
        (cwChunkSplitWord (depth + 1)) parent :=
  rfl

/-- The bounded recursive quotient digit is the weight of the corresponding labelled child
split word. -/
theorem val_cwRecursiveLabelledChildWord_eq_splitWordWeight
    (depth n : ℕ)
    (parent : PositiveWord
      (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n)
    (occurrence : Fin ((n + 1) + (n + 1))) :
    (cwRecursiveLabelledChildWord depth n parent occurrence : ℕ) =
      splitWordWeight
        (positiveWordLabelledChildren
          (cwChunkSplitWord (depth + 1)) parent occurrence) := by
  refine Fin.addCases ?_ ?_ occurrence <;> intro sample
  · simp [cwRecursiveLabelledChildWord, cwRecursiveLeftChildDigit,
      positiveWordLabelledChildren_left]
  · rw [cwRecursiveLabelledChildWord, Fin.append_right,
      positiveWordLabelledChildren_right]

/-! ## Exact target alphabets are conditional type classes -/

/-- Read a recursive doubled quotient word in the finite tagged/oriented cell alphabet.  The
natural-valued `CoarseIndex` used by compatibility is deliberately not a finite type; all
method-of-types statements must pass through this bounded representation. -/
def cwRecursiveOrientedFiniteCellSequence
    {Part : Type v} (depth n : ℕ)
    (partAt : Fin (n + 1) → Part) (sigma : Orientation)
    (coarse : CWRecursiveCoarseAddress depth n) :
    Fin ((n + 1) + (n + 1)) → CWOrientedCoarseCell Part depth :=
  fun occurrence ↦
    (labelledChildParts partAt occurrence,
      fun logicalLeg ↦ coarse (sigma logicalLeg) occurrence)

/-- Forgetting the finite digit bounds recovers the compatibility model's recursive coarse
sequence literally. -/
@[simp] theorem cwOrientedCoarseCellToIndex_comp_recursiveFiniteCellSequence
    {Part : Type v} (depth n : ℕ)
    (partAt : Fin (n + 1) → Part) (sigma : Orientation)
    (coarse : CWRecursiveCoarseAddress depth n) :
    cwOrientedCoarseCellToIndex ∘
        cwRecursiveOrientedFiniteCellSequence depth n partAt sigma coarse =
      cwRecursiveOrientedCoarseIndexSequence depth n partAt sigma coarse := by
  funext occurrence
  rfl

/-- The bounded tagged-cell encoding loses no information. -/
private theorem cwRecursiveOrientedCoarseCellToIndex_injective
    {Part : Type v} {depth : ℕ} :
    Function.Injective (cwOrientedCoarseCellToIndex :
      CWOrientedCoarseCell Part depth → CoarseIndex Part) := by
  rintro ⟨leftPart, left⟩ ⟨rightPart, right⟩ h
  apply Prod.ext
  · exact congrArg CoarseIndex.part h
  · funext logicalLeg
    apply Fin.ext
    cases logicalLeg with
    | X => simpa [cwOrientedCoarseCellToIndex] using congrArg CoarseIndex.x h
    | Y => simpa [cwOrientedCoarseCellToIndex] using congrArg CoarseIndex.y h
    | Z => simpa [cwOrientedCoarseCellToIndex] using congrArg CoarseIndex.z h

/-- A coarse index of the prescribed child total has a unique bounded-cell representative. -/
private theorem exists_recursiveFiniteCell_of_total
    {Part : Type v} {depth : ℕ} (cell : CoarseIndex Part)
    (htotal : cell.x + cell.y + cell.z = coarseTotal depth) :
    ∃ finiteCell : CWOrientedCoarseCell Part depth,
      cwOrientedCoarseCellToIndex finiteCell = cell := by
  have htotal' : cell.x + cell.y + cell.z = 2 ^ (depth + 1) := by
    simpa [coarseTotal] using htotal
  let digits : BlockAddress (fun _c ↦ CWCoarseDigit depth) := fun logicalLeg ↦
    ⟨cell.get logicalLeg, by
      cases logicalLeg <;> simp only [CoarseIndex.get] <;> omega⟩
  refine ⟨(cell.part, digits), ?_⟩
  apply CoarseIndex.ext <;> rfl

/-- Exact target tables used by a recursive child product have support only on tight child
constituents.  This is stronger than one-leg weight support and is kept explicit so an arbitrary
`CompatibilityTargets` value cannot smuggle infinitely many irrelevant natural-valued cells into
a finite type-counting theorem. -/
def CWRecursiveTargetCoarseTotalSupported
    {Part : Type v} {depth : ℕ} (targets : CompatibilityTargets Part depth) : Prop :=
  ∀ logicalLeg cell word, 0 < targets.exactProfile logicalLeg cell word →
    cell.x + cell.y + cell.z = coarseTotal depth

/-- Multiplicity of a bounded recursive `(cell, split-word)` pair is exactly the original
natural-valued compatibility-cell multiplicity. -/
theorem cwRecursiveFiniteCellSplitMultiplicity_eq_cellMultiplicity
    {Part : Type v} [Fintype Part] [DecidableEq Part]
    {depth n : ℕ}
    (partAt : Fin (n + 1) → Part) (sigma : Orientation)
    (reference : CWRecursiveCoarseAddress depth n)
    (children : Fin ((n + 1) + (n + 1)) → SplitWord depth)
    (cell : CWOrientedCoarseCell Part depth) (word : SplitWord depth) :
    WordType.multiplicity
        (WordType.jointWord
          (cwRecursiveOrientedFiniteCellSequence
            depth n partAt sigma reference) children) (cell, word) =
      cellMultiplicity
        (cwRecursiveOrientedCoarseIndexSequence
          depth n partAt sigma reference)
        children (cwOrientedCoarseCellToIndex cell) word := by
  classical
  unfold WordType.multiplicity cellMultiplicity WordType.jointWord
  congr 1
  ext occurrence
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Prod.mk.injEq]
  constructor
  · rintro ⟨hcell, hword⟩
    exact ⟨congrArg cwOrientedCoarseCellToIndex hcell, hword⟩
  · rintro ⟨hcell, hword⟩
    exact ⟨cwRecursiveOrientedCoarseCellToIndex_injective hcell, hword⟩

/-- Support of all three exact tables, expressed through the leg-parametric profile accessor. -/
theorem compatibilityTargets_exactProfile_weight_eq
    {Part : Type v} {depth : ℕ}
    (targets : CompatibilityTargets Part depth)
    (hsupported : targets.IsWeightSupported)
    (logicalLeg : Leg) (cell : CoarseIndex Part) (word : SplitWord depth)
    (hpositive : 0 < targets.exactProfile logicalLeg cell word) :
    splitWordWeight word = cell.get logicalLeg := by
  cases logicalLeg with
  | X => exact hsupported.1 cell word hpositive
  | Y => exact hsupported.2.1.1 cell word hpositive
  | Z => exact hsupported.2.2.1 cell word hpositive

/-- Membership in one physical-leg exact target alphabet is exactly membership of the labelled
child word in the corresponding conditional type class.  The explicit coarse-word condition in
`cwRecursiveExactTargetFiberParts` follows from the target support invariant; it is not an extra
counting restriction. -/
theorem mem_cwRecursiveExactTargetFiberParts_iff_conditionalTypeClass
    {Part : Type v} [Fintype Part] [DecidableEq Part]
    {depth n : ℕ}
    (partAt : Fin (n + 1) → Part) (sigma : Orientation)
    (targets : CompatibilityTargets Part depth)
    (hsupported : targets.IsWeightSupported)
    (hcoarseSupported : CWRecursiveTargetCoarseTotalSupported targets)
    (reference : CWRecursiveCoarseAddress depth n)
    (logicalLeg : Leg)
    (parent : PositiveWord
      (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n) :
    parent ∈ cwRecursiveExactTargetFiberParts
        partAt sigma targets reference (sigma logicalLeg) ↔
      cwRecursiveLabelledChildrenEquiv depth n parent ∈
        WordType.conditionalTypeClass
          (cwRecursiveOrientedFiniteCellSequence
            depth n partAt sigma reference)
          (fun pair ↦ targets.exactProfile logicalLeg
            (cwOrientedCoarseCellToIndex pair.1) pair.2) := by
  classical
  let finiteSource := cwRecursiveOrientedFiniteCellSequence
    depth n partAt sigma reference
  let source := cwRecursiveOrientedCoarseIndexSequence
    depth n partAt sigma reference
  let children := cwRecursiveLabelledChildrenEquiv depth n parent
  let jointType : CWOrientedCoarseCell Part depth × SplitWord depth → ℕ :=
    fun pair ↦ targets.exactProfile logicalLeg
      (cwOrientedCoarseCellToIndex pair.1) pair.2
  constructor
  · intro hparent
    have hdata := (mem_cwRecursiveExactTargetFiberParts_iff
      partAt sigma targets reference (sigma logicalLeg) parent).1 hparent
    rw [WordType.mem_conditionalTypeClass]
    funext pair
    obtain ⟨cell, word⟩ := pair
    rw [cwRecursiveFiniteCellSplitMultiplicity_eq_cellMultiplicity]
    simpa [source, finiteSource, children, jointType] using
      hdata.2 (cwOrientedCoarseCellToIndex cell) word
  · intro hchildren
    have hjoint :
        WordType.multiplicity
            (WordType.jointWord finiteSource children) = jointType := by
      simpa [finiteSource, children, jointType] using
        (WordType.mem_conditionalTypeClass.mp hchildren)
    have hprofile : ∀ cell word,
        cellMultiplicity source children cell word =
          targets.exactProfile logicalLeg cell word := by
      intro cell word
      by_cases hfinite : ∃ finiteCell : CWOrientedCoarseCell Part depth,
          cwOrientedCoarseCellToIndex finiteCell = cell
      · obtain ⟨finiteCell, rfl⟩ := hfinite
        have hentry := congrFun hjoint (finiteCell, word)
        rw [cwRecursiveFiniteCellSplitMultiplicity_eq_cellMultiplicity] at hentry
        simpa [source, finiteSource, children, jointType] using hentry
      · have htarget : targets.exactProfile logicalLeg cell word = 0 := by
          by_contra hnonzero
          have hpositive : 0 < targets.exactProfile logicalLeg cell word :=
            Nat.pos_of_ne_zero hnonzero
          exact hfinite (exists_recursiveFiniteCell_of_total cell
            (hcoarseSupported logicalLeg cell word hpositive))
        have hsourceCell : ∀ occurrence, source occurrence ≠ cell := by
          intro occurrence heq
          apply hfinite
          refine ⟨finiteSource occurrence, ?_⟩
          calc
            cwOrientedCoarseCellToIndex (finiteSource occurrence) =
                source occurrence := by
              simpa [finiteSource, source, Function.comp_apply] using
                congrFun
                  (cwOrientedCoarseCellToIndex_comp_recursiveFiniteCellSequence
                    depth n partAt sigma reference) occurrence
            _ = cell := heq
        simp [cellMultiplicity, hsourceCell, htarget]
    have hgroup :
        cwRecursiveLabelledChildWord depth n parent =
          reference (sigma logicalLeg) := by
      funext occurrence
      apply Fin.ext
      let cell := source occurrence
      let word := children occurrence
      have hpositive : 0 < cellMultiplicity source children cell word :=
        cellMultiplicity_pos_of_apply_eq
          source children occurrence cell word rfl rfl
      have htargetPositive :
          0 < targets.exactProfile logicalLeg cell word := by
        rw [← hprofile cell word]
        exact hpositive
      have hweight : splitWordWeight word = cell.get logicalLeg :=
        compatibilityTargets_exactProfile_weight_eq targets
          hsupported logicalLeg cell word htargetPositive
      calc
        (cwRecursiveLabelledChildWord depth n parent occurrence : ℕ) =
            splitWordWeight word := by
              simpa [word, children] using
                val_cwRecursiveLabelledChildWord_eq_splitWordWeight
                  depth n parent occurrence
        _ = cell.get logicalLeg := hweight
        _ = (reference (sigma logicalLeg) occurrence : ℕ) := by
          simp [cell, source]
    apply (mem_cwRecursiveExactTargetFiberParts_iff
      partAt sigma targets reference (sigma logicalLeg) parent).2
    refine ⟨hgroup, ?_⟩
    intro cell word
    simpa [source, children] using hprofile cell word

end AlgebraicComplexity.Examples
