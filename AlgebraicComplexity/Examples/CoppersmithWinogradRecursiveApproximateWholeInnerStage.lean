/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinogradRecursivePresentExactTargetFiber
import AlgebraicComplexity.MatrixMultiplication.CoarsenedConstituentWholeStage

set_option autoImplicit false

/-!
# A recursive approximate coarse constituent as a whole-constituent stage

This is arrow A8.2 of the paired total-weight ledger: the step from one constituent of the
labelled-child quotient to the literal copy-and-dimension stage that the seed-indexed aggregate
wrapper consumes once per selected address.

`Examples/CoppersmithWinogradRecursivePresentExactTargetFiber.lean` supplies the semantic half ---
a supported recursive approximate coarse constituent restricts onto the box of exact-target fine
addresses actually present over it --- and
`MatrixMultiplication/CoarsenedConstituentWholeStage.lean` supplies the generic packaging.  All
that is specific to the recursive route is the identification of the generic localized parts with
`cwRecursiveExactTargetFiberParts`, which is exactly the fiber condition already being carried
inside the exact-target predicate.  That identification is stated here as a reusable lemma rather
than left as a local step, because both the present-fiber arrow and this stage need it.

The inner extraction of the present exact box is a callback: nothing here fixes how that box is
degenerated, and nothing here asserts that the box is hole-free.  Replacing the *present* exact
fiber by the *full* compact exact box is the separate Order-8 obligation tracked by
`cwRecursiveInputProfileHoles` and `cwRecursiveApproximateCleanedFiberHoles`; this module does not
hide it.

`[CoppersmithWinograd1990]`.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor MoreAsymmetryCompatibility

universe u v w

/-- The generic localized-selection parts of the labelled-child coarsening at an exact-target
selector are exactly the exact-target fiber parts.

The fiber condition that `coarseningFiberSelectParts` conjoins is already implied by membership in
`cwRecursiveExactTargetFiberParts`, whose first component is that same labelled-child equation, so
conjoining it adds nothing. -/
theorem coarseningFiberSelectParts_cwRecursiveChildCoarsening_eq_exactTargetFiberParts
    {Part : Type v} [DecidableEq Part] {depth n : ℕ}
    (partAt : Fin (n + 1) → Part) (sigma : Orientation)
    (targets : CompatibilityTargets Part depth)
    (coarse : CWRecursiveCoarseAddress depth n)
    (keep : ∀ _c : Leg,
      PositiveWord (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n → Prop)
    [∀ c fine, Decidable (keep c fine)]
    (hkeep : ∀ c fine, keep c fine ↔
      fine ∈ cwRecursiveExactTargetFiberParts partAt sigma targets coarse c) :
    coarseningFiberSelectParts (cwRecursiveChildCoarsening depth n) coarse keep =
      cwRecursiveExactTargetFiberParts partAt sigma targets coarse := by
  classical
  funext physicalLeg
  ext fine
  rw [mem_coarseningFiberSelectParts, hkeep]
  constructor
  · exact And.right
  · intro hfine
    refine ⟨?_, hfine⟩
    exact (mem_cwRecursiveExactTargetFiberParts_iff
      partAt sigma targets coarse physicalLeg fine).1 hfine |>.1

/-- **A8.2: one supported recursive approximate coarse constituent, with an inner extraction of
its present exact target box, is a whole-constituent laser-volume stage.**

This is `Tensor.Restricts.coarsen_constituent_wholeInnerStage` instantiated at the recursive
approximate route: the fine partition is the approximate marginal-selected term, the coarsening is
`cwRecursiveChildCoarsening`, and the legwise keep predicate is membership in the exact-target
fiber parts.  The inner index type and its cardinality are carried exactly; no survivor count,
hole budget, or asymptotic estimate is introduced.

The conclusion is the `inner` callback of
`Tensor.Restricts.exists_aggregateMarkedDirectionalSelectedWholeInnerStage` at one selected
address. -/
noncomputable def cwRecursiveApproximateCoarsenedAlphaMarginalTerm_constituent_wholeInnerStage
    (K : Type u) [CommRing K] (q : ℕ)
    {Part : Type v} [DecidableEq Part] {depth n : ℕ}
    (partAt : Fin (n + 1) → Part)
    (term : ExactInterfaceTermParameters (depth + 1))
    (hmultiplicity : term.multiplicity = n + 1)
    (epsilon : ℝ) (sigma : Orientation)
    (alpha : ExactRecursiveSplitType
      (cwRecursiveLogicalParent term sigma) (coarseTotal depth) (n + 1))
    (targets : CompatibilityTargets Part depth)
    (coarse : CWRecursiveCoarseAddress depth n)
    (hcoarse : coarse ∈
      (cwRecursiveApproximateCoarsenedAlphaMarginalTerm
        K q term hmultiplicity epsilon sigma alpha).support)
    {I : Type w} [Fintype I]
    (innerCopies xSize ySize zSize : ℕ)
    (hcard : Fintype.card I = innerCopies)
    (inner : Restricts
      ((cwRecursiveApproximateAlphaMarginalSelectedTerm
        K q term hmultiplicity epsilon sigma alpha).box
          (cwRecursiveExactTargetFiberParts partAt sigma targets coarse)).realize
      (Tensor.indexedDirectSum
        (fun _ : I ↦ matrixMultiplication (K := K) xSize ySize zSize))) :
    WholeConstituentLaserVolumeStage K
      ((cwRecursiveApproximateCoarsenedAlphaMarginalTerm
        K q term hmultiplicity epsilon sigma alpha).constituent coarse)
      innerCopies xSize ySize zSize := by
  classical
  let P := cwRecursiveApproximateAlphaMarginalSelectedTerm
    K q term hmultiplicity epsilon sigma alpha
  let f := cwRecursiveChildCoarsening depth n
  let keep : ∀ _c : Leg,
      PositiveWord (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n → Prop :=
    fun c fine ↦ fine ∈ cwRecursiveExactTargetFiberParts
      partAt sigma targets coarse c
  have hcoarse' : coarse ∈ (P.coarsen f).support := hcoarse
  have hparts : coarseningFiberSelectParts f coarse keep =
      cwRecursiveExactTargetFiberParts partAt sigma targets coarse :=
    coarseningFiberSelectParts_cwRecursiveChildCoarsening_eq_exactTargetFiberParts
      partAt sigma targets coarse keep fun _c _fine ↦ Iff.rfl
  have hinner : Restricts
      (P.box (coarseningFiberSelectParts f coarse keep)).realize
      (Tensor.indexedDirectSum
        (fun _ : I ↦ matrixMultiplication (K := K) xSize ySize zSize)) := by
    rw [hparts]
    exact inner
  exact Tensor.Restricts.coarsen_constituent_wholeInnerStage
    P f coarse hcoarse' keep innerCopies xSize ySize zSize hcard hinner

end AlgebraicComplexity.Examples
