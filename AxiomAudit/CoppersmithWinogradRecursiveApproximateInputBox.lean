/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinogradRecursiveApproximateInputBox
import AxiomAudit.Command

set_option autoImplicit false

/-!
# Axiom audit for the recursive CW approximate-input box identity

This companion checks that the finite selector identity from
`CoppersmithWinogradRecursiveApproximateInputBox` depends only on the project's allowlisted Lean
axioms.  The audited results formalize the input selector step of [alman2025more,
`constituent.tex`, lines 138--147, 338--348, and 473--479].
-/

#assert_axioms
  AlgebraicComplexity.Examples.CWRecursiveKeepsAlphaMarginal_of_mem_cwRecursiveExactTargetFiberParts

#assert_axioms
  AlgebraicComplexity.Examples.cwRecursiveApproximateSelected_box_exactTarget_eq_inputTargetBox

/-! ## Nonvacuity regression -/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor MoreAsymmetryCompatibility

/-- The exact-joint-type premise of the box identity is satisfiable: every supplied recursive
split type is realized by a coarse labelled-child address.  Only the left half matters to this
premise; the right half is filled with zero digits. -/
example {depth n : ℕ} {term : ExactInterfaceTermParameters (depth + 1)}
    (sigma : Orientation)
    (alpha : ExactRecursiveSplitType
      (cwRecursiveLogicalParent term sigma) (coarseTotal depth) (n + 1)) :
    ∃ coarse : CWRecursiveCoarseAddress depth n,
      CWRecursiveMatchesAlpha sigma alpha coarse := by
  classical
  obtain ⟨word, hword⟩ := WordType.typeClass_nonempty
    alpha.coordinateTripleCount alpha.coordinateTripleCount_mem_types
  let coordinate : Leg → ExactRecursiveSplitType.CoordinateTriple (coarseTotal depth) →
      CWRecursiveChildDigit depth
    | .X => fun triple ↦ triple.1
    | .Y => fun triple ↦ triple.2.1
    | .Z => fun triple ↦ triple.2.2
  let coarse : CWRecursiveCoarseAddress depth n := fun physicalLeg ↦
    Fin.append
      (fun sample ↦ coordinate (sigma.symm physicalLeg) (word sample))
      (fun _sample ↦ 0)
  refine ⟨coarse, ?_⟩
  unfold CWRecursiveMatchesAlpha
  rw [show cwRecursiveLogicalLeftTripleWord sigma coarse = word by
    funext sample
    simp [cwRecursiveLogicalLeftTripleWord, cwRecursiveLogicalLeftCoordinateWord,
      coarse, coordinate]]
  exact WordType.mem_typeClass.mp hword

end AlgebraicComplexity.Examples
