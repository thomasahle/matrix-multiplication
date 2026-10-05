/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinogradRecursiveApproximateInputTransport
import AxiomAudit.Command

set_option autoImplicit false

/-!
# Axiom audit for paired recursive CW approximate-input transport

This companion checks the finite alphabet transport used in the Total-Weight manuscript's paired
fiber normalization (`better_bound/paper.tex`, Lemma `lem:paired-recursive-normalization`, lines
975--998).  It also instantiates the theorem at the identity permutation, showing that its tag and
coarse-address transport hypotheses are jointly satisfiable.
-/

#assert_axioms
  AlgebraicComplexity.Examples.cwRecursiveApproximateInputTargetParts_positionRelabel_iff

#assert_axioms
  AlgebraicComplexity.Examples.relabelParts_cwRecursiveApproximateInputTargetParts

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor MoreAsymmetryCompatibility

universe v

/-- The transport theorem specializes to the identity paired-position action without any extra
hypothesis on the target data. -/
example {Part : Type v} [DecidableEq Part] {depth n : ℕ}
    (partAt : Fin (n + 1) → Part) (sigma : Orientation)
    (term : ExactInterfaceTermParameters (depth + 1))
    (hmultiplicity : term.multiplicity = n + 1)
    (epsilon : ℝ) (targets : CompatibilityTargets Part depth)
    (coarse : CWRecursiveCoarseAddress depth n) :
    relabelParts
        (fun _physicalLeg ↦ positiveWordPositionEquiv
          (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n (Equiv.refl _))
        (cwRecursiveApproximateInputTargetParts
          partAt sigma term hmultiplicity epsilon targets coarse) =
      cwRecursiveApproximateInputTargetParts
        partAt sigma term hmultiplicity epsilon targets coarse := by
  apply relabelParts_cwRecursiveApproximateInputTargetParts
  · rfl
  · funext physicalLeg occurrence
    refine Fin.addCases ?_ ?_ occurrence <;> intro sample
    · simp only [cwRecursivePositionRelabelCoarseAddress_left, Equiv.refl_apply]
    · simp only [cwRecursivePositionRelabelCoarseAddress_right, Equiv.refl_apply]

end AlgebraicComplexity.Examples
