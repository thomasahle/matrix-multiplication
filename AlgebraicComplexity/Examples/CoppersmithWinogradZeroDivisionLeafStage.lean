/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinogradZeroNativeStage
import AlgebraicComplexity.MatrixMultiplication.ExactInterfaceDivisionLeafStage

/-!
# Zero-coordinate CW families as exact division-tree leaf stages

`cwSelectedExactInterfaceTerm_zero_nativeStage` extracts the complete selected zero-coordinate
family in the source's native leg frame.  Recursive certificate assembly consumes the same result
as a leaf of `ExactInterfaceTermDivisionTree.LeafStages`.  This module gives that direct adapter.

At positive multiplicity the source is definitionally the exact selected CW interface term, so
the already-proved native stage can be packed without a new restriction or an existential choice.
At multiplicity zero the canonical tensor-unit leaf is used.  The adapter assumes neither a
type-class cardinality bound nor any restriction of an assembled regional product.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor

universe u

/-- A positive zero-coordinate exact CW family as one checked division-tree leaf in its native
leg frame.  The selected-support cardinality and the `q`-power both remain inside the one
nontrivial matrix dimension computed by the whole-family stage. -/
noncomputable def cwSelectedExactInterfaceTerm_zero_nativeLeafStage
    (K : Type u) [CommRing K] (q : ℕ) (zero : Leg)
    {depth n : ℕ} (term : ExactInterfaceTermParameters depth)
    (hmultiplicity : term.multiplicity = n + 1)
    (hzero : term.index.count zero = 0) :
    ExactInterfaceTermDivisionTree.LeafStages K
      (cwChunkPartitionedTensor K q depth)
      (fun _c ↦ cwChunkSplitWord depth)
      (.leaf (.positive n hmultiplicity)) := by
  refine .leaf (.positive n hmultiplicity) ?_
  exact
    { copies := 1
      xSize :=
        match zero with
        | .X => 1
        | .Y => cwSelectedZeroFamilyDimension K q .Y term hmultiplicity
        | .Z => 1
      ySize :=
        match zero with
        | .X => 1
        | .Y => 1
        | .Z => cwSelectedZeroFamilyDimension K q .Z term hmultiplicity
      zSize :=
        match zero with
        | .X => cwSelectedZeroFamilyDimension K q .X term hmultiplicity
        | .Y => 1
        | .Z => 1
      stage := cwSelectedExactInterfaceTerm_zero_nativeStage
        K q zero term hmultiplicity hzero }

/-- A zero-multiplicity exact CW term contributes the canonical one-copy tensor unit to the
division-tree fold. -/
noncomputable def cwExactInterfaceTerm_zeroMultiplicityLeafStage
    (K : Type u) [CommRing K] (q : ℕ)
    {depth : ℕ} (term : ExactInterfaceTermParameters depth)
    (hmultiplicity : term.multiplicity = 0) :
    ExactInterfaceTermDivisionTree.LeafStages K
      (cwChunkPartitionedTensor K q depth)
      (fun _c ↦ cwChunkSplitWord depth)
      (.leaf (.zero hmultiplicity)) :=
  ExactInterfaceTermDivisionTree.LeafStages.zero K hmultiplicity

/-- Uniform zero-or-positive adapter for a zero-coordinate regional leaf.

The zero-coordinate equation is deliberately retained in the zero branch as part of the
certificate-facing occurrence classification, even though the tensor unit itself does not need
it. -/
noncomputable def cwSelectedExactInterfaceTerm_zero_nativeLeafStageOfCase
    (K : Type u) [CommRing K] (q : ℕ) (zero : Leg)
    {depth : ℕ} (term : ExactInterfaceTermParameters depth)
    (multiplicityCase : ExactInterfaceTermMultiplicityCase term)
    (hzero : term.index.count zero = 0) :
    ExactInterfaceTermDivisionTree.LeafStages K
      (cwChunkPartitionedTensor K q depth)
      (fun _c ↦ cwChunkSplitWord depth)
      (.leaf multiplicityCase) := by
  cases multiplicityCase with
  | zero hmultiplicity =>
      exact cwExactInterfaceTerm_zeroMultiplicityLeafStage K q term hmultiplicity
  | positive n hmultiplicity =>
      exact cwSelectedExactInterfaceTerm_zero_nativeLeafStage
        K q zero term hmultiplicity hzero

end AlgebraicComplexity.Examples
