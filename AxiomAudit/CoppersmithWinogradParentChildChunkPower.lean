/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Examples.CoppersmithWinogradParentChildChunkPower

/-!
# Focused trust audit for the parent/child chunk power identification

These assertions cover the doubled child-word length identity, the parent/child word join and its
positionwise readouts, the labelled left and right child readouts, the parent/child word
equivalence and its doubled-occurrence characterization, the transported position permutation, the
conjugation identity for decoded child-occurrence permutations, the three exact legwise
partition reindexes relating the parent and child chunk powers, and the discharged
recursive child-occurrence relabeling lift.
-/

open AlgebraicComplexity AlgebraicComplexity.Examples

#assert_axioms cwDoubledChildLength
#assert_axioms cwParentChildChunkWordJoin
#assert_axioms positiveWordEquiv_cwParentChildChunkWordJoin
#assert_axioms cwRecursiveLabelledChildren_join_left
#assert_axioms cwRecursiveLabelledChildren_join_right
#assert_axioms cwParentChildChunkWordEquiv
#assert_axioms positiveWordEquiv_cwParentChildChunkWordEquiv
#assert_axioms cwDoubledPositionPerm
#assert_axioms cwRecursiveChildOccurrencePartEquiv_eq_conj
#assert_axioms cwChunkPartitionedTensor_succ_reindexEquiv
#assert_axioms cwParentChunkPower_reindexEquiv
#assert_axioms cwChildChunkPower_reindexEquiv
#assert_axioms exists_cwRecursiveChildOccurrenceRelabeling
#assert_axioms cwRecursiveChildOccurrenceRelabelingLift_holds
