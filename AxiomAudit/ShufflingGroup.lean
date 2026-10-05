/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Combinatorics.ShufflingGroup

/-! Focused trust audit for the shuffling group of [DuanWuZhou2022] §5: uniformity of the
shuffling action and the single union bound that replaces the three-leg repair recursion. -/

#assert_axioms AlgebraicComplexity.HoleRepair.UniformOnParts.uniform_point
#assert_axioms AlgebraicComplexity.HoleRepair.UniformOnParts.ofTargetIndependentFiber
#assert_axioms AlgebraicComplexity.HoleRepair.UniformOnParts.prod
#assert_axioms AlgebraicComplexity.exists_shuffles_avoiding
#assert_axioms AlgebraicComplexity.WordShuffle.card_transporter_eq_card_stabilizer
#assert_axioms AlgebraicComplexity.WordShuffle.uniformOnTypedWords
