import AlgebraicComplexity.MatrixMultiplication.OneSlicePartitionedPower
import AxiomAudit.Command

/-!
# Axiom audit for one-slice partitioned powers

Checks both the word-aligned and whole-support positive-power constructors.
-/

open AlgebraicComplexity AlgebraicComplexity.Tensor

#assert_axioms OneSliceRestriction.PositiveSupportWordData
#assert_axioms OneSliceRestriction.ofPositiveSupportWordData
#assert_axioms OneSliceRestriction.ofPositivePowerConstituentData
#assert_axioms OneSliceRestriction.positiveSupportWord
#assert_axioms OneSliceRestriction.positivePowerConstituent
