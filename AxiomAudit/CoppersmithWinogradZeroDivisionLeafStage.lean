import AlgebraicComplexity.Examples.CoppersmithWinogradZeroDivisionLeafStage
import AxiomAudit.Command

/-! Focused trust audit for `AlgebraicComplexity.Examples.CoppersmithWinogradZeroDivisionLeafStage`:
the adapters presenting a selected zero-coordinate CW family as a leaf stage of an
`ExactInterfaceTermDivisionTree`, in the native leg frame and by case, together with the
canonical tensor-unit leaf used at multiplicity zero. -/

#assert_axioms AlgebraicComplexity.Examples.cwSelectedExactInterfaceTerm_zero_nativeLeafStage
#assert_axioms AlgebraicComplexity.Examples.cwExactInterfaceTerm_zeroMultiplicityLeafStage
#assert_axioms AlgebraicComplexity.Examples.cwSelectedExactInterfaceTerm_zero_nativeLeafStageOfCase
