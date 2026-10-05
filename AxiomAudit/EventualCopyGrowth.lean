import AxiomAudit.Command
import AlgebraicComplexity.Analysis.EventualCopyGrowth

/-! Focused trust audit for absorbing a finite prefix in an eventual copy bound. -/

#assert_axioms AlgebraicComplexity.Growth.finitePrefixPowerLoss_subexponential
#assert_axioms AlgebraicComplexity.Growth.pow_le_finitePrefixPowerLoss_mul_count
