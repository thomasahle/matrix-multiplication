import AxiomAudit.Command
import MatrixMultiplication.SimplifiedRecursiveSplitTypes

/-!
# Axiom audit for exact recursive split types

The audited totals ensure that the integral rows reconstructed from the certificate really define
finite ordered child types at both positive recursive transitions.
-/

#assert_axioms MatrixMultiplication.SimplifiedRecursiveSplitTypes.levelThreeSplitType_total
#assert_axioms MatrixMultiplication.SimplifiedRecursiveSplitTypes.levelFourSplitType_total
