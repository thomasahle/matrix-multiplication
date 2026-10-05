import AlgebraicComplexity.Examples.CoppersmithWinogradApproximateInterface
import AxiomAudit.Command

open AlgebraicComplexity AlgebraicComplexity.Examples

/-! Focused trust audit for `AlgebraicComplexity.Examples.CoppersmithWinogradApproximateInterface`:
the approximate complete-split selector on the native CW chunk partition -- its construction as
a legwise zero-out of a flat power of `CW_q`, its parent-position relabeling action, and the
containment of the exact selected interface term in its approximate counterpart. -/

#assert_axioms cwSelectedApproximateInterfaceTerm
#assert_axioms cwFlatPower_selectedApproximateInterfaceTerm_restricts
#assert_axioms cwSelectedApproximateInterfaceTermPositionRelabeling
#assert_axioms cwSelectedApproximateInterfaceTermPositionRelabeling_partEquiv
#assert_axioms cwSelectedExactInterfaceTerm_support_subset_approximate
