import AxiomAudit.Command
import AlgebraicComplexity.Examples.CoppersmithWinogradEventualVolumeLossEndpoint

/-! Focused trust audit for
`AlgebraicComplexity.Examples.CoppersmithWinogradEventualVolumeLossEndpoint`: the two
conditional endpoint theorems that turn eventual whole-constituent stages on a power of the
Coppersmith--Winograd tensor into a retained-volume budget and, from it, a strict upper bound on
`omega`. -/

#assert_axioms AlgebraicComplexity.Examples.retained_add_omega_mul_lowerVolume_le_cwPowerBudget_of_eventualStages
#assert_axioms AlgebraicComplexity.Examples.omega_lt_of_cwPower_eventualWholeConstituentVolumeLoss
