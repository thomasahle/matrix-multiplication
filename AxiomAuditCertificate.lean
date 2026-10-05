import AxiomAudit.Command
import MatrixMultiplication.Generated.ParentGainData
import MatrixMultiplication.Generated.LevelFourFeasibilityData
import MatrixMultiplication.Generated.SimplifiedCW112Leaves

/-!
# Axiom audit for generated certificate data

Opt-in companion to `AxiomAudit` covering the declarations that live inside the roughly
five-minute generated certificate build.  Besides parent gain and level-four feasibility, this
checks the bridges interpreting positive level-two entries as rational CW `112` typed leaves.
Keeping these assertions here lets the main audit target stay independent of the generated
numeral tables.  Build with

```text
lake build AxiomAuditCertificate
```

Each `#assert_axioms` fails elaboration if its declaration depends on any axiom other than
`propext`, `Classical.choice`, and `Quot.sound`.
-/

#assert_axioms MatrixMultiplication.ParentGainCertificate.Generated.regionZeroRawFloor_certified
#assert_axioms MatrixMultiplication.ParentGainCertificate.Generated.regionTwoRawFloor_certified
#assert_axioms MatrixMultiplication.LevelFourReconstruction.Generated.certificate_isValid
#assert_axioms MatrixMultiplication.LevelFourReconstruction.Generated.regionProbabilityData_isProbability
#assert_axioms MatrixMultiplication.LevelFourReconstruction.Generated.splitProbabilityData_isProbability
#assert_axioms MatrixMultiplication.Generated.SimplifiedCW112Leaves.cw112Mu_numerator_leafG_eq_mass
#assert_axioms MatrixMultiplication.Generated.SimplifiedCW112Leaves.cw112MuEntropyBits_numerator_leafG_eq
#assert_axioms MatrixMultiplication.Generated.SimplifiedCW112Leaves.storedMuIndices_are_positiveSlots
#assert_axioms MatrixMultiplication.Generated.SimplifiedCW112Leaves.selected_mu_positiveSlot
#assert_axioms MatrixMultiplication.Generated.SimplifiedCW112Leaves.selected_mu_bounds
#assert_axioms MatrixMultiplication.Generated.SimplifiedCW112Leaves.selectedLevelTwoEntry_instantiates_cw112
#assert_axioms MatrixMultiplication.Generated.SimplifiedCW112Leaves.edgeInput_instantiates_cw112_of_bounds
