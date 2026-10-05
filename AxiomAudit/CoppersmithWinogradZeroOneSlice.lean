import AlgebraicComplexity.Examples.CoppersmithWinogradZeroOneSlice
import AxiomAudit.Command

/-!
# Axiom audit for zero-coordinate CW one-slice maps

Checks the map-coherence theorem and the final recursive zero-fiber lift.  The latter's axiom
closure includes all three finite base-map identities and the intermediate word constructors, so
repeating those assertions here would only traverse the same proof graph several times.
-/

open AlgebraicComplexity AlgebraicComplexity.Examples

#assert_axioms cwZeroBaseOneSliceMap_Z_coherent
#assert_axioms cwZeroChunkOneSliceRestriction
