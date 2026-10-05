/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinogradZeroCoherentRestriction
import AlgebraicComplexity.Examples.CoppersmithWinogradZeroOrientationCoherentRestriction
import AxiomAudit.Command

/-!
# Axiom audit for the rotated coherent zero-coordinate CW chain

Checks the four levels of the rotated chain — base, base word, chunk, outer word of chunks — each
of which retains the shared map its certificates use.

It also records, as a `rfl` theorem rather than a comment, that the rotated chain's shared base map
**is** the committed zero-`Z` one.  The rotated chain restates it only to keep the committed
zero-`Z` interface chain out of that module's import closure, which is worth 1.7 GB of olean load;
this audit is where the two are checked to be the same map.
-/

open AlgebraicComplexity AlgebraicComplexity.Examples

/-- The rotated chain's canonical base map is the committed zero-`Z` one, definitionally. -/
theorem cwZeroBaseRotatedCanonicalZMap_eq_canonical
    (K : Type) [CommRing K] (q : ℕ) :
    cwZeroBaseRotatedCanonicalZMap K q = cwZeroBaseCanonicalZMap K q := rfl

#assert_axioms cwZeroBaseRotatedCanonicalZMap
#assert_axioms cwZeroBaseRotatedCanonicalZMap_eq_canonical
#assert_axioms cwZeroBaseRotatedCoherentRestriction
#assert_axioms cwZeroBaseRotatedWordCanonicalZMap
#assert_axioms cwZeroBaseRotatedWordCoherentRestriction
#assert_axioms cwZeroChunkRotatedCanonicalZMap
#assert_axioms cwZeroChunkRotatedCoherentRestriction
#assert_axioms cwZeroInterfaceRotatedCanonicalZMap
#assert_axioms cwZeroChunkOuterWordRotatedCoherentRestriction
