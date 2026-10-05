/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import MatrixMultiplication.PairedTotalWeightA5ReplacementManifest

set_option autoImplicit false

/-!
# Trust audit for the paired total-weight replacement manifest

This companion checks every public declaration in the frozen-manifest interface used to bind the
replacement certificate to its exact 225 positive rows.  The mathematical complete-split objects
come from [alman2025more, `papers/sources/2404.16349/prelim.tex:249-278` and
`papers/sources/2404.16349/constituent.tex:41-47`].  The sparse layout and row ordering audited here
are project-specific checker representation invariants.
-/

namespace MatrixMultiplication.PairedTotalWeightA5ReplacementManifest

#assert_axioms replacementTop
#assert_axioms replacementBetaThree
#assert_axioms replacementBetaThree_followsNonpositive
#assert_axioms ActiveKey
#assert_axioms Manifest
#assert_axioms Manifest.keyEquiv
#assert_axioms Manifest.row_key
#assert_axioms Manifest.top
#assert_axioms Manifest.betaThree
#assert_axioms Manifest.betaThree_followsNonpositive
#assert_axioms Manifest.row_parentSamples_pos

end MatrixMultiplication.PairedTotalWeightA5ReplacementManifest
