/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Examples.CoppersmithWinogradSquare211TypedLeaf

set_option autoImplicit false

/-!
# Axiom audit for the raw-square CW `(2,1,1)` typed leaf

Every public declaration in `CoppersmithWinogradSquare211TypedLeaf` is checked against the
repository's allowlist.  In particular, the literal raw-address identification, scalar entropy
identity, and segmented degeneration wrapper introduce no unreviewed assumptions.
-/

#assert_axioms AlgebraicComplexity.Examples.cwSquare211RationalTypedLeaf
#assert_axioms AlgebraicComplexity.Examples.cwSquare211FineLetter
#assert_axioms AlgebraicComplexity.Examples.cwSquare211RawDictionary
#assert_axioms AlgebraicComplexity.Examples.cwSquare211FineLetter_dictionary_image
#assert_axioms AlgebraicComplexity.Examples.cwSquare211Beta
#assert_axioms AlgebraicComplexity.Examples.cwSquare211RationalTypedLeaf_normalized_masses
#assert_axioms AlgebraicComplexity.Examples.cwSquare211_muEntropyBits_eq_binaryEntropyBits_add_beta
#assert_axioms AlgebraicComplexity.Examples.cwSquare211RationalTypedLeaf_marginalEntropyBits
#assert_axioms AlgebraicComplexity.Examples.cwSquare211RationalTypedLeaf_dimensionProducts
#assert_axioms AlgebraicComplexity.Examples.cwSquare211SegmentedCertificate
