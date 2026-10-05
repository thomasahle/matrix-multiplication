/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Examples.RawCyclicRowExtractionTiny

set_option autoImplicit false

/-!
# Axiom audit for the tiny one-hash cyclic-row client

The final declaration proves that the new generic finite Mode-B interface for the forthcoming
legal-hybrid appendix of the Total-Weight manuscript (`better_bound/paper.tex`) has a concrete
nonempty instance with a pure rank-one constituent.  It is not a theorem in [alman2025more]; the
paper's ordinary extraction at `papers/sources/2404.16349/constituent.tex:376-440,483-497` is an
ingredient only.
-/

open AlgebraicComplexity.Examples.RawCyclicRowExtractionTiny

#assert_axioms OneLabel
#assert_axioms OneBlockSpace
#assert_axioms soleAddress
#assert_axioms oneBlockPartition
#assert_axioms primitiveSupport
#assert_axioms cyclicSupport
#assert_axioms primitiveWord
#assert_axioms cyclicWord
#assert_axioms hashEncoding
#assert_axioms primitiveProfile
#assert_axioms primitiveProfile_mass
#assert_axioms exists_tinyRawCyclicRow_nonempty
