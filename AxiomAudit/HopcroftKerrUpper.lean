/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Examples.HopcroftKerrUpper

set_option autoImplicit false

/-!
# Axiom audit for the Hopcroft--Kerr count

Focused trust audit for `AlgebraicComplexity/Examples/HopcroftKerrUpper.lean`, which formalizes
Theorem 1 (p. 31) of J. E. Hopcroft and L. R. Kerr, *On minimizing the number of multiplications
necessary for matrix multiplication*, SIAM J. Appl. Math. **20** (1971), no. 1, 30--36.

The umbrella audit asserts the two `RankLE` instances and the decomposition table.  Asserted here
is `rankLE_count`, the statement that the certificate meets the paper's own arithmetic count
`⌈(3pn + max(n,p))/2⌉`, which the `README.md` Results table names as the certifying declaration.
-/

#assert_axioms AlgebraicComplexity.Examples.HopcroftKerr.rankLE_count
