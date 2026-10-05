/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Examples.Schonhage

set_option autoImplicit false

/-!
# Axiom audit for Schoenhage's ten-term direct-sum degeneration

Focused trust audit for `AlgebraicComplexity/Examples/Schonhage.lean`, which formalizes Section 7
of [schonhage1981partial] (A. Schoenhage, *Partial and Total Matrix Multiplication*, SIAM J.
Comput. **10** (1981), no. 3, 434--455).

The umbrella audit asserts the border-rank certificate and the endpoint `omega < 2.6`.  Asserted
here is the intermediate asymptotic-sum inequality `9^(omega/3) + 4^(omega/3) ≤ 10`, which the
`README.md` Results table names as `schonhage_asymptoticSum_bound`.
-/

#assert_axioms AlgebraicComplexity.Examples.schonhage_asymptoticSum_bound
