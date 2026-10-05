/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Examples.CoppersmithWinogradEasyHashing

set_option autoImplicit false

/-!
# Axiom audit for the easy Coppersmith--Winograd hashing endpoint

Focused trust audit for `AlgebraicComplexity/Examples/CoppersmithWinogradEasyHashing.lean`, the
equal-type hashing client for the three-constituent easy tensor of [coppersmith1990matrix], in the
presentation of Section 4.1 of He and Williams's CS 6810 notes.

The umbrella audit asserts the base inequality and the strict endpoint
`coppersmithWinograd_easy_omega_lt`.  Asserted here are the two further declarations the
`README.md` Results row names: the logarithmic form of the bound, and the decimal evaluation of
the target constant, which is declared after the endpoint and so lies outside its cone.
-/

namespace AlgebraicComplexity.Examples

#assert_axioms easyCW_omega_le_log
#assert_axioms easyCWTarget_eq_decimal

end AlgebraicComplexity.Examples
