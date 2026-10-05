/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Examples.CoppersmithWinogradFirstPower

set_option autoImplicit false

/-!
# Axiom audit for the first-power Coppersmith--Winograd target constant

Focused trust audit for `AlgebraicComplexity/Examples/CoppersmithWinogradFirstPower.lean`, the
classical non-recursive laser analysis of `CW₆` of [coppersmith1990matrix], whose numerical
conclusion is `omega < 2.3872`.

The umbrella audit asserts the base inequality, the rate inequality and the strict endpoint
`coppersmithWinograd_firstPower_omega_lt`.  Asserted here is the decimal evaluation of the target
constant that the `README.md` Results row names as the witness; it is not a dependency of the
asserted endpoint, so it needs its own assertion.
-/

namespace AlgebraicComplexity.Examples

#assert_axioms cwFirstPowerTarget_eq_decimal

end AlgebraicComplexity.Examples
