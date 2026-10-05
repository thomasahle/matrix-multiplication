/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Examples.Strassen

set_option autoImplicit false

/-!
# Axiom audit for Strassen's rank-seven decomposition

Focused trust audit for the tensor-power form of the rank certificate proved in
`AlgebraicComplexity/Examples/Strassen.lean`, following [strassen1969gaussian] (V. Strassen,
*Gaussian elimination is not optimal*, Numer. Math. **13** (1969), 354--356).

The base certificate `strassen_rankLE` and its exponent client `strassen_omega_le_log` are
asserted by the umbrella audit; the power form `strassen_rankLE_pow`, which the `README.md`
Results table names alongside them, is asserted here.
-/

#assert_axioms AlgebraicComplexity.Examples.strassen_rankLE_pow
