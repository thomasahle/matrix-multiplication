/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.MatrixMultiplication.Exponent

set_option autoImplicit false

/-!
# Axiom audit for the square exponent's elementary bounds

Focused trust audit for `AlgebraicComplexity/MatrixMultiplication/Exponent.lean`, the layer-3
module defining `omega K` and the two elementary facts the `README.md` Results tables quote about
it: the schoolbook bound `omega ≤ 3`, and the transfer
`RankLE r ⟨q,q,q⟩ → omega ≤ log r / log q` that every rank certificate in `Examples/` is
read through (Strassen's `log 7 / log 2` being the first instance, [strassen1969gaussian]).

The umbrella audit asserts the lower bound `two_le_omega` and the downstream clients; the upper
bounds and the volume form used by the rectangular and laser endpoints are asserted here.
-/

#assert_axioms AlgebraicComplexity.matrixMultiplicationExponent_le_three
#assert_axioms AlgebraicComplexity.omega_le_three
#assert_axioms AlgebraicComplexity.matrixMultiplicationExponent_le_log_of_rankLE
#assert_axioms AlgebraicComplexity.omega_le_log_of_rankLE
#assert_axioms AlgebraicComplexity.matrixMultiplication_volume_rpow_omega_div_three_le_of_rankLE
