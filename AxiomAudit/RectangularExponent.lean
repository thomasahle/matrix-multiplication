/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.MatrixMultiplication.RectangularExponent

set_option autoImplicit false

/-!
# Axiom audit for the rectangular exponent's endpoint values

Focused trust audit for `AlgebraicComplexity/MatrixMultiplication/RectangularExponent.lean`, which
defines `rectangularOmega K κ = ω(1, κ, 1)` and its dual exponent `α`, in the convention of the
rectangular literature quoted by [almanwilliams2024refined].

The umbrella audit asserts the convexity, interpolation and `α`-characterization block.  Asserted
here are the three facts the `README.md` Results row states about the exponent itself: monotonicity
in `κ`, the identification `ω(1) = ω`, and the exact value `ω(0) = 2` over a field.
-/

#assert_axioms AlgebraicComplexity.rectangularOmega_mono
#assert_axioms AlgebraicComplexity.rectangularOmega_one
#assert_axioms AlgebraicComplexity.rectangularOmega_zero
