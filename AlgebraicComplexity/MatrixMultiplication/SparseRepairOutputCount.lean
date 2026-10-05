/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Combinatorics.ProportionalSparseCounting

/-!
# Integral output counts for sparse repair

This compatibility import exposes the canonical fixed-type quotient
`fixedTypeRepairOutputCount I R = I / (2 * R)` and its exact supply, floor-remainder, positivity,
and growth theorems.  The quotient is formed after selecting a fixed type: using the pre-type
family size in the numerator would discard an unnecessary constant factor and obscure the two
distinct supply inequalities.
-/
