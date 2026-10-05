/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import MatrixMultiplication.DyadicEntropyFormEval
import MatrixMultiplication.DyadicEntropyFormZeros

/-!
# Exact signed-log forms for dyadic entropy

This compatibility umbrella exports the executable form constructors, zero-padding invariance,
and real-evaluation laws.  This is a definition-preserving refactor of the existing entropy/form
API, not a new paper theorem.  The list semantics are imported from `DyadicEntropyList`, avoiding
duplicate declarations, while definitions, evaluation proofs, and zero-padding proofs have
separate leaves.  Downstream imports and declaration names are unchanged; the smaller import
boundaries are intended to reduce the cost of clients that need only exact forms.
-/

set_option autoImplicit false
