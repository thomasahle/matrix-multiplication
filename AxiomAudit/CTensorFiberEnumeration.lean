/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.CTensorFiberEnumeration
import AxiomAudit.Command

/-!
# Axiom audit for canonical shared-leg fiber enumeration

Checks the canonical `Fin selected.card` enumeration of a shared-`Z` finite support, its
ambient-block specialization, and the exposed shared `Z` map of that specialization.
-/

open AlgebraicComplexity

#assert_axioms CTensor.FiberRetyping.ofSharedSupport
#assert_axioms CTensor.FiberRetyping.ofSharedSupportAmbient
#assert_axioms CTensor.FiberRetyping.ofSharedSupportAmbient_zMap
