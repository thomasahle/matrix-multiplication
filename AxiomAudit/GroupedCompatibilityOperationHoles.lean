/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Tensor.GroupedCompatibilityOperationHoles

set_option autoImplicit false

/-!
# Axiom audit for grouped-compatibility operation holes

The operation-level deleted-label definition and its exact fixed-group support law use only the
project's allowlisted kernel foundations.  They formalize the `Unique Triple` deletion steps in
Sections 6.3.2 and 6.4.2 of [alman2025more], adjacent to
`def:constituent:Y-compatibility` and `def:constituent:compatibility` in
`papers/sources/2404.16349/constituent.tex:274-276,324-326`.
-/

open AlgebraicComplexity.Tensor

#assert_axioms groupCompatibilityDeletedLabels
#assert_axioms mem_groupCompatibilityDeletedLabels_iff
#assert_axioms groupCompatibilityIsolatedFiberSupport_eq_filter_not_mem_deletedLabels
