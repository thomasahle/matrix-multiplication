/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Tensor.GroupedCompatibilityPermutation

set_option autoImplicit false

/-!
# Axiom audit for grouped-compatibility permutation transport

The exact transport of direct grouped-compatibility holes through a tensor-leg permutation uses
only the project's allowlisted kernel foundations.  This is the orientation seam behind the
other-region sentence in Section 6.6 of [alman2025more] at
`papers/sources/2404.16349/constituent.tex:497`, serving the `Unique Triple` cleanup of Claim 6.18
in Sections 6.3.2 and 6.4.2 at lines `274-276` and `324-326`, and its hole bound in Section 6.5 at
lines `461-479`.
-/

open AlgebraicComplexity.Tensor

#assert_axioms groupCompatibilityDeletedLabels_permuteBlockAddress
