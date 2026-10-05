/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Combinatorics.GuardedFineCompatibility

set_option autoImplicit false

/-!
# Axiom audit for guarded fine compatibility

This audit checks the relation-level fine-selection guard used before the compatibility count in
[alman2025more, Claim 6.18], `papers/sources/2404.16349/constituent.tex:350-386`.  The audited
module proves only relation identities, shared-leg transport, and the uniform finite-cardinality
wrapper; it proves no typical-set count, entropy estimate, hashing selection, tensor restriction,
or endpoint.
-/

open AlgebraicComplexity.ProgressionHash.LegalTriple

#assert_axioms FineGuardedCompatible
#assert_axioms fineGuardedCompatible_sharesLeg
#assert_axioms filter_fineGuardedCompatible_eq_empty_of_not_allowed
#assert_axioms filter_fineGuardedCompatible_eq_of_allowed
#assert_axioms card_filter_fineGuardedCompatible_le
