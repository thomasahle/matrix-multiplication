/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Combinatorics.ComplementaryOccurrenceLawPushforward

set_option autoImplicit false

/-!
# Axiom audit for occurrence-dependent symbol pushforwards

This audit checks the exact finite pushforward identities used by the Total-Weight form of
[alman2025more, Claim 6.18], `papers/sources/2404.16349/constituent.tex:402-429`.
-/

open AlgebraicComplexity.ComplementaryOccurrenceLaw

#assert_axioms pushforwardSymbols
#assert_axioms pushforwardSymbols_count
#assert_axioms cellJointProfile_pushforwardSymbols
