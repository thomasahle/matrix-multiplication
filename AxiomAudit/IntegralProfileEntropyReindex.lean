/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Probability.IntegralProfileEntropyReindex
import AxiomAudit.Command

/-!
# Axiom audit for integral-profile entropy reindexing

This enforcing audit checks that both alphabet-equivalence entropy identities use only the
project's allowlisted foundational axioms.  They supply the alphabet-relabeling step used in
[alman2025more, Claim 6.18], `papers/sources/2404.16349/constituent.tex:376-440`.

The audited declarations prove no compatibility count, independence premise, asymptotic
estimate, or CW-specific datum.
-/

set_option autoImplicit false

#assert_axioms AlgebraicComplexity.WordType.profileEntropyNats_mappedType_equiv
#assert_axioms AlgebraicComplexity.WordType.profileEntropyBits_mappedType_equiv
