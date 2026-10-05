/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Combinatorics.CompatibilityIsolationLabel

set_option autoImplicit false

/-!
# Trust audit for label-parametric compatibility isolation

This audits the elementary label adapter used after the compatibility isolation in Claim 6.18 of
[alman2025more], `papers/sources/2404.16349/constituent.tex:376-440`.  It proves no compatibility
count, fine lift, entropy or asymptotic estimate, CW-specific datum, or tensor degeneration.
-/

#assert_axioms
  AlgebraicComplexity.ProgressionHash.Seed.compatibilityIsolatedTargets_injectiveOn_label
