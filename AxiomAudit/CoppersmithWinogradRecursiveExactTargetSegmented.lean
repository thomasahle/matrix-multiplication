/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Examples.CoppersmithWinogradRecursiveExactTargetSegmented

set_option autoImplicit false

/-!
# Axiom audit for recursive CW exact targets as segmented families

These checks cover the finite cell segmentation and the exact equivalence between membership in a
recursive CW target fiber and the per-cell segment multiplicities used by the whole inner family.
This is the complete-split condition and fixed-cell subclaim used in the proof of Claim 6.18 of
[alman2025more], `papers/sources/2404.16349/constituent.tex:376-440`; it supplies an interface for,
but does not construct or audit, the family
`L_t(\boldsymbol\tau)` in `better_bound/paper.tex:1691-1775`.

No tensor restriction, counting estimate, certificate, or exponent endpoint is asserted here.
-/

#assert_axioms AlgebraicComplexity.Examples.cwRecursiveExactTargetSegmentation
#assert_axioms
  AlgebraicComplexity.Examples.mem_cwRecursiveExactTargetFiberParts_iff_segmentMultiplicity
