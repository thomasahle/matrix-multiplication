/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoPlainBatchedEndpointMarked

set_option autoImplicit false

/-! # Axiom audit for the batched endpoint over an arbitrary marked family

The batched endpoint at the margin with the marked family and the hashing-branch input freed to
binders; the endpoint remains explicitly conditional on them.

Primary source: `[duan2023faster]`, `papers/sources/2210.10173/hashing.tex:7-28` (marginal
triples, `N_alpha` and the hash modulus) and
`papers/sources/2210.10173/global_value.tex:130-140` (the section 6.2 retention bound), at the
level-two instance of section 6.3, `papers/sources/2210.10173/global_value.tex:332-348`. -/

#assert_axioms
  AlgebraicComplexity.Examples.omega_lt_2374631_of_plainBatchedStageAndLeaf_margin_marked
