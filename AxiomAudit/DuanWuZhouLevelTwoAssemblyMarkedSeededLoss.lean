/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoAssemblyMarkedSeededLoss

/-! Focused trust audit for the section 6.3 assembly against the seeded endpoint at the joint
hash loss.

Paper step: `[duan2023faster]` §6.2 assembly of retained count, Hole Lemma and leaf value
(`papers/sources/2210.10173/global_value.tex:270-305`), at §6.3's level-two parameters
(`:332-378`). -/

set_option autoImplicit false

#assert_axioms
  AlgebraicComplexity.Examples.omega_lt_2374631_of_referenceLeafWeight_marked_seeded_loss
