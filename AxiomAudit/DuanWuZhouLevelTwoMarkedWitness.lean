/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoMarkedWitness

/-! Focused trust audit for the marked family as a single joint fifteen-cell type: its marginal
typicality, the reference word's membership, and the same-type witness that supplies the localized
stage's reference frame. -/

set_option autoImplicit false

#assert_axioms AlgebraicComplexity.Examples.dwz63_marked_subset_marginal
#assert_axioms AlgebraicComplexity.Examples.dwz63_referenceWord_mem_markedWords
#assert_axioms AlgebraicComplexity.Examples.dwz63_hwitness_of_markedWords
