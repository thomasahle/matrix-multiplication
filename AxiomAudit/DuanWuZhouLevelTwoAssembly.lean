/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoAssembly

/-! Focused trust audit for the two pieces this module still carries towards the section 6.3
endpoint: the joined per-segment type with its evaluation lemma, and the leaf-weight half.  The
stage half and the combined telescope moved to the Step-1 cut family. -/

set_option autoImplicit false

#assert_axioms AlgebraicComplexity.Examples.dwz63JoinedAlphaTilde
#assert_axioms AlgebraicComplexity.Examples.dwz63JoinedAlphaTilde_apply
#assert_axioms AlgebraicComplexity.Examples.dwz63_referenceLeafAssembly_leafWeight
