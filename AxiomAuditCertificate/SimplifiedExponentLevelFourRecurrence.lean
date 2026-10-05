/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

/-!
# Certificate-tier axiom audit for level-four recurrence projections

The recurrence module reaches generated reconstruction data through its complete-split import
cone.  These direct assertions therefore live in the certificate audit target rather than the
ordinary generated-free target.
-/

#assert_axioms MatrixMultiplication.SimplifiedExponentLevelFourRecurrence.logicalYRows_pooled
#assert_axioms MatrixMultiplication.SimplifiedExponentLevelFourRecurrence.logicalZRows_pooled
#assert_axioms MatrixMultiplication.SimplifiedExponentLevelFourRecurrence.addBetaFourSlotSparse_eq_addBetaFourSlot
#assert_axioms MatrixMultiplication.SimplifiedExponentLevelFourRecurrence.betaFourParentRowSparse_eq_betaFourParentRow
