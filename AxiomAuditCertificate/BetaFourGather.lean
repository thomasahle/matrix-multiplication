/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import MatrixMultiplication.BetaFourGather

/-!
# Enforcing audit for the direct beta-four gather interface

The audited laws support bounded generated shards of the pointwise level-four convolution.  This
audit belongs to the certificate target because the global recurrence import cone reaches
generated reconstruction data.  The future scatter/gather semantic bridge will be asserted here
when proved.
-/

#assert_axioms MatrixMultiplication.SimplifiedExponentLevelFourRecurrence.betaFourParentRowGatherOn_append
#assert_axioms MatrixMultiplication.SimplifiedExponentLevelFourRecurrence.length_betaFourParentRowGatherOn
#assert_axioms MatrixMultiplication.SimplifiedExponentLevelFourRecurrence.betaFourParentRowGather_eq_on_range
