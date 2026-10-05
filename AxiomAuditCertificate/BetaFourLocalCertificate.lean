/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import MatrixMultiplication.BetaFourLocalCertificate

/-!
# Enforcing audit for parent-local beta-four certificates

These assertions cover the local-certificate-to-global-recurrence adapter.  The cache-free
arithmetic laws have their own ordinary audit in `AxiomAudit/BetaFourLocalChecker.lean`; this
adapter audit lives in the certificate target because its recurrence import cone reaches
generated reconstruction data.
-/

#assert_axioms MatrixMultiplication.SimplifiedExponentLevelFourRecurrence.BetaFourLocalData.gatherNumerator_eq_global
#assert_axioms MatrixMultiplication.SimplifiedExponentLevelFourRecurrence.BetaFourLocalData.gatherOn_eq_global
#assert_axioms MatrixMultiplication.SimplifiedExponentLevelFourRecurrence.BetaFourLocalData.scatter_eq_global
