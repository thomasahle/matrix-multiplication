/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import MatrixMultiplication.CertifiedLevelFourOccurrenceExtractionClients

/-!
# Axiom audit for the certified level-four extraction clients

The count-facing seam carries the generated data of certificate `e7987d7f…` in its closure, so
its three public declarations are asserted at the certificate tier.
-/

#assert_axioms MatrixMultiplication.CertifiedLevelFourOccurrenceExtractionClients.certifiedTargetData_supported
#assert_axioms MatrixMultiplication.CertifiedLevelFourOccurrenceExtractionClients.certifiedLevelFourOccurrenceFixedTargetCellType_to_indexedDirectSum
#assert_axioms MatrixMultiplication.CertifiedLevelFourOccurrenceExtractionClients.certifiedLevelFourOccurrenceFixedTargetCellType_to_indexedDirectSum_ofChecked
