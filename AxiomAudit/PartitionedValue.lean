/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.MatrixMultiplication.PartitionedValue

/-!
# Axiom audit for finite partitioned matrix-multiplication values

This focused audit stays below the laser extraction and Schönhage soundness imports.
-/

#assert_axioms AlgebraicComplexity.PartitionedMMCertificate.volume_pos
