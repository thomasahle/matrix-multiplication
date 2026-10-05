/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.MatrixMultiplication.CyclicLaserVolumeSoundness

/-! Focused trust audit for cyclic laser-volume sequences and their final soundness theorem. -/

#assert_axioms AlgebraicComplexity.SubexponentialCyclicLaserVolumeSequence.toSubexponentialLaserVolumeSequence
#assert_axioms AlgebraicComplexity.SubexponentialCyclicLaserVolumeSequence.hasCyclicLaserExtractionRate
#assert_axioms AlgebraicComplexity.SubexponentialCyclicLaserVolumeSequence.omega_le_of_borderRank_le
