/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.MatrixMultiplication.LaserVolumeLossMonotone

/-! # Axiom audit for source transport and base weakening of loss-aware laser-volume sequences -/

#assert_axioms AlgebraicComplexity.SubexponentialLaserVolumeLossSequence.of_restricts
#assert_axioms AlgebraicComplexity.SubexponentialLaserVolumeLossSequence.mono_copyBase
#assert_axioms AlgebraicComplexity.SubexponentialLaserVolumeLossSequence.mono_volumeBase
#assert_axioms AlgebraicComplexity.SubexponentialLaserVolumeLossSequence.mono
