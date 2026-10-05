/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.MatrixMultiplication.FiniteLaserVolumePower

/-! Focused trust audit for lossless powers of a finite laser-volume stage. -/

#assert_axioms AlgebraicComplexity.WholeConstituentLaserVolumeStage.toFin
#assert_axioms AlgebraicComplexity.WholeConstituentLaserVolumeStage.exists_power_succ
#assert_axioms AlgebraicComplexity.WholeConstituentLaserVolumeStage.exists_power_of_pos
#assert_axioms AlgebraicComplexity.WholeConstituentLaserVolumeSequenceData.ofFiniteStage
