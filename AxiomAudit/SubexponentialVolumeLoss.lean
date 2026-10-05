/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.SubexponentialVolumeLoss
import AxiomAudit.Command

/-!
# Axiom audit for subexponential volume-loss absorption
-/

open AlgebraicComplexity

#assert_axioms Growth.Subexponential.exists_ge_pos_log_le_mul
#assert_axioms SubexponentialLaserVolumeLossSequence.toUniformLaserVolumeBaseExtraction
#assert_axioms SubexponentialLaserVolumeLossSequence.hasLaserExtractionRate
#assert_axioms SubexponentialLaserVolumeLossSequence.hasLaserExtractionRate_bits
