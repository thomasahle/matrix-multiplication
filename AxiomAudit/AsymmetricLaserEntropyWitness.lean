/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import MatrixMultiplication.AsymmetricLaserEntropyWitness

/-!
# Audit of arbitrary-denominator finite-law entropy enclosures

Checks both sign directions and the zero-aware normalization identity needed by
[duan2023faster], `global_value.tex:286-309,332-378`.
-/

set_option autoImplicit false

#assert_axioms AlgebraicComplexity.AsymmetricLaserData.FiniteLaw.entropyBits_eq_log_denominator_sub
#assert_axioms AlgebraicComplexity.AsymmetricLaserData.FiniteLaw.entropyLower
#assert_axioms AlgebraicComplexity.AsymmetricLaserData.FiniteLaw.entropyUpper
#assert_axioms AlgebraicComplexity.AsymmetricLaserData.FiniteLaw.entropyLower_le
#assert_axioms AlgebraicComplexity.AsymmetricLaserData.FiniteLaw.le_entropyUpper
