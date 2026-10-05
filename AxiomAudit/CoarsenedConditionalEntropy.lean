/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Probability.CoarsenedConditionalEntropy
import AxiomAudit.Command

/-! Focused trust audit for `AlgebraicComplexity.Probability.CoarsenedConditionalEntropy`: the
data-processing inequality `H(S,T) <= H(T) + H(S | coarse T)` for `ProbabilityVector`, in nats
and in bits, together with the additive form used when a separate upper bound on the target
entropy is available. -/

set_option autoImplicit false

open AlgebraicComplexity

#assert_axioms ProbabilityVector.entropy_le_right_add_conditionalEntropy_coarsenedRight
#assert_axioms ProbabilityVector.entropyBits_le_right_add_conditionalEntropyBits_coarsenedRight
#assert_axioms ProbabilityVector.entropyBits_le_add_of_right_le_of_coarsenedConditional_le
