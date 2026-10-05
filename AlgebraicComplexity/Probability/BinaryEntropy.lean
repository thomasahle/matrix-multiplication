/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Probability.Entropy
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Tactic.Linarith

/-!
# Boolean probability vectors and binary entropy

This small adapter identifies the repository's Shannon entropy of a Boolean `ProbabilityVector`
with Mathlib's `Real.binEntropy`.  It deliberately sits outside the lightweight entropy core:
clients that only need finite entropy sums do not have to import the analytic monotonicity and
calculus developed for the binary entropy function.
-/

namespace AlgebraicComplexity.ProbabilityVector

/-- The entropy in bits of a Boolean probability vector is Mathlib's binary entropy of its
`true` mass, divided by `log 2`.

Proof sketch: the total-mass identity rewrites the `false` weight as one minus the `true` weight;
the two summands in finite Shannon entropy are then exactly the defining two summands of
`Real.binEntropy`. -/
theorem entropyBits_bool_eq_binEntropy_weight_true_div_log_two
    (p : ProbabilityVector Bool) :
    p.entropyBits = Real.binEntropy (p.weight true) / Real.log 2 := by
  have hfalse : p.weight false = 1 - p.weight true := by
    have htotal := p.total
    rw [Fintype.sum_bool] at htotal
    linarith
  unfold entropyBits entropy
  rw [Fintype.sum_bool, hfalse, Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]

end AlgebraicComplexity.ProbabilityVector
