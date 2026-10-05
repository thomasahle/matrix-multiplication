/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Probability.CrossEntropyDefs
import AlgebraicComplexity.Probability.KullbackLeiblerBasic

/-!
# Cross entropy for finite probability vectors

Cross entropy is the numerically stable way to evaluate an entropy plus a KL divergence.  The
identity in this file avoids subtracting two nearby entropy expressions in certificate checkers.
-/

namespace AlgebraicComplexity

universe u

namespace ProbabilityVector

variable {I : Type u} [Fintype I]

/-- Entropy plus KL divergence is cross entropy. -/
theorem entropy_add_klDiv_eq_crossEntropy
    (p q : ProbabilityVector I) (hq : ∀ i, 0 < q.weight i) :
    p.entropy + p.klDiv q = p.crossEntropy q := by
  rw [klDiv_eq_neg_entropy_sub_expectation_log p q hq]
  unfold crossEntropy
  ring

/-- Base-two cross-entropy identity used by exact laser-method certificates. -/
theorem entropyBits_add_klDivBits_eq_crossEntropyBits
    (p q : ProbabilityVector I) (hq : ∀ i, 0 < q.weight i) :
    p.entropyBits + p.klDivBits q = p.crossEntropyBits q := by
  unfold entropyBits klDivBits crossEntropyBits
  rw [← add_div, entropy_add_klDiv_eq_crossEntropy p q hq]

/-- Rearranged form: KL divergence is the cross-entropy gap. -/
theorem klDivBits_eq_crossEntropyBits_sub_entropyBits
    (p q : ProbabilityVector I) (hq : ∀ i, 0 < q.weight i) :
    p.klDivBits q = p.crossEntropyBits q - p.entropyBits := by
  linarith [entropyBits_add_klDivBits_eq_crossEntropyBits p q hq]

end ProbabilityVector

end AlgebraicComplexity
