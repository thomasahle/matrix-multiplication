/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Probability.Entropy
import AlgebraicComplexity.Probability.JointMarginal
import Mathlib.Algebra.BigOperators.Field

/-!
# Entropy chain rules for finite probability vectors

This module proves the elementary identities for the concrete `ProbabilityVector.joint` and
`ProbabilityVector.product` constructors.  They are useful at certificate boundaries because
they expose conditional entropy as an explicit weighted sum of child entropies, without passing
through a measure-theoretic probability API.
-/

open scoped BigOperators

namespace AlgebraicComplexity

universe u v

namespace ProbabilityVector

variable {I : Type u} {J : Type v} [Fintype I] [Fintype J]

/-- Entropy chain rule for a finite joint law. -/
theorem entropy_joint
    (p : ProbabilityVector I) (family : I → ProbabilityVector J) :
    (p.joint family).entropy =
      p.entropy + ∑ i, p.weight i * (family i).entropy := by
  classical
  unfold entropy
  rw [Fintype.sum_prod_type]
  simp_rw [joint_weight, Real.negMulLog_mul]
  calc
    (∑ i, ∑ j,
        ((family i).weight j * Real.negMulLog (p.weight i) +
          p.weight i * Real.negMulLog ((family i).weight j))) =
        (∑ i, Real.negMulLog (p.weight i)) +
          ∑ i, p.weight i * ∑ j, Real.negMulLog ((family i).weight j) := by
      simp_rw [Finset.sum_add_distrib]
      congr 1
      · apply Finset.sum_congr rfl
        intro i _
        rw [← Finset.sum_mul, (family i).total, one_mul]
      · apply Finset.sum_congr rfl
        intro i _
        rw [Finset.mul_sum]
    _ = (∑ i, Real.negMulLog (p.weight i)) +
          ∑ i, p.weight i * (family i).entropy := by rfl

/-- Conditional entropy of a joint law after revealing its outer coordinate. -/
theorem conditionalEntropy_joint_fst [DecidableEq I]
    (p : ProbabilityVector I) (family : I → ProbabilityVector J) :
    (p.joint family).conditionalEntropy Prod.fst =
      ∑ i, p.weight i * (family i).entropy := by
  rw [conditionalEntropy, pushforward_joint_fst, entropy_joint]
  ring

/-- Base-two conditional-entropy chain rule. -/
theorem conditionalEntropyBits_joint_fst [DecidableEq I]
    (p : ProbabilityVector I) (family : I → ProbabilityVector J) :
    (p.joint family).conditionalEntropyBits Prod.fst =
      ∑ i, p.weight i * (family i).entropyBits := by
  unfold conditionalEntropyBits entropyBits
  rw [conditionalEntropy_joint_fst, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Entropy is additive on independent finite products. -/
theorem entropy_product
    (p : ProbabilityVector I) (q : ProbabilityVector J) :
    (p.product q).entropy = p.entropy + q.entropy := by
  let family : I → ProbabilityVector J := fun _ ↦ q
  change (p.joint family).entropy = p.entropy + q.entropy
  rw [entropy_joint]
  change p.entropy + ∑ i, p.weight i * q.entropy = p.entropy + q.entropy
  rw [← Finset.sum_mul, p.total, one_mul]

/-- Base-two entropy is additive on independent products. -/
theorem entropyBits_product
    (p : ProbabilityVector I) (q : ProbabilityVector J) :
    (p.product q).entropyBits = p.entropyBits + q.entropyBits := by
  unfold entropyBits
  rw [entropy_product, add_div]

end ProbabilityVector

end AlgebraicComplexity
