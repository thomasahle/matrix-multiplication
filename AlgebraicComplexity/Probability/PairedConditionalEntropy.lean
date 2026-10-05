/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Probability.Coupling
import AlgebraicComplexity.Probability.SupportRestrictionDataProcessing

/-!
# Conditional entropy for paired finite laws

This lightweight module proves that after revealing one deterministic cell of each coordinate,
the remaining entropy of a coupled pair is at most the sum of the two one-coordinate conditional
entropies:

`H(D, E | C, F) ≤ H(D | C) + H(E | F)`.

The proof is deterministic KL data processing from the joint law and the product of its marginals.
Channel calculus and the stronger mutual-information identities remain downstream in
`Probability/TwoLetter.lean`.

The inequality is a paper-independent auxiliary for the exact/pooled-cell compatibility count in
Claim 6.18 of Alman--Duan--Vassilevska Williams--Xu--Xu--Zhou,
*More Asymmetry Yields Faster Matrix Multiplication*
(`papers/sources/2404.16349/constituent.tex`, lines 404--432).  That paper does not state this
two-coordinate formulation separately.
-/

set_option autoImplicit false

namespace AlgebraicComplexity

universe u v w x

namespace ProbabilityVector

variable {D : Type u} {E : Type v} [Fintype D] [Fintype E]

/-- Conditional entropy of paired occurrences after revealing both cells is at most the sum of
the two one-letter conditional entropies.

Proof sketch: compare the joint law with the product of its marginals.  Applying deterministic KL
data processing to the pair of revealed cells says that the mutual-information entropy gap cannot
increase.  Expanding the two KL divergences as entropy gaps and rearranging yields the conditional
entropy inequality; division by `log 2` converts it to bits. -/
theorem IsCoupling.pairConditionalEntropyBits_le_add
    [DecidableEq D] [DecidableEq E]
    {C : Type w} {F : Type x} [Fintype C] [Fintype F]
    [DecidableEq C] [DecidableEq F]
    {joint : ProbabilityVector (D × E)}
    {left : ProbabilityVector D} {right : ProbabilityVector E}
    (h : joint.IsCoupling left right) (leftCell : D → C) (rightCell : E → F) :
    joint.conditionalEntropyBits (fun de ↦ (leftCell de.1, rightCell de.2)) ≤
      left.conditionalEntropyBits leftCell + right.conditionalEntropyBits rightCell := by
  let cellPair : ProbabilityVector (C × F) :=
    joint.pushforward fun de ↦ (leftCell de.1, rightCell de.2)
  let leftCells : ProbabilityVector C := left.pushforward leftCell
  let rightCells : ProbabilityVector F := right.pushforward rightCell
  have hcells : cellPair.IsCoupling leftCells rightCells :=
    h.pushforward_prodMap leftCell rightCell
  have hreference :
      (left.product right).pushforward
          (fun de ↦ (leftCell de.1, rightCell de.2)) =
        leftCells.product rightCells := by
    exact pushforward_product_prodMap left right leftCell rightCell
  have hdata := klDiv_pushforward_le_of_absoluteContinuity
    (fun de ↦ (leftCell de.1, rightCell de.2)) joint (left.product right)
      h.isAbsolutelyContinuous_product
  rw [hreference] at hdata
  change cellPair.klDiv (leftCells.product rightCells) ≤
    joint.klDiv (left.product right) at hdata
  rw [hcells.klDiv_product_eq_entropy_gap,
    h.klDiv_product_eq_entropy_gap] at hdata
  have hnats :
      joint.entropy - cellPair.entropy ≤
        (left.entropy - leftCells.entropy) +
          (right.entropy - rightCells.entropy) := by
    linarith
  unfold conditionalEntropyBits conditionalEntropy
  rw [← add_div]
  exact div_le_div_of_nonneg_right hnats
    (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le

end ProbabilityVector

end AlgebraicComplexity
