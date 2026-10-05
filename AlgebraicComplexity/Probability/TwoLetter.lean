/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Probability.Coupling
import AlgebraicComplexity.Probability.MarginalProjection
import AlgebraicComplexity.Probability.PairedConditionalEntropy
import AlgebraicComplexity.Probability.SupportRestriction
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Couplings and tensorization of finite marginal fibers

This module supplies a paper-independent finite-probability interface for grouping two letters
while keeping their downstream statistics fixed.  Its main ingredients are:

* exact transport of both marginals of a coupling through arbitrary deterministic interfaces;
* recovery of the one-letter laws from their independent product;
* entropy subadditivity for an arbitrary finite coupling, including sparse marginals; and
* tensorization of maximum-entropy representatives for fibers cut out by three finite features.

The final entropy-deficit and retained-rate identities isolate the formal reason that enlarging a
one-letter optimization to correlated two-letter couplings cannot lose the independent-product
candidate.
-/

open scoped BigOperators

namespace AlgebraicComplexity

universe u v w x y z u' v'

namespace ProbabilityVector

variable {D : Type u} {E : Type v} [Fintype D] [Fintype E]

/-! ## Pushforwards and finite couplings -/

/-! Pushforward composition, finite couplings, product laws, and entropy subadditivity are
provided by `Probability/Coupling.lean`. -/

/-! ## Independent channels on correlated letters -/

/-- Mutual information of a finite joint law, in nats. -/
noncomputable def mutualInformation
    [DecidableEq D] [DecidableEq E] (joint : ProbabilityVector (D × E)) : ℝ :=
  (joint.pushforward Prod.fst).entropy +
    (joint.pushforward Prod.snd).entropy - joint.entropy

/-- Mutual information of a finite joint law, in bits. -/
noncomputable def mutualInformationBits
    [DecidableEq D] [DecidableEq E] (joint : ProbabilityVector (D × E)) : ℝ :=
  (joint.pushforward Prod.fst).entropyBits +
    (joint.pushforward Prod.snd).entropyBits - joint.entropyBits

/-- For a coupling, mutual information is its entropy-subadditivity gap. -/
theorem IsCoupling.mutualInformation_eq_entropy_gap
    [DecidableEq D] [DecidableEq E]
    {joint : ProbabilityVector (D × E)}
    {left : ProbabilityVector D} {right : ProbabilityVector E}
    (h : joint.IsCoupling left right) :
    joint.mutualInformation = left.entropy + right.entropy - joint.entropy := by
  unfold mutualInformation
  rw [h.1, h.2]

/-- Coupling mutual information is KL divergence from the independent product of its marginals. -/
theorem IsCoupling.mutualInformation_eq_klDiv_product
    [DecidableEq D] [DecidableEq E]
    {joint : ProbabilityVector (D × E)}
    {left : ProbabilityVector D} {right : ProbabilityVector E}
    (h : joint.IsCoupling left right) :
    joint.mutualInformation = joint.klDiv (left.product right) := by
  rw [h.mutualInformation_eq_entropy_gap, h.klDiv_product_eq_entropy_gap]

/-- Mutual information in bits is the nats quantity divided by `log 2`. -/
theorem mutualInformationBits_eq_div
    [DecidableEq D] [DecidableEq E] (joint : ProbabilityVector (D × E)) :
    joint.mutualInformationBits = joint.mutualInformation / Real.log 2 := by
  unfold mutualInformationBits mutualInformation entropyBits
  rw [sub_div, add_div]

/-- Product of two finite channels, applied independently to the two coordinates. -/
def productChannel
    {I : Type u} {J : Type v} {O : Type w} {P : Type x}
    [Fintype I] [Fintype J] [Fintype O] [Fintype P]
    (leftChannel : I → ProbabilityVector O)
    (rightChannel : J → ProbabilityVector P) :
    I × J → ProbabilityVector (O × P) :=
  fun ij ↦ (leftChannel ij.1).product (rightChannel ij.2)

/-- Applying product input to a product channel recovers the product of the one-letter outputs. -/
theorem mixture_product_productChannel
    {I : Type u} {J : Type v} {O : Type w} {P : Type x}
    [Fintype I] [Fintype J] [Fintype O] [Fintype P]
    (left : ProbabilityVector I) (right : ProbabilityVector J)
    (leftChannel : I → ProbabilityVector O)
    (rightChannel : J → ProbabilityVector P) :
    (left.product right).mixture (productChannel leftChannel rightChannel) =
      (left.mixture leftChannel).product (right.mixture rightChannel) := by
  classical
  ext op
  rcases op with ⟨o, p⟩
  simp only [mixture_weight, product_weight, Fintype.sum_prod_type, productChannel]
  calc
    (∑ i, ∑ j,
        (left.weight i * right.weight j) *
          ((leftChannel i).weight o * (rightChannel j).weight p)) =
        ∑ i, (left.weight i * (leftChannel i).weight o) *
          ∑ j, right.weight j * (rightChannel j).weight p := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = (∑ i, left.weight i * (leftChannel i).weight o) *
          ∑ j, right.weight j * (rightChannel j).weight p := by
      rw [Finset.sum_mul]

/-- A product channel sends a coupling to a coupling of the two one-letter channel outputs. -/
theorem IsCoupling.mixture_productChannel
    [DecidableEq D] [DecidableEq E]
    {O : Type w} {P : Type x} [Fintype O] [Fintype P]
    [DecidableEq O] [DecidableEq P]
    {joint : ProbabilityVector (D × E)}
    {left : ProbabilityVector D} {right : ProbabilityVector E}
    (h : joint.IsCoupling left right)
    (leftChannel : D → ProbabilityVector O)
    (rightChannel : E → ProbabilityVector P) :
    (joint.mixture (productChannel leftChannel rightChannel)).IsCoupling
      (left.mixture leftChannel) (right.mixture rightChannel) := by
  constructor
  · rw [pushforward_mixture]
    simp only [productChannel, pushforward_product_fst]
    ext o
    simp only [mixture_weight]
    change joint.expectation (fun de ↦ (leftChannel de.1).weight o) =
      left.expectation (fun d ↦ (leftChannel d).weight o)
    have hleft := h.expectation_left (fun d ↦ (leftChannel d).weight o)
    unfold Function.comp at hleft
    exact hleft
  · rw [pushforward_mixture]
    simp only [productChannel, pushforward_product_snd]
    ext p
    simp only [mixture_weight]
    change joint.expectation (fun de ↦ (rightChannel de.2).weight p) =
      right.expectation (fun e ↦ (rightChannel e).weight p)
    have hright := h.expectation_right (fun e ↦ (rightChannel e).weight p)
    unfold Function.comp at hright
    exact hright

/-- Expected conditional entropy of a finite channel. -/
noncomputable def channelEntropyLoss
    {I : Type u} {O : Type v} [Fintype I] [Fintype O]
    (input : ProbabilityVector I) (channel : I → ProbabilityVector O) : ℝ :=
  input.expectation fun i ↦ (channel i).entropy

/-- Base-two expected conditional entropy of a finite channel. -/
noncomputable def channelEntropyLossBits
    {I : Type u} {O : Type v} [Fintype I] [Fintype O]
    (input : ProbabilityVector I) (channel : I → ProbabilityVector O) : ℝ :=
  input.expectation fun i ↦ (channel i).entropyBits

/-- `channelEntropyLoss` is the ordinary conditional entropy of the channel output after the
input coordinate is revealed. -/
theorem channelEntropyLoss_eq_joint_conditionalEntropy
    {I : Type u} {O : Type v} [Fintype I] [Fintype O] [DecidableEq I]
    (input : ProbabilityVector I) (channel : I → ProbabilityVector O) :
    channelEntropyLoss input channel =
      (input.joint channel).conditionalEntropy Prod.fst := by
  rw [conditionalEntropy_joint_fst]
  rfl

/-- Base-two conditional-entropy identification. -/
theorem channelEntropyLossBits_eq_joint_conditionalEntropyBits
    {I : Type u} {O : Type v} [Fintype I] [Fintype O] [DecidableEq I]
    (input : ProbabilityVector I) (channel : I → ProbabilityVector O) :
    channelEntropyLossBits input channel =
      (input.joint channel).conditionalEntropyBits Prod.fst := by
  rw [conditionalEntropyBits_joint_fst]
  rfl

/-- Conditional entropy loss is additive for independent channels even when their inputs are
correlated, provided the input marginals are fixed. -/
theorem IsCoupling.channelEntropyLoss_productChannel
    [DecidableEq D] [DecidableEq E]
    {O : Type w} {P : Type x} [Fintype O] [Fintype P]
    {joint : ProbabilityVector (D × E)}
    {left : ProbabilityVector D} {right : ProbabilityVector E}
    (h : joint.IsCoupling left right)
    (leftChannel : D → ProbabilityVector O)
    (rightChannel : E → ProbabilityVector P) :
    channelEntropyLoss joint (productChannel leftChannel rightChannel) =
      channelEntropyLoss left leftChannel + channelEntropyLoss right rightChannel := by
  unfold channelEntropyLoss productChannel
  simp_rw [entropy_product]
  rw [expectation_add]
  congr 1
  · have hleft := h.expectation_left (fun d ↦ (leftChannel d).entropy)
    unfold Function.comp at hleft
    exact hleft
  · have hright := h.expectation_right (fun e ↦ (rightChannel e).entropy)
    unfold Function.comp at hright
    exact hright

/-- Base-two conditional entropy loss is likewise additive for independent channels. -/
theorem IsCoupling.channelEntropyLossBits_productChannel
    [DecidableEq D] [DecidableEq E]
    {O : Type w} {P : Type x} [Fintype O] [Fintype P]
    {joint : ProbabilityVector (D × E)}
    {left : ProbabilityVector D} {right : ProbabilityVector E}
    (h : joint.IsCoupling left right)
    (leftChannel : D → ProbabilityVector O)
    (rightChannel : E → ProbabilityVector P) :
    channelEntropyLossBits joint (productChannel leftChannel rightChannel) =
      channelEntropyLossBits left leftChannel +
        channelEntropyLossBits right rightChannel := by
  unfold channelEntropyLossBits productChannel
  simp_rw [entropyBits_product]
  rw [expectation_add]
  congr 1
  · have hleft := h.expectation_left (fun d ↦ (leftChannel d).entropyBits)
    unfold Function.comp at hleft
    exact hleft
  · have hright := h.expectation_right (fun e ↦ (rightChannel e).entropyBits)
    unfold Function.comp at hright
    exact hright

/-- Using the same channel preserves absolute continuity of two input laws. -/
theorem IsAbsolutelyContinuous.joint_sameChannel
    {I : Type u} {O : Type v} [Fintype I] [Fintype O]
    {input reference : ProbabilityVector I}
    (hac : input.IsAbsolutelyContinuous reference)
    (channel : I → ProbabilityVector O) :
    (input.joint channel).IsAbsolutelyContinuous (reference.joint channel) := by
  rintro ⟨i, o⟩ hzero
  simp only [joint_weight] at hzero ⊢
  rcases mul_eq_zero.mp hzero with hreference | hchannel
  · simp [hac i hreference]
  · simp [hchannel]

/-- Attaching the same finite conditional channel to two laws preserves their KL divergence. -/
theorem klDiv_joint_sameChannel
    {I : Type u} {O : Type v} [Fintype I] [Fintype O]
    (input reference : ProbabilityVector I)
    (channel : I → ProbabilityVector O)
    (hac : input.IsAbsolutelyContinuous reference) :
    (input.joint channel).klDiv (reference.joint channel) =
      input.klDiv reference := by
  classical
  unfold klDiv
  rw [Fintype.sum_prod_type]
  simp only [joint_weight]
  calc
    (∑ i, ∑ o,
        (input.weight i * (channel i).weight o) *
          Real.log
            ((input.weight i * (channel i).weight o) /
              (reference.weight i * (channel i).weight o))) =
        ∑ i, ∑ o, (channel i).weight o *
          (input.weight i * Real.log (input.weight i / reference.weight i)) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro o _
      by_cases hchannel : (channel i).weight o = 0
      · simp [hchannel]
      by_cases hinput : input.weight i = 0
      · simp [hinput]
      have hreference : reference.weight i ≠ 0 := by
        intro href
        exact hinput (hac i href)
      have hratio :
          (input.weight i * (channel i).weight o) /
              (reference.weight i * (channel i).weight o) =
            input.weight i / reference.weight i := by
        field_simp
      rw [hratio]
      ring
    _ = ∑ i, (∑ o, (channel i).weight o) *
          (input.weight i * Real.log (input.weight i / reference.weight i)) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_mul]
    _ = ∑ i, input.weight i *
          Real.log (input.weight i / reference.weight i) := by
      simp_rw [(channel _).total, one_mul]

/-- KL data processing through an arbitrary finite stochastic channel, allowing sparse reference
laws under the exact absolute-continuity hypothesis. -/
theorem klDiv_mixture_le
    {I : Type u} {O : Type v} [Fintype I] [Fintype O] [DecidableEq O]
    (input reference : ProbabilityVector I)
    (channel : I → ProbabilityVector O)
    (hac : input.IsAbsolutelyContinuous reference) :
    (input.mixture channel).klDiv (reference.mixture channel) ≤
      input.klDiv reference := by
  have hdata := klDiv_pushforward_le_of_absoluteContinuity
    Prod.snd (input.joint channel) (reference.joint channel)
      (hac.joint_sameChannel channel)
  rw [pushforward_joint_snd, pushforward_joint_snd,
    klDiv_joint_sameChannel input reference channel hac] at hdata
  exact hdata

/-- Stochastic-channel KL data processing in bits. -/
theorem klDivBits_mixture_le
    {I : Type u} {O : Type v} [Fintype I] [Fintype O] [DecidableEq O]
    (input reference : ProbabilityVector I)
    (channel : I → ProbabilityVector O)
    (hac : input.IsAbsolutelyContinuous reference) :
    (input.mixture channel).klDivBits (reference.mixture channel) ≤
      input.klDivBits reference := by
  unfold klDivBits
  exact div_le_div_of_nonneg_right (klDiv_mixture_le input reference channel hac)
    (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le

/-- Independent application of two channels cannot increase mutual information between the two
letters. -/
theorem IsCoupling.mutualInformation_mixture_productChannel_le
    [DecidableEq D] [DecidableEq E]
    {O : Type w} {P : Type x} [Fintype O] [Fintype P]
    [DecidableEq O] [DecidableEq P]
    {joint : ProbabilityVector (D × E)}
    {left : ProbabilityVector D} {right : ProbabilityVector E}
    (h : joint.IsCoupling left right)
    (leftChannel : D → ProbabilityVector O)
    (rightChannel : E → ProbabilityVector P) :
    (joint.mixture (productChannel leftChannel rightChannel)).mutualInformation ≤
      joint.mutualInformation := by
  let output := joint.mixture (productChannel leftChannel rightChannel)
  let leftOutput := left.mixture leftChannel
  let rightOutput := right.mixture rightChannel
  have houtput : output.IsCoupling leftOutput rightOutput :=
    h.mixture_productChannel leftChannel rightChannel
  have hdata := klDiv_mixture_le joint (left.product right)
    (productChannel leftChannel rightChannel) h.isAbsolutelyContinuous_product
  calc
    output.mutualInformation = output.klDiv (leftOutput.product rightOutput) :=
      houtput.mutualInformation_eq_klDiv_product
    _ ≤ joint.klDiv (left.product right) := by
      simpa only [output, leftOutput, rightOutput,
        mixture_product_productChannel] using hdata
    _ = joint.mutualInformation := h.mutualInformation_eq_klDiv_product.symm

/-- Base-two mutual information also contracts under independent finite channels. -/
theorem IsCoupling.mutualInformationBits_mixture_productChannel_le
    [DecidableEq D] [DecidableEq E]
    {O : Type w} {P : Type x} [Fintype O] [Fintype P]
    [DecidableEq O] [DecidableEq P]
    {joint : ProbabilityVector (D × E)}
    {left : ProbabilityVector D} {right : ProbabilityVector E}
    (h : joint.IsCoupling left right)
    (leftChannel : D → ProbabilityVector O)
    (rightChannel : E → ProbabilityVector P) :
    (joint.mixture (productChannel leftChannel rightChannel)).mutualInformationBits ≤
      joint.mutualInformationBits := by
  rw [mutualInformationBits_eq_div, mutualInformationBits_eq_div]
  exact div_le_div_of_nonneg_right
    (h.mutualInformation_mixture_productChannel_le leftChannel rightChannel)
    (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le

/-- Applying deterministic interfaces separately to the two coordinates cannot increase their
mutual information. -/
theorem IsCoupling.mutualInformation_pushforward_prodMap_le
    [DecidableEq D] [DecidableEq E]
    {C : Type w} {F : Type x} [Fintype C] [Fintype F]
    [DecidableEq C] [DecidableEq F]
    {joint : ProbabilityVector (D × E)}
    {left : ProbabilityVector D} {right : ProbabilityVector E}
    (h : joint.IsCoupling left right) (leftCell : D → C) (rightCell : E → F) :
    (joint.pushforward (fun de ↦ (leftCell de.1, rightCell de.2))).mutualInformation ≤
      joint.mutualInformation := by
  let cellPair := joint.pushforward (fun de ↦ (leftCell de.1, rightCell de.2))
  let leftCells := left.pushforward leftCell
  let rightCells := right.pushforward rightCell
  have hcells : cellPair.IsCoupling leftCells rightCells :=
    h.pushforward_prodMap leftCell rightCell
  have hdata := klDiv_pushforward_le_of_absoluteContinuity
    (fun de ↦ (leftCell de.1, rightCell de.2)) joint (left.product right)
      h.isAbsolutelyContinuous_product
  calc
    cellPair.mutualInformation = cellPair.klDiv (leftCells.product rightCells) :=
      hcells.mutualInformation_eq_klDiv_product
    _ ≤ joint.klDiv (left.product right) := by
      simpa only [cellPair, leftCells, rightCells,
        pushforward_product_prodMap] using hdata
    _ = joint.mutualInformation := h.mutualInformation_eq_klDiv_product.symm

/-- Deterministic two-coordinate data processing in bits. -/
theorem IsCoupling.mutualInformationBits_pushforward_prodMap_le
    [DecidableEq D] [DecidableEq E]
    {C : Type w} {F : Type x} [Fintype C] [Fintype F]
    [DecidableEq C] [DecidableEq F]
    {joint : ProbabilityVector (D × E)}
    {left : ProbabilityVector D} {right : ProbabilityVector E}
    (h : joint.IsCoupling left right) (leftCell : D → C) (rightCell : E → F) :
    (joint.pushforward (fun de ↦ (leftCell de.1, rightCell de.2))).mutualInformationBits ≤
      joint.mutualInformationBits := by
  rw [mutualInformationBits_eq_div, mutualInformationBits_eq_div]
  exact div_le_div_of_nonneg_right
    (h.mutualInformation_pushforward_prodMap_le leftCell rightCell)
    (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le

/-- Base-two coupling mutual information is its base-two entropy-subadditivity gap. -/
theorem IsCoupling.mutualInformationBits_eq_entropy_gap
    [DecidableEq D] [DecidableEq E]
    {joint : ProbabilityVector (D × E)}
    {left : ProbabilityVector D} {right : ProbabilityVector E}
    (h : joint.IsCoupling left right) :
    joint.mutualInformationBits =
      left.entropyBits + right.entropyBits - joint.entropyBits := by
  unfold mutualInformationBits
  rw [h.1, h.2]

/-- General parent-output entropy lower bound for two possibly different input marginals and
channels. -/
theorem IsCoupling.add_outputEntropy_sub_mutualInformation_le_pairOutputEntropy
    [DecidableEq D] [DecidableEq E]
    {O : Type w} {P : Type x} [Fintype O] [Fintype P]
    [DecidableEq O] [DecidableEq P]
    {joint : ProbabilityVector (D × E)}
    {left : ProbabilityVector D} {right : ProbabilityVector E}
    (h : joint.IsCoupling left right)
    (leftChannel : D → ProbabilityVector O)
    (rightChannel : E → ProbabilityVector P) :
    (left.mixture leftChannel).entropy + (right.mixture rightChannel).entropy -
        joint.mutualInformation ≤
      (joint.mixture (productChannel leftChannel rightChannel)).entropy := by
  have hdata := h.mutualInformation_mixture_productChannel_le leftChannel rightChannel
  have houtput := h.mixture_productChannel leftChannel rightChannel
  rw [houtput.mutualInformation_eq_entropy_gap] at hdata
  linarith

/-- General base-two parent-output entropy lower bound. -/
theorem IsCoupling.add_outputEntropyBits_sub_mutualInformationBits_le_pairOutputEntropyBits
    [DecidableEq D] [DecidableEq E]
    {O : Type w} {P : Type x} [Fintype O] [Fintype P]
    [DecidableEq O] [DecidableEq P]
    {joint : ProbabilityVector (D × E)}
    {left : ProbabilityVector D} {right : ProbabilityVector E}
    (h : joint.IsCoupling left right)
    (leftChannel : D → ProbabilityVector O)
    (rightChannel : E → ProbabilityVector P) :
    (left.mixture leftChannel).entropyBits +
        (right.mixture rightChannel).entropyBits - joint.mutualInformationBits ≤
      (joint.mixture (productChannel leftChannel rightChannel)).entropyBits := by
  have hdata :=
    h.mutualInformationBits_mixture_productChannel_le leftChannel rightChannel
  have houtput := h.mixture_productChannel leftChannel rightChannel
  rw [houtput.mutualInformationBits_eq_entropy_gap] at hdata
  linarith

/-- For identical coarse marginals and conditionally independent uses of one channel, parent-pair
entropy loses at most the mutual information carried by the coarse pair. -/
theorem IsCoupling.two_mul_outputEntropy_sub_mutualInformation_le_pairOutputEntropy
    {C : Type u} {P : Type v} [Fintype C] [Fintype P]
    [DecidableEq C] [DecidableEq P]
    {coarsePair : ProbabilityVector (C × C)} {coarse : ProbabilityVector C}
    (h : coarsePair.IsCoupling coarse coarse)
    (channel : C → ProbabilityVector P) :
    2 * (coarse.mixture channel).entropy - coarsePair.mutualInformation ≤
      (coarsePair.mixture (productChannel channel channel)).entropy := by
  have hdata := h.mutualInformation_mixture_productChannel_le channel channel
  have houtput := h.mixture_productChannel channel channel
  rw [houtput.mutualInformation_eq_entropy_gap] at hdata
  linarith

/-- Base-two parent-pair entropy lower bound. -/
theorem IsCoupling.two_mul_outputEntropyBits_sub_mutualInformationBits_le_pairOutputEntropyBits
    {C : Type u} {P : Type v} [Fintype C] [Fintype P]
    [DecidableEq C] [DecidableEq P]
    {coarsePair : ProbabilityVector (C × C)} {coarse : ProbabilityVector C}
    (h : coarsePair.IsCoupling coarse coarse)
    (channel : C → ProbabilityVector P) :
    2 * (coarse.mixture channel).entropyBits - coarsePair.mutualInformationBits ≤
      (coarsePair.mixture (productChannel channel channel)).entropyBits := by
  have hdata := h.mutualInformationBits_mixture_productChannel_le channel channel
  have houtput := h.mixture_productChannel channel channel
  rw [houtput.mutualInformationBits_eq_entropy_gap] at hdata
  linarith

/-- With identical input marginals, paired conditional-entropy loss is exactly twice the
one-letter loss. -/
theorem IsCoupling.channelEntropyLoss_productChannel_eq_two
    {C : Type u} {P : Type v} [Fintype C] [Fintype P] [DecidableEq C]
    {coarsePair : ProbabilityVector (C × C)} {coarse : ProbabilityVector C}
    (h : coarsePair.IsCoupling coarse coarse)
    (channel : C → ProbabilityVector P) :
    channelEntropyLoss coarsePair (productChannel channel channel) =
      2 * channelEntropyLoss coarse channel := by
  rw [h.channelEntropyLoss_productChannel channel channel]
  ring

/-- Conservative inequality form of `channelEntropyLoss_productChannel_eq_two`. -/
theorem IsCoupling.channelEntropyLoss_productChannel_le_two
    {C : Type u} {P : Type v} [Fintype C] [Fintype P] [DecidableEq C]
    {coarsePair : ProbabilityVector (C × C)} {coarse : ProbabilityVector C}
    (h : coarsePair.IsCoupling coarse coarse)
    (channel : C → ProbabilityVector P) :
    channelEntropyLoss coarsePair (productChannel channel channel) ≤
      2 * channelEntropyLoss coarse channel :=
  (h.channelEntropyLoss_productChannel_eq_two channel).le

/-- Base-two paired conditional-entropy loss is exactly twice its one-letter value. -/
theorem IsCoupling.channelEntropyLossBits_productChannel_eq_two
    {C : Type u} {P : Type v} [Fintype C] [Fintype P] [DecidableEq C]
    {coarsePair : ProbabilityVector (C × C)} {coarse : ProbabilityVector C}
    (h : coarsePair.IsCoupling coarse coarse)
    (channel : C → ProbabilityVector P) :
    channelEntropyLossBits coarsePair (productChannel channel channel) =
      2 * channelEntropyLossBits coarse channel := by
  rw [h.channelEntropyLossBits_productChannel channel channel]
  ring

/-- Compatibility retained rate associated with an output-parent channel. -/
noncomputable def compatibilityRetainedRate
    {I : Type u} {O : Type v} [Fintype I] [Fintype O]
    (input : ProbabilityVector I) (channel : I → ProbabilityVector O) : ℝ :=
  (input.mixture channel).entropy - channelEntropyLoss input channel

/-- Base-two compatibility retained rate associated with an output-parent channel. -/
noncomputable def compatibilityRetainedRateBits
    {I : Type u} {O : Type v} [Fintype I] [Fintype O]
    (input : ProbabilityVector I) (channel : I → ProbabilityVector O) : ℝ :=
  (input.mixture channel).entropyBits - channelEntropyLossBits input channel

/-! ### Parent entropy and a separately supplied compatibility loss

In the compatibility application, the parent law and the pooled occurrence loss need not arise
from one common channel.  The following statements therefore keep the parent coupling and the
loss scalars separate. -/

/-- If a paired compatibility loss is at most twice its one-letter value, the retained parent
rate loses exactly the output mutual-information term and no more. -/
theorem IsCoupling.two_mul_entropy_sub_loss_sub_mutualInformation_le_entropy_sub_pairLoss
    {P : Type u} [Fintype P] [DecidableEq P]
    {parentPair : ProbabilityVector (P × P)} {parent : ProbabilityVector P}
    (h : parentPair.IsCoupling parent parent)
    (loss pairLoss : ℝ) (hloss : pairLoss ≤ 2 * loss) :
    2 * (parent.entropy - loss) - parentPair.mutualInformation ≤
      parentPair.entropy - pairLoss := by
  rw [h.mutualInformation_eq_entropy_gap]
  linarith

/-- Exact nats identity when the paired compatibility loss is exactly additive. -/
theorem IsCoupling.entropy_sub_pairLoss_eq_two_mul_entropy_sub_loss_sub_mutualInformation
    {P : Type u} [Fintype P] [DecidableEq P]
    {parentPair : ProbabilityVector (P × P)} {parent : ProbabilityVector P}
    (h : parentPair.IsCoupling parent parent)
    (loss pairLoss : ℝ) (hloss : pairLoss = 2 * loss) :
    parentPair.entropy - pairLoss =
      2 * (parent.entropy - loss) - parentPair.mutualInformation := by
  rw [h.mutualInformation_eq_entropy_gap, hloss]
  ring

/-- Base-two parent/loss inequality used by compatibility certificate checkers.  The only loss
hypothesis is the explicit subadditivity condition `pairLoss ≤ 2 * loss`. -/
theorem IsCoupling.two_mul_entropyBits_sub_loss_sub_mutualInformationBits_le_entropyBits_sub_pairLoss
    {P : Type u} [Fintype P] [DecidableEq P]
    {parentPair : ProbabilityVector (P × P)} {parent : ProbabilityVector P}
    (h : parentPair.IsCoupling parent parent)
    (loss pairLoss : ℝ) (hloss : pairLoss ≤ 2 * loss) :
    2 * (parent.entropyBits - loss) - parentPair.mutualInformationBits ≤
      parentPair.entropyBits - pairLoss := by
  rw [h.mutualInformationBits_eq_entropy_gap]
  linarith

/-- Exact base-two parent/loss identity when the paired loss is additive. -/
theorem IsCoupling.entropyBits_sub_pairLoss_eq_two_mul_entropyBits_sub_loss_sub_mutualInformationBits
    {P : Type u} [Fintype P] [DecidableEq P]
    {parentPair : ProbabilityVector (P × P)} {parent : ProbabilityVector P}
    (h : parentPair.IsCoupling parent parent)
    (loss pairLoss : ℝ) (hloss : pairLoss = 2 * loss) :
    parentPair.entropyBits - pairLoss =
      2 * (parent.entropyBits - loss) - parentPair.mutualInformationBits := by
  rw [h.mutualInformationBits_eq_entropy_gap, hloss]
  ring

/-- Adapter with a separate occurrence/cell channel supplying the compatibility loss.  The
parent coupling controls the entropy term, while `cellPair` controls the conditional-entropy
term; no identification of those two channels is assumed. -/
theorem IsCoupling.entropy_sub_productCellChannelLoss_eq_two_sub_outputMutualInformation
    {P : Type u} {C : Type v} {O : Type w}
    [Fintype P] [Fintype C] [Fintype O] [DecidableEq P] [DecidableEq C]
    {parentPair : ProbabilityVector (P × P)} {parent : ProbabilityVector P}
    (hparent : parentPair.IsCoupling parent parent)
    {cellPair : ProbabilityVector (C × C)} {cell : ProbabilityVector C}
    (hcell : cellPair.IsCoupling cell cell)
    (lossChannel : C → ProbabilityVector O) :
    parentPair.entropy -
        channelEntropyLoss cellPair (productChannel lossChannel lossChannel) =
      2 * (parent.entropy - channelEntropyLoss cell lossChannel) -
        parentPair.mutualInformation := by
  apply hparent.entropy_sub_pairLoss_eq_two_mul_entropy_sub_loss_sub_mutualInformation
  exact hcell.channelEntropyLoss_productChannel_eq_two lossChannel

/-- Base-two separate-channel adapter.  This is the direct abstract shape of a paired parent law
together with the pooled compatibility-cell conditional-entropy loss. -/
theorem IsCoupling.entropyBits_sub_productCellChannelLoss_eq_two_sub_outputMutualInformationBits
    {P : Type u} {C : Type v} {O : Type w}
    [Fintype P] [Fintype C] [Fintype O] [DecidableEq P] [DecidableEq C]
    {parentPair : ProbabilityVector (P × P)} {parent : ProbabilityVector P}
    (hparent : parentPair.IsCoupling parent parent)
    {cellPair : ProbabilityVector (C × C)} {cell : ProbabilityVector C}
    (hcell : cellPair.IsCoupling cell cell)
    (lossChannel : C → ProbabilityVector O) :
    parentPair.entropyBits -
        channelEntropyLossBits cellPair (productChannel lossChannel lossChannel) =
      2 * (parent.entropyBits - channelEntropyLossBits cell lossChannel) -
        parentPair.mutualInformationBits := by
  apply hparent.entropyBits_sub_pairLoss_eq_two_mul_entropyBits_sub_loss_sub_mutualInformationBits
  exact hcell.channelEntropyLossBits_productChannel_eq_two lossChannel

/-- Exact two-channel compatibility-rate identity in nats for the special case where one channel
supplies both the parent output and the compatibility loss.  The paper's pooled occurrence loss
generally requires the separate-channel adapter above. -/
theorem IsCoupling.compatibilityRetainedRate_eq_add_sub_outputMutualInformation
    [DecidableEq D] [DecidableEq E]
    {O : Type w} {P : Type x} [Fintype O] [Fintype P]
    [DecidableEq O] [DecidableEq P]
    {joint : ProbabilityVector (D × E)}
    {left : ProbabilityVector D} {right : ProbabilityVector E}
    (h : joint.IsCoupling left right)
    (leftChannel : D → ProbabilityVector O)
    (rightChannel : E → ProbabilityVector P) :
    compatibilityRetainedRate joint (productChannel leftChannel rightChannel) =
      compatibilityRetainedRate left leftChannel +
        compatibilityRetainedRate right rightChannel -
          (joint.mixture (productChannel leftChannel rightChannel)).mutualInformation := by
  have houtput := h.mixture_productChannel leftChannel rightChannel
  have hmi := houtput.mutualInformation_eq_entropy_gap
  have hloss := h.channelEntropyLoss_productChannel leftChannel rightChannel
  unfold compatibilityRetainedRate
  rw [hloss]
  linarith

/-- Exact base-two version of the common-channel special case. -/
theorem IsCoupling.compatibilityRetainedRateBits_eq_add_sub_outputMutualInformationBits
    [DecidableEq D] [DecidableEq E]
    {O : Type w} {P : Type x} [Fintype O] [Fintype P]
    [DecidableEq O] [DecidableEq P]
    {joint : ProbabilityVector (D × E)}
    {left : ProbabilityVector D} {right : ProbabilityVector E}
    (h : joint.IsCoupling left right)
    (leftChannel : D → ProbabilityVector O)
    (rightChannel : E → ProbabilityVector P) :
    compatibilityRetainedRateBits joint (productChannel leftChannel rightChannel) =
      compatibilityRetainedRateBits left leftChannel +
        compatibilityRetainedRateBits right rightChannel -
          (joint.mixture (productChannel leftChannel rightChannel)).mutualInformationBits := by
  have houtput := h.mixture_productChannel leftChannel rightChannel
  have hmi := houtput.mutualInformationBits_eq_entropy_gap
  have hloss := h.channelEntropyLossBits_productChannel leftChannel rightChannel
  unfold compatibilityRetainedRateBits
  rw [hloss]
  linarith

/-- For two identical marginals in the common-channel special case, the exact paired retained rate
is twice the one-letter rate minus the mutual information of the paired parent/output law. -/
theorem IsCoupling.compatibilityRetainedRate_eq_two_sub_outputMutualInformation
    {C : Type u} {P : Type v} [Fintype C] [Fintype P]
    [DecidableEq C] [DecidableEq P]
    {coarsePair : ProbabilityVector (C × C)} {coarse : ProbabilityVector C}
    (h : coarsePair.IsCoupling coarse coarse)
    (channel : C → ProbabilityVector P) :
    compatibilityRetainedRate coarsePair (productChannel channel channel) =
      2 * compatibilityRetainedRate coarse channel -
        (coarsePair.mixture (productChannel channel channel)).mutualInformation := by
  have hexact :=
    h.compatibilityRetainedRate_eq_add_sub_outputMutualInformation channel channel
  linarith

/-- Base-two exact identity used by paired compatibility certificate checkers.  Its output-law
expression is definitionally the paired parent law produced by independently applying `channel`
to the two coupled coarse states. -/
theorem IsCoupling.compatibilityRetainedRateBits_eq_two_sub_outputMutualInformationBits
    {C : Type u} {P : Type v} [Fintype C] [Fintype P]
    [DecidableEq C] [DecidableEq P]
    {coarsePair : ProbabilityVector (C × C)} {coarse : ProbabilityVector C}
    (h : coarsePair.IsCoupling coarse coarse)
    (channel : C → ProbabilityVector P) :
    compatibilityRetainedRateBits coarsePair (productChannel channel channel) =
      2 * compatibilityRetainedRateBits coarse channel -
        (coarsePair.mixture (productChannel channel channel)).mutualInformationBits := by
  have hexact :=
    h.compatibilityRetainedRateBits_eq_add_sub_outputMutualInformationBits channel channel
  linarith

/-- Conservative two-letter compatibility-rate theorem in nats.  Conditional independence of
the two channel uses is explicit in `productChannel`; without it, the loss identity need not hold. -/
theorem IsCoupling.two_mul_compatibilityRetainedRate_sub_mutualInformation_le
    {C : Type u} {P : Type v} [Fintype C] [Fintype P]
    [DecidableEq C] [DecidableEq P]
    {coarsePair : ProbabilityVector (C × C)} {coarse : ProbabilityVector C}
    (h : coarsePair.IsCoupling coarse coarse)
    (channel : C → ProbabilityVector P) :
    2 * compatibilityRetainedRate coarse channel - coarsePair.mutualInformation ≤
      compatibilityRetainedRate coarsePair (productChannel channel channel) := by
  have hparent :=
    h.two_mul_outputEntropy_sub_mutualInformation_le_pairOutputEntropy channel
  have hloss := h.channelEntropyLoss_productChannel_eq_two channel
  unfold compatibilityRetainedRate
  rw [hloss]
  linarith

/-- Conservative two-letter compatibility-rate theorem in bits:
`pairedRate ≥ 2 * oneLetterRate - I(coarsePair)`. -/
theorem IsCoupling.two_mul_compatibilityRetainedRateBits_sub_mutualInformationBits_le
    {C : Type u} {P : Type v} [Fintype C] [Fintype P]
    [DecidableEq C] [DecidableEq P]
    {coarsePair : ProbabilityVector (C × C)} {coarse : ProbabilityVector C}
    (h : coarsePair.IsCoupling coarse coarse)
    (channel : C → ProbabilityVector P) :
    2 * compatibilityRetainedRateBits coarse channel - coarsePair.mutualInformationBits ≤
      compatibilityRetainedRateBits coarsePair (productChannel channel channel) := by
  have hparent :=
    h.two_mul_outputEntropyBits_sub_mutualInformationBits_le_pairOutputEntropyBits channel
  have hloss := h.channelEntropyLossBits_productChannel_eq_two channel
  unfold compatibilityRetainedRateBits
  rw [hloss]
  linarith

/-- Unequal-marginal form of the conservative two-letter compatibility-rate theorem. -/
theorem IsCoupling.add_compatibilityRetainedRateBits_sub_mutualInformationBits_le
    [DecidableEq D] [DecidableEq E]
    {O : Type w} {P : Type x} [Fintype O] [Fintype P]
    [DecidableEq O] [DecidableEq P]
    {joint : ProbabilityVector (D × E)}
    {left : ProbabilityVector D} {right : ProbabilityVector E}
    (h : joint.IsCoupling left right)
    (leftChannel : D → ProbabilityVector O)
    (rightChannel : E → ProbabilityVector P) :
    compatibilityRetainedRateBits left leftChannel +
        compatibilityRetainedRateBits right rightChannel - joint.mutualInformationBits ≤
      compatibilityRetainedRateBits joint
        (productChannel leftChannel rightChannel) := by
  have hparent :=
    h.add_outputEntropyBits_sub_mutualInformationBits_le_pairOutputEntropyBits
      leftChannel rightChannel
  have hloss := h.channelEntropyLossBits_productChannel leftChannel rightChannel
  unfold compatibilityRetainedRateBits
  rw [hloss]
  linarith

/-! ### Exact paired compatibility-numerator offset

For the CW compatibility count, normalize the two labelled child occurrences to a probability
law `occurrence` and remember their unnormalized total mass separately.  Its one-letter numerator
is then `mass * H(occurrence | cell)`.  A two-letter construction may prescribe an exact coupling
of the two occurrence laws.  The paired numerator is the analogous conditional entropy after
revealing the pair of compatibility cells.

The paired numerator can be strictly smaller than the sum of the two one-letter numerators.  The
exact improvement is the mutual information between the full occurrences which is not already
visible from their cell labels.  This section proves that identity without identifying the
parent-output law with the occurrence law.
-/

/-- Exact conditional-entropy gap for a coupling after revealing deterministic cell labels.
The right side is nonnegative by deterministic data processing. -/
theorem IsCoupling.add_conditionalEntropyBits_sub_pair_eq_informationOffset
    [DecidableEq D] [DecidableEq E]
    {C : Type w} {F : Type x} [Fintype C] [Fintype F]
    [DecidableEq C] [DecidableEq F]
    {joint : ProbabilityVector (D × E)}
    {left : ProbabilityVector D} {right : ProbabilityVector E}
    (h : joint.IsCoupling left right) (leftCell : D → C) (rightCell : E → F) :
    left.conditionalEntropyBits leftCell + right.conditionalEntropyBits rightCell -
        joint.conditionalEntropyBits (fun de ↦ (leftCell de.1, rightCell de.2)) =
      joint.mutualInformationBits -
        (joint.pushforward
          (fun de ↦ (leftCell de.1, rightCell de.2))).mutualInformationBits := by
  have hcells := h.pushforward_prodMap leftCell rightCell
  rw [h.mutualInformationBits_eq_entropy_gap,
    hcells.mutualInformationBits_eq_entropy_gap]
  unfold conditionalEntropyBits conditionalEntropy entropyBits
  ring

/-- Information retained by the full paired occurrences beyond their paired compatibility-cell
labels.  This is exactly the compatible-degree numerator offset. -/
noncomputable def occurrenceInformationOffsetBits
    {D : Type u} {E : Type v} [Fintype D] [Fintype E]
    {C : Type w} {F : Type x} [Fintype C] [Fintype F]
    [DecidableEq D] [DecidableEq E] [DecidableEq C] [DecidableEq F]
    (joint : ProbabilityVector (D × E)) (leftCell : D → C) (rightCell : E → F) : ℝ :=
  joint.mutualInformationBits -
    (joint.pushforward
      (fun de ↦ (leftCell de.1, rightCell de.2))).mutualInformationBits

/-- The paired compatibility-numerator offset is always nonnegative. -/
theorem occurrenceInformationOffsetBits_nonneg
    {D : Type u} {E : Type v} [Fintype D] [Fintype E]
    [DecidableEq D] [DecidableEq E]
    {C : Type w} {F : Type x} [Fintype C] [Fintype F]
    [DecidableEq C] [DecidableEq F]
    (joint : ProbabilityVector (D × E)) (leftCell : D → C) (rightCell : E → F) :
    0 ≤ occurrenceInformationOffsetBits joint leftCell rightCell := by
  unfold occurrenceInformationOffsetBits
  have h := IsCoupling.marginals joint
  have hdata := h.mutualInformationBits_pushforward_prodMap_le leftCell rightCell
  linarith

/-- Exact compatibility-rate identity with separate parent and occurrence couplings.

The scalar `mass` is the unnormalized occurrence mass.  In the ordinary ordered-child CW model
it is two.  The theorem applies whenever the actual one- and two-letter compatibility numerators
are respectively `mass` times the displayed conditional entropies. -/
theorem IsCoupling.pairedCompatibilityRateBits_eq_add_sub_parentInformation_add_occurrenceOffset
    {PL : Type u} {PR : Type v} [Fintype PL] [Fintype PR]
    [DecidableEq PL] [DecidableEq PR]
    {parentPair : ProbabilityVector (PL × PR)}
    {parentLeft : ProbabilityVector PL} {parentRight : ProbabilityVector PR}
    (hparent : parentPair.IsCoupling parentLeft parentRight)
    {OD : Type w} {OE : Type x} [Fintype OD] [Fintype OE]
    [DecidableEq OD] [DecidableEq OE]
    {C : Type u'} {F : Type v'} [Fintype C] [Fintype F]
    [DecidableEq C] [DecidableEq F]
    {occurrencePair : ProbabilityVector (OD × OE)}
    {occurrenceLeft : ProbabilityVector OD} {occurrenceRight : ProbabilityVector OE}
    (hoccurrence : occurrencePair.IsCoupling occurrenceLeft occurrenceRight)
    (leftCell : OD → C) (rightCell : OE → F) (mass : ℝ) :
    parentPair.entropyBits - mass *
        occurrencePair.conditionalEntropyBits
          (fun de ↦ (leftCell de.1, rightCell de.2)) =
      (parentLeft.entropyBits - mass * occurrenceLeft.conditionalEntropyBits leftCell) +
        (parentRight.entropyBits - mass * occurrenceRight.conditionalEntropyBits rightCell) -
        parentPair.mutualInformationBits +
        mass * occurrenceInformationOffsetBits occurrencePair leftCell rightCell := by
  have hparentGap := hparent.mutualInformationBits_eq_entropy_gap
  have hoccurrenceGap :=
    hoccurrence.add_conditionalEntropyBits_sub_pair_eq_informationOffset
      leftCell rightCell
  have hparentEntropy :
      parentPair.entropyBits = parentLeft.entropyBits + parentRight.entropyBits -
        parentPair.mutualInformationBits := by
    linarith
  have hpairLoss :
      occurrencePair.conditionalEntropyBits
          (fun de ↦ (leftCell de.1, rightCell de.2)) =
        occurrenceLeft.conditionalEntropyBits leftCell +
          occurrenceRight.conditionalEntropyBits rightCell -
          (occurrencePair.mutualInformationBits -
            (occurrencePair.pushforward
              (fun de ↦ (leftCell de.1, rightCell de.2))).mutualInformationBits) := by
    linarith
  unfold occurrenceInformationOffsetBits
  rw [hparentEntropy, hpairLoss]
  ring

/-- Identical-letter, per-original-source-factor form of the exact compatibility-rate identity.
It exhibits both the parent mutual-information penalty and the nonnegative numerator offset. -/
theorem IsCoupling.identicalCompatibilityRateBits_perLetter_eq_old_sub_half_parentInformation_add_offset
    {P : Type u} [Fintype P] [DecidableEq P]
    {parentPair : ProbabilityVector (P × P)} {parent : ProbabilityVector P}
    (hparent : parentPair.IsCoupling parent parent)
    {O : Type v} [Fintype O] [DecidableEq O]
    {C : Type w} [Fintype C] [DecidableEq C]
    {occurrencePair : ProbabilityVector (O × O)}
    {occurrence : ProbabilityVector O}
    (hoccurrence : occurrencePair.IsCoupling occurrence occurrence)
    (cell : O → C) (mass : ℝ) :
    (parentPair.entropyBits - mass *
        occurrencePair.conditionalEntropyBits (fun oo ↦ (cell oo.1, cell oo.2))) / 2 =
      parent.entropyBits - mass * occurrence.conditionalEntropyBits cell -
        parentPair.mutualInformationBits / 2 +
        mass * occurrenceInformationOffsetBits occurrencePair cell cell / 2 := by
  have h :=
    hparent.pairedCompatibilityRateBits_eq_add_sub_parentInformation_add_occurrenceOffset
      hoccurrence cell cell mass
  linarith

/-- Conservative identical-letter statement: per source factor, paired compatibility retains at
least the old rate minus half the mutual information of the paired parent symbols. -/
theorem IsCoupling.oldRate_sub_half_parentInformation_le_pairedCompatibilityRateBits_perLetter
    {P : Type u} [Fintype P] [DecidableEq P]
    {parentPair : ProbabilityVector (P × P)} {parent : ProbabilityVector P}
    (hparent : parentPair.IsCoupling parent parent)
    {O : Type v} [Fintype O] [DecidableEq O]
    {C : Type w} [Fintype C] [DecidableEq C]
    {occurrencePair : ProbabilityVector (O × O)}
    {occurrence : ProbabilityVector O}
    (hoccurrence : occurrencePair.IsCoupling occurrence occurrence)
    (cell : O → C) (mass : ℝ) (hmass : 0 ≤ mass) :
    parent.entropyBits - mass * occurrence.conditionalEntropyBits cell -
        parentPair.mutualInformationBits / 2 ≤
      (parentPair.entropyBits - mass *
        occurrencePair.conditionalEntropyBits (fun oo ↦ (cell oo.1, cell oo.2))) / 2 := by
  rw [hparent.identicalCompatibilityRateBits_perLetter_eq_old_sub_half_parentInformation_add_offset
    hoccurrence cell mass]
  have hoffset := occurrenceInformationOffsetBits_nonneg occurrencePair cell cell
  nlinarith

end ProbabilityVector

/-! ## Cartesian compatibility at exponent level -/

/-- A target-entropy exponent after paying a compatible-degree exponent.  This scalar interface
deliberately makes no assumptions about how either exponent was obtained. -/
def cartesianRetainedExponent (targetEntropy compatibleDegree : ℝ) : ℝ :=
  targetEntropy - compatibleDegree

/-- Cartesian compatibility principle for two possibly different letters.  The target-pair
entropy may lose the information penalty, while Cartesian compatible degrees cost no more than
the sum of the two one-letter degree exponents. -/
theorem cartesianRetainedExponent_add_sub_information_le_pair
    {hP hQ hPair information dP dQ dPair : ℝ}
    (hEntropy : hPair = hP + hQ - information)
    (hDegree : dPair ≤ dP + dQ) :
    cartesianRetainedExponent hP dP + cartesianRetainedExponent hQ dQ - information ≤
      cartesianRetainedExponent hPair dPair := by
  unfold cartesianRetainedExponent
  linarith

/-- Lower-bound form allowing independently certified one-letter retained exponents. -/
theorem retainedExponents_add_sub_information_le_cartesianPair
    {hP hQ hPair information dP dQ dPair rP rQ : ℝ}
    (hEntropy : hPair = hP + hQ - information)
    (hDegree : dPair ≤ dP + dQ)
    (hrP : rP ≤ hP - dP) (hrQ : rQ ≤ hQ - dQ) :
    rP + rQ - information ≤ cartesianRetainedExponent hPair dPair := by
  have hcartesian := cartesianRetainedExponent_add_sub_information_le_pair
    hEntropy hDegree
  unfold cartesianRetainedExponent at hcartesian ⊢
  linarith

/-- Identical-letter Cartesian compatibility bound. -/
theorem two_mul_cartesianRetainedExponent_sub_information_le_pair
    {h hPair information d dPair : ℝ}
    (hEntropy : hPair = 2 * h - information)
    (hDegree : dPair ≤ 2 * d) :
    2 * cartesianRetainedExponent h d - information ≤
      cartesianRetainedExponent hPair dPair := by
  unfold cartesianRetainedExponent
  linarith

/-- Per-original-source-factor form of the identical-letter Cartesian compatibility bound. -/
theorem cartesianRetainedExponent_sub_half_information_le_pairPerSource
    {h hPair information d dPair : ℝ}
    (hEntropy : hPair = 2 * h - information)
    (hDegree : dPair ≤ 2 * d) :
    cartesianRetainedExponent h d - information / 2 ≤
      cartesianRetainedExponent hPair dPair / 2 := by
  have hpair := two_mul_cartesianRetainedExponent_sub_information_le_pair
    hEntropy hDegree
  linarith

/-! ## Three-feature marginal fibers -/

/-- Three deterministic finite features whose pushforwards define a marginal fiber. -/
structure ThreeFeatureSystem
    (S : Type u) (C : Type v) (L : Type w) (R : Type x) where
  coarse : S → C
  left : S → L
  right : S → R

namespace ThreeFeatureSystem

variable
    {S : Type u} {C : Type v} {L : Type w} {R : Type x}
    {T : Type y} {C' : Type z} {L' : Type u'} {R' : Type v'}
    [Fintype S] [Fintype C] [Fintype L] [Fintype R]
    [Fintype T] [Fintype C'] [Fintype L'] [Fintype R']
    [DecidableEq C] [DecidableEq L] [DecidableEq R]
    [DecidableEq C'] [DecidableEq L'] [DecidableEq R']

/-- Two laws lie in the same three-feature marginal fiber. -/
def SameFiber (F : ThreeFeatureSystem S C L R)
    (p q : ProbabilityVector S) : Prop :=
  p.pushforward F.coarse = q.pushforward F.coarse ∧
    p.pushforward F.left = q.pushforward F.left ∧
    p.pushforward F.right = q.pushforward F.right

@[refl] theorem sameFiber_refl (F : ThreeFeatureSystem S C L R)
    (p : ProbabilityVector S) : F.SameFiber p p :=
  ⟨rfl, rfl, rfl⟩

theorem SameFiber.symm {F : ThreeFeatureSystem S C L R}
    {p q : ProbabilityVector S} (h : F.SameFiber p q) : F.SameFiber q p :=
  ⟨h.1.symm, h.2.1.symm, h.2.2.symm⟩

theorem SameFiber.trans {F : ThreeFeatureSystem S C L R}
    {p q r : ProbabilityVector S} (hpq : F.SameFiber p q)
    (hqr : F.SameFiber q r) : F.SameFiber p r :=
  ⟨hpq.1.trans hqr.1, hpq.2.1.trans hqr.2.1, hpq.2.2.trans hqr.2.2⟩

/-- A law has maximum entropy in its three-feature marginal fiber. -/
def IsMaximumEntropy (F : ThreeFeatureSystem S C L R)
    (p : ProbabilityVector S) : Prop :=
  ∀ q : ProbabilityVector S, F.SameFiber q p → q.entropy ≤ p.entropy

/-- Pair the corresponding features of two letters. -/
def product (F : ThreeFeatureSystem S C L R)
    (G : ThreeFeatureSystem T C' L' R') :
    ThreeFeatureSystem (S × T) (C × C') (L × L') (R × R') where
  coarse st := (F.coarse st.1, G.coarse st.2)
  left st := (F.left st.1, G.left st.2)
  right st := (F.right st.1, G.right st.2)

/-- Equality of a paired-feature law forces equality of its first one-letter feature marginal. -/
private theorem fst_feature_eq_of_prodMap_eq
    [DecidableEq S] [DecidableEq T]
    (joint other : ProbabilityVector (S × T))
    {A : Type v} {B : Type w} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (f : S → A) (g : T → B)
    (h : joint.pushforward (fun st ↦ (f st.1, g st.2)) =
      other.pushforward (fun st ↦ (f st.1, g st.2))) :
    (joint.pushforward Prod.fst).pushforward f =
      (other.pushforward Prod.fst).pushforward f := by
  have hjoint := (ProbabilityVector.IsCoupling.marginals joint).pushforward_prodMap f g
  have hother := (ProbabilityVector.IsCoupling.marginals other).pushforward_prodMap f g
  calc
    (joint.pushforward Prod.fst).pushforward f =
        (joint.pushforward (fun st ↦ (f st.1, g st.2))).pushforward Prod.fst :=
      hjoint.1.symm
    _ = (other.pushforward (fun st ↦ (f st.1, g st.2))).pushforward Prod.fst := by
      rw [h]
    _ = (other.pushforward Prod.fst).pushforward f := hother.1

/-- Equality of a paired-feature law forces equality of its second one-letter feature marginal. -/
private theorem snd_feature_eq_of_prodMap_eq
    [DecidableEq S] [DecidableEq T]
    (joint other : ProbabilityVector (S × T))
    {A : Type v} {B : Type w} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (f : S → A) (g : T → B)
    (h : joint.pushforward (fun st ↦ (f st.1, g st.2)) =
      other.pushforward (fun st ↦ (f st.1, g st.2))) :
    (joint.pushforward Prod.snd).pushforward g =
      (other.pushforward Prod.snd).pushforward g := by
  have hjoint := (ProbabilityVector.IsCoupling.marginals joint).pushforward_prodMap f g
  have hother := (ProbabilityVector.IsCoupling.marginals other).pushforward_prodMap f g
  calc
    (joint.pushforward Prod.snd).pushforward g =
        (joint.pushforward (fun st ↦ (f st.1, g st.2))).pushforward Prod.snd :=
      hjoint.2.symm
    _ = (other.pushforward (fun st ↦ (f st.1, g st.2))).pushforward Prod.snd := by
      rw [h]
    _ = (other.pushforward Prod.snd).pushforward g := hother.2

/-- A product-feature fiber projects to the first one-letter feature fiber. -/
theorem SameFiber.fstMarginal
    [DecidableEq S] [DecidableEq T]
    {F : ThreeFeatureSystem S C L R} {G : ThreeFeatureSystem T C' L' R'}
    {joint reference : ProbabilityVector (S × T)}
    (h : (F.product G).SameFiber joint reference) :
    F.SameFiber (joint.pushforward Prod.fst) (reference.pushforward Prod.fst) := by
  exact
    ⟨fst_feature_eq_of_prodMap_eq joint reference F.coarse G.coarse h.1,
      fst_feature_eq_of_prodMap_eq joint reference F.left G.left h.2.1,
      fst_feature_eq_of_prodMap_eq joint reference F.right G.right h.2.2⟩

/-- A product-feature fiber projects to the second one-letter feature fiber. -/
theorem SameFiber.sndMarginal
    [DecidableEq S] [DecidableEq T]
    {F : ThreeFeatureSystem S C L R} {G : ThreeFeatureSystem T C' L' R'}
    {joint reference : ProbabilityVector (S × T)}
    (h : (F.product G).SameFiber joint reference) :
    G.SameFiber (joint.pushforward Prod.snd) (reference.pushforward Prod.snd) := by
  exact
    ⟨snd_feature_eq_of_prodMap_eq joint reference F.coarse G.coarse h.1,
      snd_feature_eq_of_prodMap_eq joint reference F.left G.left h.2.1,
      snd_feature_eq_of_prodMap_eq joint reference F.right G.right h.2.2⟩

/-- Products of laws in one-letter fibers lie in the corresponding product-feature fiber. -/
theorem sameFiber_product
    (F : ThreeFeatureSystem S C L R) (G : ThreeFeatureSystem T C' L' R')
    {p p' : ProbabilityVector S} {q q' : ProbabilityVector T}
    (hp : F.SameFiber p p') (hq : G.SameFiber q q') :
    (F.product G).SameFiber (p.product q) (p'.product q') := by
  constructor
  · change (p.product q).pushforward
        (fun st ↦ (F.coarse st.1, G.coarse st.2)) =
      (p'.product q').pushforward
        (fun st ↦ (F.coarse st.1, G.coarse st.2))
    rw [ProbabilityVector.pushforward_product_prodMap,
      ProbabilityVector.pushforward_product_prodMap, hp.1, hq.1]
  constructor
  · change (p.product q).pushforward
        (fun st ↦ (F.left st.1, G.left st.2)) =
      (p'.product q').pushforward
        (fun st ↦ (F.left st.1, G.left st.2))
    rw [ProbabilityVector.pushforward_product_prodMap,
      ProbabilityVector.pushforward_product_prodMap, hp.2.1, hq.2.1]
  · change (p.product q).pushforward
        (fun st ↦ (F.right st.1, G.right st.2)) =
      (p'.product q').pushforward
        (fun st ↦ (F.right st.1, G.right st.2))
    rw [ProbabilityVector.pushforward_product_prodMap,
      ProbabilityVector.pushforward_product_prodMap, hp.2.2, hq.2.2]

/-- Products of one-letter maximum-entropy representatives maximize entropy in the paired
three-feature fiber. -/
theorem isMaximumEntropy_product
    [DecidableEq S] [DecidableEq T]
    (F : ThreeFeatureSystem S C L R) (G : ThreeFeatureSystem T C' L' R')
    {p : ProbabilityVector S} {q : ProbabilityVector T}
    (hp : F.IsMaximumEntropy p) (hq : G.IsMaximumEntropy q) :
    (F.product G).IsMaximumEntropy (p.product q) := by
  intro joint hjoint
  have hleft := hjoint.fstMarginal
  have hright := hjoint.sndMarginal
  have hleft' : F.SameFiber (joint.pushforward Prod.fst) p := by
    simpa [SameFiber] using hleft
  have hright' : G.SameFiber (joint.pushforward Prod.snd) q := by
    simpa [SameFiber] using hright
  have hcoupling := ProbabilityVector.IsCoupling.marginals joint
  calc
    joint.entropy ≤
        (joint.pushforward Prod.fst).entropy +
          (joint.pushforward Prod.snd).entropy := hcoupling.entropy_le_add
    _ ≤ p.entropy + q.entropy := add_le_add
      (hp _ hleft') (hq _ hright')
    _ = (p.product q).entropy := ProbabilityVector.entropy_product p q |>.symm

/-! ## Combination-loss and retained-rate identities -/

/-- Entropy deficit from a chosen maximum-entropy representative.  This is the abstract
combination-loss quantity, independent of a particular tensor construction. -/
noncomputable def combinationLoss (_F : ThreeFeatureSystem S C L R)
    (maximum candidate : ProbabilityVector S) : ℝ :=
  maximum.entropy - candidate.entropy

/-- Combination loss is nonnegative when the first law is maximum entropy in the candidate's
feature fiber. -/
theorem combinationLoss_nonneg
    (F : ThreeFeatureSystem S C L R)
    {maximum candidate : ProbabilityVector S}
    (hmaximum : F.IsMaximumEntropy maximum)
    (hfiber : F.SameFiber candidate maximum) :
    0 ≤ F.combinationLoss maximum candidate := by
  unfold combinationLoss
  linarith [hmaximum candidate hfiber]

omit [Fintype C] [Fintype L] [Fintype R]
  [Fintype C'] [Fintype L'] [Fintype R']
  [DecidableEq C] [DecidableEq L] [DecidableEq R]
  [DecidableEq C'] [DecidableEq L'] [DecidableEq R'] in
/-- Independent products add their one-letter combination losses exactly. -/
theorem combinationLoss_product
    (F : ThreeFeatureSystem S C L R) (G : ThreeFeatureSystem T C' L' R')
    (maximumLeft candidateLeft : ProbabilityVector S)
    (maximumRight candidateRight : ProbabilityVector T) :
    (F.product G).combinationLoss
        (maximumLeft.product maximumRight) (candidateLeft.product candidateRight) =
      F.combinationLoss maximumLeft candidateLeft +
        G.combinationLoss maximumRight candidateRight := by
  unfold combinationLoss
  rw [ProbabilityVector.entropy_product, ProbabilityVector.entropy_product]
  ring

/-- Entropy of a prescribed directional interface minus combination loss.  Unlike raw entropy of
the candidate law, this is the abstract form of the paper's `H(candidate.pushforward W) - P`
branch. -/
noncomputable def directionalRetainedRate
    {A : Type y} [Fintype A] [DecidableEq A]
    (F : ThreeFeatureSystem S C L R) (interface : S → A)
    (maximum candidate : ProbabilityVector S) : ℝ :=
  (candidate.pushforward interface).entropy - F.combinationLoss maximum candidate

omit [Fintype C] [Fintype L] [Fintype R]
  [Fintype C'] [Fintype L'] [Fintype R']
  [DecidableEq C] [DecidableEq L] [DecidableEq R]
  [DecidableEq C'] [DecidableEq L'] [DecidableEq R'] in
/-- Independent products add directional retained rates exactly under the paired interface. -/
theorem directionalRetainedRate_product
    {A : Type u'} {B : Type v'} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (F : ThreeFeatureSystem S C L R) (G : ThreeFeatureSystem T C' L' R')
    (interfaceLeft : S → A) (interfaceRight : T → B)
    (maximumLeft candidateLeft : ProbabilityVector S)
    (maximumRight candidateRight : ProbabilityVector T) :
    (F.product G).directionalRetainedRate
        (fun st ↦ (interfaceLeft st.1, interfaceRight st.2))
        (maximumLeft.product maximumRight) (candidateLeft.product candidateRight) =
      F.directionalRetainedRate interfaceLeft maximumLeft candidateLeft +
        G.directionalRetainedRate interfaceRight maximumRight candidateRight := by
  unfold directionalRetainedRate
  rw [ProbabilityVector.pushforward_product_prodMap,
    ProbabilityVector.entropy_product, combinationLoss_product]
  ring

/-- Base-two combination loss, matching entropy-rate conventions in matrix-multiplication
optimization programs. -/
noncomputable def combinationLossBits (_F : ThreeFeatureSystem S C L R)
    (maximum candidate : ProbabilityVector S) : ℝ :=
  maximum.entropyBits - candidate.entropyBits

omit [Fintype C] [Fintype L] [Fintype R]
  [DecidableEq C] [DecidableEq L] [DecidableEq R] in
/-- Base-two combination loss is the nats quantity divided by `log 2`. -/
theorem combinationLossBits_eq_div
    (F : ThreeFeatureSystem S C L R)
    (maximum candidate : ProbabilityVector S) :
    F.combinationLossBits maximum candidate =
      F.combinationLoss maximum candidate / Real.log 2 := by
  unfold combinationLossBits combinationLoss ProbabilityVector.entropyBits
  rw [sub_div]

/-- Base-two directional-interface entropy minus base-two combination loss. -/
noncomputable def directionalRetainedRateBits
    {A : Type y} [Fintype A] [DecidableEq A]
    (F : ThreeFeatureSystem S C L R) (interface : S → A)
    (maximum candidate : ProbabilityVector S) : ℝ :=
  (candidate.pushforward interface).entropyBits -
    F.combinationLossBits maximum candidate

omit [Fintype C] [Fintype L] [Fintype R]
  [Fintype C'] [Fintype L'] [Fintype R']
  [DecidableEq C] [DecidableEq L] [DecidableEq R]
  [DecidableEq C'] [DecidableEq L'] [DecidableEq R'] in
/-- Independent products add base-two combination losses exactly. -/
theorem combinationLossBits_product
    (F : ThreeFeatureSystem S C L R) (G : ThreeFeatureSystem T C' L' R')
    (maximumLeft candidateLeft : ProbabilityVector S)
    (maximumRight candidateRight : ProbabilityVector T) :
    (F.product G).combinationLossBits
        (maximumLeft.product maximumRight) (candidateLeft.product candidateRight) =
      F.combinationLossBits maximumLeft candidateLeft +
        G.combinationLossBits maximumRight candidateRight := by
  unfold combinationLossBits
  rw [ProbabilityVector.entropyBits_product, ProbabilityVector.entropyBits_product]
  ring

omit [Fintype C] [Fintype L] [Fintype R]
  [Fintype C'] [Fintype L'] [Fintype R']
  [DecidableEq C] [DecidableEq L] [DecidableEq R]
  [DecidableEq C'] [DecidableEq L'] [DecidableEq R'] in
/-- Independent products add base-two directional retained rates exactly. -/
theorem directionalRetainedRateBits_product
    {A : Type u'} {B : Type v'} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (F : ThreeFeatureSystem S C L R) (G : ThreeFeatureSystem T C' L' R')
    (interfaceLeft : S → A) (interfaceRight : T → B)
    (maximumLeft candidateLeft : ProbabilityVector S)
    (maximumRight candidateRight : ProbabilityVector T) :
    (F.product G).directionalRetainedRateBits
        (fun st ↦ (interfaceLeft st.1, interfaceRight st.2))
        (maximumLeft.product maximumRight) (candidateLeft.product candidateRight) =
      F.directionalRetainedRateBits interfaceLeft maximumLeft candidateLeft +
        G.directionalRetainedRateBits interfaceRight maximumRight candidateRight := by
  unfold directionalRetainedRateBits
  rw [ProbabilityVector.pushforward_product_prodMap,
    ProbabilityVector.entropyBits_product, combinationLossBits_product]
  ring

/-- Bundled fixed-interface certificate for the independent two-letter construction: it preserves
both one-letter laws, lies in the paired feature fiber, retains maximum-entropy representatives,
and adds the base-two retained rates exactly. -/
theorem fixedInterface_product
    [DecidableEq S] [DecidableEq T]
    {A : Type u'} {B : Type v'} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (F : ThreeFeatureSystem S C L R) (G : ThreeFeatureSystem T C' L' R')
    (interfaceLeft : S → A) (interfaceRight : T → B)
    (maximumLeft candidateLeft : ProbabilityVector S)
    (maximumRight candidateRight : ProbabilityVector T)
    (hmaximumLeft : F.IsMaximumEntropy maximumLeft)
    (hmaximumRight : G.IsMaximumEntropy maximumRight)
    (hleft : F.SameFiber candidateLeft maximumLeft)
    (hright : G.SameFiber candidateRight maximumRight) :
    (candidateLeft.product candidateRight).IsCoupling candidateLeft candidateRight ∧
      (F.product G).SameFiber (candidateLeft.product candidateRight)
        (maximumLeft.product maximumRight) ∧
      (F.product G).IsMaximumEntropy (maximumLeft.product maximumRight) ∧
      (F.product G).directionalRetainedRateBits
          (fun st ↦ (interfaceLeft st.1, interfaceRight st.2))
          (maximumLeft.product maximumRight) (candidateLeft.product candidateRight) =
        F.directionalRetainedRateBits interfaceLeft maximumLeft candidateLeft +
          G.directionalRetainedRateBits interfaceRight maximumRight candidateRight := by
  exact
    ⟨ProbabilityVector.product_isCoupling candidateLeft candidateRight,
      sameFiber_product F G hleft hright,
      isMaximumEntropy_product F G hmaximumLeft hmaximumRight,
      directionalRetainedRateBits_product F G interfaceLeft interfaceRight
        maximumLeft candidateLeft maximumRight candidateRight⟩

/-- The independent product is an admissible two-letter witness with exactly the sum of the
one-letter directional retained rates. -/
theorem exists_productWitness_directionalRetainedRate
    [DecidableEq S] [DecidableEq T]
    {A : Type u'} {B : Type v'} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (F : ThreeFeatureSystem S C L R) (G : ThreeFeatureSystem T C' L' R')
    (interfaceLeft : S → A) (interfaceRight : T → B)
    (maximumLeft candidateLeft : ProbabilityVector S)
    (maximumRight candidateRight : ProbabilityVector T)
    (hleft : F.SameFiber candidateLeft maximumLeft)
    (hright : G.SameFiber candidateRight maximumRight) :
    ∃ joint : ProbabilityVector (S × T),
      joint.IsCoupling candidateLeft candidateRight ∧
        (F.product G).SameFiber joint (maximumLeft.product maximumRight) ∧
        (F.product G).directionalRetainedRate
            (fun st ↦ (interfaceLeft st.1, interfaceRight st.2))
            (maximumLeft.product maximumRight) joint =
          F.directionalRetainedRate interfaceLeft maximumLeft candidateLeft +
            G.directionalRetainedRate interfaceRight maximumRight candidateRight := by
  refine ⟨candidateLeft.product candidateRight,
    ProbabilityVector.product_isCoupling candidateLeft candidateRight, ?_, ?_⟩
  · exact sameFiber_product F G hleft hright
  · exact directionalRetainedRate_product F G interfaceLeft interfaceRight
      maximumLeft candidateLeft maximumRight candidateRight

/-- Any upper bound valid for every admissible correlated two-letter rate is at least the old
independent sum.  This is the optimizer-facing no-regression theorem. -/
theorem add_directionalRetainedRate_le_of_bounds_all_couplings
    [DecidableEq S] [DecidableEq T]
    {A : Type u'} {B : Type v'} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (F : ThreeFeatureSystem S C L R) (G : ThreeFeatureSystem T C' L' R')
    (interfaceLeft : S → A) (interfaceRight : T → B)
    (maximumLeft candidateLeft : ProbabilityVector S)
    (maximumRight candidateRight : ProbabilityVector T)
    (hleft : F.SameFiber candidateLeft maximumLeft)
    (hright : G.SameFiber candidateRight maximumRight)
    (bound : ℝ)
    (hbound : ∀ joint : ProbabilityVector (S × T),
      joint.IsCoupling candidateLeft candidateRight →
      (F.product G).SameFiber joint (maximumLeft.product maximumRight) →
      (F.product G).directionalRetainedRate
          (fun st ↦ (interfaceLeft st.1, interfaceRight st.2))
          (maximumLeft.product maximumRight) joint ≤ bound) :
    F.directionalRetainedRate interfaceLeft maximumLeft candidateLeft +
        G.directionalRetainedRate interfaceRight maximumRight candidateRight ≤ bound := by
  have hproduct := hbound (candidateLeft.product candidateRight)
    (ProbabilityVector.product_isCoupling candidateLeft candidateRight)
    (sameFiber_product F G hleft hright)
  rw [directionalRetainedRate_product] at hproduct
  exact hproduct

/-- Base-two optimizer-facing no-regression theorem: an upper bound on every admissible
correlated rate must dominate the independent sum of the old one-letter rates. -/
theorem add_directionalRetainedRateBits_le_of_bounds_all_couplings
    [DecidableEq S] [DecidableEq T]
    {A : Type u'} {B : Type v'} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (F : ThreeFeatureSystem S C L R) (G : ThreeFeatureSystem T C' L' R')
    (interfaceLeft : S → A) (interfaceRight : T → B)
    (maximumLeft candidateLeft : ProbabilityVector S)
    (maximumRight candidateRight : ProbabilityVector T)
    (hleft : F.SameFiber candidateLeft maximumLeft)
    (hright : G.SameFiber candidateRight maximumRight)
    (bound : ℝ)
    (hbound : ∀ joint : ProbabilityVector (S × T),
      joint.IsCoupling candidateLeft candidateRight →
      (F.product G).SameFiber joint (maximumLeft.product maximumRight) →
      (F.product G).directionalRetainedRateBits
          (fun st ↦ (interfaceLeft st.1, interfaceRight st.2))
          (maximumLeft.product maximumRight) joint ≤ bound) :
    F.directionalRetainedRateBits interfaceLeft maximumLeft candidateLeft +
        G.directionalRetainedRateBits interfaceRight maximumRight candidateRight ≤ bound := by
  have hproduct := hbound (candidateLeft.product candidateRight)
    (ProbabilityVector.product_isCoupling candidateLeft candidateRight)
    (sameFiber_product F G hleft hright)
  rw [directionalRetainedRateBits_product] at hproduct
  exact hproduct

end ThreeFeatureSystem

/-! ## Adapter to finite marginal information projections -/

namespace ThreeMarginalProjectionModel

variable
    {S : Type u} {C : Type v} {L : Type w} {R : Type x}
    [Fintype S] [Fintype C] [Fintype L] [Fintype R]
    [DecidableEq C] [DecidableEq L] [DecidableEq R]

/-- Forget the log-linear certificate and retain just the three feature maps cutting out its
feasible marginal fiber. -/
def featureSystem (M : ThreeMarginalProjectionModel S C L R) :
    ThreeFeatureSystem S C L R where
  coarse := M.coarse
  left := M.leftFeature
  right := M.rightFeature

/-- The generic feature-fiber predicate is exactly the existing projection-model feasibility
predicate. -/
@[simp] theorem isFeasible_iff_sameFiber
    (M : ThreeMarginalProjectionModel S C L R) (q : ProbabilityVector S) :
    M.IsFeasible q ↔ M.featureSystem.SameFiber q M.reference :=
  Iff.rfl

/-- A log-linear reference law is a maximum-entropy representative of its three-feature fiber. -/
theorem reference_isMaximumEntropy
    (M : ThreeMarginalProjectionModel S C L R) :
    M.featureSystem.IsMaximumEntropy M.reference := by
  intro q hq
  have hfeasible : M.IsFeasible q := (M.isFeasible_iff_sameFiber q).2 hq
  have hlog := M.expectation_log_reference_eq q hfeasible
  have hgap := ProbabilityVector.klDiv_eq_entropy_sub_of_expectation_log_eq
    q M.reference M.reference_pos hlog
  have hnonneg := ProbabilityVector.klDiv_nonneg q M.reference M.reference_pos
  linarith

/-- Products of two log-linear reference laws maximize entropy in the paired feature fiber. -/
theorem product_reference_isMaximumEntropy
    {T : Type y} {C' : Type z} {L' : Type u'} {R' : Type v'}
    [Fintype T] [Fintype C'] [Fintype L'] [Fintype R']
    [DecidableEq S] [DecidableEq T]
    [DecidableEq C'] [DecidableEq L'] [DecidableEq R']
    (M : ThreeMarginalProjectionModel S C L R)
    (N : ThreeMarginalProjectionModel T C' L' R') :
    (M.featureSystem.product N.featureSystem).IsMaximumEntropy
      (M.reference.product N.reference) :=
  ThreeFeatureSystem.isMaximumEntropy_product M.featureSystem N.featureSystem
    M.reference_isMaximumEntropy N.reference_isMaximumEntropy

end ThreeMarginalProjectionModel

end AlgebraicComplexity
