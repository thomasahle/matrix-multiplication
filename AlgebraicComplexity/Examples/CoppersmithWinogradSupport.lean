/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinograd
import AlgebraicComplexity.Examples.CoppersmithWinogradSupportCore
import AlgebraicComplexity.Probability.SupportDistribution

/-!
# The six-block support of the Coppersmith--Winograd tensor

This file records the optimizer-independent combinatorial data used by the classical laser
analysis of `CW_q`.  The support has three corner addresses and three middle addresses.  We prove
that it is tight and construct its standard one-parameter symmetric probability distribution,
including exact formulas for all three marginals.

The definitions are deliberately independent of a particular exponent target or numerical
optimizer, making this file a small regression client for the generic partitioned-support API and
for the probability-layer `SupportDistribution` interface (a finite probability vector on the
support).
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor

private theorem cw200_not_mem_tail :
    cw200 ∉ ({cw020, cw002, cw011, cw101, cw110} : Finset CWBlockAddress) := by
  simp [cw200, cw020, cw002, cw011, cw101, cw110, cwBlockAddress]

private theorem cw020_not_mem_tail :
    cw020 ∉ ({cw002, cw011, cw101, cw110} : Finset CWBlockAddress) := by
  simp [cw020, cw002, cw011, cw101, cw110, cwBlockAddress]

private theorem cw002_not_mem_tail :
    cw002 ∉ ({cw011, cw101, cw110} : Finset CWBlockAddress) := by
  simp [cw002, cw011, cw101, cw110, cwBlockAddress]

private theorem cw011_not_mem_tail :
    cw011 ∉ ({cw101, cw110} : Finset CWBlockAddress) := by
  simp [cw011, cw101, cw110, cwBlockAddress]

private theorem cw101_ne_cw110 : cw101 ≠ cw110 := by
  simp [cw101, cw110, cwBlockAddress]

/-- Expand a sum over the six standard CW addresses in their documented order. -/
theorem sum_cwBlockSupport {M : Type*} [AddCommMonoid M] (f : CWBlockAddress → M) :
    ∑ s ∈ cwBlockSupport, f s =
      f cw200 + (f cw020 + (f cw002 + (f cw011 + (f cw101 + f cw110)))) := by
  unfold cwBlockSupport
  rw [Finset.sum_insert cw200_not_mem_tail,
    Finset.sum_insert cw020_not_mem_tail,
    Finset.sum_insert cw002_not_mem_tail,
    Finset.sum_insert cw011_not_mem_tail,
    Finset.sum_insert (by simpa using cw101_ne_cw110)]
  simp

/-- Expand a product over the six standard CW addresses in their documented order. -/
theorem prod_cwBlockSupport {M : Type*} [CommMonoid M] (f : CWBlockAddress → M) :
    ∏ s ∈ cwBlockSupport, f s =
      f cw200 * (f cw020 * (f cw002 * (f cw011 * (f cw101 * f cw110)))) := by
  unfold cwBlockSupport
  rw [Finset.prod_insert cw200_not_mem_tail,
    Finset.prod_insert cw020_not_mem_tail,
    Finset.prod_insert cw002_not_mem_tail,
    Finset.prod_insert cw011_not_mem_tail,
    Finset.prod_insert (by simpa using cw101_ne_cw110)]
  simp

private def cw200Supported : cwBlockSupport := ⟨cw200, by decide⟩
private def cw020Supported : cwBlockSupport := ⟨cw020, by decide⟩
private def cw002Supported : cwBlockSupport := ⟨cw002, by decide⟩
private def cw011Supported : cwBlockSupport := ⟨cw011, by decide⟩
private def cw101Supported : cwBlockSupport := ⟨cw101, by decide⟩
private def cw110Supported : cwBlockSupport := ⟨cw110, by decide⟩

private theorem cwBlockSupport_subtype_univ :
    (Finset.univ : Finset cwBlockSupport) =
      {cw200Supported, cw020Supported, cw002Supported, cw011Supported,
        cw101Supported, cw110Supported} := by
  decide

private theorem cw200Supported_not_mem_tail :
    cw200Supported ∉
      ({cw020Supported, cw002Supported, cw011Supported, cw101Supported,
        cw110Supported} : Finset cwBlockSupport) := by
  decide

private theorem cw020Supported_not_mem_tail :
    cw020Supported ∉
      ({cw002Supported, cw011Supported, cw101Supported,
        cw110Supported} : Finset cwBlockSupport) := by
  decide

private theorem cw002Supported_not_mem_tail :
    cw002Supported ∉
      ({cw011Supported, cw101Supported, cw110Supported} : Finset cwBlockSupport) := by
  decide

private theorem cw011Supported_not_mem_tail :
    cw011Supported ∉ ({cw101Supported, cw110Supported} : Finset cwBlockSupport) := by
  decide

private theorem cw101Supported_ne_cw110Supported :
    cw101Supported ≠ cw110Supported := by
  decide

private theorem sum_cwBlockSupport_subtype {M : Type*} [AddCommMonoid M]
    (f : cwBlockSupport → M) :
    ∑ s, f s =
      f cw200Supported +
        (f cw020Supported +
          (f cw002Supported +
            (f cw011Supported + (f cw101Supported + f cw110Supported)))) := by
  rw [cwBlockSupport_subtype_univ]
  rw [Finset.sum_insert cw200Supported_not_mem_tail,
    Finset.sum_insert cw020Supported_not_mem_tail,
    Finset.sum_insert cw002Supported_not_mem_tail,
    Finset.sum_insert cw011Supported_not_mem_tail,
    Finset.sum_insert (by simpa using cw101Supported_ne_cw110Supported)]
  simp

/-- Integer labels witnessing tightness of the CW support. -/
def cwBlockWeight : CWBlock → ℤ
  | .zero => 0
  | .middle => 1
  | .last => 2

theorem cwBlockWeight_injective : Function.Injective cwBlockWeight := by
  intro a b h
  cases a <;> cases b <;> simp_all [cwBlockWeight]

/-- Every supported address has total block weight two. -/
theorem cwBlockSupport_weight_sum (s : CWBlockAddress) (hs : s ∈ cwBlockSupport) :
    ∑ c, cwBlockWeight (s c) = 2 := by
  simp only [cwBlockSupport, Finset.mem_insert, Finset.mem_singleton] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [cw200, cw020, cw002, cw011, cw101, cw110, cwBlockAddress,
      cwBlockWeight, sum_leg]

/-- The standard six-block CW support is tight. -/
theorem cwBlockSupport_isTight : IsTightSupport cwBlockSupport := by
  refine ⟨fun _ ↦ cwBlockWeight, ?_, 2, ?_⟩
  · intro c
    exact cwBlockWeight_injective
  · exact cwBlockSupport_weight_sum

/-- Mass assigned by the symmetric CW distribution to an ambient block address. -/
noncomputable def cwBlockMass (b : ℝ) (s : CWBlockAddress) : ℝ :=
  match s .X, s .Y, s .Z with
  | .last, .zero, .zero
  | .zero, .last, .zero
  | .zero, .zero, .last => 1 / 3 - b
  | _, _, _ => b

/-- The standard symmetric distribution: every corner receives `1/3-b`, and every middle
address receives `b`. -/
noncomputable def cwSupportDistribution (b : ℝ) (hb0 : 0 ≤ b) (hb1 : b ≤ 1 / 3) :
    SupportDistribution cwBlockSupport where
  weight s := cwBlockMass b s.1
  nonneg := by
    rintro ⟨s, hs⟩
    change 0 ≤ cwBlockMass b s
    simp only [cwBlockSupport, Finset.mem_insert, Finset.mem_singleton] at hs
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [cwBlockMass, cw200, cw020, cw002, cw011, cw101, cw110,
        cwBlockAddress, hb0] <;>
      norm_num at hb1 ⊢ <;>
      assumption
  total := by
    rw [← Finset.attach_eq_univ, Finset.sum_attach]
    rw [sum_cwBlockSupport]
    simp [cwBlockMass, cw200, cw020, cw002, cw011, cw101, cw110, cwBlockAddress]
    ring

private theorem cwSupportDistribution_marginal_eq_sum
    (b : ℝ) (hb0 : 0 ≤ b) (hb1 : b ≤ 1 / 3) (c : Leg) (a : CWBlock) :
    (cwSupportDistribution b hb0 hb1).marginal c a =
      ∑ s ∈ cwBlockSupport, if s c = a then cwBlockMass b s else 0 := by
  unfold SupportDistribution.marginal
  simp only [cwSupportDistribution]
  rw [← Finset.attach_eq_univ]
  change
    (∑ s ∈ cwBlockSupport.attach,
      (fun t : CWBlockAddress ↦ if t c = a then cwBlockMass b t else 0) s.1) = _
  exact Finset.sum_attach cwBlockSupport
    (fun t : CWBlockAddress ↦ if t c = a then cwBlockMass b t else 0)

private theorem cwSupport_marginal_expansion
    (ν : SupportDistribution cwBlockSupport) (c : Leg) (a : CWBlock) :
    ν.marginal c a =
      (if cw200 c = a then ν.weight cw200Supported else 0) +
        ((if cw020 c = a then ν.weight cw020Supported else 0) +
          ((if cw002 c = a then ν.weight cw002Supported else 0) +
            ((if cw011 c = a then ν.weight cw011Supported else 0) +
              ((if cw101 c = a then ν.weight cw101Supported else 0) +
                (if cw110 c = a then ν.weight cw110Supported else 0))))) := by
  unfold SupportDistribution.marginal
  rw [sum_cwBlockSupport_subtype]
  simp only [cw200Supported, cw020Supported, cw002Supported, cw011Supported,
    cw101Supported, cw110Supported]
  rfl

/-- The zero-block mass in every leg marginal. -/
theorem cwSupportDistribution_marginal_zero
    (b : ℝ) (hb0 : 0 ≤ b) (hb1 : b ≤ 1 / 3) (c : Leg) :
    (cwSupportDistribution b hb0 hb1).marginal c .zero = 2 / 3 - b := by
  rw [cwSupportDistribution_marginal_eq_sum, sum_cwBlockSupport]
  cases c <;>
    simp [cwBlockMass, cw200, cw020, cw002, cw011,
      cw101, cw110, cwBlockAddress] <;>
    ring

/-- The middle-block mass in every leg marginal. -/
theorem cwSupportDistribution_marginal_middle
    (b : ℝ) (hb0 : 0 ≤ b) (hb1 : b ≤ 1 / 3) (c : Leg) :
    (cwSupportDistribution b hb0 hb1).marginal c .middle = 2 * b := by
  rw [cwSupportDistribution_marginal_eq_sum, sum_cwBlockSupport]
  cases c <;>
    simp [cwBlockMass, cw200, cw020, cw002, cw011,
      cw101, cw110, cwBlockAddress] <;>
    ring

/-- The final-block mass in every leg marginal. -/
theorem cwSupportDistribution_marginal_last
    (b : ℝ) (hb0 : 0 ≤ b) (hb1 : b ≤ 1 / 3) (c : Leg) :
    (cwSupportDistribution b hb0 hb1).marginal c .last = 1 / 3 - b := by
  rw [cwSupportDistribution_marginal_eq_sum, sum_cwBlockSupport]
  cases c <;>
    simp [cwBlockMass, cw200, cw020, cw002, cw011,
      cw101, cw110, cwBlockAddress]

/-- The symmetric CW distribution is uniquely determined by its three marginals. -/
theorem cwSupportDistribution_unique_of_sameMarginals
    (b : ℝ) (hb0 : 0 ≤ b) (hb1 : b ≤ 1 / 3)
    (ν : SupportDistribution cwBlockSupport)
    (hν : (cwSupportDistribution b hb0 hb1).SameMarginals ν) :
    ν = cwSupportDistribution b hb0 hb1 := by
  have h200 : ν.weight cw200Supported = 1 / 3 - b := by
    have h := hν .X .last
    rw [cwSupportDistribution_marginal_last,
      cwSupport_marginal_expansion] at h
    simpa [cw200Supported, cw020Supported, cw002Supported, cw011Supported,
      cw101Supported, cw110Supported, cw200, cw020, cw002, cw011, cw101,
      cw110, cwBlockAddress] using h.symm
  have h020 : ν.weight cw020Supported = 1 / 3 - b := by
    have h := hν .Y .last
    rw [cwSupportDistribution_marginal_last,
      cwSupport_marginal_expansion] at h
    simpa [cw200Supported, cw020Supported, cw002Supported, cw011Supported,
      cw101Supported, cw110Supported, cw200, cw020, cw002, cw011, cw101,
      cw110, cwBlockAddress] using h.symm
  have h002 : ν.weight cw002Supported = 1 / 3 - b := by
    have h := hν .Z .last
    rw [cwSupportDistribution_marginal_last,
      cwSupport_marginal_expansion] at h
    simpa [cw200Supported, cw020Supported, cw002Supported, cw011Supported,
      cw101Supported, cw110Supported, cw200, cw020, cw002, cw011, cw101,
      cw110, cwBlockAddress] using h.symm
  have hX := hν .X .middle
  have hY := hν .Y .middle
  have hZ := hν .Z .middle
  rw [cwSupportDistribution_marginal_middle,
    cwSupport_marginal_expansion] at hX hY hZ
  simp [cw011Supported, cw101Supported, cw110Supported,
    cw200, cw020, cw002, cw011, cw101,
    cw110, cwBlockAddress] at hX hY hZ
  change 2 * b = ν.weight cw101Supported + ν.weight cw110Supported at hX
  change 2 * b = ν.weight cw011Supported + ν.weight cw110Supported at hY
  change 2 * b = ν.weight cw011Supported + ν.weight cw101Supported at hZ
  have h011 : ν.weight cw011Supported = b := by linarith
  have h101 : ν.weight cw101Supported = b := by linarith
  have h110 : ν.weight cw110Supported = b := by linarith
  apply SupportDistribution.ext
  funext s
  rcases s with ⟨s, hs⟩
  simp only [cwBlockSupport, Finset.mem_insert, Finset.mem_singleton] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl
  · simpa [cwSupportDistribution, cwBlockMass, cw200, cwBlockAddress,
      cw200Supported] using h200
  · simpa [cwSupportDistribution, cwBlockMass, cw020, cwBlockAddress,
      cw020Supported] using h020
  · simpa [cwSupportDistribution, cwBlockMass, cw002, cwBlockAddress,
      cw002Supported] using h002
  · simpa [cwSupportDistribution, cwBlockMass, cw011, cwBlockAddress,
      cw011Supported] using h011
  · simpa [cwSupportDistribution, cwBlockMass, cw101, cwBlockAddress,
      cw101Supported] using h101
  · simpa [cwSupportDistribution, cwBlockMass, cw110, cwBlockAddress,
      cw110Supported] using h110

/-- Consequently, the symmetric CW distribution maximizes entropy among all distributions with
the same marginals. -/
theorem cwSupportDistribution_isMaximumEntropy
    (b : ℝ) (hb0 : 0 ≤ b) (hb1 : b ≤ 1 / 3) :
    (cwSupportDistribution b hb0 hb1).IsMaximumEntropy :=
  SupportDistribution.isMaximumEntropy_of_unique _
    (cwSupportDistribution_unique_of_sameMarginals b hb0 hb1)

/-- Matrix-multiplication volume of a standard CW constituent.  The three corner constituents
have volume one, while each middle constituent has volume `q`. -/
def cwConstituentVolume (q : ℕ) (s : cwBlockSupport) : ℕ :=
  match s.1 .X, s.1 .Y, s.1 .Z with
  | .last, .zero, .zero
  | .zero, .last, .zero
  | .zero, .zero, .last => 1
  | .zero, .middle, .middle
  | .middle, .zero, .middle
  | .middle, .middle, .zero => q
  | _, _, _ => 0

theorem cwConstituentVolume_pos {q : ℕ} (hq : 0 < q) (s : cwBlockSupport) :
    0 < cwConstituentVolume q s := by
  rcases s with ⟨s, hs⟩
  simp only [cwBlockSupport, Finset.mem_insert, Finset.mem_singleton] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [cwConstituentVolume, cw200, cw020, cw002, cw011, cw101, cw110,
      cwBlockAddress, hq]

/-- Exact expected logarithmic volume of the six CW constituents. -/
theorem cwSupportDistribution_expectedLogVolume
    (q : ℕ) (b : ℝ) (hb0 : 0 ≤ b) (hb1 : b ≤ 1 / 3) :
    (cwSupportDistribution b hb0 hb1).expectedLogNat (cwConstituentVolume q) =
      3 * b * Real.log q := by
  unfold SupportDistribution.expectedLogNat ProbabilityVector.expectation
  rw [sum_cwBlockSupport_subtype]
  simp [cwSupportDistribution, cwConstituentVolume, cwBlockMass,
    cw200Supported, cw020Supported, cw002Supported, cw011Supported,
    cw101Supported, cw110Supported, cw200, cw020, cw002, cw011, cw101,
    cw110, cwBlockAddress]
  ring

/-- Expand a finite sum over the three CW block labels. -/
theorem sum_cwBlock {M : Type*} [AddCommMonoid M] (f : CWBlock → M) :
    ∑ a, f a = f .zero + f .middle + f .last := by
  rw [show (Finset.univ : Finset CWBlock) = {.zero, .middle, .last} by
    ext a
    cases a <;> simp]
  simp [add_assoc]

/-- Expand a finite product over the three CW blocks. -/
theorem prod_cwBlock {M : Type*} [CommMonoid M] (f : CWBlock → M) :
    ∏ a, f a = f .zero * f .middle * f .last := by
  rw [show (Finset.univ : Finset CWBlock) = {.zero, .middle, .last} by
    ext a
    cases a <;> simp]
  simp [mul_assoc]

/-- Exact entropy of each of the three identical CW marginals. -/
theorem cwSupportDistribution_marginalEntropy
    (b : ℝ) (hb0 : 0 ≤ b) (hb1 : b ≤ 1 / 3) (c : Leg) :
    (cwSupportDistribution b hb0 hb1).marginalEntropy c =
      Real.negMulLog (2 / 3 - b) +
        Real.negMulLog (2 * b) +
        Real.negMulLog (1 / 3 - b) := by
  rw [SupportDistribution.marginalEntropy, sum_cwBlock]
  simp only [cwSupportDistribution_marginal_zero,
    cwSupportDistribution_marginal_middle, cwSupportDistribution_marginal_last]

/-- Since all three marginals agree, the bottleneck marginal entropy is their common entropy. -/
theorem cwSupportDistribution_minimumMarginalEntropy
    (b : ℝ) (hb0 : 0 ≤ b) (hb1 : b ≤ 1 / 3) :
    (cwSupportDistribution b hb0 hb1).minimumMarginalEntropy =
      Real.negMulLog (2 / 3 - b) +
        Real.negMulLog (2 * b) +
        Real.negMulLog (1 / 3 - b) := by
  unfold SupportDistribution.minimumMarginalEntropy
  rw [cwSupportDistribution_marginalEntropy,
    cwSupportDistribution_marginalEntropy,
    cwSupportDistribution_marginalEntropy]
  simp

end AlgebraicComplexity.Examples
