/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import MatrixMultiplication.ConditionalIntegerEntropyDual

set_option autoImplicit false

/-!
# Support-restricted conditional integer entropy dual core

The ordinary conditional integer dual sums the Gibbs partition over a common ambient child
alphabet.  A conditional combinatorial program often has a smaller legal alphabet in each parent
row.  This file proves the corresponding honest restriction: the row law must vanish off its
legal predicate, and the Gibbs partition then sums only over legal states.

For the paired-parent program, take `legal z u := coordZ u = z`. The resulting natural-number
partition is literally `sum_u if coordZ u = z then weight u else 0`, the filtered row sum used by
the finite checker. This core contains no integral-profile disintegration or profile-entropy
corollary. No tensor or Coppersmith--Winograd semantic identification is asserted here.

## References

- [alman2025more] Josh Alman et al., *More Asymmetry Yields Faster Matrix Multiplication*.
- [dupont2026improving] Emilien Dupont et al., *Improving the Matrix Multiplication Exponent with
  Modern Optimization and AlphaEvolve*.
-/

open scoped BigOperators

namespace MatrixMultiplication.SupportRestrictedConditionalIntegerEntropyDual

open AlgebraicComplexity

noncomputable section

universe u v w

/-- The subtype cut out by a finite predicate. -/
abbrev PredicateFiber {U : Type u} (legal : U → Prop) := {u : U // legal u}

/-- A sum whose summand vanishes off a predicate may be evaluated on the predicate subtype. -/
theorem sum_predicateFiber_eq
    {U : Type u} {M : Type w} [Fintype U] [AddCommMonoid M]
    (legal : U → Prop) [DecidablePred legal]
    (f : U → M) (hzero : ∀ u, ¬legal u → f u = 0) :
    (∑ u : PredicateFiber legal, f u.1) = ∑ u, f u := by
  have hsplit := Fintype.sum_subtype_add_sum_subtype legal f
  have hcomplement :
      (∑ u : {u : U // ¬legal u}, f u.1) = 0 := by
    apply Finset.sum_eq_zero
    intro u _
    exact hzero u.1 u.2
  rw [hcomplement, add_zero] at hsplit
  exact hsplit

/-- Restrict a probability row to a prescribed predicate, without renormalizing. -/
noncomputable def restrictToPredicate
    {U : Type u} [Fintype U]
    (row : ProbabilityVector U) (legal : U → Prop) [DecidablePred legal]
    (hoff : ∀ u, ¬legal u → row.weight u = 0) :
    ProbabilityVector (PredicateFiber legal) where
  weight u := row.weight u.1
  nonneg u := row.nonneg u.1
  total := by
    rw [sum_predicateFiber_eq legal row.weight hoff]
    exact row.total

/-- Restricting a row preserves every legal state's weight definitionally. -/
@[simp] theorem restrictToPredicate_weight
    {U : Type u} [Fintype U]
    (row : ProbabilityVector U) (legal : U → Prop) [DecidablePred legal]
    (hoff : ∀ u, ¬legal u → row.weight u = 0)
    (u : PredicateFiber legal) :
    (restrictToPredicate row legal hoff).weight u = row.weight u.1 :=
  rfl

/-- Prescribed support restriction preserves entropy. -/
theorem restrictToPredicate_entropy
    {U : Type u} [Fintype U]
    (row : ProbabilityVector U) (legal : U → Prop) [DecidablePred legal]
    (hoff : ∀ u, ¬legal u → row.weight u = 0) :
    (restrictToPredicate row legal hoff).entropy = row.entropy := by
  unfold ProbabilityVector.entropy
  simp only [restrictToPredicate_weight]
  rw [sum_predicateFiber_eq legal (fun u ↦ Real.negMulLog (row.weight u))]
  intro u hu
  rw [hoff u hu]
  simp

/-- Prescribed support restriction preserves expectations of ambient statistics. -/
theorem restrictToPredicate_expectation
    {U : Type u} [Fintype U]
    (row : ProbabilityVector U) (legal : U → Prop) [DecidablePred legal]
    (hoff : ∀ u, ¬legal u → row.weight u = 0) (f : U → ℝ) :
    (restrictToPredicate row legal hoff).expectation (f ∘ Subtype.val) =
      row.expectation f := by
  unfold ProbabilityVector.expectation
  simp only [restrictToPredicate_weight, Function.comp_apply]
  rw [sum_predicateFiber_eq legal (fun u ↦ row.weight u * f u)]
  intro u hu
  rw [hoff u hu]
  simp

/-- Natural-number Gibbs partition of one legal conditional row. -/
def restrictedIntegerFiberPartition
    {Z : Type u} {U : Type v} [Fintype U]
    (legal : Z → U → Prop) [DecidableRel legal]
    (weight : Z → U → ℕ) (z : Z) : ℕ :=
  ∑ u, if legal z u then weight z u else 0

/-- The ambient filtered sum is the intrinsic subtype sum. -/
theorem sum_predicateFiber_weight_eq_restrictedIntegerFiberPartition
    {Z : Type u} {U : Type v} [Fintype U]
    (legal : Z → U → Prop) [DecidableRel legal]
    (weight : Z → U → ℕ) (z : Z) :
    (∑ u : PredicateFiber (legal z), weight z u.1) =
      restrictedIntegerFiberPartition legal weight z := by
  calc
    (∑ u : PredicateFiber (legal z), weight z u.1) =
        ∑ u : PredicateFiber (legal z),
          (if legal z u.1 then weight z u.1 else 0) := by
      apply Finset.sum_congr rfl
      intro u _
      simp [u.2]
    _ = ∑ u, if legal z u then weight z u else 0 := by
      exact sum_predicateFiber_eq (legal z)
        (fun u ↦ if legal z u then weight z u else 0) (by
          intro u hu
          simp [hu])
    _ = restrictedIntegerFiberPartition legal weight z := rfl

/-- A nonempty legal row with positive pointwise integer weights has positive partition. -/
theorem restrictedIntegerFiberPartition_pos
    {Z : Type u} {U : Type v} [Fintype U]
    (legal : Z → U → Prop) [DecidableRel legal]
    (weight : Z → U → ℕ) (hweight : ∀ z u, 0 < weight z u)
    (z : Z) (hlegal : ∃ u, legal z u) :
    0 < restrictedIntegerFiberPartition legal weight z := by
  letI : Nonempty (PredicateFiber (legal z)) :=
    ⟨⟨Classical.choose hlegal, Classical.choose_spec hlegal⟩⟩
  rw [← sum_predicateFiber_weight_eq_restrictedIntegerFiberPartition legal weight z]
  exact Finset.sum_pos (fun u _ ↦ hweight z u.1) Finset.univ_nonempty

/-- Exponentiating logarithmic integer weights on the legal subtype gives the cast of the
filtered natural-number partition. -/
theorem partition_log_integerWeight_restricted
    {Z : Type u} {U : Type v} [Fintype U]
    (legal : Z → U → Prop) [DecidableRel legal]
    (weight : Z → U → ℕ) (hweight : ∀ z u, 0 < weight z u) (z : Z) :
    MaximumEntropyDual.partition
        (fun u : PredicateFiber (legal z) ↦ Real.log (weight z u.1 : ℝ)) =
      (restrictedIntegerFiberPartition legal weight z : ℝ) := by
  unfold MaximumEntropyDual.partition
  calc
    (∑ u : PredicateFiber (legal z), Real.exp (Real.log (weight z u.1 : ℝ))) =
        ∑ u : PredicateFiber (legal z), (weight z u.1 : ℝ) := by
      apply Finset.sum_congr rfl
      intro u _
      rw [Real.exp_log]
      exact_mod_cast hweight z u.1
    _ = ((∑ u : PredicateFiber (legal z), weight z u.1 : ℕ) : ℝ) := by
      push_cast
      rfl
    _ = (restrictedIntegerFiberPartition legal weight z : ℝ) := by
      exact_mod_cast
        sum_predicateFiber_weight_eq_restrictedIntegerFiberPartition legal weight z

/-- Rowwise support-restricted integer dual in natural-log units. -/
theorem entropy_le_restrictedIntegerPartition_sub_expectation
    {U : Type u} [Fintype U]
    (row : ProbabilityVector U) (legal : U → Prop) [DecidablePred legal]
    (weight : U → ℕ) (hweight : ∀ u, 0 < weight u)
    (hlegal : ∃ u, legal u)
    (hoff : ∀ u, ¬legal u → row.weight u = 0) :
    row.entropy ≤
      Real.log (∑ u, if legal u then weight u else 0 : ℕ) -
        ∑ u, row.weight u * Real.log (weight u : ℝ) := by
  letI : Nonempty (PredicateFiber legal) :=
    ⟨⟨Classical.choose hlegal, Classical.choose_spec hlegal⟩⟩
  let restricted := restrictToPredicate row legal hoff
  let score : PredicateFiber legal → ℝ :=
    fun u ↦ Real.log (weight u.1 : ℝ)
  have hdual : restricted.entropy ≤
      Real.log (MaximumEntropyDual.partition score) - restricted.expectation score := by
    simpa only [ProbabilityVector.entropy, ProbabilityVector.expectation,
      MaximumEntropyDual.entropy] using
      MaximumEntropyDual.entropy_le_logPartition_sub_expectation
        restricted.weight score restricted.nonneg restricted.total
  have hpartition : MaximumEntropyDual.partition score =
      ((∑ u, if legal u then weight u else 0 : ℕ) : ℝ) := by
    simpa only [score, restrictedIntegerFiberPartition] using
      partition_log_integerWeight_restricted
        (fun _ : Unit ↦ legal) (fun _ u ↦ weight u)
        (fun _ u ↦ hweight u) ()
  have hrestrictedEntropy : restricted.entropy = row.entropy := by
    simpa only [restricted] using restrictToPredicate_entropy row legal hoff
  have hrestrictedExpectation :
      restricted.expectation score =
        row.expectation (fun u ↦ Real.log (weight u : ℝ)) := by
    change (restrictToPredicate row legal hoff).expectation
        ((fun u : U ↦ Real.log (weight u : ℝ)) ∘ Subtype.val) =
      row.expectation (fun u ↦ Real.log (weight u : ℝ))
    exact restrictToPredicate_expectation row legal hoff
      (fun u ↦ Real.log (weight u : ℝ))
  rw [hpartition, hrestrictedEntropy, hrestrictedExpectation] at hdual
  simpa only [ProbabilityVector.expectation] using hdual

/-- Parent-weighted logarithms of the legal integer partitions, in nats. -/
def restrictedIntegerPartitionLogNats
    {Z : Type u} {U : Type v} [Fintype Z] [Fintype U]
    (parent : ProbabilityVector Z)
    (legal : Z → U → Prop) [DecidableRel legal]
    (weight : Z → U → ℕ) : ℝ :=
  ∑ z, parent.weight z *
    Real.log (restrictedIntegerFiberPartition legal weight z : ℝ)

/-- Conditional integer dual whose Gibbs sum is restricted independently in every parent row. -/
def supportRestrictedConditionalIntegerDualNats
    {Z : Type u} {U : Type v} [Fintype Z] [Fintype U]
    (parent : ProbabilityVector Z) (row : Z → ProbabilityVector U)
    (legal : Z → U → Prop) [DecidableRel legal]
    (weight : Z → U → ℕ) : ℝ :=
  ∑ z, parent.weight z *
    (Real.log (restrictedIntegerFiberPartition legal weight z : ℝ) -
      ∑ u, (row z).weight u * Real.log (weight z u : ℝ))

/-- The restricted dual is partition log minus the ordinary score expectation. -/
theorem supportRestrictedConditionalIntegerDualNats_eq
    {Z : Type u} {U : Type v} [Fintype Z] [Fintype U]
    (parent : ProbabilityVector Z) (row : Z → ProbabilityVector U)
    (legal : Z → U → Prop) [DecidableRel legal]
    (weight : Z → U → ℕ) :
    supportRestrictedConditionalIntegerDualNats parent row legal weight =
      restrictedIntegerPartitionLogNats parent legal weight -
        ConditionalIntegerEntropyDual.integerWeightExpectationNats parent row weight := by
  unfold supportRestrictedConditionalIntegerDualNats restrictedIntegerPartitionLogNats
    ConditionalIntegerEntropyDual.integerWeightExpectationNats
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib]

/-- The support-restricted conditional integer dual in bits. -/
def supportRestrictedConditionalIntegerDualBits
    {Z : Type u} {U : Type v} [Fintype Z] [Fintype U]
    (parent : ProbabilityVector Z) (row : Z → ProbabilityVector U)
    (legal : Z → U → Prop) [DecidableRel legal]
    (weight : Z → U → ℕ) : ℝ :=
  supportRestrictedConditionalIntegerDualNats parent row legal weight / Real.log 2

/-- A row family is supported on its legal predicates wherever the parent has positive mass. -/
def RowsSupportedOnPositiveParent
    {Z : Type u} {U : Type v} [Fintype Z] [Fintype U]
    (parent : ProbabilityVector Z) (row : Z → ProbabilityVector U)
    (legal : Z → U → Prop) : Prop :=
  ∀ z, 0 < parent.weight z → ∀ u, ¬legal z u → (row z).weight u = 0

/-- Positive integer weights give a rigorous conditional-entropy upper bound with the Gibbs
partition restricted to the legal states in each parent row. -/
theorem conditionalEntropy_le_supportRestrictedConditionalIntegerDualNats
    {Z : Type u} {U : Type v}
    [Fintype Z] [DecidableEq Z] [Fintype U] [Nonempty U]
    (parent : ProbabilityVector Z) (row : Z → ProbabilityVector U)
    (legal : Z → U → Prop) [DecidableRel legal]
    (weight : Z → U → ℕ) (hweight : ∀ z u, 0 < weight z u)
    (hlegal : ∀ z, 0 < parent.weight z → ∃ u, legal z u)
    (hsupport : RowsSupportedOnPositiveParent parent row legal) :
    (parent.joint row).conditionalEntropy Prod.fst ≤
      supportRestrictedConditionalIntegerDualNats parent row legal weight := by
  rw [ProbabilityVector.conditionalEntropy_joint_fst]
  unfold supportRestrictedConditionalIntegerDualNats
  apply Finset.sum_le_sum
  intro z _
  by_cases hz : parent.weight z = 0
  · simp [hz]
  · have hzpos : 0 < parent.weight z :=
      lt_of_le_of_ne (parent.nonneg z) (Ne.symm hz)
    exact mul_le_mul_of_nonneg_left
      (entropy_le_restrictedIntegerPartition_sub_expectation
        (row z) (legal z) (weight z) (hweight z) (hlegal z hzpos)
        (hsupport z hzpos)) (parent.nonneg z)

/-- Full rowwise support is a convenient sufficient premise for the restricted conditional dual. -/
theorem conditionalEntropy_le_supportRestrictedConditionalIntegerDualNats_of_rowsSupported
    {Z : Type u} {U : Type v}
    [Fintype Z] [DecidableEq Z] [Fintype U] [Nonempty U]
    (parent : ProbabilityVector Z) (row : Z → ProbabilityVector U)
    (legal : Z → U → Prop) [DecidableRel legal]
    (weight : Z → U → ℕ) (hweight : ∀ z u, 0 < weight z u)
    (hlegal : ∀ z, 0 < parent.weight z → ∃ u, legal z u)
    (hsupport : ∀ z u, ¬legal z u → (row z).weight u = 0) :
    (parent.joint row).conditionalEntropy Prod.fst ≤
      supportRestrictedConditionalIntegerDualNats parent row legal weight := by
  exact conditionalEntropy_le_supportRestrictedConditionalIntegerDualNats
    parent row legal weight hweight hlegal (fun z _ ↦ hsupport z)

/-- Base-two form of the support-restricted conditional integer dual. -/
theorem conditionalEntropyBits_le_supportRestrictedConditionalIntegerDualBits
    {Z : Type u} {U : Type v}
    [Fintype Z] [DecidableEq Z] [Fintype U] [Nonempty U]
    (parent : ProbabilityVector Z) (row : Z → ProbabilityVector U)
    (legal : Z → U → Prop) [DecidableRel legal]
    (weight : Z → U → ℕ) (hweight : ∀ z u, 0 < weight z u)
    (hlegal : ∀ z, 0 < parent.weight z → ∃ u, legal z u)
    (hsupport : RowsSupportedOnPositiveParent parent row legal) :
    (parent.joint row).conditionalEntropyBits Prod.fst ≤
      supportRestrictedConditionalIntegerDualBits parent row legal weight := by
  unfold ProbabilityVector.conditionalEntropyBits
    supportRestrictedConditionalIntegerDualBits
  exact (div_le_div_iff_of_pos_right (Real.log_pos (by norm_num : (1 : ℝ) < 2))).2
    (conditionalEntropy_le_supportRestrictedConditionalIntegerDualNats
      parent row legal weight hweight hlegal hsupport)

/-- Outer-mass-weighted conditional-entropy form.  This is the direct finite-block statement and
contains no parent `H(Z)` contribution. -/
theorem mass_mul_conditionalEntropyBits_le_supportRestrictedConditionalIntegerDualBits
    {Z : Type u} {U : Type v}
    [Fintype Z] [DecidableEq Z] [Fintype U] [Nonempty U]
    (parent : ProbabilityVector Z) (row : Z → ProbabilityVector U)
    (legal : Z → U → Prop) [DecidableRel legal]
    (weight : Z → U → ℕ) (hweight : ∀ z u, 0 < weight z u)
    (hlegal : ∀ z, 0 < parent.weight z → ∃ u, legal z u)
    (hsupport : RowsSupportedOnPositiveParent parent row legal)
    (mass : ℝ) (hmass : 0 ≤ mass) :
    mass * (parent.joint row).conditionalEntropyBits Prod.fst ≤
      mass * supportRestrictedConditionalIntegerDualBits parent row legal weight := by
  exact mul_le_mul_of_nonneg_left
    (conditionalEntropyBits_le_supportRestrictedConditionalIntegerDualBits
      parent row legal weight hweight hlegal hsupport) hmass

/-- Fixed-moment client form in bits. -/
theorem conditionalEntropyBits_le_restrictedIntegerPartitionLog_sub_fixedMoment
    {Z : Type u} {U : Type v}
    [Fintype Z] [DecidableEq Z] [Fintype U] [Nonempty U]
    (parent : ProbabilityVector Z) (row : Z → ProbabilityVector U)
    (legal : Z → U → Prop) [DecidableRel legal]
    (weight : Z → U → ℕ) (hweight : ∀ z u, 0 < weight z u)
    (hlegal : ∀ z, 0 < parent.weight z → ∃ u, legal z u)
    (hsupport : RowsSupportedOnPositiveParent parent row legal)
    (fixedMomentNats : ℝ)
    (hmoment :
      ConditionalIntegerEntropyDual.integerWeightExpectationNats parent row weight =
        fixedMomentNats) :
    (parent.joint row).conditionalEntropyBits Prod.fst ≤
      (restrictedIntegerPartitionLogNats parent legal weight - fixedMomentNats) /
        Real.log 2 := by
  have hdual := conditionalEntropyBits_le_supportRestrictedConditionalIntegerDualBits
    parent row legal weight hweight hlegal hsupport
  rw [supportRestrictedConditionalIntegerDualBits,
    supportRestrictedConditionalIntegerDualNats_eq, hmoment] at hdual
  exact hdual

/-- Subtracting the support-restricted dual gives a certified lower bound on a retained entropy
gap.  This is the A5-facing orientation: no parent-entropy term is added. -/
theorem sourceEntropyBits_sub_supportRestrictedDual_le_retained
    {Z : Type u} {U : Type v}
    [Fintype Z] [DecidableEq Z] [Fintype U] [Nonempty U]
    (parent : ProbabilityVector Z) (row : Z → ProbabilityVector U)
    (legal : Z → U → Prop) [DecidableRel legal]
    (weight : Z → U → ℕ) (hweight : ∀ z u, 0 < weight z u)
    (hlegal : ∀ z, 0 < parent.weight z → ∃ u, legal z u)
    (hsupport : RowsSupportedOnPositiveParent parent row legal)
    (sourceEntropyBits : ℝ) :
    sourceEntropyBits -
        supportRestrictedConditionalIntegerDualBits parent row legal weight ≤
      sourceEntropyBits - (parent.joint row).conditionalEntropyBits Prod.fst := by
  exact sub_le_sub_left
    (conditionalEntropyBits_le_supportRestrictedConditionalIntegerDualBits
      parent row legal weight hweight hlegal hsupport) sourceEntropyBits

/-- Outer-mass-weighted retained-gap form used when one finite conditional program represents a
subprobability block of a larger certificate. -/
theorem mass_mul_sourceEntropyBits_sub_supportRestrictedDual_le_retained
    {Z : Type u} {U : Type v}
    [Fintype Z] [DecidableEq Z] [Fintype U] [Nonempty U]
    (parent : ProbabilityVector Z) (row : Z → ProbabilityVector U)
    (legal : Z → U → Prop) [DecidableRel legal]
    (weight : Z → U → ℕ) (hweight : ∀ z u, 0 < weight z u)
    (hlegal : ∀ z, 0 < parent.weight z → ∃ u, legal z u)
    (hsupport : RowsSupportedOnPositiveParent parent row legal)
    (mass sourceEntropyBits : ℝ) (hmass : 0 ≤ mass) :
    mass * (sourceEntropyBits -
        supportRestrictedConditionalIntegerDualBits parent row legal weight) ≤
      mass * (sourceEntropyBits -
        (parent.joint row).conditionalEntropyBits Prod.fst) := by
  exact mul_le_mul_of_nonneg_left
    (sourceEntropyBits_sub_supportRestrictedDual_le_retained
      parent row legal weight hweight hlegal hsupport sourceEntropyBits) hmass

/-- Fixed-coordinate specialization.  This is definitionally the A5 checker's per-parent filtered
integer row sum when `coord` is logical Z and `weight` is the categorical product factor. -/
def fixedCoordinateIntegerFiberPartition
    {Z : Type u} {U : Type v} [DecidableEq Z] [Fintype U]
    (coord : U → Z) (weight : U → ℕ) (z : Z) : ℕ :=
  restrictedIntegerFiberPartition
    (fun z u ↦ coord u = z) (fun _ u ↦ weight u) z

/-- The fixed-coordinate partition is the corresponding filtered ambient sum. -/
theorem fixedCoordinateIntegerFiberPartition_eq
    {Z : Type u} {U : Type v} [DecidableEq Z] [Fintype U]
    (coord : U → Z) (weight : U → ℕ) (z : Z) :
    fixedCoordinateIntegerFiberPartition coord weight z =
      ∑ u, if coord u = z then weight u else 0 :=
  rfl

end

end MatrixMultiplication.SupportRestrictedConditionalIntegerEntropyDual
