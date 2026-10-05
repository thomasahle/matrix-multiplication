/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Analysis.RegionalExponent
import AlgebraicComplexity.Probability.CrossEntropy
import AlgebraicComplexity.Probability.EntropyChainRule
import AlgebraicComplexity.Probability.ParentConsistency
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith

/-!
# From parent consistency to retained regional exponents

The parent-consistency theorem bounds the entropy of compatibility alternatives.  Laser-method
applications use the *negative* of that entropy inside a retained branch exponent, then take a
minimum of three directional branch totals.  This module supplies the generic bridge between
those two formulations.

There are two independent steps.

* `sum_pooledRetainedRate_add_quadratic_le_sum_retainedRate` aggregates the local quadratic
  parent corrections with arbitrary nonnegative outer weights.
* `regionalTotal_addCorrection_sub_eq` proves that, when a chosen branch is active both before
  and after correction, the increase in the sum of regional minima is exactly the sum of the
  chosen corrections.  The active branch may vary from region to region.

Neither statement mentions Coppersmith--Winograd tensors or a particular certificate, so they
can be reused by other entropy-based extraction arguments.
-/

open scoped BigOperators

namespace AlgebraicComplexity

universe u₁ u₂ u₃ u₄ u₅ u₆

namespace CompatibilityPoolingModel

variable
    {Node : Type u₁} {U : Type u₂} {L : Type u₃} {R : Type u₄}
    {CL : Type u₅} {CR : Type u₆}
    [Fintype Node] [Fintype U] [Fintype L] [Fintype R] [Fintype CL] [Fintype CR]
    [DecidableEq U] [DecidableEq L] [DecidableEq R] [DecidableEq CL] [DecidableEq CR]

/-- A fixed local contribution minus the entropy of the compatible alternatives.  This is the
sign convention with which compatibility-counting estimates enter retained exponents. -/
noncomputable def retainedRate
    (fixed : ℝ) (q : ProbabilityVector (Sample U L R)) : ℝ :=
  fixed - q.conditionalEntropyBits (coarseMap (U := U) (L := L) (R := R))

/-- The retained rate obtained when the prescribed parent law is dropped and the pooled child
laws are independently coupled. -/
noncomputable def pooledRetainedRate
    (M : CompatibilityPoolingModel U L R CL CR) (fixed : ℝ) : ℝ :=
  retainedRate fixed M.reference

omit [DecidableEq L] [DecidableEq R] [DecidableEq CL] [DecidableEq CR] in
/-- The pooled compatibility entropy is the coarse-law-weighted sum of the two pooled child
entropies.  This identifies the abstract conditional entropy in the parent-consistency theorem
with the explicit entropy penalty used in recursive type-counting formulas. -/
theorem reference_conditionalEntropyBits_eq
    (M : CompatibilityPoolingModel U L R CL CR) :
    M.reference.conditionalEntropyBits
        (coarseMap (U := U) (L := L) (R := R)) =
      ∑ u, M.coarseLaw.weight u *
        ((M.pooledLeft (M.leftCell u)).entropyBits +
          (M.pooledRight (M.rightCell u)).entropyBits) := by
  rw [reference, coarseMap, ProbabilityVector.conditionalEntropyBits_joint_fst]
  apply Finset.sum_congr rfl
  intro u _
  rw [ProbabilityVector.entropyBits_product]

omit [DecidableEq U] [DecidableEq CL] [DecidableEq CR] in
/-- The decoupled parent law has full support.  Consequently every prescribed parent law is
absolutely continuous with respect to it, so the exact KL correction is finite. -/
theorem decoupledParent_pos [Nonempty U]
    (M : CompatibilityPoolingModel U L R CL CR) (z : L × R) :
    0 < M.decoupledParent.weight z := by
  change 0 <
    (M.reference.pushforward (parentMap (U := U) (L := L) (R := R))).weight z
  exact ProbabilityVector.pushforward_weight_pos_of_surjective
    (parentMap (U := U) (L := L) (R := R)) M.reference M.reference_pos
    (parentMap_surjective (U := U) (L := L) (R := R)) z

omit [DecidableEq U] [DecidableEq CL] [DecidableEq CR] in
/-- Explicit finite absolute-continuity statement for the prescribed parent law. -/
theorem prescribedParent_isAbsolutelyContinuous [Nonempty U]
    (M : CompatibilityPoolingModel U L R CL CR) (β : ProbabilityVector (L × R)) :
    β.IsAbsolutelyContinuous M.decoupledParent :=
  ProbabilityVector.isAbsolutelyContinuous_of_reference_pos
    β M.decoupledParent M.decoupledParent_pos

omit [DecidableEq U] [DecidableEq CL] [DecidableEq CR] in
/-- Stable cross-entropy form of the exact marginal-KL correction. -/
theorem parentEntropyBits_add_parentKlBits_eq_crossEntropyBits [Nonempty U]
    (M : CompatibilityPoolingModel U L R CL CR) (β : ProbabilityVector (L × R)) :
    β.entropyBits + β.klDivBits M.decoupledParent =
      β.crossEntropyBits M.decoupledParent :=
  ProbabilityVector.entropyBits_add_klDivBits_eq_crossEntropyBits
    β M.decoupledParent M.decoupledParent_pos

/-- Restoring a prescribed parent marginal raises the retained local rate by at least the
quadratic parent-consistency correction. -/
theorem pooledRetainedRate_add_quadratic_le_retainedRate [Nonempty U]
    (M : CompatibilityPoolingModel U L R CL CR)
    (q : ProbabilityVector (Sample U L R)) (β : ProbabilityVector (L × R))
    (fixed : ℝ) (hq : M.IsFeasible q) (hparent : M.parentLaw q = β) :
    M.pooledRetainedRate fixed + β.quadraticKlLowerBits M.decoupledParent ≤
      retainedRate fixed q := by
  have hentropy :=
    M.conditionalEntropyBits_le_sub_prescribedParentQuadratic q β hq hparent
  unfold pooledRetainedRate retainedRate
  linarith

/-- Weighted finite aggregation of the local parent-consistency correction.  This is the exact
form needed when node masses and region masses have already been folded into `weight`. -/
theorem sum_pooledRetainedRate_add_quadratic_le_sum_retainedRate [Nonempty U]
    (M : Node → CompatibilityPoolingModel U L R CL CR)
    (q : Node → ProbabilityVector (Sample U L R))
    (β : Node → ProbabilityVector (L × R))
    (fixed weight : Node → ℝ)
    (hweight : ∀ node, 0 ≤ weight node)
    (hfeasible : ∀ node, (M node).IsFeasible (q node))
    (hparent : ∀ node, (M node).parentLaw (q node) = β node) :
    (∑ node, weight node * (M node).pooledRetainedRate (fixed node)) +
        ∑ node, weight node *
          (β node).quadraticKlLowerBits (M node).decoupledParent ≤
      ∑ node, weight node * retainedRate (fixed node) (q node) := by
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun node _ ↦ by
    have hlocal := pooledRetainedRate_add_quadratic_le_retainedRate
      (M node) (q node) (β node) (fixed node) (hfeasible node) (hparent node)
    nlinarith [hweight node]

end CompatibilityPoolingModel

namespace RegionalExponent

variable {Region : Type u₁} [Fintype Region]

/-- A branch is active when it attains the directional minimum.  Ties are allowed. -/
def IsActive (f : Fin 3 → ℝ) (branch : Fin 3) : Prop :=
  ∀ other, f branch ≤ f other

/-- Any active branch realizes the three-way minimum. -/
theorem threeWayMin_eq_of_isActive {f : Fin 3 → ℝ} {branch : Fin 3}
    (hactive : IsActive f branch) :
    threeWayMin f = f branch := by
  fin_cases branch
  · exact min_eq_left (le_min (hactive 1) (hactive 2))
  · change threeWayMin f = f 1
    have h12 : f 1 ≤ f 2 := by simpa using hactive 2
    have h10 : f 1 ≤ f 0 := by simpa using hactive 0
    rw [threeWayMin, min_eq_left h12, min_eq_right h10]
  · exact threeWayMin_eq_two (hactive 0) (hactive 1)

/-- Add an independently certified correction to every directional branch. -/
def addCorrection (f correction : Fin 3 → ℝ) (branch : Fin 3) : ℝ :=
  f branch + correction branch

/-- Nonnegative directional corrections cannot decrease the retained minimum. -/
theorem threeWayMin_le_addCorrection
    (f correction : Fin 3 → ℝ) (hcorrection : ∀ branch, 0 ≤ correction branch) :
    threeWayMin f ≤ threeWayMin (addCorrection f correction) := by
  apply threeWayMin_mono
  intro branch
  exact le_add_of_nonneg_right (hcorrection branch)

/-- If the same branch is active before and after correction, its correction is exactly the
increase in the retained minimum. -/
theorem threeWayMin_addCorrection_sub_eq
    (f correction : Fin 3 → ℝ) (branch : Fin 3)
    (hbefore : IsActive f branch)
    (hafter : IsActive (addCorrection f correction) branch) :
    threeWayMin (addCorrection f correction) - threeWayMin f = correction branch := by
  rw [threeWayMin_eq_of_isActive hafter, threeWayMin_eq_of_isActive hbefore]
  simp [addCorrection]

/-- Certificate that a correction of at least `floor` is fully visible in the retained minimum.
The distinguished active branch is an explicit parameter rather than being hard-coded to one
physical direction. -/
structure ActiveBranchCertificate (branch : Fin 3) (floor : ℝ) where
  baseline : Fin 3 → ℝ
  correction : Fin 3 → ℝ
  activeBefore : IsActive baseline branch
  activeAfter : IsActive (addCorrection baseline correction) branch
  floor_le_correction : floor ≤ correction branch

/-- Retained-minimum gain represented by a generic active-branch certificate. -/
noncomputable def ActiveBranchCertificate.retainedGain
    {branch : Fin 3} {floor : ℝ} (C : ActiveBranchCertificate branch floor) : ℝ :=
  threeWayMin (addCorrection C.baseline C.correction) - threeWayMin C.baseline

theorem ActiveBranchCertificate.retainedGain_eq
    {branch : Fin 3} {floor : ℝ} (C : ActiveBranchCertificate branch floor) :
    C.retainedGain = C.correction branch :=
  threeWayMin_addCorrection_sub_eq C.baseline C.correction branch
    C.activeBefore C.activeAfter

theorem ActiveBranchCertificate.floor_le_retainedGain
    {branch : Fin 3} {floor : ℝ} (C : ActiveBranchCertificate branch floor) :
    floor ≤ C.retainedGain := by
  rw [C.retainedGain_eq]
  exact C.floor_le_correction

/-- Sum of the directional bottleneck exponents over all regions. -/
noncomputable def regionalTotal (branches : Region → Fin 3 → ℝ) : ℝ :=
  ∑ region, threeWayMin (branches region)

/-- Adding nonnegative branch corrections cannot decrease the total retained exponent. -/
theorem regionalTotal_le_addCorrection
    (branches correction : Region → Fin 3 → ℝ)
    (hcorrection : ∀ region branch, 0 ≤ correction region branch) :
    regionalTotal branches ≤
      regionalTotal (fun region ↦ addCorrection (branches region) (correction region)) := by
  exact Finset.sum_le_sum fun region _ ↦
    threeWayMin_le_addCorrection (branches region) (correction region) (hcorrection region)

/-- Exact active-branch accounting for an arbitrary finite collection of regions.  In
particular, neither a globally fixed active direction nor a six-distinct-orientations hypothesis
is needed at this scalar stage. -/
theorem regionalTotal_addCorrection_sub_eq
    (branches correction : Region → Fin 3 → ℝ)
    (active : Region → Fin 3)
    (hbefore : ∀ region, IsActive (branches region) (active region))
    (hafter : ∀ region,
      IsActive (addCorrection (branches region) (correction region)) (active region)) :
    regionalTotal (fun region ↦ addCorrection (branches region) (correction region)) -
        regionalTotal branches =
      ∑ region, correction region (active region) := by
  rw [regionalTotal, regionalTotal, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun region _ ↦
    threeWayMin_addCorrection_sub_eq
      (branches region) (correction region) (active region)
      (hbefore region) (hafter region)

section Stagewise

variable {Stage : Type u₂} [Fintype Stage]

/-- Sum of retained regional exponents across sequential stages.  At the scalar level this is the
logarithm of the product of the stagewise copy counts. -/
noncomputable def stagewiseTotal
    (branches : Stage → Region → Fin 3 → ℝ) : ℝ :=
  ∑ stage, regionalTotal (branches stage)

/-- Exact stagewise composition of active parent-consistency gains.  Each stage has its own
regional minimum, so the right side is a sum of local corrections rather than a single KL term
on a joint probability space. -/
theorem stagewiseTotal_addCorrection_sub_eq
    (branches correction : Stage → Region → Fin 3 → ℝ)
    (active : Stage → Region → Fin 3)
    (hbefore : ∀ stage region,
      IsActive (branches stage region) (active stage region))
    (hafter : ∀ stage region,
      IsActive
        (addCorrection (branches stage region) (correction stage region))
        (active stage region)) :
    stagewiseTotal
        (fun stage region ↦ addCorrection (branches stage region) (correction stage region)) -
        stagewiseTotal branches =
      ∑ stage, ∑ region, correction stage region (active stage region) := by
  rw [stagewiseTotal, stagewiseTotal, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun stage _ ↦
    regionalTotal_addCorrection_sub_eq
      (branches stage) (correction stage) (active stage)
      (hbefore stage) (hafter stage)

end Stagewise

end RegionalExponent

end AlgebraicComplexity
