/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Probability.Finite
import Mathlib.Tactic.FinCases

/-!
# Regional bottleneck exponents

Asymmetric laser arguments assign every standard orientation slot three branch totals and retain
their minimum.  At a constituent stage, each branch total is a sum over all interface terms.

This file proves the exact one-hot specialization used by time-sharing clients that repeat one
active orientation slot.  All terms select the same active standard slot.  The active slot keeps the minimum of the three
*aggregated* term sums, every inactive slot contributes zero, and summing over standard slots
therefore recovers exactly the desired regional exponent.  In particular, no sum of per-term
minima is introduced.

The three-way bottleneck `threeWayMin` and its order lemmas need nothing but a linear order on
the branch values, so they are stated over an arbitrary `LinearOrder`.  The branch corrections
and the slot aggregation, which use addition and probability weights, stay real-valued.
-/

open scoped BigOperators

namespace AlgebraicComplexity

universe u v

namespace RegionalExponent

variable {Term : Type u} {Slot : Type v}
variable [Fintype Term] [Fintype Slot] [DecidableEq Slot]

section ThreeWayMin

/-! Branch values are only ever compared, so the three-way bottleneck and its order lemmas are
stated over an arbitrary linear order.  The regional-exponent definitions below instantiate
`α = ℝ`, so real-valued clients are unaffected. -/

variable {α : Type*} [LinearOrder α]

/-- The minimum of the three directional branch values. -/
def threeWayMin (f : Fin 3 → α) : α :=
  min (f 0) (min (f 1) (f 2))

/-- Monotonicity of the three directional bottleneck. -/
theorem threeWayMin_mono {f g : Fin 3 → α} (h : ∀ b, f b ≤ g b) :
    threeWayMin f ≤ threeWayMin g := by
  unfold threeWayMin
  exact min_le_min (h 0) (min_le_min (h 1) (h 2))

/-- The three-way bottleneck is below every individual branch value. -/
theorem threeWayMin_le (f : Fin 3 → α) (b : Fin 3) : threeWayMin f ≤ f b := by
  fin_cases b
  · exact min_le_left _ _
  · exact le_trans (min_le_right _ _) (min_le_left _ _)
  · exact le_trans (min_le_right _ _) (min_le_right _ _)

/-- A value below all three directional branches is below their bottleneck. -/
theorem le_threeWayMin {a : α} {f : Fin 3 → α} (h : ∀ b, a ≤ f b) :
    a ≤ threeWayMin f := by
  exact le_min (h 0) (le_min (h 1) (h 2))

/-- If branch `b₀` is a bottleneck, the three-way minimum is its value. -/
theorem threeWayMin_eq_of_forall_le {f : Fin 3 → α} {b₀ : Fin 3}
    (h : ∀ b, f b₀ ≤ f b) : threeWayMin f = f b₀ :=
  le_antisymm (threeWayMin_le f b₀) (le_min (h 0) (le_min (h 1) (h 2)))

/-- If branch two is a bottleneck, the three-way minimum is its value.  This is the
`b₀ = 2` case of `threeWayMin_eq_of_forall_le`, the third branch comparison being
reflexivity. -/
theorem threeWayMin_eq_two {f : Fin 3 → α}
    (h20 : f 2 ≤ f 0) (h21 : f 2 ≤ f 1) :
    threeWayMin f = f 2 := by
  refine threeWayMin_eq_of_forall_le fun b ↦ ?_
  fin_cases b
  · exact h20
  · exact h21
  · exact le_rfl

end ThreeWayMin

/-- Add a correction to the directional branch `b₀`, leaving the other two branches
unchanged. -/
def correctBranch (b₀ : Fin 3) (f : Fin 3 → ℝ) (c : ℝ) (b : Fin 3) : ℝ :=
  if b = b₀ then f b + c else f b

/-- The corrected branch receives exactly the correction. -/
@[simp] theorem correctBranch_self (b₀ : Fin 3) (f : Fin 3 → ℝ) (c : ℝ) :
    correctBranch b₀ f c b₀ = f b₀ + c := by
  simp [correctBranch]

/-- Branches other than the corrected one are unchanged. -/
theorem correctBranch_of_ne (b₀ : Fin 3) (f : Fin 3 → ℝ) (c : ℝ)
    {b : Fin 3} (h : b ≠ b₀) : correctBranch b₀ f c b = f b := by
  simp [correctBranch, h]

/-- If branch `b₀` is a bottleneck both before and after receiving a correction, the retained
exponent increases by exactly that correction. -/
theorem threeWayMin_correctBranch_sub {f : Fin 3 → ℝ} {c : ℝ} {b₀ : Fin 3}
    (h : ∀ b, f b₀ ≤ f b) (hc : ∀ b, b ≠ b₀ → f b₀ + c ≤ f b) :
    threeWayMin (correctBranch b₀ f c) - threeWayMin f = c := by
  have hcorr : ∀ b, correctBranch b₀ f c b₀ ≤ correctBranch b₀ f c b := by
    intro b
    by_cases hb : b = b₀
    · subst hb
      exact le_refl _
    · rw [correctBranch_self, correctBranch_of_ne _ _ _ hb]
      exact hc b hb
  rw [threeWayMin_eq_of_forall_le h, threeWayMin_eq_of_forall_le hcorr, correctBranch_self]
  simp

/-- Add a correction to directional branch two.  Specialization of `correctBranch` retained for
existing clients. -/
abbrev correctBranchTwo (f : Fin 3 → ℝ) (c : ℝ) : Fin 3 → ℝ :=
  correctBranch 2 f c

/-- Branch zero is unchanged by a branch-two correction. -/
@[simp] theorem correctBranchTwo_zero (f : Fin 3 → ℝ) (c : ℝ) :
    correctBranchTwo f c 0 = f 0 := by
  simp [correctBranch]

/-- Branch one is unchanged by a branch-two correction. -/
@[simp] theorem correctBranchTwo_one (f : Fin 3 → ℝ) (c : ℝ) :
    correctBranchTwo f c 1 = f 1 := by
  simp [correctBranch]

/-- Branch two receives exactly the branch-two correction. -/
@[simp] theorem correctBranchTwo_two (f : Fin 3 → ℝ) (c : ℝ) :
    correctBranchTwo f c 2 = f 2 + c := by
  simp

/-- If branch two remains active after receiving a correction, the retained exponent increases
by exactly that correction.  Specialization of `threeWayMin_correctBranch_sub` at `b₀ = 2`. -/
theorem threeWayMin_correctBranchTwo_sub
    {f : Fin 3 → ℝ} {c : ℝ}
    (h20 : f 2 ≤ f 0) (h21 : f 2 ≤ f 1)
    (hc20 : f 2 + c ≤ f 0) (hc21 : f 2 + c ≤ f 1) :
    threeWayMin (correctBranchTwo f c) - threeWayMin f = c := by
  refine threeWayMin_correctBranch_sub (b₀ := 2) (fun b => ?_) (fun b hb => ?_)
  · fin_cases b
    · exact h20
    · exact h21
    · exact le_refl _
  · fin_cases b
    · exact hc20
    · exact hc21
    · exact absurd rfl hb

/-- A branch total in one standard slot.  `multiplicity t` contains all outer regional scaling
for term `t`; `value t s b` is its unweighted contribution to branch `b` in slot `s`. -/
noncomputable def branchTotal
    (weights : Term → ProbabilityVector Slot) (multiplicity : Term → ℝ)
    (value : Term → Slot → Fin 3 → ℝ) (s : Slot) (b : Fin 3) : ℝ :=
  ∑ t, (weights t).weight s * multiplicity t * value t s b

/-- Retained exponent of a standard slot: the bottleneck of its three aggregated branches. -/
noncomputable def slotExponent
    (weights : Term → ProbabilityVector Slot) (multiplicity : Term → ℝ)
    (value : Term → Slot → Fin 3 → ℝ) (s : Slot) : ℝ :=
  threeWayMin fun b ↦ branchTotal weights multiplicity value s b

/-- Sum of retained exponents over all standard slots. -/
noncomputable def totalExponent
    (weights : Term → ProbabilityVector Slot) (multiplicity : Term → ℝ)
    (value : Term → Slot → Fin 3 → ℝ) : ℝ :=
  ∑ s, slotExponent weights multiplicity value s

omit [DecidableEq Slot] in
/-- A family of per-slot lower bounds satisfying all three branch constraints gives a lower
bound on the total retained exponent.  This is the certificate-facing form of the linear program
`maximize ∑_s floor(s)` subject to `floor(s) ≤ branchTotal(s,b)` for every branch `b`. -/
theorem sum_slotLowerBound_le_totalExponent
    (weights : Term → ProbabilityVector Slot) (multiplicity : Term → ℝ)
    (value : Term → Slot → Fin 3 → ℝ) (floor : Slot → ℝ)
    (hfloor : ∀ s b, floor s ≤ branchTotal weights multiplicity value s b) :
    (∑ s, floor s) ≤ totalExponent weights multiplicity value := by
  unfold totalExponent slotExponent
  exact Finset.sum_le_sum fun s _hs ↦ le_threeWayMin (hfloor s)

/-- In the selected slot, shared point-mass term weights recover the complete sum over terms. -/
@[simp] theorem branchTotal_constantPointMass_active
    (active : Slot) (multiplicity : Term → ℝ)
    (value : Term → Slot → Fin 3 → ℝ) (b : Fin 3) :
    branchTotal (ProbabilityVector.constantPointMass (κ := Term) active)
        multiplicity value active b =
      ∑ t, multiplicity t * value t active b := by
  simp [branchTotal, ProbabilityVector.constantPointMass]

/-- Every nonselected slot has zero branch total. -/
@[simp] theorem branchTotal_constantPointMass_inactive
    (active s : Slot) (h : s ≠ active) (multiplicity : Term → ℝ)
    (value : Term → Slot → Fin 3 → ℝ) (b : Fin 3) :
    branchTotal (ProbabilityVector.constantPointMass (κ := Term) active)
        multiplicity value s b = 0 := by
  simp [branchTotal, ProbabilityVector.constantPointMass, h]

/-- The selected slot retains the minimum of the three aggregated term sums. -/
@[simp] theorem slotExponent_constantPointMass_active
    (active : Slot) (multiplicity : Term → ℝ)
    (value : Term → Slot → Fin 3 → ℝ) :
    slotExponent (ProbabilityVector.constantPointMass (κ := Term) active)
        multiplicity value active =
      threeWayMin fun b ↦ ∑ t, multiplicity t * value t active b := by
  simp [slotExponent]

/-- A nonselected standard slot has retained exponent zero. -/
@[simp] theorem slotExponent_constantPointMass_inactive
    (active s : Slot) (h : s ≠ active) (multiplicity : Term → ℝ)
    (value : Term → Slot → Fin 3 → ℝ) :
    slotExponent (ProbabilityVector.constantPointMass (κ := Term) active)
        multiplicity value s = 0 := by
  simp [slotExponent, threeWayMin, h]

/-- Summing over all standard slots after a shared point-mass specialization leaves exactly the
three-way minimum of the aggregated branch sums in the active slot. -/
theorem totalExponent_constantPointMass
    (active : Slot) (multiplicity : Term → ℝ)
    (value : Term → Slot → Fin 3 → ℝ) :
    totalExponent (ProbabilityVector.constantPointMass (κ := Term) active)
        multiplicity value =
      threeWayMin fun b ↦ ∑ t, multiplicity t * value t active b := by
  classical
  rw [totalExponent, Finset.sum_eq_single active]
  · exact slotExponent_constantPointMass_active active multiplicity value
  · intro s _ hs
    exact slotExponent_constantPointMass_inactive active s hs multiplicity value
  · simp

/-! ## Pooling terms with a common orientation -/

/-- With a deterministic slot assignment, the branch total in slot `s` is the sum over exactly
the terms assigned to `s`.

For the regional laser application, `Slot` is the set of tensor-leg orientations.  This identity
is purely arithmetic: its semantic use requires one *joint* hashing/compatibility invocation for
all terms in an assignment fiber. -/
@[simp] theorem branchTotal_pointMassAssignment
    (assignment : Term → Slot) (multiplicity : Term → ℝ)
    (value : Term → Slot → Fin 3 → ℝ) (s : Slot) (b : Fin 3) :
    branchTotal (fun t ↦ ProbabilityVector.pointMass (assignment t))
        multiplicity value s b =
      ∑ t, if s = assignment t then multiplicity t * value t s b else 0 := by
  classical
  unfold branchTotal
  apply Finset.sum_congr rfl
  intro t _ht
  by_cases h : s = assignment t
  · simp [h]
  · simp [h]

/-- Exact orientation-fiber aggregation formula for deterministic regional assignments.

Each slot takes one minimum *after* summing the branch contributions of every term assigned to
that slot, and the slot contributions are then added.  Thus repeated orientations may be pooled;
heterogeneously oriented terms remain in separate physical-coordinate hashing invocations. -/
theorem totalExponent_pointMassAssignment
    (assignment : Term → Slot) (multiplicity : Term → ℝ)
    (value : Term → Slot → Fin 3 → ℝ) :
    totalExponent (fun t ↦ ProbabilityVector.pointMass (assignment t))
        multiplicity value =
      ∑ s, threeWayMin fun b ↦
        ∑ t, if s = assignment t then multiplicity t * value t s b else 0 := by
  classical
  unfold totalExponent slotExponent
  apply Finset.sum_congr rfl
  intro s _hs
  congr 1
  funext b
  exact branchTotal_pointMassAssignment assignment multiplicity value s b

/-- Independent per-term bottlenecks never exceed the bottleneck obtained by a sound joint
invocation which pools all terms in one fixed orientation.

This order lemma does not itself construct that joint invocation; the tensor client must first
show that all terms use the same physical isolated/compatibility legs. -/
theorem sum_threeWayMin_le_threeWayMin_sum
    (rate : Term → Fin 3 → ℝ) :
    (∑ t, threeWayMin (rate t)) ≤
      threeWayMin (fun b ↦ ∑ t, rate t b) := by
  apply le_min
  · exact Finset.sum_le_sum fun t _ht ↦ threeWayMin_le (rate t) 0
  apply le_min
  · exact Finset.sum_le_sum fun t _ht ↦ threeWayMin_le (rate t) 1
  · exact Finset.sum_le_sum fun t _ht ↦ threeWayMin_le (rate t) 2

end RegionalExponent

end AlgebraicComplexity
