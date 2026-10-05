/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Combinatorics.ConditionalWordTypeCore
import MatrixMultiplication.DyadicIntegralProfileEntropyCore
import MatrixMultiplication.LevelFourA5CategoricalConditionalIntegerDual
import MatrixMultiplication.SupportRestrictedConditionalIntegerEntropyDualForm
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

set_option autoImplicit false

/-!
# Exact signed forms for the level-four A5 categorical program

This module closes the normalization boundary between the semantic categorical conditional dual
and its exact signed-integer-log form.  For an integral state profile of mass `D`, evaluation at a
dyadic width `bits` is exactly `D / 2^bits` times the normalized categorical dual.  Consequently
the retained form composes directly with the arbitrary-feasible-channel entropy theorem.

No premise `D = 2^bits` is needed: the factor `D / 2^bits` is the outer mass used by the finite
A5 program.  The generated certificate will instantiate `bits = 32`.

This is the signed-log serialization step of the Total-Weight manuscript's dual-certificate
argument (`better_bound/paper.tex`, `sec:dual`, Proposition `prop:dual`, lines 2286–2307 in the
2026-09-06 draft), applied conditionally on the fixed-coordinate rows. The underlying
combination-loss use is [alman2025more],
`papers/sources/2404.16349/constituent.tex:113-147`. These are algebraic evaluation identities
and a conditional dual bound, not a proof of the concrete competitor encoding or an exponent
endpoint.
-/

open scoped BigOperators

namespace MatrixMultiplication.LevelFourA5CategoricalConditionalIntegerDualForm

open AlgebraicComplexity
open AlgebraicComplexity.LevelFourReconstruction
open AlgebraicComplexity.MoreAsymmetryCompatibility
open AlgebraicComplexity.Tensor
open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicIntegralProfileEntropy
open MatrixMultiplication.LevelFourA5CategoricalConditionalIntegerDual
open MatrixMultiplication.SignedDyadicLogForm
open MatrixMultiplication.SupportRestrictedConditionalIntegerEntropyDual
open MatrixMultiplication.SupportRestrictedConditionalIntegerEntropyDualForm

noncomputable section

universe u

/-- The first marginal of the fixed-coordinate graph is the literal logical-coordinate fiber
count. -/
theorem mappedType_fst_fixedCoordinateGraphProfile
    (parent : Fin positiveLevelFourShapeCount) (sigma : Orientation)
    (stateProfile : LevelFourValidSlot parent → ℕ) :
    WordType.mappedType Prod.fst
        (fixedCoordinateGraphProfile parent sigma stateProfile) =
      fixedCoordinateFiberNumerator
        (levelFourA5Coordinate parent sigma .Z) stateProfile := by
  funext z
  rw [WordType.mappedType_fst_apply]
  rfl

/-- The normalized graph parent is exactly the normalized logical-coordinate fiber count. -/
theorem graphParent_weight
    {parent : Fin positiveLevelFourShapeCount} {sigma : Orientation}
    (data : Program parent sigma) (z : LevelFourA5Coordinate) :
    data.graphParent.weight z =
      (fixedCoordinateFiberNumerator
          (levelFourA5Coordinate parent sigma .Z) data.stateProfile z : ℝ) /
        (WordType.profileMass data.stateProfile : ℝ) := by
  unfold Program.graphParent WordType.normalizedJointProfileParent
  rw [WordType.normalizedProfileProbability_pushforward_weight]
  change
    (WordType.mappedType Prod.fst
        (fixedCoordinateGraphProfile parent sigma data.stateProfile) z : ℝ) /
      (WordType.profileMass
        (fixedCoordinateGraphProfile parent sigma data.stateProfile) : ℝ) = _
  rw [congrFun
      (mappedType_fst_fixedCoordinateGraphProfile parent sigma data.stateProfile) z,
    profileMass_fixedCoordinateGraphProfile]

/-- The program state law is the literal normalized state count. -/
theorem stateLaw_weight
    {parent : Fin positiveLevelFourShapeCount} {sigma : Orientation}
    (data : Program parent sigma) (slot : LevelFourValidSlot parent) :
    data.stateLaw.weight slot =
      (data.stateProfile slot : ℝ) /
        (WordType.profileMass data.stateProfile : ℝ) := by
  unfold Program.stateLaw
  rw [WordType.normalizedProfileProbability_weight]

/-- Count-normalized expansion of the semantic categorical conditional dual. -/
theorem categoricalDualBits_eq_countExpression
    {parent : Fin positiveLevelFourShapeCount} {sigma : Orientation}
    (data : Program parent sigma) :
    data.categoricalDualBits =
      ((∑ z,
          (fixedCoordinateFiberNumerator
              (levelFourA5Coordinate parent sigma .Z) data.stateProfile z : ℝ) /
            (WordType.profileMass data.stateProfile : ℝ) *
          Real.log (fixedCoordinateIntegerFiberPartition
            (levelFourA5Coordinate parent sigma .Z)
            (categoricalProductWeight data.weights) z : ℝ)) -
        ∑ slot,
          (data.stateProfile slot : ℝ) /
            (WordType.profileMass data.stateProfile : ℝ) *
          Real.log (categoricalProductWeight data.weights slot : ℝ)) /
        Real.log 2 := by
  unfold Program.categoricalDualBits restrictedIntegerPartitionLogNats
  rw [Program.fixedMomentNats,
    ← expectation_log_categoricalProductWeight data.weights data.stateLaw]
  unfold ProbabilityVector.expectation
  simp_rw [graphParent_weight data, stateLaw_weight data]
  rfl

/-- Converting one count to the common dyadic scale commutes with normalization by the positive
total count. -/
theorem mass_mul_log2Nat_eq_normalized
    (bits total : ℕ) (htotal : 0 < total) (coefficient argument : ℕ) :
    mass bits coefficient * SignedDyadicLogForm.log2Nat argument =
      mass bits total *
        (((coefficient : ℝ) / (total : ℝ) * Real.log (argument : ℝ)) /
          Real.log 2) := by
  have htotalReal : (total : ℝ) ≠ 0 := by exact_mod_cast htotal.ne'
  have hpow : (2 : ℝ) ^ bits ≠ 0 := by positivity
  have hlogTwo : Real.log (2 : ℝ) ≠ 0 :=
    (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'
  unfold mass SignedDyadicLogForm.log2Nat
  field_simp [htotalReal, hpow, hlogTwo]
  <;> ring

/-- Exact signed form of the mass-weighted categorical conditional dual. -/
def categoricalDualForm
    {parent : Fin positiveLevelFourShapeCount} {sigma : Orientation}
    (data : Program parent sigma) : Form :=
  fixedCoordinateDualForm
    (levelFourA5Coordinate parent sigma .Z)
    data.stateProfile (categoricalProductWeight data.weights)

/-- Evaluating the exact categorical dual form at width `bits` gives the program's total state
mass times its semantic categorical conditional dual. -/
theorem categoricalDualForm_eval
    {parent : Fin positiveLevelFourShapeCount} {sigma : Orientation}
    (bits : ℕ) (data : Program parent sigma) :
    Form.eval bits (categoricalDualForm data) =
      mass bits (WordType.profileMass data.stateProfile) *
        data.categoricalDualBits := by
  rw [categoricalDualForm, fixedCoordinateDualForm_eval,
    categoricalDualBits_eq_countExpression]
  simp_rw [mass_mul_log2Nat_eq_normalized bits
    (WordType.profileMass data.stateProfile) data.stateProfileMass_pos]
  rw [← Finset.mul_sum, ← Finset.mul_sum,
    ← Finset.sum_div, ← Finset.sum_div]
  ring

/-- The source homogeneous entropy form has the expected mass-weighted integral-profile
semantics. -/
theorem sourceEntropyForm_eval_eq_mass_mul_profileEntropyBits
    {parent : Fin positiveLevelFourShapeCount} {sigma : Orientation}
    (bits : ℕ) (data : Program parent sigma) :
    Form.eval bits (sourceEntropyForm bits data.stateProfile) =
      mass bits (WordType.profileMass data.stateProfile) *
        (WordType.profileEntropyNats data.stateProfile / Real.log 2) := by
  classical
  rw [sourceEntropyForm_eval]
  change
    MatrixMultiplication.DyadicEntropyForm.weightedEntropyList bits
        (MatrixMultiplication.SimplifiedExponentRootRecurrence.numeratorList
          data.stateProfile) = _
  rw [weightedEntropyList_numeratorList,
    weightedEntropy_eq_mass_mul_profileEntropyBits]

/-- Exact retained form for one categorical program. -/
def categoricalRetainedForm
    {parent : Fin positiveLevelFourShapeCount} {sigma : Orientation}
    (bits : ℕ) (data : Program parent sigma) : Form :=
  retainedRowForm bits
    (levelFourA5Coordinate parent sigma .Z)
    data.stateProfile (categoricalProductWeight data.weights)

/-- Evaluating the exact retained form gives the same mass times the gap between the source
profile's entropy in bits and the categorical conditional dual. -/
theorem categoricalRetainedForm_eval
    {parent : Fin positiveLevelFourShapeCount} {sigma : Orientation}
    (bits : ℕ) (data : Program parent sigma) :
    Form.eval bits (categoricalRetainedForm bits data) =
      mass bits (WordType.profileMass data.stateProfile) *
        (WordType.profileEntropyNats data.stateProfile / Real.log 2 -
          data.categoricalDualBits) := by
  unfold categoricalRetainedForm retainedRowForm
  rw [Form.eval_sub]
  change
    Form.eval bits (sourceEntropyForm bits data.stateProfile) -
      Form.eval bits (categoricalDualForm data) = _
  rw [sourceEntropyForm_eval_eq_mass_mul_profileEntropyBits,
    categoricalDualForm_eval]
  ring

/-- Literal width used by the frozen A5 source table. -/
theorem categoricalRetainedForm32_eval
    {parent : Fin positiveLevelFourShapeCount} {sigma : Orientation}
    (data : Program parent sigma) :
    Form.eval 32 (categoricalRetainedForm 32 data) =
      mass 32 (WordType.profileMass data.stateProfile) *
        (WordType.profileEntropyNats data.stateProfile / Real.log 2 -
          data.categoricalDualBits) :=
  categoricalRetainedForm_eval 32 data

/-- The exact retained form lower-bounds the true retained entropy of every feasible competitor
channel. -/
theorem categoricalRetainedForm_eval_le_of_feasibleRows
    {parent : Fin positiveLevelFourShapeCount} {sigma : Orientation}
    (bits : ℕ) (data : Program parent sigma)
    (rows : LevelFourA5Coordinate →
      ProbabilityVector (LevelFourValidSlot parent))
    (hrows : data.FeasibleRows rows) :
    Form.eval bits (categoricalRetainedForm bits data) ≤
      mass bits (WordType.profileMass data.stateProfile) *
        (WordType.profileEntropyNats data.stateProfile / Real.log 2 -
          (data.graphParent.joint rows).conditionalEntropyBits Prod.fst) := by
  rw [categoricalRetainedForm_eval]
  exact mul_le_mul_of_nonneg_left
    (sub_le_sub_left
      (data.conditionalEntropyBits_le_categoricalDualBits_of_feasibleRows rows hrows)
      (WordType.profileEntropyNats data.stateProfile / Real.log 2)) (by
        unfold mass
        positivity)

end

end MatrixMultiplication.LevelFourA5CategoricalConditionalIntegerDualForm
