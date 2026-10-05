/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.RecursiveSplitCertificateGeometry
import AlgebraicComplexity.Probability.Pushforward
import Mathlib.Data.Finset.Sym
import MatrixMultiplication.SupportRestrictedConditionalIntegerEntropyDualNormalized

set_option autoImplicit false

/-!
# The categorical integer dual used by the level-four A5 program

This file is the finite adapter between genuine level-four parent-local slots and the
support-restricted conditional integer dual.  Its three categorical factors are the logical
`X` coordinate, the logical `Y` coordinate, and the boundary complement orbit (with one pooled
interior category).  Conditioning is on the logical `Z` coordinate.

The resulting row partition is definitionally

`sum_u if coordZ u = z then weight u else 0`.

Thus a later generated certificate only has to provide positive integer factors and bounds for
these finite row sums.  This module does not identify the program with a CW competitor family and
does not contain any generated numerical row.

## References

- [alman2025more] Josh Alman et al., *More Asymmetry Yields Faster Matrix Multiplication*.
- [dupont2026improving] Emilien Dupont et al., *Improving the Matrix Multiplication Exponent with
  Modern Optimization and AlphaEvolve*.
-/

open scoped BigOperators

namespace MatrixMultiplication.LevelFourA5CategoricalConditionalIntegerDual

open AlgebraicComplexity
open AlgebraicComplexity.LevelFourReconstruction
open AlgebraicComplexity.MoreAsymmetryCompatibility
open AlgebraicComplexity.Tensor

noncomputable section

universe u

/-- The nine possible coordinates of a total-eight child shape. -/
abbrev LevelFourA5Coordinate := Fin 9

/-- One logical coordinate of a genuine parent-local level-four child slot. -/
def levelFourA5Coordinate
    (parent : Fin positiveLevelFourShapeCount) (sigma : Orientation) (c : Leg)
    (slot : LevelFourValidSlot parent) : LevelFourA5Coordinate :=
  ExactRecursiveSplitType.coordinate c (levelFourChildShape parent sigma slot)

/-- Boundary states remembered by logical-`Z` compatibility. -/
def levelFourA5Boundary
    (parent : Fin positiveLevelFourShapeCount) (sigma : Orientation)
    (slot : LevelFourValidSlot parent) : Prop :=
  (levelFourChildShape parent sigma slot).get .X = 0 ∨
    (levelFourChildShape parent sigma slot).get .Y = 0

/-- A complement orbit is remembered when either of its two representatives is on the logical
`X/Y` boundary. -/
def levelFourA5BoundaryOrbitRelevant
    (parent : Fin positiveLevelFourShapeCount) (sigma : Orientation)
    (slot : LevelFourValidSlot parent) : Prop :=
  levelFourA5Boundary parent sigma slot ∨
    levelFourA5Boundary parent sigma (levelFourComplementSlot parent slot)

/-- Boundary complement orbits, together with one pooled interior category. -/
abbrev LevelFourA5BoundaryCategory (parent : Fin positiveLevelFourShapeCount) :=
  Option (Sym2 (LevelFourValidSlot parent))

/-- Canonical categorical label of a slot.  A boundary-relevant orbit is represented by its
unordered complementary pair, while all other slots use the single pooled label `none`. -/
def levelFourA5BoundaryCategory
    (parent : Fin positiveLevelFourShapeCount) (sigma : Orientation)
    (slot : LevelFourValidSlot parent) : LevelFourA5BoundaryCategory parent :=
  by
    classical
    exact if levelFourA5BoundaryOrbitRelevant parent sigma slot then
      some (s(slot, levelFourComplementSlot parent slot))
    else none

/-- Boundary relevance is invariant under the complementary-slot involution. -/
theorem levelFourA5BoundaryOrbitRelevant_complement_iff
    (parent : Fin positiveLevelFourShapeCount) (sigma : Orientation)
    (slot : LevelFourValidSlot parent) :
    levelFourA5BoundaryOrbitRelevant parent sigma
        (levelFourComplementSlot parent slot) ↔
      levelFourA5BoundaryOrbitRelevant parent sigma slot := by
  rw [levelFourA5BoundaryOrbitRelevant, levelFourA5BoundaryOrbitRelevant,
    levelFourComplementSlot_involutive parent slot]
  exact or_comm

/-- The boundary label is genuinely a complement-orbit label, including for self-complementary
slots. -/
theorem levelFourA5BoundaryCategory_complement
    (parent : Fin positiveLevelFourShapeCount) (sigma : Orientation)
    (slot : LevelFourValidSlot parent) :
    levelFourA5BoundaryCategory parent sigma (levelFourComplementSlot parent slot) =
      levelFourA5BoundaryCategory parent sigma slot := by
  classical
  unfold levelFourA5BoundaryCategory
  rw [levelFourComplementSlot_involutive parent slot]
  by_cases h : levelFourA5BoundaryOrbitRelevant parent sigma slot
  · have hc : levelFourA5BoundaryOrbitRelevant parent sigma
        (levelFourComplementSlot parent slot) :=
      (levelFourA5BoundaryOrbitRelevant_complement_iff parent sigma slot).2 h
    simp [h, hc, Sym2.eq_swap]
  · have hc : ¬levelFourA5BoundaryOrbitRelevant parent sigma
        (levelFourComplementSlot parent slot) := by
      exact fun hc ↦ h
        ((levelFourA5BoundaryOrbitRelevant_complement_iff parent sigma slot).1 hc)
    simp [h, hc]

/-- Positive integer factors for the three A5 categorical features. -/
structure CategoricalIntegerWeights
    (parent : Fin positiveLevelFourShapeCount) (sigma : Orientation) where
  xFactor : LevelFourA5Coordinate → ℕ
  yFactor : LevelFourA5Coordinate → ℕ
  boundaryFactor : LevelFourA5BoundaryCategory parent → ℕ
  xFactor_pos : ∀ x, 0 < xFactor x
  yFactor_pos : ∀ y, 0 < yFactor y
  boundaryFactor_pos : ∀ boundary, 0 < boundaryFactor boundary

/-- The positive categorical product weight used by the A5 checker. -/
def categoricalProductWeight
    {parent : Fin positiveLevelFourShapeCount} {sigma : Orientation}
    (weights : CategoricalIntegerWeights parent sigma)
    (slot : LevelFourValidSlot parent) : ℕ :=
  weights.xFactor (levelFourA5Coordinate parent sigma .X slot) *
    weights.yFactor (levelFourA5Coordinate parent sigma .Y slot) *
      weights.boundaryFactor (levelFourA5BoundaryCategory parent sigma slot)

/-- Every categorical product weight is strictly positive. -/
theorem categoricalProductWeight_pos
    {parent : Fin positiveLevelFourShapeCount} {sigma : Orientation}
    (weights : CategoricalIntegerWeights parent sigma)
    (slot : LevelFourValidSlot parent) :
    0 < categoricalProductWeight weights slot := by
  exact Nat.mul_pos
    (Nat.mul_pos (weights.xFactor_pos _) (weights.yFactor_pos _))
    (weights.boundaryFactor_pos _)

/-- The logarithm of the product factor is the sum of its three categorical potentials. -/
theorem log_categoricalProductWeight
    {parent : Fin positiveLevelFourShapeCount} {sigma : Orientation}
    (weights : CategoricalIntegerWeights parent sigma)
    (slot : LevelFourValidSlot parent) :
    Real.log (categoricalProductWeight weights slot : ℝ) =
      Real.log (weights.xFactor
        (levelFourA5Coordinate parent sigma .X slot) : ℝ) +
      Real.log (weights.yFactor
        (levelFourA5Coordinate parent sigma .Y slot) : ℝ) +
      Real.log (weights.boundaryFactor
        (levelFourA5BoundaryCategory parent sigma slot) : ℝ) := by
  have hx : (weights.xFactor
      (levelFourA5Coordinate parent sigma .X slot) : ℝ) ≠ 0 := by
    exact_mod_cast (weights.xFactor_pos _).ne'
  have hy : (weights.yFactor
      (levelFourA5Coordinate parent sigma .Y slot) : ℝ) ≠ 0 := by
    exact_mod_cast (weights.yFactor_pos _).ne'
  have hb : (weights.boundaryFactor
      (levelFourA5BoundaryCategory parent sigma slot) : ℝ) ≠ 0 := by
    exact_mod_cast (weights.boundaryFactor_pos _).ne'
  simp only [categoricalProductWeight, Nat.cast_mul]
  rw [Real.log_mul (mul_ne_zero hx hy) hb, Real.log_mul hx hy]

/-- The fixed logarithmic moment written solely in terms of the two coordinate marginals and the
boundary-orbit/pool marginal. -/
def categoricalFixedMomentNats
    {parent : Fin positiveLevelFourShapeCount} {sigma : Orientation}
    (weights : CategoricalIntegerWeights parent sigma)
    (stateLaw : ProbabilityVector (LevelFourValidSlot parent)) : ℝ :=
  (stateLaw.pushforward
      (levelFourA5Coordinate parent sigma .X)).expectation
        (fun x ↦ Real.log (weights.xFactor x : ℝ)) +
  (stateLaw.pushforward
      (levelFourA5Coordinate parent sigma .Y)).expectation
        (fun y ↦ Real.log (weights.yFactor y : ℝ)) +
  (stateLaw.pushforward
      (levelFourA5BoundaryCategory parent sigma)).expectation
        (fun boundary ↦ Real.log (weights.boundaryFactor boundary : ℝ))

/-- The expected log product depends only on the advertised three categorical marginals. -/
theorem expectation_log_categoricalProductWeight
    {parent : Fin positiveLevelFourShapeCount} {sigma : Orientation}
    (weights : CategoricalIntegerWeights parent sigma)
    (stateLaw : ProbabilityVector (LevelFourValidSlot parent)) :
    stateLaw.expectation
        (fun slot ↦ Real.log (categoricalProductWeight weights slot : ℝ)) =
      categoricalFixedMomentNats weights stateLaw := by
  calc
    stateLaw.expectation
        (fun slot ↦ Real.log (categoricalProductWeight weights slot : ℝ)) =
      stateLaw.expectation (fun slot ↦
        Real.log (weights.xFactor
          (levelFourA5Coordinate parent sigma .X slot) : ℝ) +
        Real.log (weights.yFactor
          (levelFourA5Coordinate parent sigma .Y slot) : ℝ) +
        Real.log (weights.boundaryFactor
          (levelFourA5BoundaryCategory parent sigma slot) : ℝ)) :=
      stateLaw.expectation_congr (log_categoricalProductWeight weights)
    _ =
      stateLaw.expectation (fun slot ↦
        Real.log (weights.xFactor
          (levelFourA5Coordinate parent sigma .X slot) : ℝ)) +
      stateLaw.expectation (fun slot ↦
        Real.log (weights.yFactor
          (levelFourA5Coordinate parent sigma .Y slot) : ℝ)) +
      stateLaw.expectation (fun slot ↦
        Real.log (weights.boundaryFactor
          (levelFourA5BoundaryCategory parent sigma slot) : ℝ)) := by
      rw [ProbabilityVector.expectation_add, ProbabilityVector.expectation_add]
    _ = categoricalFixedMomentNats weights stateLaw := by
      unfold categoricalFixedMomentNats
      rw [ProbabilityVector.pushforward_expectation,
        ProbabilityVector.pushforward_expectation,
        ProbabilityVector.pushforward_expectation]
      rfl

/-- The unconditional state law of a finite channel. -/
def channelStateLaw
    {Z : Type u} [Fintype Z]
    {parent : Fin positiveLevelFourShapeCount}
    (outer : ProbabilityVector Z)
    (rows : Z → ProbabilityVector (LevelFourValidSlot parent)) :
    ProbabilityVector (LevelFourValidSlot parent) :=
  outer.mixture rows

/-- A state-only score has channel expectation equal to its expectation under the channel
mixture. -/
theorem integerWeightExpectationNats_eq_channelStateLaw_expectation
    {Z : Type u} [Fintype Z]
    {parent : Fin positiveLevelFourShapeCount} {sigma : Orientation}
    (outer : ProbabilityVector Z)
    (rows : Z → ProbabilityVector (LevelFourValidSlot parent))
    (weights : CategoricalIntegerWeights parent sigma) :
    ConditionalIntegerEntropyDual.integerWeightExpectationNats outer rows
        (fun _ slot ↦ categoricalProductWeight weights slot) =
      (channelStateLaw outer rows).expectation
        (fun slot ↦ Real.log (categoricalProductWeight weights slot : ℝ)) := by
  unfold ConditionalIntegerEntropyDual.integerWeightExpectationNats
    channelStateLaw ProbabilityVector.expectation
  simp only [ProbabilityVector.mixture_weight]
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  simp_rw [mul_assoc]
  exact Finset.sum_comm

/-- Consequently, the score expectation is fixed by the two coordinate marginals and the
boundary-orbit/pool marginal of the channel's unconditional state law. -/
theorem integerWeightExpectationNats_eq_categoricalFixedMoment
    {Z : Type u} [Fintype Z]
    {parent : Fin positiveLevelFourShapeCount} {sigma : Orientation}
    (outer : ProbabilityVector Z)
    (rows : Z → ProbabilityVector (LevelFourValidSlot parent))
    (weights : CategoricalIntegerWeights parent sigma) :
    ConditionalIntegerEntropyDual.integerWeightExpectationNats outer rows
        (fun _ slot ↦ categoricalProductWeight weights slot) =
      categoricalFixedMomentNats weights (channelStateLaw outer rows) := by
  rw [integerWeightExpectationNats_eq_channelStateLaw_expectation,
    expectation_log_categoricalProductWeight]

/-- The canonical fixed-coordinate graph profile of an integral valid-slot profile. -/
def fixedCoordinateGraphProfile
    (parent : Fin positiveLevelFourShapeCount) (sigma : Orientation)
    (stateProfile : LevelFourValidSlot parent → ℕ) :
    LevelFourA5Coordinate × LevelFourValidSlot parent → ℕ :=
  fun entry ↦
    if levelFourA5Coordinate parent sigma .Z entry.2 = entry.1 then
      stateProfile entry.2
    else 0

/-- The fixed-coordinate graph profile vanishes away from its defining graph. -/
theorem fixedCoordinateGraphProfile_zero_off_graph
    (parent : Fin positiveLevelFourShapeCount) (sigma : Orientation)
    (stateProfile : LevelFourValidSlot parent → ℕ)
    (z : LevelFourA5Coordinate) (slot : LevelFourValidSlot parent)
    (hoff : levelFourA5Coordinate parent sigma .Z slot ≠ z) :
    fixedCoordinateGraphProfile parent sigma stateProfile (z, slot) = 0 := by
  simp [fixedCoordinateGraphProfile, hoff]

/-- Forgetting the fixed coordinate recovers the literal state profile. -/
theorem mappedType_snd_fixedCoordinateGraphProfile
    (parent : Fin positiveLevelFourShapeCount) (sigma : Orientation)
    (stateProfile : LevelFourValidSlot parent → ℕ) :
    WordType.mappedType Prod.snd
        (fixedCoordinateGraphProfile parent sigma stateProfile) = stateProfile := by
  classical
  funext slot
  rw [WordType.mappedType_eq_sum_ite, Fintype.sum_prod_type]
  simp [fixedCoordinateGraphProfile]

/-- Adding the deterministic coordinate label preserves total profile mass. -/
theorem profileMass_fixedCoordinateGraphProfile
    (parent : Fin positiveLevelFourShapeCount) (sigma : Orientation)
    (stateProfile : LevelFourValidSlot parent → ℕ) :
    WordType.profileMass (fixedCoordinateGraphProfile parent sigma stateProfile) =
      WordType.profileMass stateProfile := by
  rw [← WordType.profileMass_mappedType Prod.snd
    (fixedCoordinateGraphProfile parent sigma stateProfile),
    mappedType_snd_fixedCoordinateGraphProfile]

/-- One complete categorical program for a heterogeneous level-four parent.  The nonempty field
is deliberately explicit: positive profile mass supplies it in concrete clients, without
incorrectly requiring every ambient logical-`Z` coordinate to occur. -/
structure Program
    (parent : Fin positiveLevelFourShapeCount) (sigma : Orientation) where
  stateProfile : LevelFourValidSlot parent → ℕ
  stateProfileMass_pos : 0 < WordType.profileMass stateProfile
  slotNonempty : Nonempty (LevelFourValidSlot parent)
  weights : CategoricalIntegerWeights parent sigma

namespace Program

variable {parent : Fin positiveLevelFourShapeCount} {sigma : Orientation}

/-- Integral joint profile obtained by adjoining the deterministic logical-Z label. -/
def graphProfile (data : Program parent sigma) :
    LevelFourA5Coordinate × LevelFourValidSlot parent → ℕ :=
  fixedCoordinateGraphProfile parent sigma data.stateProfile

/-- The graph profile has positive mass whenever the program state profile does. -/
theorem graphProfileMass_pos (data : Program parent sigma) :
    0 < WordType.profileMass data.graphProfile := by
  rw [graphProfile, profileMass_fixedCoordinateGraphProfile]
  exact data.stateProfileMass_pos

/-- Normalized logical-Z marginal of the program's graph profile. -/
noncomputable def graphParent (data : Program parent sigma) :
    ProbabilityVector LevelFourA5Coordinate :=
  WordType.normalizedJointProfileParent data.graphProfile data.graphProfileMass_pos

/-- Zero-safe conditional state rows of the program's graph profile. -/
noncomputable def graphRows (data : Program parent sigma) :
    LevelFourA5Coordinate → ProbabilityVector (LevelFourValidSlot parent) := by
  letI : Nonempty (LevelFourValidSlot parent) := data.slotNonempty
  exact WordType.normalizedJointProfileRows data.graphProfile data.graphProfileMass_pos

/-- Normalized unconditional state law of a categorical program. -/
noncomputable def stateLaw (data : Program parent sigma) :
    ProbabilityVector (LevelFourValidSlot parent) :=
  WordType.normalizedProfileProbability data.stateProfile data.stateProfileMass_pos

/-- The canonical graph disintegration has the original normalized state profile as its
unconditional state law. -/
theorem channelStateLaw_graphParent_graphRows (data : Program parent sigma) :
    channelStateLaw data.graphParent data.graphRows = data.stateLaw := by
  classical
  letI : Nonempty (LevelFourValidSlot parent) := data.slotNonempty
  apply ProbabilityVector.ext
  funext slot
  calc
    (channelStateLaw data.graphParent data.graphRows).weight slot =
        ((data.graphParent.joint data.graphRows).pushforward Prod.snd).weight slot := by
      rw [ProbabilityVector.pushforward_joint_snd]
      rfl
    _ = ((WordType.normalizedProfileProbability data.graphProfile
          data.graphProfileMass_pos).pushforward Prod.snd).weight slot := by
      rw [graphParent, graphRows,
        WordType.normalizedJointProfileParent_joint_rows]
    _ = (WordType.mappedType Prod.snd data.graphProfile slot : ℝ) /
          (WordType.profileMass data.graphProfile : ℝ) :=
      WordType.normalizedProfileProbability_pushforward_weight
        data.graphProfile data.graphProfileMass_pos Prod.snd slot
    _ = (data.stateProfile slot : ℝ) /
          (WordType.profileMass data.stateProfile : ℝ) := by
      rw [graphProfile, mappedType_snd_fixedCoordinateGraphProfile,
        profileMass_fixedCoordinateGraphProfile]
    _ = data.stateLaw.weight slot := by
      rw [stateLaw, WordType.normalizedProfileProbability_weight]

/-- The row partition in the concrete A5 program. -/
def rowPartition (data : Program parent sigma)
    (z : LevelFourA5Coordinate) : ℕ :=
  SupportRestrictedConditionalIntegerEntropyDual.fixedCoordinateIntegerFiberPartition
    (levelFourA5Coordinate parent sigma .Z)
    (categoricalProductWeight data.weights) z

/-- Literal checker form of one row partition. -/
theorem rowPartition_eq_sum_filter (data : Program parent sigma)
    (z : LevelFourA5Coordinate) :
    data.rowPartition z =
      ∑ slot, if levelFourA5Coordinate parent sigma .Z slot = z then
        categoricalProductWeight data.weights slot else 0 :=
  rfl

/-- The partition consumed by the restricted dual is definitionally the exposed checker row. -/
theorem restrictedIntegerFiberPartition_eq_rowPartition
    (data : Program parent sigma) (z : LevelFourA5Coordinate) :
    SupportRestrictedConditionalIntegerEntropyDual.restrictedIntegerFiberPartition
        (fun z slot ↦ levelFourA5Coordinate parent sigma .Z slot = z)
        (fun _ slot ↦ categoricalProductWeight data.weights slot) z =
      data.rowPartition z :=
  rfl

/-- The fixed categorical score moment of this parent program. -/
def fixedMomentNats (data : Program parent sigma) : ℝ :=
  categoricalFixedMomentNats data.weights data.stateLaw

/-- Equality of exactly the three categorical marginals used by the product score.  No equality
of full state laws is required. -/
def SameCategoricalMarginals (data : Program parent sigma)
    (candidate : ProbabilityVector (LevelFourValidSlot parent)) : Prop :=
  candidate.pushforward (levelFourA5Coordinate parent sigma .X) =
      data.stateLaw.pushforward (levelFourA5Coordinate parent sigma .X) ∧
  candidate.pushforward (levelFourA5Coordinate parent sigma .Y) =
      data.stateLaw.pushforward (levelFourA5Coordinate parent sigma .Y) ∧
  candidate.pushforward (levelFourA5BoundaryCategory parent sigma) =
      data.stateLaw.pushforward (levelFourA5BoundaryCategory parent sigma)

/-- Matching the three categorical marginals preserves the categorical score moment. -/
theorem categoricalFixedMomentNats_eq_of_sameCategoricalMarginals
    (data : Program parent sigma)
    {candidate : ProbabilityVector (LevelFourValidSlot parent)}
    (h : data.SameCategoricalMarginals candidate) :
    categoricalFixedMomentNats data.weights candidate = data.fixedMomentNats := by
  rcases h with ⟨hX, hY, hBoundary⟩
  change categoricalFixedMomentNats data.weights candidate =
    categoricalFixedMomentNats data.weights data.stateLaw
  unfold categoricalFixedMomentNats
  rw [hX, hY, hBoundary]

/-- Feasibility premises for an arbitrary A5 competitor channel: each positive parent row lies
on the fixed-coordinate graph, and its unconditional state law has the three prescribed
categorical marginals. -/
def FeasibleRows (data : Program parent sigma)
    (rows : LevelFourA5Coordinate →
      ProbabilityVector (LevelFourValidSlot parent)) : Prop :=
  SupportRestrictedConditionalIntegerEntropyDual.RowsSupportedOnPositiveParent
      data.graphParent rows
      (fun z slot ↦ levelFourA5Coordinate parent sigma .Z slot = z) ∧
    data.SameCategoricalMarginals (channelStateLaw data.graphParent rows)

/-- The exact restricted dual evaluated by the numerical A5 row checker. -/
def categoricalDualBits (data : Program parent sigma) : ℝ :=
  (SupportRestrictedConditionalIntegerEntropyDual.restrictedIntegerPartitionLogNats
      data.graphParent
      (fun z slot ↦ levelFourA5Coordinate parent sigma .Z slot = z)
      (fun _ slot ↦ categoricalProductWeight data.weights slot) -
    data.fixedMomentNats) / Real.log 2

/-- Every feasible competitor channel is bounded by the categorical dual.  This is the
maximum-entropy-facing statement: the candidate rows are arbitrary and need not equal the
canonical source graph rows. -/
theorem conditionalEntropyBits_le_categoricalDualBits_of_feasibleRows
    (data : Program parent sigma)
    (rows : LevelFourA5Coordinate →
      ProbabilityVector (LevelFourValidSlot parent))
    (hrows : data.FeasibleRows rows) :
    (data.graphParent.joint rows).conditionalEntropyBits Prod.fst ≤
      data.categoricalDualBits := by
  classical
  letI : Nonempty (LevelFourValidSlot parent) := data.slotNonempty
  let legal : LevelFourA5Coordinate → LevelFourValidSlot parent → Prop :=
    fun z slot ↦ levelFourA5Coordinate parent sigma .Z slot = z
  let weight : LevelFourA5Coordinate → LevelFourValidSlot parent → ℕ :=
    fun _ slot ↦ categoricalProductWeight data.weights slot
  have hprofile : ∀ z slot, ¬legal z slot → data.graphProfile (z, slot) = 0 := by
    intro z slot hoff
    exact fixedCoordinateGraphProfile_zero_off_graph
      parent sigma data.stateProfile z slot (by simpa [legal] using hoff)
  have hmoment :
      ConditionalIntegerEntropyDual.integerWeightExpectationNats
          data.graphParent rows weight = data.fixedMomentNats := by
    calc
      ConditionalIntegerEntropyDual.integerWeightExpectationNats
          data.graphParent rows weight =
        categoricalFixedMomentNats data.weights
          (channelStateLaw data.graphParent rows) :=
        integerWeightExpectationNats_eq_categoricalFixedMoment
          data.graphParent rows data.weights
      _ = data.fixedMomentNats :=
        data.categoricalFixedMomentNats_eq_of_sameCategoricalMarginals hrows.2
  exact
    SupportRestrictedConditionalIntegerEntropyDual.conditionalEntropyBits_le_restrictedIntegerPartitionLog_sub_fixedMoment
        data.graphParent rows legal weight
        (fun _ slot ↦ categoricalProductWeight_pos data.weights slot)
        (SupportRestrictedConditionalIntegerEntropyDual.exists_legal_of_normalizedJointProfileParent_weight_pos
            data.graphProfile data.graphProfileMass_pos legal hprofile)
        hrows.1 data.fixedMomentNats hmoment

/-- The canonical graph rows are feasible; this is a consistency witness, not a restriction on
the arbitrary competitor rows in the preceding theorem. -/
theorem graphRows_feasible (data : Program parent sigma) :
    data.FeasibleRows data.graphRows := by
  classical
  letI : Nonempty (LevelFourValidSlot parent) := data.slotNonempty
  let legal : LevelFourA5Coordinate → LevelFourValidSlot parent → Prop :=
    fun z slot ↦ levelFourA5Coordinate parent sigma .Z slot = z
  have hprofile : ∀ z slot, ¬legal z slot → data.graphProfile (z, slot) = 0 := by
    intro z slot hoff
    exact fixedCoordinateGraphProfile_zero_off_graph
      parent sigma data.stateProfile z slot (by simpa [legal] using hoff)
  refine ⟨SupportRestrictedConditionalIntegerEntropyDual.normalizedJointProfileRows_supportedOnPositiveParent
        data.graphProfile data.graphProfileMass_pos legal hprofile, ?_⟩
  unfold SameCategoricalMarginals
  rw [channelStateLaw_graphParent_graphRows]
  exact ⟨rfl, rfl, rfl⟩

/-- The concrete fixed-coordinate graph channel is bounded by the categorical dual.  Legal-row
nonemptiness is derived only at positive parent mass; unused ambient `Fin 9` rows impose no
surjectivity premise. -/
theorem graphConditionalEntropyBits_le_categoricalDualBits
    (data : Program parent sigma) :
    (data.graphParent.joint data.graphRows).conditionalEntropyBits Prod.fst ≤
      data.categoricalDualBits := by
  exact data.conditionalEntropyBits_le_categoricalDualBits_of_feasibleRows
    data.graphRows data.graphRows_feasible

end Program

/-- Heterogeneous-parent aggregation.  A later 225-row generated client may choose a different
parent shape, state profile, and integer factor table at every row. -/
theorem sum_mass_mul_graphConditionalEntropyBits_le_categoricalDualBits
    {I : Type u} [Fintype I]
    (parent : I → Fin positiveLevelFourShapeCount)
    (sigma : I → Orientation)
    (data : ∀ i, Program (parent i) (sigma i))
    (outerMass : I → ℝ) (houterMass : ∀ i, 0 ≤ outerMass i) :
    (∑ i, outerMass i *
      (((data i).graphParent.joint (data i).graphRows).conditionalEntropyBits Prod.fst)) ≤
      ∑ i, outerMass i * (data i).categoricalDualBits := by
  apply Finset.sum_le_sum
  intro i _
  exact mul_le_mul_of_nonneg_left
    ((data i).graphConditionalEntropyBits_le_categoricalDualBits)
    (houterMass i)

/-- Heterogeneous aggregation for arbitrary feasible competitor channels.  This is the form
intended for a later generated 225-row client. -/
theorem sum_mass_mul_conditionalEntropyBits_le_categoricalDualBits_of_feasibleRows
    {I : Type u} [Fintype I]
    (parent : I → Fin positiveLevelFourShapeCount)
    (sigma : I → Orientation)
    (data : ∀ i, Program (parent i) (sigma i))
    (rows : ∀ i, LevelFourA5Coordinate →
      ProbabilityVector (LevelFourValidSlot (parent i)))
    (hrows : ∀ i, (data i).FeasibleRows (rows i))
    (outerMass : I → ℝ) (houterMass : ∀ i, 0 ≤ outerMass i) :
    (∑ i, outerMass i *
      (((data i).graphParent.joint (rows i)).conditionalEntropyBits Prod.fst)) ≤
      ∑ i, outerMass i * (data i).categoricalDualBits := by
  apply Finset.sum_le_sum
  intro i _
  exact mul_le_mul_of_nonneg_left
    ((data i).conditionalEntropyBits_le_categoricalDualBits_of_feasibleRows
      (rows i) (hrows i))
    (houterMass i)

end

end MatrixMultiplication.LevelFourA5CategoricalConditionalIntegerDual
