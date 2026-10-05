/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Analysis.RegionalExponent
import AlgebraicComplexity.Probability.Rational
import AlgebraicComplexity.Tensor.Relation

/-!
# Rational tagged regional grouping

A constituent term may first be tagged by its outer region and then subdivided rationally among
physical orientation slots.  Terms assigned to the same slot are processed by one joint hashing
invocation, so the three directional branch totals are summed before taking their minimum.

This file separates three claims which are sometimes conflated in an informal time-sharing
argument:

* a normalized rational subdivision preserves every additive interface statistic exactly;
* an integral realization of that subdivision really does regroup the tensor factors, with no
  factor lost or duplicated; and
* any feasible family of slotwise LP floors lower-bounds the pooled regional exponent.

The tag type is arbitrary.  In the matrix-multiplication application it can be the pair
`(constituent term, outer region)`.  The tensorial theorem deliberately asks the client for one
valid transformation of the complete grouped input in each slot.  Thus it does not assert that
hashing terms with different physical orientations is sound.
-/

open scoped BigOperators

namespace AlgebraicComplexity

universe u v w

/-- A normalized rational subdivision of every tagged factor among a finite set of slots. -/
structure RationalTaggedSubdivision (Tag : Type u) (Slot : Type v) [Fintype Slot] where
  data : Tag → RationalProbabilityData Slot
  valid : ∀ tag, (data tag).IsProbability

namespace RationalTaggedSubdivision

variable {Tag : Type u} {Slot : Type v} [Fintype Slot]

/-- Rational fraction of tagged factor `tag` assigned to `slot`. -/
def weight (x : RationalTaggedSubdivision Tag Slot) (tag : Tag) (slot : Slot) : ℚ :=
  (x.data tag).weight slot

theorem weight_nonneg (x : RationalTaggedSubdivision Tag Slot) (tag : Tag) (slot : Slot) :
    0 ≤ x.weight tag slot :=
  (x.valid tag).1 slot

/-- A rational subdivision weight viewed as a nonnegative rational. -/
def nnWeight (x : RationalTaggedSubdivision Tag Slot) (tag : Tag) (slot : Slot) : ℚ≥0 :=
  ⟨x.weight tag slot, x.weight_nonneg tag slot⟩

@[simp, norm_cast] theorem coe_nnWeight
    (x : RationalTaggedSubdivision Tag Slot) (tag : Tag) (slot : Slot) :
    (x.nnWeight tag slot : ℚ) = x.weight tag slot :=
  rfl

/-- Every tagged factor is subdivided with total rational mass one. -/
@[simp] theorem sum_weight (x : RationalTaggedSubdivision Tag Slot) (tag : Tag) :
    ∑ slot, x.weight tag slot = 1 :=
  (x.valid tag).2

/-- The real probability vectors used by `RegionalExponent`. -/
noncomputable def toRealWeights (x : RationalTaggedSubdivision Tag Slot) :
    Tag → ProbabilityVector Slot :=
  fun tag ↦ (x.data tag).toReal (x.valid tag)

@[simp] theorem toRealWeights_weight
    (x : RationalTaggedSubdivision Tag Slot) (tag : Tag) (slot : Slot) :
    (x.toRealWeights tag).weight slot = (x.weight tag slot : ℝ) :=
  rfl

section AdditiveInterface

variable {M : Type w} [AddCommMonoid M] [Module ℚ M]

/-- The portion of an additive datum routed to one orientation slot. -/
def slotDatum [Fintype Tag]
    (x : RationalTaggedSubdivision Tag Slot) (datum : Tag → M) (slot : Slot) : M :=
  ∑ tag, x.weight tag slot • datum tag

/-- A single tagged datum is exactly recovered after summing all its rational pieces. -/
theorem sum_weight_smul (x : RationalTaggedSubdivision Tag Slot) (tag : Tag) (datum : M) :
    (∑ slot, x.weight tag slot • datum) = datum := by
  rw [← Finset.sum_smul, x.sum_weight, one_smul]

/-- Rational subdivision preserves the complete additive interface object, not merely its total
mass.  Taking `M = Feature → ℚ` gives simultaneous preservation of every coordinate of a
finite interface or complete-split table. -/
theorem sum_slotDatum_eq [Fintype Tag]
    (x : RationalTaggedSubdivision Tag Slot) (datum : Tag → M) :
    (∑ slot, x.slotDatum datum slot) = ∑ tag, datum tag := by
  classical
  unfold slotDatum
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro tag _htag
  exact x.sum_weight_smul tag (datum tag)

end AdditiveInterface

section ScalarInterface

variable [Fintype Tag]

/-- Total rational mass routed to one orientation slot. -/
def slotMass (x : RationalTaggedSubdivision Tag Slot)
    (mass : Tag → ℚ) (slot : Slot) : ℚ :=
  ∑ tag, x.weight tag slot * mass tag

/-- Slotwise aggregate of an arbitrary scalar interface feature. -/
def slotFeatureTotal {Feature : Type*}
    (x : RationalTaggedSubdivision Tag Slot) (mass : Tag → ℚ)
    (profile : Tag → Feature → ℚ) (slot : Slot) (feature : Feature) : ℚ :=
  ∑ tag, x.weight tag slot * (mass tag * profile tag feature)

/-- Rational time sharing preserves total tagged mass exactly. -/
theorem sum_slotMass_eq (x : RationalTaggedSubdivision Tag Slot) (mass : Tag → ℚ) :
    (∑ slot, x.slotMass mass slot) = ∑ tag, mass tag := by
  simpa only [slotMass, slotDatum, smul_eq_mul] using
    (x.sum_slotDatum_eq (M := ℚ) mass)

/-- Rational time sharing preserves every coordinate of a weighted interface/profile table.
This is the direct adapter for concatenated CSD and matrix-interface masses. -/
theorem sum_slotFeatureTotal_eq {Feature : Type*}
    (x : RationalTaggedSubdivision Tag Slot) (mass : Tag → ℚ)
    (profile : Tag → Feature → ℚ) (feature : Feature) :
    (∑ slot, x.slotFeatureTotal mass profile slot feature) =
      ∑ tag, mass tag * profile tag feature := by
  simpa only [slotFeatureTotal, slotDatum, smul_eq_mul] using
    (x.sum_slotDatum_eq (M := ℚ) (fun tag ↦ mass tag * profile tag feature))

end ScalarInterface

/-! ## Exact finite realization and tensor regrouping -/

/-- Natural copy counts realizing a rational subdivision at supplied tagged multiplicities.

The equality is deliberately part of the data-facing boundary: a certificate may clear all
denominators at one fixed power/stride and verify it by exact rational arithmetic. -/
structure NaturalRealization (x : RationalTaggedSubdivision Tag Slot)
    (multiplicity : Tag → ℕ) where
  count : Tag → Slot → ℕ
  count_cast : ∀ tag slot,
    (count tag slot : ℚ) = x.weight tag slot * (multiplicity tag : ℚ)

/-- One common denominator-clearing stride for all tagged subdivision weights. -/
noncomputable def commonStride [Fintype Tag]
    (x : RationalTaggedSubdivision Tag Slot) : ℕ :=
  ∏ p : Tag × Slot, (x.nnWeight p.1 p.2).den

/-- Numerator copy count at `commonStride`, written using the product of all other denominators. -/
noncomputable def commonCount [Fintype Tag]
    (x : RationalTaggedSubdivision Tag Slot) (tag : Tag) (slot : Slot) : ℕ := by
  classical
  exact (x.nnWeight tag slot).num *
    (Finset.univ.erase (tag, slot)).prod (fun p ↦ (x.nnWeight p.1 p.2).den)

/-- The common denominator product is strictly positive. -/
theorem commonStride_pos [Fintype Tag] (x : RationalTaggedSubdivision Tag Slot) :
    0 < x.commonStride := by
  unfold commonStride
  exact Finset.prod_pos fun p _hp ↦ (x.nnWeight p.1 p.2).den_pos

/-- The explicit numerator counts realize every rational weight at `commonStride`. -/
theorem commonCount_cast [Fintype Tag] (x : RationalTaggedSubdivision Tag Slot)
    (tag : Tag) (slot : Slot) :
    (x.commonCount tag slot : ℚ) =
      x.weight tag slot * (x.commonStride : ℚ) := by
  classical
  let q : ℚ≥0 := x.nnWeight tag slot
  let rest : ℕ :=
    (Finset.univ.erase (tag, slot)).prod (fun p ↦ (x.nnWeight p.1 p.2).den)
  have hden : (q : ℚ) * (q.den : ℚ) = (q.num : ℚ) := by
    exact_mod_cast q.mul_den_eq_num
  have hstride : x.commonStride = q.den * rest := by
    exact (Finset.mul_prod_erase Finset.univ
      (fun p : Tag × Slot ↦ (x.nnWeight p.1 p.2).den)
      (Finset.mem_univ (tag, slot))).symm
  change ((q.num * rest : ℕ) : ℚ) = (q : ℚ) * (x.commonStride : ℚ)
  rw [hstride]
  push_cast
  rw [← hden]
  ring

/-- Every finite rational tagged subdivision has an exact natural realization at one common,
positive stride. -/
noncomputable def commonNaturalRealization [Fintype Tag]
    (x : RationalTaggedSubdivision Tag Slot) :
    x.NaturalRealization (fun _tag ↦ x.commonStride) where
  count := x.commonCount
  count_cast := x.commonCount_cast

/-- Multiplying every tagged base multiplicity by the common stride realizes the same rational
subdivision, even when the base multiplicities vary from tag to tag. -/
noncomputable def scaledCommonNaturalRealization [Fintype Tag]
    (x : RationalTaggedSubdivision Tag Slot) (baseMultiplicity : Tag → ℕ) :
    x.NaturalRealization (fun tag ↦ x.commonStride * baseMultiplicity tag) where
  count tag slot := x.commonCount tag slot * baseMultiplicity tag
  count_cast tag slot := by
    rw [Nat.cast_mul, x.commonCount_cast, Nat.cast_mul]
    ring

/-- Existential form of common-denominator realization, convenient for clients which do not
care which common multiple is chosen. -/
theorem exists_positive_commonNaturalRealization [Fintype Tag]
    (x : RationalTaggedSubdivision Tag Slot) :
    ∃ stride : ℕ, 0 < stride ∧
      Nonempty (x.NaturalRealization (fun _tag ↦ stride)) :=
  ⟨x.commonStride, x.commonStride_pos, ⟨x.commonNaturalRealization⟩⟩

namespace NaturalRealization

variable {x : RationalTaggedSubdivision Tag Slot} {multiplicity : Tag → ℕ}

/-- Exact rational realization neither loses nor duplicates copies of a tagged factor. -/
theorem sum_count (realization : x.NaturalRealization multiplicity) (tag : Tag) :
    ∑ slot, realization.count tag slot = multiplicity tag := by
  have hcast : ((∑ slot, realization.count tag slot : ℕ) : ℚ) =
      (multiplicity tag : ℚ) := by
    calc
      ((∑ slot, realization.count tag slot : ℕ) : ℚ) =
          ∑ slot, (realization.count tag slot : ℚ) := by norm_cast
      _ = ∑ slot, x.weight tag slot * (multiplicity tag : ℚ) := by
        apply Finset.sum_congr rfl
        intro slot _hslot
        exact realization.count_cast tag slot
      _ = (∑ slot, x.weight tag slot) * (multiplicity tag : ℚ) := by
        rw [Finset.sum_mul]
      _ = (multiplicity tag : ℚ) := by simp
  exact_mod_cast hcast

/-- Regrouping integrally realized pieces by orientation slot is an equality in every commutative
monoid.  For tensors, multiplication is tensor product and powers are repeated tensor powers. -/
theorem prod_pow_recombine [Fintype Tag]
    {A : Type*} [CommMonoid A] (realization : x.NaturalRealization multiplicity)
    (input : Tag → A) :
    (∏ tag, input tag ^ multiplicity tag) =
      ∏ slot, ∏ tag, input tag ^ realization.count tag slot := by
  classical
  calc
    (∏ tag, input tag ^ multiplicity tag) =
        ∏ tag, input tag ^ (∑ slot, realization.count tag slot) := by
      apply Finset.prod_congr rfl
      intro tag _htag
      rw [realization.sum_count tag]
    _ = ∏ tag, ∏ slot, input tag ^ realization.count tag slot := by
      apply Finset.prod_congr rfl
      intro tag _htag
      exact (Finset.prod_pow_eq_pow_sum Finset.univ
        (realization.count tag) (input tag)).symm
    _ = ∏ slot, ∏ tag, input tag ^ realization.count tag slot := by
      exact Finset.prod_comm

/-- Sound grouped-stage assembly.  Each slot gets one transformation whose input contains all
tagged pieces routed to that common slot.  The outputs of those slotwise invocations may then be
tensorized.  This is the generic semantic theorem behind fractional orientation time sharing. -/
theorem tensorialRelation_grouped [Fintype Tag]
    {A : Type*} [CommMonoid A] (realization : x.NaturalRealization multiplicity)
    (D : TensorialRelation A) (input : Tag → A) (output : Slot → A)
    (hslot : ∀ slot,
      D.Rel (∏ tag, input tag ^ realization.count tag slot) (output slot)) :
    D.Rel (∏ tag, input tag ^ multiplicity tag) (∏ slot, output slot) := by
  rw [realization.prod_pow_recombine input]
  exact D.fintype_prod _ _ hslot

end NaturalRealization

/-! ## Pooled rational regional exponent -/

section Exponent

variable [Fintype Tag]

/-- Branch totals under rational tagged subdivision are exactly the rationally weighted sums
used by the fractional orientation LP. -/
@[simp] theorem branchTotal_toRealWeights
    (x : RationalTaggedSubdivision Tag Slot) (multiplicity : Tag → ℝ)
    (value : Tag → Slot → Fin 3 → ℝ) (slot : Slot) (branch : Fin 3) :
    RegionalExponent.branchTotal x.toRealWeights multiplicity value slot branch =
      ∑ tag, (x.weight tag slot : ℝ) * multiplicity tag * value tag slot branch := by
  rfl

/-- Exact fixed-parameter objective for fractional tagged-orientation grouping: within each
physical orientation slot, sum all fractional tagged branch contributions first, take one
three-way bottleneck, and finally add the slot bottlenecks. -/
theorem totalExponent_toRealWeights
    (x : RationalTaggedSubdivision Tag Slot) (multiplicity : Tag → ℝ)
    (value : Tag → Slot → Fin 3 → ℝ) :
    RegionalExponent.totalExponent x.toRealWeights multiplicity value =
      ∑ slot, RegionalExponent.threeWayMin fun branch ↦
        ∑ tag, (x.weight tag slot : ℝ) * multiplicity tag * value tag slot branch := by
  rfl

/-- A feasible fractional tagged-orientation LP solution certifies its complete objective as a
lower bound on the pooled regional exponent. -/
theorem sum_slotFloor_le_totalExponent
    (x : RationalTaggedSubdivision Tag Slot) (multiplicity : Tag → ℝ)
    (value : Tag → Slot → Fin 3 → ℝ) (floor : Slot → ℝ)
    (hfloor : ∀ slot branch,
      floor slot ≤
        ∑ tag, (x.weight tag slot : ℝ) * multiplicity tag * value tag slot branch) :
    (∑ slot, floor slot) ≤
      RegionalExponent.totalExponent x.toRealWeights multiplicity value := by
  apply RegionalExponent.sum_slotLowerBound_le_totalExponent
  intro slot branch
  simpa using hfloor slot branch

end Exponent

end RationalTaggedSubdivision

end AlgebraicComplexity
