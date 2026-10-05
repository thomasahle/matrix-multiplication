/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Adapters.CSLib.ProbabilityPMF
import AlgebraicComplexity.Combinatorics.Hashing
import Mathlib.Data.Fintype.BigOperators

/-!
# Uniform affine hash seeds

This file is the probabilistic wrapper around the deterministic counting results in
`AlgebraicComplexity.Combinatorics.Hashing`.  Keeping the two layers separate is intentional:
the collision and extraction arguments can use probability, while their finite sample spaces
and fibers remain inspectable exact objects.

The principal result below says that, for fixed block indices `I`, `J` and a fixed bucket `b`,
the mass of the common-bucket event under a uniform affine seed is exactly the cardinality of the
free weight space divided by the cardinality of the seed space.  No independence heuristic or
asymptotic estimate enters this calculation.

The one external (CSLib) fact used here — invariance of a finite uniform distribution under an
equivalence — is consumed through the adapter module
`AlgebraicComplexity.Adapters.CSLib.ProbabilityPMF`, per the dependency policy in `DESIGN.md`;
this file does not import `Cslib.*` directly.
-/

namespace AlgebraicComplexity

universe u v

namespace ProgressionHash

open scoped ENNReal

/-- The uniform distribution on affine hash seeds. -/
noncomputable def uniformSeed (R : Type u) (ι : Type v)
    [Fintype R] [Nonempty R] [Fintype ι] : PMF (Seed R ι) :=
  PMF.uniformOfFintype (Seed R ι)

/-- Uniform law on the product presentation `(offset, shift, weights)`. -/
noncomputable def uniformSeedData (R : Type u) (ι : Type v)
    [Fintype R] [Nonempty R] [Fintype ι] : PMF (R × R × (ι → R)) := by
  classical
  exact PMF.uniformOfFintype (R × R × (ι → R))

@[simp] theorem uniformSeed_apply (R : Type u) (ι : Type v)
    [Fintype R] [Nonempty R] [Fintype ι] (seed : Seed R ι) :
    uniformSeed R ι seed = (Fintype.card (Seed R ι) : ℝ≥0∞)⁻¹ := by
  simp [uniformSeed]

/-- Under the product presentation of a seed, the uniform seed law is still uniform.  This is
the precise finite-probability statement that the offset, shift, and weight table may be sampled
as one uniformly random tuple. -/
theorem uniformSeed_map_equivProd (R : Type u) (ι : Type v)
    [Fintype R] [Nonempty R] [Fintype ι] :
    (uniformSeed R ι).map (Seed.equivProd : Seed R ι ≃ R × R × (ι → R)) =
      uniformSeedData R ι := by
  classical
  exact AlgebraicComplexity.Adapters.CSLib.uniformOfFintype_map_equiv Seed.equivProd

namespace Seed

variable {R : Type u} [Field R] [Fintype R]
variable {ι : Type v} [Fintype ι]

/-- Exact probability mass of the event that fixed `X`- and `Y`-block indices land in the same
prescribed bucket.  The numerator is the number of freely selectable linear-weight tables. -/
theorem uniformSeed_commonBucket_mass (I J : ι → R) (b : R) :
    (uniformSeed R ι).toOuterMeasure {seed | InCommonBucket I J b seed} =
      (Fintype.card R ^ Fintype.card ι : ℝ≥0∞) /
        Fintype.card (Seed R ι) := by
  classical
  letI : Fintype {seed : Seed R ι // InCommonBucket I J b seed} :=
    Fintype.ofEquiv (ι → R) (commonBucketEquivWeights I J b)
  rw [uniformSeed, PMF.toOuterMeasure_uniformOfFintype_apply]
  congr 1
  norm_cast
  rw [Fintype.card_eq_nat_card]
  exact card_commonBucket I J b

/-- The paper-facing form of the first hashing probability: a fixed legal pair hits a prescribed
bucket with probability exactly `1 / |R|²`. -/
theorem uniformSeed_commonBucket_mass_eq_inv_square (I J : ι → R) (b : R) :
    (uniformSeed R ι).toOuterMeasure {seed | InCommonBucket I J b seed} =
      1 / ((Fintype.card R : ℝ≥0∞) * Fintype.card R) := by
  rw [uniformSeed_commonBucket_mass]
  have hR : (Fintype.card R : ℝ≥0∞) ≠ 0 := by
    norm_cast
    exact Fintype.card_ne_zero (α := R)
  have hSeed : (Fintype.card (Seed R ι) : ℝ≥0∞) ≠ 0 := by
    norm_cast
    exact Fintype.card_ne_zero (α := Seed R ι)
  apply (ENNReal.div_eq_div_iff (mul_ne_zero hR hR)
    (ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.coe_ne_top) hSeed ENNReal.coe_ne_top).2
  norm_cast
  rw [card_seed]
  ring

/-- Exact `1 / |R|²` probability for the three-hash event in the paper. -/
theorem uniformSeed_commonTriple_mass_eq_inv_square [NeZero (2 : R)]
    (I J K : ι → R) (target b : R)
    (hlegal : ∀ t, I t + J t + K t = target) :
    (uniformSeed R ι).toOuterMeasure
        {seed | InCommonTriple I J K target b seed} =
      1 / ((Fintype.card R : ℝ≥0∞) * Fintype.card R) := by
  rw [show {seed : Seed R ι | InCommonTriple I J K target b seed} =
      {seed | InCommonBucket I J b seed} from
    Set.ext fun seed => inCommonTriple_iff_commonBucket seed I J K target b hlegal]
  exact uniformSeed_commonBucket_mass_eq_inv_square I J b

/-- Multiplicative form of the conditional-collision law.  Under a uniform affine seed, the mass
of the event that an alternative `J'` also hits `b`, multiplied by `|R|`, is exactly the mass of
the original common-bucket event. -/
theorem uniformSeed_collision_mass_mul_card (I J J' : ι → R) (b : R) (hJJ' : J' ≠ J) :
    (uniformSeed R ι).toOuterMeasure
          {seed | InCommonBucket I J b seed ∧ seed.yHash J' = b} * Fintype.card R =
      (uniformSeed R ι).toOuterMeasure {seed | InCommonBucket I J b seed} := by
  classical
  let common : Set (Seed R ι) := {seed | InCommonBucket I J b seed}
  let collision : Set (Seed R ι) :=
    {seed | InCommonBucket I J b seed ∧ seed.yHash J' = b}
  change (uniformSeed R ι).toOuterMeasure collision * Fintype.card R =
    (uniformSeed R ι).toOuterMeasure common
  letI : Fintype common := Fintype.ofFinite common
  letI : Fintype collision := Fintype.ofFinite collision
  rw [uniformSeed, PMF.toOuterMeasure_uniformOfFintype_apply,
    PMF.toOuterMeasure_uniformOfFintype_apply]
  have hcountNat : Nat.card collision * Nat.card R = Nat.card common :=
    card_commonBucket_collision_mul I J J' b hJJ'
  have hcount :
      (Fintype.card collision : ℝ≥0∞) * Fintype.card R = Fintype.card common := by
    norm_cast
    simpa only [Fintype.card_eq_nat_card] using hcountNat
  calc
    (Fintype.card collision : ℝ≥0∞) / Fintype.card (Seed R ι) * Fintype.card R =
        ((Fintype.card collision : ℝ≥0∞) * Fintype.card R) /
          Fintype.card (Seed R ι) := by
      simp only [div_eq_mul_inv]
      ac_rfl
    _ = (Fintype.card common : ℝ≥0∞) / Fintype.card (Seed R ι) := by rw [hcount]

/-- Probability form of the paper's conditional-collision statement: after conditioning the
original pair `(I,J)` into bucket `b`, a distinct alternative `J'` hits that bucket with factor
exactly `1 / |R|`. -/
theorem uniformSeed_collision_mass (I J J' : ι → R) (b : R) (hJJ' : J' ≠ J) :
    (uniformSeed R ι).toOuterMeasure
        {seed | InCommonBucket I J b seed ∧ seed.yHash J' = b} =
      (uniformSeed R ι).toOuterMeasure {seed | InCommonBucket I J b seed} /
        Fintype.card R := by
  have hcard : (Fintype.card R : ℝ≥0∞) ≠ 0 := by
    norm_cast
    exact Fintype.card_ne_zero (α := R)
  apply (ENNReal.eq_div_iff hcard ENNReal.coe_ne_top).2
  simpa [mul_comm] using
    uniformSeed_collision_mass_mul_card (R := R) (ι := ι) I J J' b hJJ'

/-- Paper-facing conditional collision law for two distinct legal block triples sharing their
`X`-index.  The joint mass is the original triple's mass divided by `|R|`. -/
theorem uniformSeed_twoTriples_mass [NeZero (2 : R)]
    (I J K J' K' : ι → R) (target b : R)
    (hlegal : ∀ t, I t + J t + K t = target)
    (hlegal' : ∀ t, I t + J' t + K' t = target)
    (hJJ' : J' ≠ J) :
    (uniformSeed R ι).toOuterMeasure {seed |
        InCommonTriple I J K target b seed ∧ InCommonTriple I J' K' target b seed} =
      (uniformSeed R ι).toOuterMeasure {seed |
        InCommonTriple I J K target b seed} / Fintype.card R := by
  have hjoint :
      {seed : Seed R ι |
          InCommonTriple I J K target b seed ∧ InCommonTriple I J' K' target b seed} =
        {seed | InCommonBucket I J b seed ∧ seed.yHash J' = b} := by
    ext seed
    rw [Set.mem_setOf_eq, Set.mem_setOf_eq,
      inCommonTriple_iff_commonBucket seed I J K target b hlegal,
      inCommonTriple_iff_commonBucket seed I J' K' target b hlegal']
    simp only [InCommonBucket]
    tauto
  have hbase :
      {seed : Seed R ι | InCommonTriple I J K target b seed} =
        {seed | InCommonBucket I J b seed} :=
    Set.ext fun seed => inCommonTriple_iff_commonBucket seed I J K target b hlegal
  rw [hjoint, hbase]
  exact uniformSeed_collision_mass I J J' b hJJ'

end Seed

end ProgressionHash

end AlgebraicComplexity
