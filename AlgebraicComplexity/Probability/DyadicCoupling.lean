/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Probability.DyadicMass
import AlgebraicComplexity.Probability.TwoLetter

/-!
# Exact dyadic coupling certificates

Numerical two-letter certificates store a joint numerator table at a finer dyadic denominator
than its one-letter marginals.  This module gives that boundary a paper-independent API.  The
predicate `DyadicMassData.HasMarginals` is a finite, denominator-cleared row/column checksum, and
`HasMarginals.toReal_isCoupling` transports it to the real-valued `ProbabilityVector.IsCoupling`
interface used by the entropy library.

The module also records the two generic recursive invariants needed by certificate evaluators:
a self-coupling preserves every additive per-letter statistic after division by two, and applying
the same conditional channel to its two coordinates preserves both one-letter output laws.  These
facts cover child-mass recurrences, complete-split marginals, and additive leaf dimensions.  They
do not assert a paired hashing or compatibility theorem; those rates genuinely depend on the
joint law and are handled separately in `Probability.TwoLetter`.
-/

open scoped BigOperators

namespace AlgebraicComplexity

namespace DyadicMassData

variable {I J O : Type*}

/-- Two exact dyadic masses are equal when all numerator coordinates agree. -/
@[ext] theorem ext_numerator {data₁ data₂ : DyadicMassData I}
    (h : ∀ i, data₁.numerator i = data₂.numerator i) : data₁ = data₂ := by
  cases data₁ with
  | mk numerator₁ =>
    cases data₂ with
    | mk numerator₂ =>
      congr
      funext i
      exact h i

/-- Interpret an exactly normalized dyadic numerator table as a real probability vector. -/
noncomputable def toProbabilityVector [Fintype I]
    (bits : ℕ) (data : DyadicMassData I) (hdata : data.IsProbability bits) :
    ProbabilityVector I :=
  (data.toRational bits).toReal (data.toRational_isProbability hdata)

@[simp] theorem toProbabilityVector_weight [Fintype I]
    (bits : ℕ) (data : DyadicMassData I) (hdata : data.IsProbability bits) (i : I) :
    (data.toProbabilityVector bits hdata).weight i =
      (data.numerator i : ℝ) / dyadicDenominator bits := by
  unfold toProbabilityVector
  rw [RationalProbabilityData.toReal_weight]
  simp only [toRational]
  rw [Rat.cast_div, Rat.cast_natCast, Rat.cast_natCast]

/-- Denominator-cleared row and column marginal equations for a joint dyadic table.

If the marginals use `bits` denominator bits and the joint table uses `bits + extra`, each joint
row/column sum is the corresponding marginal numerator multiplied by `2^extra`.  The definition
does not mention `bits`, so the same finite checksum can be reused at any base precision. -/
def HasMarginals [Fintype I] [Fintype J]
    (extra : ℕ) (joint : DyadicMassData (I × J))
    (left : DyadicMassData I) (right : DyadicMassData J) : Prop :=
  (∀ i, ∑ j, joint.numerator (i, j) =
      left.numerator i * dyadicDenominator extra) ∧
    (∀ j, ∑ i, joint.numerator (i, j) =
      right.numerator j * dyadicDenominator extra)

/-- Denominator-cleared aggregate marginal equation.  It allows unequal row and column
marginals, requiring only that their sum equal two copies of `base` after rescaling. -/
def HasAggregateMarginal [Fintype I] [DecidableEq I]
    (extra : ℕ) (joint : DyadicMassData (I × I)) (base : DyadicMassData I) : Prop :=
  ∀ i,
    (joint.pushforward Prod.fst).numerator i +
        (joint.pushforward Prod.snd).numerator i =
      2 * (base.numerator i * dyadicDenominator extra)

namespace HasMarginals

variable [Fintype I] [Fintype J]
variable {extra : ℕ} {joint : DyadicMassData (I × J)}
variable {left : DyadicMassData I} {right : DyadicMassData J}

/-- The exact first pushforward of a dyadic coupling is the rescaled left marginal. -/
theorem pushforward_fst_eq_rescale
    [DecidableEq I]
    (h : HasMarginals extra joint left right) :
    joint.pushforward Prod.fst = left.rescale extra := by
  ext i
  simp only [pushforward, rescale]
  rw [Fintype.sum_prod_type]
  rw [Finset.sum_eq_single i]
  · simpa using h.1 i
  · intro other _ hne
    simp [hne]
  · simp

/-- The exact second pushforward of a dyadic coupling is the rescaled right marginal. -/
theorem pushforward_snd_eq_rescale
    [DecidableEq J]
    (h : HasMarginals extra joint left right) :
    joint.pushforward Prod.snd = right.rescale extra := by
  ext j
  simp only [pushforward, rescale]
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  rw [Finset.sum_eq_single j]
  · simpa using h.2 j
  · intro other _ hne
    simp [hne]
  · simp

/-- A normalized marginal and exact row sums force normalization of the joint table at the wider
dyadic denominator. -/
theorem joint_isProbability
    [DecidableEq I]
    (h : HasMarginals extra joint left right) {bits : ℕ}
    (hleft : left.IsProbability bits) :
    joint.IsProbability (bits + extra) := by
  have hpush : (joint.pushforward Prod.fst).IsProbability (bits + extra) := by
    rw [h.pushforward_fst_eq_rescale]
    exact left.rescale_isProbability hleft extra
  unfold IsProbability at hpush ⊢
  rw [show (∑ ij, joint.numerator ij) = joint.totalNumerator by rfl,
    ← totalNumerator_pushforward Prod.fst joint,
    show (joint.pushforward Prod.fst).totalNumerator =
      ∑ i, (joint.pushforward Prod.fst).numerator i by rfl]
  exact hpush

/-- A self-coupling automatically satisfies the denominator-cleared aggregate-interface
equation used by two-letter tensor assembly. -/
theorem hasAggregateMarginal
    {I : Type*} [Fintype I] [DecidableEq I]
    {extra : ℕ} {joint : DyadicMassData (I × I)} {base : DyadicMassData I}
    (h : HasMarginals extra joint base base) :
    HasAggregateMarginal extra joint base := by
  intro i
  rw [h.pushforward_fst_eq_rescale, h.pushforward_snd_eq_rescale]
  simp only [rescale_numerator]
  ring

end HasMarginals

namespace HasAggregateMarginal

variable {I : Type*} [Fintype I] [DecidableEq I]
variable {extra : ℕ} {joint : DyadicMassData (I × I)} {base : DyadicMassData I}

/-- The aggregate row-plus-column checksum and normalization of the base already force
normalization of the joint table.  A separate joint-simplex field is therefore unnecessary in an
aggregate-interface certificate. -/
theorem joint_isProbability
    (h : HasAggregateMarginal extra joint base) {bits : ℕ}
    (hbase : base.IsProbability bits) :
    joint.IsProbability (bits + extra) := by
  have hsum :
      (∑ i, (joint.pushforward Prod.fst).numerator i) +
          ∑ i, (joint.pushforward Prod.snd).numerator i =
        2 * ((∑ i, base.numerator i) * dyadicDenominator extra) := by
    calc
      _ = ∑ i, ((joint.pushforward Prod.fst).numerator i +
          (joint.pushforward Prod.snd).numerator i) :=
        Finset.sum_add_distrib.symm
      _ = ∑ i, 2 * (base.numerator i * dyadicDenominator extra) :=
        Finset.sum_congr rfl (fun i _ ↦ h i)
      _ = 2 * ∑ i, base.numerator i * dyadicDenominator extra := by
        rw [Finset.mul_sum]
      _ = 2 * ((∑ i, base.numerator i) * dyadicDenominator extra) := by
        rw [Finset.sum_mul]
  have htwice : joint.totalNumerator + joint.totalNumerator =
      2 * (base.totalNumerator * dyadicDenominator extra) := by
    simpa only [
      show (∑ i, (joint.pushforward Prod.fst).numerator i) =
        (joint.pushforward Prod.fst).totalNumerator by rfl,
      show (∑ i, (joint.pushforward Prod.snd).numerator i) =
        (joint.pushforward Prod.snd).totalNumerator by rfl,
      totalNumerator_pushforward,
      show (∑ i, base.numerator i) = base.totalNumerator by rfl] using hsum
  have hbaseTotal : base.totalNumerator = dyadicDenominator bits := by
    simpa only [IsProbability,
      show (∑ i, base.numerator i) = base.totalNumerator by rfl] using hbase
  rw [hbaseTotal] at htwice
  have htotal : joint.totalNumerator =
      dyadicDenominator bits * dyadicDenominator extra := by
    omega
  simpa only [IsProbability,
    show (∑ ij, joint.numerator ij) = joint.totalNumerator by rfl,
    dyadicDenominator, pow_add] using htotal

end HasAggregateMarginal

/-- Exact scatter-add commutes with conversion from normalized dyadic data to real probability
vectors. -/
theorem toProbabilityVector_pushforward
    [Fintype I] [Fintype J] [DecidableEq J]
    {bits : ℕ} {data : DyadicMassData I} (hdata : data.IsProbability bits)
    (map : I → J) :
    (data.toProbabilityVector bits hdata).pushforward map =
      (data.pushforward map).toProbabilityVector bits
        (data.pushforward_isProbability hdata map) := by
  ext j
  rw [ProbabilityVector.pushforward_weight]
  simp only [toProbabilityVector_weight, pushforward]
  calc
    (∑ i, if map i = j then
        (data.numerator i : ℝ) / dyadicDenominator bits else 0) =
        ∑ i, ((if map i = j then data.numerator i else 0 : ℕ) : ℝ) /
          dyadicDenominator bits := by
      apply Finset.sum_congr rfl
      intro i _
      split_ifs <;> simp_all
    _ = (∑ i, ((if map i = j then data.numerator i else 0 : ℕ) : ℝ)) /
          dyadicDenominator bits := by
      rw [Finset.sum_div]
    _ = ((∑ i, if map i = j then data.numerator i else 0 : ℕ) : ℝ) /
          dyadicDenominator bits := by
      norm_cast

namespace HasMarginals

variable [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
variable {extra bits : ℕ} {joint : DyadicMassData (I × J)}
variable {left : DyadicMassData I} {right : DyadicMassData J}

/-- Exact dyadic row/column checks produce a genuine real-valued coupling.  This is the main
adapter consumed by entropy and fixed-interface theorems.

Proof sketch: convert scatter-add along `fst` and `snd` to real pushforwards, replace the exact
pushforward numerator tables by the rescaled marginals, and use invariance of rational weights
under dyadic rescaling. -/
theorem toReal_isCoupling
    (h : HasMarginals extra joint left right)
    (hleft : left.IsProbability bits) (hright : right.IsProbability bits) :
    (joint.toProbabilityVector (bits + extra) (h.joint_isProbability hleft)).IsCoupling
      (left.toProbabilityVector bits hleft)
      (right.toProbabilityVector bits hright) := by
  constructor
  · rw [toProbabilityVector_pushforward]
    ext i
    simp only [toProbabilityVector_weight]
    rw [h.pushforward_fst_eq_rescale]
    simp only [rescale_numerator, dyadicDenominator, pow_add]
    push_cast
    field_simp
  · rw [toProbabilityVector_pushforward]
    ext j
    simp only [toProbabilityVector_weight]
    rw [h.pushforward_snd_eq_rescale]
    simp only [rescale_numerator, dyadicDenominator, pow_add]
    push_cast
    field_simp

end HasMarginals

end DyadicMassData

namespace ProbabilityVector.IsCoupling

variable {I J O : Type*}
variable [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
variable {joint : ProbabilityVector (I × J)}
variable {left : ProbabilityVector I} {right : ProbabilityVector J}

/-- Any additive per-letter scalar statistic depends only on the two coupling marginals. -/
theorem expectation_add_coordinates
    (h : joint.IsCoupling left right) (f : I → ℝ) (g : J → ℝ) :
    joint.expectation (fun ij ↦ f ij.1 + g ij.2) =
      left.expectation f + right.expectation g := by
  rw [ProbabilityVector.expectation_add]
  rw [show (fun ij : I × J ↦ f ij.1) = f ∘ Prod.fst by rfl,
    show (fun ij : I × J ↦ g ij.2) = g ∘ Prod.snd by rfl,
    h.expectation_left, h.expectation_right]

/-- For a self-coupling, the per-original-factor value of every additive statistic is unchanged. -/
theorem expectation_add_coordinates_eq_two
    {joint : ProbabilityVector (I × I)} {base : ProbabilityVector I}
    (h : joint.IsCoupling base base) (f : I → ℝ) :
    joint.expectation (fun ij ↦ f ij.1 + f ij.2) =
      2 * base.expectation f := by
  rw [h.expectation_add_coordinates f f]
  ring

/-- Bundled recursive-interface invariant for a self-coupling.

Every additive scalar evaluator field is doubled before the per-source-factor division, while
the paired output of an arbitrary one-letter conditional channel has the original output law on
both coordinates.  Pointwise choices of the scalar statistic cover vector-valued mass and
dimension tables. -/
theorem preserves_additiveStatistic_and_channel
    {joint : ProbabilityVector (I × I)} {base : ProbabilityVector I}
    (h : joint.IsCoupling base base) (statistic : I → ℝ)
    [Fintype O] [DecidableEq O] (channel : I → ProbabilityVector O) :
    joint.expectation (fun ij ↦ statistic ij.1 + statistic ij.2) =
        2 * base.expectation statistic ∧
      (joint.mixture (ProbabilityVector.productChannel channel channel)).IsCoupling
        (base.mixture channel) (base.mixture channel) := by
  exact ⟨h.expectation_add_coordinates_eq_two statistic,
    h.mixture_productChannel channel channel⟩

end ProbabilityVector.IsCoupling

end AlgebraicComplexity
