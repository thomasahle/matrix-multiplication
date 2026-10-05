import MatrixMultiplication.LogLinearCompression
import Mathlib.Algebra.BigOperators.Field

/-!
# Finite-family logarithm compression

This module lifts the scalar chord and tangent inequalities in `LogLinearCompression` to
executable finite families.  A binning function may pool arbitrarily many logarithm arguments:

* positive coefficients are replaced by two aggregate coefficients at the bin endpoints;
* negative coefficients are replaced by one aggregate coefficient at the bin center plus one
  exact rational first-order residual.

The statements are independent of dyadic arithmetic.  Generated checkers may instantiate all
weights, arguments, endpoints, centers, and residuals by exact rationals and leave only the small
set of endpoint/center logarithms to an interval certificate.
-/

open scoped BigOperators

noncomputable section

namespace MatrixMultiplication.LogLinearCompression

universe u v

/-- Sum a real-valued family over one fiber of a finite binning map. -/
def fiberSum {Item : Type u} {Bin : Type v} [Fintype Item] [DecidableEq Bin]
    (bin : Item → Bin) (term : Item → ℝ) (b : Bin) : ℝ :=
  ∑ item : {item : Item // bin item = b}, term item.1

/-- Total coefficient of the lower endpoint in the chord expansion of one bin. -/
def chordLowerCoefficient
    {Item : Type u} {Bin : Type v} [Fintype Item] [DecidableEq Bin]
    (bin : Item → Bin) (weight argument : Item → ℝ)
    (lower upper : Bin → ℝ) (b : Bin) : ℝ :=
  fiberSum bin (fun item ↦
    weight item * ((upper b - argument item) / (upper b - lower b))) b

/-- Total coefficient of the upper endpoint in the chord expansion of one bin. -/
def chordUpperCoefficient
    {Item : Type u} {Bin : Type v} [Fintype Item] [DecidableEq Bin]
    (bin : Item → Bin) (weight argument : Item → ℝ)
    (lower upper : Bin → ℝ) (b : Bin) : ℝ :=
  fiberSum bin (fun item ↦
    weight item * ((argument item - lower b) / (upper b - lower b))) b

/-- Weighted scalar chord bounds sum over an arbitrary finite family. -/
theorem weighted_logTwo_chord_lower
    {Item : Type u} [Fintype Item]
    (weight argument lower upper : Item → ℝ)
    (hweight : ∀ item, 0 ≤ weight item)
    (hlower : ∀ item, 0 < lower item)
    (hla : ∀ item, lower item ≤ argument item)
    (hau : ∀ item, argument item ≤ upper item)
    (hlu : ∀ item, lower item < upper item) :
    (∑ item, weight item *
      (((upper item - argument item) / (upper item - lower item)) *
          (Real.log (lower item) / Real.log 2) +
        ((argument item - lower item) / (upper item - lower item)) *
          (Real.log (upper item) / Real.log 2))) ≤
      ∑ item, weight item * (Real.log (argument item) / Real.log 2) := by
  apply Finset.sum_le_sum
  intro item _hitem
  exact mul_le_mul_of_nonneg_left
    (logTwo_chord_lower (hlower item) (hla item) (hau item) (hlu item))
    (hweight item)

/-- Binned chord certificate with only two logarithms per bin.

The two endpoint coefficients are exact fiber sums.  In particular, the theorem never assumes
that the item arguments or weights are constant inside a bin. -/
theorem binned_weighted_logTwo_chord_lower
    {Item : Type u} {Bin : Type v} [Fintype Item] [Fintype Bin] [DecidableEq Bin]
    (bin : Item → Bin) (weight argument : Item → ℝ)
    (lower upper : Bin → ℝ)
    (hweight : ∀ item, 0 ≤ weight item)
    (hlower : ∀ b, 0 < lower b)
    (hla : ∀ item, lower (bin item) ≤ argument item)
    (hau : ∀ item, argument item ≤ upper (bin item))
    (hlu : ∀ b, lower b < upper b) :
    (∑ b : Bin, (
        chordLowerCoefficient (Item := Item) (Bin := Bin)
            bin weight argument lower upper b *
            (Real.log (lower b) / Real.log 2) +
          chordUpperCoefficient (Item := Item) (Bin := Bin)
              bin weight argument lower upper b *
            (Real.log (upper b) / Real.log 2))) ≤
      ∑ item, weight item * (Real.log (argument item) / Real.log 2) := by
  classical
  have hitem := weighted_logTwo_chord_lower weight argument
    (fun item ↦ lower (bin item)) (fun item ↦ upper (bin item))
    hweight (fun item ↦ hlower (bin item)) hla hau (fun item ↦ hlu (bin item))
  calc
    (∑ b : Bin, (
        chordLowerCoefficient (Item := Item) (Bin := Bin)
            bin weight argument lower upper b *
            (Real.log (lower b) / Real.log 2) +
          chordUpperCoefficient (Item := Item) (Bin := Bin)
              bin weight argument lower upper b *
            (Real.log (upper b) / Real.log 2))) =
        ∑ b : Bin, ∑ item : {item : Item // bin item = b},
          weight item.1 *
            (((upper b - argument item.1) / (upper b - lower b)) *
                (Real.log (lower b) / Real.log 2) +
              ((argument item.1 - lower b) / (upper b - lower b)) *
                (Real.log (upper b) / Real.log 2)) := by
          apply Finset.sum_congr rfl
          intro b _hb
          unfold chordLowerCoefficient chordUpperCoefficient fiberSum
          rw [Finset.sum_mul, Finset.sum_mul, ← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro item _hitem
          ring
    _ = ∑ item, weight item *
          (((upper (bin item) - argument item) /
                (upper (bin item) - lower (bin item))) *
              (Real.log (lower (bin item)) / Real.log 2) +
            ((argument item - lower (bin item)) /
                (upper (bin item) - lower (bin item))) *
              (Real.log (upper (bin item)) / Real.log 2)) := by
      have hfiber :
          (∑ b : Bin, ∑ item : {item : Item // bin item = b},
            weight item.1 *
              (((upper b - argument item.1) / (upper b - lower b)) *
                  (Real.log (lower b) / Real.log 2) +
                ((argument item.1 - lower b) / (upper b - lower b)) *
                  (Real.log (upper b) / Real.log 2))) =
          ∑ b : Bin, ∑ item : {item : Item // bin item = b},
            weight item.1 *
              (((upper (bin item.1) - argument item.1) /
                    (upper (bin item.1) - lower (bin item.1))) *
                  (Real.log (lower (bin item.1)) / Real.log 2) +
                ((argument item.1 - lower (bin item.1)) /
                    (upper (bin item.1) - lower (bin item.1))) *
                  (Real.log (upper (bin item.1)) / Real.log 2)) := by
        apply Finset.sum_congr rfl
        intro b _hb
        apply Finset.sum_congr rfl
        intro item _hitem
        simp [item.property]
      rw [hfiber]
      exact Fintype.sum_fiberwise bin (fun item ↦
        weight item *
          (((upper (bin item) - argument item) /
                (upper (bin item) - lower (bin item))) *
              (Real.log (lower (bin item)) / Real.log 2) +
            ((argument item - lower (bin item)) /
                (upper (bin item) - lower (bin item))) *
              (Real.log (upper (bin item)) / Real.log 2)))
    _ ≤ ∑ item, weight item * (Real.log (argument item) / Real.log 2) := hitem

/-- Tangent upper bound with a different positive center for every item. -/
theorem weighted_logTwo_le_variable_tangent
    {Item : Type u} [Fintype Item]
    (weight argument center : Item → ℝ)
    (hweight : ∀ item, 0 ≤ weight item)
    (hargument : ∀ item, 0 < argument item)
    (hcenter : ∀ item, 0 < center item) :
    (∑ item, weight item * (Real.log (argument item) / Real.log 2)) ≤
      ∑ item, weight item *
        (Real.log (center item) / Real.log 2 +
          ((argument item - center item) / center item) / Real.log 2) := by
  apply Finset.sum_le_sum
  intro item _hitem
  exact mul_le_mul_of_nonneg_left
    (logTwo_tangent_upper (hargument item) (hcenter item)) (hweight item)

/-- Binned tangent certificate for a negative logarithmic family.

Writing `W_b` for the exact total weight in bin `b`, this is

`-Σᵢ wᵢ log₂(aᵢ) ≥ -Σ_b W_b log₂(c_b)
  - (Σᵢ wᵢ (aᵢ/c_{bin i} - 1)) / log 2`.

The last sum is an exact rational residual whenever the inputs and centers are rational. -/
theorem neg_binned_weighted_logTwo_tangent_lower
    {Item : Type u} {Bin : Type v} [Fintype Item] [Fintype Bin] [DecidableEq Bin]
    (bin : Item → Bin) (weight argument : Item → ℝ) (center : Bin → ℝ)
    (hweight : ∀ item, 0 ≤ weight item)
    (hargument : ∀ item, 0 < argument item)
    (hcenter : ∀ b, 0 < center b) :
    -(∑ b : Bin, fiberSum (Item := Item) (Bin := Bin) bin weight b *
          (Real.log (center b) / Real.log 2)) -
        (∑ item, weight item * (argument item / center (bin item) - 1)) /
          Real.log 2 ≤
      -(∑ item, weight item * (Real.log (argument item) / Real.log 2)) := by
  classical
  have htangent := weighted_logTwo_le_variable_tangent
    weight argument (fun item ↦ center (bin item))
    hweight hargument (fun item ↦ hcenter (bin item))
  have hcenterSum :
      (∑ b : Bin, fiberSum (Item := Item) (Bin := Bin) bin weight b *
          (Real.log (center b) / Real.log 2)) =
        ∑ item, weight item *
          (Real.log (center (bin item)) / Real.log 2) := by
    calc
      (∑ b : Bin, fiberSum (Item := Item) (Bin := Bin) bin weight b *
          (Real.log (center b) / Real.log 2)) =
          ∑ b : Bin, ∑ item : {item : Item // bin item = b},
            weight item.1 * (Real.log (center b) / Real.log 2) := by
        apply Finset.sum_congr rfl
        intro b _hb
        unfold fiberSum
        rw [Finset.sum_mul]
      _ = ∑ item, weight item *
          (Real.log (center (bin item)) / Real.log 2) := by
        have hfiber :
            (∑ b : Bin, ∑ item : {item : Item // bin item = b},
              weight item.1 * (Real.log (center b) / Real.log 2)) =
            ∑ b : Bin, ∑ item : {item : Item // bin item = b},
              weight item.1 *
                (Real.log (center (bin item.1)) / Real.log 2) := by
          apply Finset.sum_congr rfl
          intro b _hb
          apply Finset.sum_congr rfl
          intro item _hitem
          simp [item.property]
        rw [hfiber]
        exact Fintype.sum_fiberwise bin (fun item ↦
          weight item * (Real.log (center (bin item)) / Real.log 2))
  rw [hcenterSum]
  have hlogTwo : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num)).ne'
  have hexpand :
      (∑ item, weight item *
        (Real.log (center (bin item)) / Real.log 2 +
          ((argument item - center (bin item)) / center (bin item)) /
            Real.log 2)) =
      (∑ item, weight item *
        (Real.log (center (bin item)) / Real.log 2)) +
      (∑ item, weight item * (argument item / center (bin item) - 1)) /
        Real.log 2 := by
    calc
      (∑ item, weight item *
        (Real.log (center (bin item)) / Real.log 2 +
          ((argument item - center (bin item)) / center (bin item)) /
            Real.log 2)) =
          ∑ item,
            (weight item * (Real.log (center (bin item)) / Real.log 2) +
              weight item *
                (((argument item - center (bin item)) / center (bin item)) /
                  Real.log 2)) := by
            apply Finset.sum_congr rfl
            intro item _hitem
            ring
      _ = (∑ item, weight item *
            (Real.log (center (bin item)) / Real.log 2)) +
          ∑ item, weight item *
            (((argument item - center (bin item)) / center (bin item)) /
              Real.log 2) := Finset.sum_add_distrib
      _ = (∑ item, weight item *
            (Real.log (center (bin item)) / Real.log 2)) +
          (∑ item, weight item * (argument item / center (bin item) - 1)) /
            Real.log 2 := by
          congr 1
          calc
            (∑ item, weight item *
              (((argument item - center (bin item)) / center (bin item)) /
                Real.log 2)) =
                ∑ item,
                  (weight item *
                    ((argument item - center (bin item)) /
                      center (bin item))) / Real.log 2 := by
                    apply Finset.sum_congr rfl
                    intro item _hitem
                    ring
            _ = (∑ item, weight item *
                  ((argument item - center (bin item)) /
                    center (bin item))) / Real.log 2 :=
              (Finset.sum_div ..).symm
            _ = (∑ item,
                  weight item * (argument item / center (bin item) - 1)) /
                Real.log 2 := by
              congr 1
              apply Finset.sum_congr rfl
              intro item _hitem
              have hc : center (bin item) ≠ 0 := (hcenter (bin item)).ne'
              field_simp [hc]
  rw [hexpand] at htangent
  linarith

end MatrixMultiplication.LogLinearCompression
