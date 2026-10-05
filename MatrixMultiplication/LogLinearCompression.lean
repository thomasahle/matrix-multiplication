import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Compression inequalities for logarithmic certificates

Large entropy certificates initially contain tens of thousands of distinct integer logarithms.
This module supplies two elementary but effective ways to pool nearby arguments without losing
rigor:

* concavity gives a chord lower bound for positive log coefficients;
* the tangent inequality gives an upper bound for negative log coefficients.

If the tangent center is the coefficient-weighted arithmetic mean, all linear error terms cancel.
For executable certificates it is often cheaper to use a nearby dyadic center, aggregate the
remaining rational error, and certify one additional multiple of `1 / log 2`.
-/

open scoped BigOperators

noncomputable section

namespace MatrixMultiplication.LogLinearCompression

/-- A logarithm lies above the chord joining two positive endpoints. -/
theorem log_chord_lower {lower argument upper : ℝ}
    (hlower : 0 < lower) (hla : lower ≤ argument) (hau : argument ≤ upper)
    (hlu : lower < upper) :
    ((upper - argument) / (upper - lower)) * Real.log lower +
        ((argument - lower) / (upper - lower)) * Real.log upper ≤
      Real.log argument := by
  have hden : 0 < upper - lower := sub_pos.mpr hlu
  have hupper : 0 < upper := hlower.trans hlu
  have hleft : 0 ≤ (upper - argument) / (upper - lower) :=
    div_nonneg (sub_nonneg.mpr hau) hden.le
  have hright : 0 ≤ (argument - lower) / (upper - lower) :=
    div_nonneg (sub_nonneg.mpr hla) hden.le
  have hsum :
      (upper - argument) / (upper - lower) +
          (argument - lower) / (upper - lower) = 1 := by
    field_simp
    ring
  have hcomb :
      ((upper - argument) / (upper - lower)) • lower +
          ((argument - lower) / (upper - lower)) • upper = argument := by
    simp only [smul_eq_mul]
    field_simp
    ring
  have hconcave := strictConcaveOn_log_Ioi.concaveOn.2 hlower hupper
    hleft hright hsum
  rw [hcomb] at hconcave
  simpa only [smul_eq_mul] using hconcave

/-- Base-two version of `log_chord_lower`. -/
theorem logTwo_chord_lower {lower argument upper : ℝ}
    (hlower : 0 < lower) (hla : lower ≤ argument) (hau : argument ≤ upper)
    (hlu : lower < upper) :
    ((upper - argument) / (upper - lower)) *
          (Real.log lower / Real.log 2) +
        ((argument - lower) / (upper - lower)) *
          (Real.log upper / Real.log 2) ≤
      Real.log argument / Real.log 2 := by
  have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h := log_chord_lower hlower hla hau hlu
  have heq :
      ((upper - argument) / (upper - lower)) *
            (Real.log lower / Real.log 2) +
          ((argument - lower) / (upper - lower)) *
            (Real.log upper / Real.log 2) =
        (((upper - argument) / (upper - lower)) * Real.log lower +
          ((argument - lower) / (upper - lower)) * Real.log upper) /
            Real.log 2 := by
    field_simp
  rw [heq]
  exact div_le_div_of_nonneg_right h hlogTwo.le

/-- The tangent to `log` at any positive center is a global upper bound. -/
theorem log_tangent_upper {argument center : ℝ}
    (hargument : 0 < argument) (hcenter : 0 < center) :
    Real.log argument ≤ Real.log center + (argument - center) / center := by
  have hratio : 0 < argument / center := div_pos hargument hcenter
  have h := Real.log_le_sub_one_of_pos hratio
  rw [Real.log_div hargument.ne' hcenter.ne'] at h
  have hrewrite : argument / center - 1 = (argument - center) / center := by
    field_simp
  rw [hrewrite] at h
  linarith

/-- Base-two version of `log_tangent_upper`. -/
theorem logTwo_tangent_upper {argument center : ℝ}
    (hargument : 0 < argument) (hcenter : 0 < center) :
    Real.log argument / Real.log 2 ≤
      Real.log center / Real.log 2 +
        ((argument - center) / center) / Real.log 2 := by
  rw [← add_div]
  exact div_le_div_of_nonneg_right
    (log_tangent_upper hargument hcenter) (Real.log_pos (by norm_num)).le

/-- A weighted family of tangent bounds.  This form keeps the rational first-order correction
explicit, which is convenient when the chosen center is dyadic. -/
theorem weighted_logTwo_le_tangent
    {ι : Type*} [Fintype ι]
    (weight argument : ι → ℝ) (center : ℝ)
    (hweight : ∀ i, 0 ≤ weight i)
    (hargument : ∀ i, 0 < argument i)
    (hcenter : 0 < center) :
    (∑ i, weight i * (Real.log (argument i) / Real.log 2)) ≤
      ∑ i, weight i *
        (Real.log center / Real.log 2 +
          ((argument i - center) / center) / Real.log 2) := by
  apply Finset.sum_le_sum
  intro i _
  exact mul_le_mul_of_nonneg_left
    (logTwo_tangent_upper (hargument i) hcenter) (hweight i)

end MatrixMultiplication.LogLinearCompression
