import AlgebraicComplexity.Tensor.OriginalCWNumerics

set_option linter.style.header false

/-!
# The remaining theorem interfaces for the original CW bound

The finite algebra and the scalar inequality are formalized elsewhere. This file states the final
implication with the two genuinely asymptotic ingredients left explicit:

* the tight-support extraction lower bound for the tensor square; and
* Schönhage's value/border-rank criterion.

As those two interfaces are formalized, this theorem will become the end-to-end historical result.
-/

namespace AlgebraicComplexity.OriginalCW

/--
A log-domain formulation of the two remaining asymptotic facts. `valueLog` stands for
`log₂ V_ρ(CW₆^{⊗2})`.
-/
structure AsymptoticInterfaces (omega valueLog : ℝ) : Prop where
  tightSupportLowerBound : squareLogLower ≤ valueLog
  schonhageCriterion : 6 < valueLog → omega ≤ (rho : ℝ)

/-- The formal algebra and numerical certificate reduce the rounded CW theorem to two interfaces. -/
theorem omega_lt_2376_of_interfaces
    (omega valueLog : ℝ) (h : AsymptoticInterfaces omega valueLog) :
    omega < (roundedTarget : ℝ) := by
  have hvalue : 6 < valueLog := squareLogLower_gt_six.trans_le h.tightSupportLowerBound
  have homega : omega ≤ (rho : ℝ) := h.schonhageCriterion hvalue
  have hrho : (rho : ℝ) < (roundedTarget : ℝ) := by
    exact_mod_cast rho_lt_roundedTarget
  exact homega.trans_lt hrho

#print axioms omega_lt_2376_of_interfaces

end AlgebraicComplexity.OriginalCW
