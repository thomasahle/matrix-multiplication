import AlgebraicComplexity.Analysis.StructuralZeroMultinomialLossCore

/-! # Subexponential growth of the structural-zero multinomial loss -/

namespace AlgebraicComplexity.WordType

universe u

variable {I : Type u} [Fintype I]

/-- The zero-safe loss is polynomial, hence subexponential. -/
theorem structuralZeroMultinomialLoss_subexponential (a : I → ℕ) :
    Growth.Subexponential (structuralZeroMultinomialLoss a) := by
  classical
  have hfactor (i : I) : Growth.Subexponential
      (fun k ↦ (((a i * k + 1 : ℕ) : ℝ))) := by
    have hlinear := (Growth.Subexponential.natCast_pow 1).const_mul
      (show (0 : ℝ) ≤ (a i : ℝ) by positivity)
    have hone := Growth.Subexponential.const (c := (1 : ℝ)) (by norm_num)
    convert hlinear.add hone using 1
    funext k
    push_cast
    simp only [pow_one]
  have hprod := Growth.Subexponential.fintype_prod
    (fun i k ↦ (((a i * k + 1 : ℕ) : ℝ))) hfactor
  exact hprod.const_mul (by positivity)

end AlgebraicComplexity.WordType
