import AxiomAudit.Command
import AlgebraicComplexity.Analysis.SubexponentialDenominator

/-! Focused trust audit for `AlgebraicComplexity.Analysis.SubexponentialDenominator`: the single
bootstrap theorem that an exponentially growing family count eventually dominates a
subexponential integral denominator, stated as an exact inequality of natural numbers. -/

#assert_axioms AlgebraicComplexity.Growth.Subexponential.exists_forall_natCast_denominator_le_count_of_pow_le_mul
