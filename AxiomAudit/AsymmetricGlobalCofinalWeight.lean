/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.MatrixMultiplication.AsymmetricGlobalCofinalWeight

/-!
# Axiom audit for cofinal weighted powers

Audit of [duan2023faster], section 6, `eq:value_before_nth_root` to
`eq:numeric_conclusion_g` (`papers/sources/2210.10173/global_value.tex:269-309`).
-/

set_option autoImplicit false

#assert_axioms AlgebraicComplexity.AsymmetricGlobal.omega_lt_three_mul_of_cofinal_hasTauWeight
