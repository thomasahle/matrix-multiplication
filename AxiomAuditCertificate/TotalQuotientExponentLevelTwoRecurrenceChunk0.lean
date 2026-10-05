/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoRecurrenceChunk0

set_option autoImplicit false

/-!
# Audit of the archived total-weight recurrence input slice

The diagnostic certificate is identified in `better_bound/paper.tex:3560-3563`.
Its recursive parameters use [alman2025more],
`papers/sources/2404.16349/constituent.tex:41-47`.
Both literal data and the composed recurrence equality are kernel checked; neither is an
exponent endpoint.

## Reference

- [alman2025more] Josh Alman et al., *More Asymmetry Yields Faster Matrix Multiplication*.
-/

#assert_axioms
  MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoRecurrence.Chunk0.expectedInputs
#assert_axioms
  MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoRecurrence.Chunk0.inputs_eq
