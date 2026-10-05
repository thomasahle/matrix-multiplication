/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import MatrixMultiplication.SignedDyadicLogFormSum

/-!
# Axiom audit for the signed-log form sum split

Covers every public declaration of `MatrixMultiplication/SignedDyadicLogFormSum.lean`.  These are
structural identities about constants and term lists, with no generated datum anywhere in their
closure, so they belong in the ordinary audit target rather than the certificate tier.

Build with

```text
lake build AxiomAudit
```

Each `#assert_axioms` fails elaboration if its declaration depends on any axiom other than
`propext`, `Classical.choice`, and `Quot.sound`.
-/

#assert_axioms MatrixMultiplication.SignedDyadicLogForm.Form.add_assoc
#assert_axioms MatrixMultiplication.SignedDyadicLogForm.Form.zero_add
#assert_axioms MatrixMultiplication.SignedDyadicLogForm.Form.add_zero
#assert_axioms MatrixMultiplication.SignedDyadicLogForm.Form.sum_append
#assert_axioms MatrixMultiplication.SignedDyadicLogForm.Form.sum_flatten
