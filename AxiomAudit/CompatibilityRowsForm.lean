/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import MatrixMultiplication.CompatibilityRowsForm

/-!
# Enforcing audit for exact compatibility-row forms

This leaf covers the two declarations of the signed-log adapter carried unchanged out of the
former `SimplifiedExponentRootRecurrence` monolith: the exact form of one compatibility branch
and the theorem that evaluating it returns the branch's real homogeneous-entropy rate.  The
semantic half of the same namespace is audited by `AxiomAudit/CompatibilityRows.lean`.

No new mathematical claim is made by this module or by the split it audits.

The audited declarations carry no claim of their own; the entropies they represent exactly are
those of [alman2025more], `papers/sources/2404.16349/constituent.tex:113-147`, and of
`better_bound/paper.tex`, `sec:dual` (lines 2274-2307).

## References

- [alman2025more] Josh Alman, Ran Duan, Virginia Vassilevska Williams, Yinzhan Xu, Zixuan Xu,
  and Renfei Zhou, *More Asymmetry Yields Faster Matrix Multiplication*.
- *Total-Weight Hashing and Rectangular Volume in the Coppersmith--Winograd Method*.
-/

set_option autoImplicit false

#assert_axioms
  MatrixMultiplication.SimplifiedExponentRootRecurrence.CompatibilityRows.form
#assert_axioms
  MatrixMultiplication.SimplifiedExponentRootRecurrence.CompatibilityRows.form_eval
