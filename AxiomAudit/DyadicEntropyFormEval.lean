/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import MatrixMultiplication.DyadicEntropyFormEval

/-!
# Enforcing audit for the real evaluation of dyadic entropy forms

This leaf covers the seven real-evaluation and rescaling laws carried unchanged out of the
former `DyadicEntropyForm` monolith by the definition-preserving split: the three
entropy-evaluation identities, the two denominator-rescaling laws, and the two outer-mass
weighting laws.  The umbrella audit re-asserts them as a composition check.

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

#assert_axioms MatrixMultiplication.DyadicEntropyForm.entropyTermForm_eval
#assert_axioms MatrixMultiplication.DyadicEntropyForm.entropyForm_eval
#assert_axioms MatrixMultiplication.DyadicEntropyForm.weightedEntropyForm_eval
#assert_axioms MatrixMultiplication.DyadicEntropyForm.eval_at_add_bits
#assert_axioms MatrixMultiplication.DyadicEntropyForm.rescale_eval
#assert_axioms MatrixMultiplication.DyadicEntropyForm.scaleNat_eval_add_bits
#assert_axioms MatrixMultiplication.DyadicEntropyForm.scaleNat_weightedEntropyForm_eval
