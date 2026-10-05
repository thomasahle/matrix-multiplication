/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import MatrixMultiplication.DyadicEntropyFormZeros

/-!
# Enforcing audit for zero-padding invariance of dyadic entropy forms

This leaf covers the five zero-removal laws carried unchanged out of the former
`DyadicEntropyForm` monolith by the definition-preserving split.  They are the preprocessing
step that lets a compact generated certificate discard padded zero slots before it builds an
exact signed-log form, so they are audited at the leaf that a definition-only client imports.

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

#assert_axioms MatrixMultiplication.DyadicEntropyForm.sum_dropZeros
#assert_axioms MatrixMultiplication.DyadicEntropyForm.entropyForm_dropZeros
#assert_axioms MatrixMultiplication.DyadicEntropyForm.weightedEntropyForm_dropZeros
#assert_axioms MatrixMultiplication.DyadicEntropyForm.map_weightedEntropyForm_dropZeros
#assert_axioms MatrixMultiplication.DyadicEntropyForm.sum_map_weightedEntropyForm_dropZeros
