/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinogradChunkSplitWordEquivCore
import AxiomAudit.Command

set_option autoImplicit false

/-!
# Axiom audit for the native-CW/complete-split word equivalence

These checks cover both directions of the identification between a native Coppersmith--Winograd
chunk and its complete-split ternary word, and the two `simp` lemmas saying that the equivalence
acts by the already-audited encoding.  The chunk alphabet is the one used by the complete split
distributions of [alman2025more], `papers/sources/2404.16349/prelim.tex:249-269`.

No tensor restriction, compatibility count, asymptotic rate or exponent endpoint is asserted here.

## References

- [alman2025more] Josh Alman, Ran Duan, Virginia Vassilevska Williams, Yinzhan Xu, Zixuan Xu,
  and Renfei Zhou, *More Asymmetry Yields Faster Matrix Multiplication*.
-/

open AlgebraicComplexity.Examples

#assert_axioms cwBlockDigitEquiv
#assert_axioms cwBlockDigitEquiv_apply
#assert_axioms cwChunkSplitWordEquiv
#assert_axioms cwChunkSplitWordEquiv_apply
