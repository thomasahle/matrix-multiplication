/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.InterfaceTensorWordSplitCore
import AxiomAudit.Command

set_option autoImplicit false

/-!
# Axiom audit for consecutive complete-split half-words

These checks cover the canonical equivalence between a depth-`d+1` complete-split word and its two
consecutive depth-`d` halves, the additivity of the aggregate coordinate across that split, and
literal concatenation.  This is the word-level semantics of the complete split distributions of
[alman2025more], `papers/sources/2404.16349/prelim.tex:249-269`.

No distribution, profile, tensor realization or numerical endpoint is asserted here.

## References

- [alman2025more] Josh Alman, Ran Duan, Virginia Vassilevska Williams, Yinzhan Xu, Zixuan Xu,
  and Renfei Zhou, *More Asymmetry Yields Faster Matrix Multiplication*.
-/

open AlgebraicComplexity

#assert_axioms splitIndexSuccEquiv
#assert_axioms splitWordSuccEquiv
#assert_axioms splitWordWeight_succ
#assert_axioms concatSplitWords
#assert_axioms splitWordSuccEquiv_concatSplitWords
