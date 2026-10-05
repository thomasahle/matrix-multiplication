/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinogradRecursiveChildWordCore
import AxiomAudit.Command

set_option autoImplicit false

/-!
# Axiom audit for recursive CW labelled-child words

These checks cover the bounded child-digit and coarse-address alphabets, the left-child digit and
word, the full `2(n+1)`-letter labelled child word, and the `simp` lemma that its first half is the
left-child word.  This is the finite address underlying the complete-split compatibility cells of
[alman2025more], Claim 6.18, `papers/sources/2404.16349/constituent.tex:404-429`.

No coarsening, hashing predicate, counting estimate or exponent endpoint is asserted here.

## References

- [alman2025more] Josh Alman, Ran Duan, Virginia Vassilevska Williams, Yinzhan Xu, Zixuan Xu,
  and Renfei Zhou, *More Asymmetry Yields Faster Matrix Multiplication*.
-/

open AlgebraicComplexity.Examples

#assert_axioms CWRecursiveChildDigit
#assert_axioms CWRecursiveCoarseAddress
#assert_axioms cwRecursiveLeftChildDigit
#assert_axioms cwRecursiveLeftChildWord
#assert_axioms cwRecursiveLabelledChildWord
#assert_axioms cwRecursiveLabelledChildWord_left
