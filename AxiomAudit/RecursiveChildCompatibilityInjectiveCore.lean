/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.RecursiveChildCompatibilityInjectiveCore
import AxiomAudit.Command

set_option autoImplicit false

/-!
# Axiom audit for dependency-light recursive-child injectivity

These checks cover the identification of the lightweight left/right half-word observations with
the public complete-split projections, and the theorem that a positive word of parent chunks is
determined by the sequence of its labelled children.  That injectivity is the step the
compatibility count of [alman2025more] relies on in the proof of Claim 6.18,
`papers/sources/2404.16349/constituent.tex:404-429`.

No compatibility model, count, rate or endpoint is asserted here.

## References

- [alman2025more] Josh Alman, Ran Duan, Virginia Vassilevska Williams, Yinzhan Xu, Zixuan Xu,
  and Renfei Zhou, *More Asymmetry Yields Faster Matrix Multiplication*.
-/

open AlgebraicComplexity.MoreAsymmetryCompatibility

#assert_axioms leftChildHalf_eq_splitWordSuccEquiv
#assert_axioms rightChildHalf_eq_splitWordSuccEquiv
#assert_axioms positiveWordLabelledChildren_injective
