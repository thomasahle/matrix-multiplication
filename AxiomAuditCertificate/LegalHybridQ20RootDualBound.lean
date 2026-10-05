/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import MatrixMultiplication.LegalHybridQ20RootDualBound

set_option autoImplicit false

/-!
# Axiom audit and concrete root-one client for q20 homogeneous duality

The source specializes the Gibbs/KL proof of `prop:dual`,
`better_bound/paper.tex:2274-2307`, to the actual q20 root numerators and integer factors.
The weighted regional root law follows [alman2025more], `prop:global-stage-no-eps`,
`papers/sources/2404.16349/global.tex:81-90`. The q20 literals are project-specific data.

Every public declaration is asserted below; their axiom cones also include the private
reconstruction and partition-enumeration helpers. The client applies the result at literal
root one, whose reconstruction includes both positive shapes and boundary mass. It assumes
no normalized row, abstract reference law, or entropy certificate hypothesis.

## Reference

- [alman2025more] Josh Alman, Ran Duan, Virginia Vassilevska Williams, Yinzhan Xu,
  Zixuan Xu, and Renfei Zhou, *More Asymmetry Yields Faster Matrix Multiplication*.
- Total-Weight manuscript, `better_bound/paper.tex:2274-2307`, `prop:dual`.
-/

namespace MatrixMultiplication.LegalHybridQ20RootDualBound

#assert_axioms rootNumerator
#assert_axioms integerDualBound
#assert_axioms rootMaxEntropy_le_integerDualBound
#assert_axioms rootXCertifiedRate
#assert_axioms rootXSemanticRate
#assert_axioms rootXCertifiedRate_le_rootXSemanticRate

/-- The literal root-one q20 entropy fiber satisfies the concrete integer-dual upper bound. -/
example :
    HomogeneousEntropyDual.maximumHomogeneousEntropyBits
        (SimplifiedExponentRootRecurrence.rootCoordinate 0)
        (SimplifiedExponentRootRecurrence.rootCoordinate 1)
        (SimplifiedExponentRootRecurrence.rootCoordinate 2)
        (fun i ↦ DyadicEntropy.mass 20 (rootNumerator 1 i)) ≤ integerDualBound 1 :=
  rootMaxEntropy_le_integerDualBound 1

/-- The same actual root-one law gives the intended conservative logical-X rate. -/
example : rootXCertifiedRate 1 ≤ rootXSemanticRate 1 :=
  rootXCertifiedRate_le_rootXSemanticRate 1

end MatrixMultiplication.LegalHybridQ20RootDualBound
