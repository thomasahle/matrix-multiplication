/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.MatrixMultiplication.BiniInterpolation

set_option autoImplicit false

/-!
# Axiom audit for the border-rank exponent transfer

Focused trust audit for `AlgebraicComplexity/MatrixMultiplication/BiniInterpolation.lean`, which
carries Bini's interpolation argument -- D. Bini, M. Capovani, F. Romani and G. Lotti,
*O(n^2.7799) complexity for n × n approximate matrix multiplication*, Inform. Process. Lett.
**8** (1979), no. 5, 234--235 -- to the exponent transfer
`borderRank r ⟨q,q,q⟩ → omega ≤ log r / log q`.

The umbrella audit asserts the surrounding degeneration and border-rank machinery.  The two
exponent-transfer statements every approximate certificate in `Examples/` is read through are
asserted here.
-/

namespace AlgebraicComplexity

#assert_axioms omega_le_log_of_borderRankLEAt
#assert_axioms omega_le_log_of_borderRankLE

end AlgebraicComplexity
