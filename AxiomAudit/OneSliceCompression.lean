/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Examples.AlmanLiOneSliceSpeedup
import AlgebraicComplexity.MatrixMultiplication.OneSliceCompression

set_option autoImplicit false

/-!
# Axiom audit for one-slice compression

Focused trust audit for [AlmanLi2026, Proposition 5.7, p. 18] (= [Strassen1988, Proposition 6.4]):
the proof in `MatrixMultiplication/OneSliceCompression.lean` and the discharged statement
`AlmanLi.OneSliceCompression` of `Examples/AlmanLiOneSliceSpeedup.lean`.
-/

namespace AlgebraicComplexity

#assert_axioms oneSliceDirectSum_eq_sum
#assert_axioms span_range_indexedSliceX
#assert_axioms LinearIndependent.exists_linearMap_apply_eq
#assert_axioms restricts_map_oneSliceDirectSum
#assert_axioms AlmanLi.oneSliceCompression

end AlgebraicComplexity
