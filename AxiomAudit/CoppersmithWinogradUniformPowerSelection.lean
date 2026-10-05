/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.Examples.CoppersmithWinogradUniformPowerSelection

/-! Focused trust audit for the Coppersmith--Winograd zero-`Z` uniform local `q`-power: the
outer middle-count statistic and its polynomial bound, the loss-free uniformity of the selected
family, the merged dimension of the whole retained class, the fused merged leaf in both its
abstract and label-map forms, and the pigeonhole route kept available for families selected by
weight alone. -/

open AlgebraicComplexity
open AlgebraicComplexity.Examples

#assert_axioms cwInterfaceMiddleCount
#assert_axioms cwInterfaceQExponent
#assert_axioms cwInterfaceMiddleCount_le
#assert_axioms cwInterfaceMiddleCount_eq_of_mem_support
#assert_axioms cwSelectedExactInterfaceTerm_mergedDimension_eq
#assert_axioms cwSelectedExactInterfaceTerm_restricts_mergedOneSlice
#assert_axioms cwZeroZOneSliceFiberRetyping
#assert_axioms cwZeroZOneSliceFiberRetyping_targetConstituent
#assert_axioms cwSelectedExactInterfaceTerm_zeroZ_restricts_oneSlice_of_labelMaps
#assert_axioms cwSelectedExactInterfaceTerm_zeroZ_restricts_mergedOneSlice_of_labelMaps
#assert_axioms cwSelectedExactInterfaceTerm_zeroZ_exists_uniform_power_fibre
