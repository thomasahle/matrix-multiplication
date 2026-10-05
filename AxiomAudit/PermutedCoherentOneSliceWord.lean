/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.PermutedCoherentOneSliceWord
import AxiomAudit.Command

/-!
# Axiom audit for coherent one-slice word certificates in a rotated frame

Checks the dependent-congruence lemma that replaces the `congr` bookkeeping of the committed
zero-`Z` chain, the three readings of a transported certificate's maps, and the coherent rotated
word recursion itself.
-/

open AlgebraicComplexity

/-! ## The dependent bookkeeping -/

#assert_axioms OneSliceProduct.coordinateProductMapAfter_heq

/-! ## Reading the maps of a transported certificate -/

#assert_axioms OneSliceRestriction.congrTensor_legMap
#assert_axioms OneSliceRestriction.permuteExternal_legMap
#assert_axioms OneSliceRestriction.permuteExternal_legMap_Z

/-! ## The canonical shared map, and the coherent recursion -/

#assert_axioms OneSliceRestriction.constWordZMap
#assert_axioms OneSliceRestriction.constWordZMap_zero
#assert_axioms OneSliceRestriction.constWordZMap_succ
#assert_axioms OneSliceRestriction.permutedCoherentWord
#assert_axioms OneSliceRestriction.permutedCoherentPositivePowerConstituent
