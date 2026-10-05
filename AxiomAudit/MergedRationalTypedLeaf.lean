/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AxiomAudit.Command
import AlgebraicComplexity.MatrixMultiplication.MergedRationalTypedLeaf

/-! Focused trust audit for the merged rational typed leaf (C1b item 8): the leg-scaling helper and
its two dimension-product laws, the passage from a merged leaf to an ordinary rational typed leaf,
the exact bookkeeping on the designated leg and its invariance on the other two, the zero-class
constructor with its four comparisons against the class, the fine (representative) leaf and the
**exact factorization** `merged = classCardProduct · representative` that carries E1's
zero-coordinate entropy term into the leaf dimension, the three leg-named `Restricts`-level merge
absorptions, and the stage dimension shrink the packaging interface consumes. -/

open AlgebraicComplexity
open AlgebraicComplexity.MergedRationalTypedLeaf

#assert_axioms AlgebraicComplexity.RationalTypedLeaf.scaleLeg
#assert_axioms AlgebraicComplexity.RationalTypedLeaf.legFactorProduct_pos
#assert_axioms AlgebraicComplexity.RationalTypedLeaf.scaleLeg_dimensionProduct_self
#assert_axioms AlgebraicComplexity.RationalTypedLeaf.scaleLeg_dimensionProduct_of_ne
#assert_axioms AlgebraicComplexity.RationalTypedLeaf.dimensionProduct_le_scaleLeg

#assert_axioms toRationalTypedLeaf
#assert_axioms toRationalTypedLeaf_dimension_mergeLeg
#assert_axioms toRationalTypedLeaf_dimension_of_ne
#assert_axioms mergedFactorProduct_pos
#assert_axioms dimensionProduct_mergeLeg
#assert_axioms dimensionProduct_of_ne
#assert_axioms residual_dimensionProduct_le

#assert_axioms ofZeroClasses
#assert_axioms ofZeroClasses_mergedFactor
#assert_axioms pow_ones_le_mergedFactor
#assert_axioms card_le_mergedFactor
#assert_axioms card_mul_pow_le_mergedFactor
#assert_axioms mergedFactor_eq_card_mul_pow_of_uniform

#assert_axioms classCardProduct_pos
#assert_axioms representativeLeaf
#assert_axioms representativeLeaf_dimensionProduct_mergeLeg
#assert_axioms mergedFactorProduct_of_uniform
#assert_axioms dimensionProduct_mergeLeg_eq_classCardProduct_mul_representative
#assert_axioms representativeLeaf_dimensionProduct_le
#assert_axioms classCardProduct_le_mergedFactorProduct
#assert_axioms classCardProduct_mul_residual_le_dimensionProduct_mergeLeg

#assert_axioms restricts_matrixMultiplication_mergeX
#assert_axioms restricts_matrixMultiplication_mergeY
#assert_axioms restricts_matrixMultiplication_mergeZ
#assert_axioms AlgebraicComplexity.WholeConstituentLaserVolumeStage.shrinkDimensions
