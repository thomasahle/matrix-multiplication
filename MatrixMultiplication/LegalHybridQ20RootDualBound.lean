/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import MatrixMultiplication.Generated.LegalHybridQ20PrimaryData
import MatrixMultiplication.Generated.LegalHybridQ20RootDualData
import MatrixMultiplication.SimplifiedExponentLevelFourRecurrence
import MatrixMultiplication.SimplifiedExponentRootRecurrence
import Mathlib.Data.List.OfFn

set_option autoImplicit false

/-!
# Homogeneous integer-dual bounds for the actual q20 root laws

This module instantiates `prop:dual` and `eq:partition` of the Total-Weight manuscript,
`better_bound/paper.tex:2274-2307`. The root laws are the homogeneous representation of
[alman2025more], `prop:global-stage-no-eps`,
`papers/sources/2404.16349/global.tex:81-90`: the product of the regional weight `A_r` and
its normalized shape law `alpha_r`. The concrete reconstruction follows
`better_bound/legal_hybrid/check_directed.py:654-688` and its `weighted_integer_dual` call.

For every total-sixteen shape, the reference numerator is read from the canonical q20 top
source. A positive shape receives the sum over all six incoming regions and every genuine
ordered child pair; a boundary shape receives its native top-zero numerator. In particular,
the diagonal positive-parent schedule alone is not the root law. The unrelated six lower
primary fields are empty because neither top reconstruction nor top-zero lookup reads them.

Proof sketch: enumerate the committed 153 shapes by the existing finite root index. This
identifies the semantic integer partition with the six already checked literal partitions.
The positive factors then instantiate the existing zero-safe homogeneous version of the
paper's Gibbs/KL argument. Subtracting that upper bound gives a conservative logical-X rate.
No optimizer convergence, positive root mass, or per-root probability normalization is assumed.

The q20 candidate SHA-256 is
`0e8355da17679e855c12f0a2cdf53d53709417e8508c9941be8920456cc43b8d`; its integer witness is
`6b45b2c1c24ce9c1d08881d48708919c37ea7d90989762e9b6bb7b5aebb52b6a`.
These are project-specific data, not parameters supplied by [alman2025more]. This module does
not identify a separately serialized marginal table, certify a rational rate floor, construct
an extraction, or prove an exponent endpoint. It does not evaluate the complete sparse data.

## Reference

- [alman2025more] Josh Alman, Ran Duan, Virginia Vassilevska Williams, Yinzhan Xu,
  Zixuan Xu, and Renfei Zhou, *More Asymmetry Yields Faster Matrix Multiplication*.
- Total-Weight manuscript, `better_bound/paper.tex:2274-2307`, `prop:dual` and `eq:partition`.
- Exact q20 root factor and partition data: `Generated/LegalHybridQ20RootDualData.lean`.
-/

open scoped BigOperators

namespace MatrixMultiplication.LegalHybridQ20RootDualBound

open AlgebraicComplexity.LevelFourReconstruction
open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.EntropyDual
open MatrixMultiplication.Generated.LegalHybridQ20RootDualData
open MatrixMultiplication.HomogeneousEntropyDual
open MatrixMultiplication.HomogeneousIntegerEntropyDualForm
open MatrixMultiplication.IntegerEntropyDual
open MatrixMultiplication.SimplifiedExponentLevelFourRecurrence
open MatrixMultiplication.SimplifiedExponentRootRecurrence
open MatrixMultiplication.SimplifiedVolumeReconstruction

noncomputable section

/-- Only the canonical top field is read by the root reconstruction. -/
private def topPrimary : PrimaryTables :=
  { top := MatrixMultiplication.Generated.LegalHybridQ20Primary.topChunks
    pos3A := #[]
    pos3Alpha := #[]
    edgeZero2 := #[]
    zero3 := #[]
    zero4 := #[]
    mu := #[] }

/-- Actual q20 numerator of a total-sixteen root shape, including positive and boundary mass.

Positive shapes sum every incoming region and every ordered child pair belonging to that
parent. Boundary shapes use the original zero-coordinate shape ordering and sparse lookup. -/
def rootNumerator (root : Fin 6) (index : Fin rootShapeCount) : ℕ :=
  let shape := rootShape index
  if shape.IsPositive then
    ∑ region : Fin 6,
      ((levelFourPairsForParent shape).map fun pair ↦
        topNumeratorFrom (reconstructedTopBranchRows topPrimary)
          root.val region.val (levelFourPairs.idxOf pair)).sum
  else
    topZeroNumerator topPrimary root.val
      (MatrixMultiplication.LevelFourRemainingReconstruction.zeroFourShapes.idxOf shape)

/-- The finite semantic root index enumerates exactly the committed ordered shape list. -/
private theorem rootShape_ofFn : List.ofFn rootShape = shapes 16 := by
  calc
    List.ofFn rootShape =
        List.ofFn (fun i : Fin (shapes 16).length ↦
          rootShape (Fin.cast shapes_sixteen_length i)) :=
      List.ofFn_congr shapes_sixteen_length.symm rootShape
    _ = List.ofFn (shapes 16).get := by rfl
    _ = shapes 16 := List.ofFn_get _

/-- The typed semantic partition is the already checked canonical partition at this root. -/
private theorem semanticPartition_eq (root : Fin 6) :
    integerPartitionNumerator (rootCoordinate 0) (rootCoordinate 1) (rootCoordinate 2)
        (fun x : Fin 17 ↦ xFactor root x.val)
        (fun y : Fin 17 ↦ yFactor root y.val)
        (fun z : Fin 17 ↦ zFactor root z.val) = expectedPartition root := by
  calc
    integerPartitionNumerator (rootCoordinate 0) (rootCoordinate 1) (rootCoordinate 2)
        (fun x : Fin 17 ↦ xFactor root x.val)
        (fun y : Fin 17 ↦ yFactor root y.val)
        (fun z : Fin 17 ↦ zFactor root z.val) =
        ((List.ofFn rootShape).map fun shape ↦
          xFactor root shape.x * yFactor root shape.y * zFactor root shape.z).sum := by
      change (∑ i : Fin rootShapeCount,
          xFactor root (rootShape i).x * yFactor root (rootShape i).y *
            zFactor root (rootShape i).z) = _
      simp only [List.map_ofFn, List.sum_ofFn, Function.comp_apply]
    _ = partitionNumerator root := by
      rw [rootShape_ofFn]
      rfl
    _ = expectedPartition root := partitionNumerator_eq root

/-- Exact homogeneous integer-dual upper expression for one reconstructed q20 root law.

The checked partition logarithm is multiplied by this root's actual mass. All three
potential expectations use the coordinate marginals of that same unnormalized law. -/
def integerDualBound (root : Fin 6) : ℝ :=
  mass 20 (∑ i, rootNumerator root i) *
      (Real.log (expectedPartition root : ℝ) / Real.log 2) -
    ((∑ x : Fin 17, logIntegerPotential (xFactor root) x.val *
        marginal (rootCoordinate 0) (fun i ↦ mass 20 (rootNumerator root i)) x) +
     (∑ y : Fin 17, logIntegerPotential (yFactor root) y.val *
        marginal (rootCoordinate 1) (fun i ↦ mass 20 (rootNumerator root i)) y) +
     (∑ z : Fin 17, logIntegerPotential (zFactor root) z.val *
        marginal (rootCoordinate 2) (fun i ↦ mass 20 (rootNumerator root i)) z))

/-- The concrete expression is the generic homogeneous integer dual with its partition reduced. -/
private theorem homogeneousIntegerDual_eq (root : Fin 6) :
    homogeneousIntegerDualBits 20 (rootNumerator root)
        (rootCoordinate 0) (rootCoordinate 1) (rootCoordinate 2)
        (fun x : Fin 17 ↦ xFactor root x.val)
        (fun y : Fin 17 ↦ yFactor root y.val)
        (fun z : Fin 17 ↦ zFactor root z.val) = integerDualBound root := by
  unfold homogeneousIntegerDualBits
  rw [integerPartition_eq_cast, semanticPartition_eq]
  rfl

/-- The maximum homogeneous entropy with the actual q20 root marginals is bounded by its
canonical integer dual, including when that root has zero mass.

Proof sketch: the reference is a nonnegative dyadic row by construction. Apply the existing
zero-safe Gibbs/KL dual inequality with the three proved-positive coordinate factors, then
replace the semantic partition by its checked integer value. -/
theorem rootMaxEntropy_le_integerDualBound (root : Fin 6) :
    maximumHomogeneousEntropyBits (rootCoordinate 0) (rootCoordinate 1) (rootCoordinate 2)
        (fun i ↦ mass 20 (rootNumerator root i)) ≤ integerDualBound root := by
  letI : Nonempty (Fin rootShapeCount) := ⟨⟨0, by decide⟩⟩
  have hdual :=
    maximumHomogeneousEntropyBits_dyadic_le_homogeneousIntegerDualBits_of_nonnegative
      20 (rootNumerator root) (rootCoordinate 0) (rootCoordinate 1) (rootCoordinate 2)
      (fun x : Fin 17 ↦ xFactor root x.val)
      (fun y : Fin 17 ↦ yFactor root y.val)
      (fun z : Fin 17 ↦ zFactor root z.val)
      (fun x ↦ xFactor_pos root x.val)
      (fun y ↦ yFactor_pos root y.val)
      (fun z ↦ zFactor_pos root z.val)
  exact hdual.trans_eq (homogeneousIntegerDual_eq root)

/-- Conservative logical-X root rate: marginal entropy plus reference entropy minus the
canonical integer-dual upper expression, all measured in homogeneous bits. -/
def rootXCertifiedRate (root : Fin 6) : ℝ :=
  homogeneousEntropyBits
      (marginal (rootCoordinate 0) (fun i ↦ mass 20 (rootNumerator root i))) +
    homogeneousEntropyBits (fun i ↦ mass 20 (rootNumerator root i)) - integerDualBound root

/-- Mathematical logical-X root rate, using maximum entropy in the actual three-marginal
fiber of the reconstructed q20 root law, without a claim about tensor extraction. -/
def rootXSemanticRate (root : Fin 6) : ℝ :=
  homogeneousEntropyBits
      (marginal (rootCoordinate 0) (fun i ↦ mass 20 (rootNumerator root i))) +
    homogeneousEntropyBits (fun i ↦ mass 20 (rootNumerator root i)) -
    maximumHomogeneousEntropyBits (rootCoordinate 0) (rootCoordinate 1) (rootCoordinate 2)
      (fun i ↦ mass 20 (rootNumerator root i))

/-- Replacing the actual q20 root maximum entropy by its canonical integer dual can only
decrease the logical-X rate. No positive-mass or normalization premise is required. -/
theorem rootXCertifiedRate_le_rootXSemanticRate (root : Fin 6) :
    rootXCertifiedRate root ≤ rootXSemanticRate root := by
  unfold rootXCertifiedRate rootXSemanticRate
  exact sub_le_sub_left (rootMaxEntropy_le_integerDualBound root) _

end

end MatrixMultiplication.LegalHybridQ20RootDualBound
