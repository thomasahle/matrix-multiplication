/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Tensor.Leg
import AlgebraicComplexity.Tensor.Basic
import AlgebraicComplexity.Tensor.Relation
import AlgebraicComplexity.Tensor.Restriction
import AlgebraicComplexity.Tensor.Product
import AlgebraicComplexity.Tensor.DirectSum
import AlgebraicComplexity.Tensor.DirectSumPower
import AlgebraicComplexity.Tensor.IndexedDirectSum
import AlgebraicComplexity.Tensor.IndexedDegeneration
import AlgebraicComplexity.Tensor.IndexedSubfamily
import AlgebraicComplexity.Tensor.IndexedProduct
import AlgebraicComplexity.Tensor.IndexedPower
import AlgebraicComplexity.Tensor.IteratedProduct
import AlgebraicComplexity.Tensor.Power
import AlgebraicComplexity.Tensor.PowerCoherence
import AlgebraicComplexity.Tensor.PositiveExternalPower
import AlgebraicComplexity.Tensor.PowerFamily
import AlgebraicComplexity.Tensor.PowerZeroUnit
import AlgebraicComplexity.Tensor.Rank
import AlgebraicComplexity.Tensor.RankCompression
import AlgebraicComplexity.Tensor.Concise
import AlgebraicComplexity.Tensor.Coordinates
import AlgebraicComplexity.Tensor.Polynomial
import AlgebraicComplexity.Tensor.Degeneration
import AlgebraicComplexity.Tensor.FreeLunchSpeedup
import AlgebraicComplexity.Tensor.PolynomialScalar
import AlgebraicComplexity.Tensor.PolynomialKernelFrame
import AlgebraicComplexity.Tensor.OneSliceBorderSpeedup
import AlgebraicComplexity.Tensor.BorderRank
import AlgebraicComplexity.Tensor.BorderRankTransport
import AlgebraicComplexity.Tensor.BorderConcise
import AlgebraicComplexity.Tensor.AsymptoticRank
import AlgebraicComplexity.Tensor.AsymptoticRankCalculus
import AlgebraicComplexity.Tensor.Monomial
import AlgebraicComplexity.Tensor.PolynomialInterpolation
import AlgebraicComplexity.Tensor.Partitioned
import AlgebraicComplexity.Tensor.PartitionedGrouping
import AlgebraicComplexity.Tensor.PartitionedGroupingBoxes
import AlgebraicComplexity.Tensor.PartitionedBoxRetyping
import AlgebraicComplexity.Tensor.PartitionedMonomial
import AlgebraicComplexity.Tensor.PartitionedPermutation
import AlgebraicComplexity.Tensor.PartitionedReindex
import AlgebraicComplexity.Tensor.PartitionedRelabeling
import AlgebraicComplexity.Tensor.PartitionedCoarsening
import AlgebraicComplexity.Tensor.PartitionedProduct
import AlgebraicComplexity.Tensor.PartitionedPower
import AlgebraicComplexity.Tensor.PartitionedPowerRelabeling
import AlgebraicComplexity.Tensor.PartitionedExtraction
import AlgebraicComplexity.Tensor.PartitionedDirectSum
import AlgebraicComplexity.Tensor.CompatibilityZeroing
import AlgebraicComplexity.Tensor.GroupedCompatibilityZeroing
import AlgebraicComplexity.Tensor.HoleRepair
import AlgebraicComplexity.Tensor.HoleRepairTree
import AlgebraicComplexity.Tensor.AsymptoticIndependenceNumber
import AlgebraicComplexity.Tensor.AsymptoticInvariant
import AlgebraicComplexity.Tensor.AsymptoticSliceRank
import AlgebraicComplexity.Tensor.CompatibilityIsolationCeiling
import AlgebraicComplexity.Tensor.CoordinateBlockWord
import AlgebraicComplexity.Tensor.CoordinateTensorSingle
import AlgebraicComplexity.Tensor.DegenerationPermutation
import AlgebraicComplexity.Tensor.GroupCoefficients
import AlgebraicComplexity.Tensor.GroupTensor
import AlgebraicComplexity.Tensor.GroupedCompatibilityOperationHoles
import AlgebraicComplexity.Tensor.GroupedCompatibilityPermutation
import AlgebraicComplexity.Tensor.IndependenceMeasure
import AlgebraicComplexity.Tensor.IndependenceNumber
import AlgebraicComplexity.Tensor.IndependenceSplitting
import AlgebraicComplexity.Tensor.KoszulFlattening
import AlgebraicComplexity.Tensor.MatrixFlattening
import AlgebraicComplexity.Tensor.MatrixFlatteningDirectSum
import AlgebraicComplexity.Tensor.MonomialIndependence
import AlgebraicComplexity.Tensor.PartitionedBlockMap
import AlgebraicComplexity.Tensor.PartitionedBlockMapPower
import AlgebraicComplexity.Tensor.PartitionedBoxRestriction
import AlgebraicComplexity.Tensor.PartitionedPermutePower
import AlgebraicComplexity.Tensor.PartitionedPowerExternalInterchange
import AlgebraicComplexity.Tensor.PartitionedPowerSupportDecodeCore
import AlgebraicComplexity.Tensor.PartitionedPowerSupportDecodeRecursive
import AlgebraicComplexity.Tensor.PartitionedProductConstituent
import AlgebraicComplexity.Tensor.PartitionedReindexConstituent
import AlgebraicComplexity.Tensor.PartitionedReindexStructureRelabeling
import AlgebraicComplexity.Tensor.PartitionedSelectPositivePower
import AlgebraicComplexity.Tensor.PartitionedSelectStructure
import AlgebraicComplexity.Tensor.PermutationCoherence
import AlgebraicComplexity.Tensor.PositiveWordAppendConst
import AlgebraicComplexity.Tensor.PositiveWordConstantPower
import AlgebraicComplexity.Tensor.PositiveWordRelation
import AlgebraicComplexity.Tensor.SingleLegHoleRepair
import AlgebraicComplexity.Tensor.SliceRank
import AlgebraicComplexity.Tensor.SliceRankDegeneration
import AlgebraicComplexity.Tensor.SliceRankSaturation
import AlgebraicComplexity.Tensor.StrassenEquations
import AlgebraicComplexity.Tensor.Subrank
import AlgebraicComplexity.Tensor.SubstitutionMethod
import AlgebraicComplexity.Tensor.SubstitutionMethodScale

/-!
# Reusable tensor algebra for algebraic complexity

This is the stable public entry point for the paper-independent tensor foundation. It collects
the three-leg tensor representation and its structural calculus:

* leg maps, permutations, isomorphisms, and exact restrictions;
* tensor-product-compatible relations, labelled decompositions, and staged transformations;
* products, sums, binomial direct-sum powers, indexed families, powers, and their coherence
  equivalences;
* constructive rank, polynomial degeneration, border rank, and asymptotic rank;
* slice rank, subrank, independence numbers, and the asymptotic invariants above them;
* matrix and Koszul flattenings, Strassen's equations, and the substitution method;
* group tensors and their coefficient bookkeeping;
* coordinate bridges and monomial certificates; and
* partitioned tensors, semantic zeroing, extraction, grouping, and finite hole repair.

The umbrella intentionally does **not** import named tensors, matrix-multiplication exponents,
hashing, numerical certificates, or paper clients.  It also excludes the `Tensor/` modules that
bridge upwards into `Combinatorics/`, `Probability/` or `Analysis/` — word-type extraction and the
coarsening/localization modules built on it, and the block-entropy bridges: importing any of them
here would drag layer 2 into the stable root, which `scripts/check_tensor_boundary.sh` forbids
(its five grandfathered edges are edges *out of* those modules, not licences to import them).
They remain available through their narrow modules.  Every other tracked module under
`AlgebraicComplexity/Tensor/` is reachable from here, so the boundary check restricts the whole
layer.

Implementation files should continue importing the narrowest module they need. This umbrella is
for downstream users, API smoke tests, documentation, and a potential future CSLib contribution.
-/
