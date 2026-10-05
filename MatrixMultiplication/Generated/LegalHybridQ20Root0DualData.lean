/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.LevelFourShapeDefs
import MatrixMultiplication.HomogeneousIntegerEntropyDualForm
import Mathlib.Tactic.NormNum

set_option autoImplicit false

/-!
# Canonical q20 root-zero integer-dual partition

This is the root-zero arithmetic instance of `eq:partition` in
`better_bound/paper.tex:2274-2307`, with logarithmic potentials from positive integer factors
as in `prop:dual`. The support is the committed `shapes 16`: all 153 ordered nonnegative triples
of total sixteen, the root alphabet for eight CW letters [coppersmith1990matrix].

The three rows of seventeen factors are copied exactly from root zero of
`better_bound/legal_hybrid/standard_integer_dual_witness.json`, SHA-256
`6b45b2c1c24ce9c1d08881d48708919c37ea7d90989762e9b6bb7b5aebb52b6a`.
That witness names the canonical candidate `better_bound/legal_hybrid/candidate_b32.npz`,
SHA-256 `0e8355da17679e855c12f0a2cdf53d53709417e8508c9941be8920456cc43b8d`.
The consumer is `legal_hybrid/check_directed.py:684-688`, calling
`export_simplified_exponent_scalar.py:474-507`. No exponential or floating-point generation
step is trusted here.

The proof checks seventeen fixed-X subtotals, each containing at most seventeen integer
products, then composes them by the committed lexicographic shape enumeration. The three
factor functions take the positive default one outside 0,...,16; these values are not used by
`shapes 16`. The aggregate uses the existing explicit-list partition API, not an independent
support or cached replacement definition. No heartbeat or recursion limit is raised.

This proves neither root marginal correspondence nor the complete dual inequality, entropy
recurrence, tensor extraction, numerical margin, or exponent endpoint. Those remain separate
q20 reconstruction and semantic obligations.

## Reference

- [coppersmith1990matrix] Don Coppersmith and Shmuel Winograd, *Matrix multiplication via
  arithmetic progressions*.
- Total-Weight manuscript, `better_bound/paper.tex:2274-2307`, `eq:partition` and `prop:dual`.
-/

namespace MatrixMultiplication.Generated.LegalHybridQ20Root0DualData

open AlgebraicComplexity.LevelFourReconstruction
open MatrixMultiplication.HomogeneousIntegerEntropyDualForm

/-- Root-zero X-coordinate integer factors, with positive default one off the root alphabet. -/
def xFactor : ℕ → ℕ
  | 0 => 4294967296
  | 1 => 34513394397
  | 2 => 1209913689207
  | 3 => 7050740972138
  | 4 => 13441023810807
  | 5 => 17416780162892
  | 6 => 17669147814086
  | 7 => 16306473312657
  | 8 => 8257480145599
  | 9 => 2680973493975
  | 10 => 100034486508
  | 11 => 105530615000
  | 12 => 146129782981
  | 13 => 125781985023
  | 14 => 116964432843
  | 15 => 358965278955
  | 16 => 1871150115941
  | _ => 1

/-- Root-zero Y-coordinate integer factors, with positive default one off the root alphabet. -/
def yFactor : ℕ → ℕ
  | 0 => 4294967296
  | 1 => 32282281713
  | 2 => 1560913033818
  | 3 => 7513295957234
  | 4 => 12483025993541
  | 5 => 17202081468490
  | 6 => 18465566097880
  | 7 => 14900547841341
  | 8 => 7035667363244
  | 9 => 2226444690219
  | 10 => 99629119348
  | 11 => 116387966291
  | 12 => 156186475852
  | 13 => 124966516503
  | 14 => 118739043670
  | 15 => 362467014729
  | 16 => 1859483873209
  | _ => 1

/-- Root-zero Z-coordinate integer factors, with positive default one off the root alphabet. -/
def zFactor : ℕ → ℕ
  | 0 => 4294967296
  | 1 => 35318195244
  | 2 => 1167890192855
  | 3 => 7710747542329
  | 4 => 14530201173103
  | 5 => 18633622529277
  | 6 => 19711654852782
  | 7 => 17980014818846
  | 8 => 8564838085127
  | 9 => 2630483737363
  | 10 => 103442746487
  | 11 => 108902376104
  | 12 => 149625862724
  | 13 => 126739584322
  | 14 => 118673553337
  | 15 => 359062900770
  | 16 => 1871653710324
  | _ => 1

/-- Every value of the root-zero X factor is strictly positive. -/
theorem xFactor_pos (i : ℕ) : 0 < xFactor i := by
  unfold xFactor
  split <;> decide

/-- Every value of the root-zero Y factor is strictly positive. -/
theorem yFactor_pos (i : ℕ) : 0 < yFactor i := by
  unfold yFactor
  split <;> decide

/-- Every value of the root-zero Z factor is strictly positive. -/
theorem zFactor_pos (i : ℕ) : 0 < zFactor i := by
  unfold zFactor
  split <;> decide

/-- Sum of the integer products over the legal root shapes with first coordinate `x`. -/
def fixedXSubtotal (x : ℕ) : ℕ :=
  ((List.range (16 - x + 1)).map fun y ↦
    xFactor x * yFactor y * zFactor (16 - x - y)).sum

/-- The fixed-X subtotal at `x = 0`, checked using only 17 integer products. -/
theorem fixedXSubtotal_0 :
    fixedXSubtotal 0 = 660651538277660151486129308474277888 := by
  decide

/-- The fixed-X subtotal at `x = 1`, checked using only 16 integer products. -/
theorem fixedXSubtotal_1 :
    fixedXSubtotal 1 = 12285122653770461589995188239756042774 := by
  decide

/-- The fixed-X subtotal at `x = 2`, checked using only 15 integer products. -/
theorem fixedXSubtotal_2 :
    fixedXSubtotal 2 = 794148479494023281079718538989801247385 := by
  decide

/-- The fixed-X subtotal at `x = 3`, checked using only 14 integer products. -/
theorem fixedXSubtotal_3 :
    fixedXSubtotal 3 = 6847739286858640901710982348127623798726 := by
  decide

/-- The fixed-X subtotal at `x = 4`, checked using only 13 integer products. -/
theorem fixedXSubtotal_4 :
    fixedXSubtotal 4 = 16092862596979358828563321486075082685429 := by
  decide

/-- The fixed-X subtotal at `x = 5`, checked using only 12 integer products. -/
theorem fixedXSubtotal_5 :
    fixedXSubtotal 5 = 21761035000392930310401715443629367056620 := by
  decide

/-- The fixed-X subtotal at `x = 6`, checked using only 11 integer products. -/
theorem fixedXSubtotal_6 :
    fixedXSubtotal 6 = 19553392746405749460549832496865469521516 := by
  decide

/-- The fixed-X subtotal at `x = 7`, checked using only 10 integer products. -/
theorem fixedXSubtotal_7 :
    fixedXSubtotal 7 = 13355813655736597349949013823795419446489 := by
  decide

/-- The fixed-X subtotal at `x = 8`, checked using only 9 integer products. -/
theorem fixedXSubtotal_8 :
    fixedXSubtotal 8 = 4190913445967749190241946096142002121955 := by
  decide

/-- The fixed-X subtotal at `x = 9`, checked using only 8 integer products. -/
theorem fixedXSubtotal_9 :
    fixedXSubtotal 9 = 686405619130197181170761858986910778375 := by
  decide

/-- The fixed-X subtotal at `x = 10`, checked using only 7 integer products. -/
theorem fixedXSubtotal_10 :
    fixedXSubtotal 10 = 9659866662849370888601981125864414464 := by
  decide

/-- The fixed-X subtotal at `x = 11`, checked using only 6 integer products. -/
theorem fixedXSubtotal_11 :
    fixedXSubtotal 11 = 2308415737554901292300264840475205000 := by
  decide

/-- The fixed-X subtotal at `x = 12`, checked using only 5 integer products. -/
theorem fixedXSubtotal_12 :
    fixedXSubtotal 12 = 358496182293804586590811654715896947 := by
  decide

/-- The fixed-X subtotal at `x = 13`, checked using only 4 integer products. -/
theorem fixedXSubtotal_13 :
    fixedXSubtotal 13 = 19900918818443170574521476029893665 := by
  decide

/-- The fixed-X subtotal at `x = 14`, checked using only 3 integer products. -/
theorem fixedXSubtotal_14 :
    fixedXSubtotal 14 = 1504194484343594673417004263448740 := by
  decide

/-- The fixed-X subtotal at `x = 15`, checked using only 2 integer products. -/
theorem fixedXSubtotal_15 :
    fixedXSubtotal 15 = 104222638771016650085445150965760 := by
  decide

/-- The fixed-X subtotal at `x = 16`, checked using only one integer product. -/
theorem fixedXSubtotal_16 :
    fixedXSubtotal 16 = 34516627312255582156237523910656 := by
  decide

/-- The root-zero integer partition on the committed total-sixteen shape support. -/
def partitionNumerator : ℕ :=
  integerPartitionNumeratorOn (shapes 16) Shape.x Shape.y Shape.z xFactor yFactor zFactor

/-- The partition is the sum of the seventeen fixed-X subtotals.

Proof sketch: distribute the product-weight map and sum over the lexicographic enumeration's
concatenated fixed-X rows. No numerical product is reduced in this structural step.
-/
theorem partitionNumerator_eq_sum_fixedXSubtotal :
    partitionNumerator = ((List.range 17).map fixedXSubtotal).sum := by
  unfold partitionNumerator integerPartitionNumeratorOn shapes
  generalize List.range 17 = xs
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.flatMap_cons, List.map_append, List.sum_append, List.map_cons,
      List.sum_cons, List.map_map]
    change fixedXSubtotal x + _ = fixedXSubtotal x + _
    exact congrArg (fun value ↦ fixedXSubtotal x + value) ih

/-- The canonical q20 root-zero partition is the exact displayed positive integer.

Proof sketch: rewrite the structural partition decomposition, substitute the seventeen checked
subtotals, and add them. The final arithmetic check sees seventeen integers, not 153 products.
-/
theorem partitionNumerator_eq :
    partitionNumerator = 83307604927592561572213746647943930712389 := by
  rw [partitionNumerator_eq_sum_fixedXSubtotal]
  have hRange : List.range 17 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16] := by
    decide
  rw [hRange]
  norm_num only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    fixedXSubtotal_0, fixedXSubtotal_1, fixedXSubtotal_2,
    fixedXSubtotal_3, fixedXSubtotal_4, fixedXSubtotal_5,
    fixedXSubtotal_6, fixedXSubtotal_7, fixedXSubtotal_8,
    fixedXSubtotal_9, fixedXSubtotal_10, fixedXSubtotal_11,
    fixedXSubtotal_12, fixedXSubtotal_13, fixedXSubtotal_14,
    fixedXSubtotal_15, fixedXSubtotal_16]

end MatrixMultiplication.Generated.LegalHybridQ20Root0DualData
