/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinogradPartition
import AlgebraicComplexity.MatrixMultiplication.ExternalProduct
import AlgebraicComplexity.Tensor.PartitionedCoarsening
import AlgebraicComplexity.Tensor.PartitionedPower

/-!
# The coarsened tensor square of the Coppersmith--Winograd tensor

The 1990 Coppersmith--Winograd construction starts with `CW_q ⊗ CW_q`.  Each original leg has
block degrees `0`, `1`, and `2`; in the square, pairs of blocks are merged according to the sum of
their degrees.  This file performs that regrouping through the generic partition-coarsening API
and proves that the coarse support is exactly the fifteen addresses `(I,J,K)` with `I+J+K=4`.

It also computes the source fibers of the four representative constituent classes `004`, `013`,
`022`, and `112`, expands those constituents as sums of transported raw products, and proves the
elementary `004` restriction.  Coordinate identifications for the ordinary `013` and `022`
classes are developed in `CoppersmithWinogradSquareConstituents`; the exceptional `112` value
argument is intentionally left downstream.

The support and fiber facts are small closed computations over the six base CW addresses.  The
algebraic statements then use the generic coarsening realization theorem, so this client tests
both the combinatorial address convention and the reusable direct-sum API.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor

universe u

/-- Natural-number version of the standard CW block weight. -/
def cwBlockDegree : CWBlock → ℕ
  | .zero => 0
  | .middle => 1
  | .last => 2

/-- The first CW block has degree zero. -/
@[simp] theorem cwBlockDegree_zero : cwBlockDegree .zero = 0 := rfl

/-- The middle CW block has degree one. -/
@[simp] theorem cwBlockDegree_middle : cwBlockDegree .middle = 1 := rfl

/-- The last CW block has degree two. -/
@[simp] theorem cwBlockDegree_last : cwBlockDegree .last = 2 := rfl

/-- A pair of CW blocks has total degree at most four. -/
def cwSquareBlockDegree (word : PositiveWord CWBlock 1) : Fin 5 :=
  ⟨cwBlockDegree word.1 + cwBlockDegree word.2, by
    rcases word with ⟨a, b⟩
    cases a <;> cases b <;> decide⟩

/-- The numeric value of a square-block degree is the sum of its two base block degrees. -/
@[simp] theorem cwSquareBlockDegree_val (word : PositiveWord CWBlock 1) :
    (cwSquareBlockDegree word).val = cwBlockDegree word.1 + cwBlockDegree word.2 :=
  rfl

/-- Apply the degree-sum coarsening independently on all three legs. -/
def cwSquareDegreeMap : ∀ _ : Leg, PositiveWord CWBlock 1 → Fin 5 :=
  fun _ ↦ cwSquareBlockDegree

/-- A coarse square address has one degree in `{0,1,2,3,4}` on every leg. -/
abbrev CWSquareAddress := BlockAddress (fun _ : Leg ↦ Fin 5)

/-- Convenience constructor for a coarse square address. -/
abbrev cwSquareAddress (x y z : Fin 5) : CWSquareAddress :=
  ofLegs x y z

/-- An uncoarsened square address obtained from two base CW addresses. -/
abbrev cwSquareRawAddress (left right : CWBlockAddress) :
    BlockAddress (fun _ : Leg ↦ PositiveWord CWBlock 1) :=
  blockAddressProductEquiv
    (A := fun _ : Leg ↦ CWBlock) (B := fun _ : Leg ↦ CWBlock) (left, right)

/-- The 36 addresses in the uncoarsened square support. -/
def cwSquareRawSupport :
    Finset (BlockAddress (fun _ : Leg ↦ PositiveWord CWBlock 1)) :=
  (cwBlockSupport.product cwBlockSupport).map
    (blockAddressProductEquiv
      (A := fun _ : Leg ↦ CWBlock) (B := fun _ : Leg ↦ CWBlock)).toEmbedding

/-- The combinatorial support obtained by squaring the six CW addresses and coarsening each pair
by degree sum. -/
def cwSquareSupport : Finset CWSquareAddress :=
  cwSquareRawSupport.image (coarsenBlockAddress cwSquareDegreeMap)

/-- Source square addresses contributing to one coarsened constituent. -/
def cwSquareSourceFiber (target : CWSquareAddress) :
    Finset (BlockAddress (fun _ : Leg ↦ PositiveWord CWBlock 1)) :=
  cwSquareRawSupport.filter fun source ↦
    coarsenBlockAddress cwSquareDegreeMap source = target

abbrev cwSquare004 : CWSquareAddress := cwSquareAddress 0 0 4
abbrev cwSquare013 : CWSquareAddress := cwSquareAddress 0 1 3
abbrev cwSquare022 : CWSquareAddress := cwSquareAddress 0 2 2
abbrev cwSquare112 : CWSquareAddress := cwSquareAddress 1 1 2

/-- The `004` constituent comes from the square of the corresponding corner constituent. -/
theorem cwSquareSourceFiber_004 :
    cwSquareSourceFiber cwSquare004 =
      {cwSquareRawAddress cw002 cw002} := by
  decide

/-- The `013` constituent merges the two orders of a corner and a middle constituent. -/
theorem cwSquareSourceFiber_013 :
    cwSquareSourceFiber cwSquare013 =
      {cwSquareRawAddress cw002 cw011,
        cwSquareRawAddress cw011 cw002} := by
  decide

/-- The `022` constituent merges two ordered corner products and the square of a middle
constituent. -/
theorem cwSquareSourceFiber_022 :
    cwSquareSourceFiber cwSquare022 =
      {cwSquareRawAddress cw002 cw020,
        cwSquareRawAddress cw020 cw002,
        cwSquareRawAddress cw011 cw011} := by
  decide

/-- The special `112` constituent is the sum of four ordered products. -/
theorem cwSquareSourceFiber_112 :
    cwSquareSourceFiber cwSquare112 =
      {cwSquareRawAddress cw002 cw110,
        cwSquareRawAddress cw110 cw002,
        cwSquareRawAddress cw011 cw101,
        cwSquareRawAddress cw101 cw011} := by
  decide

/-- Exactly one raw square constituent contributes to class `004`. -/
@[simp] theorem card_cwSquareSourceFiber_004 :
    (cwSquareSourceFiber cwSquare004).card = 1 := by
  rw [cwSquareSourceFiber_004]
  decide

/-- Exactly two raw square constituents contribute to class `013`. -/
@[simp] theorem card_cwSquareSourceFiber_013 :
    (cwSquareSourceFiber cwSquare013).card = 2 := by
  rw [cwSquareSourceFiber_013]
  decide

/-- Exactly three raw square constituents contribute to class `022`. -/
@[simp] theorem card_cwSquareSourceFiber_022 :
    (cwSquareSourceFiber cwSquare022).card = 3 := by
  rw [cwSquareSourceFiber_022]
  decide

/-- Exactly four raw square constituents contribute to the exceptional class `112`. -/
@[simp] theorem card_cwSquareSourceFiber_112 :
    (cwSquareSourceFiber cwSquare112).card = 4 := by
  rw [cwSquareSourceFiber_112]
  decide

/-- The fifteen-address degree-four antidiagonal. -/
def cwSquareAntidiagonal : Finset CWSquareAddress :=
  { cwSquareAddress 0 0 4,
    cwSquareAddress 0 1 3,
    cwSquareAddress 0 2 2,
    cwSquareAddress 0 3 1,
    cwSquareAddress 0 4 0,
    cwSquareAddress 1 0 3,
    cwSquareAddress 1 1 2,
    cwSquareAddress 1 2 1,
    cwSquareAddress 1 3 0,
    cwSquareAddress 2 0 2,
    cwSquareAddress 2 1 1,
    cwSquareAddress 2 2 0,
    cwSquareAddress 3 0 1,
    cwSquareAddress 3 1 0,
    cwSquareAddress 4 0 0 }

/-- The coarsened square support is exactly the degree-four antidiagonal.  This is a small finite
kernel computation (36 source pairs and 15 targets), retained as an early regression
test for direction and leg-order mistakes. -/
theorem cwSquareSupport_eq_antidiagonal :
    cwSquareSupport = cwSquareAntidiagonal := by
  decide

/-- Every listed coarse support address has total degree four. -/
theorem cwSquareAntidiagonal_degree_sum (address : CWSquareAddress)
    (haddress : address ∈ cwSquareAntidiagonal) :
    (address .X).val + (address .Y).val + (address .Z).val = 4 := by
  simp only [cwSquareAntidiagonal, Finset.mem_insert, Finset.mem_singleton] at haddress
  rcases haddress with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl <;> decide

/-- The coarsened square has fifteen support addresses. -/
@[simp] theorem card_cwSquareSupport : cwSquareSupport.card = 15 := by
  rw [cwSquareSupport_eq_antidiagonal]
  decide

section

variable (K : Type u) [CommRing K]
variable (q : ℕ)

/-- Block spaces of the uncoarsened tensor square. -/
abbrev CWSquareRawBlockSpace :=
  PositivePowerBlockSpace K (CWPartitionBlockSpace K q) 1

/-- The five coarsened block spaces on each leg of `CW_q ⊗ CW_q`. -/
abbrev CWSquareBlockSpace :=
  CoarsenedBlockSpace (V := CWSquareRawBlockSpace K q) cwSquareDegreeMap

/-- The typed CW tensor square after merging block pairs by their degree sum. -/
noncomputable def cwSquarePartitionedTensor :
    PartitionedTensor (K := K) (A := fun _ : Leg ↦ Fin 5)
      (CWSquareBlockSpace K q) :=
  ((cwPartitionedTensor K q).positivePower 1).coarsen cwSquareDegreeMap

/-- A raw square constituent is the external product of its two base CW constituents. -/
@[simp] theorem cwSquareRawConstituent (left right : CWBlockAddress) :
    ((cwPartitionedTensor K q).positivePower 1).constituent
        (cwSquareRawAddress left right) =
      Tensor.external
        ((cwPartitionedTensor K q).constituent left)
        ((cwPartitionedTensor K q).constituent right) := by
  rfl

/-- Fiberwise expansion of an arbitrary coarsened square constituent. -/
theorem cwSquareConstituent_eq_sum_sourceFiber (target : CWSquareAddress) :
    (cwSquarePartitionedTensor K q).constituent target =
      ∑ source ∈ cwSquareSourceFiber target,
        coarsenedTerm ((cwPartitionedTensor K q).positivePower 1)
          cwSquareDegreeMap target source := by
  rw [cwSquarePartitionedTensor, PartitionedTensor.coarsen_constituent,
    coarsenedConstituent_eq_sum_filter]
  rfl

/-- Exact one-term expansion of the `004` constituent. -/
theorem cwSquareConstituent_004 :
    (cwSquarePartitionedTensor K q).constituent cwSquare004 =
      coarsenedTerm ((cwPartitionedTensor K q).positivePower 1)
        cwSquareDegreeMap cwSquare004 (cwSquareRawAddress cw002 cw002) := by
  rw [cwSquareConstituent_eq_sum_sourceFiber, cwSquareSourceFiber_004]
  simp

/-- Exact two-term expansion of the `013` constituent. -/
theorem cwSquareConstituent_013 :
    (cwSquarePartitionedTensor K q).constituent cwSquare013 =
      coarsenedTerm ((cwPartitionedTensor K q).positivePower 1)
          cwSquareDegreeMap cwSquare013 (cwSquareRawAddress cw002 cw011) +
        coarsenedTerm ((cwPartitionedTensor K q).positivePower 1)
          cwSquareDegreeMap cwSquare013 (cwSquareRawAddress cw011 cw002) := by
  rw [cwSquareConstituent_eq_sum_sourceFiber, cwSquareSourceFiber_013]
  rw [Finset.sum_insert (by decide), Finset.sum_singleton]

/-- Exact three-term expansion of the `022` constituent. -/
theorem cwSquareConstituent_022 :
    (cwSquarePartitionedTensor K q).constituent cwSquare022 =
      coarsenedTerm ((cwPartitionedTensor K q).positivePower 1)
          cwSquareDegreeMap cwSquare022 (cwSquareRawAddress cw002 cw020) +
        coarsenedTerm ((cwPartitionedTensor K q).positivePower 1)
          cwSquareDegreeMap cwSquare022 (cwSquareRawAddress cw020 cw002) +
        coarsenedTerm ((cwPartitionedTensor K q).positivePower 1)
          cwSquareDegreeMap cwSquare022 (cwSquareRawAddress cw011 cw011) := by
  rw [cwSquareConstituent_eq_sum_sourceFiber, cwSquareSourceFiber_022]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton]
  abel

/-- Exact four-term expansion of the special `112` constituent. -/
theorem cwSquareConstituent_112 :
    (cwSquarePartitionedTensor K q).constituent cwSquare112 =
      coarsenedTerm ((cwPartitionedTensor K q).positivePower 1)
          cwSquareDegreeMap cwSquare112 (cwSquareRawAddress cw002 cw110) +
        coarsenedTerm ((cwPartitionedTensor K q).positivePower 1)
          cwSquareDegreeMap cwSquare112 (cwSquareRawAddress cw110 cw002) +
        coarsenedTerm ((cwPartitionedTensor K q).positivePower 1)
          cwSquareDegreeMap cwSquare112 (cwSquareRawAddress cw011 cw101) +
        coarsenedTerm ((cwPartitionedTensor K q).positivePower 1)
          cwSquareDegreeMap cwSquare112 (cwSquareRawAddress cw101 cw011) := by
  rw [cwSquareConstituent_eq_sum_sourceFiber, cwSquareSourceFiber_112]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton]
  abel

/-- The raw `002 ⊗ 002` term restricts to scalar multiplication. -/
theorem cwSquareRaw_002_002_restricts :
    Restricts
      (((cwPartitionedTensor K q).positivePower 1).constituent
        (cwSquareRawAddress cw002 cw002))
      (matrixMultiplication (K := K) 1 1 1) := by
  rw [cwSquareRawConstituent]
  have hbase :
      Restricts ((cwPartitionedTensor K q).constituent cw002)
        (matrixMultiplication (K := K) 1 1 1) := by
    simpa [cwPartitionedTensor, cwPartitionConstituent_ofLegs,
      cw002, cwBlockAddress] using cw002Constituent_restricts K q
  exact (hbase.external hbase).trans
    (Tensor.Isomorphic.matrixMultiplication_externalProduct
      (K := K) 1 1 1 1 1 1).restricts

/-- The canonical `004` coarse constituent is scalar multiplication, as in class (a) on journal
page 266. -/
theorem cwSquareConstituent_004_restricts :
    Restricts
      ((cwSquarePartitionedTensor K q).constituent cwSquare004)
      (matrixMultiplication (K := K) 1 1 1) := by
  rw [cwSquareConstituent_004]
  exact
    (Restricts.coarsenedTerm_of_eq
      ((cwPartitionedTensor K q).positivePower 1)
      cwSquareDegreeMap cwSquare004 (cwSquareRawAddress cw002 cw002)
      (by decide)).trans
    (cwSquareRaw_002_002_restricts K q)

/-- The client construction uses the purely combinatorial fifteen-address support above. -/
@[simp] theorem cwSquarePartitionedTensor_support :
    (cwSquarePartitionedTensor K q).support = cwSquareSupport := by
  rfl

/-- Therefore the typed tensor square has exactly the support stated in the 1990 paper. -/
theorem cwSquarePartitionedTensor_support_eq_antidiagonal :
    (cwSquarePartitionedTensor K q).support = cwSquareAntidiagonal := by
  rw [cwSquarePartitionedTensor_support, cwSquareSupport_eq_antidiagonal]

/-- Regrouping the tensor-square blocks preserves the realized square tensor. -/
theorem cwSquare_coarsening_isomorphic :
    Isomorphic
      ((cwPartitionedTensor K q).positivePower 1).realize
      (cwSquarePartitionedTensor K q).realize :=
  Isomorphic.partitionedCoarsen
    ((cwPartitionedTensor K q).positivePower 1) cwSquareDegreeMap

/-- The realized coarsened square inherits the squared `(q+2)\u00b2` constructive border-rank
certificate.

Proof sketch: tensor the base `q+2` certificate twice, identify the canonical second tensor
power with the positive partition power, and finally apply the exact degree-sum coarsening
isomorphism. -/
theorem cwSquarePartitionedTensor_borderRankLE :
    BorderRankLE ((q + 2) ^ 2) (cwSquarePartitionedTensor K q).realize := by
  have hisomorphic : Isomorphic
      (Tensor.power (cwPartitionedTensor K q).realize 2)
      (cwSquarePartitionedTensor K q).realize :=
    (Tensor.Isomorphic.power_partitionedPositivePower
      (cwPartitionedTensor K q) 1).trans
        (cwSquare_coarsening_isomorphic K q)
  exact (BorderRankLE.isomorphic hisomorphic).mp
    ((cwPartitionedTensor_borderRankLE K q).power 2)

end

end AlgebraicComplexity.Examples
