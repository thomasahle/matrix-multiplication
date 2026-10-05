/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinogradCompatibilityCoarseHashing
import AlgebraicComplexity.MatrixMultiplication.CoarsenedInterfaceSelection

/-!
# Total-weight quotient of CW complete-split words

The coarse alphabet used by CW hashing remembers only the total weight of a complete-split word.
This file exposes that map before restricting to native CW chunks and proves that digitwise
complement descends to the involution `t ↦ 2^(depth+1) - t` on totals.

The quotient is intentionally noninjective.  Coarsened constituents contain the sum of every
fine constituent in a total-weight fiber; no theorem below chooses or reconstructs a fine word
from its total.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor MoreAsymmetryCompatibility

universe u v

/-- A finite-feature labeling of complete-split words which remembers their total weight.
The feature map may collapse arbitrarily many words of the same total; injectivity is not part of
the interface. -/
structure CWTotalPreservingSplitMap (depth : ℕ) (Label : Type v) where
  label : SplitWord depth → Label
  total : Label → ℕ
  total_label : ∀ word, total (label word) = splitWordWeight word

namespace CWTotalPreservingSplitMap

/-- Apply a total-preserving split-word feature map to a native CW chunk. -/
def chunkLabel {Label : Type v} (feature : CWTotalPreservingSplitMap depth Label)
    (chunk : PositiveWord CWBlock (2 ^ depth - 1)) : Label :=
  feature.label (cwChunkSplitWord depth chunk)

@[simp] theorem total_chunkLabel {Label : Type v}
    (feature : CWTotalPreservingSplitMap depth Label)
    (chunk : PositiveWord CWBlock (2 ^ depth - 1)) :
    feature.total (feature.chunkLabel chunk) =
      splitWordWeight (cwChunkSplitWord depth chunk) :=
  feature.total_label _

/-- Legwise coarsening of the native CW chunk alphabet by independently supplied
total-preserving feature maps. -/
def chunkCoarsening {Label : Leg → Type v}
    (feature : ∀ c, CWTotalPreservingSplitMap depth (Label c)) :
    ∀ c, PositiveWord CWBlock (2 ^ depth - 1) → Label c :=
  fun c ↦ (feature c).chunkLabel

/-- The induced native-chunk map preserves total weight on every leg. -/
@[simp] theorem total_chunkCoarsening {Label : Leg → Type v}
    (feature : ∀ c, CWTotalPreservingSplitMap depth (Label c))
    (c : Leg) (chunk : PositiveWord CWBlock (2 ^ depth - 1)) :
    (feature c).total (chunkCoarsening feature c chunk) =
      splitWordWeight (cwChunkSplitWord depth chunk) :=
  (feature c).total_chunkLabel chunk

/-- A total-preserving feature quotient of native CW chunks leaves the represented tensor
unchanged.  Neither this statement nor `PartitionedTensor.coarsen` assumes that any feature map
is injective. -/
theorem chunkCoarsening_isomorphic
    {Label : Leg → Type v} [∀ c, Fintype (Label c)] [∀ c, DecidableEq (Label c)]
    (feature : ∀ c, CWTotalPreservingSplitMap depth (Label c))
    (K : Type u) [CommRing K] (q : ℕ) :
    Isomorphic (cwChunkPartitionedTensor K q depth).realize
      ((cwChunkPartitionedTensor K q depth).coarsen (chunkCoarsening feature)).realize :=
  Tensor.Isomorphic.partitionedCoarsen
    (cwChunkPartitionedTensor K q depth) (chunkCoarsening feature)

end CWTotalPreservingSplitMap

/-! ## The globally consistent length-two quotient used by the current candidate -/

/-- A two-digit split word, written in coordinate order. -/
def cwSplitPair (left right : SplitDigit) : SplitWord 1 :=
  ![left, right]

/-- Sort the two digits of a length-two split word.  Its fibers are exactly

* `01 ~ 10` at total one;
* `02 ~ 20`, with `11` separate, at total two; and
* `12 ~ 21` at total three.

Thus this is the fixed map encoded by the certificate specification
`2:1=0|0; 2:2=0|1|0; 2:3=0|0`, with singleton totals zero and four unchanged. -/
def cwSortedPairSplitWord (word : SplitWord 1) : SplitWord 1 :=
  cwSplitPair (min (word 0) (word 1)) (max (word 0) (word 1))

@[simp] theorem cwSortedPairSplitWord_pair (left right : SplitDigit) :
    cwSortedPairSplitWord (cwSplitPair left right) =
      cwSplitPair (min left right) (max left right) :=
  rfl

/-- Sorting the pair does not change its total digit weight. -/
theorem splitWordWeight_cwSortedPairSplitWord (word : SplitWord 1) :
    splitWordWeight (cwSortedPairSplitWord word) = splitWordWeight word := by
  by_cases h : word 0 ≤ word 1
  · simp [splitWordWeight, cwSortedPairSplitWord, cwSplitPair, h]
  · have h' : word 1 ≤ word 0 := le_of_not_ge h
    simp [splitWordWeight, cwSortedPairSplitWord, cwSplitPair, h', Nat.add_comm]

/-- The current candidate's fixed quotient as a total-preserving feature map. -/
def cwSortedPairSplitMap : CWTotalPreservingSplitMap 1 (SplitWord 1) where
  label := cwSortedPairSplitWord
  total := splitWordWeight
  total_label := splitWordWeight_cwSortedPairSplitWord

/-- The fixed pair quotient is genuinely noninjective (`01` and `10` collide). -/
theorem cwSortedPairSplitWord_not_injective :
    ¬ Function.Injective cwSortedPairSplitWord := by
  intro hinjective
  have heq : cwSplitPair (0 : SplitDigit) 1 = cwSplitPair 1 0 :=
    hinjective (by decide)
  have hne : cwSplitPair (0 : SplitDigit) 1 ≠ cwSplitPair 1 0 := by decide
  exact hne heq

/-- Use the same fixed pair-sorting quotient on all three tensor legs. -/
def cwSortedPairChunkFeatures :
    ∀ _c : Leg, CWTotalPreservingSplitMap 1 (SplitWord 1) :=
  fun _c ↦ cwSortedPairSplitMap

/-- Native length-two CW chunks mapped by the same fixed quotient on every leg. -/
def cwSortedPairChunkCoarsening :
    ∀ _c : Leg, PositiveWord CWBlock (2 ^ 1 - 1) → SplitWord 1 :=
  CWTotalPreservingSplitMap.chunkCoarsening cwSortedPairChunkFeatures

@[simp] theorem cwSortedPairChunkCoarsening_total (c : Leg)
    (chunk : PositiveWord CWBlock (2 ^ 1 - 1)) :
    splitWordWeight (cwSortedPairChunkCoarsening c chunk) =
      splitWordWeight (cwChunkSplitWord 1 chunk) :=
  CWTotalPreservingSplitMap.total_chunkCoarsening cwSortedPairChunkFeatures c chunk

/-- Tensor-level soundness of the globally consistent quotient used by the current numerical
candidate. -/
theorem cwSortedPairChunkCoarsening_isomorphic
    (K : Type u) [CommRing K] (q : ℕ) :
    Isomorphic (cwChunkPartitionedTensor K q 1).realize
      ((cwChunkPartitionedTensor K q 1).coarsen cwSortedPairChunkCoarsening).realize :=
  CWTotalPreservingSplitMap.chunkCoarsening_isomorphic
    cwSortedPairChunkFeatures K q

/-- Exact coarse multiplicity selection for a power of the current globally coarsened chunk
tensor.  This is the finite semantic bridge used before quotient-alphabet hashing and repair. -/
theorem power_cwSortedPairChunkCoarsen_selectPositiveTypes
    (K : Type u) [CommRing K] (q n : ℕ)
    (a : ∀ _c : Leg, SplitWord 1 → ℕ) :
    Restricts (Tensor.power (cwChunkPartitionedTensor K q 1).realize (n + 1))
      ((cwChunkPartitionedTensor K q 1).selectCoarsenedPositiveTypes
        cwSortedPairChunkCoarsening n a).realize :=
  Tensor.Restricts.power_selectCoarsenedPositiveTypes
    (cwChunkPartitionedTensor K q 1) cwSortedPairChunkCoarsening n a

/-- The total-weight quotient as a total-preserving split-word feature map. -/
def cwSplitWordTotalMap (depth : ℕ) :
    CWTotalPreservingSplitMap depth (CWCoarseDigit depth) where
  label := cwSplitWordTotalDigit depth
  total := fun digit ↦ digit.val
  total_label := fun _word ↦ rfl

/-- Legwise total-weight quotient for a partition whose native labels are complete-split words. -/
def cwSplitWordTotalCoarsening (depth : ℕ) :
    ∀ _c : Leg, SplitWord depth → CWCoarseDigit depth :=
  fun _c ↦ cwSplitWordTotalDigit depth

/-- The total quotient of a native CW chunk agrees definitionally with the coarse digit already
used by the hashing development. -/
@[simp] theorem cwSplitWordTotalDigit_cwChunkSplitWord (depth : ℕ)
    (chunk : PositiveWord CWBlock (2 ^ depth - 1)) :
    cwSplitWordTotalDigit depth (cwChunkSplitWord depth chunk) =
      cwChunkCoarseDigit depth chunk :=
  rfl

/-- Every split digit and its digitwise complement have total weight two. -/
theorem splitDigit_add_rev_val (digit : SplitDigit) :
    (digit : ℕ) + (Fin.rev digit : ℕ) = 2 := by
  simp only [Fin.val_rev]
  have hdigit := digit.isLt
  omega

/-- A complete-split word and its digitwise complement have the full legal coarse total. -/
theorem splitWordWeight_add_complementSplitWord {depth : ℕ}
    (word : SplitWord depth) :
    splitWordWeight word + splitWordWeight (complementSplitWord word) =
      coarseTotal depth := by
  classical
  unfold splitWordWeight complementSplitWord coarseTotal
  rw [← Finset.sum_add_distrib]
  simp_rw [splitDigit_add_rev_val]
  simp [pow_succ, Nat.mul_comm]

/-- Complementation acts on total weights by subtraction from the full coarse total. -/
theorem splitWordWeight_complementSplitWord {depth : ℕ}
    (word : SplitWord depth) :
    splitWordWeight (complementSplitWord word) =
      coarseTotal depth - splitWordWeight word := by
  have h := splitWordWeight_add_complementSplitWord word
  omega

/-- Complementation on the total-weight quotient. -/
def cwCoarseDigitComplement (depth : ℕ)
    (digit : CWCoarseDigit depth) : CWCoarseDigit depth :=
  ⟨coarseTotal depth - digit.val,
    Nat.lt_succ_iff.mpr (Nat.sub_le _ _)⟩

@[simp] theorem cwCoarseDigitComplement_val (depth : ℕ)
    (digit : CWCoarseDigit depth) :
    (cwCoarseDigitComplement depth digit : ℕ) = coarseTotal depth - digit.val :=
  rfl

/-- The coarse complement is an involution on all legal total digits. -/
@[simp] theorem cwCoarseDigitComplement_involutive (depth : ℕ)
    (digit : CWCoarseDigit depth) :
    cwCoarseDigitComplement depth (cwCoarseDigitComplement depth digit) = digit := by
  apply Fin.ext
  simp only [cwCoarseDigitComplement_val]
  have hdigit : digit.val ≤ coarseTotal depth := Nat.lt_succ_iff.mp digit.isLt
  omega

/-- Digitwise fine complementation descends exactly to coarse total complementation. -/
@[simp] theorem cwSplitWordTotalDigit_complement (depth : ℕ)
    (word : SplitWord depth) :
    cwSplitWordTotalDigit depth (complementSplitWord word) =
      cwCoarseDigitComplement depth (cwSplitWordTotalDigit depth word) := by
  apply Fin.ext
  exact splitWordWeight_complementSplitWord word

/-- Realization-level specialization of arbitrary finite coarsening to the CW total quotient. -/
theorem cwSplitWordTotalCoarsening_isomorphic
    {K : Type u} [CommSemiring K]
    {V : ∀ _c, SplitWord depth → Type v}
    [∀ c word, AddCommMonoid (V c word)]
    [∀ c word, Module K (V c word)]
    (P : PartitionedTensor (K := K) (A := fun _c ↦ SplitWord depth) V) :
    Isomorphic P.realize
      (P.coarsen (cwSplitWordTotalCoarsening depth)).realize :=
  Tensor.Isomorphic.partitionedCoarsen P (cwSplitWordTotalCoarsening depth)

/-! ## Explicit noninjectivity regression -/

/-- One depth-one split word with digits `(0,1)`. -/
def cwTotalCollisionLeft : SplitWord 1 :=
  fun position ↦ ⟨position.val, position.isLt.trans (by decide)⟩

/-- The distinct depth-one split word with digits `(1,0)`. -/
def cwTotalCollisionRight : SplitWord 1 :=
  fun position ↦ ⟨(Fin.rev position).val, (Fin.rev position).isLt.trans (by decide)⟩

theorem cwTotalCollisionLeft_ne_right :
    cwTotalCollisionLeft ≠ cwTotalCollisionRight := by
  intro h
  have hzero := congrFun h (0 : Fin 2)
  simp [cwTotalCollisionLeft, cwTotalCollisionRight] at hzero

/-- The total quotient is genuinely noninjective already at depth one. -/
theorem cwSplitWordTotalDigit_not_injective_depthOne :
    ¬ Function.Injective (cwSplitWordTotalDigit 1) := by
  intro hinjective
  apply cwTotalCollisionLeft_ne_right
  apply hinjective
  decide

end AlgebraicComplexity.Examples
