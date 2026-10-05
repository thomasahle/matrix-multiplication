/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinogradChunkPartitionCore
import AlgebraicComplexity.MatrixMultiplication.PositiveWordProductCore
import AlgebraicComplexity.Tensor.PartitionedPowerSupportDecodeRecursive

/-!
# Canonical dimensions of Coppersmith--Winograd chunk constituents

A chunk address in a positive power determines a supported word of base CW addresses.  This
module recovers such a word and defines each chunk dimension as the product of the corresponding
base dimensions.  It contains only finite support and dimension bookkeeping.

The tensor restriction to the resulting matrix-multiplication tensor and the rational typed-leaf
adapter remain in `CoppersmithWinogradChunkTypedLeaf`.  Keeping them separate lets exact
zero-coordinate clients use the canonical dimensions without importing the entropy, hashing, and
hole-repair stack.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor

universe u

/-- Products along positive words preserve strict positivity. -/
theorem positiveWordProduct_pos_of_forall
    {I : Type u} (dimension : I → ℕ) (hpositive : ∀ i, 0 < dimension i)
    (r : ℕ) (word : PositiveWord I r) :
    0 < positiveWordProduct dimension r word :=
  AlgebraicComplexity.positiveWordProduct_pos_of_forall dimension hpositive r word

/-- Purely finite matrix-dimension table attached to a CW block address.  Its fallback value is
irrelevant because all clients below restrict the address to `cwBlockSupport`. -/
abbrev cwBlockMatrixDimensions (q : ℕ) (address : CWBlockAddress) : ℕ × ℕ × ℕ :=
  match address .X, address .Y, address .Z with
  | .zero, .middle, .middle => (1, 1, q)
  | .middle, .zero, .middle => (q, 1, 1)
  | .middle, .middle, .zero => (1, q, 1)
  | _, _, _ => (1, 1, 1)

/-- Canonical rectangular matrix dimension of one supported base CW constituent on one leg. -/
def cwBaseConstituentDimension (q : ℕ) (support : cwBlockSupport) : Leg → ℕ
  | .X => (cwBlockMatrixDimensions q support.1).1
  | .Y => (cwBlockMatrixDimensions q support.1).2.1
  | .Z => (cwBlockMatrixDimensions q support.1).2.2

@[simp] theorem cwBaseConstituentDimension_X (q : ℕ) (support : cwBlockSupport) :
    cwBaseConstituentDimension q support .X = (cwBlockMatrixDimensions q support.1).1 :=
  rfl

@[simp] theorem cwBaseConstituentDimension_Y (q : ℕ) (support : cwBlockSupport) :
    cwBaseConstituentDimension q support .Y = (cwBlockMatrixDimensions q support.1).2.1 :=
  rfl

@[simp] theorem cwBaseConstituentDimension_Z (q : ℕ) (support : cwBlockSupport) :
    cwBaseConstituentDimension q support .Z = (cwBlockMatrixDimensions q support.1).2.2 :=
  rfl

theorem cwBaseConstituentDimension_pos (q : ℕ) (hq : 0 < q)
    (support : cwBlockSupport) (c : Leg) :
    0 < cwBaseConstituentDimension q support c := by
  rcases support with ⟨address, haddress⟩
  simp only [cwBlockSupport, Finset.mem_insert, Finset.mem_singleton] at haddress
  rcases haddress with rfl | rfl | rfl | rfl | rfl | rfl <;>
    cases c <;>
    simp [cwBaseConstituentDimension, cwBlockMatrixDimensions, hq,
      cw200, cw020, cw002, cw011, cw101, cw110, cwBlockAddress]

/-- Recover the supported base-CW word underlying a chunk constituent address. -/
noncomputable def cwChunkSupportedWordOfAddress
    (K : Type u) [CommRing K] (q depth : ℕ)
    (support : (cwChunkPartitionedTensor K q depth).support) :
    PositiveWord (cwPartitionedTensor K q).support (2 ^ depth - 1) :=
  (cwPartitionedTensor K q).positiveSupportWordOfAddress (2 ^ depth - 1) support

/-- Transposing the recovered base word returns the original chunk address. -/
theorem positiveSupportWordBlockAddress_cwChunkSupportedWordOfAddress
    (K : Type u) [CommRing K] (q depth : ℕ)
    (support : (cwChunkPartitionedTensor K q depth).support) :
    positiveSupportWordBlockAddress (cwPartitionedTensor K q).support
        (2 ^ depth - 1)
        (cwChunkSupportedWordOfAddress K q depth support) = support.1 :=
  (cwPartitionedTensor K q).positiveSupportWordBlockAddress_positiveSupportWordOfAddress
    (2 ^ depth - 1) support

/-- Canonical dimension of a chunk constituent: multiply the corresponding base CW dimensions
over all `2^depth` letters in the recovered support word. -/
noncomputable def cwChunkConstituentDimension
    (K : Type u) [CommRing K] (q depth : ℕ)
    (support : (cwChunkPartitionedTensor K q depth).support) (c : Leg) : ℕ :=
  positiveWordProduct (fun s ↦ cwBaseConstituentDimension q s c)
    (2 ^ depth - 1) (cwChunkSupportedWordOfAddress K q depth support)

@[simp] theorem cwChunkConstituentDimension_X
    (K : Type u) [CommRing K] (q depth : ℕ)
    (support : (cwChunkPartitionedTensor K q depth).support) :
    cwChunkConstituentDimension K q depth support .X =
      positiveWordProduct (fun s ↦ (cwBlockMatrixDimensions q s.1).1)
        (2 ^ depth - 1) (cwChunkSupportedWordOfAddress K q depth support) :=
  rfl

@[simp] theorem cwChunkConstituentDimension_Y
    (K : Type u) [CommRing K] (q depth : ℕ)
    (support : (cwChunkPartitionedTensor K q depth).support) :
    cwChunkConstituentDimension K q depth support .Y =
      positiveWordProduct (fun s ↦ (cwBlockMatrixDimensions q s.1).2.1)
        (2 ^ depth - 1) (cwChunkSupportedWordOfAddress K q depth support) :=
  rfl

@[simp] theorem cwChunkConstituentDimension_Z
    (K : Type u) [CommRing K] (q depth : ℕ)
    (support : (cwChunkPartitionedTensor K q depth).support) :
    cwChunkConstituentDimension K q depth support .Z =
      positiveWordProduct (fun s ↦ (cwBlockMatrixDimensions q s.1).2.2)
        (2 ^ depth - 1) (cwChunkSupportedWordOfAddress K q depth support) :=
  rfl

theorem cwChunkConstituentDimension_pos
    (K : Type u) [CommRing K] (q depth : ℕ) (hq : 0 < q)
    (support : (cwChunkPartitionedTensor K q depth).support) (c : Leg) :
    0 < cwChunkConstituentDimension K q depth support c := by
  exact positiveWordProduct_pos_of_forall
    (fun s ↦ cwBaseConstituentDimension q s c)
    (fun s ↦ cwBaseConstituentDimension_pos q hq s c)
    (2 ^ depth - 1) (cwChunkSupportedWordOfAddress K q depth support)

end AlgebraicComplexity.Examples
