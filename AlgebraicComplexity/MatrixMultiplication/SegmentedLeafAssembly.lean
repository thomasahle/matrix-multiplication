/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.ExternalProduct
import AlgebraicComplexity.Tensor.PartitionedPower

/-!
# Factorwise assembly of consecutive typed-leaf segments

Aggregate hashing treats several consecutive source-word regions as one long hashing word.  The
semantic certificate for such a word must be derived from certificates for the individual
regions; assuming the desired degeneration of the already concatenated constituent would merely
hide the assembly theorem.

This module proves the required paper-independent bridge.  Polynomial degenerations of two (or
four) consecutive supported constituent words assemble to the matrix-multiplication tensor whose
three dimensions are the corresponding products.  The only hypotheses are the segmentwise
degenerations.  Concatenation and reassociation are supplied by the canonical partitioned-power
isomorphisms.
-/

namespace AlgebraicComplexity

open Tensor

universe u v w

namespace Tensor.PolynomialDegenerates

variable {K : Type u} [CommSemiring K]
variable {A : Leg → Type w} [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]
variable {V : ∀ c, A c → Type (max u v)}
variable [∀ c a, AddCommMonoid (V c a)] [∀ c a, Module K (V c a)]

/-- Assemble two consecutive supported-word constituents from their separate semantic leaf
certificates.  In particular, no degeneration of the concatenated constituent is assumed. -/
theorem positiveSupportWordTensor_append_matrixMultiplication
    (P : PartitionedTensor (K := K) (A := A) V)
    {n m : ℕ} (left : PositiveWord P.support n) (right : PositiveWord P.support m)
    {leftX leftY leftZ rightX rightY rightZ : ℕ}
    (hleft : PolynomialDegenerates (P.positiveSupportWordTensor n left)
      (matrixMultiplication (K := K) leftX leftY leftZ))
    (hright : PolynomialDegenerates (P.positiveSupportWordTensor m right)
      (matrixMultiplication (K := K) rightX rightY rightZ)) :
    PolynomialDegenerates
      (P.positiveSupportWordTensor (n + m + 1)
        (positiveWordAppend left m right))
      (matrixMultiplication (K := K)
        (leftX * rightX) (leftY * rightY) (leftZ * rightZ)) := by
  have hsplit : PolynomialDegenerates
      (P.positiveSupportWordTensor (n + m + 1)
        (positiveWordAppend left m right))
      (Tensor.external
        (P.positiveSupportWordTensor n left)
        (P.positiveSupportWordTensor m right)) :=
    PolynomialDegenerates.of_restricts
      (PartitionedTensor.Isomorphic.positiveSupportWordTensor_append
        P left right).symm.restricts
  exact hsplit.trans <|
    (hleft.external hright).trans <|
      PolynomialDegenerates.of_restricts
        (Tensor.Isomorphic.matrixMultiplication_externalProduct
          (K := K) leftX leftY leftZ rightX rightY rightZ).restricts

/-- A local semantic certificate for one nonempty consecutive source-word segment.  The dependent
source tensor is hidden inside the record, allowing heterogeneous segment lengths and rectangular
dimensions to be folded without casts in downstream certificate code. -/
structure SegmentedLeafCertificate
    (P : PartitionedTensor (K := K) (A := A) V) where
  depth : ℕ
  word : PositiveWord P.support depth
  xSize : ℕ
  ySize : ℕ
  zSize : ℕ
  degenerates : PolynomialDegenerates (P.positiveSupportWordTensor depth word)
    (matrixMultiplication (K := K) xSize ySize zSize)

namespace SegmentedLeafCertificate

/-- Concatenate two local segment certificates.  The proof is constructed by the canonical word
reassociation and tensor-product laws, so the result contains no aggregate semantic assumption. -/
def append
    {P : PartitionedTensor (K := K) (A := A) V}
    (left right : SegmentedLeafCertificate P) : SegmentedLeafCertificate P where
  depth := left.depth + right.depth + 1
  word := positiveWordAppend left.word right.depth right.word
  xSize := left.xSize * right.xSize
  ySize := left.ySize * right.ySize
  zSize := left.zSize * right.zSize
  degenerates := positiveSupportWordTensor_append_matrixMultiplication
    P left.word right.word left.degenerates right.degenerates

@[simp] theorem append_depth
    {P : PartitionedTensor (K := K) (A := A) V}
    (left right : SegmentedLeafCertificate P) :
    (left.append right).depth = left.depth + right.depth + 1 := rfl

@[simp] theorem append_xSize
    {P : PartitionedTensor (K := K) (A := A) V}
    (left right : SegmentedLeafCertificate P) :
    (left.append right).xSize = left.xSize * right.xSize := rfl

@[simp] theorem append_ySize
    {P : PartitionedTensor (K := K) (A := A) V}
    (left right : SegmentedLeafCertificate P) :
    (left.append right).ySize = left.ySize * right.ySize := rfl

@[simp] theorem append_zSize
    {P : PartitionedTensor (K := K) (A := A) V}
    (left right : SegmentedLeafCertificate P) :
    (left.append right).zSize = left.zSize * right.zSize := rfl

/-- Left-associated assembly of an arbitrary finite tail of local segment certificates.  Starting
from one head segment makes nonemptiness explicit and avoids a fictitious empty tensor factor. -/
def appendList
    {P : PartitionedTensor (K := K) (A := A) V} :
    SegmentedLeafCertificate P → List (SegmentedLeafCertificate P) →
      SegmentedLeafCertificate P
  | head, [] => head
  | head, next :: tail => appendList (head.append next) tail

@[simp] theorem appendList_nil
    {P : PartitionedTensor (K := K) (A := A) V}
    (head : SegmentedLeafCertificate P) : head.appendList [] = head := rfl

@[simp] theorem appendList_cons
    {P : PartitionedTensor (K := K) (A := A) V}
    (head next : SegmentedLeafCertificate P)
    (tail : List (SegmentedLeafCertificate P)) :
    head.appendList (next :: tail) = (head.append next).appendList tail := rfl

/-- The assembled word length is the sum of the nonempty segment lengths. -/
theorem appendList_depth_add_one
    {P : PartitionedTensor (K := K) (A := A) V}
    (head : SegmentedLeafCertificate P)
    (tail : List (SegmentedLeafCertificate P)) :
    (head.appendList tail).depth + 1 =
      (head.depth + 1) + (tail.map fun segment ↦ segment.depth + 1).sum := by
  induction tail generalizing head with
  | nil => simp
  | cons next tail ih =>
      rw [appendList_cons, ih]
      simp only [append_depth, List.map_cons, List.sum_cons]
      omega

/-- The assembled `X` dimension is the left fold of the local `X` dimensions. -/
theorem appendList_xSize
    {P : PartitionedTensor (K := K) (A := A) V}
    (head : SegmentedLeafCertificate P)
    (tail : List (SegmentedLeafCertificate P)) :
    (head.appendList tail).xSize =
      tail.foldl (fun value segment ↦ value * segment.xSize) head.xSize := by
  induction tail generalizing head with
  | nil => rfl
  | cons next tail ih => exact ih (head.append next)

/-- The assembled `Y` dimension is the left fold of the local `Y` dimensions. -/
theorem appendList_ySize
    {P : PartitionedTensor (K := K) (A := A) V}
    (head : SegmentedLeafCertificate P)
    (tail : List (SegmentedLeafCertificate P)) :
    (head.appendList tail).ySize =
      tail.foldl (fun value segment ↦ value * segment.ySize) head.ySize := by
  induction tail generalizing head with
  | nil => rfl
  | cons next tail ih => exact ih (head.append next)

/-- The assembled `Z` dimension is the left fold of the local `Z` dimensions. -/
theorem appendList_zSize
    {P : PartitionedTensor (K := K) (A := A) V}
    (head : SegmentedLeafCertificate P)
    (tail : List (SegmentedLeafCertificate P)) :
    (head.appendList tail).zSize =
      tail.foldl (fun value segment ↦ value * segment.zSize) head.zSize := by
  induction tail generalizing head with
  | nil => rfl
  | cons next tail ih => exact ih (head.append next)

/-- Read an assembled segment certificate as a constituent of any definitionally equal positive
power.  The only transport is the canonical cast of the word-length index. -/
theorem positivePower_constituent
    {P : PartitionedTensor (K := K) (A := A) V}
    (certificate : SegmentedLeafCertificate P)
    {totalDepth : ℕ} (hdepth : certificate.depth = totalDepth) :
    PolynomialDegenerates
      ((P.positivePower totalDepth).constituent
        (positiveSupportWordBlockAddress P.support totalDepth
          (positiveWordCast hdepth certificate.word)))
      (matrixMultiplication (K := K)
        certificate.xSize certificate.ySize certificate.zSize) := by
  rw [P.positivePower_constituent_positiveSupportWordBlockAddress]
  exact (PolynomialDegenerates.of_restricts
    (PartitionedTensor.Isomorphic.positiveSupportWordTensor_cast
      P hdepth certificate.word).restricts).trans certificate.degenerates

/-- Address-and-dimension form consumed by aggregate hashing stages.  All hypotheses are finite
structural equalities; the semantic degeneration remains the one constructed from local segment
certificates. -/
theorem positivePower_constituent_at_address
    {P : PartitionedTensor (K := K) (A := A) V}
    (certificate : SegmentedLeafCertificate P)
    {totalDepth xSize ySize zSize : ℕ}
    (hdepth : certificate.depth = totalDepth)
    (address : BlockAddress (fun c ↦ PositiveWord (A c) totalDepth))
    (haddress : address = positiveSupportWordBlockAddress P.support totalDepth
      (positiveWordCast hdepth certificate.word))
    (hx : certificate.xSize = xSize)
    (hy : certificate.ySize = ySize)
    (hz : certificate.zSize = zSize) :
    PolynomialDegenerates ((P.positivePower totalDepth).constituent address)
      (matrixMultiplication (K := K) xSize ySize zSize) := by
  subst address
  subst xSize
  subst ySize
  subst zSize
  exact certificate.positivePower_constituent hdepth

end SegmentedLeafCertificate

end Tensor.PolynomialDegenerates

end AlgebraicComplexity
