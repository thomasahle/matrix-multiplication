/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.UniformPowerSelection
import AlgebraicComplexity.MatrixMultiplication.CTensorOneSliceExtraction

/-!
# Fusing a uniform-local-power family into one merged leaf

`UniformPowerSelection` produces a sub-family of a shared-leg selected family on which the local
`q`-power exponent is constant.  `CTensorOneSliceFusion` fuses `h` copies of `⟨1, d, 1⟩` sharing
one `Z` block into the single tensor `⟨1, h * d, 1⟩`.  This module is the join: at a uniform
exponent `k` the fused dimension `h * q ^ k` is *literally* the merged dimension
`ZeroCoordinateMerge.mergedDimension q ones fibre`, so the whole retained type class — cardinality
included — enters one matrix dimension, and the result is in the shape
`WholeConstituentLaserVolumeStage` consumes.

## Leg convention

All statements are in Lean's `(X, Y, Z)` leg order, and the merged type-class dimension lands on
the **`Y`** leg: the fused tensor is `⟨1, mergedDimension, 1⟩`, matching
`CTensor.partitioned_oneSliceMatrixMultiplication_isomorphic` and
`ZeroCoordinateMerge.mergeY`.  The certificate's own volume coordinate `c` is the
Coppersmith--Winograd matrix-shape slot `(c + 2) mod 3` (`better_bound/r4_scoping/OBLIGATIONS.md`
§9.1), so a client pairing these statements with a certificate row must rotate; nothing here
depends on that rotation.

## What is assumed and what is proved

The C-tensor retyping `C` and the pointwise identification `htarget` of its constituents with the
canonical one-slice tensor are *inputs*: they are the shared-`Z` coherence that a zero-coordinate
client supplies.  Everything downstream of them — the fusion, the identification of `h * q ^ k`
with the merged dimension, the sub-family degeneration and the stage packaging — is proved here.
No Coppersmith--Winograd constant and no certificate datum occurs.
-/

namespace AlgebraicComplexity

open Tensor

universe u v w z

namespace CTensor.FiberRetyping

section Labels

variable {K : Type u} [CommSemiring K]
variable {A : Leg → Type w} [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]
variable {V : ∀ c, A c → Type v}
variable [∀ c a, AddCommMonoid (V c a)] [∀ c a, Module K (V c a)]
variable {X Y Z : Type v}
variable [AddCommMonoid X] [Module K X]
variable [AddCommMonoid Y] [Module K Y]
variable [AddCommMonoid Z] [Module K Z]

/-- Every C-tensor index of a fibre retyping names a genuinely selected source address.  This is
what lets a client discharge the pointwise constituent identity `htarget` by a hypothesis
quantified over selected *addresses* rather than over the enumeration. -/
theorem sourceAddress_mem
    {P : PartitionedTensor (K := K) (A := A) V}
    {selected : Finset (BlockAddress A)} {h : ℕ}
    (C : FiberRetyping (X := X) (Y := Y) (Z := Z) P selected h) (i : Fin h) :
    C.sourceAddress i ∈ selected := by
  have hmem : C.sourceAddress i ∈ Finset.univ.map
      (fiberAddressEmbedding C.xLabel C.yLabel C.zLabel C.x_injective) :=
    Finset.mem_map.mpr ⟨i, Finset.mem_univ i, rfl⟩
  exact (Finset.ext_iff.mp C.selected_eq (C.sourceAddress i)).mpr hmem

/-- The legwise map into the canonical one-slice constituent space at one address of a shared-`Z`
fibre: `X` and `Y` maps depending only on the address's block label, together with one map shared
by every constituent on the common `Z` block.  Sharing the `Z` map is not a convenience — a
C-tensor cannot apply different linear maps to the same source variable in different summands. -/
noncomputable def oneSliceLabelConstituentMap {d : ℕ} {zLabel : A .Z}
    (xMap : ∀ a : A .X, V .X a →ₗ[K] MMSpace K 1 d 1 .X)
    (yMap : ∀ a : A .Y, V .Y a →ₗ[K] MMSpace K 1 d 1 .Y)
    (zMap : V .Z zLabel →ₗ[K] MMSpace K 1 d 1 .Z)
    (x : A .X) (y : A .Y) : ∀ c,
      V c (Tensor.ofLegs x y zLabel c) →ₗ[K]
        CTensor.ConstituentSpace (MMSpace K 1 d 1 .X) (MMSpace K 1 d 1 .Y)
          (MMSpace K 1 d 1 .Z) c
  | .X => xMap x
  | .Y => yMap y
  | .Z => zMap

end Labels

end CTensor.FiberRetyping

namespace UniformPowerSelection

section Fusion

variable {K : Type u} [CommSemiring K]
variable {A : Leg → Type w} [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]
variable {V : ∀ c, A c → Type u}
variable [∀ c a, AddCommMonoid (V c a)] [∀ c a, Module K (V c a)]

/-- **Uniform local power, fused.**  A shared-`Z` fibre of uniform local `q`-power `q ^ k`,
retyped as a C-tensor whose constituents are all the canonical one-slice tensor `⟨1, q ^ k, 1⟩`,
restricts to the single matrix-multiplication tensor `⟨1, mergedDimension q ones fibre, 1⟩`.

This is the point at which the exact type class contributes its **cardinality** to a matrix
dimension instead of being discarded in favour of one representative. -/
theorem restricts_matrixMultiplication_mergedDimension
    {P : PartitionedTensor (K := K) (A := A) V}
    {fibre : Finset (BlockAddress A)} {ones : BlockAddress A → ℕ} {q k : ℕ}
    (huniform : ∀ address ∈ fibre, ones address = k)
    (C : CTensor.FiberRetyping
      (X := MMSpace K 1 (q ^ k) 1 .X)
      (Y := MMSpace K 1 (q ^ k) 1 .Y)
      (Z := MMSpace K 1 (q ^ k) 1 .Z)
      P fibre fibre.card)
    (htarget : ∀ i, C.targetConstituent i = CTensor.oneSliceConstituent K (q ^ k)) :
    Restricts (P.withSupport fibre).realize
      (matrixMultiplication (K := K) 1
        (ZeroCoordinateMerge.mergedDimension q ones fibre) 1) := by
  rw [ZeroCoordinateMerge.mergedDimension_of_uniform q ones fibre huniform]
  exact C.restricts_oneSliceMatrixMultiplication htarget

/-- Full-support form of `restricts_matrixMultiplication_mergedDimension`: when the whole selected
family already has a uniform local power — which is what exact complete-split consistency
delivers, see `outerChunkStatistic_eq_of_mem_selectEncodedExactInterfaceTerm_support` — no
sub-family is taken and no loss is paid. -/
theorem restricts_matrixMultiplication_mergedDimension_of_support
    {P : PartitionedTensor (K := K) (A := A) V}
    {ones : BlockAddress A → ℕ} {q k : ℕ}
    (huniform : ∀ address ∈ P.support, ones address = k)
    (C : CTensor.FiberRetyping
      (X := MMSpace K 1 (q ^ k) 1 .X)
      (Y := MMSpace K 1 (q ^ k) 1 .Y)
      (Z := MMSpace K 1 (q ^ k) 1 .Z)
      P P.support P.support.card)
    (htarget : ∀ i, C.targetConstituent i = CTensor.oneSliceConstituent K (q ^ k)) :
    Restricts P.realize
      (matrixMultiplication (K := K) 1
        (ZeroCoordinateMerge.mergedDimension q ones P.support) 1) := by
  rw [ZeroCoordinateMerge.mergedDimension_of_uniform q ones P.support huniform]
  exact C.restricts_oneSliceMatrixMultiplication_of_support htarget

/-- The merged one-slice **stage**: one whole-constituent laser-volume stage with a single copy
and rectangular dimensions `⟨1, mergedDimension, 1⟩` (Lean leg order).  This is the object
`WholeConstituentLaserVolumeStage.external` multiplies into an assembly, so a merged zero-block
factor is absorbed by `ZeroCoordinateMerge.mergeY` with no further tensor algebra. -/
noncomputable def mergedOneSliceStage
    {P : PartitionedTensor (K := K) (A := A) V}
    {fibre : Finset (BlockAddress A)} {ones : BlockAddress A → ℕ} {q k : ℕ}
    (huniform : ∀ address ∈ fibre, ones address = k)
    (C : CTensor.FiberRetyping
      (X := MMSpace K 1 (q ^ k) 1 .X)
      (Y := MMSpace K 1 (q ^ k) 1 .Y)
      (Z := MMSpace K 1 (q ^ k) 1 .Z)
      P fibre fibre.card)
    (htarget : ∀ i, C.targetConstituent i = CTensor.oneSliceConstituent K (q ^ k)) :
    WholeConstituentLaserVolumeStage.{u, max u w, z} K (P.withSupport fibre).realize 1 1
      (ZeroCoordinateMerge.mergedDimension q ones fibre) 1 :=
  ZeroCoordinateMerge.stageOfRestricts K
    (restricts_matrixMultiplication_mergedDimension huniform C htarget)

/-- **Item 4, in one statement.**  A shared-leg selected family whose members carry *varying*
local `q`-powers, each bounded by `chunkBound` on each of the `n + 1` outer samples, has a
sub-family on which the power is uniform, such that

* the sub-family's merged dimension is within the named subexponential factor
  `uniformPowerLoss chunkBound n` of the whole family's merged dimension, and
* the whole family degenerates to the single matrix-multiplication tensor
  `⟨1, mergedDimension of the sub-family, 1⟩`.

The retyping family `retyping` and its pointwise identification `htarget` are the shared-`Z`
coherence input; the injectivity `hx` of the `X` labels — already proved for zero-coordinate
interfaces — is what makes the sub-family a degeneration rather than a deletion. -/
theorem exists_uniform_power_fibre_restricts_mergedDimension
    (P : PartitionedTensor (K := K) (A := A) V)
    (ones : BlockAddress A → ℕ) (q chunkBound n : ℕ)
    (hbound : ∀ address ∈ P.support, ones address ≤ chunkBound * (n + 1))
    (hx : Set.InjOn (fun address ↦ address .X) (P.support : Set (BlockAddress A)))
    (retyping : ∀ k : ℕ, CTensor.FiberRetyping
      (X := MMSpace K 1 (q ^ k) 1 .X)
      (Y := MMSpace K 1 (q ^ k) 1 .Y)
      (Z := MMSpace K 1 (q ^ k) 1 .Z)
      P (P.support.filter fun address ↦ ones address = k)
        (P.support.filter fun address ↦ ones address = k).card)
    (htarget : ∀ k i,
      (retyping k).targetConstituent i = CTensor.oneSliceConstituent K (q ^ k)) :
    ∃ k ≤ chunkBound * (n + 1),
      ((ZeroCoordinateMerge.mergedDimension q ones P.support : ℕ) : ℝ) ≤
          uniformPowerLoss chunkBound n *
            ((ZeroCoordinateMerge.mergedDimension q ones
              (P.support.filter fun address ↦ ones address = k) : ℕ) : ℝ) ∧
        Restricts P.realize
          (matrixMultiplication (K := K) 1
            (ZeroCoordinateMerge.mergedDimension q ones
              (P.support.filter fun address ↦ ones address = k)) 1) := by
  classical
  obtain ⟨k, hk, huniform, hfibre⟩ :=
    exists_uniform_power_fibre q ones P.support chunkBound n hbound
  have hmerged : ZeroCoordinateMerge.mergedDimension q ones
      (P.support.filter fun address ↦ ones address = k) =
      (P.support.filter fun address ↦ ones address = k).card * q ^ k :=
    ZeroCoordinateMerge.mergedDimension_of_uniform q ones _ huniform
  refine ⟨k, hk, ?_, ?_⟩
  · unfold uniformPowerLoss
    rw [hmerged]
    exact_mod_cast hfibre
  · exact (restricts_withSupport_of_injOn_x P (Finset.filter_subset _ _) hx).trans
      (restricts_matrixMultiplication_mergedDimension huniform (retyping k) (htarget k))

end Fusion

end UniformPowerSelection

end AlgebraicComplexity
