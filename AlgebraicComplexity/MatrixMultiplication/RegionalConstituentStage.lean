/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Tensor.PartitionedProductConstituent
import AlgebraicComplexity.MatrixMultiplication.WholeConstituentLaserVolumeAssembly

set_option autoImplicit false

/-!
# Regional constituent stages of a partitioned external product

Layer 3 (`AlgebraicComplexity/MatrixMultiplication/`).  An aggregate extraction whose source is a
*regional product* needs one whole-constituent stage per constituent of the assembled partitioned
tensor.  This module supplies exactly that, one region boundary at a time.

`WholeConstituentLaserVolumeStage.external`
(`MatrixMultiplication/WholeConstituentLaserVolumeAssembly.lean`) already multiplies copy counts
and all three rectangular dimensions exactly, but it speaks about
`Tensor.external leftSource rightSource`.  `PartitionedTensor.constituent_external`
(`Tensor/PartitionedProductConstituent.lean`) identifies that tensor with
`(P.external Q).constituent q`.  Composing the two gives `externalConstituent`: from a stage for
`P`'s constituent at the left half of a paired block address and a stage for `Q`'s constituent at
the right half, a stage for the product's constituent at the paired address, with

`copies₁ * copies₂` copies and dimensions `x₁ * x₂`, `y₁ * y₂`, `z₁ * z₂`.

## Why this is binary, and why that is enough

This is the type an aggregate whole-inner theorem asks of its `inner` callback at a product block
index.  Several regions are multiplied in one at a time: three regions are two applications, `n`
regions are `n - 1`, left-associated.  No `n`-ary partitioned product is ever named, which is what
keeps the whole tensor calculus — `Tensor.external`, `Isomorphic.matrixMultiplication_external`,
`Isomorphic.external_indexedDirectSum` — usable at every step.  An `n`-ary product indexed by a
`Fintype` of regions would need an `n`-ary tensor product of the regional block spaces, a
different algebraic object from the binary one on which all of those laws are stated.  The same
verdict is reached, for the same reason, by the segmented-division lane's
`MatrixMultiplication/SegmentedLocalizedDivisionIterated.lean`, which iterates the *law* rather
than naming the iterated tensor.

The mirror facts about the assembled product are already committed:
`PartitionedTensor.mem_external_support` and `card_external_support`
(`Tensor/PartitionedProductCore.lean`) describe its support, and
`map_partitionExternalEquiv_external_realize` (`Tensor/PartitionedProductRealization.lean`)
identifies its realization with the external product of the regional realizations.
-/

namespace AlgebraicComplexity

open Tensor

universe u v w x y

namespace WholeConstituentLaserVolumeStage

variable (K : Type u) [CommSemiring K]
variable {A : Leg → Type w} [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]
variable {B : Leg → Type x} [∀ c, Fintype (B c)] [∀ c, DecidableEq (B c)]
variable {V : ∀ c, A c → Type v}
variable [∀ c a, AddCommMonoid (V c a)] [∀ c a, Module K (V c a)]
variable {W : ∀ c, B c → Type y}
variable [∀ c b, AddCommMonoid (W c b)] [∀ c b, Module K (W c b)]

/-- **One region boundary of a regional product.**

Given a whole-constituent stage for each factor's constituent at its half of a paired block
address, the product's constituent at that address carries a whole-constituent stage whose copy
count and three rectangular dimensions are the products of the factors'.

This is `WholeConstituentLaserVolumeStage.external` read through
`PartitionedTensor.constituent_external`; the two sources are definitionally the same tensor, so
no transport is needed. -/
noncomputable def externalConstituent
    (P : PartitionedTensor (K := K) (A := A) V)
    (Q : PartitionedTensor (K := K) (A := B) W)
    (q : BlockAddress (ProductBlockIndex A B))
    {leftCopies leftX leftY leftZ : ℕ}
    {rightCopies rightX rightY rightZ : ℕ}
    (left : WholeConstituentLaserVolumeStage K (P.constituent fun c ↦ (q c).1)
      leftCopies leftX leftY leftZ)
    (right : WholeConstituentLaserVolumeStage K (Q.constituent fun c ↦ (q c).2)
      rightCopies rightX rightY rightZ) :
    WholeConstituentLaserVolumeStage K ((P.external Q).constituent q)
      (leftCopies * rightCopies) (leftX * rightX) (leftY * rightY) (leftZ * rightZ) :=
  WholeConstituentLaserVolumeStage.external K left right

/-- The output index of `externalConstituent` is the pair index, so its copy count really is the
product of the two regional copy counts.  Recorded because the aggregate wrapper flattens copy
counts and a client should be able to see the arithmetic without unfolding. -/
theorem card_I_externalConstituent
    (P : PartitionedTensor (K := K) (A := A) V)
    (Q : PartitionedTensor (K := K) (A := B) W)
    (q : BlockAddress (ProductBlockIndex A B))
    {leftCopies leftX leftY leftZ : ℕ}
    {rightCopies rightX rightY rightZ : ℕ}
    (left : WholeConstituentLaserVolumeStage K (P.constituent fun c ↦ (q c).1)
      leftCopies leftX leftY leftZ)
    (right : WholeConstituentLaserVolumeStage K (Q.constituent fun c ↦ (q c).2)
      rightCopies rightX rightY rightZ) :
    letI := (externalConstituent K P Q q left right).fintypeI
    Fintype.card (externalConstituent K P Q q left right).I = leftCopies * rightCopies :=
  (externalConstituent K P Q q left right).card_I

end WholeConstituentLaserVolumeStage

end AlgebraicComplexity
