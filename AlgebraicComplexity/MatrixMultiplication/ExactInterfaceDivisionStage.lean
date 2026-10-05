/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.InterfaceTensorRegionalDivisionFamily
import AlgebraicComplexity.MatrixMultiplication.WholeConstituentLaserVolumeAssembly

/-!
# Whole-stage assembly over exact interface-division trees

An `ExactInterfaceTermDivisionTree` already proves that one source power restricts to the
recursively parenthesized external product of all its selected leaves.  A later extraction should
therefore provide one `WholeConstituentLaserVolumeStage` at each leaf and derive the assembled
source restriction from that theorem; it should never accept a restriction of the complete leaf
product as a new hypothesis.

This module supplies that anti-laundering constructor.  `Packed` hides only the four natural-number
outputs of a finite stage.  `ExactInterfaceTermDivisionTree.LeafStages` mirrors a division tree and
stores one packed stage at each leaf.  Its two interpretations first fold the stages by the exact
external-product law and then precompose with the proved regional-division restriction from the
source power.

Nothing here is specific to a tensor family, a region orientation, or a certificate.
-/

namespace AlgebraicComplexity

open Tensor

universe u v w z

namespace WholeConstituentLaserVolumeStage

/-- A finite whole-constituent stage with its copy count and three rectangular dimensions bundled.

The source remains an explicit index of the structure.  Thus packing existential output sizes does
not hide or assume a tensor restriction. -/
structure Packed (K : Type u) [CommSemiring K]
    {Source : Leg → Type v} [∀ c, AddCommMonoid (Source c)] [∀ c, Module K (Source c)]
    (source : Tensor3 K Source) where
  copies : ℕ
  xSize : ℕ
  ySize : ℕ
  zSize : ℕ
  stage : WholeConstituentLaserVolumeStage.{u, v, z} K source copies xSize ySize zSize

namespace Packed

/-- Transport a packed stage backwards through a proved exact source restriction. -/
noncomputable def precompose
    (K : Type u) [CommSemiring K]
    {V : Leg → Type v} [∀ c, AddCommMonoid (V c)] [∀ c, Module K (V c)]
    {W : Leg → Type w} [∀ c, AddCommMonoid (W c)] [∀ c, Module K (W c)]
    {source : Tensor3 K V} {newSource : Tensor3 K W}
    (hsource : Restricts newSource source)
    (packed : Packed.{u, v, z} K source) : Packed.{u, w, z} K newSource where
  copies := packed.copies
  xSize := packed.xSize
  ySize := packed.ySize
  zSize := packed.zSize
  stage := WholeConstituentLaserVolumeStage.precompose K hsource packed.stage

/-- Externally multiply two packed stages.  Copy counts and all three dimensions multiply
exactly. -/
noncomputable def external
    (K : Type u) [CommSemiring K]
    {V : Leg → Type v} [∀ c, AddCommMonoid (V c)] [∀ c, Module K (V c)]
    {W : Leg → Type w} [∀ c, AddCommMonoid (W c)] [∀ c, Module K (W c)]
    {leftSource : Tensor3 K V} {rightSource : Tensor3 K W}
    (left : Packed.{u, v, z} K leftSource)
    (right : Packed.{u, w, z} K rightSource) :
    Packed.{u, max v w, z} K (Tensor.external leftSource rightSource) where
  copies := left.copies * right.copies
  xSize := left.xSize * right.xSize
  ySize := left.ySize * right.ySize
  zSize := left.zSize * right.zSize
  stage := WholeConstituentLaserVolumeStage.external K left.stage right.stage

end Packed
end WholeConstituentLaserVolumeStage

namespace ExactInterfaceTermDivisionTree

variable (K : Type u) [CommSemiring K]
variable {depth : ℕ}
variable {A : Leg → Type w} [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]
variable {V : ∀ c, A c → Type (max u v)}
variable [∀ c a, AddCommMonoid (V c a)] [∀ c a, Module K (V c a)]

/-- A division tree equipped with one whole-constituent stage at every selected leaf.

The constructor shape is deliberately the same as `ExactInterfaceTermDivisionTree`.  In
particular, a branch stores only its two recursively checked children; it has no field for a
restriction of their assembled external product. -/
inductive LeafStages
    (P : PartitionedTensor (K := K) (A := A) V)
    (encode : ∀ c, A c → SplitWord depth) :
    {term : ExactInterfaceTermParameters depth} →
      ExactInterfaceTermDivisionTree term →
      Type (max (max u v) (max w (z + 1))) where
  | leaf {term : ExactInterfaceTermParameters depth}
      (multiplicityCase : ExactInterfaceTermMultiplicityCase term)
      (packed : WholeConstituentLaserVolumeStage.Packed.{u, max u (max v w), z} K
        (P.exactInterfaceTermPowerRestriction encode multiplicityCase).target) :
      LeafStages P encode (.leaf multiplicityCase)
  | branch {parent : ExactInterfaceTermParameters depth}
      (division : ExactInterfaceTermBinaryDivision parent)
      {left : ExactInterfaceTermDivisionTree division.leftTerm}
      {right : ExactInterfaceTermDivisionTree division.rightTerm}
      (leftStages : LeafStages P encode left)
      (rightStages : LeafStages P encode right) :
      LeafStages P encode (.branch division left right)

namespace LeafStages

/-- Fold all checked leaf stages into one stage on the exact external product represented by the
division tree. -/
noncomputable def toPacked
    {P : PartitionedTensor (K := K) (A := A) V}
    {encode : ∀ c, A c → SplitWord depth}
    {term : ExactInterfaceTermParameters depth}
    {tree : ExactInterfaceTermDivisionTree term}
    (stages : LeafStages.{u, v, w, z} K P encode tree) :
    WholeConstituentLaserVolumeStage.Packed.{u, max u (max v w), z} K
      (tree.leafPowerRestriction P encode).target := by
  induction stages with
  | leaf multiplicityCase packed =>
      exact packed
  | branch division leftStages rightStages leftPacked rightPacked =>
      exact WholeConstituentLaserVolumeStage.Packed.external K leftPacked rightPacked

/-- **Exact division-tree stage assembly from the original source power.**

The only source transformation used here is
`Tensor.Restricts.power_exactInterfaceTermDivisionTree`; all remaining work is the lossless fold of
the explicitly supplied leaf stages. -/
noncomputable def toPowerPacked
    {P : PartitionedTensor (K := K) (A := A) V}
    {encode : ∀ c, A c → SplitWord depth}
    {term : ExactInterfaceTermParameters depth}
    {tree : ExactInterfaceTermDivisionTree term}
    (stages : LeafStages.{u, v, w, z} K P encode tree) :
    WholeConstituentLaserVolumeStage.Packed.{u, max u (max v w), z} K
      (Tensor.power P.realize term.multiplicity) :=
  WholeConstituentLaserVolumeStage.Packed.precompose K
    (Tensor.Restricts.power_exactInterfaceTermDivisionTree P encode tree)
    stages.toPacked

end LeafStages
end ExactInterfaceTermDivisionTree

end AlgebraicComplexity
