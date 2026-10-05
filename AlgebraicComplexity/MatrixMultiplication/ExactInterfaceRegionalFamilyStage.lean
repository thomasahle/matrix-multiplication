/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.ExactInterfaceDivisionStage
import AlgebraicComplexity.MatrixMultiplication.ExactInterfaceRegionalFamily

/-!
# Checked leaf stages following an exact regional family

`ExactInterfaceRegionalFamily.toDivisionTree` computes a division tree from a binary family of
regional terms.  A certificate client must populate leaf stages in precisely the same dependent
tree shape.  This module makes that alignment structural: `ExactInterfaceRegionalFamily.Stages`
mirrors the regional family, stores one local stage at each leaf, and compiles to the ordinary
`ExactInterfaceTermDivisionTree.LeafStages` consumed by the tensor fold.

The conventional six-region constructor is included as a small client.  It records the six stages
in the same parenthesization as `ExactInterfaceRegionalFamily.six`; no equality cast or traversal
index is needed.
-/

namespace AlgebraicComplexity

open Tensor

universe u v w z

namespace ExactInterfaceRegionalFamily

variable (K : Type u) [CommSemiring K]
variable {depth : ℕ} {index : LevelConstituentIndex depth}
variable {A : Leg → Type w} [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]
variable {V : ∀ c, A c → Type (max u v)}
variable [∀ c a, AddCommMonoid (V c a)] [∀ c a, Module K (V c a)]

/-- A regional family with one locally checked exact division stage at every leaf.

The branch constructor stores only its two staged child families.  It has no tensor-semantic
field for their external product. -/
inductive Stages
    (P : PartitionedTensor (K := K) (A := A) V)
    (encode : ∀ c, A c → SplitWord depth) :
    (family : ExactInterfaceRegionalFamily index) → Type (max (max u v) (max w (z + 1))) where
  | leaf (regionalLeaf : ExactInterfaceRegionalLeaf index)
      (stage : ExactInterfaceTermDivisionTree.LeafStages.{u, v, w, z} K P encode
        (.leaf regionalLeaf.multiplicityCase)) :
      Stages P encode (.leaf regionalLeaf)
  | branch {left right : ExactInterfaceRegionalFamily index}
      (leftStages : Stages P encode left)
      (rightStages : Stages P encode right) :
      Stages P encode (.branch left right)

namespace Stages

/-- Compile the structurally matching regional stages to the division-tree stages used by the
exact tensor fold. -/
noncomputable def toDivisionTreeLeafStages
    {P : PartitionedTensor (K := K) (A := A) V}
    {encode : ∀ c, A c → SplitWord depth} :
    {family : ExactInterfaceRegionalFamily index} →
      ExactInterfaceRegionalFamily.Stages.{u, v, w, z} K P encode family →
      ExactInterfaceTermDivisionTree.LeafStages.{u, v, w, z} K P encode
        family.toDivisionTree
  | _, .leaf _regionalLeaf stage => stage
  | _, .branch leftStages rightStages =>
      .branch (branchDivision _ _) (toDivisionTreeLeafStages leftStages)
        (toDivisionTreeLeafStages rightStages)

/-- The six conventional regional leaves, with their stages forced into the same balanced binary
shape as `ExactInterfaceRegionalFamily.six`. -/
noncomputable def six
    {P : PartitionedTensor (K := K) (A := A) V}
    {encode : ∀ c, A c → SplitWord depth}
    (r₁ r₂ r₃ r₄ r₅ r₆ : ExactInterfaceRegionalLeaf index)
    (s₁ : ExactInterfaceTermDivisionTree.LeafStages.{u, v, w, z} K P encode
      (.leaf r₁.multiplicityCase))
    (s₂ : ExactInterfaceTermDivisionTree.LeafStages.{u, v, w, z} K P encode
      (.leaf r₂.multiplicityCase))
    (s₃ : ExactInterfaceTermDivisionTree.LeafStages.{u, v, w, z} K P encode
      (.leaf r₃.multiplicityCase))
    (s₄ : ExactInterfaceTermDivisionTree.LeafStages.{u, v, w, z} K P encode
      (.leaf r₄.multiplicityCase))
    (s₅ : ExactInterfaceTermDivisionTree.LeafStages.{u, v, w, z} K P encode
      (.leaf r₅.multiplicityCase))
    (s₆ : ExactInterfaceTermDivisionTree.LeafStages.{u, v, w, z} K P encode
      (.leaf r₆.multiplicityCase)) :
    ExactInterfaceRegionalFamily.Stages.{u, v, w, z} K P encode
      (ExactInterfaceRegionalFamily.six
        (.leaf r₁) (.leaf r₂) (.leaf r₃) (.leaf r₄) (.leaf r₅) (.leaf r₆)) :=
  .branch
    (.branch (.leaf r₁ s₁) (.branch (.leaf r₂ s₂) (.leaf r₃ s₃)))
    (.branch (.leaf r₄ s₄) (.branch (.leaf r₅ s₅) (.leaf r₆ s₆)))

end Stages
end ExactInterfaceRegionalFamily

end AlgebraicComplexity
