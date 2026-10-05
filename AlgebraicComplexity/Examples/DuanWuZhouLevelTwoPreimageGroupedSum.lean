/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoPreimageAmbient
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoPlainGroupedStage
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoPlainFineBridge

set_option autoImplicit false

/-!
# The grouped direct sum on the reachable ambient, with no hole hypotheses

On a *box* ambient the self-label group isolation is degenerate: a crossed address sharing a
`Y`-label deletes its uncrossed partner, and the surviving support is empty.  That is what refuted
the `.Y`-isolation assembly.

On `dwz63PreimageFine` it is neither degenerate nor unsound, and both facts are free:

* **Sound**, because equality of the pivot label is always a sound compatibility relation
  (`dwz63_isCompatibilitySound_selfLabel`, no hypothesis).
* **Lossless at `.Y`**, because two supported addresses sharing a fine `Y`-word share its coarse
  image's `Y`-word, and the retained family is `Y`-injective, so they have the *same* group and
  nothing is deleted.
* **Exactly Step 2 at `.Z`**, because coarse `Z`-blocks are deliberately shared, so the fine
  `Z`-words compatible with two retained triples are precisely what is removed.

So the whole grouped direct sum needs only the hash's two `InjOn` certificates.  `usefulFor`,
`compatibleWith`, `hholes` and `hambient` disappear: the hole set is not a parameter, it is the
set of `Z`-words the isolation deletes.

`[DuanWuZhou2022]`, `global_value.tex:74-89`.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor

universe u

noncomputable section

variable {n : ℕ}
variable {retained : Finset (BlockAddress fun _ : Leg ↦ PositiveWord (Fin 5) n)}

/-- The support after the `.Y` self-label isolation. -/
noncomputable def dwz63PreimageYSupport (K : Type u) [CommRing K]
    (retained : Finset (BlockAddress fun _ : Leg ↦ PositiveWord (Fin 5) n))
    (a₀ : retained) : Finset (BlockAddress fun _ : Leg ↦ PositiveWord (PositiveWord CWBlock 1) n) :=
  groupCompatibilityIsolatedSupport (dwz63PreimageFine K n retained).support
    (dwz63PlainCoarseGroup retained (fun c ↦ positiveWordMap (cwSquareDegreeMap c) n) a₀) Leg.Y
    (fun label address ↦ address Leg.Y = label)

/-- The support after the `.Z` self-label isolation --- Additional Zeroing-Out Step 2. -/
noncomputable def dwz63PreimageZSupport (K : Type u) [CommRing K]
    (retained : Finset (BlockAddress fun _ : Leg ↦ PositiveWord (Fin 5) n))
    (a₀ : retained) : Finset (BlockAddress fun _ : Leg ↦ PositiveWord (PositiveWord CWBlock 1) n) :=
  groupCompatibilityIsolatedSupport (dwz63PreimageYSupport K retained a₀)
    (dwz63PlainCoarseGroup retained (fun c ↦ positiveWordMap (cwSquareDegreeMap c) n) a₀) Leg.Z
    (fun label address ↦ address Leg.Z = label)

/-- The isolated ambient. -/
noncomputable def dwz63PreimageIsolated (K : Type u) [CommRing K]
    (retained : Finset (BlockAddress fun _ : Leg ↦ PositiveWord (Fin 5) n))
    (a₀ : retained) :=
  (dwz63PreimageFine K n retained).withSupport (dwz63PreimageZSupport K retained a₀)

/-- **Every leg reads the group on the isolated ambient.** -/
theorem dwz63_preimageIsolated_hasGroupUniqueLegFibers (K : Type u) [CommRing K]
    (a₀ : retained)
    (hX : Set.InjOn (fun s : BlockAddress fun _ : Leg ↦ PositiveWord (Fin 5) n ↦ s .X)
      (retained : Set _))
    (hY : Set.InjOn (fun s : BlockAddress fun _ : Leg ↦ PositiveWord (Fin 5) n ↦ s .Y)
      (retained : Set _)) :
    ∀ pivot, HasGroupUniqueLegFibers (dwz63PreimageZSupport K retained a₀)
      (dwz63PreimageZSupport K retained a₀)
      (dwz63PlainCoarseGroup retained (fun c ↦ positiveWordMap (cwSquareDegreeMap c) n) a₀) pivot := by
  classical
  set group := dwz63PlainCoarseGroup retained (fun c ↦ positiveWordMap (cwSquareDegreeMap c) n) a₀ with hgroup
  have hySubset : dwz63PreimageYSupport K retained a₀ ⊆
      (dwz63PreimageFine K n retained).support :=
    groupCompatibilityIsolatedSupport_subset _ _ _ _
  have hzSubset : dwz63PreimageZSupport K retained a₀ ⊆
      dwz63PreimageYSupport K retained a₀ :=
    groupCompatibilityIsolatedSupport_subset _ _ _ _
  have hXa : HasGroupUniqueLegFibers (dwz63PreimageFine K n retained).support
      (dwz63PreimageFine K n retained).support group Leg.X :=
    dwz63PlainCoarseGroup_hasGroupUniqueLegFibers_x retained (fun c ↦ positiveWordMap (cwSquareDegreeMap c) n) a₀ _
  have hYa : HasGroupUniqueLegFibers (dwz63PreimageFine K n retained).support
      (dwz63PreimageFine K n retained).support group Leg.Y :=
    dwz63PlainCoarseGroup_hasGroupUniqueLegFibers_y hX hY
      (dwz63PreimageFine_hcover K n retained)
  have hZa : HasGroupUniqueLegFibers (dwz63PreimageYSupport K retained a₀)
      (dwz63PreimageZSupport K retained a₀) group Leg.Z :=
    groupCompatibilityIsolatedSupport_hasGroupUniqueLegFibers _ _ _ _
      (dwz63_isCompatibilitySound_selfLabel _ Leg.Z)
  intro pivot
  cases pivot with
  | X => exact ((hXa.restrictToSubset hySubset).restrictToSubset hzSubset).toSelf
  | Y => exact ((hYa.restrictToSubset hySubset).restrictToSubset hzSubset).toSelf
  | Z => exact hZa.toSelf

/-- The explicit grouping of the isolated ambient. -/
noncomputable def dwz63PreimageGrouping (K : Type u) [CommRing K]
    (a₀ : retained)
    (hX : Set.InjOn (fun s : BlockAddress fun _ : Leg ↦ PositiveWord (Fin 5) n ↦ s .X)
      (retained : Set _))
    (hY : Set.InjOn (fun s : BlockAddress fun _ : Leg ↦ PositiveWord (Fin 5) n ↦ s .Y)
      (retained : Set _)) :
    (dwz63PreimageIsolated K retained a₀).LegGrouping retained :=
  PartitionedTensor.LegGrouping.ofGroupUnique (dwz63PreimageIsolated K retained a₀)
    (dwz63PlainCoarseGroup retained (fun c ↦ positiveWordMap (cwSquareDegreeMap c) n) a₀) a₀
    (dwz63_preimageIsolated_hasGroupUniqueLegFibers K a₀ hX hY)

/-- **The grouped direct sum on the reachable ambient.**

The hash's two `InjOn` certificates are the only inputs.  No hole set, no `usefulFor`, no
`compatibleWith`, no `hambient`. -/
theorem dwz63_preimageFine_restricts_groupedDirectSum (K : Type u) [CommRing K]
    (a₀ : retained)
    (hX : Set.InjOn (fun s : BlockAddress fun _ : Leg ↦ PositiveWord (Fin 5) n ↦ s .X)
      (retained : Set _))
    (hY : Set.InjOn (fun s : BlockAddress fun _ : Leg ↦ PositiveWord (Fin 5) n ↦ s .Y)
      (retained : Set _)) :
    Restricts (dwz63PreimageFine K n retained).realize
      (Tensor.indexedDirectSum
        (V := PartitionedTensor.LegGrouping.GroupAmbientFamily
          (K := K)
          (V := PositivePowerBlockSpace K
            (PositivePowerBlockSpace K (CWPartitionBlockSpace K dwz63Q) 1) n)
          (Γ := retained))
        fun a ↦ ((dwz63PreimageGrouping K a₀ hX hY).fiber a).realize) := by
  classical
  have hy : Restricts (dwz63PreimageFine K n retained).realize
      ((dwz63PreimageFine K n retained).withSupport
        (dwz63PreimageYSupport K retained a₀)).realize :=
    Tensor.Restricts.partitionedGroupCompatibilityIsolated _ _ Leg.Y _
      (dwz63_isCompatibilitySound_selfLabel _ Leg.Y)
  have hz : Restricts
      ((dwz63PreimageFine K n retained).withSupport
        (dwz63PreimageYSupport K retained a₀)).realize
      (dwz63PreimageIsolated K retained a₀).realize :=
    Tensor.Restricts.partitionedGroupCompatibilityIsolated _ _ Leg.Z _
      (dwz63_isCompatibilitySound_selfLabel _ Leg.Z)
  exact (hy.trans hz).trans
    (dwz63PreimageGrouping K a₀ hX hY).restricts_groupedIndexedDirectSum

end

end AlgebraicComplexity.Examples
