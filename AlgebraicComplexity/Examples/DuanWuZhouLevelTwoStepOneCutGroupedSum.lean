/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoStepOneCutHoles
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoPlainFineBridge
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoPlainGroupedStage

set_option autoImplicit false

/-!
# Additional Zeroing-Out Step 2, re-issued on the Step-1 cut

Layer 4 (`AlgebraicComplexity/Examples/`).  `[duan2023faster]`, section 6.1 `sec:global-algo`,
Additional Zeroing-Out **Step 2**, `papers/sources/2210.10173/global_value.tex:84-89`:

> In this step, we will zero out any small `Z`-block `Z_K̂ ∈ Z_K` such that `Z_K̂` is compatible
>  with more than one triple, or `Z_K̂` is not useful for the unique triple `(X_I, Y_J, Z_K)` that
> it
> is compatible with.  After such zeroing out, we call the obtained tensor `𝒯^{(2)}`.  We claim
>  `𝒯^{(2)} ≅ ⨁_{(X_I,Y_J,Z_K)} 𝒯^{(2)}|_{X_I,Y_J,Z_K}` due to the first zeroing-out rule
> here.
> (`:84-89`)

The tree already has this step on the **uncut** preimage ambient
(`Examples/DuanWuZhouLevelTwoPreimageGroupedSum.lean`, image 77).  That module is superseded by the
R1 repair and is neither edited nor imported here: the paper performs Step 2 on `𝒯^{(1)}`, the
tensor **after** Step 1 (`:72`), and running it on the uncut ambient is exactly what made the hole
family degree-determined.  This module re-issues it, as new definitions, on
`dwz63FineStepOneCut` (`Examples/DuanWuZhouLevelTwoStepOneKeep.lean`).

Nothing in the argument changes, because every engine it uses is parametric in the ambient:

* the compatibility relation is equality of the pivot label, which is sound with no hypothesis
  (`dwz63_isCompatibilitySound_selfLabel`, `Examples/DuanWuZhouLevelTwoPlainFineBridge.lean:111`);
* the `.Y` isolation is lossless and the `.X` leg reads the group for free
  (`dwz63PlainCoarseGroup_hasGroupUniqueLegFibers_x`,
  `Examples/DuanWuZhouLevelTwoPlainGroupedStage.lean:127`, and `…_y` at `:145`, whose only input
  is
  the cover `dwz63CutFineHcover`);
* the `.Z` isolation is the paper's first rule at `:86` --- "compatible with more than one triple"
  --- and it is what makes the direct-sum claim at `:89` true
  (`groupCompatibilityIsolatedSupport_hasGroupUniqueLegFibers`,
  `Tensor/GroupedCompatibilityZeroing.lean:111`);
* the direct sum itself is `PartitionedTensor.LegGrouping.restricts_groupedIndexedDirectSum`
  (`Tensor/PartitionedGrouping.lean:193`), which is `:89`.

The summands `((dwz63CutGrouping …).fiber a)` are the paper's `𝒯^{(2)}|_{X_I,Y_J,Z_K}`
(`:98-100`),
each a broken copy of `𝒯^*` with holes in its `Z`-variables; the holes are counted by image 145's
`dwz63CutReferenceHoles` and bounded by image 147.

Primary source `[duan2023faster]`: Ran Duan, Hongxun Wu and Renfei Zhou, *Faster Matrix
Multiplication via Asymmetric Hashing*, arXiv:2210.10173, section 6.1 `sec:global-algo`,
`papers/sources/2210.10173/global_value.tex:72, 84-89, 98-102`.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor

universe u

noncomputable section

variable {n : ℕ}
variable {retained : Finset (BlockAddress fun _ : Leg ↦ PositiveWord (Fin 5) n)}

/-! ## The cover, on the cut -/

/-- **Every address of `𝒯^{(1)}` lies over a retained triple.**

`global_value.tex:55` fixes a triple `(X_I, Y_J, Z_K)` and reads `S_{i,j,k}` off it; the cut is a
sub-object of the reachable preimage ambient, whose defining condition is that the coarse image is
retained, so the cover survives the cut verbatim.

Proof sketch: a selected address is a supported address of the preimage ambient
(`PartitionedTensor.mem_select_support`), and there the cover is `dwz63PreimageFine_hcover`. -/
theorem dwz63CutFineHcover (K : Type u) [CommRing K]
    (retained : Finset (BlockAddress fun _ : Leg ↦ PositiveWord (Fin 5) n))
    (a₀ : retained) (s : ℕ) :
    ∀ x ∈ (dwz63FineStepOneCut K n retained a₀ s).support, ∃ a : retained,
      ∀ c, (a : BlockAddress fun _ : Leg ↦ PositiveWord (Fin 5) n) c =
        positiveWordMap (cwSquareDegreeMap c) n (x c) := by
  intro x hx
  exact dwz63PreimageFine_hcover K n retained x
    ((PartitionedTensor.mem_select_support (dwz63PreimageFine K n retained)
      (dwz63FineStepOneKeep retained a₀ s) x).mp hx).1

/-! ## The two isolations (`global_value.tex:86`) -/

/-- The support of `𝒯^{(1)}` after the `.Y` self-label isolation.  Lossless; see the module
docstring. -/
def dwz63CutYSupport (K : Type u) [CommRing K]
    (retained : Finset (BlockAddress fun _ : Leg ↦ PositiveWord (Fin 5) n))
    (a₀ : retained) (s : ℕ) :
    Finset (BlockAddress fun _ : Leg ↦ PositiveWord (PositiveWord CWBlock 1) n) :=
  groupCompatibilityIsolatedSupport (dwz63FineStepOneCut K n retained a₀ s).support
    (dwz63PlainCoarseGroup retained (fun c ↦ positiveWordMap (cwSquareDegreeMap c) n) a₀) Leg.Y
    (fun label address ↦ address Leg.Y = label)

/-- The support after the `.Z` self-label isolation: **the first rule of Additional Zeroing-Out
Step 2** (`global_value.tex:86`), "`Z_K̂` is compatible with more than one triple", on
`𝒯^{(1)}`.
The `Z`-words it deletes are the holes of image 145's `dwz63CutReferenceHoles`. -/
def dwz63CutZSupport (K : Type u) [CommRing K]
    (retained : Finset (BlockAddress fun _ : Leg ↦ PositiveWord (Fin 5) n))
    (a₀ : retained) (s : ℕ) :
    Finset (BlockAddress fun _ : Leg ↦ PositiveWord (PositiveWord CWBlock 1) n) :=
  groupCompatibilityIsolatedSupport (dwz63CutYSupport K retained a₀ s)
    (dwz63PlainCoarseGroup retained (fun c ↦ positiveWordMap (cwSquareDegreeMap c) n) a₀) Leg.Z
    (fun label address ↦ address Leg.Z = label)

/-- **`𝒯^{(2)}`** (`global_value.tex:89`), at the section 6.3 instance and over the Step-1 cut.
-/
def dwz63CutIsolated (K : Type u) [CommRing K]
    (retained : Finset (BlockAddress fun _ : Leg ↦ PositiveWord (Fin 5) n))
    (a₀ : retained) (s : ℕ) :=
  (dwz63FineStepOneCut K n retained a₀ s).withSupport (dwz63CutZSupport K retained a₀ s)

/-- **Every leg reads the group on `𝒯^{(2)}`.**

This is what the paper's "due to the first zeroing-out rule here" (`global_value.tex:89`) asserts:
after the rule, a surviving small block belongs to one triple only, so the tensor splits.

Proof sketch: the `.X` leg reads the group with no hypothesis; the `.Y` leg reads it from the two
`InjOn` certificates through the cover; the `.Z` leg reads it because the isolation was performed
there.  Each is then restricted along the two support inclusions. -/
theorem dwz63_cutIsolated_hasGroupUniqueLegFibers (K : Type u) [CommRing K]
    (a₀ : retained) (s : ℕ)
    (hX : Set.InjOn (fun x : BlockAddress fun _ : Leg ↦ PositiveWord (Fin 5) n ↦ x .X)
      (retained : Set _))
    (hY : Set.InjOn (fun x : BlockAddress fun _ : Leg ↦ PositiveWord (Fin 5) n ↦ x .Y)
      (retained : Set _)) :
    ∀ pivot, HasGroupUniqueLegFibers (dwz63CutZSupport K retained a₀ s)
      (dwz63CutZSupport K retained a₀ s)
      (dwz63PlainCoarseGroup retained
        (fun c ↦ positiveWordMap (cwSquareDegreeMap c) n) a₀) pivot := by
  classical
  have hySubset : dwz63CutYSupport K retained a₀ s ⊆
      (dwz63FineStepOneCut K n retained a₀ s).support :=
    groupCompatibilityIsolatedSupport_subset _ _ _ _
  have hzSubset : dwz63CutZSupport K retained a₀ s ⊆ dwz63CutYSupport K retained a₀ s :=
    groupCompatibilityIsolatedSupport_subset _ _ _ _
  have hXa : HasGroupUniqueLegFibers (dwz63FineStepOneCut K n retained a₀ s).support
      (dwz63FineStepOneCut K n retained a₀ s).support
      (dwz63PlainCoarseGroup retained
        (fun c ↦ positiveWordMap (cwSquareDegreeMap c) n) a₀) Leg.X :=
    dwz63PlainCoarseGroup_hasGroupUniqueLegFibers_x retained
      (fun c ↦ positiveWordMap (cwSquareDegreeMap c) n) a₀ _
  have hYa : HasGroupUniqueLegFibers (dwz63FineStepOneCut K n retained a₀ s).support
      (dwz63FineStepOneCut K n retained a₀ s).support
      (dwz63PlainCoarseGroup retained
        (fun c ↦ positiveWordMap (cwSquareDegreeMap c) n) a₀) Leg.Y :=
    dwz63PlainCoarseGroup_hasGroupUniqueLegFibers_y hX hY
      (dwz63CutFineHcover K retained a₀ s)
  have hZa : HasGroupUniqueLegFibers (dwz63CutYSupport K retained a₀ s)
      (dwz63CutZSupport K retained a₀ s)
      (dwz63PlainCoarseGroup retained
        (fun c ↦ positiveWordMap (cwSquareDegreeMap c) n) a₀) Leg.Z :=
    groupCompatibilityIsolatedSupport_hasGroupUniqueLegFibers _ _ _ _
      (dwz63_isCompatibilitySound_selfLabel _ Leg.Z)
  intro pivot
  cases pivot with
  | X => exact ((hXa.restrictToSubset hySubset).restrictToSubset hzSubset).toSelf
  | Y => exact ((hYa.restrictToSubset hySubset).restrictToSubset hzSubset).toSelf
  | Z => exact hZa.toSelf

/-- The explicit grouping of `𝒯^{(2)}` by retained triple (`global_value.tex:89`). -/
def dwz63CutGrouping (K : Type u) [CommRing K] (a₀ : retained) (s : ℕ)
    (hX : Set.InjOn (fun x : BlockAddress fun _ : Leg ↦ PositiveWord (Fin 5) n ↦ x .X)
      (retained : Set _))
    (hY : Set.InjOn (fun x : BlockAddress fun _ : Leg ↦ PositiveWord (Fin 5) n ↦ x .Y)
      (retained : Set _)) :
    (dwz63CutIsolated K retained a₀ s).LegGrouping retained :=
  PartitionedTensor.LegGrouping.ofGroupUnique (dwz63CutIsolated K retained a₀ s)
    (dwz63PlainCoarseGroup retained (fun c ↦ positiveWordMap (cwSquareDegreeMap c) n) a₀) a₀
    (dwz63_cutIsolated_hasGroupUniqueLegFibers K a₀ s hX hY)

/-- **`𝒯^{(1)} ⊵ ⨁_{(X_I,Y_J,Z_K)} 𝒯^{(2)}|_{X_I,Y_J,Z_K}`** (`global_value.tex:89`).

Additional Zeroing-Out Step 2 performed on `𝒯^{(1)}`, and the direct-sum claim it licenses.  The
hash's two `InjOn` certificates are the only inputs; the hole family is not a parameter, it is what
the `.Z` isolation deletes.

Proof sketch: two applications of `Restricts.partitionedGroupCompatibilityIsolated`
(`Tensor/GroupedCompatibilityZeroing.lean:158`), at `.Y` and then `.Z`, composed with
`LegGrouping.restricts_groupedIndexedDirectSum`. -/
theorem dwz63_stepOneCut_restricts_groupedDirectSum (K : Type u) [CommRing K]
    (a₀ : retained) (s : ℕ)
    (hX : Set.InjOn (fun x : BlockAddress fun _ : Leg ↦ PositiveWord (Fin 5) n ↦ x .X)
      (retained : Set _))
    (hY : Set.InjOn (fun x : BlockAddress fun _ : Leg ↦ PositiveWord (Fin 5) n ↦ x .Y)
      (retained : Set _)) :
    Restricts (dwz63FineStepOneCut K n retained a₀ s).realize
      (Tensor.indexedDirectSum
        (V := PartitionedTensor.LegGrouping.GroupAmbientFamily
          (K := K)
          (V := PositivePowerBlockSpace K
            (PositivePowerBlockSpace K (CWPartitionBlockSpace K dwz63Q) 1) n)
          (Γ := retained))
        fun a ↦ ((dwz63CutGrouping K a₀ s hX hY).fiber a).realize) := by
  classical
  have hy : Restricts (dwz63FineStepOneCut K n retained a₀ s).realize
      ((dwz63FineStepOneCut K n retained a₀ s).withSupport
        (dwz63CutYSupport K retained a₀ s)).realize :=
    Tensor.Restricts.partitionedGroupCompatibilityIsolated _ _ Leg.Y _
      (dwz63_isCompatibilitySound_selfLabel _ Leg.Y)
  have hz : Restricts
      ((dwz63FineStepOneCut K n retained a₀ s).withSupport
        (dwz63CutYSupport K retained a₀ s)).realize
      (dwz63CutIsolated K retained a₀ s).realize :=
    Tensor.Restricts.partitionedGroupCompatibilityIsolated _ _ Leg.Z _
      (dwz63_isCompatibilitySound_selfLabel _ Leg.Z)
  exact (hy.trans hz).trans
    (dwz63CutGrouping K a₀ s hX hY).restricts_groupedIndexedDirectSum

end

end AlgebraicComplexity.Examples
