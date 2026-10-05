/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.WholeConstituentLaserVolume
import AlgebraicComplexity.Tensor.LocalizedCoarsenedSelection

set_option autoImplicit false

/-!
# One coarse constituent as a whole-constituent laser-volume stage

`Tensor/LocalizedCoarsenedSelection.lean` proves that a single constituent of a coarsened
partitioned tensor restricts to the *whole* fine subfamily in its coarse fiber cut by an arbitrary
legwise predicate (`Restricts.coarsen_constituent_to_fineFiberSelect`), and that this localized
family is exactly one Cartesian box of the original fine partition
(`PartitionedTensor.coarseningFiber_select_eq_box`).  Every aggregate-hashing wrapper in the
library then wants the *same* composite: given an inner matrix-multiplication extraction of that
box, package the coarse constituent as a `WholeConstituentLaserVolumeStage`, whose `inner`
callback the wrapper consumes once per selected address.

This module states that composite once.  The inner extraction is a callback, so nothing here
depends on how the box is degenerated --- a rational typed leaf, a segmented leaf, a hole repair
--- and nothing depends on which hashing family selected `target`.  The only hypotheses are that
`target` is supported after coarsening and that the inner index type has the advertised
cardinality; both index type and copy count are carried exactly, never estimated.

Existing instances of this composite that were written out by hand are
`Examples/CoppersmithWinogradTotalWeightSelectedTermMarkedLeafStage.lean`'s
`cwSelectedExactInterfaceTerm_presentFixedCell_wholeStage_ofMarkedLeaf` (whole selected term
rather than one constituent) and, in the `[duan2023faster]` route,
`Examples/DuanWuZhouLevelTwoGroupedLeaf.lean`'s
`dwz63_brokenGroup_restricts_brokenReferenceLeaf` followed by its stage packaging.

`[CoppersmithWinograd1990]`, `[duan2023faster]`.
-/

namespace AlgebraicComplexity

open Tensor

universe u v w x z

variable {K : Type u} [CommSemiring K]
variable {A : Leg → Type w} {B : Leg → Type x}
variable [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]
variable [∀ c, Fintype (B c)] [∀ c, DecidableEq (B c)]
variable {V : ∀ c, A c → Type (max u v)}
variable [∀ c a, AddCommMonoid (V c a)] [∀ c a, Module K (V c a)]

/-- **A supported coarse constituent, with an inner extraction of its localized box, is a whole
constituent stage.**

`target` is supported in `P.coarsen f`, so its constituent restricts to the realization of the
entire fine fiber over `target` cut by `keep`; that localized family is the single box
`P.box (coarseningFiberSelectParts f target keep)`.  Composing with any exact inner extraction of
that box gives the stage, carrying the inner index type `I` unchanged and its cardinality as the
copy count.

This is the `inner` callback of the aggregate directional wrappers in
`MatrixMultiplication/AggregateMarkedDirectional*WholeInnerStage.lean`, instantiated at
`P := (fine tensor).coarsen f` and one selected address. -/
def Tensor.Restricts.coarsen_constituent_wholeInnerStage
    {I : Type z} [Fintype I]
    (P : PartitionedTensor (K := K) (A := A) V)
    (f : ∀ c, A c → B c) (target : BlockAddress B)
    (htarget : target ∈ (P.coarsen f).support)
    (keep : ∀ c, A c → Prop) [∀ c a, Decidable (keep c a)]
    (innerCopies xSize ySize zSize : ℕ)
    (hcard : Fintype.card I = innerCopies)
    (inner : Restricts
      (P.box (coarseningFiberSelectParts f target keep)).realize
      (Tensor.indexedDirectSum
        (fun _ : I ↦ matrixMultiplication (K := K) xSize ySize zSize))) :
    WholeConstituentLaserVolumeStage K ((P.coarsen f).constituent target)
      innerCopies xSize ySize zSize where
  I := I
  card_I := hcard
  source_restricts := by
    have hfiber : Restricts ((P.coarsen f).constituent target)
        ((P.coarseningFiber f target).select keep).realize :=
      Tensor.Restricts.coarsen_constituent_to_fineFiberSelect P f target htarget keep
    rw [PartitionedTensor.coarseningFiber_select_eq_box] at hfiber
    exact hfiber.trans inner

end AlgebraicComplexity
