/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinogradChunkPartitionCore
import AlgebraicComplexity.Examples.CoppersmithWinogradSplitWordCore
import MatrixMultiplication.CertificateDerivedPerTreeForestBudget

set_option autoImplicit false

/-!
# The remaining forest obligation of the `ω < 2.36999` endpoint, named

The milestone's stage hypothesis is an eventual whole-constituent family on
`Tensor.power (coppersmithWinograd K 5) 8`.  Committed source already carries the whole conduit
from a chunk-division *forest* to that family:
`AlgebraicComplexity.Examples.cwDepthThreeEventualDivisionForestStageData_toCWPowerEight` transports
an `EventualExactInterfaceDivisionForestStageData` on `cwChunkPartitionedTensor K 5 3` along the
canonical chunk isomorphism, and
`CertificateDerivedForestVolumeBudget.eventualForestStageData_of_meetsBudget` builds that record
from a forest, its multiplicity equation and its per-leaf budgets.

What committed source does **not** carry is any *value* of that record — nor of
`ExactInterfaceTermDivisionTree.Staged` at a CW chunk, nor of an
`EventualExactInterfaceDivisionForestStageData` anywhere.  Every module that mentions one takes it
as a hypothesis.  This module is the honest terminus of that chain: it states, as one explicit
argument list at exactly the endpoint's type, everything a producer still owes.

## What this module derives

Given the arguments below, the endpoint record is *built*, not assumed.  In particular the nominal
volume growth, the aggregate certificate volume rate, the volume-side subexponential loss, and the
two base positivity facts are all discharged inside
`CertificateDerivedPerTreeForestBudget.eventualForestStageData_of_treeProducts` and the committed
forest fold.  Feeding the result to the depth-three transport yields the milestone's stage hypothesis with
no coercion.

## What a producer still owes, and why it is genuinely open

The `forest` argument is the obstruction, and it is not a matter of effort.  A staged tree is a term,
a division tree and a `LeafStages`; the first two are combinatorics, but every leaf of the third
carries a `WholeConstituentLaserVolumeStage.Packed` on the selected constituent.  In committed
source the only closed leaves are degenerate: `LeafStages.zero` is unconditional but `1 × 1 × 1`,
and `cwSelectedExactInterfaceTerm_zero_nativeLeafStage` has real side lengths but requires a leg
with no constituent letters.  Every route to a volume-carrying interior leaf runs through
`LeafStages.ofNonempty` fed by a CW compatibility-cleanup theorem, and each of those still carries
an undischarged box restriction onto a matrix multiplication.  That restriction, and the counting
that selects the addresses, is the laser-method content the endpoint is waiting on.

`hbudget` is the second genuinely open input: `MeetsBudget` has no decision procedure, and at a
positive-multiplicity leaf it is the semantic inequality
`2 ^ (multiplicity · certificateWordVolumeBits) ≤ xSize · ySize · zSize`.

Nothing here asserts a tensor extraction, support exhaustiveness or optimizer optimality.
-/

namespace MatrixMultiplication.CoppersmithWinogradDepthThreeForestResiduals

open AlgebraicComplexity
open AlgebraicComplexity.Examples
open AlgebraicComplexity.Tensor
open MatrixMultiplication.CertificateDerivedLeafVolumeBudget
open MatrixMultiplication.CertificateDerivedForestVolumeBudget
open MatrixMultiplication.CertificateDerivedPerTreeForestBudget
open MatrixMultiplication.SimplifiedSequencePackaging (strideValue)

universe u

/-- **The endpoint's forest record, from the named residual inputs.**

At `blockPower = 1` and stride `38` on one depth-three CW₅ chunk per block, this is the exact
argument list a producer still owes: past a cutoff, a nonempty forest of checked staged
division trees per repetition, its exact multiplicity equation `= 1 * (38 * r)`, a subexponential
positive copy loss, the forest's copy growth at the product of its per-tree copy counts, and its
per-leaf volume budgets against the committed certificate rates.

The forest is left general on purpose: the endpoint's mass-`19` profile selects four *distinct*
chunk classes with multiplicities `9, 5, 2, 3`, so a constructor that repeated a single tree would
be the wrong shape for it.

The result is the record accepted verbatim by
`cwDepthThreeEventualDivisionForestStageData_toCWPowerEight`, whose output is in turn the stage
hypothesis of the committed endpoint composition. -/
noncomputable def cwDepthThreeForestStageData
    (K : Type u) [CommRing K]
    {copyBase : ℝ} (hcopyBase : 0 < copyBase)
    (cutoff rootCount : ℕ)
    (forest : ∀ r, cutoff ≤ r → 0 < r →
      PositiveWord
        (ExactInterfaceTermDivisionTree.Staged K (cwChunkPartitionedTensor K 5 3)
          (fun _c ↦ cwChunkSplitWord 3)) rootCount)
    (hmultiplicity : ∀ r (hcutoff : cutoff ≤ r) (hr : 0 < r),
      positiveWordSum (fun staged ↦ staged.term.multiplicity) rootCount
        (forest r hcutoff hr) = 1 * (strideValue * r))
    (copyLoss : ℕ → ℝ)
    (hcopyLossSubexponential : Growth.Subexponential copyLoss)
    (hcopyLossPos : ∀ r, 0 < r → 0 < copyLoss r)
    (hcopyGrowth : ∀ r (hcutoff : cutoff ≤ r) (hr : 0 < r),
      copyBase ^ r ≤ copyLoss r *
        (((ExactInterfaceTermDivisionTree.Staged.positiveNatProduct
          (fun staged ↦ (staged.toPowerPacked K).copies) rootCount
          (forest r hcutoff hr) : ℕ) : ℝ)))
    (hbudget : ∀ r (hcutoff : cutoff ≤ r) (hr : 0 < r),
      ForestMeetsBudget K certificateRates 1 rootCount (forest r hcutoff hr)) :
    EventualExactInterfaceDivisionForestStageData K
      (cwChunkPartitionedTensor K 5 3) (fun _c ↦ cwChunkSplitWord 3)
      1 strideValue copyBase
      ((2 : ℝ) ^ (3 * ((strideValue : ℕ) : ℝ) *
        MatrixMultiplication.TotalWeightVolumeLossEndpoint.nominalVolume)) :=
  eventualForestStageData_of_treeProducts K hcopyBase cutoff rootCount forest hmultiplicity
    copyLoss hcopyLossSubexponential hcopyLossPos hcopyGrowth hbudget

end MatrixMultiplication.CoppersmithWinogradDepthThreeForestResiduals
