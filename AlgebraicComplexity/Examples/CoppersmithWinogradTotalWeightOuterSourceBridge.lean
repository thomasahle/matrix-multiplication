/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinogradTotalWeightOuterDepthFour
import AlgebraicComplexity.MatrixMultiplication.WholeConstituentLaserVolumeAssembly

/-!
# The source bridge: from the honest power `(CW_q^e)^(stride · r)` to the cleanup's ambient

The merged total-weight cleanup
(`CoppersmithWinogradMergedTypedLeafCleanup`, `OBLIGATIONS.md` §9.10) concludes from the source

`P.realize`, where `P = (Q.positivePower n).withSupport ambient`,
`Q = (cwChunkPartitionedTensor K q depth).coarsen (cwTotalWeightChunkCoarsening depth)`,

but the `ω < 2.36999` endpoint's honest source is the flat power
`(CW₅^{⊗8})^{⊗38r}`.  Item-8--9's release listed the passage between them as named hypothesis (c),
"small, unclaimed".  This module discharges it.

## The chain, and why it is only two steps

`cwCoarsePower_restricts` already carries `(CW_q^e)^s` to the realization of
`cwTotalWeightCoarsePower K q depth n`, whenever `e · s = 2^depth · (n + 1)`; every step of it is a
proved isomorphism.  What was missing is
the passage from that **full** coarse power to the **`ambient`** the cleanup consumes, i.e. the
first zeroing pass.  That step is `Tensor.Restricts.partitionedCompatibilityIsolated` at pivot `.X`,
whose only input is the pair `compatibleX` / `soundX` of the already committed
`CWTotalWeightOuterCoarseCleanup` record.

## The full-support `X`-pass trap does **not** bite, and no new hypothesis is needed

`UniformPowerSelection.restricts_withSupport_of_injOn_x` would also produce a `withSupport`
restriction, but it demands `Set.InjOn (· .X)` on the **whole** ambient support, and on the full
coarse power that is false — distinct coarse addresses routinely share an `X` word.  Taking it as a
hypothesis would make the statement vacuous.  This is exactly the trap
`CoppersmithWinogradTotalWeightOuterDepthFour` documents at its `xSupport_injOn`, and the committed
answer is used here unchanged: **isolate first, then read injectivity off the isolated support.**

Consequently this module introduces **no named hypothesis at all**.  Its only input is the
committed `CWTotalWeightOuterCoarseCleanup`, which is a record of finite, non-tensor data, and
`ownLabelCleanup` below exhibits an inhabitant of it, so nothing here is vacuous.  The two premises
the merged cleanup asks about its ambient — `hambient` and `hX` — are discharged by the committed
`xSupport_subset` and `xSupport_injOn`; `xSupport_cleanupPremises` records that in one place.

## What a client still owes

Only the arithmetic alignment `e · (stride · r) = 2^depth · (n r + 1)`.  At the endpoint's
parameters `q = 5`, `e = 8`, `depth = 4`, `stride = 38`, `n r = 19r - 1` it is
`8 · 38r = 304r = 16 · 19r`, proved once in `levelFourStride38_align`.

## The stage form closes the loop

`MergedLeafBudget.omega_lt_236999_of_mergedStageFamily_at_floor` takes a stage family on the
*power* source `(CW₅^{⊗8})^{⊗ strideValue · r}`, while `cwTotalWeightMergedCleanupStage` produces
one on the *cleanup's* source.  `WholeConstituentLaserVolumeStage.precompose` moves a stage
backwards along a restriction, so `cwLevelFour_stageFamily_of_cleanupStageFamily` turns the second
into the first verbatim, at `strideValue = 38`.  That is the whole passage the milestone's tensor
side was missing between §9.10's cleanup and its endpoint.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor

universe u v

namespace CWTotalWeightOuterCoarseCleanup

variable {K : Type u} [CommRing K] {q depth : ℕ} {n : ℕ → ℕ}

/-! ## The bridge -/

/-- **The source bridge.**  From the finite cleanup inputs and the chunk-alignment identity alone,
the honest asymptotic source `(CW_q^e)^(stride · r)` restricts to the realization of exactly the
partitioned tensor the merged total-weight cleanup consumes: the coarse word power with its support
replaced by the `X`-isolated ambient.

Nothing is assumed beyond the record: `cwCoarsePower_restricts` is a composition of proved
isomorphisms, and the second step is `partitionedCompatibilityIsolated` at pivot `.X`, whose input
is the record's own `soundX`. -/
theorem xSupport_source_restricts
    (data : CWTotalWeightOuterCoarseCleanup K q depth n) (e stride : ℕ)
    (halign : ∀ r, 0 < r → e * (stride * r) = 2 ^ depth * (n r + 1))
    (r : ℕ) (hr : 0 < r) :
    Restricts
      (Tensor.power (Tensor.power (coppersmithWinograd K q) e) (stride * r))
      ((cwTotalWeightCoarsePower K q depth (n r)).withSupport (data.xSupport r)).realize :=
  (cwCoarsePower_restricts K q depth e (stride * r) (n r) (halign r hr)).trans
    (Tensor.Restricts.partitionedCompatibilityIsolated
      (cwTotalWeightCoarsePower K q depth (n r)) .X (data.compatibleX r) (data.soundX r))

/-- **The composable form.**  Any conclusion the cleanup draws from the `X`-isolated ambient is a
conclusion about the endpoint's honest source tensor.

This is the shape `C3`'s assembly consumes: it supplies `hcleanup` — for the merged leaf, one of
`cwTotalWeightFeatureYZCompatibilityCleanup_to_matrixMultiplicationDirectSum_of_{degeneration,
mergedLeaf,zeroClasses}` at `ambient := data.xSupport r` — and receives the restriction from
`(CW_q^e)^(stride · r)`, with no hypothesis added anywhere. -/
theorem source_restricts_of_cleanup
    {W : Leg → Type v} [∀ c, AddCommMonoid (W c)] [∀ c, Module K (W c)]
    {target : Tensor3 K W}
    (data : CWTotalWeightOuterCoarseCleanup K q depth n) (e stride : ℕ)
    (halign : ∀ r, 0 < r → e * (stride * r) = 2 ^ depth * (n r + 1))
    (r : ℕ) (hr : 0 < r)
    (hcleanup :
      Restricts
        ((cwTotalWeightCoarsePower K q depth (n r)).withSupport (data.xSupport r)).realize
        target) :
    Restricts
      (Tensor.power (Tensor.power (coppersmithWinograd K q) e) (stride * r)) target :=
  (data.xSupport_source_restricts e stride halign r hr).trans hcleanup

/-- The two ambient premises the merged cleanup asks for, at `ambient := data.xSupport r`, are
both already committed theorems.  Recording them together is what lets a client instantiate the
cleanup at this ambient without re-deriving anything. -/
theorem xSupport_cleanupPremises
    (data : CWTotalWeightOuterCoarseCleanup K q depth n) (r : ℕ) :
    data.xSupport r ⊆ (cwTotalWeightCoarsePower K q depth (n r)).support ∧
      Set.InjOn
        (fun address : BlockAddress
          (fun _c : Leg ↦ PositiveWord (CWCoarseDigit depth) (n r)) ↦ address .X)
        (data.xSupport r) :=
  ⟨data.xSupport_subset r, data.xSupport_injOn r⟩

/-! ## Non-vacuity -/

/-- The hashing client's instantiation of the whole record: every pass isolates by "own label",
whose soundness is `rfl`.  This exhibits an inhabitant of the bridge's only input, so
`xSupport_source_restricts` is not vacuously quantified. -/
def ownLabelCleanup (K : Type u) [CommRing K] (q depth : ℕ) (n : ℕ → ℕ) :
    CWTotalWeightOuterCoarseCleanup K q depth n where
  compatibleX := fun r ↦ ownLabelCompatible
    (A := fun _c : Leg ↦ PositiveWord (CWCoarseDigit depth) (n r)) .X
  compatibleY := fun r ↦ ownLabelCompatible
    (A := fun _c : Leg ↦ PositiveWord (CWCoarseDigit depth) (n r)) .Y
  compatibleZ := fun r ↦ ownLabelCompatible
    (A := fun _c : Leg ↦ PositiveWord (CWCoarseDigit depth) (n r)) .Z
  soundX := fun _r ↦ isCompatibilitySound_ownLabelCompatible _ .X
  soundY := fun _r ↦ isCompatibilitySound_ownLabelCompatible _ .Y
  soundZ := fun _r ↦ isCompatibilitySound_ownLabelCompatible _ .Z

end CWTotalWeightOuterCoarseCleanup

/-! ## The level-four endpoint parameters -/

/-- The chunk alignment at the `ω < 2.36999` endpoint: a stride block of `8 · 38 r = 304 r`
Coppersmith--Winograd letters is exactly `19 r` chunks of `2^4 = 16` letters, so the positive-power
exponent is `n r = 19 r - 1`.  Only `8 · 38 ≡ 0 (mod 16)` is used. -/
theorem levelFourStride38_align (r : ℕ) (hr : 0 < r) :
    8 * (38 * r) = 2 ^ 4 * ((19 * r - 1) + 1) := by
  have hpow : (2 : ℕ) ^ 4 = 16 := by norm_num
  rw [hpow]
  omega

/-- **The endpoint instance of the source bridge.**  At `q = 5`, `e = 8`, `depth = 4` and
`stride = 38`, the honest source `(CW₅^{⊗8})^{⊗38 r}` restricts to the merged cleanup's ambient for
every `r > 0`. -/
theorem cwLevelFour_xSupport_source_restricts
    {K : Type u} [CommRing K]
    (data : CWTotalWeightOuterCoarseCleanup K 5 4 (fun r ↦ 19 * r - 1))
    (r : ℕ) (hr : 0 < r) :
    Restricts
      (Tensor.power (Tensor.power (coppersmithWinograd K 5) 8) (38 * r))
      ((cwTotalWeightCoarsePower K 5 4 (19 * r - 1)).withSupport (data.xSupport r)).realize :=
  data.xSupport_source_restricts 8 38 (fun r hr ↦ levelFourStride38_align r hr) r hr

/-- The endpoint instance of the composable form: this is the statement `C3`'s assembly needs, with
the cleanup conclusion as its only remaining input. -/
theorem cwLevelFour_source_restricts_of_cleanup
    {K : Type u} [CommRing K]
    {W : Leg → Type v} [∀ c, AddCommMonoid (W c)] [∀ c, Module K (W c)]
    {target : Tensor3 K W}
    (data : CWTotalWeightOuterCoarseCleanup K 5 4 (fun r ↦ 19 * r - 1))
    (r : ℕ) (hr : 0 < r)
    (hcleanup :
      Restricts
        ((cwTotalWeightCoarsePower K 5 4 (19 * r - 1)).withSupport (data.xSupport r)).realize
        target) :
    Restricts
      (Tensor.power (Tensor.power (coppersmithWinograd K 5) 8) (38 * r)) target :=
  (cwLevelFour_xSupport_source_restricts data r hr).trans hcleanup

/-! ## The stage form -/

/-- **Transport a whole-constituent stage from the cleanup's source to the endpoint's source.**

`cwTotalWeightMergedCleanupStage` builds its stage on the `X`-isolated coarse ambient; the
acceptance side wants one on the honest power `(CW₅^{⊗8})^{⊗38 r}`.  Composing the source bridge
with `WholeConstituentLaserVolumeStage.precompose` changes neither the copy count nor any of the
three rectangular dimensions. -/
noncomputable def cwLevelFour_stage_of_cleanupStage
    {K : Type u} [CommRing K]
    (data : CWTotalWeightOuterCoarseCleanup K 5 4 (fun r ↦ 19 * r - 1))
    (r : ℕ) (hr : 0 < r) {copies xSize ySize zSize : ℕ}
    (stage : WholeConstituentLaserVolumeStage K
      ((cwTotalWeightCoarsePower K 5 4 (19 * r - 1)).withSupport (data.xSupport r)).realize
      copies xSize ySize zSize) :
    WholeConstituentLaserVolumeStage K
      (Tensor.power (Tensor.power (coppersmithWinograd K 5) 8) (38 * r))
      copies xSize ySize zSize :=
  WholeConstituentLaserVolumeStage.precompose K
    (cwLevelFour_xSupport_source_restricts data r hr) stage

/-- **The stage-family form: exactly the `stage` hypothesis of the `2.36999` endpoint.**

`MergedLeafBudget.omega_lt_236999_of_mergedStageFamily_at_floor` asks for a family of stages on
`Tensor.power (Tensor.power (coppersmithWinograd K 5) 8) (strideValue * r)` with `strideValue = 38`.
Given the merged cleanup's own stage family on the `X`-isolated ambient, this produces it. -/
noncomputable def cwLevelFour_stageFamily_of_cleanupStageFamily
    {K : Type u} [CommRing K]
    (data : CWTotalWeightOuterCoarseCleanup K 5 4 (fun r ↦ 19 * r - 1))
    {count xSide ySide zSide : ℕ → ℕ}
    (stage : ∀ r, 0 < r →
      WholeConstituentLaserVolumeStage K
        ((cwTotalWeightCoarsePower K 5 4 (19 * r - 1)).withSupport (data.xSupport r)).realize
        (count r) (xSide r) (ySide r) (zSide r)) :
    ∀ r, 0 < r →
      WholeConstituentLaserVolumeStage K
        (Tensor.power (Tensor.power (coppersmithWinograd K 5) 8) (38 * r))
        (count r) (xSide r) (ySide r) (zSide r) :=
  fun r hr ↦ cwLevelFour_stage_of_cleanupStage data r hr (stage r hr)

end AlgebraicComplexity.Examples
