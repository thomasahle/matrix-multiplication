/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import MatrixMultiplication.CertificateDerivedForestVolumeBudget

set_option autoImplicit false

/-!
# Endpoint forest data with per-tree obligations

`MatrixMultiplication/CertificateDerivedForestVolumeBudget.lean` builds the endpoint's
`EventualExactInterfaceDivisionForestStageData` from a nonempty forest, its exact multiplicity
equation, per-leaf budgets and copy growth.  Two of its inputs are awkward for a producer.  Copy
growth is phrased through `Staged.positiveProductToBlockedPowerPacked`, a packed field of a
transported fold, whereas what a producer counts is the copies of each individual tree; and the
aggregate volume rate is asked for even though the committed certificate rates already dominate it.

This module removes both obstacles and adds the constant-forest corollary.

## What is derived here rather than assumed

* The four packed statistics of a folded forest are the corresponding `positiveNatProduct` of the
  per-tree statistics.  `Staged.positiveProduct` already has that fold law; the blocked-power
  repackaging is a `Packed.precompose`, which copies all four fields verbatim, so the law lifts.
* For the constant word `positiveWordConst`, those folds collapse further: the multiplicity sum is
  `(n + 1) * multiplicity`, each packed statistic is an `(n + 1)`-st power, and `ForestMeetsBudget`
  follows from the single tree's `MeetsBudget`.
* `certificateRates` and its `DominatesCertificate` proof are committed, so the aggregate
  `CarriesWordRate` input of the endpoint constructor is discharged outright; a client here
  supplies no volume rate at all.
* The endpoint constructor uses its volume loss only through `1 ≤ volumeLoss`, so the constant `1`
  discharges the volume-side loss.  The copy loss stays an explicit input: CW copy growth is
  genuinely lossy, and pinning it to `1` here would strengthen an obligation nobody can meet.
* `certificateRates` is also what fixes the budget predicate, so `hbudget` below is stated against
  the committed rates rather than against a rate the client would have to supply and justify.

## The two constructors, and which one a CW client wants

`eventualForestStageData_of_treeProducts` is the general one and the intended shape: it accepts an
arbitrary forest, so the several *distinct* root constituent types a laser-method stage selects from
disjoint source segments are all allowed — which is what the endpoint's own mass-`19` profile needs.
Its one improvement over the committed constructor is that copy growth is asked for at the explicit
product of per-tree copy counts, a quantity a producer can count, rather than at the packed
blocked-power field.

`eventualUniformForestStageData` is the corollary for a forest that repeats a single tree.  It is a
convenience for the degenerate case and is deliberately *not* presented as the endpoint's shape.

## What remains an input

The forest itself, its multiplicity equation, its per-leaf volume budgets, and copy growth with a
subexponential positive copy loss.  No degeneration, no census and no assembled forest restriction
is assumed.  The nominal volume growth is *not* re-proved here; it is the committed constructor's
fold.

None of the form laws below is a global `@[simp]` lemma: they are stated for explicit rewriting so
that no client's elaboration silently depends on the packed representation.
-/

namespace MatrixMultiplication.CertificateDerivedPerTreeForestBudget

open AlgebraicComplexity
open AlgebraicComplexity.Tensor
open MatrixMultiplication.CertificateDerivedLeafVolumeBudget
open MatrixMultiplication.CertificateDerivedForestVolumeBudget
open MatrixMultiplication.SimplifiedSequencePackaging (strideValue)

universe u v w z

/-! ## Folding a constant word -/

section ConstantWord

variable {S : Type*}

/-- Summing a weight over the constant word of `n + 1` letters multiplies it by `n + 1`. -/
theorem positiveWordSum_positiveWordConst (weight : S → ℕ) (entry : S) (n : ℕ) :
    positiveWordSum weight n (positiveWordConst entry n) = (n + 1) * weight entry := by
  induction n with
  | zero =>
      show weight entry = 1 * weight entry
      exact (one_mul _).symm
  | succ n ih =>
      show positiveWordSum weight n (positiveWordConst entry n) + weight entry = _
      rw [ih]
      ring

/-- Multiplying a natural statistic over the constant word of `n + 1` letters raises it to the
`n + 1`-st power. -/
theorem positiveNatProduct_positiveWordConst (value : S → ℕ) (entry : S) (n : ℕ) :
    ExactInterfaceTermDivisionTree.Staged.positiveNatProduct value n
        (positiveWordConst entry n) =
      value entry ^ (n + 1) := by
  induction n with
  | zero =>
      show value entry = value entry ^ 1
      exact (pow_one _).symm
  | succ n ih =>
      show ExactInterfaceTermDivisionTree.Staged.positiveNatProduct value n
          (positiveWordConst entry n) * value entry = _
      rw [ih, ← pow_succ]

end ConstantWord

/-! ## The packed statistics of a folded forest -/

section Fold

variable (K : Type u) [CommSemiring K]
variable {depth : ℕ}
variable {A : Leg → Type w} [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]
variable {V : ∀ c, A c → Type (max u v)}
variable [∀ c a, AddCommMonoid (V c a)] [∀ c a, Module K (V c a)]
variable {P : PartitionedTensor (K := K) (A := A) V}
variable {encode : ∀ c, A c → SplitWord depth}
variable {n blockPower repetitions : ℕ}
variable (stages : PositiveWord
  (ExactInterfaceTermDivisionTree.Staged.{u, v, w, z} K P encode) n)

/-- The copy count of a blocked folded forest is the product of the per-tree copy counts.

Repackaging the fold as a blocked power is a `Packed.precompose`, which carries all four packed
fields through unchanged, so this is the committed `positiveProduct_copies` fold law. -/
theorem positiveProductToBlockedPowerPacked_copies
    (hmultiplicity :
      positiveWordSum (fun staged ↦ staged.term.multiplicity) n stages =
        blockPower * repetitions) :
    (ExactInterfaceTermDivisionTree.Staged.positiveProductToBlockedPowerPacked K
        stages hmultiplicity).copies =
      ExactInterfaceTermDivisionTree.Staged.positiveNatProduct
        (fun staged ↦ (staged.toPowerPacked K).copies) n stages := by
  simpa only [ExactInterfaceTermDivisionTree.Staged.positiveProductToBlockedPowerPacked,
    WholeConstituentLaserVolumeStage.Packed.precompose] using
    ExactInterfaceTermDivisionTree.Staged.positiveProduct_copies K n stages

/-- The `x` side length of a blocked folded forest is the product of the per-tree `x` lengths. -/
theorem positiveProductToBlockedPowerPacked_xSize
    (hmultiplicity :
      positiveWordSum (fun staged ↦ staged.term.multiplicity) n stages =
        blockPower * repetitions) :
    (ExactInterfaceTermDivisionTree.Staged.positiveProductToBlockedPowerPacked K
        stages hmultiplicity).xSize =
      ExactInterfaceTermDivisionTree.Staged.positiveNatProduct
        (fun staged ↦ (staged.toPowerPacked K).xSize) n stages := by
  simpa only [ExactInterfaceTermDivisionTree.Staged.positiveProductToBlockedPowerPacked,
    WholeConstituentLaserVolumeStage.Packed.precompose] using
    ExactInterfaceTermDivisionTree.Staged.positiveProduct_xSize K n stages

/-- The `y` side length of a blocked folded forest is the product of the per-tree `y` lengths. -/
theorem positiveProductToBlockedPowerPacked_ySize
    (hmultiplicity :
      positiveWordSum (fun staged ↦ staged.term.multiplicity) n stages =
        blockPower * repetitions) :
    (ExactInterfaceTermDivisionTree.Staged.positiveProductToBlockedPowerPacked K
        stages hmultiplicity).ySize =
      ExactInterfaceTermDivisionTree.Staged.positiveNatProduct
        (fun staged ↦ (staged.toPowerPacked K).ySize) n stages := by
  simpa only [ExactInterfaceTermDivisionTree.Staged.positiveProductToBlockedPowerPacked,
    WholeConstituentLaserVolumeStage.Packed.precompose] using
    ExactInterfaceTermDivisionTree.Staged.positiveProduct_ySize K n stages

/-- The `z` side length of a blocked folded forest is the product of the per-tree `z` lengths. -/
theorem positiveProductToBlockedPowerPacked_zSize
    (hmultiplicity :
      positiveWordSum (fun staged ↦ staged.term.multiplicity) n stages =
        blockPower * repetitions) :
    (ExactInterfaceTermDivisionTree.Staged.positiveProductToBlockedPowerPacked K
        stages hmultiplicity).zSize =
      ExactInterfaceTermDivisionTree.Staged.positiveNatProduct
        (fun staged ↦ (staged.toPowerPacked K).zSize) n stages := by
  simpa only [ExactInterfaceTermDivisionTree.Staged.positiveProductToBlockedPowerPacked,
    WholeConstituentLaserVolumeStage.Packed.precompose] using
    ExactInterfaceTermDivisionTree.Staged.positiveProduct_zSize K n stages

end Fold

/-! ## The uniform forest -/

section Uniform

variable (K : Type u) [CommSemiring K]
variable {depth : ℕ}
variable {A : Leg → Type w} [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]
variable {V : ∀ c, A c → Type (max u v)}
variable [∀ c a, AddCommMonoid (V c a)] [∀ c a, Module K (V c a)]
variable {P : PartitionedTensor (K := K) (A := A) V}
variable {encode : ∀ c, A c → SplitWord depth}

/-- A single tree's per-leaf budget gives the whole constant forest's budget. -/
theorem forestMeetsBudget_positiveWordConst (R : ClassVolumeRates) (wordsPerUnit : ℕ)
    (staged : ExactInterfaceTermDivisionTree.Staged.{u, v, w, z} K P encode)
    (hstaged : MeetsBudget K R wordsPerUnit staged.leafStages) (n : ℕ) :
    ForestMeetsBudget K R wordsPerUnit n (positiveWordConst staged n) := by
  induction n with
  | zero => exact hstaged
  | succ n ih => exact ⟨ih, hstaged⟩

/-- The constant forest's exact multiplicity equation, in the endpoint's `blockPower = 1` form.

The producer owes only the integer identity `(n + 1) * multiplicity = 38 * r`. -/
theorem positiveWordSum_positiveWordConst_eq_strideValue_mul
    (staged : ExactInterfaceTermDivisionTree.Staged.{u, v, w, z} K P encode) (n r : ℕ)
    (hmultiplicity : (n + 1) * staged.term.multiplicity = strideValue * r) :
    positiveWordSum (fun entry ↦ entry.term.multiplicity) n (positiveWordConst staged n) =
      1 * (strideValue * r) := by
  rw [positiveWordSum_positiveWordConst, one_mul]
  exact hmultiplicity

end Uniform

/-! ## The endpoint record, general and uniform -/

section Endpoint

variable (K : Type u) [CommSemiring K]
variable {A : Leg → Type w} [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]
variable {V : ∀ c, A c → Type (max u v)}
variable [∀ c a, AddCommMonoid (V c a)] [∀ c a, Module K (V c a)]
variable {P : PartitionedTensor (K := K) (A := A) V}
variable {encode : ∀ c, A c → SplitWord 3}

/-- **Endpoint forest data with copy growth stated per tree.**

This is the general constructor: the forest is arbitrary, so the several root constituent types a
laser-method stage selects from disjoint source segments are all allowed.  The only change from the
committed `eventualForestStageData_of_meetsBudget` is that copy growth is asked for at the explicit
product of the per-tree copy counts rather than at the packed blocked-power field, which is what a
producer can actually count.

Three of the committed constructor's inputs are discharged here rather than passed on: the
aggregate certificate volume rate, via `certificateRates_dominatesCertificate`; the volume-side
subexponential loss, at the constant `1`, which is all the volume fold ever uses; and the volume
base's positivity.  The nominal volume growth remains the committed fold and is not re-proved. -/
noncomputable def eventualForestStageData_of_treeProducts
    {copyBase : ℝ} (hcopyBase : 0 < copyBase)
    (cutoff rootCount : ℕ)
    (forest : ∀ r, cutoff ≤ r → 0 < r →
      PositiveWord
        (ExactInterfaceTermDivisionTree.Staged.{u, v, w, z} K P encode) rootCount)
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
    EventualExactInterfaceDivisionForestStageData K P encode
      1 strideValue copyBase
      ((2 : ℝ) ^ (3 * ((strideValue : ℕ) : ℝ) *
        MatrixMultiplication.TotalWeightVolumeLossEndpoint.nominalVolume)) :=
  eventualForestStageData_of_meetsBudget K certificateRates_dominatesCertificate hcopyBase
    cutoff rootCount forest hmultiplicity
    copyLoss (fun _ ↦ 1)
    hcopyLossSubexponential (Growth.Subexponential.const zero_le_one)
    hcopyLossPos
    (fun r hcutoff hr ↦ by
      rw [positiveProductToBlockedPowerPacked_copies K (forest r hcutoff hr)
        (hmultiplicity r hcutoff hr)]
      exact hcopyGrowth r hcutoff hr)
    hbudget
    (fun _ ↦ le_refl 1)

/-- **Endpoint forest data from one repeated staged tree.**

The uniform corollary of `eventualForestStageData_of_treeProducts`: when every root segment selects
the same constituent type, the producer supplies one checked staged tree, the integer identity
`(rootCount + 1) * multiplicity = 38 * r`, that tree's copy growth at the `rootCount + 1`-st power,
and its per-leaf volume budget.

A laser-method stage that mixes root types — as the endpoint's own mass-`19` profile does — should
use the general constructor above instead; this one is the convenience, not the intended shape. -/
noncomputable def eventualUniformForestStageData
    {copyBase : ℝ} (hcopyBase : 0 < copyBase)
    (cutoff rootCount : ℕ)
    (tree : ∀ r, cutoff ≤ r → 0 < r →
      ExactInterfaceTermDivisionTree.Staged.{u, v, w, z} K P encode)
    (hmultiplicity : ∀ r (hcutoff : cutoff ≤ r) (hr : 0 < r),
      (rootCount + 1) * (tree r hcutoff hr).term.multiplicity = strideValue * r)
    (copyLoss : ℕ → ℝ)
    (hcopyLossSubexponential : Growth.Subexponential copyLoss)
    (hcopyLossPos : ∀ r, 0 < r → 0 < copyLoss r)
    (hcopyGrowth : ∀ r (hcutoff : cutoff ≤ r) (hr : 0 < r),
      copyBase ^ r ≤ copyLoss r *
        (((((tree r hcutoff hr).toPowerPacked K).copies ^ (rootCount + 1) : ℕ) : ℝ)))
    (hbudget : ∀ r (hcutoff : cutoff ≤ r) (hr : 0 < r),
      MeetsBudget K certificateRates 1 (tree r hcutoff hr).leafStages) :
    EventualExactInterfaceDivisionForestStageData K P encode
      1 strideValue copyBase
      ((2 : ℝ) ^ (3 * ((strideValue : ℕ) : ℝ) *
        MatrixMultiplication.TotalWeightVolumeLossEndpoint.nominalVolume)) :=
  eventualForestStageData_of_treeProducts K hcopyBase cutoff rootCount
    (fun r hcutoff hr ↦ positiveWordConst (tree r hcutoff hr) rootCount)
    (fun r hcutoff hr ↦
      positiveWordSum_positiveWordConst_eq_strideValue_mul K (tree r hcutoff hr) rootCount r
        (hmultiplicity r hcutoff hr))
    copyLoss hcopyLossSubexponential hcopyLossPos
    (fun r hcutoff hr ↦ by
      rw [positiveNatProduct_positiveWordConst]
      exact hcopyGrowth r hcutoff hr)
    (fun r hcutoff hr ↦
      forestMeetsBudget_positiveWordConst K certificateRates 1 (tree r hcutoff hr)
        (hbudget r hcutoff hr) rootCount)

end Endpoint

end MatrixMultiplication.CertificateDerivedPerTreeForestBudget
