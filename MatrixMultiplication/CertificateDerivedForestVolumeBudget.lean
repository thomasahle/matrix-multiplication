/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.EventualExactInterfaceDivisionForestStage
import MatrixMultiplication.CertificateDerivedLeafVolumeBudget

set_option autoImplicit false

/-!
# Certificate-derived volume budgets for exact division forests

The endpoint assembles a nonempty forest of exact interface-division trees.  Its forest record
already proves that the sum of the root multiplicities is the source exponent.  Consequently the
word census needed by the scalar volume certificate is derived by folding the per-tree budget over
the forest; it is not a separate hypothesis on an artificial aggregate tree.

This module performs that fold.  It then gives a constructor for the endpoint's depth-three
`blockPower = 1` forest data whose volume-growth field follows from:

* the exact forest multiplicity equation;
* the certificate-derived per-leaf budgets;
* and a volume loss bounded below by one.

Copy growth and the semantic leaf stages remain explicit inputs.  No degeneration of the assembled
forest, generated recurrence table, or additional census is assumed.
-/

namespace MatrixMultiplication.CertificateDerivedForestVolumeBudget

open AlgebraicComplexity
open AlgebraicComplexity.Tensor
open MatrixMultiplication.CertificateDerivedLeafVolumeBudget
open MatrixMultiplication.SimplifiedSequencePackaging (strideValue strideValue_pos)

universe u v w z

section Fold

variable (K : Type u) [CommSemiring K]
variable {depth : ℕ}
variable {A : Leg → Type w} [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]
variable {V : ∀ c, A c → Type (max u v)}
variable [∀ c a, AddCommMonoid (V c a)] [∀ c a, Module K (V c a)]
variable {P : PartitionedTensor (K := K) (A := A) V}
variable {encode : ∀ c, A c → SplitWord depth}

/-- Every checked root tree in a nonempty forest satisfies its recursively defined leaf budgets. -/
def ForestMeetsBudget (R : ClassVolumeRates) (wordsPerUnit : ℕ) :
    (n : ℕ) →
      PositiveWord
        (ExactInterfaceTermDivisionTree.Staged.{u, v, w, z} K P encode) n → Prop
  | 0, staged => MeetsBudget K R wordsPerUnit staged.leafStages
  | n + 1, stages =>
      ForestMeetsBudget R wordsPerUnit n stages.1 ∧
        MeetsBudget K R wordsPerUnit stages.2.leafStages

@[simp] theorem forestMeetsBudget_zero (R : ClassVolumeRates) (wordsPerUnit : ℕ)
    (staged : ExactInterfaceTermDivisionTree.Staged.{u, v, w, z} K P encode) :
    ForestMeetsBudget K R wordsPerUnit 0 staged ↔
      MeetsBudget K R wordsPerUnit staged.leafStages :=
  Iff.rfl

@[simp] theorem forestMeetsBudget_succ (R : ClassVolumeRates) (wordsPerUnit n : ℕ)
    (stages : PositiveWord
      (ExactInterfaceTermDivisionTree.Staged.{u, v, w, z} K P encode) (n + 1)) :
    ForestMeetsBudget K R wordsPerUnit (n + 1) stages ↔
      ForestMeetsBudget K R wordsPerUnit n stages.1 ∧
        MeetsBudget K R wordsPerUnit stages.2.leafStages :=
  Iff.rfl

/-- Sum the recursively defined leaf-volume budgets of every tree in a nonempty forest. -/
noncomputable def forestVolumeBits (R : ClassVolumeRates) (wordsPerUnit : ℕ) :
    (n : ℕ) →
      PositiveWord
        (ExactInterfaceTermDivisionTree.Staged.{u, v, w, z} K P encode) n → ℝ
  | 0, staged => treeVolumeBits R wordsPerUnit staged.tree
  | n + 1, stages =>
      forestVolumeBits R wordsPerUnit n stages.1 +
        treeVolumeBits R wordsPerUnit stages.2.tree

@[simp] theorem forestVolumeBits_zero (R : ClassVolumeRates) (wordsPerUnit : ℕ)
    (staged : ExactInterfaceTermDivisionTree.Staged.{u, v, w, z} K P encode) :
    forestVolumeBits K R wordsPerUnit 0 staged =
      treeVolumeBits R wordsPerUnit staged.tree :=
  rfl

@[simp] theorem forestVolumeBits_succ (R : ClassVolumeRates) (wordsPerUnit n : ℕ)
    (stages : PositiveWord
      (ExactInterfaceTermDivisionTree.Staged.{u, v, w, z} K P encode) (n + 1)) :
    forestVolumeBits K R wordsPerUnit (n + 1) stages =
      forestVolumeBits K R wordsPerUnit n stages.1 +
        treeVolumeBits R wordsPerUnit stages.2.tree :=
  rfl

/-- A nonempty forest carries a requested three-coordinate volume rate per source word when the
sum of its realized class budgets dominates that rate on the exact total root multiplicity.

Unlike pointwise class domination, this aggregate predicate permits one class to lie below the
requested mean when other classes compensate above it. -/
def CarriesWordRate (R : ClassVolumeRates) (wordsPerUnit : ℕ) (wordRate : ℝ)
    (n : ℕ)
    (stages : PositiveWord
      (ExactInterfaceTermDivisionTree.Staged.{u, v, w, z} K P encode) n) : Prop :=
  ((wordsPerUnit * positiveWordSum
      (fun staged ↦ staged.term.multiplicity) n stages : ℕ) : ℝ) * wordRate ≤
    forestVolumeBits K R wordsPerUnit n stages

/-- Pointwise domination of the certificate rate implies aggregate domination over any forest.
This is the conservative specialization; class-dependent clients should normally prove
`CarriesWordRate` directly from their weighted class census. -/
theorem carriesCertificateWordRate_of_dominates
    {R : ClassVolumeRates} (hR : R.DominatesCertificate) (wordsPerUnit : ℕ)
    (n : ℕ)
    (stages : PositiveWord
      (ExactInterfaceTermDivisionTree.Staged.{u, v, w, z} K P encode) n) :
    CarriesWordRate K R wordsPerUnit certificateWordVolumeBits n stages := by
  induction n with
  | zero =>
      exact certificate_le_treeVolumeBits hR wordsPerUnit stages.tree
  | succ n ih =>
      have hleft := ih stages.1
      have hright := certificate_le_treeVolumeBits hR wordsPerUnit stages.2.tree
      calc
        ((wordsPerUnit * positiveWordSum
              (fun staged ↦ staged.term.multiplicity) (n + 1) stages : ℕ) : ℝ) *
            certificateWordVolumeBits =
          ((wordsPerUnit * positiveWordSum
              (fun staged ↦ staged.term.multiplicity) n stages.1 : ℕ) : ℝ) *
              certificateWordVolumeBits +
            ((wordsPerUnit * stages.2.term.multiplicity : ℕ) : ℝ) *
              certificateWordVolumeBits := by
            rw [positiveWordSum_succ, Nat.mul_add]
            push_cast
            ring
        _ ≤ forestVolumeBits K R wordsPerUnit n stages.1 +
              treeVolumeBits R wordsPerUnit stages.2.tree :=
          add_le_add hleft hright
        _ = forestVolumeBits K R wordsPerUnit (n + 1) stages :=
          (forestVolumeBits_succ K R wordsPerUnit n stages).symm

/-- Folding budgeted trees over a nonempty forest realizes the sum of their leaf budgets as the
product of the three assembled rectangular dimensions. -/
theorem two_rpow_forestVolumeBits_le_positiveProduct
    (R : ClassVolumeRates) (wordsPerUnit : ℕ)
    (n : ℕ)
    (stages : PositiveWord
      (ExactInterfaceTermDivisionTree.Staged.{u, v, w, z} K P encode) n)
    (hstages : ForestMeetsBudget K R wordsPerUnit n stages) :
    (2 : ℝ) ^ (forestVolumeBits K R wordsPerUnit n stages) ≤
      (((ExactInterfaceTermDivisionTree.Staged.positiveProduct K n stages).xSize *
        (ExactInterfaceTermDivisionTree.Staged.positiveProduct K n stages).ySize *
        (ExactInterfaceTermDivisionTree.Staged.positiveProduct K n stages).zSize : ℕ) : ℝ) := by
  induction n with
  | zero =>
      exact two_rpow_treeVolumeBits_le_toPowerPacked
        K R wordsPerUnit stages.leafStages hstages
  | succ n ih =>
      obtain ⟨hleft, hright⟩ := hstages
      have hl := ih stages.1 hleft
      have hr := two_rpow_treeVolumeBits_le_toPowerPacked
        K R wordsPerUnit stages.2.leafStages hright
      have hbase : (0 : ℝ) < 2 := by norm_num
      rw [forestVolumeBits_succ, Real.rpow_add hbase]
      have hcast :
          ((ExactInterfaceTermDivisionTree.Staged.positiveProduct K (n + 1) stages).xSize *
              (ExactInterfaceTermDivisionTree.Staged.positiveProduct K (n + 1) stages).ySize *
              (ExactInterfaceTermDivisionTree.Staged.positiveProduct K (n + 1) stages).zSize : ℕ) =
            ((ExactInterfaceTermDivisionTree.Staged.positiveProduct K n stages.1).xSize *
                (ExactInterfaceTermDivisionTree.Staged.positiveProduct K n stages.1).ySize *
                (ExactInterfaceTermDivisionTree.Staged.positiveProduct K n stages.1).zSize) *
              ((stages.2.toPowerPacked K).xSize * (stages.2.toPowerPacked K).ySize *
                (stages.2.toPowerPacked K).zSize) := by
        change
          ((ExactInterfaceTermDivisionTree.Staged.positiveProduct K n stages.1).xSize *
                (stages.2.toPowerPacked K).xSize) *
              ((ExactInterfaceTermDivisionTree.Staged.positiveProduct K n stages.1).ySize *
                (stages.2.toPowerPacked K).ySize) *
              ((ExactInterfaceTermDivisionTree.Staged.positiveProduct K n stages.1).zSize *
                (stages.2.toPowerPacked K).zSize) = _
        ring
      rw [hcast]
      calc
        _ ≤
            (((ExactInterfaceTermDivisionTree.Staged.positiveProduct K n stages.1).xSize *
                (ExactInterfaceTermDivisionTree.Staged.positiveProduct K n stages.1).ySize *
                (ExactInterfaceTermDivisionTree.Staged.positiveProduct K n stages.1).zSize : ℕ) : ℝ) *
              (((stages.2.toPowerPacked K).xSize * (stages.2.toPowerPacked K).ySize *
                (stages.2.toPowerPacked K).zSize : ℕ) : ℝ) :=
          mul_le_mul hl hr (Real.rpow_nonneg hbase.le _) (Nat.cast_nonneg _)
        _ =
            ((((ExactInterfaceTermDivisionTree.Staged.positiveProduct K n stages.1).xSize *
                (ExactInterfaceTermDivisionTree.Staged.positiveProduct K n stages.1).ySize *
                (ExactInterfaceTermDivisionTree.Staged.positiveProduct K n stages.1).zSize) *
              ((stages.2.toPowerPacked K).xSize * (stages.2.toPowerPacked K).ySize *
                (stages.2.toPowerPacked K).zSize) : ℕ) : ℝ) := by
          push_cast
          rfl

/-- An aggregate per-word rate, together with its per-leaf realizations, gives the corresponding
volume bound for the checked forest. -/
theorem two_rpow_wordRate_le_positiveProduct
    (R : ClassVolumeRates) (wordsPerUnit : ℕ) (wordRate : ℝ)
    (n : ℕ)
    (stages : PositiveWord
      (ExactInterfaceTermDivisionTree.Staged.{u, v, w, z} K P encode) n)
    (haggregate : CarriesWordRate K R wordsPerUnit wordRate n stages)
    (hstages : ForestMeetsBudget K R wordsPerUnit n stages) :
    (2 : ℝ) ^
        ((((wordsPerUnit * positiveWordSum
          (fun staged ↦ staged.term.multiplicity) n stages : ℕ) : ℝ)) * wordRate) ≤
      (((ExactInterfaceTermDivisionTree.Staged.positiveProduct K n stages).xSize *
        (ExactInterfaceTermDivisionTree.Staged.positiveProduct K n stages).ySize *
        (ExactInterfaceTermDivisionTree.Staged.positiveProduct K n stages).zSize : ℕ) : ℝ) :=
  le_trans
    (Real.rpow_le_rpow_of_exponent_le (by norm_num) haggregate)
    (two_rpow_forestVolumeBits_le_positiveProduct K R wordsPerUnit n stages hstages)

/-- Folding individually budgeted exact trees over a nonempty forest realizes the certificate's
volume rate on every source word counted by the sum of the forest's root multiplicities. -/
theorem two_rpow_certificate_le_positiveProduct
    {R : ClassVolumeRates} (hR : R.DominatesCertificate) (wordsPerUnit : ℕ)
    (n : ℕ)
    (stages : PositiveWord
      (ExactInterfaceTermDivisionTree.Staged.{u, v, w, z} K P encode) n)
    (hstages : ForestMeetsBudget K R wordsPerUnit n stages) :
    (2 : ℝ) ^
        ((((wordsPerUnit * positiveWordSum
          (fun staged ↦ staged.term.multiplicity) n stages : ℕ) : ℝ)) *
            certificateWordVolumeBits) ≤
      (((ExactInterfaceTermDivisionTree.Staged.positiveProduct K n stages).xSize *
        (ExactInterfaceTermDivisionTree.Staged.positiveProduct K n stages).ySize *
        (ExactInterfaceTermDivisionTree.Staged.positiveProduct K n stages).zSize : ℕ) : ℝ) := by
  exact two_rpow_wordRate_le_positiveProduct K R wordsPerUnit certificateWordVolumeBits n
    stages (carriesCertificateWordRate_of_dominates K hR wordsPerUnit n stages) hstages

end Fold

section Endpoint

variable (K : Type u) [CommSemiring K]
variable {A : Leg → Type w} [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]
variable {V : ∀ c, A c → Type (max u v)}
variable [∀ c a, AddCommMonoid (V c a)] [∀ c a, Module K (V c a)]
variable {P : PartitionedTensor (K := K) (A := A) V}
variable {encode : ∀ c, A c → SplitWord 3}

/-- At `blockPower = 1` and stride `38`, an aggregate certificate-rate inequality and the forest's
own multiplicity equation give the nominal endpoint volume-growth inequality.  This is the
class-compensating form: it does not require every class rate to dominate the mean pointwise. -/
theorem nominalVolumeGrowth_of_forestCarriesCertificate
    {R : ClassVolumeRates}
    {cutoff rootCount : ℕ}
    (forest : ∀ r, cutoff ≤ r → 0 < r →
      PositiveWord
        (ExactInterfaceTermDivisionTree.Staged.{u, v, w, z} K P encode) rootCount)
    (hmultiplicity : ∀ r (hcutoff : cutoff ≤ r) (hr : 0 < r),
      positiveWordSum (fun staged ↦ staged.term.multiplicity) rootCount
        (forest r hcutoff hr) = 1 * (strideValue * r))
    (volumeLoss : ℕ → ℝ)
    (hstages : ∀ r (hcutoff : cutoff ≤ r) (hr : 0 < r),
      ForestMeetsBudget K R 1 rootCount (forest r hcutoff hr))
    (haggregate : ∀ r (hcutoff : cutoff ≤ r) (hr : 0 < r),
      CarriesWordRate K R 1 certificateWordVolumeBits rootCount
        (forest r hcutoff hr))
    (hloss : ∀ r, (1 : ℝ) ≤ volumeLoss r) :
    ∀ r (hcutoff : cutoff ≤ r) (hr : 0 < r),
      ((2 : ℝ) ^ (3 * ((strideValue : ℕ) : ℝ) *
        MatrixMultiplication.TotalWeightVolumeLossEndpoint.nominalVolume)) ^ r ≤
        volumeLoss r *
          (((ExactInterfaceTermDivisionTree.Staged.positiveProductToBlockedPowerPacked K
              (forest r hcutoff hr) (hmultiplicity r hcutoff hr)).xSize *
            (ExactInterfaceTermDivisionTree.Staged.positiveProductToBlockedPowerPacked K
              (forest r hcutoff hr) (hmultiplicity r hcutoff hr)).ySize *
            (ExactInterfaceTermDivisionTree.Staged.positiveProductToBlockedPowerPacked K
              (forest r hcutoff hr) (hmultiplicity r hcutoff hr)).zSize : ℕ) : ℝ) := by
  intro r hcutoff hr
  have hfold := two_rpow_wordRate_le_positiveProduct K R 1 certificateWordVolumeBits
    rootCount (forest r hcutoff hr) (haggregate r hcutoff hr) (hstages r hcutoff hr)
  have hexponent :
      (((1 * positiveWordSum (fun staged ↦ staged.term.multiplicity) rootCount
        (forest r hcutoff hr) : ℕ) : ℝ) * certificateWordVolumeBits) =
        certificateStrideVolumeBits * (r : ℝ) := by
    rw [hmultiplicity r hcutoff hr]
    simp only [one_mul, certificateStrideVolumeBits]
    push_cast
    ring
  have hbudget :
      (2 : ℝ) ^ (certificateStrideVolumeBits * (r : ℝ)) ≤
        (((ExactInterfaceTermDivisionTree.Staged.positiveProductToBlockedPowerPacked K
              (forest r hcutoff hr) (hmultiplicity r hcutoff hr)).xSize *
            (ExactInterfaceTermDivisionTree.Staged.positiveProductToBlockedPowerPacked K
              (forest r hcutoff hr) (hmultiplicity r hcutoff hr)).ySize *
            (ExactInterfaceTermDivisionTree.Staged.positiveProductToBlockedPowerPacked K
              (forest r hcutoff hr) (hmultiplicity r hcutoff hr)).zSize : ℕ) : ℝ) := by
    rw [← hexponent]
    simpa only [ExactInterfaceTermDivisionTree.Staged.positiveProductToBlockedPowerPacked,
      WholeConstituentLaserVolumeStage.Packed.precompose] using hfold
  have haggregate :
      3 * ((strideValue : ℕ) : ℝ) *
          MatrixMultiplication.TotalWeightVolumeLossEndpoint.nominalVolume * (r : ℝ) ≤
        certificateStrideVolumeBits * (r : ℝ) :=
    mul_le_mul_of_nonneg_right nominalVolume_le_certificateStrideVolumeBits
      (Nat.cast_nonneg r)
  have hbase : (0 : ℝ) < 2 := by norm_num
  have hpow :
      ((2 : ℝ) ^ (3 * ((strideValue : ℕ) : ℝ) *
          MatrixMultiplication.TotalWeightVolumeLossEndpoint.nominalVolume)) ^ r =
        (2 : ℝ) ^ (3 * ((strideValue : ℕ) : ℝ) *
          MatrixMultiplication.TotalWeightVolumeLossEndpoint.nominalVolume * (r : ℝ)) := by
    rw [← Real.rpow_natCast
        ((2 : ℝ) ^ (3 * ((strideValue : ℕ) : ℝ) *
          MatrixMultiplication.TotalWeightVolumeLossEndpoint.nominalVolume)) r,
      ← Real.rpow_mul hbase.le]
  have hstep :
      (2 : ℝ) ^ (3 * ((strideValue : ℕ) : ℝ) *
          MatrixMultiplication.TotalWeightVolumeLossEndpoint.nominalVolume * (r : ℝ)) ≤
        (((ExactInterfaceTermDivisionTree.Staged.positiveProductToBlockedPowerPacked K
              (forest r hcutoff hr) (hmultiplicity r hcutoff hr)).xSize *
            (ExactInterfaceTermDivisionTree.Staged.positiveProductToBlockedPowerPacked K
              (forest r hcutoff hr) (hmultiplicity r hcutoff hr)).ySize *
            (ExactInterfaceTermDivisionTree.Staged.positiveProductToBlockedPowerPacked K
              (forest r hcutoff hr) (hmultiplicity r hcutoff hr)).zSize : ℕ) : ℝ) :=
    le_trans (Real.rpow_le_rpow_of_exponent_le (by norm_num) haggregate) hbudget
  have hsize :
      (0 : ℝ) ≤
        (((ExactInterfaceTermDivisionTree.Staged.positiveProductToBlockedPowerPacked K
              (forest r hcutoff hr) (hmultiplicity r hcutoff hr)).xSize *
            (ExactInterfaceTermDivisionTree.Staged.positiveProductToBlockedPowerPacked K
              (forest r hcutoff hr) (hmultiplicity r hcutoff hr)).ySize *
            (ExactInterfaceTermDivisionTree.Staged.positiveProductToBlockedPowerPacked K
              (forest r hcutoff hr) (hmultiplicity r hcutoff hr)).zSize : ℕ) : ℝ) :=
    Nat.cast_nonneg _
  calc
    ((2 : ℝ) ^ (3 * ((strideValue : ℕ) : ℝ) *
        MatrixMultiplication.TotalWeightVolumeLossEndpoint.nominalVolume)) ^ r =
      (2 : ℝ) ^ (3 * ((strideValue : ℕ) : ℝ) *
        MatrixMultiplication.TotalWeightVolumeLossEndpoint.nominalVolume * (r : ℝ)) := hpow
    _ ≤
        (((ExactInterfaceTermDivisionTree.Staged.positiveProductToBlockedPowerPacked K
              (forest r hcutoff hr) (hmultiplicity r hcutoff hr)).xSize *
            (ExactInterfaceTermDivisionTree.Staged.positiveProductToBlockedPowerPacked K
              (forest r hcutoff hr) (hmultiplicity r hcutoff hr)).ySize *
            (ExactInterfaceTermDivisionTree.Staged.positiveProductToBlockedPowerPacked K
              (forest r hcutoff hr) (hmultiplicity r hcutoff hr)).zSize : ℕ) : ℝ) := hstep
    _ = 1 *
        (((ExactInterfaceTermDivisionTree.Staged.positiveProductToBlockedPowerPacked K
              (forest r hcutoff hr) (hmultiplicity r hcutoff hr)).xSize *
            (ExactInterfaceTermDivisionTree.Staged.positiveProductToBlockedPowerPacked K
              (forest r hcutoff hr) (hmultiplicity r hcutoff hr)).ySize *
            (ExactInterfaceTermDivisionTree.Staged.positiveProductToBlockedPowerPacked K
              (forest r hcutoff hr) (hmultiplicity r hcutoff hr)).zSize : ℕ) : ℝ) := (one_mul _).symm
    _ ≤ volumeLoss r *
        (((ExactInterfaceTermDivisionTree.Staged.positiveProductToBlockedPowerPacked K
              (forest r hcutoff hr) (hmultiplicity r hcutoff hr)).xSize *
            (ExactInterfaceTermDivisionTree.Staged.positiveProductToBlockedPowerPacked K
              (forest r hcutoff hr) (hmultiplicity r hcutoff hr)).ySize *
            (ExactInterfaceTermDivisionTree.Staged.positiveProductToBlockedPowerPacked K
              (forest r hcutoff hr) (hmultiplicity r hcutoff hr)).zSize : ℕ) : ℝ) :=
      mul_le_mul_of_nonneg_right (hloss r) hsize

/-- Pointwise class domination is a conservative corollary of the aggregate forest theorem. -/
theorem nominalVolumeGrowth_of_forestMeetsBudget
    {R : ClassVolumeRates} (hR : R.DominatesCertificate)
    {cutoff rootCount : ℕ}
    (forest : ∀ r, cutoff ≤ r → 0 < r →
      PositiveWord
        (ExactInterfaceTermDivisionTree.Staged.{u, v, w, z} K P encode) rootCount)
    (hmultiplicity : ∀ r (hcutoff : cutoff ≤ r) (hr : 0 < r),
      positiveWordSum (fun staged ↦ staged.term.multiplicity) rootCount
        (forest r hcutoff hr) = 1 * (strideValue * r))
    (volumeLoss : ℕ → ℝ)
    (hstages : ∀ r (hcutoff : cutoff ≤ r) (hr : 0 < r),
      ForestMeetsBudget K R 1 rootCount (forest r hcutoff hr))
    (hloss : ∀ r, (1 : ℝ) ≤ volumeLoss r) :
    ∀ r (hcutoff : cutoff ≤ r) (hr : 0 < r),
      ((2 : ℝ) ^ (3 * ((strideValue : ℕ) : ℝ) *
        MatrixMultiplication.TotalWeightVolumeLossEndpoint.nominalVolume)) ^ r ≤
        volumeLoss r *
          (((ExactInterfaceTermDivisionTree.Staged.positiveProductToBlockedPowerPacked K
              (forest r hcutoff hr) (hmultiplicity r hcutoff hr)).xSize *
            (ExactInterfaceTermDivisionTree.Staged.positiveProductToBlockedPowerPacked K
              (forest r hcutoff hr) (hmultiplicity r hcutoff hr)).ySize *
            (ExactInterfaceTermDivisionTree.Staged.positiveProductToBlockedPowerPacked K
              (forest r hcutoff hr) (hmultiplicity r hcutoff hr)).zSize : ℕ) : ℝ) :=
  nominalVolumeGrowth_of_forestCarriesCertificate K forest hmultiplicity volumeLoss hstages
    (fun r hcutoff hr ↦
      carriesCertificateWordRate_of_dominates K hR 1 rootCount (forest r hcutoff hr)) hloss

/-- Construct endpoint-ready exact-division forest data from copy growth, per-leaf realizations,
and a forest-level aggregate certificate-rate inequality.  This is the preferred constructor for
class-dependent rates: compensation between leaf classes is explicit in `haggregate`. -/
noncomputable def eventualForestStageData_of_aggregateBudget
    {R : ClassVolumeRates}
    {copyBase : ℝ} (hcopyBase : 0 < copyBase)
    (cutoff rootCount : ℕ)
    (forest : ∀ r, cutoff ≤ r → 0 < r →
      PositiveWord
        (ExactInterfaceTermDivisionTree.Staged.{u, v, w, z} K P encode) rootCount)
    (hmultiplicity : ∀ r (hcutoff : cutoff ≤ r) (hr : 0 < r),
      positiveWordSum (fun staged ↦ staged.term.multiplicity) rootCount
        (forest r hcutoff hr) = 1 * (strideValue * r))
    (copyLoss volumeLoss : ℕ → ℝ)
    (hcopyLossSubexponential : Growth.Subexponential copyLoss)
    (hvolumeLossSubexponential : Growth.Subexponential volumeLoss)
    (hcopyLossPos : ∀ r, 0 < r → 0 < copyLoss r)
    (hcopyGrowth : ∀ r (hcutoff : cutoff ≤ r) (hr : 0 < r),
      copyBase ^ r ≤ copyLoss r *
        (((ExactInterfaceTermDivisionTree.Staged.positiveProductToBlockedPowerPacked K
          (forest r hcutoff hr) (hmultiplicity r hcutoff hr)).copies : ℕ) : ℝ))
    (hstages : ∀ r (hcutoff : cutoff ≤ r) (hr : 0 < r),
      ForestMeetsBudget K R 1 rootCount (forest r hcutoff hr))
    (haggregate : ∀ r (hcutoff : cutoff ≤ r) (hr : 0 < r),
      CarriesWordRate K R 1 certificateWordVolumeBits rootCount
        (forest r hcutoff hr))
    (hvolumeLossOneLe : ∀ r, (1 : ℝ) ≤ volumeLoss r) :
    EventualExactInterfaceDivisionForestStageData K P encode
      1 strideValue copyBase
      ((2 : ℝ) ^ (3 * ((strideValue : ℕ) : ℝ) *
        MatrixMultiplication.TotalWeightVolumeLossEndpoint.nominalVolume)) where
  stride_pos := strideValue_pos
  copyBase_pos := hcopyBase
  volumeBase_pos := by positivity
  cutoff := cutoff
  rootCount := rootCount
  forest := forest
  multiplicity_eq := hmultiplicity
  copyLoss := copyLoss
  volumeLoss := volumeLoss
  copyLoss_subexponential := hcopyLossSubexponential
  volumeLoss_subexponential := hvolumeLossSubexponential
  copyLoss_pos := hcopyLossPos
  copy_growth := hcopyGrowth
  volume_growth := nominalVolumeGrowth_of_forestCarriesCertificate
    K forest hmultiplicity volumeLoss hstages haggregate hvolumeLossOneLe

/-- Construct endpoint-ready exact-division forest data from copy-growth data and pointwise
certificate-dominating per-leaf volume budgets.  This conservative constructor is a corollary of
`eventualForestStageData_of_aggregateBudget`; the source census and volume growth are derived. -/
noncomputable def eventualForestStageData_of_meetsBudget
    {R : ClassVolumeRates} (hR : R.DominatesCertificate)
    {copyBase : ℝ} (hcopyBase : 0 < copyBase)
    (cutoff rootCount : ℕ)
    (forest : ∀ r, cutoff ≤ r → 0 < r →
      PositiveWord
        (ExactInterfaceTermDivisionTree.Staged.{u, v, w, z} K P encode) rootCount)
    (hmultiplicity : ∀ r (hcutoff : cutoff ≤ r) (hr : 0 < r),
      positiveWordSum (fun staged ↦ staged.term.multiplicity) rootCount
        (forest r hcutoff hr) = 1 * (strideValue * r))
    (copyLoss volumeLoss : ℕ → ℝ)
    (hcopyLossSubexponential : Growth.Subexponential copyLoss)
    (hvolumeLossSubexponential : Growth.Subexponential volumeLoss)
    (hcopyLossPos : ∀ r, 0 < r → 0 < copyLoss r)
    (hcopyGrowth : ∀ r (hcutoff : cutoff ≤ r) (hr : 0 < r),
      copyBase ^ r ≤ copyLoss r *
        (((ExactInterfaceTermDivisionTree.Staged.positiveProductToBlockedPowerPacked K
          (forest r hcutoff hr) (hmultiplicity r hcutoff hr)).copies : ℕ) : ℝ))
    (hstages : ∀ r (hcutoff : cutoff ≤ r) (hr : 0 < r),
      ForestMeetsBudget K R 1 rootCount (forest r hcutoff hr))
    (hvolumeLossOneLe : ∀ r, (1 : ℝ) ≤ volumeLoss r) :
    EventualExactInterfaceDivisionForestStageData K P encode
      1 strideValue copyBase
      ((2 : ℝ) ^ (3 * ((strideValue : ℕ) : ℝ) *
        MatrixMultiplication.TotalWeightVolumeLossEndpoint.nominalVolume)) :=
  eventualForestStageData_of_aggregateBudget K hcopyBase cutoff rootCount forest hmultiplicity
    copyLoss volumeLoss hcopyLossSubexponential hvolumeLossSubexponential hcopyLossPos hcopyGrowth
    hstages
    (fun r hcutoff hr ↦
      carriesCertificateWordRate_of_dominates K hR 1 rootCount (forest r hcutoff hr))
    hvolumeLossOneLe

end Endpoint

end MatrixMultiplication.CertificateDerivedForestVolumeBudget
