/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.EventualWholeConstituentLaserVolumeLoss
import AlgebraicComplexity.MatrixMultiplication.ExactInterfaceDivisionLeafStage
import MatrixMultiplication.Generated.TotalQuotientVolumeScalarData
import MatrixMultiplication.SimplifiedSequencePackaging
import MatrixMultiplication.TotalWeightVolumeLossEndpoint

set_option autoImplicit false

/-!
# Certificate-derived per-leaf volume budgets, and their aggregation over classified leaves

## What this module is

`MatrixMultiplication/MergedLeafBudget.lean` (`922faa8`) closes the volume side of the milestone
with three *hand-floored* per-leg constants: E2's FINE floors `(209, 211, 215)` and its merge gains
`(16, 16, 17)`, read off `better_bound/r4_scoping/E2_LATTICE.md` §1 and named as Lean literals.
That file says so itself: *"the census constants below are E2's measurements named as Lean
constants … not quantities derived inside Lean from the certificate."*

This module is the replacement layer.  It derives the volume budget from the **certificate's own
committed volume datum** and aggregates it over the classified leaves of an exact division tree.
`MergedLeafBudget.lean` is not edited, not imported, and not weakened: the new budget is built
beside it and `leafExponentBudget_lt_certificateStrideVolumeBudget` proves the new one is
*strictly larger*, so every client of the old constants keeps its conclusion.

Three things happen here.

* **The budget becomes certificate-derived.**  `certificateWordVolumeBits` is
  `3 · TotalQuotientVolumeScalar.volumeFloor`, i.e. three times the exact rational
  `3755689 / 625000` that `MatrixMultiplication/Generated/TotalQuotientVolumeScalarData.lean` seals
  from certificate SHA-256 `e7987d7f…`, together with its own strict theorem
  `three_mul_volumeFloor_lt_scalarCoordinateSum`.  No E2 measurement is copied.  One `CW₅⁸` source
  word therefore carries `11267067 / 625000 = 18.0273072` bits of three-coordinate volume, and one
  `38`-word stride block carries `428148546 / 625000 = 685.0376736`.

* **The budget is per leaf, and it is classified.**  `LeafVolumeClass` names the five classes a
  division-tree leaf can fall in — the empty (zero-multiplicity) leaf, the three zero orientations
  `X`, `Y`, `Z`, and the positive leaf — and `leafVolumeClass` classifies an
  `ExactInterfaceTermParameters` by its `LevelConstituentIndex.count`.  `leafVolumeBits` is the
  certificate's rate on the leaf's *own* source words, so a leaf's budget is its share of the
  certificate's volume and nothing else.  `ClassVolumeRates` leaves room for genuinely
  class-dependent rates: any assignment dominating the certificate's scalar rate pointwise feeds
  the same aggregation unchanged.

* **The aggregation is lossless and, for the word census, unconditional.**
  `certificate_le_treeVolumeBits` sums the per-leaf budgets along an
  `ExactInterfaceTermDivisionTree` and shows the total is at least the certificate's rate on the
  root's words — the leaf multiplicities add to the root multiplicity because
  `ExactInterfaceTermBinaryDivision.multiplicity_eq` says so, exactly as
  `leafPowerRestriction_exponent` already exploits on the tensor side.  `two_rpow_le_toPacked` then
  transports that sum through `LeafStages.toPacked`, whose branch step multiplies all three
  rectangular sides.  Adding bit budgets and multiplying dimensions is the *same* operation, so no
  rounding is spent at any leaf and none at any branch.

## Why a product budget is the right budget here, and where E1's warning does and does not apply

`SimplifiedSequencePackaging.LeafExponentsValid` is deliberately **per leg**, because FINDING V
showed that at leaf base `5` a *sum* budget constrains the wrong object: `Σ⌊a⌋ < ⌊Σ a⌋` and the old
`304 ≤ x + y + z` was not achievable leg by leg.

`EventualWholeConstituentLaserVolumeLossData.volume_growth` is not that statement.  Its field is

```
volumeBase ^ r ≤ volumeLoss r * ((xSize r * ySize r * zSize r : ℕ) : ℝ)
```

— a bound on the **product** only.  At leaf base `2` there is no quantization between a product of
dimensions and a sum of bits, so the rotation-invariant total is exactly the quantity the field
asks for, and the per-leg flooring is pure loss.  That loss is one whole bit:
`certificateStrideVolumeBudget = 685` against `SimplifiedSequencePackaging.leafExponentBudget = 684`
(`= 225 + 227 + 232`, E1's floored triple).  The extra bit is precisely `⌊Σ M⌋ − Σ⌊M⌋` on E1's
per-leg design rates `(232.226085530, 225.206144930, 227.605457774)`.

## The named hypothesis

`StrideBlockLeafCensus` is the *one* named hypothesis of the aggregation, and it belongs to
burn-down item 13 (the leaf classification's completeness, in flight with codex-2.36x).  It says
only that the stride block's exact division tree at repetition `r` carries exactly `38 · r` source
words — the word form of `TotalWeightEndpointComposition.sourceLetters_eq`'s `304 · r` letters.
Nothing else about the classification is assumed: the classifier `leafVolumeClass` is total, the
word conservation inside the tree is proved, and the empty class is discharged outright on the
committed canonical leaf (`meetsBudget_zero`).

## Honest gap

The certificate seals its volume as a **scalar**: `volumeFloor` is one rational per source word,
summed over the three coordinates.  Its per-coordinate split — E1's `M_d`, the numbers E2 rotated
into `(209, 211, 215)` — is *not* committed in Lean, so this module gives every class the
certificate's scalar rate and lets the *census* do the differentiating.  `ClassVolumeRates` and
`DominatesCertificate` are the seam at which a later tranche installs genuinely class-dependent
rates; installing them requires committing the certificate's per-coordinate volume table, which is
not attempted here.

Also not attempted here: the per-leaf realization itself.  `MeetsBudget` is an *input* to the
aggregation at every positive-multiplicity leaf.  Discharging it is the per-class semantic
identification — the merged zero-block dimension `∑ s ∈ cls, 5 ^ ones s` for a zero orientation
(`MergedRationalTypedLeaf`, and the oriented zero-coordinate laws `059925a`/`4f130a2`/`b8a957d`),
the one-type letters for a positive leaf — and it is the second tranche of this item.
-/

namespace MatrixMultiplication.CertificateDerivedLeafVolumeBudget

open AlgebraicComplexity
open AlgebraicComplexity.Tensor
open MatrixMultiplication.SimplifiedSequencePackaging

universe u v w z

/-! ## The certificate's own volume rate

Everything numeric in this module is a consequence of the two committed declarations
`MatrixMultiplication.Generated.TotalQuotientVolumeScalar.volumeFloor` and
`…​.three_mul_volumeFloor_lt_scalarCoordinateSum`.  No other numeral is introduced. -/

open MatrixMultiplication.Generated.TotalQuotientVolumeScalar in
/-- **The certificate-derived volume rate of one source word**, in bits, summed over the three
rectangular coordinates: three times the committed rational volume floor of the `e7987`
total-weight certificate.

This is the constant that replaces E2's hand-floored census.  It is `18.0273072`. -/
noncomputable def certificateWordVolumeBits : ℝ := 3 * volumeFloor

theorem certificateWordVolumeBits_eq :
    certificateWordVolumeBits = (11267067 / 625000 : ℝ) := by
  norm_num [certificateWordVolumeBits,
    MatrixMultiplication.Generated.TotalQuotientVolumeScalar.volumeFloor]

theorem certificateWordVolumeBits_nonneg : 0 ≤ certificateWordVolumeBits := by
  rw [certificateWordVolumeBits_eq]; norm_num

theorem certificateWordVolumeBits_pos : 0 < certificateWordVolumeBits := by
  rw [certificateWordVolumeBits_eq]; norm_num

/-- **The rate is a genuine lower bound for the certificate's exact aggregate.**  This is the
committed strict theorem `three_mul_volumeFloor_lt_scalarCoordinateSum` read in this module's
vocabulary, and it is what makes `certificateWordVolumeBits` *derived* rather than assumed. -/
theorem certificateWordVolumeBits_lt_scalarCoordinateSum :
    certificateWordVolumeBits <
      MatrixMultiplication.Generated.TotalQuotientVolumeScalar.scalarCoordinateSum :=
  MatrixMultiplication.Generated.TotalQuotientVolumeScalar.three_mul_volumeFloor_lt_scalarCoordinateSum

/-- **The certificate-derived volume of one `38`-word stride block**: `428148546 / 625000
= 685.0376736` bits. -/
noncomputable def certificateStrideVolumeBits : ℝ :=
  ((strideValue : ℕ) : ℝ) * certificateWordVolumeBits

theorem certificateStrideVolumeBits_eq :
    certificateStrideVolumeBits = (428148546 / 625000 : ℝ) := by
  rw [certificateStrideVolumeBits, strideValue_cast, certificateWordVolumeBits_eq]
  norm_num

/-- The integral stride-block budget the certificate certifies. -/
def certificateStrideVolumeBudget : ℕ := 685

theorem certificateStrideVolumeBudget_le_certificateStrideVolumeBits :
    ((certificateStrideVolumeBudget : ℕ) : ℝ) ≤ certificateStrideVolumeBits := by
  rw [certificateStrideVolumeBits_eq]
  norm_num [certificateStrideVolumeBudget]

/-- **The certificate-derived budget strictly dominates E2's hand-floored leg census.**

`SimplifiedSequencePackaging.leafExponentBudget = 684` is `225 + 227 + 232`, i.e. E1's per-leg
design rates floored **separately**; the certificate's own scalar datum certifies `685`.  The
recovered bit is exactly `⌊Σ M⌋ − Σ⌊M⌋`, and it is recoverable only because
`volume_growth` bounds the *product* of the three sides.  Consequently every conclusion drawn from
the hand-floored constants survives unchanged. -/
theorem leafExponentBudget_lt_certificateStrideVolumeBudget :
    leafExponentBudget < certificateStrideVolumeBudget := by
  norm_num [leafExponentBudget, certificateStrideVolumeBudget]

/-- The same statement spelled out on the three committed per-leg budgets, so that the comparison
never goes through a hand-copied total. -/
theorem legBudgets_lt_certificateStrideVolumeBudget :
    xExponentBudget + yExponentBudget + zExponentBudget < certificateStrideVolumeBudget := by
  rw [leafExponentBudget_eq]
  exact leafExponentBudget_lt_certificateStrideVolumeBudget

/-- **The nominal volume exponent fits inside the certificate's own stride-block volume.**
`3 · 38 · 6 = 684 ≤ 685.0376736`.  This is the exponent
`TotalWeightEndpointComposition.omega_lt_236999_final` pins its `stages` argument at. -/
theorem nominalVolume_le_certificateStrideVolumeBits :
    3 * ((strideValue : ℕ) : ℝ) *
        MatrixMultiplication.TotalWeightVolumeLossEndpoint.nominalVolume ≤
      certificateStrideVolumeBits := by
  rw [certificateStrideVolumeBits_eq, strideValue_cast]
  norm_num [MatrixMultiplication.TotalWeightVolumeLossEndpoint.nominalVolume]

/-- **The backed-off volume exponent fits with room.**  `3 · 38 · 5.999 = 683.886 ≤ 685.0376736`,
a margin of `1.1516736` bits per stride block. -/
theorem backedOffVolume_le_certificateStrideVolumeBits :
    3 * ((strideValue : ℕ) : ℝ) *
        MatrixMultiplication.TotalWeightVolumeLossEndpoint.backedOffVolume ≤
      certificateStrideVolumeBits := by
  rw [certificateStrideVolumeBits_eq, strideValue_cast]
  norm_num [MatrixMultiplication.TotalWeightVolumeLossEndpoint.backedOffVolume]

/-! ## The leaf classification and its per-class rates -/

/-- **The volume class of a division-tree leaf.**

* `empty` — zero multiplicity.  The leaf is the canonical tensor unit and its budget is `0`;
  `meetsBudget_zeroMultiplicity` discharges it outright.
* `zeroOriented c` — positive multiplicity with the constituent index dead on leg `c`.  These are
  the *zero orientations*: the leaf's volume lives on the two live legs, and the merged
  zero-coordinate support is what pays for it.
* `positive` — positive multiplicity with all three legs live. -/
inductive LeafVolumeClass
  | empty
  | zeroOriented (zero : Leg)
  | positive
  deriving DecidableEq, Repr

/-- Classify an exact interface term by its multiplicity and its constituent-index counts.  The
zero orientations are tested in leg order `X, Y, Z`, so the classifier is total and deterministic
even for an index that is dead on two legs. -/
def leafVolumeClass {depth : ℕ} (term : ExactInterfaceTermParameters depth) : LeafVolumeClass :=
  if term.multiplicity = 0 then .empty
  else if term.index.count .X = 0 then .zeroOriented .X
  else if term.index.count .Y = 0 then .zeroOriented .Y
  else if term.index.count .Z = 0 then .zeroOriented .Z
  else .positive

@[simp] theorem leafVolumeClass_of_multiplicity_zero {depth : ℕ}
    {term : ExactInterfaceTermParameters depth} (h : term.multiplicity = 0) :
    leafVolumeClass term = .empty := by
  simp [leafVolumeClass, h]

theorem leafVolumeClass_eq_positive {depth : ℕ} {term : ExactInterfaceTermParameters depth}
    (hmultiplicity : term.multiplicity ≠ 0) (hX : term.index.count .X ≠ 0)
    (hY : term.index.count .Y ≠ 0) (hZ : term.index.count .Z ≠ 0) :
    leafVolumeClass term = .positive := by
  simp [leafVolumeClass, hmultiplicity, hX, hY, hZ]

theorem leafVolumeClass_eq_zeroOriented_X {depth : ℕ}
    {term : ExactInterfaceTermParameters depth}
    (hmultiplicity : term.multiplicity ≠ 0) (hX : term.index.count .X = 0) :
    leafVolumeClass term = .zeroOriented .X := by
  simp [leafVolumeClass, hmultiplicity, hX]

/-- **A per-class volume-rate assignment**, in bits of three-coordinate volume per source word.

The certificate seals only the scalar rate, so `certificateRates` gives every class the same
number.  The structure exists so that a later tranche can install genuinely class-dependent rates
— a zero orientation above the mean, a positive leaf below it — without touching a single line of
the aggregation below. -/
structure ClassVolumeRates where
  /-- Three-coordinate volume bits carried by one source word of a leaf of this class. -/
  rate : LeafVolumeClass → ℝ
  rate_nonneg : ∀ c, 0 ≤ rate c

/-- **The certificate's own rates**: its scalar per-word volume on every class. -/
noncomputable def certificateRates : ClassVolumeRates where
  rate := fun _ ↦ certificateWordVolumeBits
  rate_nonneg := fun _ ↦ certificateWordVolumeBits_nonneg

@[simp] theorem certificateRates_rate (c : LeafVolumeClass) :
    certificateRates.rate c = certificateWordVolumeBits := rfl

/-- **The per-class budget theorems, as committed rationals.**  Each of the five classes carries
`11267067 / 625000 = 18.0273072` bits of three-coordinate volume per source word under the
certificate's own rate. -/
theorem certificateRates_rate_eq (c : LeafVolumeClass) :
    certificateRates.rate c = (11267067 / 625000 : ℝ) := by
  rw [certificateRates_rate, certificateWordVolumeBits_eq]

theorem certificateRates_rate_empty :
    certificateRates.rate .empty = (11267067 / 625000 : ℝ) := certificateRates_rate_eq _

theorem certificateRates_rate_zeroOriented (c : Leg) :
    certificateRates.rate (.zeroOriented c) = (11267067 / 625000 : ℝ) :=
  certificateRates_rate_eq _

theorem certificateRates_rate_positive :
    certificateRates.rate .positive = (11267067 / 625000 : ℝ) := certificateRates_rate_eq _

/-- A rate assignment is **certificate-derived** when it never falls below the certificate's own
scalar rate.  Pointwise domination is all the aggregation needs, so no census of the classes has
to be known in order to install a refined assignment. -/
def ClassVolumeRates.DominatesCertificate (R : ClassVolumeRates) : Prop :=
  ∀ c, certificateWordVolumeBits ≤ R.rate c

theorem certificateRates_dominatesCertificate :
    certificateRates.DominatesCertificate := fun _ ↦ le_rfl

/-! ## The per-leaf budget, and its aggregate over an exact division tree

`wordsPerUnit` is the number of `CW₅⁸` source words one unit of a tree's `multiplicity` carries.
For the depth-four chunk route a unit is one `16`-letter chunk and `wordsPerUnit = 2`; for a
word-indexed route it is `1`.  Keeping it a parameter is what makes this layer independent of the
producer's blocking choice, exactly as `TotalWeightEndpointComposition` keeps `blockPower` out of
the milestone's residual. -/

/-- **The certificate-derived volume budget of one leaf**: its class's rate on its own source
words.  A zero-multiplicity leaf gets `0`. -/
noncomputable def leafVolumeBits (R : ClassVolumeRates) (wordsPerUnit : ℕ) {depth : ℕ}
    (term : ExactInterfaceTermParameters depth) : ℝ :=
  ((wordsPerUnit * term.multiplicity : ℕ) : ℝ) * R.rate (leafVolumeClass term)

theorem leafVolumeBits_nonneg (R : ClassVolumeRates) (wordsPerUnit : ℕ) {depth : ℕ}
    (term : ExactInterfaceTermParameters depth) : 0 ≤ leafVolumeBits R wordsPerUnit term :=
  mul_nonneg (Nat.cast_nonneg _) (R.rate_nonneg _)

/-- **The empty class's budget is zero.**  A zero-multiplicity leaf carries no source word, so the
certificate gives it nothing and the canonical `1 × 1 × 1` stage of
`ExactInterfaceTermDivisionTree.LeafStages.zero` meets it. -/
@[simp] theorem leafVolumeBits_of_multiplicity_zero (R : ClassVolumeRates) (wordsPerUnit : ℕ)
    {depth : ℕ} {term : ExactInterfaceTermParameters depth} (h : term.multiplicity = 0) :
    leafVolumeBits R wordsPerUnit term = 0 := by
  simp [leafVolumeBits, h]

/-- Sum of the per-leaf budgets over all leaves of an exact division tree. -/
noncomputable def treeVolumeBits (R : ClassVolumeRates) (wordsPerUnit : ℕ) {depth : ℕ} :
    {term : ExactInterfaceTermParameters depth} →
      ExactInterfaceTermDivisionTree term → ℝ
  | term, .leaf _ => leafVolumeBits R wordsPerUnit term
  | _, .branch _ left right =>
      treeVolumeBits R wordsPerUnit left + treeVolumeBits R wordsPerUnit right

@[simp] theorem treeVolumeBits_leaf (R : ClassVolumeRates) (wordsPerUnit : ℕ) {depth : ℕ}
    {term : ExactInterfaceTermParameters depth}
    (multiplicityCase : ExactInterfaceTermMultiplicityCase term) :
    treeVolumeBits R wordsPerUnit (.leaf multiplicityCase) =
      leafVolumeBits R wordsPerUnit term := rfl

@[simp] theorem treeVolumeBits_branch (R : ClassVolumeRates) (wordsPerUnit : ℕ) {depth : ℕ}
    {parent : ExactInterfaceTermParameters depth}
    (division : ExactInterfaceTermBinaryDivision parent)
    (left : ExactInterfaceTermDivisionTree division.leftTerm)
    (right : ExactInterfaceTermDivisionTree division.rightTerm) :
    treeVolumeBits R wordsPerUnit (.branch division left right) =
      treeVolumeBits R wordsPerUnit left + treeVolumeBits R wordsPerUnit right := rfl

/-- **The aggregation over classified leaves, with no census hypothesis.**

The leaf multiplicities of an exact division tree add to the root multiplicity — that is
`ExactInterfaceTermBinaryDivision.multiplicity_eq`, the same fact the tensor side already uses in
`ExactInterfaceTermDivisionTree.leafPowerRestriction_exponent` — so the classified per-leaf budgets
total at least the certificate's rate on the root's own words, for *any* certificate-derived rate
assignment.  No completeness hypothesis is needed for this step; the classifier is total and the
word bookkeeping is proved. -/
theorem certificate_le_treeVolumeBits {R : ClassVolumeRates} (hR : R.DominatesCertificate)
    (wordsPerUnit : ℕ) {depth : ℕ} {term : ExactInterfaceTermParameters depth}
    (tree : ExactInterfaceTermDivisionTree term) :
    ((wordsPerUnit * term.multiplicity : ℕ) : ℝ) * certificateWordVolumeBits ≤
      treeVolumeBits R wordsPerUnit tree := by
  induction tree with
  | @leaf leafTerm multiplicityCase =>
      rw [treeVolumeBits_leaf, leafVolumeBits]
      exact mul_le_mul_of_nonneg_left (hR _) (Nat.cast_nonneg _)
  | @branch parent division left right ihleft ihright =>
      have hm : wordsPerUnit * parent.multiplicity =
          wordsPerUnit * division.leftTerm.multiplicity +
            wordsPerUnit * division.rightTerm.multiplicity := by
        show wordsPerUnit * parent.multiplicity =
          wordsPerUnit * division.leftMultiplicity + wordsPerUnit * division.rightMultiplicity
        rw [division.multiplicity_eq, Nat.mul_add]
      calc ((wordsPerUnit * parent.multiplicity : ℕ) : ℝ) * certificateWordVolumeBits
          = ((wordsPerUnit * division.leftTerm.multiplicity : ℕ) : ℝ) *
                certificateWordVolumeBits +
              ((wordsPerUnit * division.rightTerm.multiplicity : ℕ) : ℝ) *
                certificateWordVolumeBits := by
            rw [hm]
            push_cast
            ring
        _ ≤ treeVolumeBits R wordsPerUnit left + treeVolumeBits R wordsPerUnit right :=
            add_le_add ihleft ihright
        _ = treeVolumeBits R wordsPerUnit (.branch division left right) :=
            (treeVolumeBits_branch R wordsPerUnit division left right).symm

/-! ## The lossless fold through `LeafStages.toPacked`

Adding bit budgets and multiplying rectangular dimensions are the same operation, so the branch
step of `WholeConstituentLaserVolumeStage.Packed.external` — which multiplies all three sides —
transports the sum of leaf budgets with no rounding at all. -/

section Fold

variable (K : Type u) [CommSemiring K]
variable {depth : ℕ}
variable {A : Leg → Type w} [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]
variable {V : ∀ c, A c → Type (max u v)}
variable [∀ c a, AddCommMonoid (V c a)] [∀ c a, Module K (V c a)]
variable {P : PartitionedTensor (K := K) (A := A) V}
variable {encode : ∀ c, A c → SplitWord depth}

/-- **The per-leaf obligation.**  Every leaf's packed stage realizes its own certificate-derived
budget as a rectangular volume.  This is the *input* to the aggregation; discharging it leaf class
by leaf class is the semantic identification named in the module's honest gap. -/
def MeetsBudget (R : ClassVolumeRates) (wordsPerUnit : ℕ) :
    {term : ExactInterfaceTermParameters depth} →
      {tree : ExactInterfaceTermDivisionTree term} →
        ExactInterfaceTermDivisionTree.LeafStages.{u, v, w, z} K P encode tree → Prop
  | term, _, .leaf _ packed =>
      (2 : ℝ) ^ (leafVolumeBits R wordsPerUnit term) ≤
        ((packed.xSize * packed.ySize * packed.zSize : ℕ) : ℝ)
  | _, _, .branch _ leftStages rightStages =>
      MeetsBudget R wordsPerUnit leftStages ∧ MeetsBudget R wordsPerUnit rightStages

@[simp] theorem meetsBudget_leaf (R : ClassVolumeRates) (wordsPerUnit : ℕ)
    {term : ExactInterfaceTermParameters depth}
    (multiplicityCase : ExactInterfaceTermMultiplicityCase term)
    (packed : WholeConstituentLaserVolumeStage.Packed.{u, max u (max v w), z} K
      (P.exactInterfaceTermPowerRestriction encode multiplicityCase).target) :
    MeetsBudget K R wordsPerUnit
        (ExactInterfaceTermDivisionTree.LeafStages.leaf multiplicityCase packed) ↔
      (2 : ℝ) ^ (leafVolumeBits R wordsPerUnit term) ≤
        ((packed.xSize * packed.ySize * packed.zSize : ℕ) : ℝ) := Iff.rfl

@[simp] theorem meetsBudget_branch (R : ClassVolumeRates) (wordsPerUnit : ℕ)
    {parent : ExactInterfaceTermParameters depth}
    (division : ExactInterfaceTermBinaryDivision parent)
    {left : ExactInterfaceTermDivisionTree division.leftTerm}
    {right : ExactInterfaceTermDivisionTree division.rightTerm}
    (leftStages : ExactInterfaceTermDivisionTree.LeafStages.{u, v, w, z} K P encode left)
    (rightStages : ExactInterfaceTermDivisionTree.LeafStages.{u, v, w, z} K P encode right) :
    MeetsBudget K R wordsPerUnit
        (ExactInterfaceTermDivisionTree.LeafStages.branch division leftStages rightStages) ↔
      MeetsBudget K R wordsPerUnit leftStages ∧ MeetsBudget K R wordsPerUnit rightStages :=
  Iff.rfl

/-- **The empty class, discharged.**  A zero-multiplicity leaf's budget is `0` and every packed
stage has positive sides once they are the canonical `1`s, so the obligation is met by the
canonical tensor-unit leaf without any semantic input. -/
theorem meetsBudget_zeroMultiplicity (R : ClassVolumeRates) (wordsPerUnit : ℕ)
    {term : ExactInterfaceTermParameters depth}
    (hmultiplicity : term.multiplicity = 0)
    (multiplicityCase : ExactInterfaceTermMultiplicityCase term)
    (packed : WholeConstituentLaserVolumeStage.Packed.{u, max u (max v w), z} K
      (P.exactInterfaceTermPowerRestriction encode multiplicityCase).target)
    (hx : 0 < packed.xSize) (hy : 0 < packed.ySize) (hz : 0 < packed.zSize) :
    MeetsBudget K R wordsPerUnit
      (ExactInterfaceTermDivisionTree.LeafStages.leaf multiplicityCase packed) := by
  show (2 : ℝ) ^ (leafVolumeBits R wordsPerUnit term) ≤
    ((packed.xSize * packed.ySize * packed.zSize : ℕ) : ℝ)
  rw [leafVolumeBits_of_multiplicity_zero R wordsPerUnit hmultiplicity, Real.rpow_zero]
  have hpos : 0 < packed.xSize * packed.ySize * packed.zSize :=
    Nat.mul_pos (Nat.mul_pos hx hy) hz
  exact_mod_cast hpos

/-- **The empty class, discharged on the canonical leaf.**  The committed zero-multiplicity leaf
`ExactInterfaceTermDivisionTree.LeafStages.zero` is the `1 × 1 × 1` stage on the zeroth tensor
power; its certificate-derived budget is `0` and it meets it with no hypothesis at all. -/
theorem meetsBudget_zero (R : ClassVolumeRates) (wordsPerUnit : ℕ)
    {term : ExactInterfaceTermParameters depth}
    (hmultiplicity : term.multiplicity = 0) :
    MeetsBudget K R wordsPerUnit
      (ExactInterfaceTermDivisionTree.LeafStages.zero.{u, v, w, z}
        (P := P) (encode := encode) K hmultiplicity) := by
  show (2 : ℝ) ^ (leafVolumeBits R wordsPerUnit term) ≤ ((1 * 1 * 1 : ℕ) : ℝ)
  rw [leafVolumeBits_of_multiplicity_zero R wordsPerUnit hmultiplicity, Real.rpow_zero]
  norm_num

/-- **The fold.**  If every leaf meets its own certificate-derived budget, the whole stage assembled
by `ExactInterfaceTermDivisionTree.LeafStages.toPacked` realizes the *sum* of those budgets as its
rectangular volume. -/
theorem two_rpow_treeVolumeBits_le_toPacked (R : ClassVolumeRates) (wordsPerUnit : ℕ)
    {term : ExactInterfaceTermParameters depth}
    {tree : ExactInterfaceTermDivisionTree term}
    (stages : ExactInterfaceTermDivisionTree.LeafStages.{u, v, w, z} K P encode tree)
    (hstages : MeetsBudget K R wordsPerUnit stages) :
    (2 : ℝ) ^ (treeVolumeBits R wordsPerUnit tree) ≤
      ((stages.toPacked.xSize * stages.toPacked.ySize * stages.toPacked.zSize : ℕ) : ℝ) := by
  induction stages with
  | @leaf leafTerm multiplicityCase packed => exact hstages
  | @branch parent division left right leftStages rightStages ihleft ihright =>
      obtain ⟨hleft, hright⟩ := hstages
      have hl := ihleft hleft
      have hr := ihright hright
      have hbase : (0 : ℝ) < 2 := by norm_num
      rw [treeVolumeBits_branch, Real.rpow_add hbase]
      have hcast :
          ((ExactInterfaceTermDivisionTree.LeafStages.branch division leftStages
                  rightStages).toPacked.xSize *
              (ExactInterfaceTermDivisionTree.LeafStages.branch division leftStages
                  rightStages).toPacked.ySize *
              (ExactInterfaceTermDivisionTree.LeafStages.branch division leftStages
                  rightStages).toPacked.zSize : ℕ) =
            (leftStages.toPacked.xSize * leftStages.toPacked.ySize *
                leftStages.toPacked.zSize) *
              (rightStages.toPacked.xSize * rightStages.toPacked.ySize *
                rightStages.toPacked.zSize) := by
        show (leftStages.toPacked.xSize * rightStages.toPacked.xSize) *
            (leftStages.toPacked.ySize * rightStages.toPacked.ySize) *
            (leftStages.toPacked.zSize * rightStages.toPacked.zSize) = _
        ring
      rw [hcast, Nat.cast_mul]
      exact mul_le_mul hl hr (Real.rpow_nonneg hbase.le _) (Nat.cast_nonneg _)

/-- The same bound on the stage assembled directly from the source power: `toPowerPacked`
precomposes with a proved restriction and therefore keeps all three sides. -/
theorem two_rpow_treeVolumeBits_le_toPowerPacked (R : ClassVolumeRates) (wordsPerUnit : ℕ)
    {term : ExactInterfaceTermParameters depth}
    {tree : ExactInterfaceTermDivisionTree term}
    (stages : ExactInterfaceTermDivisionTree.LeafStages.{u, v, w, z} K P encode tree)
    (hstages : MeetsBudget K R wordsPerUnit stages) :
    (2 : ℝ) ^ (treeVolumeBits R wordsPerUnit tree) ≤
      ((stages.toPowerPacked.xSize * stages.toPowerPacked.ySize *
        stages.toPowerPacked.zSize : ℕ) : ℝ) :=
  two_rpow_treeVolumeBits_le_toPacked K R wordsPerUnit stages hstages

/-- **The certificate-derived volume of one assembled stage.**  Combining the census-free
aggregation with the lossless fold: a stage assembled from budgeted classified leaves realizes the
certificate's own rate on every source word its tree carries. -/
theorem two_rpow_certificate_le_toPowerPacked {R : ClassVolumeRates}
    (hR : R.DominatesCertificate) (wordsPerUnit : ℕ)
    {term : ExactInterfaceTermParameters depth}
    {tree : ExactInterfaceTermDivisionTree term}
    (stages : ExactInterfaceTermDivisionTree.LeafStages.{u, v, w, z} K P encode tree)
    (hstages : MeetsBudget K R wordsPerUnit stages) :
    (2 : ℝ) ^ (((wordsPerUnit * term.multiplicity : ℕ) : ℝ) * certificateWordVolumeBits) ≤
      ((stages.toPowerPacked.xSize * stages.toPowerPacked.ySize *
        stages.toPowerPacked.zSize : ℕ) : ℝ) :=
  le_trans
    (Real.rpow_le_rpow_of_exponent_le (by norm_num)
      (certificate_le_treeVolumeBits hR wordsPerUnit tree))
    (two_rpow_treeVolumeBits_le_toPowerPacked K R wordsPerUnit stages hstages)

end Fold

/-! ## The `volume_growth` field

`AlgebraicComplexity.EventualWholeConstituentLaserVolumeLossData.volume_growth` reads

```
volume_growth : ∀ r, cutoff ≤ r → 0 < r →
  volumeBase ^ r ≤ volumeLoss r * (((xSize r * ySize r * zSize r : ℕ) : ℝ))
```

at `volumeBase = 2 ^ (3 · stride · volume)`.  The theorems below produce exactly that inequality —
only the product of the three sides is constrained, which is why the certificate's rotation-
invariant scalar rate is the right budget and the per-leg flooring is pure loss. -/

/-- **The `volume_growth` field from an aggregated leaf budget.**

`budget r` is the total bit budget the classified leaves supply at repetition `r`; the two
hypotheses are that the assembled sides realize it and that it dominates the field's own exponent.
The loss sequence is only required to be at least `1`, which the constant loss `fun _ ↦ 1` — and a
fortiori any growing loss — satisfies. -/
theorem volume_growth_of_aggregate {volume : ℝ} {cutoff : ℕ}
    {xSize ySize zSize : ℕ → ℕ} {budget : ℕ → ℝ} {volumeLoss : ℕ → ℝ}
    (hbudget : ∀ r, cutoff ≤ r → 0 < r →
      (2 : ℝ) ^ (budget r) ≤ ((xSize r * ySize r * zSize r : ℕ) : ℝ))
    (haggregate : ∀ r, cutoff ≤ r → 0 < r →
      3 * ((strideValue : ℕ) : ℝ) * volume * (r : ℝ) ≤ budget r)
    (hloss : ∀ r, (1 : ℝ) ≤ volumeLoss r) :
    ∀ r, cutoff ≤ r → 0 < r →
      ((2 : ℝ) ^ (3 * ((strideValue : ℕ) : ℝ) * volume)) ^ r ≤
        volumeLoss r * ((xSize r * ySize r * zSize r : ℕ) : ℝ) := by
  intro r hcutoff hr
  have hbase : (0 : ℝ) < 2 := by norm_num
  have hpow :
      ((2 : ℝ) ^ (3 * ((strideValue : ℕ) : ℝ) * volume)) ^ r =
        (2 : ℝ) ^ (3 * ((strideValue : ℕ) : ℝ) * volume * (r : ℝ)) := by
    rw [← Real.rpow_natCast ((2 : ℝ) ^ (3 * ((strideValue : ℕ) : ℝ) * volume)) r,
      ← Real.rpow_mul hbase.le]
  have hstep : (2 : ℝ) ^ (3 * ((strideValue : ℕ) : ℝ) * volume * (r : ℝ)) ≤
      ((xSize r * ySize r * zSize r : ℕ) : ℝ) :=
    le_trans (Real.rpow_le_rpow_of_exponent_le (by norm_num) (haggregate r hcutoff hr))
      (hbudget r hcutoff hr)
  have hsize : (0 : ℝ) ≤ ((xSize r * ySize r * zSize r : ℕ) : ℝ) := Nat.cast_nonneg _
  calc ((2 : ℝ) ^ (3 * ((strideValue : ℕ) : ℝ) * volume)) ^ r
      = (2 : ℝ) ^ (3 * ((strideValue : ℕ) : ℝ) * volume * (r : ℝ)) := hpow
    _ ≤ ((xSize r * ySize r * zSize r : ℕ) : ℝ) := hstep
    _ = 1 * ((xSize r * ySize r * zSize r : ℕ) : ℝ) := (one_mul _).symm
    _ ≤ volumeLoss r * ((xSize r * ySize r * zSize r : ℕ) : ℝ) :=
        mul_le_mul_of_nonneg_right (hloss r) hsize

/-! ### The named completeness hypothesis, and the certificate-derived instantiations -/

/-- **The one named hypothesis of the aggregation — burn-down item 13, the leaf classification's
completeness (in flight with codex-2.36x).**

It says only that the stride block's exact division tree at repetition `r` carries exactly the
`38 · r` `CW₅⁸` source words of `r` stride blocks, i.e. that the classified leaves cover the whole
block and nothing more.  This is the word form of
`TotalWeightEndpointComposition.sourceLetters_eq`'s `sourcePower * (strideValue * r) = 304 · r`.

Nothing else about the classification is assumed: `leafVolumeClass` is total, the internal word
conservation of the tree is proved (`certificate_le_treeVolumeBits`), and the empty class is
discharged outright (`meetsBudget_zeroMultiplicity`). -/
def StrideBlockLeafCensus {depth : ℕ} (wordsPerUnit : ℕ)
    (term : ℕ → ExactInterfaceTermParameters depth) (cutoff : ℕ) : Prop :=
  ∀ r, cutoff ≤ r → 0 < r → wordsPerUnit * (term r).multiplicity = strideValue * r

/-- The census hypothesis turns the census-free aggregate into the exact stride-block budget
`685.0376736 · r`. -/
theorem certificateStrideVolumeBits_mul_eq {depth : ℕ} {wordsPerUnit : ℕ}
    {term : ℕ → ExactInterfaceTermParameters depth} {cutoff : ℕ}
    (hcensus : StrideBlockLeafCensus wordsPerUnit term cutoff)
    (r : ℕ) (hcutoff : cutoff ≤ r) (hr : 0 < r) :
    ((wordsPerUnit * (term r).multiplicity : ℕ) : ℝ) * certificateWordVolumeBits =
      certificateStrideVolumeBits * (r : ℝ) := by
  rw [hcensus r hcutoff hr, certificateStrideVolumeBits]
  push_cast
  ring

/-- **The certificate-derived `volume_growth` field, at the nominal volume exponent `6`.**

This is the shape `TotalWeightEndpointComposition.omega_lt_236999_final` consumes: the volume base
of its `stages` argument is `2 ^ (3 · strideValue · nominalVolume)`.  The three inputs are the
per-leaf budgets realized by the classified leaves, the named census hypothesis, and a loss
sequence at or above `1`. -/
theorem volume_growth_nominal_of_census {depth : ℕ} {wordsPerUnit : ℕ}
    {term : ℕ → ExactInterfaceTermParameters depth} {cutoff : ℕ}
    {xSize ySize zSize : ℕ → ℕ} {volumeLoss : ℕ → ℝ}
    (hcensus : StrideBlockLeafCensus wordsPerUnit term cutoff)
    (hbudget : ∀ r, cutoff ≤ r → 0 < r →
      (2 : ℝ) ^ (((wordsPerUnit * (term r).multiplicity : ℕ) : ℝ) * certificateWordVolumeBits) ≤
        ((xSize r * ySize r * zSize r : ℕ) : ℝ))
    (hloss : ∀ r, (1 : ℝ) ≤ volumeLoss r) :
    ∀ r, cutoff ≤ r → 0 < r →
      ((2 : ℝ) ^ (3 * ((strideValue : ℕ) : ℝ) *
          MatrixMultiplication.TotalWeightVolumeLossEndpoint.nominalVolume)) ^ r ≤
        volumeLoss r * ((xSize r * ySize r * zSize r : ℕ) : ℝ) := by
  refine volume_growth_of_aggregate (budget := fun r ↦ certificateStrideVolumeBits * (r : ℝ))
    ?_ ?_ hloss
  · intro r hcutoff hr
    rw [← certificateStrideVolumeBits_mul_eq hcensus r hcutoff hr]
    exact hbudget r hcutoff hr
  · intro r _ _
    have hr : (0 : ℝ) ≤ (r : ℝ) := Nat.cast_nonneg _
    exact mul_le_mul_of_nonneg_right nominalVolume_le_certificateStrideVolumeBits hr

/-- **The certificate-derived `volume_growth` field, at the backed-off exponent `5.999`.**

The same statement at `MatrixMultiplication.TotalWeightVolumeLossEndpoint.backedOffVolume`, i.e. at
base `2 ^ (3 · 38 · 5.999)`.  The certificate's stride-block volume clears it by `1.1516736` bits
per stride block. -/
theorem volume_growth_backedOff_of_census {depth : ℕ} {wordsPerUnit : ℕ}
    {term : ℕ → ExactInterfaceTermParameters depth} {cutoff : ℕ}
    {xSize ySize zSize : ℕ → ℕ} {volumeLoss : ℕ → ℝ}
    (hcensus : StrideBlockLeafCensus wordsPerUnit term cutoff)
    (hbudget : ∀ r, cutoff ≤ r → 0 < r →
      (2 : ℝ) ^ (((wordsPerUnit * (term r).multiplicity : ℕ) : ℝ) * certificateWordVolumeBits) ≤
        ((xSize r * ySize r * zSize r : ℕ) : ℝ))
    (hloss : ∀ r, (1 : ℝ) ≤ volumeLoss r) :
    ∀ r, cutoff ≤ r → 0 < r →
      ((2 : ℝ) ^ (3 * ((strideValue : ℕ) : ℝ) *
          MatrixMultiplication.TotalWeightVolumeLossEndpoint.backedOffVolume)) ^ r ≤
        volumeLoss r * ((xSize r * ySize r * zSize r : ℕ) : ℝ) := by
  refine volume_growth_of_aggregate (budget := fun r ↦ certificateStrideVolumeBits * (r : ℝ))
    ?_ ?_ hloss
  · intro r hcutoff hr
    rw [← certificateStrideVolumeBits_mul_eq hcensus r hcutoff hr]
    exact hbudget r hcutoff hr
  · intro r _ _
    have hr : (0 : ℝ) ≤ (r : ℝ) := Nat.cast_nonneg _
    exact mul_le_mul_of_nonneg_right backedOffVolume_le_certificateStrideVolumeBits hr

/-! ### The whole directed volume-growth side, in one statement -/

section Endpoint

variable (K : Type u) [CommSemiring K]
variable {depth : ℕ}
variable {A : Leg → Type w} [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]
variable {V : ∀ c, A c → Type (max u v)}
variable [∀ c a, AddCommMonoid (V c a)] [∀ c a, Module K (V c a)]
variable {P : PartitionedTensor (K := K) (A := A) V}
variable {encode : ∀ c, A c → SplitWord depth}

/-- **Item 19's directed volume-growth side, assembled.**

A family of exact division trees whose classified leaves each meet their certificate-derived
budget, together with the named census hypothesis, supplies the `volume_growth` field of
`AlgebraicComplexity.EventualWholeConstituentLaserVolumeLossData` at the nominal volume base
`2 ^ (3 · strideValue · nominalVolume)` — the base
`TotalWeightEndpointComposition.omega_lt_236999_final` pins its `stages` argument at.

No per-leg budget appears anywhere in the statement, and no E2 measurement is used: the whole
numeric content is the committed rational `volumeFloor` of the `e7987` certificate. -/
theorem volume_growth_of_classifiedLeafStages {R : ClassVolumeRates}
    (hR : R.DominatesCertificate) (wordsPerUnit : ℕ) {cutoff : ℕ}
    {term : ℕ → ExactInterfaceTermParameters depth}
    {tree : ∀ r, ExactInterfaceTermDivisionTree (term r)}
    {stages : ∀ r, ExactInterfaceTermDivisionTree.LeafStages.{u, v, w, z} K P encode (tree r)}
    {xSize ySize zSize : ℕ → ℕ} {volumeLoss : ℕ → ℝ}
    (hcensus : StrideBlockLeafCensus wordsPerUnit term cutoff)
    (hstages : ∀ r, cutoff ≤ r → 0 < r → MeetsBudget K R wordsPerUnit (stages r))
    (hsizes : ∀ r, cutoff ≤ r → 0 < r →
      (stages r).toPowerPacked.xSize * (stages r).toPowerPacked.ySize *
          (stages r).toPowerPacked.zSize ≤ xSize r * ySize r * zSize r)
    (hloss : ∀ r, (1 : ℝ) ≤ volumeLoss r) :
    ∀ r, cutoff ≤ r → 0 < r →
      ((2 : ℝ) ^ (3 * ((strideValue : ℕ) : ℝ) *
          MatrixMultiplication.TotalWeightVolumeLossEndpoint.nominalVolume)) ^ r ≤
        volumeLoss r * ((xSize r * ySize r * zSize r : ℕ) : ℝ) := by
  refine volume_growth_nominal_of_census hcensus ?_ hloss
  intro r hcutoff hr
  refine le_trans
    (two_rpow_certificate_le_toPowerPacked K hR wordsPerUnit (stages r) (hstages r hcutoff hr)) ?_
  exact_mod_cast hsizes r hcutoff hr

/-- **The same assembly at the backed-off exponent `5.999`**, i.e. at volume base
`2 ^ (3 · 38 · 5.999)`.  Identical inputs; the certificate's stride-block volume clears this base
by `1.1516736` bits instead of `1.0376736`. -/
theorem volume_growth_backedOff_of_classifiedLeafStages {R : ClassVolumeRates}
    (hR : R.DominatesCertificate) (wordsPerUnit : ℕ) {cutoff : ℕ}
    {term : ℕ → ExactInterfaceTermParameters depth}
    {tree : ∀ r, ExactInterfaceTermDivisionTree (term r)}
    {stages : ∀ r, ExactInterfaceTermDivisionTree.LeafStages.{u, v, w, z} K P encode (tree r)}
    {xSize ySize zSize : ℕ → ℕ} {volumeLoss : ℕ → ℝ}
    (hcensus : StrideBlockLeafCensus wordsPerUnit term cutoff)
    (hstages : ∀ r, cutoff ≤ r → 0 < r → MeetsBudget K R wordsPerUnit (stages r))
    (hsizes : ∀ r, cutoff ≤ r → 0 < r →
      (stages r).toPowerPacked.xSize * (stages r).toPowerPacked.ySize *
          (stages r).toPowerPacked.zSize ≤ xSize r * ySize r * zSize r)
    (hloss : ∀ r, (1 : ℝ) ≤ volumeLoss r) :
    ∀ r, cutoff ≤ r → 0 < r →
      ((2 : ℝ) ^ (3 * ((strideValue : ℕ) : ℝ) *
          MatrixMultiplication.TotalWeightVolumeLossEndpoint.backedOffVolume)) ^ r ≤
        volumeLoss r * ((xSize r * ySize r * zSize r : ℕ) : ℝ) := by
  refine volume_growth_backedOff_of_census hcensus ?_ hloss
  intro r hcutoff hr
  refine le_trans
    (two_rpow_certificate_le_toPowerPacked K hR wordsPerUnit (stages r) (hstages r hcutoff hr)) ?_
  exact_mod_cast hsizes r hcutoff hr

end Endpoint

end MatrixMultiplication.CertificateDerivedLeafVolumeBudget
