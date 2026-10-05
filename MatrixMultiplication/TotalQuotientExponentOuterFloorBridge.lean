/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import MatrixMultiplication.Generated.TotalQuotientExponentStageFloors
import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.SimplifiedExponentLevelThreeRecurrence
import MatrixMultiplication.SimplifiedExponentRootRecurrence
import MatrixMultiplication.TotalQuotientCompleteSplitRecurrence

set_option autoImplicit false

/-!
# The outer floor-domination seam of the total-weight track: root and level three

`MatrixMultiplication/TotalWeightEndpointComposition.lean` states the volume-only milestone's
final composition `omega_lt_236999_final` from four named hypotheses.  Two of them are

```text
hroot       : ∀ region branch, rootFloor region       ≤ rootRate region branch
hlevelThree : ∀ region branch, levelThreeFloor region ≤ levelThreeRate region branch
```

with `rootRate levelThreeRate : Region → Fin 3 → ℝ`.  This module is the **consumer seam** for
those two hypotheses: it pins each rate to the committed recurrence API that computes it, and it
proves the directed floor transport once, generically, instead of once per (region, branch).

## What this module is, and what it deliberately is not

It is **not** a discharge of `hroot` or `hlevelThree`, and nothing below should be cited as one.
The load-bearing witnesses — a `Region`-indexed root-row family for the `e7987…` total-weight
certificate, and the level-three per-region orientation / per-node integer duals / per-chunk exact
forms for the same certificate — are **absent from the repository**, and this file therefore takes
them as explicit parameters.  Concretely, at the time of writing:

* nothing anywhere produces a `SimplifiedExponentRootRecurrence.RootRows` from
  `SimplifiedVolumeReconstruction.PrimaryTables`, and `PrimaryTables` carries no dual field at all,
  so the committed root duals (raw binary32 words, row width `3 * 17`) are not yet decodable into
  the `weightX / weightY / weightZ` the structure needs;
* no level-three orientation, dual-weight, active-node or chunk payload exists for the `e7987…`
  candidate; the ones that do exist belong to the refuted `eab2c7…` certificate and are
  provenance-quarantined.

What *is* committed, and is used here verbatim, is the arithmetic: the three-branch root rate
`SimplifiedExponentRootRecurrence.rootBranchRate`, the quotient-parametric level-three regional
rate `SimplifiedExponentLevelThreeRecurrence.regionBranchRateFor` at the total-weight slot
`TotalQuotientCompleteSplitRecurrence.totalWeightSupportSlot`, the exact signed-log forms of both
together with their evaluation theorems, the kernel-checked lower-bound certificates of
`MatrixMultiplication/SignedDyadicLogCertificate.lean`, and the six-decimal stage floors of
`Generated/TotalQuotientExponentStageFloors.lean`.

## The one chain, factored out

Every one of the eighteen committed level-four branch files
`Generated/TotalQuotientExponentLevelFourAnalyticRegion{r}Branch{b}.lean` ends with the same five
step calculation

```text
floor ≤ lower = certificate.lower ≤ Form.eval bits certificate.form
             = Form.eval bits (Form.sum forms) = rate
```

`BranchFloorCertificate` is exactly that chain's data, and `BranchFloorCertificate.floor_le_rate`
is the chain.  A producer that emits chunked forms, their summed lower-bound certificate, the
rational endpoint, and one evaluation equality against the recurrence's own form gets the bridge
hypothesis in the endpoint's shape with no further arithmetic.

`rootBranchCertificateOfForms` and `levelThreeBranchCertificateOfForms` do the last step for the
producer: they consume an *evaluation* equality against `rootBranchForm` / `regionBranchFormFor`,
so no shard ever has to be compared to the whole parent form syntactically.

## Imports

Deliberately light — the two recurrence APIs, the total-weight slot, the generic certificate
layer, and the small floor table.  No primary-table cone is imported, so this seam cannot become
another heavyweight kernel dependency; the generated payload arrives later, in the producer's own
modules, and meets these statements from outside.
-/

namespace MatrixMultiplication.TotalQuotientExponentOuterFloorBridge

open MatrixMultiplication.Generated.TotalQuotientExponentStageFloors
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

noncomputable section

/-! ## The reusable directed branch-floor checker -/

/-- **One directed regional branch floor, in certificate form.**

The data a producer emits for a single `(region, branch)` pair: the bounded exact forms it sharded
the branch into, their summed kernel-checked lower-bound certificate, the rational endpoint it
adds up to, and the three equalities tying those to each other and to the semantic rate.

Keeping this as a structure rather than a hypothesis bundle means the eighteen-fold family
assembly below is a single `fun` and the producer's file needs no `calc` at all. -/
structure BranchFloorCertificate (bits : ℕ) (floor rate : ℝ) where
  /-- The bounded shards the branch was split into. -/
  forms : List Form
  /-- Their summed kernel-checked lower-bound certificate. -/
  certificate : LowerBound bits
  /-- The rational endpoint carried by that certificate. -/
  lower : ℝ
  /-- The certificate's exact form is the sum of the shards. -/
  certificate_form : certificate.form = Form.sum forms
  /-- The stated endpoint is the certificate's endpoint. -/
  lower_eq_certificate_lower : lower = certificate.lower
  /-- The generated six-decimal floor is below that endpoint. -/
  floor_le_lower : floor ≤ lower
  /-- The semantic branch rate is the exact value of the summed shards. -/
  rate_eq : rate = Form.eval bits (Form.sum forms)

/-- **The directed floor transport.**  The five-step chain that every committed level-four branch
file writes out by hand, proved once. -/
theorem BranchFloorCertificate.floor_le_rate {bits : ℕ} {floor rate : ℝ}
    (data : BranchFloorCertificate bits floor rate) : floor ≤ rate := by
  calc
    floor ≤ data.lower := data.floor_le_lower
    _ = data.certificate.lower := data.lower_eq_certificate_lower
    _ ≤ Form.eval bits data.certificate.form := data.certificate.lower_le_eval
    _ = Form.eval bits (Form.sum data.forms) :=
      congrArg (Form.eval bits) data.certificate_form
    _ = rate := data.rate_eq.symm

/-- **The absent-support certificate.**  A region whose retained family is empty has the empty
shard list and hence exact rate `0`, so any floor at or below `0` dominates it.

This is not a degenerate convenience: in the `e7987…` total-weight candidate the root family's
regions `2` and `3` are exactly of this kind — `rootFloorNumerators` is `#[1157, 2677749, 0, 0,
2074, 678]`, and `rootFloor_eq_zero_two` / `rootFloor_eq_zero_three` below discharge the `hfloor`
premise outright — so six of the eighteen root inequalities need no numerical payload at all. -/
def BranchFloorCertificate.ofEmpty (bits : ℕ) {floor rate : ℝ}
    (hfloor : floor ≤ 0) (hrate : rate = 0) :
    BranchFloorCertificate bits floor rate where
  forms := []
  certificate := LowerBound.constant bits 0
  lower := 0
  certificate_form := rfl
  lower_eq_certificate_lower := by
    simp [LowerBound.constant]
  floor_le_lower := hfloor
  rate_eq := by
    rw [hrate]
    simp [Form.sum, Form.eval, Form.termsValue, Form.zero]

/-- The total-weight candidate retains no root family in region `2`: its generated floor is
exactly `0`. -/
theorem rootFloor_eq_zero_two : rootFloor ⟨2, by decide⟩ = 0 := by
  norm_num [rootFloor, rootFloorNumerators, denominator]

/-- The total-weight candidate retains no root family in region `3`: its generated floor is
exactly `0`. -/
theorem rootFloor_eq_zero_three : rootFloor ⟨3, by decide⟩ = 0 := by
  norm_num [rootFloor, rootFloorNumerators, denominator]

/-- **The family assembly.**  A certificate at every `(index, branch)` pair is the componentwise
domination the endpoint's hypotheses are stated as.

Stated for an arbitrary finite index and an arbitrary per-pair denominator, because the root and
level-three families differ in both: the root branches carry the top and child denominators of
`rootBranchForm`, the level-three branches all carry
`(referenceBits + compatibilityExtraBits) + outerBits`. -/
theorem floor_le_rate_of_branchCertificates {Index : Type*}
    (bits : Index → Fin 3 → ℕ) (floor : Index → ℝ) (rate : Index → Fin 3 → ℝ)
    (certificates : ∀ index branch,
      BranchFloorCertificate (bits index branch) (floor index) (rate index branch))
    (index : Index) (branch : Fin 3) : floor index ≤ rate index branch :=
  (certificates index branch).floor_le_rate

/-! ## The root family -/

section Root

open MatrixMultiplication.SimplifiedExponentRootRecurrence

variable {A X Y Z : Type*}

/-- **The root rate in the endpoint's shape.**  A `Region`-indexed root-row family, evaluated at
the committed three-branch root rate: logical `X` at the top denominator, and the two
compatibility branches at the child denominator. -/
def rootRateOfRows (topBits childBits : ℕ)
    (coordX : A → X) (coordY : A → Y) (coordZ : A → Z)
    (rows : Region → RootRows A X Y Z) (region : Region) (branch : Fin 3) : ℝ :=
  rootBranchRate topBits childBits coordX coordY coordZ (rows region) branch

/-- The denominator `rootBranchForm` uses for one root branch: the top denominator on the logical
`X` branch and the child denominator on the two compatibility branches. -/
def rootBranchBits (topBits childBits : ℕ)
    (coordX : A → X) (coordY : A → Y) (coordZ : A → Z)
    (rows : Region → RootRows A X Y Z) (region : Region) (branch : Fin 3) : ℕ :=
  (rootBranchForm topBits childBits coordX coordY coordZ (rows region) branch).1

/-- **The root producer's constructor.**  Everything a generated root branch file has to supply:
its bounded shards, their summed certificate, the rational endpoint, the floor comparison, and one
*evaluation* equality between the shard sum and the recurrence's own exact branch form.

The evaluation equality is deliberately not a syntactic one: `LowerBound.sum_form` and
`LowerBound.sum_lower_le_eval_sum_of_forall₂` let independently normalized shards be reassembled
by value, so no producer ever reduces a whole-branch canonical form. -/
def rootBranchCertificateOfForms (topBits childBits : ℕ)
    (coordX : A → X) (coordY : A → Y) (coordZ : A → Z)
    (rows : Region → RootRows A X Y Z) (region : Region) (branch : Fin 3)
    (forms : List Form)
    (certificate : LowerBound (rootBranchBits topBits childBits coordX coordY coordZ rows
      region branch))
    (lower : ℝ)
    (hform : certificate.form = Form.sum forms)
    (hlower : lower = certificate.lower)
    (hfloor : rootFloor region ≤ lower)
    (heval :
      Form.eval (rootBranchBits topBits childBits coordX coordY coordZ rows region branch)
          (Form.sum forms) =
        Form.eval (rootBranchBits topBits childBits coordX coordY coordZ rows region branch)
          (rootBranchForm topBits childBits coordX coordY coordZ (rows region) branch).2) :
    BranchFloorCertificate
      (rootBranchBits topBits childBits coordX coordY coordZ rows region branch)
      (rootFloor region)
      (rootRateOfRows topBits childBits coordX coordY coordZ rows region branch) where
  forms := forms
  certificate := certificate
  lower := lower
  certificate_form := hform
  lower_eq_certificate_lower := hlower
  floor_le_lower := hfloor
  rate_eq := by
    rw [heval]
    exact (rootBranchForm_eval topBits childBits coordX coordY coordZ (rows region) branch).symm

/-- **`hroot`, from eighteen directed root branch certificates.**

The statement is verbatim the `hroot` hypothesis of
`MatrixMultiplication.TotalWeightEndpointComposition.omega_lt_236999_final`, at
`rootRate := rootRateOfRows …`.  The root-row family is a named parameter because no reconstruction
of it from the committed `e7987…` primary tables exists yet. -/
theorem rootFloor_le_rootBranchRate (topBits childBits : ℕ)
    (coordX : A → X) (coordY : A → Y) (coordZ : A → Z)
    (rows : Region → RootRows A X Y Z)
    (certificates : ∀ region branch,
      BranchFloorCertificate
        (rootBranchBits topBits childBits coordX coordY coordZ rows region branch)
        (rootFloor region)
        (rootRateOfRows topBits childBits coordX coordY coordZ rows region branch)) :
    ∀ region branch, rootFloor region ≤
      rootRateOfRows topBits childBits coordX coordY coordZ rows region branch :=
  fun region branch => (certificates region branch).floor_le_rate

/-- The total-weight candidate's root geometry: `153` ordered root shapes, all three logical roles
reading a `17`-valued physical coordinate.  This is the shape the committed root dual chunk
`Generated/TotalQuotientPrimaryRootDualData0.lean` is serialized at — its row width is
`Manifest.rootDualRowWidth = 3 * 17`. -/
def totalQuotientRootRate (topBits childBits : ℕ)
    (rows : Region → RootRows (Fin rootShapeCount) (Fin 17) (Fin 17) (Fin 17))
    (region : Region) (branch : Fin 3) : ℝ :=
  rootRateOfRows topBits childBits (rootCoordinate 0) (rootCoordinate 1) (rootCoordinate 2)
    rows region branch

/-- `hroot` at the total-weight candidate's root geometry. -/
theorem rootFloor_le_totalQuotientRootRate (topBits childBits : ℕ)
    (rows : Region → RootRows (Fin rootShapeCount) (Fin 17) (Fin 17) (Fin 17))
    (certificates : ∀ region branch,
      BranchFloorCertificate
        (rootBranchBits topBits childBits (rootCoordinate 0) (rootCoordinate 1)
          (rootCoordinate 2) rows region branch)
        (rootFloor region)
        (totalQuotientRootRate topBits childBits rows region branch)) :
    ∀ region branch, rootFloor region ≤ totalQuotientRootRate topBits childBits rows region branch :=
  rootFloor_le_rootBranchRate topBits childBits (rootCoordinate 0) (rootCoordinate 1)
    (rootCoordinate 2) rows certificates

end Root

/-! ## The level-three family -/

section LevelThree

open MatrixMultiplication.SimplifiedExponentLevelThreeRecurrence
open MatrixMultiplication.SimplifiedVolumeReconstruction
open MatrixMultiplication.TotalQuotientCompleteSplitRecurrence (totalWeightSupportSlot)

/-- The common denominator of every level-three regional branch form: the parent's child rows sit
at `2 ^ (referenceBits + compatibilityExtraBits)` and the outer occurrence mass at `2 ^ outerBits`,
so `(12 + 24) + 32 = 68`. -/
def levelThreeBits : ℕ := (referenceBits + compatibilityExtraBits) + outerBits

/-- **The level-three rate in the endpoint's shape.**

The committed quotient-parametric regional branch rate, pinned at the total-weight quotient's slot
action.  `data` and `massThree` are the certificate's own primary tables and cached level-three
occurrence masses; `orders` and `weights` are the per-region orientation and per-node integer dual
family. -/
def levelThreeRate (data : PrimaryTables) (massThree : Array ℕ)
    (orders : ℕ → CoordinateOrder) (weights : ℕ → DualWeights)
    (region : Region) (branch : Fin 3) : ℝ :=
  regionBranchRateFor totalWeightSupportSlot data massThree orders weights region.val branch

/-- The repeated `(X, Z, Y)` regional orientation.

This is *not* optimizer output: the exporter fixes `coordinate_map = [0, 2, 1]` independently of
the certificate, and the committed `e7987…` level-four payload
`Generated/TotalQuotientExponentLevelFourOrientation.lean` is literally this order.  It is
recorded here so a producer does not have to rediscover it, but the level-three theorems below
still quantify over `orders`, because the level-three orientation payload for this candidate has
never been exported and the identification is not proved anywhere. -/
def repeatedXZYOrder (_region : ℕ) : CoordinateOrder := ⟨0, 2, 1⟩

/-- Each repeated regional order is nevertheless an individual coordinate permutation. -/
theorem repeatedXZYOrder_isPermutation (region : ℕ) :
    (repeatedXZYOrder region).IsPermutation := by
  simp [repeatedXZYOrder, CoordinateOrder.IsPermutation]

/-- **The level-three producer's constructor.**  As on the root side, the producer supplies its
bounded shards, their summed certificate, the endpoint, the floor comparison, and one *evaluation*
equality against the recurrence's own regional branch form. -/
def levelThreeBranchCertificateOfForms (data : PrimaryTables) (massThree : Array ℕ)
    (orders : ℕ → CoordinateOrder) (weights : ℕ → DualWeights)
    (region : Region) (branch : Fin 3)
    (forms : List Form) (certificate : LowerBound levelThreeBits) (lower : ℝ)
    (hform : certificate.form = Form.sum forms)
    (hlower : lower = certificate.lower)
    (hfloor : levelThreeFloor region ≤ lower)
    (heval : Form.eval levelThreeBits (Form.sum forms) =
      Form.eval levelThreeBits
        (regionBranchFormFor totalWeightSupportSlot data massThree orders weights
          region.val branch)) :
    BranchFloorCertificate levelThreeBits (levelThreeFloor region)
      (levelThreeRate data massThree orders weights region branch) where
  forms := forms
  certificate := certificate
  lower := lower
  certificate_form := hform
  lower_eq_certificate_lower := hlower
  floor_le_lower := hfloor
  rate_eq := by
    rw [heval]
    exact (regionBranchFormFor_eval totalWeightSupportSlot data massThree orders weights
      region.val branch).symm

/-- **`hlevelThree`, from eighteen directed level-three branch certificates.**

Verbatim the `hlevelThree` hypothesis of
`MatrixMultiplication.TotalWeightEndpointComposition.omega_lt_236999_final`, at
`levelThreeRate := levelThreeRate …`. -/
theorem levelThreeFloor_le_branchRate (data : PrimaryTables) (massThree : Array ℕ)
    (orders : ℕ → CoordinateOrder) (weights : ℕ → DualWeights)
    (certificates : ∀ region branch,
      BranchFloorCertificate levelThreeBits (levelThreeFloor region)
        (levelThreeRate data massThree orders weights region branch)) :
    ∀ region branch,
      levelThreeFloor region ≤ levelThreeRate data massThree orders weights region branch :=
  fun region branch => (certificates region branch).floor_le_rate

end LevelThree

end

end MatrixMultiplication.TotalQuotientExponentOuterFloorBridge
