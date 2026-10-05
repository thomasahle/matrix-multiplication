/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import MatrixMultiplication.TotalQuotientExponentStageAggregation
import MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoData
import MatrixMultiplication.TotalQuotientLevelTwoActiveEdgeShards

/-!
# The level-two branch-floor certificate of the total-weight candidate

`MatrixMultiplication/TotalQuotientExponentLevelTwoRecurrence.lean` reduces the inner half of the
`C′` acceptance split to a single finite obligation, `BranchFloorCertified data massThree`: the
certified rational floor
`Generated.TotalQuotientExponentStageFloors.levelTwoFloor () = 1 742 834 / 1 000 000` lies below all
three exact level-two branch rates.  This module discharges that obligation outright, so
`TotalQuotientExponentStageAggregation.innerRetainedFloor_le_levelTwoFamilyExponent` becomes
unconditional, and `TotalWeightAcceptanceAssembly.LevelTwoTableInput` loses its `certificate` field
as a residual.

It is the Lean side of `better_bound/total_weight_level_two_emission/HANDOFF.md` §4, over the
generated payload of certificate SHA-256
`e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3` emitted by that handoff's
`recurrence_variant/` invocation.

## The table pair

`certifiedTables` is `TotalQuotientVolumeReconstruction.primaryTables`, the seven sparse primary
families of that certificate, and `certifiedMassThree` is the level-two checker's cached top-pair
pushforward `MassThree.expectedNumerators`.

The pushforward is taken as the **cached array**, not as
`SimplifiedVolumeReconstruction.levelThreeMassNumerators certifiedTables`.  The two are equal — that
is `Generated.TotalQuotientVolumeRecurrence.Mass3.recurrence_eq` composed with the emitted
`massThree_expected_eq` — but proving it requires the whole `TotalQuotientVolumeRecurrenceMass3` /
`…TopScatter` tranche, which nothing else here needs.  This is a deliberate, recorded narrowing:
the interface `TotalQuotientExponentLevelTwoRecurrence.BranchFloorCertified` and
`TotalWeightAcceptanceAssembly.LevelTwoTableInput` both take the table and the mass-three array as
an *independent pair*, so the certificate below is exactly as strong as its statement and no
stronger.  Identifying `certifiedMassThree` with the recurrence's own pushforward is a separate,
still-open step; it is not used, and not claimed, anywhere below.

## Why this module and not the emitted aggregate

The emitted `recurrence_variant/TotalQuotientExponentLevelTwoRecurrenceData.lean` also concludes two
*convenience* theorems about `TotalQuotientVolumeReconstruction.reconstructedBranchRate`, a
definition that does not exist in the repository (HANDOFF §4 checklist step 3), and for those it
imports `Generated.TotalQuotientVolumeRecurrenceMass3`.  Since the two defs it needs would have to
be reachable from that generated module's own imports, the aggregate cannot be landed verbatim
without editing a generated file.  The three parts of it that `branchFloorCertified_of_normalizedForms`
actually consumes — `activeEdges_eq`, `activeInputs_eq_expected` and the three
`expectedBranch{i}_normalize` — are reproduced here, with the same proof scripts, over the same
generated chunks; the one exception is `activeEdges_eq`, whose single `decide` exceeds the
project's original `-M 3000` compiler budget and is therefore sharded in
`MatrixMultiplication/TotalQuotientLevelTwoActiveEdgeShards.lean`.  The other `23` emitted modules are landed verbatim in `Generated/`.

## Fidelity of the landed generated payload

The `23` landed modules were checked by the emission report
(`better_bound/total_weight_level_two_emission/HANDOFF.md` §3) to normalise, under exactly the six
declared name substitutions, to byte-identical committed `Generated/SimplifiedExponentLevelTwo*`
text, with a single intended delta: `commonFloor := 871417/500000` here against the sorted-pair
`4357/2500`.  The `428`-module stale module-doc adjective filed on the board concerns the emitted
*level-three* families and does not occur in any of these files; their headers carry only the
certificate digest.

The committed sorted-pair family is *not* usable for this purpose, and not merely for the floor
constant: `Generated/SimplifiedExponentLevelTwo*` was emitted from certificate `e7987d7f…` while the
committed `Generated/SimplifiedVolume*` primary tables carry certificate `eab2c7ae…`, so
`SimplifiedExponentLevelTwoRecurrenceChunk0.inputs_eq` is **false** as stated and fails `decide`.
That family sits outside every configured build target, which is why the mismatch was latent; it is
reported on the board.

## Margins

`Branch{i}.branchFloor` is the rigorous directed floor `constantNumerator / 2 ^ 56 − ceiling`:

| branch | `branchFloor` | margin over `1.742834` |
| --- | --- | --- |
| 0 | `1.743354415956214` | `5.204e-04` |
| 1 | `1.743074176360053` | `2.402e-04` |
| 2 | `1.742834313208066` | `3.132e-07` |

Branch `2` is the bottleneck.  All comparisons are exact rational arithmetic on integer literals.

## What is *not* certified here

Only the level-two (inner) stage.  The root, level-four and level-three floors of
`Generated/TotalQuotientExponentStageFloors` still have no Lean recurrence for either candidate —
item 3 of `MatrixMultiplication/TotalQuotientExponentStageAggregation.lean`'s "exact missing
artifacts", untouched here.
-/

namespace MatrixMultiplication.TotalQuotientExponentLevelTwoCertificate

open MatrixMultiplication.Generated.TotalQuotientExponentLevelTwo
open MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoRecurrence
open MatrixMultiplication.SignedDyadicLogForm
open MatrixMultiplication.SimplifiedExponentRecurrence
open MatrixMultiplication.SimplifiedExponentRecurrence.Chunked
open MatrixMultiplication.SimplifiedVolumeReconstruction

-- The three `decide` reductions below are the emitted aggregate's own calls over generated
-- certificate tables; they carry the generator's elaboration budget verbatim
-- (`Generated/TotalQuotientExponentLevelTwoRecurrenceChunk*.lean` set the same two options).
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-! ## The active-edge list and the eighteen edge-input chunks

Reproduced from the emitted aggregate, with its proof scripts unchanged. -/

/-- The recurrence's own active-edge list is the one the level-two checker cached; the eight-shard
kernel reduction lives in `MatrixMultiplication/TotalQuotientLevelTwoActiveEdgeShards.lean`, which
also records why the emitted aggregate's single `decide` does not fit the project's original
`-M 3000` compiler budget. -/
theorem activeEdges_eq : activeEdges = MassThree.expectedActiveEdges.toList :=
  TotalQuotientLevelTwoActiveEdgeShards.activeEdges_eq

/-- The eighteen exported edge-input chunks, in order. -/
def expectedInputChunks : List (List EdgeInput) :=
  [Chunk0.expectedInputs,
    Chunk1.expectedInputs,
    Chunk2.expectedInputs,
    Chunk3.expectedInputs,
    Chunk4.expectedInputs,
    Chunk5.expectedInputs,
    Chunk6.expectedInputs,
    Chunk7.expectedInputs,
    Chunk8.expectedInputs,
    Chunk9.expectedInputs,
    Chunk10.expectedInputs,
    Chunk11.expectedInputs,
    Chunk12.expectedInputs,
    Chunk13.expectedInputs,
    Chunk14.expectedInputs,
    Chunk15.expectedInputs,
    Chunk16.expectedInputs,
    Chunk17.expectedInputs]

/-- The full exported edge-input list of the level-two stage. -/
def expectedInputs : List EdgeInput := expectedInputChunks.flatten

/-- The recurrence's active inputs over the total-weight primary tables are the exported list.
This is the table-dependent half of the certificate; each chunk contributes its own kernel-checked
`inputs_eq`. -/
theorem activeInputs_eq_expected :
    activeInputsWithMassThree TotalQuotientVolumeReconstruction.primaryTables
        MassThree.expectedNumerators =
      expectedInputs := by
  unfold activeInputsWithMassThree activeInputChunksWithMassThree
    activeEdgeInputRangeWithMassThree
  rw [activeEdges_eq]
  unfold expectedInputs expectedInputChunks
  rw [Chunk0.inputs_eq, Chunk1.inputs_eq, Chunk2.inputs_eq, Chunk3.inputs_eq,
    Chunk4.inputs_eq, Chunk5.inputs_eq, Chunk6.inputs_eq, Chunk7.inputs_eq,
    Chunk8.inputs_eq, Chunk9.inputs_eq, Chunk10.inputs_eq, Chunk11.inputs_eq,
    Chunk12.inputs_eq, Chunk13.inputs_eq, Chunk14.inputs_eq, Chunk15.inputs_eq,
    Chunk16.inputs_eq, Chunk17.inputs_eq]

/-! ## The three form normalizations -/

/-- Exported branch `0` is the normal form of the exact level-two branch form. -/
theorem expectedBranch0_normalize :
    Form.normalize (inputBranchForm expectedInputs 0) = Branch0.expectedForm := by
  decide

/-- Exported branch `1` is the normal form of the exact level-two branch form. -/
theorem expectedBranch1_normalize :
    Form.normalize (inputBranchForm expectedInputs 1) = Branch1.expectedForm := by
  decide

/-- Exported branch `2` is the normal form of the exact level-two branch form. -/
theorem expectedBranch2_normalize :
    Form.normalize (inputBranchForm expectedInputs 2) = Branch2.expectedForm := by
  decide

/-! ## The certified table pair -/

noncomputable section

/-- The primary tables the certificate is stated over: the seven sparse families of certificate
`e7987d7f…`. -/
def certifiedTables : PrimaryTables := TotalQuotientVolumeReconstruction.primaryTables

/-- The cached level-three mass numerators the level-two checker consumes. -/
def certifiedMassThree : Array ℕ := MassThree.expectedNumerators

/-- The exported target forms, in branch order. -/
def certifiedTargets : Fin 3 → Form :=
  ![Branch0.expectedForm, Branch1.expectedForm, Branch2.expectedForm]

/-! ## The two halves of `branchFloorCertified_of_normalizedForms` -/

/-- `hnormalize`: the exact branch forms of the certified table pair normalize to the exported
targets. -/
theorem branchForm_normalize (coordinate : Fin 3) :
    Form.normalize
        (TotalQuotientExponentLevelTwoRecurrence.branchForm certifiedTables certifiedMassThree
          coordinate) =
      certifiedTargets coordinate := by
  have hform :
      TotalQuotientExponentLevelTwoRecurrence.branchForm certifiedTables certifiedMassThree
          coordinate =
        inputBranchForm expectedInputs coordinate := by
    show activeBranchFormWithMassThree TotalQuotientVolumeReconstruction.primaryTables
      MassThree.expectedNumerators coordinate = _
    unfold activeBranchFormWithMassThree
    rw [activeInputs_eq_expected]
  rw [hform]
  fin_cases coordinate
  · exact expectedBranch0_normalize
  · exact expectedBranch1_normalize
  · exact expectedBranch2_normalize

/-- The certified stage floor is the emitted common floor: `1 742 834 / 1 000 000 =
871 417 / 500 000`. -/
theorem levelTwoFloor_eq_commonFloor :
    Generated.TotalQuotientExponentStageFloors.levelTwoFloor () = commonFloor := by
  norm_num [Generated.TotalQuotientExponentStageFloors.levelTwoFloor,
    Generated.TotalQuotientExponentStageFloors.denominator, commonFloor]

/-- `hfloor`: the certified stage floor is below every exported target form.  Exact, at the
bottleneck margin `3.132e-07` on branch `2`. -/
theorem levelTwoFloor_le_target (coordinate : Fin 3) :
    Generated.TotalQuotientExponentStageFloors.levelTwoFloor () ≤
      Form.eval levelTwoFormBits (certifiedTargets coordinate) := by
  rw [levelTwoFloor_eq_commonFloor]
  fin_cases coordinate
  · exact commonFloor_le_branch0
  · exact commonFloor_le_branch1
  · exact commonFloor_le_branch2

/-! ## The certificate -/

/-- **The level-two branch-floor certificate, discharged.**

This is `h4.certificate` of `TotalWeightAcceptanceAssembly.LevelTwoTableInput` and the last
hypothesis of `TotalQuotientExponentStageAggregation.innerRetainedFloor_le_levelTwoFamilyExponent`.
It is proved outright from generated data; nothing about it is assumed. -/
theorem branchFloorCertified :
    TotalQuotientExponentLevelTwoRecurrence.BranchFloorCertified
      certifiedTables certifiedMassThree :=
  TotalQuotientExponentLevelTwoRecurrence.branchFloorCertified_of_normalizedForms
    certifiedTables certifiedMassThree certifiedTargets branchForm_normalize levelTwoFloor_le_target

/-! ## The inner half of the `C′` split, unconditionally -/

/-- **The inner acceptance floor is unconditional.**  `innerRetainedFloor = 433/250 = 1.732` is a
lower bound for the exact level-two family exponent of the certified table pair, with no remaining
hypothesis.  Certified margin `1.742834 − 1.732 = 1.083e-02`.

This is `TotalQuotientExponentStageAggregation.innerRetainedFloor_le_levelTwoFamilyExponent` with
its certificate argument supplied. -/
theorem innerRetainedFloor_le_levelTwoFamilyExponent :
    TotalWeightAcceptanceFloors.innerRetainedFloor ≤
      AlgebraicComplexity.RetainedExponentAggregation.familyExponent
        (TotalQuotientExponentLevelTwoRecurrence.familyRate certifiedTables certifiedMassThree) :=
  TotalQuotientExponentStageAggregation.innerRetainedFloor_le_levelTwoFamilyExponent
    certifiedTables certifiedMassThree branchFloorCertified

/-- The same statement against the concrete level-two bottleneck, which is the number
`TotalWeightAcceptanceAssembly.LevelTwoTableInput.realizes` compares against. -/
theorem innerRetainedFloor_le_retainedExponent :
    TotalWeightAcceptanceFloors.innerRetainedFloor ≤
      TotalQuotientExponentLevelTwoRecurrence.retainedExponent
        certifiedTables certifiedMassThree := by
  have h := TotalQuotientExponentLevelTwoRecurrence.innerRetainedFloor_le_retainedExponent
    certifiedTables certifiedMassThree branchFloorCertified
  simpa only [TotalWeightAcceptanceFloors.innerRetainedFloor] using h

end

end MatrixMultiplication.TotalQuotientExponentLevelTwoCertificate
