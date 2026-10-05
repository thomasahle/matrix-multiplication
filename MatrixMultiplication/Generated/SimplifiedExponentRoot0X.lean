import MatrixMultiplication.SimplifiedExponentRootRecurrence
import MatrixMultiplication.SignedDyadicLogCanonical

/-! Exact root retained-rate recurrence data; certificate SHA-256 `eab2c7aee9904dac6a716369cfa3460fde34d2c36f2fd21a952601f8c3cb8082`. -/

/-! **PROVENANCE QUARANTINE — R7, 2026-08-28 (eab2c7 retained side).**  The retained exponent
`8.200434` this payload feeds is computed from the **ARCHIVED (uncorrected)** evaluator
complement table.  Under the corrected table the same certificate yields `8.160594`, which is
below the `8.2` floor, so the payload was **refuted for endpoint use on 2026-08-28** (commit
`8a8e110`'s analysis).  Every declaration below stays kernel-true *as a statement about the
emitted arrays*; none of it may instantiate an `hsemantic` obligation or any retained-exponent
endpoint.  Listed in `scripts/artifact_provenance_quarantine.txt` and enforced by
`scripts/check_artifact_provenance.sh`.
-/

namespace MatrixMultiplication.Generated.SimplifiedExponentRoot.Root0X

open MatrixMultiplication.SignedDyadicLogForm
open MatrixMultiplication.SimplifiedExponentRootRecurrence

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

def referenceNumerators : Array ℕ := #[
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 1, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 6, 12, 12, 6, 2, 0, 0, 0, 0, 0,
    0, 0, 2, 9, 22, 27, 22, 9, 2, 0, 0, 0, 0, 0, 0, 6, 22, 38, 40, 22, 6, 0, 0, 0, 0, 0, 1, 14, 27,
    38, 27, 12, 1, 0, 0, 0, 0, 4, 14, 22, 22, 12, 2, 0, 0, 0, 0, 1, 6, 9, 6, 1, 0, 0, 0, 0, 0, 2,
    2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
  ]
def weightXNumerators : Array ℕ := #[
    256, 2630, 11373, 29625, 54070, 73788, 76647, 59641, 33884, 14660, 7235, 5946, 5312, 3168,
    2344, 6070, 29517
  ]
def weightYNumerators : Array ℕ := #[
    256, 2510, 10629, 27542, 50246, 68402, 70849, 54796, 30793, 13141, 6575, 5535, 4929, 2896,
    2223, 6014, 28657
  ]
def weightZNumerators : Array ℕ := #[
    256, 2688, 11791, 31006, 56946, 77840, 80609, 62570, 35294, 15132, 7476, 6143, 5456, 3199,
    2384, 6077, 29562
  ]

def referenceNumerator (state : Fin rootShapeCount) : ℕ :=
  referenceNumerators[state.val]?.getD 0
def weightX (value : Fin 17) : ℕ := weightXNumerators[value.val]?.getD 0
def weightY (value : Fin 17) : ℕ := weightYNumerators[value.val]?.getD 0
def weightZ (value : Fin 17) : ℕ := weightZNumerators[value.val]?.getD 0

def rows : RootRows (Fin rootShapeCount) (Fin 17) (Fin 17) (Fin 17) :=
  { states := List.ofFn id
    referenceNumerator := referenceNumerator
    referenceList := [
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 1, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 6, 12, 12, 6, 2, 0, 0, 0, 0, 0,
    0, 0, 2, 9, 22, 27, 22, 9, 2, 0, 0, 0, 0, 0, 0, 6, 22, 38, 40, 22, 6, 0, 0, 0, 0, 0, 1, 14, 27,
    38, 27, 12, 1, 0, 0, 0, 0, 4, 14, 22, 22, 12, 2, 0, 0, 0, 0, 1, 6, 9, 6, 1, 0, 0, 0, 0, 0, 2,
    2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
  ]
    marginalXList := [
    0, 0, 4, 40, 93, 134, 120, 76, 23, 4, 0, 0, 0, 0, 0, 0, 0
  ]
    weightX := weightX
    weightY := weightY
    weightZ := weightZ
    logicalY := ⟨[], [], []⟩
    logicalZ := ⟨[], [], []⟩ }

def expectedForm : Form := {
  constantNumerator := 0
  terms := [⟨2, -16⟩,
      ⟨4, -12⟩,
      ⟨6, -36⟩,
      ⟨9, -27⟩,
      ⟨12, -48⟩,
      ⟨14, -28⟩,
      ⟨22, -132⟩,
      ⟨23, -23⟩,
      ⟨27, -81⟩,
      ⟨38, -76⟩,
      ⟨40, -80⟩,
      ⟨76, -76⟩,
      ⟨93, -93⟩,
      ⟨120, -120⟩,
      ⟨134, -134⟩,
      ⟨494, 988⟩,
      ⟨10629, 6⟩,
      ⟨11373, 4⟩,
      ⟨11791, 4⟩,
      ⟨13141, 4⟩,
      ⟨14660, 4⟩,
      ⟨15132, 4⟩,
      ⟨27542, 44⟩,
      ⟨29625, 40⟩,
      ⟨30793, 23⟩,
      ⟨31006, 40⟩,
      ⟨33884, 23⟩,
      ⟨35294, 23⟩,
      ⟨50246, 93⟩,
      ⟨54070, 93⟩,
      ⟨54796, 72⟩,
      ⟨56946, 93⟩,
      ⟨59641, 76⟩,
      ⟨62570, 76⟩,
      ⟨68402, 132⟩,
      ⟨70849, 120⟩,
      ⟨73788, 134⟩,
      ⟨76647, 120⟩,
      ⟨77840, 134⟩,
      ⟨80609, 120⟩,
      ⟨5664145184412065, -494⟩] }

theorem recurrence_normalize :
    Form.fastCanonical
      (rootXForm 20 (rootCoordinate 0) (rootCoordinate 1) (rootCoordinate 2) rows) =
      expectedForm := by
  decide

end MatrixMultiplication.Generated.SimplifiedExponentRoot.Root0X
