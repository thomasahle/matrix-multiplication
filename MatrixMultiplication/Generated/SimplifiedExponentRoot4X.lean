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

namespace MatrixMultiplication.Generated.SimplifiedExponentRoot.Root4X

open MatrixMultiplication.SignedDyadicLogForm
open MatrixMultiplication.SimplifiedExponentRootRecurrence

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

def referenceNumerators : Array ℕ := #[
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 2, 4, 6, 4, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 10, 20, 20, 10, 4, 0, 0, 0, 0,
    0, 0, 0, 4, 13, 34, 48, 34, 13, 4, 0, 0, 0, 0, 0, 2, 10, 34, 62, 64, 34, 10, 2, 0, 0, 0, 0, 4,
    20, 48, 64, 48, 20, 4, 0, 0, 0, 0, 6, 20, 34, 34, 20, 6, 0, 0, 0, 0, 4, 10, 13, 10, 4, 0, 0, 0,
    0, 2, 4, 4, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0
  ]
def weightXNumerators : Array ℕ := #[
    256, 2676, 11849, 31770, 59835, 84296, 90131, 71906, 41467, 17816, 8523, 6848, 6090, 3557,
    2512, 6190, 26431
  ]
def weightYNumerators : Array ℕ := #[
    256, 2515, 10775, 28535, 53531, 75199, 80264, 63694, 36417, 15547, 7571, 6231, 5509, 3209,
    2373, 6173, 24823
  ]
def weightZNumerators : Array ℕ := #[
    256, 2692, 11897, 31732, 59462, 83314, 88722, 70979, 41267, 17933, 8542, 6771, 6092, 3622,
    2514, 5983, 26712
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
    0, 0, 0, 0, 0, 0, 2, 4, 6, 4, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 10, 20, 20, 10, 4, 0, 0, 0, 0,
    0, 0, 0, 4, 13, 34, 48, 34, 13, 4, 0, 0, 0, 0, 0, 2, 10, 34, 62, 64, 34, 10, 2, 0, 0, 0, 0, 4,
    20, 48, 64, 48, 20, 4, 0, 0, 0, 0, 6, 20, 34, 34, 20, 6, 0, 0, 0, 0, 4, 10, 13, 10, 4, 0, 0, 0,
    0, 2, 4, 4, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0
  ]
    marginalXList := [
    0, 0, 18, 68, 150, 218, 208, 120, 41, 12, 0, 0, 0, 0, 0, 0, 0
  ]
    weightX := weightX
    weightY := weightY
    weightZ := weightZ
    logicalY := ⟨[], [], []⟩
    logicalZ := ⟨[], [], []⟩ }

def expectedForm : Form := {
  constantNumerator := 0
  terms := [⟨2, -12⟩,
      ⟨4, -48⟩,
      ⟨6, -18⟩,
      ⟨10, -60⟩,
      ⟨12, -12⟩,
      ⟨13, -39⟩,
      ⟨18, -18⟩,
      ⟨20, -120⟩,
      ⟨34, -204⟩,
      ⟨41, -41⟩,
      ⟨48, -144⟩,
      ⟨62, -62⟩,
      ⟨64, -128⟩,
      ⟨68, -68⟩,
      ⟨120, -120⟩,
      ⟨150, -150⟩,
      ⟨208, -208⟩,
      ⟨218, -218⟩,
      ⟨835, 1670⟩,
      ⟨10775, 18⟩,
      ⟨11849, 18⟩,
      ⟨11897, 18⟩,
      ⟨15547, 12⟩,
      ⟨17816, 12⟩,
      ⟨17933, 12⟩,
      ⟨28535, 68⟩,
      ⟨31732, 68⟩,
      ⟨31770, 68⟩,
      ⟨36417, 41⟩,
      ⟨41267, 41⟩,
      ⟨41467, 41⟩,
      ⟨53531, 150⟩,
      ⟨59462, 150⟩,
      ⟨59835, 150⟩,
      ⟨63694, 120⟩,
      ⟨70979, 120⟩,
      ⟨71906, 120⟩,
      ⟨75199, 218⟩,
      ⟨80264, 208⟩,
      ⟨83314, 220⟩,
      ⟨84296, 218⟩,
      ⟨88722, 206⟩,
      ⟨90131, 208⟩,
      ⟨7805478224329473, -835⟩] }

theorem recurrence_normalize :
    Form.fastCanonical
      (rootXForm 20 (rootCoordinate 0) (rootCoordinate 1) (rootCoordinate 2) rows) =
      expectedForm := by
  decide

end MatrixMultiplication.Generated.SimplifiedExponentRoot.Root4X
