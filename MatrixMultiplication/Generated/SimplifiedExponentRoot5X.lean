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

namespace MatrixMultiplication.Generated.SimplifiedExponentRoot.Root5X

open MatrixMultiplication.SignedDyadicLogForm
open MatrixMultiplication.SimplifiedExponentRootRecurrence

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

def referenceNumerators : Array ℕ := #[
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 1, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 6, 6, 4, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 8, 14, 17, 14, 8, 0, 0, 0, 0, 0, 0, 0, 4, 14, 24, 22, 14, 4, 0, 0, 0, 0, 0, 1, 6, 18, 24,
    17, 6, 1, 0, 0, 0, 0, 2, 6, 14, 14, 6, 2, 0, 0, 0, 0, 1, 4, 8, 4, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
  ]
def weightXNumerators : Array ℕ := #[
    256, 2667, 11563, 30007, 54368, 73492, 75500, 57956, 32354, 13803, 6935, 5828, 5184, 3047,
    2341, 6249, 31561
  ]
def weightYNumerators : Array ℕ := #[
    256, 2557, 10848, 27893, 50236, 67418, 68862, 52755, 29490, 12564, 6360, 5399, 4789, 2808,
    2205, 6105, 28775
  ]
def weightZNumerators : Array ℕ := #[
    256, 2650, 11359, 29162, 52426, 70497, 72079, 55480, 31281, 13620, 6817, 5635, 5046, 3063,
    2306, 5984, 30712
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
    0, 0, 0, 0, 0, 0, 0, 1, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 6, 6, 4, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 8, 14, 17, 14, 8, 0, 0, 0, 0, 0, 0, 0, 4, 14, 24, 22, 14, 4, 0, 0, 0, 0, 0, 1, 6, 18, 24,
    17, 6, 1, 0, 0, 0, 0, 2, 6, 14, 14, 6, 2, 0, 0, 0, 0, 1, 4, 8, 4, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
  ]
    marginalXList := [
    0, 0, 4, 20, 61, 82, 73, 44, 18, 0, 0, 0, 0, 0, 0, 0, 0
  ]
    weightX := weightX
    weightY := weightY
    weightZ := weightZ
    logicalY := ⟨[], [], []⟩
    logicalZ := ⟨[], [], []⟩ }

def expectedForm : Form := {
  constantNumerator := 0
  terms := [⟨2, -6⟩,
      ⟨4, -28⟩,
      ⟨6, -36⟩,
      ⟨8, -24⟩,
      ⟨14, -84⟩,
      ⟨17, -34⟩,
      ⟨18, -36⟩,
      ⟨20, -20⟩,
      ⟨22, -22⟩,
      ⟨24, -48⟩,
      ⟨44, -44⟩,
      ⟨61, -61⟩,
      ⟨73, -73⟩,
      ⟨82, -82⟩,
      ⟨302, 604⟩,
      ⟨10848, 4⟩,
      ⟨11359, 4⟩,
      ⟨11563, 4⟩,
      ⟨27893, 20⟩,
      ⟨29162, 20⟩,
      ⟨29490, 18⟩,
      ⟨30007, 20⟩,
      ⟨31281, 18⟩,
      ⟨32354, 18⟩,
      ⟨50236, 62⟩,
      ⟨52426, 61⟩,
      ⟨52755, 44⟩,
      ⟨54368, 61⟩,
      ⟨55480, 44⟩,
      ⟨57956, 44⟩,
      ⟨67418, 84⟩,
      ⟨68862, 70⟩,
      ⟨70497, 82⟩,
      ⟨72079, 73⟩,
      ⟨73492, 82⟩,
      ⟨75500, 73⟩,
      ⟨4995288055092330, -302⟩] }

theorem recurrence_normalize :
    Form.fastCanonical
      (rootXForm 20 (rootCoordinate 0) (rootCoordinate 1) (rootCoordinate 2) rows) =
      expectedForm := by
  decide

end MatrixMultiplication.Generated.SimplifiedExponentRoot.Root5X
