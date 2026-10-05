/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoRecurrenceChunk17

/-!
# The level-two active-edge list, in eight kernel shards

`SimplifiedExponentRecurrence.Chunked.activeEdges` is
`(List.range edgeCount).filter edgeActive` with `edgeCount = 126 · 6 · 10 = 7560`, and the level-two
retained-rate checker consumes it through the cached array
`Generated.TotalQuotientExponentLevelTwoRecurrence.MassThree.expectedActiveEdges` (`1620` entries).
Identifying the two is the one step of
`better_bound/total_weight_level_two_emission/HANDOFF.md` §4 that the emitted aggregate leaves as a
single `decide`.

## Why it is sharded

That single `decide` does not fit the project's configured compiler budget.  Measured with raw
`lean -j 1`: it succeeds at `-M 12000` in `247 s` with a peak resident set of `3.42 GB` (peak memory
footprint `5.33 GB`), and fails with `(kernel) excessive memory consumption detected` at the
`weakLeanArgs` value `-M 3000` used by every build in this repository.  A `rfl` proof is worse — it
had not finished after `10 min` at `-M 3000`.  That is why the committed sorted-pair twin of this
statement (`Generated/SimplifiedExponentLevelTwoRecurrenceData.activeEdges_eq`) sits outside every
configured build target and has never been compiled.

`edgeActive` is table-independent — it is `splitSlotIsValid` and `IsPositive` of `splitShapeAt`,
pure index combinatorics — so the reduction splits cleanly along the index range.  Eight shards of
`945` indices each are checked separately; the shard sizes `152, 181, 193, 266, 230, 220, 226, 152`
sum to `1620`.  Each shard is one `decide` over one eighth of the range, and the garbage collector
reclaims between declarations, so the whole module builds inside `-M 3000`.

Nothing here is assumed: `activeEdges_eq` is a theorem, and the eight shards plus the range split
and the final reassembly are all kernel reductions.
-/

namespace MatrixMultiplication.TotalQuotientLevelTwoActiveEdgeShards

open MatrixMultiplication.Generated.TotalQuotientExponentLevelTwoRecurrence
open MatrixMultiplication.SimplifiedExponentRecurrence
open MatrixMultiplication.SimplifiedExponentRecurrence.Chunked

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-- The cached active-edge list of the level-two checker, as a `List`. -/
def cached : List ℕ := MassThree.expectedActiveEdges.toList

/-- The `7560` edge indices, split into eight consecutive blocks of `945`. -/
theorem range_split :
    List.range edgeCount =
      List.range' 0 945 ++ List.range' 945 945 ++ List.range' 1890 945 ++
        List.range' 2835 945 ++ List.range' 3780 945 ++ List.range' 4725 945 ++
          List.range' 5670 945 ++ List.range' 6615 945 := by
  decide

/-- Shard `0`: indices `0 … 944` contribute the first `152` active edges. -/
theorem shard0 : (List.range' 0 945).filter edgeActive = cached.take 152 := by decide

/-- Shard `1`: indices `945 … 1889` contribute the next `181` active edges. -/
theorem shard1 :
    (List.range' 945 945).filter edgeActive = (cached.drop 152).take 181 := by decide

/-- Shard `2`: indices `1890 … 2834` contribute the next `193` active edges. -/
theorem shard2 :
    (List.range' 1890 945).filter edgeActive = (cached.drop 333).take 193 := by decide

/-- Shard `3`: indices `2835 … 3779` contribute the next `266` active edges. -/
theorem shard3 :
    (List.range' 2835 945).filter edgeActive = (cached.drop 526).take 266 := by decide

/-- Shard `4`: indices `3780 … 4724` contribute the next `230` active edges. -/
theorem shard4 :
    (List.range' 3780 945).filter edgeActive = (cached.drop 792).take 230 := by decide

/-- Shard `5`: indices `4725 … 5669` contribute the next `220` active edges. -/
theorem shard5 :
    (List.range' 4725 945).filter edgeActive = (cached.drop 1022).take 220 := by decide

/-- Shard `6`: indices `5670 … 6614` contribute the next `226` active edges. -/
theorem shard6 :
    (List.range' 5670 945).filter edgeActive = (cached.drop 1242).take 226 := by decide

/-- Shard `7`: indices `6615 … 7559` contribute the last `152` active edges. -/
theorem shard7 :
    (List.range' 6615 945).filter edgeActive = cached.drop 1468 := by decide

/-- The eight cached slices reassemble to the cached list. -/
theorem cached_reassemble :
    cached.take 152 ++ (cached.drop 152).take 181 ++ (cached.drop 333).take 193 ++
        (cached.drop 526).take 266 ++ (cached.drop 792).take 230 ++
          (cached.drop 1022).take 220 ++ (cached.drop 1242).take 226 ++ cached.drop 1468 =
      cached := by
  decide

/-- **The recurrence's own active-edge list is the one the level-two checker cached.**

This is the emitted aggregate's `activeEdges_eq`, proved inside the project's compiler budget. -/
theorem activeEdges_eq : activeEdges = MassThree.expectedActiveEdges.toList := by
  show (List.range edgeCount).filter edgeActive = cached
  rw [range_split]
  simp only [List.filter_append]
  rw [shard0, shard1, shard2, shard3, shard4, shard5, shard6, shard7]
  exact cached_reassemble

end MatrixMultiplication.TotalQuotientLevelTwoActiveEdgeShards
