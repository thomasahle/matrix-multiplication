/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import MatrixMultiplication.TotalQuotientExponentLevelTwoActiveEdgeData

/-!
# Active-edge certificate for the lightweight total-quotient checker

The positive level-two geometry has 1,620 active addresses among 7,560 padded candidates.  A
single reduction of that filter is unnecessarily expensive, so this module checks eight
consecutive ranges and then reassembles them.  It imports neither real entropy nor the historical
1,620-row recurrence proofs.

The displayed address array is not trusted.  Every shard and the final list equality are evaluated
by Lean's kernel, and `SimplifiedExponentLevelTwoInputSemantics.activeEdges_eq` transports this
finite geometry to the established semantic recurrence.
-/

namespace MatrixMultiplication.TotalQuotientExponentLevelTwoActiveEdges

open MatrixMultiplication.SimplifiedExponentLevelTwoInput

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-- The cached active-edge address list. -/
def cached : List Nat :=
  MatrixMultiplication.TotalQuotientExponentLevelTwoActiveEdgeData.expectedActiveEdges.toList

/-- Split the complete padded address range into eight bounded proof shards. -/
theorem range_split :
    List.range edgeCount =
      List.range' 0 945 ++ List.range' 945 945 ++ List.range' 1890 945 ++
        List.range' 2835 945 ++ List.range' 3780 945 ++ List.range' 4725 945 ++
          List.range' 5670 945 ++ List.range' 6615 945 := by
  decide

/-- Active addresses in padded range `0 … 944`. -/
theorem shard0 : (List.range' 0 945).filter edgeActive = cached.take 152 := by decide

/-- Active addresses in padded range `945 … 1889`. -/
theorem shard1 :
    (List.range' 945 945).filter edgeActive = (cached.drop 152).take 181 := by decide

/-- Active addresses in padded range `1890 … 2834`. -/
theorem shard2 :
    (List.range' 1890 945).filter edgeActive = (cached.drop 333).take 193 := by decide

/-- Active addresses in padded range `2835 … 3779`. -/
theorem shard3 :
    (List.range' 2835 945).filter edgeActive = (cached.drop 526).take 266 := by decide

/-- Active addresses in padded range `3780 … 4724`. -/
theorem shard4 :
    (List.range' 3780 945).filter edgeActive = (cached.drop 792).take 230 := by decide

/-- Active addresses in padded range `4725 … 5669`. -/
theorem shard5 :
    (List.range' 4725 945).filter edgeActive = (cached.drop 1022).take 220 := by decide

/-- Active addresses in padded range `5670 … 6614`. -/
theorem shard6 :
    (List.range' 5670 945).filter edgeActive = (cached.drop 1242).take 226 := by decide

/-- Active addresses in padded range `6615 … 7559`. -/
theorem shard7 :
    (List.range' 6615 945).filter edgeActive = cached.drop 1468 := by decide

/-- The eight certified slices reassemble to the cached list. -/
theorem cached_reassemble :
    cached.take 152 ++ (cached.drop 152).take 181 ++ (cached.drop 333).take 193 ++
        (cached.drop 526).take 266 ++ (cached.drop 792).take 230 ++
          (cached.drop 1022).take 220 ++ (cached.drop 1242).take 226 ++ cached.drop 1468 =
      cached := by
  decide

/-- The lightweight checker's computed active-edge list is exactly the displayed cache.

Proof sketch: distribute filtering over `range_split`, replace each finite shard by its checked
slice, and use `cached_reassemble`. -/
theorem activeEdges_eq : activeEdges = cached := by
  show (List.range edgeCount).filter edgeActive = cached
  rw [range_split]
  simp only [List.filter_append]
  rw [shard0, shard1, shard2, shard3, shard4, shard5, shard6, shard7]
  exact cached_reassemble

end MatrixMultiplication.TotalQuotientExponentLevelTwoActiveEdges
