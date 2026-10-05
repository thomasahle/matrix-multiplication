/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.AsymmetricLaserNativeSupport
import AlgebraicComplexity.MatrixMultiplication.AsymmetricLaserSplitRefinement
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoFiniteSplit
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoHoleIntegrationAvailability

/-!
# The finite DWZ decoder supplies the physical coarse-Z support premise

This transcribes [duan2023faster], `def:global-compatible` and `def:useful_g`,
`papers/sources/2210.10173/global_value.tex:35-51,75-82`, at the section 6.3 table
(`global_value.tex:332-378`). The complete ordered alphabet supplies the degree check;
the shared decoder theorem transfers it to nonzero entries. Existing availability identifies
a decoded fine word's coarse Z-word with the reference's actual Z-word.

The profile is the existing finite decoder at its unchanged period, not a replacement
positive-only table. No same-seed selection, hole budget, repair or exponent bound is proved.
-/

set_option autoImplicit false

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity AsymmetricLaserData Tensor

universe u

/-- Every nonzero decoded DWZ entry has its row's physical coarse-Z degree.
Proof sketch: the declared alphabet has the prescribed sum; convert that equality to `Fin 5`
and apply the shared support theorem, rather than rechecking the 135 weighted entries. -/
theorem dwz63FiniteSplitPair_zDegree (s : Nat) (row : Fin 15)
    (pair : PositiveWord CWBlock 1)
    (h : (dwz63FiniteSplitPair s).splitCount row pair ≠ 0) :
    cwSquareDegreeMap Leg.Z pair = dwz63ZIndex row := by
  apply splitRequirementsFromProfiles_support dwz63FiniteCoarseLaw dwz63FiniteProfile
    dwz63ZIndex dwz63Boundary
    (fun p : PositiveWord CWBlock 1 => [cwBlockDegree p.1, cwBlockDegree p.2])
    (20000000000000000 * s) (cwSquareDegreeMap Leg.Z) ?_ row pair h
  intro c letter hmem
  apply Fin.ext
  rw [(dwz63FiniteProfile_isOrderedSplitFor c).2] at hmem
  simpa only [cwSquareDegreeMap, cwSquareBlockDegree, List.sum_cons, List.sum_nil,
    Nat.add_zero] using orderedSplitAlphabet_degree_of_mem hmem

/-- Coarsening an available word for the decoded profile returns its reference's own Z-word.
This applies the existing hole-pipeline consumer with the derived, not assumed, support premise. -/
theorem dwz63FiniteSplitPair_coarseZ (K : Type u) [CommRing K] (n s : Nat)
    (wRef : PositiveWord ((cwSquarePartitionedTensor K dwz63Q).support) n)
    (z : SegmentedAvailableWord (dwz63Seg K n wRef) (dwz63FiniteSplitPair s).splitCount) :
    positiveWordMap (cwSquareDegreeMap Leg.Z) n z.1 =
      positiveSupportWordBlockAddress ((cwSquarePartitionedTensor K dwz63Q).support) n
        wRef Leg.Z :=
  dwz63_coarseZ_of_segmentedAvailable K n wRef (dwz63FiniteSplitPair s).splitCount
    (dwz63FiniteSplitPair_zDegree s) z

end AlgebraicComplexity.Examples
