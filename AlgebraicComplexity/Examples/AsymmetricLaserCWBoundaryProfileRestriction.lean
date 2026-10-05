/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.AsymmetricLaserCWBoundaryProfile
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoFineCellGeneral

/-!
# A finite boundary profile produces its actual native restricted cell

This shared CW adapter formalizes [duan2023faster],
`papers/sources/2210.10173/component_value.tex:459-475` (`thm:zero-i` and
its restricted-splitting argument). At every admitted positive integral length,
the complete physical-Z profile determines the actual zero-X/Y localized cell.
The committed zero-leg and uniform-dimension proofs feed its single shared-leg
fusion map. The target dimension uses the actual support cardinality, without a
new cardinality formula or an analytic-rate hypothesis. The literal full022 law
is instantiated in the companion Examples module of this image.
-/

set_option autoImplicit false

namespace AlgebraicComplexity.Examples

open Tensor AsymmetricLaserData MoreAsymmetryCompatibility
open scoped BigOperators

/-- The actual native cell selected by the decoded Z profile at the integral multiplier. -/
noncomputable def cwBoundaryProfileCell (K : Type*) [CommRing K] (q : Nat)
    (zero : Leg) (k : Fin 5) (profile : LegProfile) (j n : Nat) :=
  ((cwPartitionedTensor K q).positivePower 1).segmentedLocalizedSplittingPower
    cwSquareDegreeMap n 1 (fun _ ↦ 0)
    (SegmentedSplitRestriction.ofLeg
      (A := fun _ : Leg ↦ PositiveWord CWBlock 1) Leg.Z
      (fun _ ↦ WordType.proportionalCounts (cwBoundaryProfileCounts profile) j))
    (dwz63ZeroCellTarget zero k n)

/-- Both ordered halves contribute to the common middle-coordinate exponent. -/
noncomputable def cwBoundaryProfileExponent (profile : LegProfile) (j : Nat) : Nat :=
  ∑ p : PositiveWord CWBlock 1,
    WordType.proportionalCounts (cwBoundaryProfileCounts profile) j p * cwWordMiddleCount 1 p

/-- Admission derives the one-slice restriction of the actual permuted full profile cell. -/
theorem cwBoundaryProfile_restricts (K : Type*) [CommRing K]
    (data : CWBoundaryProfileData) (zero : Leg) (k : Fin 5) (profile : LegProfile)
    (hdecode : decodeCWBoundaryProfile data = some (zero, k, profile)) (j n : Nat) :
    Restricts
      (Tensor.permute (zeroOrientation zero)
        (cwBoundaryProfileCell K data.q zero k profile j n).realize)
      (matrixMultiplication (K := K) 1
        ((cwBoundaryProfileCell K data.q zero k profile j n).support.card *
          data.q ^ cwBoundaryProfileExponent profile j) 1) := by
  classical
  have hzero := (decodeCWBoundaryProfile_sound data zero k profile hdecode).2.1
  let α := WordType.proportionalCounts (cwBoundaryProfileCounts profile) j
  let target := dwz63ZeroCellTarget zero k n
  have htarget : target zero = positiveWordConst (0 : Fin 5) n :=
    dwz63ZeroCellTarget_self zero k n
  refine dwz63_fineCellPower_restricts_matrixMultiplication K data.q zero n
    (cwBoundaryProfileExponent profile j)
    (segmentedLocalizedKeep cwSquareDegreeMap (fun _ : Fin (n + 1) ↦ (0 : Fin 1))
      (SegmentedSplitRestriction.ofLeg
        (A := fun _ : Leg ↦ PositiveWord CWBlock 1) Leg.Z (fun _ ↦ α)) target) ?_ ?_
  · intro s hs
    exact dwz63_cellPower_zeroLeg_eq_const K data.q n zero α target htarget s hs
  · intro s hs
    exact dwz63_cellPower_cellOnes_eq_alphaSum K data.q zero hzero n α target htarget s hs

/-- At an admitted positive length the integral type class inhabits the actual cell,
and its fused middle dimension is positive. -/
theorem cwBoundaryProfile_nonempty (K : Type*) [CommRing K]
    (data : CWBoundaryProfileData) (zero : Leg) (k : Fin 5) (profile : LegProfile)
    (hdecode : decodeCWBoundaryProfile data = some (zero, k, profile)) (j n : Nat)
    (hlength : n + 1 = profile.law.denominator * j) :
    (cwBoundaryProfileCell K data.q zero k profile j n).support.Nonempty ∧
      0 < (cwBoundaryProfileCell K data.q zero k profile j n).support.card *
        data.q ^ cwBoundaryProfileExponent profile j := by
  classical
  rcases decodeCWBoundaryProfile_sound data zero k profile hdecode with
    ⟨hq, hzero, _, _, _, _, _, _, _, hmass, hdegree⟩
  let α := WordType.proportionalCounts (cwBoundaryProfileCounts profile) j
  have hαdegree : ∀ p, α p ≠ 0 → cwSquareBlockDegree p = k := by
    intro p hp
    apply hdegree p
    intro h
    exact hp (by simp [α, WordType.proportionalCounts, h])
  have htype : α ∈ WordType.types (PositiveWord CWBlock 1) (n + 1) := by
    rw [WordType.mem_types]
    change (∑ p, cwBoundaryProfileCounts profile p * j) = n + 1
    rw [← Finset.sum_mul]
    change WordType.profileMass (cwBoundaryProfileCounts profile) * j = n + 1
    rw [hmass, hlength]
  have hinj := dwz63_card_typeClass_le_zeroFineCellSupport K data.q zero hzero k n α hαdegree
  have hpos : 0 < (cwBoundaryProfileCell K data.q zero k profile j n).support.card :=
    lt_of_lt_of_le (Finset.card_pos.mpr (WordType.typeClass_nonempty α htype)) hinj
  exact ⟨Finset.card_pos.mp hpos, Nat.mul_pos hpos (Nat.pow_pos hq)⟩

end AlgebraicComplexity.Examples
