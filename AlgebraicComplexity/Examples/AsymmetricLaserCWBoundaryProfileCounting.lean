/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.AsymmetricLaserCWBoundaryProfileRestriction
import AlgebraicComplexity.Combinatorics.WordTypeCardinalityCore

/-!
# Exact native boundary-profile counts and finite matrix dimensions

This CW-specific instance of the existing type-class cardinality API transcribes
[duan2023faster], `papers/sources/2210.10173/component_value.tex:468-475`:
the surviving Z blocks determine the zero-X/Y tensor and its matrix dimension.
The split restriction is the actual physical-Z object of `prelim.tex:337-367`.
The existing forced-address injection and live-leg injectivity identify its
native support with the complete ordered-Z type class. No second counting engine
or complete-word profile is introduced. The multinomial formula requires the
actual positive word length; the type-class equality also covers empty classes.
The literal full022 client is included in the accompanying Examples module.
-/

set_option autoImplicit false

namespace AlgebraicComplexity.Examples

open Tensor AsymmetricLaserData MoreAsymmetryCompatibility
open scoped BigOperators

/-- The admitted native support has exactly the cardinality of its physical-Z type class. -/
theorem cwBoundaryProfile_card_eq_typeClass (K : Type*) [CommRing K]
    (data : CWBoundaryProfileData) (zero : Leg) (k : Fin 5) (profile : LegProfile)
    (hdecode : decodeCWBoundaryProfile data = some (zero, k, profile)) (j n : Nat) :
    (cwBoundaryProfileCell K data.q zero k profile j n).support.card =
      (WordType.typeClass (n + 1)
        (WordType.proportionalCounts (cwBoundaryProfileCounts profile) j)).card := by
  classical
  rcases decodeCWBoundaryProfile_sound data zero k profile hdecode with
    ⟨_, hzero, _, _, _, _, _, _, _, _, hdegree⟩
  let α := WordType.proportionalCounts (cwBoundaryProfileCounts profile) j
  let target := dwz63ZeroCellTarget zero k n
  let cell := cwBoundaryProfileCell K data.q zero k profile j n
  have hαdegree : ∀ p, α p ≠ 0 → cwSquareBlockDegree p = k := by
    intro p hp
    apply hdegree p
    intro h
    exact hp (by simp [α, WordType.proportionalCounts, h])
  have hmem : ∀ s ∈ cell.support,
      s ∈ (((cwPartitionedTensor K data.q).positivePower 1).positivePower n).support := by
    intro s hs
    exact ((dwz63_mem_cellPower_support_iff K data.q n α target s).mp hs).1
  have hzeroCell : ∀ s ∈ cell.support,
      s zero = positiveWordConst (positiveWordConst CWBlock.zero 1) n := by
    intro s hs
    exact dwz63_cellPower_zeroLeg_eq_const K data.q n zero α target
      (dwz63ZeroCellTarget_self zero k n) s hs
  have hbase : ∀ s ∈ cwBlockSupport, ∀ t ∈ cwBlockSupport,
      s zero = CWBlock.zero → t zero = CWBlock.zero → s Leg.Z = t Leg.Z → s = t := by
    cases zero
    · exact cwSupported_eq_of_zero_of_secondLiveLeg_eq Leg.X
    · exact cwSupported_eq_of_zero_of_firstLiveLeg_eq Leg.Y
    · exact absurd rfl hzero
  have hinj := dwz63_finePower_injOn_liveLeg K data.q zero Leg.Z hbase n
    cell.support hmem hzeroCell
  refine le_antisymm ?_
    (dwz63_card_typeClass_le_zeroFineCellSupport K data.q zero hzero k n α hαdegree)
  refine Finset.card_le_card_of_injOn
    (fun s ↦ positiveWordEquiv (PositiveWord CWBlock 1) n (s Leg.Z)) ?_ ?_
  · intro s hs
    exact WordType.mem_typeClass.mpr
      (((dwz63_mem_cellPower_support_iff K data.q n α target s).mp hs).2.2)
  · intro s hs t ht h
    exact hinj hs ht ((positiveWordEquiv (PositiveWord CWBlock 1) n).injective h)

/-- At the admitted integral length the native support count is its complete multinomial. -/
theorem cwBoundaryProfile_card_eq_multinomial (K : Type*) [CommRing K]
    (data : CWBoundaryProfileData) (zero : Leg) (k : Fin 5) (profile : LegProfile)
    (hdecode : decodeCWBoundaryProfile data = some (zero, k, profile)) (j n : Nat)
    (hlength : n + 1 = profile.law.denominator * j) :
    (cwBoundaryProfileCell K data.q zero k profile j n).support.card =
      Nat.multinomial Finset.univ
        (WordType.proportionalCounts (cwBoundaryProfileCounts profile) j) := by
  classical
  rw [cwBoundaryProfile_card_eq_typeClass K data zero k profile hdecode j n]
  apply WordType.card_typeClass_eq_multinomial_light
  rw [WordType.mem_types]
  change (∑ p, cwBoundaryProfileCounts profile p * j) = n + 1
  rw [← Finset.sum_mul]
  change WordType.profileMass (cwBoundaryProfileCounts profile) * j = n + 1
  have hmass := (decodeCWBoundaryProfile_sound data zero k profile hdecode).2.2.2.2.2.2.2.2.2.1
  exact (congrArg (fun d ↦ d * j) hmass).trans hlength.symm

/-- The actual admitted cell restricts onto a matrix tensor with its derived finite dimension. -/
theorem cwBoundaryProfile_restricts_multinomial (K : Type*) [CommRing K]
    (data : CWBoundaryProfileData) (zero : Leg) (k : Fin 5) (profile : LegProfile)
    (hdecode : decodeCWBoundaryProfile data = some (zero, k, profile)) (j n : Nat)
    (hlength : n + 1 = profile.law.denominator * j) :
    Restricts
      (Tensor.permute (zeroOrientation zero)
        (cwBoundaryProfileCell K data.q zero k profile j n).realize)
      (matrixMultiplication (K := K) 1
        (Nat.multinomial Finset.univ
          (WordType.proportionalCounts (cwBoundaryProfileCounts profile) j) *
          data.q ^ cwBoundaryProfileExponent profile j) 1) := by
  have h := cwBoundaryProfile_restricts K data zero k profile hdecode j n
  rwa [cwBoundaryProfile_card_eq_multinomial K data zero k profile hdecode j n hlength] at h

end AlgebraicComplexity.Examples
