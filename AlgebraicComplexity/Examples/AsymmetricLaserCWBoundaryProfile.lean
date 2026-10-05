/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.AsymmetricLaserData
import AlgebraicComplexity.Examples.CoppersmithWinogradSquare

/-!
# Finite admission of a native boundary split profile

This shared CW constructor transcribes [duan2023faster],
`papers/sources/2210.10173/component_value.tex:459-475` (the restricted-splitting
argument after `thm:zero-i`), and `prelim.tex:337-367`. A level-two zero-X/Y cell
has one complete physical-Z ordered-pair law. Legal zero-count letters remain.

The decoder admits only that native format. Its integral function is derived on
the nine CW pairs; no tensor, semantic restriction, rate or analytic inequality
is stored. This CW-specific adapter belongs in Examples because the target
alphabet is native CW. The native restriction and literal DWZ022 instance are
separate modules in the same image. Full producing-DAG Checks remain open.
-/

set_option autoImplicit false

namespace AlgebraicComplexity.Examples

open Tensor AsymmetricLaserData
open scoped BigOperators

/-- Finite data for the level-two zero-X/Y cell with one ordered physical-Z profile. -/
structure CWBoundaryProfileData where
  q : Nat
  zeroLeg : Nat
  zDegree : Nat
  profile : ProfileDescriptor

/-- Check the complete native profile and decode its zero leg, bounded degree and actual law.
The native shape is derived from the zero leg and degree; unsupported views reject. -/
def decodeCWBoundaryProfile (data : CWBoundaryProfileData) :
    Option (Leg × Fin 5 × LegProfile) :=
  match data.profile.view, data.profile.legs with
  | .orderedSplit, [profile] =>
      if h : 0 < data.q ∧ data.zeroLeg < 2 ∧ data.zDegree < 5 ∧
          profile.physicalLeg = 2 ∧ profile.alphabet = orderedSplitAlphabet 2 data.zDegree ∧
          profile.law.counts.length = profile.alphabet.length ∧
          0 < profile.law.denominator ∧ profile.law.counts.sum = profile.law.denominator then
        some (if data.zeroLeg = 0 then Leg.X else Leg.Y,
          ⟨data.zDegree, h.2.2.1⟩, profile)
      else none
  | _, _ => none

/-- Extend the finite Z profile by zero to all nine native ordered CW pairs. -/
def cwBoundaryProfileCounts (profile : LegProfile) (p : PositiveWord CWBlock 1) : Nat :=
  profile.countAt [cwBlockDegree p.1, cwBlockDegree p.2]

/-- Complete aligned profile counts have exactly the serialized denominator as native mass. -/
theorem cwBoundaryProfileCounts_mass (profile : LegProfile) (k : Fin 5)
    (halphabet : profile.alphabet = orderedSplitAlphabet 2 k.val)
    (hlength : profile.law.counts.length = profile.alphabet.length)
    (hmass : profile.law.counts.sum = profile.law.denominator) :
    WordType.profileMass (cwBoundaryProfileCounts profile) = profile.law.denominator := by
  rcases profile with ⟨leg, alphabet, ⟨denominator, counts⟩⟩
  dsimp at halphabet hlength hmass ⊢
  subst alphabet
  change (∑ p : CWBlock × CWBlock,
    (LegProfile.mk leg (orderedSplitAlphabet 2 k.val) ⟨denominator, counts⟩).countAt
      [cwBlockDegree p.1, cwBlockDegree p.2]) = _
  rw [Fintype.sum_prod_type]
  have huniv : (Finset.univ : Finset CWBlock) = {.zero, .middle, .last} := by decide
  have sumCW (f : CWBlock → Nat) : (∑ x, f x) = f .zero + f .middle + f .last := by
    rw [huniv, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_singleton]
    omega
  rw [sumCW, sumCW, sumCW, sumCW]
  fin_cases k
  all_goals norm_num [orderedSplitAlphabet, List.range_succ] at hlength
  all_goals first
    | obtain ⟨a, rfl⟩ := List.length_eq_one_iff.mp hlength
    | obtain ⟨a, b, rfl⟩ := List.length_eq_two.mp hlength
    | obtain ⟨a, b, c, rfl⟩ := List.length_eq_three.mp hlength
  all_goals
    simp only [cwBlockDegree]
    norm_num [LegProfile.countAt, orderedSplitAlphabet, List.range_succ, List.lookup,
      BEq.beq, List.beq, Nat.beq] at *
    omega

/-- A nonzero decoded native count has the admitted coarse degree. -/
theorem cwBoundaryProfileCounts_degree (profile : LegProfile) (k : Fin 5)
    (halphabet : profile.alphabet = orderedSplitAlphabet 2 k.val)
    (p : PositiveWord CWBlock 1) (hp : cwBoundaryProfileCounts profile p ≠ 0) :
    cwSquareBlockDegree p = k := by
  have hmem : [cwBlockDegree p.1, cwBlockDegree p.2] ∈ profile.alphabet := by
    by_contra h
    exact hp (LegProfile.countAt_eq_zero_of_not_mem profile _ h)
  rw [halphabet] at hmem
  rcases p with ⟨left, right⟩
  fin_cases k <;> cases left <;> cases right <;>
    simp_all [orderedSplitAlphabet, cwBlockDegree, cwSquareBlockDegree]

/-- Successful admission binds the actual finite profile and derives its native mass/support.
No all-length tensor or rate hypothesis enters this finite check. -/
theorem decodeCWBoundaryProfile_sound (data : CWBoundaryProfileData)
    (zero : Leg) (k : Fin 5) (profile : LegProfile)
    (hdecode : decodeCWBoundaryProfile data = some (zero, k, profile)) :
    0 < data.q ∧ zero ≠ Leg.Z ∧
      data.zeroLeg = (if zero = Leg.X then 0 else 1) ∧ data.zDegree = k.val ∧
      data.profile.view = ProfileView.orderedSplit ∧ data.profile.legs = [profile] ∧
      profile.physicalLeg = 2 ∧ profile.alphabet = orderedSplitAlphabet 2 k.val ∧
      0 < profile.law.denominator ∧
      WordType.profileMass (cwBoundaryProfileCounts profile) = profile.law.denominator ∧
      (∀ p, cwBoundaryProfileCounts profile p ≠ 0 → cwSquareBlockDegree p = k) := by
  unfold decodeCWBoundaryProfile at hdecode
  split at hdecode
  next p hv hl =>
    split at hdecode
    next h =>
      have heq := Option.some.inj hdecode
      have hz := congrArg Prod.fst heq
      have hk := congrArg (fun x : Leg × Fin 5 × LegProfile => x.2.1) heq
      have hp := congrArg (fun x : Leg × Fin 5 × LegProfile => x.2.2) heq
      dsimp at hz hk hp
      subst zero
      subst k
      subst profile
      refine ⟨h.1, ?_, ?_, rfl, hv, hl, h.2.2.2.1, h.2.2.2.2.1,
        h.2.2.2.2.2.2.1, ?_, ?_⟩
      · split <;> decide
      · split <;> simp_all
        omega
      · exact cwBoundaryProfileCounts_mass p ⟨data.zDegree, h.2.2.1⟩ h.2.2.2.2.1 h.2.2.2.2.2.1
          h.2.2.2.2.2.2.2
      · exact cwBoundaryProfileCounts_degree p ⟨data.zDegree, h.2.2.1⟩ h.2.2.2.2.1
    next => simp at hdecode
  next => simp at hdecode

end AlgebraicComplexity.Examples
