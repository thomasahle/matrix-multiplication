/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.AsymmetricLaserCWBoundaryProfileRestriction
import AlgebraicComplexity.MatrixMultiplication.AsymmetricLaserOrientationRule
import AlgebraicComplexity.Tensor.PartitionedPermutation

/-!
# Native boundary children with transported profiles

This shared CW adapter formalizes [duan2023faster],
`papers/sources/2210.10173/prelim.tex:337-367` (`def:restricted_splitting`)
and `component_value.tex:459-475` (the boundary restricted-splitting argument).
The split profile is an input to the native tensor, including its physical leg.
An orientation moves that leg and the tensor together.

A child reference resolves one earlier finite boundary entry and checks its
output-to-input physical table. Its actual partition is derived from that same
entry. The support equivalence preserves the native coarse fiber and complete
ordered law on the output leg e(Z); realization is the actual tensor permutation.
No separately supplied tensor, profile, restriction or scalar witness enters the
decoder. Unused entries entries are not validated. The adapter is CW-specific
because the native boundary alphabet and cell are CW objects; the literal full022
client accompanies it. Full producing-DAG Checks and parent extraction remain open.
-/

set_option autoImplicit false

namespace AlgebraicComplexity.Examples

open Tensor AsymmetricLaserData MoreAsymmetryCompatibility

/-- The native entry and decoded parameters of one boundary child, with its physical frame. -/
structure CWBoundaryChild where
  native : CWBoundaryProfileData
  zeroLeg : Leg
  zDegree : Fin 5
  profile : LegProfile
  orientation : Orientation

/-- Resolve a backward native boundary entry, its complete profile and its physical frame. -/
def decodeCWBoundaryChild (entries : List CWBoundaryProfileData) (child : ChildRef) :
    Option CWBoundaryChild := do
  let data ← entries[child.nodeId]?
  let decoded ← decodeCWBoundaryProfile data
  let e ← decodePhysicalLegs child.physicalLegs
  pure ⟨data, decoded.1, decoded.2.1, decoded.2.2, e⟩

/-- The output profile keeps every ordered letter and count, and constrains the image of Z. -/
def cwBoundaryChildProfile (leaf : CWBoundaryChild) : LegProfile :=
  { leaf.profile with physicalLeg := physicalLegCode (leaf.orientation Leg.Z) }

/-- The actual output partition is the permutation of the referenced native profile cell. -/
noncomputable def cwBoundaryChildCell (K : Type*) [CommRing K]
    (leaf : CWBoundaryChild) (j n : Nat) :=
  (cwBoundaryProfileCell K leaf.native.q leaf.zeroLeg leaf.zDegree leaf.profile j n).permute
    leaf.orientation

/-- Admission binds the reference, native profile and inverse physical-leg table together. -/
theorem decodeCWBoundaryChild_sound (entries : List CWBoundaryProfileData) (child : ChildRef)
    (leaf : CWBoundaryChild) (h : decodeCWBoundaryChild entries child = some leaf) :
    child.ValidBefore entries.length ∧ entries[child.nodeId]? = some leaf.native ∧
      decodeCWBoundaryProfile leaf.native = some (leaf.zeroLeg, leaf.zDegree, leaf.profile) ∧
      decodePhysicalLegs child.physicalLegs = some leaf.orientation := by
  cases hl : entries[child.nodeId]? with
  | none => simp [decodeCWBoundaryChild, hl] at h
  | some data =>
      cases hd : decodeCWBoundaryProfile data with
      | none => simp [decodeCWBoundaryChild, hl, hd] at h
      | some decoded =>
          rcases decoded with ⟨zero, k, profile⟩
          cases he : decodePhysicalLegs child.physicalLegs with
          | none => simp [decodeCWBoundaryChild, hl, he] at h
          | some e =>
              have hh : (⟨data, zero, k, profile, e⟩ : CWBoundaryChild) = leaf := by
                simpa [decodeCWBoundaryChild, hl, hd, he] using h
              subst leaf
              have hback : child.nodeId < entries.length := by
                by_contra hn
                have hz := List.getElem?_eq_none (Nat.le_of_not_lt hn)
                rw [hz] at hl
                contradiction
              have hperm : child.physicalLegs.Perm [0, 1, 2] := by
                unfold decodePhysicalLegs at he
                split at he <;> simp_all only [reduceCtorEq]
                all_goals decide
              exact ⟨⟨hback, hperm⟩, rfl, hd, rfl⟩

/-- Surviving output addresses are exactly the permuted native coarse fiber with the complete
ordered profile on e(Z). This constrains actual support, including every zero-count letter. -/
theorem cwBoundaryChild_mem_support_iff (K : Type*) [CommRing K]
    (leaf : CWBoundaryChild) (j n : Nat)
    (s : BlockAddress (fun _ : Leg ↦ PositiveWord (PositiveWord CWBlock 1) n)) :
    s ∈ (cwBoundaryChildCell K leaf j n).support ↔
      s ∈ ((((cwPartitionedTensor K leaf.native.q).positivePower 1).positivePower n).permute
        leaf.orientation).support ∧
      (∀ c, positiveWordMap (cwSquareDegreeMap (leaf.orientation.symm c)) n (s c) =
        dwz63ZeroCellTarget leaf.zeroLeg leaf.zDegree n (leaf.orientation.symm c)) ∧
      WordType.multiplicity
        (positiveWordEquiv (PositiveWord CWBlock 1) n (s (leaf.orientation Leg.Z))) =
        WordType.proportionalCounts (cwBoundaryProfileCounts (cwBoundaryChildProfile leaf)) j := by
  classical
  have haddr (c : Leg) :
      ((permuteBlockAddress
        (A := fun _ : Leg ↦ PositiveWord (PositiveWord CWBlock 1) n)
        leaf.orientation).symm s) c = s (leaf.orientation c) := by
    exact (congrArg ((permuteBlockAddress
      (A := fun _ : Leg ↦ PositiveWord (PositiveWord CWBlock 1) n)
      leaf.orientation).symm s) (leaf.orientation.symm_apply_apply c)).symm.trans
        (permuteBlockAddress_symm_apply_apply
          (A := fun _ : Leg ↦ PositiveWord (PositiveWord CWBlock 1) n)
          leaf.orientation s (leaf.orientation c))
  simp only [cwBoundaryChildCell, PartitionedTensor.mem_permute_support, cwBoundaryProfileCell]
  rw [dwz63_mem_cellPower_support_iff]
  change _ ↔ _ ∧ _ ∧ _ = WordType.proportionalCounts (cwBoundaryProfileCounts leaf.profile) j
  constructor
  · rintro ⟨hs, hc, hp⟩
    refine ⟨hs, ?_, ?_⟩
    · intro c
      simpa only [permuteBlockAddress_symm_apply_apply] using hc (leaf.orientation.symm c)
    · simpa only [haddr] using hp
  · rintro ⟨hs, hc, hp⟩
    refine ⟨hs, ?_, ?_⟩
    · intro c
      rw [haddr]
      exact (hc (leaf.orientation c)).trans
        (congrArg (dwz63ZeroCellTarget leaf.zeroLeg leaf.zDegree n)
          (leaf.orientation.symm_apply_apply c))
    · simpa only [haddr] using hp

/-- Realization uses the very same native profile tensor that the finite reference decoded. -/
theorem cwBoundaryChild_realize (K : Type*) [CommRing K]
    (leaf : CWBoundaryChild) (j n : Nat) :
    (cwBoundaryChildCell K leaf j n).realize =
      Tensor.permute leaf.orientation
        (cwBoundaryProfileCell K leaf.native.q leaf.zeroLeg leaf.zDegree
          leaf.profile j n).realize :=
  PartitionedTensor.permute_realize _ _

/-- An admitted integral boundary child has inhabited actual support in its output frame. -/
theorem cwBoundaryChild_nonempty (K : Type*) [CommRing K]
    (entries : List CWBoundaryProfileData) (child : ChildRef) (leaf : CWBoundaryChild)
    (h : decodeCWBoundaryChild entries child = some leaf) (j n : Nat)
    (hlength : n + 1 = leaf.profile.law.denominator * j) :
    (cwBoundaryChildCell K leaf j n).support.Nonempty := by
  have hd := (decodeCWBoundaryChild_sound entries child leaf h).2.2.1
  have hn := (cwBoundaryProfile_nonempty K leaf.native leaf.zeroLeg leaf.zDegree leaf.profile
    hd j n hlength).1
  simpa only [cwBoundaryChildCell, PartitionedTensor.permute_support, Finset.map_nonempty] using hn

end AlgebraicComplexity.Examples
