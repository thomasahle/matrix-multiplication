/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.AsymmetricLaserCWBaseRule
import AlgebraicComplexity.MatrixMultiplication.AsymmetricLaserData
import AlgebraicComplexity.MatrixMultiplication.AsymmetricLaserOrientationRule

/-!
# Finite admission of an ordered product of CW base leaves

This shared CW rule follows [duan2023faster], under `papers/sources/2210.10173/`:
`prelim.tex:294-309` gives the two ordered factors of a split; `second_power.tex:51-63`
identifies native base components and their matrix products; `component_value.tex:205-225`,
equation `eq:def_tstar_c`, retains both occurrences when complementary children coincide.

The finite payload is a CW parameter, a prefix of native shape entries and two references.
The prefix length is the position of the new parent: a successful lookup is necessarily
backward. Both shape admissions and inverse physical-leg decodes must succeed. Semantic
source tensors and positive matrix dimensions are derived, never fields of the payload.
Repeated IDs remain two labelled factors of one split term, not two additional root copies.

This adapter belongs in Examples because its shared provider is the native CW tensor.
It admits unrestricted base-leaf products only; it does not validate unused prefix entries,
extract a full parent constituent, transport profiles, or interpret an arbitrary producing DAG.
The literal DWZ pair is a separate client in the same image. Shared-map coherence, complete
Checks, repair and the exponent regression remain separate obligations.
-/

set_option autoImplicit false

namespace AlgebraicComplexity.Examples

open Tensor AsymmetricLaserData

universe u

/-- Finite data for a binary product; the new parent is immediately after the supplied prefix. -/
structure CWBaseProductData where
  q : Nat
  shapePrefix : List (List Nat)
  children : SplitChildren

/-- Resolve one backward reference and check native admission and its inverse physical frame.
Absent references, unsupported shapes, zero q and malformed leg tables all reject. -/
def decodeCWBaseChild (q : Nat) (shapePrefix : List (List Nat)) (child : ChildRef) :
    Option (cwBlockSupport × Orientation) := do
  let shape ← shapePrefix[child.nodeId]?
  if cwBaseRuleCheck { q := q, shape := shape } then
    let s ← decodeCWBaseShape shape
    let e ← decodePhysicalLegs child.physicalLegs
    pure (s, e)
  else
    none

/-- Derive one admitted leaf's dimensions from its native shape and physical orientation. -/
def cwBaseChildDimensions (q : Nat) (leaf : cwBlockSupport × Orientation) : Nat × Nat × Nat :=
  physicalLegMatrixDimensions leaf.2 (cwConstituentDimensions q leaf.1.val).1
    (cwConstituentDimensions q leaf.1.val).2.1 (cwConstituentDimensions q leaf.1.val).2.2

/-- Multiply the two derived dimension triples componentwise, retaining both occurrences. -/
def cwBaseProductDimensions (q : Nat) (left right : cwBlockSupport × Orientation) :
    Nat × Nat × Nat :=
  ((cwBaseChildDimensions q left).1 * (cwBaseChildDimensions q right).1,
    (cwBaseChildDimensions q left).2.1 * (cwBaseChildDimensions q right).2.1,
    (cwBaseChildDimensions q left).2.2 * (cwBaseChildDimensions q right).2.2)

/-- Admit a product precisely when both labelled references pass the finite child decoder. -/
def cwBaseProductCheck (data : CWBaseProductData) : Bool :=
  (decodeCWBaseChild data.q data.shapePrefix data.children.left).isSome &&
    (decodeCWBaseChild data.q data.shapePrefix data.children.right).isSome

/-- Successful child decoding binds the native source and physical frame to the finite input,
proves backward validity, and derives a restriction with positive matrix dimensions. -/
theorem decodeCWBaseChild_sound (K : Type u) [CommRing K] (q : Nat)
    (shapePrefix : List (List Nat)) (child : ChildRef) (leaf : cwBlockSupport × Orientation)
    (h : decodeCWBaseChild q shapePrefix child = some leaf) :
    child.ValidBefore shapePrefix.length ∧
      shapePrefix[child.nodeId]? = some (cwBaseShapeDigits leaf.1.val) ∧
      physicalLegTable leaf.2 = child.physicalLegs ∧
      (0 < (cwBaseChildDimensions q leaf).1 ∧
        0 < (cwBaseChildDimensions q leaf).2.1 ∧
        0 < (cwBaseChildDimensions q leaf).2.2) ∧
      Restricts (Tensor.permute leaf.2 (cwSupportedConstituent K q leaf.1))
        (matrixMultiplication (K := K) (cwBaseChildDimensions q leaf).1
          (cwBaseChildDimensions q leaf).2.1 (cwBaseChildDimensions q leaf).2.2) := by
  cases hl : shapePrefix[child.nodeId]? with
  | none => simp [decodeCWBaseChild, hl] at h
  | some shape =>
      cases hc : cwBaseRuleCheck { q := q, shape := shape } with
      | false => simp [decodeCWBaseChild, hl, hc] at h
      | true =>
          obtain ⟨s, hs, hshape, hpos, hrest⟩ :=
            cwBaseRuleCheck_sound K { q := q, shape := shape } hc
          cases he : decodePhysicalLegs child.physicalLegs with
          | none => simp [decodeCWBaseChild, hl, he] at h
          | some e =>
              have hh : (s, e) = leaf := by
                simpa [decodeCWBaseChild, hl, hc, hs, he] using h
              subst leaf
              have hback : child.nodeId < shapePrefix.length := by
                by_contra hn
                have hz := List.getElem?_eq_none (Nat.le_of_not_lt hn)
                rw [hz] at hl
                contradiction
              have hperm : child.physicalLegs.Perm [0, 1, 2] := by
                unfold decodePhysicalLegs at he
                split at he <;> simp_all only [reduceCtorEq]
                all_goals decide
              refine ⟨⟨hback, hperm⟩, ?_, decodePhysicalLegs_sound _ _ he, ?_, ?_⟩
              · rw [hshape]
              · dsimp [cwBaseChildDimensions, physicalLegMatrixDimensions]
                split <;> simp_all
              · exact decodePhysicalLegs_restricts K child.physicalLegs e
                  (cwConstituentDimensions q s.val).1
                  (cwConstituentDimensions q s.val).2.1
                  (cwConstituentDimensions q s.val).2.2 he _ hrest

/-- A successful finite product check derives both actual source factors and a matrix product.
No semantic restriction or output dimensions are assumed in the finite data. -/
theorem cwBaseProductCheck_sound (K : Type u) [CommRing K] (data : CWBaseProductData)
    (h : cwBaseProductCheck data = true) :
    ∃ left right : cwBlockSupport × Orientation,
      decodeCWBaseChild data.q data.shapePrefix data.children.left = some left ∧
      decodeCWBaseChild data.q data.shapePrefix data.children.right = some right ∧
      data.children.ValidBefore data.shapePrefix.length ∧
      (0 < (cwBaseProductDimensions data.q left right).1 ∧
        0 < (cwBaseProductDimensions data.q left right).2.1 ∧
        0 < (cwBaseProductDimensions data.q left right).2.2) ∧
      Restricts
        (Tensor.external
          (Tensor.permute left.2 (cwSupportedConstituent K data.q left.1))
          (Tensor.permute right.2 (cwSupportedConstituent K data.q right.1)))
        (matrixMultiplication (K := K) (cwBaseProductDimensions data.q left right).1
          (cwBaseProductDimensions data.q left right).2.1
          (cwBaseProductDimensions data.q left right).2.2) := by
  cases hl : decodeCWBaseChild data.q data.shapePrefix data.children.left with
  | none => simp [cwBaseProductCheck, hl] at h
  | some left =>
      cases hr : decodeCWBaseChild data.q data.shapePrefix data.children.right with
      | none => simp [cwBaseProductCheck, hr] at h
      | some right =>
          obtain ⟨hvL, _, _, hpL, hL⟩ := decodeCWBaseChild_sound K _ _ _ left hl
          obtain ⟨hvR, _, _, hpR, hR⟩ := decodeCWBaseChild_sound K _ _ _ right hr
          refine ⟨left, right, rfl, rfl, ⟨hvL, hvR⟩, ?_, ?_⟩
          · exact ⟨Nat.mul_pos hpL.1 hpR.1, Nat.mul_pos hpL.2.1 hpR.2.1,
              Nat.mul_pos hpL.2.2 hpR.2.2⟩
          · exact (Restricts.external hL hR).trans
              (Isomorphic.matrixMultiplication_external (K := K)
                (cwBaseChildDimensions data.q left).1
                (cwBaseChildDimensions data.q left).2.1
                (cwBaseChildDimensions data.q left).2.2
                (cwBaseChildDimensions data.q right).1
                (cwBaseChildDimensions data.q right).2.1
                (cwBaseChildDimensions data.q right).2.2).restricts

end AlgebraicComplexity.Examples
