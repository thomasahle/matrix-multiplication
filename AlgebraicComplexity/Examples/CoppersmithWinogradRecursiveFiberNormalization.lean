/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinogradRecursiveCompetitorCounting
import AlgebraicComplexity.Examples.CoppersmithWinogradRecursiveCleanup

/-!
# Normalizing recursive CW child-word fibers

A positive recursive constituent exposes two labelled children at every parent position.  The
normalization used before sparse hole repair must therefore permute parent positions, carrying the
left and right child of one parent together.  An arbitrary permutation of the `2(n+1)` child
occurrences would not preserve the parent tensor product.

This module defines the paired action and proves its two finite semantic properties:

* it commutes with the concrete labelled-child quotient of a fine CW block word;
* on supported quotient addresses, a permutation matching the tagged ordered-left type carries
  the complete left/right quotient address to the reference address.

The second fact uses tightness to recover every right child from its left child.  It therefore
also handles self-complementary child shapes without identifying their two labelled occurrences.
No hashing estimate, cleanup count, repair theorem, or target-box degeneration is assumed.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor MoreAsymmetryCompatibility

universe u v

/-- Read one leg from the nested product representation of a visible child-coordinate triple. -/
def cwRecursiveCoordinateTripleGet {depth : ℕ} (logicalLeg : Leg) :
    ExactRecursiveSplitType.CoordinateTriple (coarseTotal depth) →
      CWRecursiveChildDigit depth
  | triple => match logicalLeg with
    | .X => triple.1
    | .Y => triple.2.1
    | .Z => triple.2.2

@[simp] theorem cwRecursiveCoordinateTripleGet_logicalLeftTripleWord
    {depth n : ℕ} (sigma : Orientation)
    (address : CWRecursiveCoarseAddress depth n)
    (logicalLeg : Leg) (sample : Fin (n + 1)) :
    cwRecursiveCoordinateTripleGet logicalLeg
        (cwRecursiveLogicalLeftTripleWord sigma address sample) =
      address (sigma logicalLeg) (Fin.castAdd (n + 1) sample) := by
  cases logicalLeg <;> rfl

/-- Relabel both child occurrences of every parent position by the same permutation. -/
def cwRecursivePositionRelabelCoarseAddress (depth n : ℕ)
    (tau : Equiv.Perm (Fin (n + 1)))
    (address : CWRecursiveCoarseAddress depth n) :
    CWRecursiveCoarseAddress depth n :=
  fun physicalLeg occurrence ↦
    Fin.addCases
      (fun sample ↦ address physicalLeg
        (Fin.castAdd (n + 1) (tau sample)))
      (fun sample ↦ address physicalLeg
        (Fin.natAdd (n + 1) (tau sample)))
      occurrence

@[simp] theorem cwRecursivePositionRelabelCoarseAddress_left
    (depth n : ℕ) (tau : Equiv.Perm (Fin (n + 1)))
    (address : CWRecursiveCoarseAddress depth n)
    (physicalLeg : Leg) (sample : Fin (n + 1)) :
    cwRecursivePositionRelabelCoarseAddress depth n tau address physicalLeg
        (Fin.castAdd (n + 1) sample) =
      address physicalLeg (Fin.castAdd (n + 1) (tau sample)) := by
  simp [cwRecursivePositionRelabelCoarseAddress]

@[simp] theorem cwRecursivePositionRelabelCoarseAddress_right
    (depth n : ℕ) (tau : Equiv.Perm (Fin (n + 1)))
    (address : CWRecursiveCoarseAddress depth n)
    (physicalLeg : Leg) (sample : Fin (n + 1)) :
    cwRecursivePositionRelabelCoarseAddress depth n tau address physicalLeg
        (Fin.natAdd (n + 1) sample) =
      address physicalLeg (Fin.natAdd (n + 1) (tau sample)) := by
  rw [cwRecursivePositionRelabelCoarseAddress, Fin.addCases_right]

/-- The concrete child quotient commutes with paired parent-position relabelling. -/
theorem cwRecursiveLabelledChildWord_positionRelabel
    (depth n : ℕ) (tau : Equiv.Perm (Fin (n + 1)))
    (word : PositiveWord (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n) :
    cwRecursiveLabelledChildWord depth n
        (positiveWordPositionEquiv
          (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n tau word) =
      Fin.addCases
        (fun sample ↦ cwRecursiveLabelledChildWord depth n word
          (Fin.castAdd (n + 1) (tau sample)))
        (fun sample ↦ cwRecursiveLabelledChildWord depth n word
          (Fin.natAdd (n + 1) (tau sample))) := by
  funext occurrence
  refine Fin.addCases ?_ ?_ occurrence <;> intro sample
  · simp [cwRecursiveLabelledChildWord, Function.comp_apply]
  · rw [Fin.addCases_right, cwRecursiveLabelledChildWord, Fin.append_right,
      cwRecursiveLabelledChildWord, Fin.append_right]
    simp [positiveWordPositionEquiv, Function.comp_apply]

/-- Grouping a fine address by labelled children commutes with the paired action. -/
theorem cwRecursiveChildGroup_positionRelabel
    (depth n : ℕ) (tau : Equiv.Perm (Fin (n + 1)))
    (address : BlockAddress (fun _c ↦
      PositiveWord (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n)) :
    cwRecursiveChildGroup depth n
        (fun physicalLeg ↦ positiveWordPositionEquiv
          (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n tau
            (address physicalLeg)) =
      cwRecursivePositionRelabelCoarseAddress depth n tau
        (cwRecursiveChildGroup depth n address) := by
  funext physicalLeg occurrence
  have hword := congrFun
    (cwRecursiveLabelledChildWord_positionRelabel
      depth n tau (address physicalLeg)) occurrence
  exact hword

/-- The permutation of the full occurrence index induced by one parent-position permutation. -/
def cwRecursiveOccurrencePositionEquiv {n : ℕ}
    (tau : Equiv.Perm (Fin (n + 1))) :
    Equiv.Perm (Fin ((n + 1) + (n + 1))) :=
  finSumFinEquiv.symm.trans
    ((Equiv.sumCongr tau tau).trans finSumFinEquiv)

@[simp] theorem cwRecursiveOccurrencePositionEquiv_castAdd
    {n : ℕ} (tau : Equiv.Perm (Fin (n + 1)))
    (sample : Fin (n + 1)) :
    cwRecursiveOccurrencePositionEquiv tau (Fin.castAdd (n + 1) sample) =
      Fin.castAdd (n + 1) (tau sample) := by
  simp [cwRecursiveOccurrencePositionEquiv]

@[simp] theorem cwRecursiveOccurrencePositionEquiv_natAdd
    {n : ℕ} (tau : Equiv.Perm (Fin (n + 1)))
    (sample : Fin (n + 1)) :
    cwRecursiveOccurrencePositionEquiv tau (Fin.natAdd (n + 1) sample) =
      Fin.natAdd (n + 1) (tau sample) := by
  simp only [cwRecursiveOccurrencePositionEquiv, Equiv.trans_apply,
    finSumFinEquiv_symm_apply_natAdd, Equiv.sumCongr_apply, Sum.map_inr,
    finSumFinEquiv_apply_right]

/-- Function form of paired quotient relabelling, used by cell-multiplicity invariance. -/
theorem cwRecursivePositionRelabelCoarseAddress_apply_eq_comp
    (depth n : ℕ) (tau : Equiv.Perm (Fin (n + 1)))
    (address : CWRecursiveCoarseAddress depth n) (physicalLeg : Leg) :
    cwRecursivePositionRelabelCoarseAddress depth n tau address physicalLeg =
      address physicalLeg ∘ cwRecursiveOccurrencePositionEquiv tau := by
  funext occurrence
  refine Fin.addCases ?_ ?_ occurrence <;> intro sample
  · simp [Function.comp_apply]
  · rw [cwRecursivePositionRelabelCoarseAddress_right]
    simp only [Function.comp_apply, cwRecursiveOccurrencePositionEquiv_natAdd]

/-- Function-composition form of child-word equivariance. -/
theorem cwRecursiveLabelledChildWord_positionRelabel_eq_comp
    (depth n : ℕ) (tau : Equiv.Perm (Fin (n + 1)))
    (word : PositiveWord (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n) :
    cwRecursiveLabelledChildWord depth n
        (positiveWordPositionEquiv
          (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n tau word) =
    cwRecursiveLabelledChildWord depth n word ∘
        cwRecursiveOccurrencePositionEquiv tau := by
  rw [cwRecursiveLabelledChildWord_positionRelabel]
  funext occurrence
  refine Fin.addCases ?_ ?_ occurrence <;> intro sample
  · simp [Function.comp_apply]
  · rw [Fin.addCases_right]
    simp only [Function.comp_apply, cwRecursiveOccurrencePositionEquiv_natAdd]

/-- Finite tagged alphabet used to normalize one recursive node-region family. -/
abbrev CWRecursiveTaggedLeftTriple (Part : Type v) (depth : ℕ) :=
  Part × ExactRecursiveSplitType.CoordinateTriple (coarseTotal depth)

/-- The region tag and ordered-left child shape at one parent position. -/
def cwRecursiveTaggedLeftTripleWord
    {Part : Type v} {depth n : ℕ}
    (partAt : Fin (n + 1) → Part) (sigma : Orientation)
    (address : CWRecursiveCoarseAddress depth n) :
    Fin (n + 1) → CWRecursiveTaggedLeftTriple Part depth :=
  fun sample ↦
    (partAt sample, cwRecursiveLogicalLeftTripleWord sigma address sample)

/-- Canonical parent-position permutation between two recursively grouped addresses having the
same tagged ordered-left type. -/
noncomputable def cwRecursivePositionPermOfSameTaggedMultiplicity
    {Part : Type v} [Fintype Part] {depth n : ℕ}
    (partAt : Fin (n + 1) → Part) (sigma : Orientation)
    (left right : CWRecursiveCoarseAddress depth n)
    (h : WordType.multiplicity
        (cwRecursiveTaggedLeftTripleWord partAt sigma left) =
      WordType.multiplicity
        (cwRecursiveTaggedLeftTripleWord partAt sigma right)) :
    Equiv.Perm (Fin (n + 1)) :=
  WordType.positionPermOfSameMultiplicity
    (cwRecursiveTaggedLeftTripleWord partAt sigma left)
    (cwRecursiveTaggedLeftTripleWord partAt sigma right) h

/-- The canonical permutation sends the tagged ordered-left word of `right` to that of `left`. -/
theorem cwRecursiveTaggedLeftTripleWord_positionPermOfSameMultiplicity
    {Part : Type v} [Fintype Part] {depth n : ℕ}
    (partAt : Fin (n + 1) → Part) (sigma : Orientation)
    (left right : CWRecursiveCoarseAddress depth n)
    (h : WordType.multiplicity
        (cwRecursiveTaggedLeftTripleWord partAt sigma left) =
      WordType.multiplicity
        (cwRecursiveTaggedLeftTripleWord partAt sigma right)) :
    cwRecursiveTaggedLeftTripleWord partAt sigma right ∘
        cwRecursivePositionPermOfSameTaggedMultiplicity
          partAt sigma left right h =
      cwRecursiveTaggedLeftTripleWord partAt sigma left :=
  WordType.positionPermOfSameMultiplicity_map
    (cwRecursiveTaggedLeftTripleWord partAt sigma left)
    (cwRecursiveTaggedLeftTripleWord partAt sigma right) h

/-- The normalization permutation preserves the node/region tag. -/
theorem partAt_comp_cwRecursivePositionPermOfSameTaggedMultiplicity
    {Part : Type v} [Fintype Part] {depth n : ℕ}
    (partAt : Fin (n + 1) → Part) (sigma : Orientation)
    (left right : CWRecursiveCoarseAddress depth n)
    (h : WordType.multiplicity
        (cwRecursiveTaggedLeftTripleWord partAt sigma left) =
      WordType.multiplicity
        (cwRecursiveTaggedLeftTripleWord partAt sigma right)) :
    partAt ∘ cwRecursivePositionPermOfSameTaggedMultiplicity
        partAt sigma left right h = partAt := by
  funext sample
  have hmap := congrFun
    (cwRecursiveTaggedLeftTripleWord_positionPermOfSameMultiplicity
      partAt sigma left right h) sample
  exact congrArg Prod.fst hmap

/-- Matching the tagged ordered-left type matches the complete supported left/right quotient.

The right half is not an extra type hypothesis: tightness of the supported CW quotient recovers it
coordinatewise from the left half and the fixed parent constituent. -/
theorem cwRecursivePositionRelabelCoarseAddress_positionPermOfSameTaggedMultiplicity_of_totals
    {Part : Type v} [Fintype Part] {depth n : ℕ}
    (partAt : Fin (n + 1) → Part) (sigma : Orientation)
    (parentCount : Leg → ℕ)
    (left right : CWRecursiveCoarseAddress depth n)
    (hleftTotal : ∀ physicalLeg sample,
      (left physicalLeg (Fin.castAdd (n + 1) sample) : ℕ) +
          (left physicalLeg (Fin.natAdd (n + 1) sample) : ℕ) =
        parentCount physicalLeg)
    (hrightTotal : ∀ physicalLeg sample,
      (right physicalLeg (Fin.castAdd (n + 1) sample) : ℕ) +
          (right physicalLeg (Fin.natAdd (n + 1) sample) : ℕ) =
        parentCount physicalLeg)
    (htype : WordType.multiplicity
        (cwRecursiveTaggedLeftTripleWord partAt sigma left) =
      WordType.multiplicity
        (cwRecursiveTaggedLeftTripleWord partAt sigma right)) :
    cwRecursivePositionRelabelCoarseAddress depth n
        (cwRecursivePositionPermOfSameTaggedMultiplicity
          partAt sigma left right htype) right = left := by
  let tau := cwRecursivePositionPermOfSameTaggedMultiplicity
    partAt sigma left right htype
  have hmap := cwRecursiveTaggedLeftTripleWord_positionPermOfSameMultiplicity
    partAt sigma left right htype
  funext physicalLeg occurrence
  let logicalLeg := sigma.symm physicalLeg
  have hphysical : sigma logicalLeg = physicalLeg := sigma.apply_symm_apply physicalLeg
  refine Fin.addCases ?_ ?_ occurrence <;> intro sample
  · have hcoordinate := congrArg
      (fun tagged ↦ cwRecursiveCoordinateTripleGet logicalLeg tagged.2)
      (congrFun hmap sample)
    simpa [tau, hphysical, cwRecursiveTaggedLeftTripleWord] using hcoordinate
  · apply Fin.ext
    have hcoordinate := congrArg
      (fun tagged ↦
        (cwRecursiveCoordinateTripleGet logicalLeg tagged.2 : ℕ))
      (congrFun hmap sample)
    have hrightSum := hrightTotal physicalLeg (tau sample)
    have hleftSum := hleftTotal physicalLeg sample
    have hleftCoordinate :
        (right physicalLeg (Fin.castAdd (n + 1) (tau sample)) : ℕ) =
          (left physicalLeg (Fin.castAdd (n + 1) sample) : ℕ) := by
      simpa [tau, hphysical, cwRecursiveTaggedLeftTripleWord] using hcoordinate
    simp only [cwRecursivePositionRelabelCoarseAddress_right]
    rw [hleftCoordinate] at hrightSum
    exact Nat.add_left_cancel (hrightSum.trans hleftSum.symm)

/-- Fine-support specialization of
`cwRecursivePositionRelabelCoarseAddress_positionPermOfSameTaggedMultiplicity_of_totals`.
Support is used only to derive the fixed left-plus-right parent totals. -/
theorem cwRecursivePositionRelabelCoarseAddress_positionPermOfSameTaggedMultiplicity
    (K : Type u) [CommRing K] (q : ℕ)
    {Part : Type v} [Fintype Part] {depth n : ℕ}
    (partAt : Fin (n + 1) → Part)
    (term : ExactInterfaceTermParameters (depth + 1))
    (hmultiplicity : term.multiplicity = n + 1)
    (sigma : Orientation)
    (alpha : ExactRecursiveSplitType
      (cwRecursiveLogicalParent term sigma) (coarseTotal depth) (n + 1))
    (left right : CWRecursiveCoarseAddress depth n)
    (hleft : left ∈ (cwRecursiveCoarsenedAlphaMarginalTerm
      K q term hmultiplicity sigma alpha).support)
    (hright : right ∈ (cwRecursiveCoarsenedAlphaMarginalTerm
      K q term hmultiplicity sigma alpha).support)
    (htype : WordType.multiplicity
        (cwRecursiveTaggedLeftTripleWord partAt sigma left) =
      WordType.multiplicity
        (cwRecursiveTaggedLeftTripleWord partAt sigma right)) :
    cwRecursivePositionRelabelCoarseAddress depth n
        (cwRecursivePositionPermOfSameTaggedMultiplicity
          partAt sigma left right htype) right = left := by
  apply
    cwRecursivePositionRelabelCoarseAddress_positionPermOfSameTaggedMultiplicity_of_totals
      partAt sigma term.index.count left right
  · exact fun physicalLeg sample ↦
      cwRecursiveCoarsenedAlphaMarginalTerm_left_add_right
        K q term hmultiplicity sigma alpha left hleft physicalLeg sample
  · exact fun physicalLeg sample ↦
      cwRecursiveCoarsenedAlphaMarginalTerm_left_add_right
        K q term hmultiplicity sigma alpha right hright physicalLeg sample

end AlgebraicComplexity.Examples
