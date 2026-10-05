/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.MoreAsymmetryCompatibilityAggregation
import AlgebraicComplexity.MatrixMultiplication.RecursiveChildCompatibilityInjectiveCore
import AlgebraicComplexity.MatrixMultiplication.RecursiveChildOccurrenceProfile
import AlgebraicComplexity.MatrixMultiplication.RecursiveChildShape

set_option autoImplicit false

/-!
# Compatibility model on labelled recursive children

This module is the thin compatibility wrapper around `RecursiveChildOccurrences`.  Parent block
labels are left unchanged, while each parent sample is observed twice: once through its labelled
left half and once through its labelled right half.  The resulting coarse address is the triple
of child weights used by the recursive constituent hash.

The dependency-light half-word and empirical-profile laws live in
`RecursiveChildOccurrences`; tensor-facing clients need this file only when invoking the generic
compatibility zeroing theorems.
-/

namespace AlgebraicComplexity
namespace MoreAsymmetryCompatibility

open Tensor
open scoped BigOperators

universe u v

namespace RecursiveChildShape

/-- Interpret a bounded recursive child shape as the coarse constituent index in one fixed
parent part. -/
def toCoarseIndex {parent : Leg → ℕ} {childTotal : ℕ} {Part : Type v}
    (part : Part) (u : RecursiveChildShape parent childTotal) : CoarseIndex Part where
  part := part
  x := u.get .X
  y := u.get .Y
  z := u.get .Z

@[simp] theorem toCoarseIndex_part
    {parent : Leg → ℕ} {childTotal : ℕ} {Part : Type v}
    (part : Part) (u : RecursiveChildShape parent childTotal) :
    (toCoarseIndex part u).part = part :=
  rfl

@[simp] theorem toCoarseIndex_get
    {parent : Leg → ℕ} {childTotal : ℕ} {Part : Type v}
    (part : Part) (u : RecursiveChildShape parent childTotal) (c : Leg) :
    (toCoarseIndex part u).get c = u.get c := by
  cases c <;> rfl

end RecursiveChildShape

/-- Compatibility model on the two labelled children of every encoded parent chunk. -/
def recursiveChildCompatibilityModel {A : Leg → Type u} {Part : Type v}
    {depth n : ℕ} (encode : ∀ c, A c → SplitWord (depth + 1))
    (partAt : Fin (n + 1) → Part) :
    CompatibilityModel (fun c ↦ PositiveWord (A c) n) Part depth
      ((n + 1) + (n + 1)) where
  chunks c word := positiveWordLabelledChildren (encode c) word
  coarse address sample :=
    { part := labelledChildParts partAt sample
      x := splitWordWeight
        (positiveWordLabelledChildren (encode .X) (address .X) sample)
      y := splitWordWeight
        (positiveWordLabelledChildren (encode .Y) (address .Y) sample)
      z := splitWordWeight
        (positiveWordLabelledChildren (encode .Z) (address .Z) sample) }

@[simp] theorem recursiveChildCompatibilityModel_chunks
    {A : Leg → Type u} {Part : Type v} {depth n : ℕ}
    (encode : ∀ c, A c → SplitWord (depth + 1))
    (partAt : Fin (n + 1) → Part) (c : Leg) (word : PositiveWord (A c) n) :
    (recursiveChildCompatibilityModel encode partAt).chunks c word =
      positiveWordLabelledChildren (encode c) word :=
  rfl

@[simp] theorem recursiveChildCompatibilityModel_coarse_part
    {A : Leg → Type u} {Part : Type v} {depth n : ℕ}
    (encode : ∀ c, A c → SplitWord (depth + 1))
    (partAt : Fin (n + 1) → Part)
    (address : BlockAddress (fun c ↦ PositiveWord (A c) n))
    (sample : Fin ((n + 1) + (n + 1))) :
    ((recursiveChildCompatibilityModel encode partAt).coarse address sample).part =
      labelledChildParts partAt sample :=
  rfl

/-- Coarse child coordinates are definitionally the weights of the exposed child words. -/
theorem recursiveChildCompatibilityModel_hasCoarseWeights
    {A : Leg → Type u} {Part : Type v} {depth n : ℕ}
    (encode : ∀ c, A c → SplitWord (depth + 1))
    (partAt : Fin (n + 1) → Part)
    (address : BlockAddress (fun c ↦ PositiveWord (A c) n)) :
    (recursiveChildCompatibilityModel encode partAt).HasCoarseWeights address := by
  intro c sample
  cases c <;> rfl

/-- Splitting a legal parent address into labelled halves preserves coordinatewise CW legality. -/
theorem recursiveChildCompatibilityModel_isFineLegal
    {A : Leg → Type u} {Part : Type v} {depth n : ℕ}
    (encode : ∀ c, A c → SplitWord (depth + 1))
    (partAt : Fin (n + 1) → Part)
    (address : BlockAddress (fun c ↦ PositiveWord (A c) n))
    (hlegal : IsParentFineLegal encode address) :
    (recursiveChildCompatibilityModel encode partAt).IsFineLegal address :=
  labelledChildren_fineLegal encode address hlegal

/-- On one leg, the two child coarse weights add to the encoded parent weight. -/
theorem recursiveChildCompatibilityModel_coarse_add
    {A : Leg → Type u} {Part : Type v} {depth n : ℕ}
    (encode : ∀ c, A c → SplitWord (depth + 1))
    (partAt : Fin (n + 1) → Part)
    (address : BlockAddress (fun c ↦ PositiveWord (A c) n))
    (c : Leg) (sample : Fin (n + 1)) :
    ((recursiveChildCompatibilityModel encode partAt).coarse address
          (Fin.castAdd (n + 1) sample)).get c +
        ((recursiveChildCompatibilityModel encode partAt).coarse address
          (Fin.natAdd (n + 1) sample)).get c =
      splitWordWeight
        (encode c (positiveWordEquiv (A c) n (address c) sample)) := by
  cases c with
  | X =>
      simp only [recursiveChildCompatibilityModel, CoarseIndex.get,
        positiveWordLabelledChildren_left]
      rw [positiveWordLabelledChildren_right]
      simpa only [leftChildHalf_eq_splitWordSuccEquiv,
        rightChildHalf_eq_splitWordSuccEquiv] using
        (splitWordWeight_succ depth
          (encode .X (positiveWordEquiv (A .X) n (address .X) sample))).symm
  | Y =>
      simp only [recursiveChildCompatibilityModel, CoarseIndex.get,
        positiveWordLabelledChildren_left]
      rw [positiveWordLabelledChildren_right]
      simpa only [leftChildHalf_eq_splitWordSuccEquiv,
        rightChildHalf_eq_splitWordSuccEquiv] using
        (splitWordWeight_succ depth
          (encode .Y (positiveWordEquiv (A .Y) n (address .Y) sample))).symm
  | Z =>
      simp only [recursiveChildCompatibilityModel, CoarseIndex.get,
        positiveWordLabelledChildren_left]
      rw [positiveWordLabelledChildren_right]
      simpa only [leftChildHalf_eq_splitWordSuccEquiv,
        rightChildHalf_eq_splitWordSuccEquiv] using
        (splitWordWeight_succ depth
          (encode .Z (positiveWordEquiv (A .Z) n (address .Z) sample))).symm

/-- If every parent chunk has the constituent's prescribed coordinate, its two labelled child
coordinates sum to that coordinate at every sample. -/
theorem recursiveChildCompatibilityModel_coarse_add_eq_parent
    {A : Leg → Type u} {Part : Type v} {depth n : ℕ}
    (encode : ∀ c, A c → SplitWord (depth + 1))
    (partAt : Fin (n + 1) → Part)
    (address : BlockAddress (fun c ↦ PositiveWord (A c) n))
    (parent : Leg → ℕ)
    (hparent : ∀ c sample,
      splitWordWeight (encode c (positiveWordEquiv (A c) n (address c) sample)) =
        parent c)
    (c : Leg) (sample : Fin (n + 1)) :
    ((recursiveChildCompatibilityModel encode partAt).coarse address
          (Fin.castAdd (n + 1) sample)).get c +
        ((recursiveChildCompatibilityModel encode partAt).coarse address
          (Fin.natAdd (n + 1) sample)).get c =
      parent c := by
  rw [recursiveChildCompatibilityModel_coarse_add, hparent]

/-- The left child at one parent sample, as an element of the finite bounded child-shape
alphabet.  Containment follows from the right child's nonnegative weight; the fixed child total
follows from fine legality. -/
def recursiveLeftChildShape
    {A : Leg → Type u} {Part : Type v} {depth n : ℕ}
    (encode : ∀ c, A c → SplitWord (depth + 1))
    (part : Part)
    (address : BlockAddress (fun c ↦ PositiveWord (A c) n))
    (parent : Leg → ℕ)
    (hparent : ∀ c sample,
      splitWordWeight (encode c (positiveWordEquiv (A c) n (address c) sample)) =
        parent c)
    (hlegal : IsParentFineLegal encode address)
    (sample : Fin (n + 1)) :
    RecursiveChildShape parent (coarseTotal depth) := by
  let model := recursiveChildCompatibilityModel encode (fun _ : Fin (n + 1) ↦ part)
  let q := model.coarse address (Fin.castAdd (n + 1) sample)
  have haddX := recursiveChildCompatibilityModel_coarse_add_eq_parent
    encode (fun _ ↦ part) address parent hparent .X sample
  have haddY := recursiveChildCompatibilityModel_coarse_add_eq_parent
    encode (fun _ ↦ part) address parent hparent .Y sample
  have haddZ := recursiveChildCompatibilityModel_coarse_add_eq_parent
    encode (fun _ ↦ part) address parent hparent .Z sample
  have hfine : model.IsFineLegal address :=
    recursiveChildCompatibilityModel_isFineLegal encode (fun _ ↦ part) address hlegal
  have hweights : model.HasCoarseWeights address :=
    recursiveChildCompatibilityModel_hasCoarseWeights encode (fun _ ↦ part) address
  have htotal := model.coarse_sum_eq_coarseTotal address hfine hweights
    (Fin.castAdd (n + 1) sample)
  refine AlgebraicComplexity.RecursiveChildShape.ofCoordinates
    (fun c ↦ q.get c) ?_ ?_
  · intro c
    cases c with
    | X =>
        change q.x ≤ parent .X
        change q.x + _ = parent .X at haddX
        omega
    | Y =>
        change q.y ≤ parent .Y
        change q.y + _ = parent .Y at haddY
        omega
    | Z =>
        change q.z ≤ parent .Z
        change q.z + _ = parent .Z at haddZ
        omega
  · change q.x + q.y + q.z = coarseTotal depth
    exact htotal

/-- The finite child-shape encoding reproduces the model's left coarse index exactly. -/
theorem recursiveLeftChildShape_toCoarseIndex
    {A : Leg → Type u} {Part : Type v} {depth n : ℕ}
    (encode : ∀ c, A c → SplitWord (depth + 1))
    (part : Part)
    (address : BlockAddress (fun c ↦ PositiveWord (A c) n))
    (parent : Leg → ℕ)
    (hparent : ∀ c sample,
      splitWordWeight (encode c (positiveWordEquiv (A c) n (address c) sample)) =
        parent c)
    (hlegal : IsParentFineLegal encode address)
    (sample : Fin (n + 1)) :
    RecursiveChildShape.toCoarseIndex part
        (recursiveLeftChildShape encode part address parent hparent hlegal sample) =
      (recursiveChildCompatibilityModel encode (fun _ ↦ part)).coarse address
        (Fin.castAdd (n + 1) sample) := by
  apply CoarseIndex.ext
  · simp only [RecursiveChildShape.toCoarseIndex_part,
      recursiveChildCompatibilityModel_coarse_part, labelledChildParts_left]
  · change (recursiveLeftChildShape encode part address parent hparent hlegal sample).get .X =
        ((recursiveChildCompatibilityModel encode (fun _ ↦ part)).coarse address
          (Fin.castAdd (n + 1) sample)).get .X
    simp only [recursiveLeftChildShape,
      AlgebraicComplexity.RecursiveChildShape.get_ofCoordinates]
  · change (recursiveLeftChildShape encode part address parent hparent hlegal sample).get .Y =
        ((recursiveChildCompatibilityModel encode (fun _ ↦ part)).coarse address
          (Fin.castAdd (n + 1) sample)).get .Y
    simp only [recursiveLeftChildShape,
      AlgebraicComplexity.RecursiveChildShape.get_ofCoordinates]
  · change (recursiveLeftChildShape encode part address parent hparent hlegal sample).get .Z =
        ((recursiveChildCompatibilityModel encode (fun _ ↦ part)).coarse address
          (Fin.castAdd (n + 1) sample)).get .Z
    simp only [recursiveLeftChildShape,
      AlgebraicComplexity.RecursiveChildShape.get_ofCoordinates]

/-- The model's right child is the coordinatewise complement of its labelled left child.  This
is the exact finite bridge from a left-child type `alpha` to the paper's occurrence profile
`alpha(u) + alpha(s-u)`. -/
theorem recursiveRightCoarse_eq_complementLeft
    {A : Leg → Type u} {Part : Type v} {depth n : ℕ}
    (encode : ∀ c, A c → SplitWord (depth + 1))
    (part : Part)
    (address : BlockAddress (fun c ↦ PositiveWord (A c) n))
    (parent : Leg → ℕ)
    (hparentTotal : parent .X + parent .Y + parent .Z = 2 * coarseTotal depth)
    (hparent : ∀ c sample,
      splitWordWeight (encode c (positiveWordEquiv (A c) n (address c) sample)) =
        parent c)
    (hlegal : IsParentFineLegal encode address)
    (sample : Fin (n + 1)) :
    (recursiveChildCompatibilityModel encode (fun _ ↦ part)).coarse address
        (Fin.natAdd (n + 1) sample) =
      RecursiveChildShape.toCoarseIndex part
        ((RecursiveChildShape.complementPerm hparentTotal)
          (recursiveLeftChildShape encode part address parent hparent hlegal sample)) := by
  let model := recursiveChildCompatibilityModel encode (fun _ : Fin (n + 1) ↦ part)
  let u := recursiveLeftChildShape encode part address parent hparent hlegal sample
  have hadd (c : Leg) :
      (model.coarse address (Fin.castAdd (n + 1) sample)).get c +
          (model.coarse address (Fin.natAdd (n + 1) sample)).get c = parent c :=
    recursiveChildCompatibilityModel_coarse_add_eq_parent
      encode (fun _ ↦ part) address parent hparent c sample
  have hleft (c : Leg) :
      (model.coarse address (Fin.castAdd (n + 1) sample)).get c = u.get c := by
    rw [← recursiveLeftChildShape_toCoarseIndex
      encode part address parent hparent hlegal sample]
    exact RecursiveChildShape.toCoarseIndex_get part u c
  apply CoarseIndex.ext
  · change (model.coarse address (Fin.natAdd (n + 1) sample)).part = part
    simp only [model, recursiveChildCompatibilityModel_coarse_part,
      labelledChildParts_right]
  · change (model.coarse address (Fin.natAdd (n + 1) sample)).get .X =
        ((RecursiveChildShape.complementPerm hparentTotal) u).get .X
    rw [RecursiveChildShape.complementPerm_apply,
      AlgebraicComplexity.RecursiveChildShape.complement_get]
    have h := hadd .X
    rw [hleft .X] at h
    omega
  · change (model.coarse address (Fin.natAdd (n + 1) sample)).get .Y =
        ((RecursiveChildShape.complementPerm hparentTotal) u).get .Y
    rw [RecursiveChildShape.complementPerm_apply,
      AlgebraicComplexity.RecursiveChildShape.complement_get]
    have h := hadd .Y
    rw [hleft .Y] at h
    omega
  · change (model.coarse address (Fin.natAdd (n + 1) sample)).get .Z =
        ((RecursiveChildShape.complementPerm hparentTotal) u).get .Z
    rw [RecursiveChildShape.complementPerm_apply,
      AlgebraicComplexity.RecursiveChildShape.complement_get]
    have h := hadd .Z
    rw [hleft .Z] at h
    omega

/-- The finite word of labelled child shapes: the left ordered split at each parent sample,
followed by its coordinatewise complement. -/
def recursiveChildShapeWord
    {A : Leg → Type u} {Part : Type v} {depth n : ℕ}
    (encode : ∀ c, A c → SplitWord (depth + 1))
    (part : Part)
    (address : BlockAddress (fun c ↦ PositiveWord (A c) n))
    (parent : Leg → ℕ)
    (hparentTotal : parent .X + parent .Y + parent .Z = 2 * coarseTotal depth)
    (hparent : ∀ c sample,
      splitWordWeight (encode c (positiveWordEquiv (A c) n (address c) sample)) =
        parent c)
    (hlegal : IsParentFineLegal encode address) :
    Fin ((n + 1) + (n + 1)) → RecursiveChildShape parent (coarseTotal depth) :=
  let left := recursiveLeftChildShape encode part address parent hparent hlegal
  Fin.append left ((RecursiveChildShape.complementPerm hparentTotal) ∘ left)

/-- Reading a labelled child shape as a coarse index recovers the compatibility model's complete
coarse word. -/
theorem recursiveChildCompatibilityModel_coarse_eq_shapeWord
    {A : Leg → Type u} {Part : Type v} {depth n : ℕ}
    (encode : ∀ c, A c → SplitWord (depth + 1))
    (part : Part)
    (address : BlockAddress (fun c ↦ PositiveWord (A c) n))
    (parent : Leg → ℕ)
    (hparentTotal : parent .X + parent .Y + parent .Z = 2 * coarseTotal depth)
    (hparent : ∀ c sample,
      splitWordWeight (encode c (positiveWordEquiv (A c) n (address c) sample)) =
        parent c)
    (hlegal : IsParentFineLegal encode address) :
    (recursiveChildCompatibilityModel encode (fun _ ↦ part)).coarse address =
      RecursiveChildShape.toCoarseIndex part ∘
        recursiveChildShapeWord encode part address parent hparentTotal hparent hlegal := by
  funext occurrence
  refine Fin.addCases ?_ ?_ occurrence
  · intro sample
    rw [Function.comp_apply, recursiveChildShapeWord, Fin.append_left]
    exact (recursiveLeftChildShape_toCoarseIndex
      encode part address parent hparent hlegal sample).symm
  · intro sample
    rw [Function.comp_apply, recursiveChildShapeWord, Fin.append_right,
      Function.comp_apply]
    exact recursiveRightCoarse_eq_complementLeft
      encode part address parent hparentTotal hparent hlegal sample

/-- Exact occurrence-multiplicity formula for the finite recursive child-shape word.  This is the
denominator-free form of `alpha(u) + alpha(s-u)` and treats self-complementary shapes correctly. -/
theorem multiplicity_recursiveChildShapeWord_apply
    {A : Leg → Type u} {Part : Type v} {depth n : ℕ}
    (encode : ∀ c, A c → SplitWord (depth + 1))
    (part : Part)
    (address : BlockAddress (fun c ↦ PositiveWord (A c) n))
    (parent : Leg → ℕ)
    (hparentTotal : parent .X + parent .Y + parent .Z = 2 * coarseTotal depth)
    (hparent : ∀ c sample,
      splitWordWeight (encode c (positiveWordEquiv (A c) n (address c) sample)) =
        parent c)
    (hlegal : IsParentFineLegal encode address)
    (u : RecursiveChildShape parent (coarseTotal depth)) :
    WordType.multiplicity
        (recursiveChildShapeWord encode part address parent hparentTotal hparent hlegal) u =
      WordType.multiplicity
          (recursiveLeftChildShape encode part address parent hparent hlegal) u +
        WordType.multiplicity
          (recursiveLeftChildShape encode part address parent hparent hlegal)
            ((RecursiveChildShape.complementPerm hparentTotal).symm u) := by
  exact WordType.multiplicity_append_complement_apply
    (RecursiveChildShape.complementPerm hparentTotal)
    (recursiveLeftChildShape encode part address parent hparent hlegal) u

/-- Selecting an exact integral type `alphaCounts` for the ordered left-child word forces the
paper's full labelled occurrence profile `alpha(u) + alpha(s-u)`.  This theorem has no positivity
assumption, so structural-zero split shapes are represented faithfully. -/
theorem multiplicity_recursiveChildShapeWord_eq_of_leftType
    {A : Leg → Type u} {Part : Type v} {depth n : ℕ}
    (encode : ∀ c, A c → SplitWord (depth + 1))
    (part : Part)
    (address : BlockAddress (fun c ↦ PositiveWord (A c) n))
    (parent : Leg → ℕ)
    (hparentTotal : parent .X + parent .Y + parent .Z = 2 * coarseTotal depth)
    (hparent : ∀ c sample,
      splitWordWeight (encode c (positiveWordEquiv (A c) n (address c) sample)) =
        parent c)
    (hlegal : IsParentFineLegal encode address)
    (alphaCounts : RecursiveChildShape parent (coarseTotal depth) → ℕ)
    (hleft : WordType.multiplicity
      (recursiveLeftChildShape encode part address parent hparent hlegal) = alphaCounts) :
    WordType.multiplicity
        (recursiveChildShapeWord encode part address parent hparentTotal hparent hlegal) =
      fun child ↦ alphaCounts child +
        alphaCounts ((RecursiveChildShape.complementPerm hparentTotal).symm child) := by
  funext child
  rw [multiplicity_recursiveChildShapeWord_apply]
  simp only [hleft]

/-- An exact left-child type automatically has the correct sample mass. -/
theorem sum_eq_of_recursiveLeftChildType
    {A : Leg → Type u} {Part : Type v} {depth n : ℕ}
    (encode : ∀ c, A c → SplitWord (depth + 1))
    (part : Part)
    (address : BlockAddress (fun c ↦ PositiveWord (A c) n))
    (parent : Leg → ℕ)
    (hparent : ∀ c sample,
      splitWordWeight (encode c (positiveWordEquiv (A c) n (address c) sample)) =
        parent c)
    (hlegal : IsParentFineLegal encode address)
    (alphaCounts : RecursiveChildShape parent (coarseTotal depth) → ℕ)
    (hleft : WordType.multiplicity
      (recursiveLeftChildShape encode part address parent hparent hlegal) = alphaCounts) :
    (∑ child, alphaCounts child) = n + 1 := by
  rw [← hleft]
  exact WordType.sum_multiplicity
    (recursiveLeftChildShape encode part address parent hparent hlegal)

/-- The coarse child word is literally the append of its labelled left and right coarse words. -/
theorem recursiveChildCompatibilityModel_coarse_eq_append
    {A : Leg → Type u} {Part : Type v} {depth n : ℕ}
    (encode : ∀ c, A c → SplitWord (depth + 1))
    (partAt : Fin (n + 1) → Part)
    (address : BlockAddress (fun c ↦ PositiveWord (A c) n)) :
    (recursiveChildCompatibilityModel encode partAt).coarse address =
      Fin.append
        (fun sample ↦ (recursiveChildCompatibilityModel encode partAt).coarse address
          (Fin.castAdd (n + 1) sample))
        (fun sample ↦ (recursiveChildCompatibilityModel encode partAt).coarse address
          (Fin.natAdd (n + 1) sample)) := by
  funext occurrence
  refine Fin.addCases ?_ ?_ occurrence
  · intro sample
    rw [Fin.append_left]
  · intro sample
    rw [Fin.append_right]

/-- The empirical child-shape profile is the exact sum of the two labelled profiles. -/
theorem multiplicity_recursiveChildCompatibilityModel_coarse
    {A : Leg → Type u} {Part : Type v} {U : Type*} [Fintype U] {depth n : ℕ}
    (encode : ∀ c, A c → SplitWord (depth + 1))
    (partAt : Fin (n + 1) → Part)
    (address : BlockAddress (fun c ↦ PositiveWord (A c) n))
    (observe : CoarseIndex Part → U) :
    WordType.multiplicity
        (observe ∘ (recursiveChildCompatibilityModel encode partAt).coarse address) =
      WordType.multiplicity
          (fun sample ↦ observe ((recursiveChildCompatibilityModel encode partAt).coarse
            address (Fin.castAdd (n + 1) sample))) +
        WordType.multiplicity
          (fun sample ↦ observe ((recursiveChildCompatibilityModel encode partAt).coarse
            address (Fin.natAdd (n + 1) sample))) := by
  let left : Fin (n + 1) → CoarseIndex Part := fun sample ↦
    (recursiveChildCompatibilityModel encode partAt).coarse address
      (Fin.castAdd (n + 1) sample)
  let right : Fin (n + 1) → CoarseIndex Part := fun sample ↦
    (recursiveChildCompatibilityModel encode partAt).coarse address
      (Fin.natAdd (n + 1) sample)
  have hcoarse :
      (recursiveChildCompatibilityModel encode partAt).coarse address =
        Fin.append left right := by
    simpa only [left, right] using
      recursiveChildCompatibilityModel_coarse_eq_append encode partAt address
  have hmap : observe ∘ (recursiveChildCompatibilityModel encode partAt).coarse address =
      Fin.append (observe ∘ left) (observe ∘ right) := by
    rw [hcoarse]
    funext occurrence
    refine Fin.addCases ?_ ?_ occurrence
    · intro sample
      simp only [Function.comp_apply, Fin.append_left]
    · intro sample
      rw [Function.comp_apply, Fin.append_right, Fin.append_right]
      rfl
  calc
    WordType.multiplicity
        (observe ∘ (recursiveChildCompatibilityModel encode partAt).coarse address) =
        WordType.multiplicity (Fin.append (observe ∘ left) (observe ∘ right)) := by
      rw [hmap]
    _ = WordType.multiplicity (observe ∘ left) +
        WordType.multiplicity (observe ∘ right) :=
      WordType.multiplicity_append (observe ∘ left) (observe ∘ right)
    _ = _ := by
      rfl

end MoreAsymmetryCompatibility
end AlgebraicComplexity
