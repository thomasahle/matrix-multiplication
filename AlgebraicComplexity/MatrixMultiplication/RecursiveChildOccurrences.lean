/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Tensor.Leg
import AlgebraicComplexity.Tensor.PositiveWord
import Mathlib.Logic.Equiv.Fin.Basic

set_option autoImplicit false

/-!
# Labelled child occurrences of recursive complete-split words

The recursive constituent theorem hashes the two consecutive halves of each parent
complete-split chunk.  For `samples` parent chunks this produces `samples + samples` labelled
child positions: all left children followed by all right children.  The distinction is semantic,
not cosmetic.  Inside a fixed parent constituent the whole-parent weight is constant, whereas
the left-child weight is the ordered split variable used by the theorem.

This dependency-light module proves the exact word identities needed at that boundary.  Its
`RecursiveSplitWord` abbreviation is definitionally the same finite function type as the public
`SplitWord`, without importing the much larger interface-profile theory.  It does not import
compatibility zeroing or partitioned tensor realization.  The downstream
`RecursiveChildCompatibilityModel` merely packages these definitions as a `CompatibilityModel`.
-/

namespace AlgebraicComplexity

open Tensor

universe u v

/-! ## The two consecutive halves of one parent word -/

/-- Dependency-light spelling of one complete-split digit. -/
abbrev RecursiveSplitDigit := Fin 3

/-- Dependency-light spelling of a depth-`depth` complete-split word.  This is definitionally
equal to `SplitWord depth` in `InterfaceTensor`. -/
abbrev RecursiveSplitWord (depth : ℕ) := Fin (2 ^ depth) → RecursiveSplitDigit

/-- Split the positions of a parent word into its two consecutive halves. -/
def recursiveSplitIndexSuccEquiv (depth : ℕ) :
    Fin (2 ^ (depth + 1)) ≃ Fin (2 ^ depth) ⊕ Fin (2 ^ depth) :=
  (finCongr (by simp [pow_succ, Nat.mul_two])).trans
    (@finSumFinEquiv (2 ^ depth) (2 ^ depth)).symm

/-- The labelled left half of a parent complete-split word. -/
def leftChildHalf {depth : ℕ} (parent : RecursiveSplitWord (depth + 1)) :
    RecursiveSplitWord depth :=
  fun position ↦ parent ((recursiveSplitIndexSuccEquiv depth).symm (Sum.inl position))

/-- The labelled right half of a parent complete-split word. -/
def rightChildHalf {depth : ℕ} (parent : RecursiveSplitWord (depth + 1)) :
    RecursiveSplitWord depth :=
  fun position ↦ parent ((recursiveSplitIndexSuccEquiv depth).symm (Sum.inr position))

/-- Embed a left-child position into the corresponding position of its parent word. -/
def leftChildPosition (depth : ℕ) (position : Fin (2 ^ depth)) :
    Fin (2 ^ (depth + 1)) :=
  (recursiveSplitIndexSuccEquiv depth).symm (Sum.inl position)

/-- Embed a right-child position into the corresponding position of its parent word. -/
def rightChildPosition (depth : ℕ) (position : Fin (2 ^ depth)) :
    Fin (2 ^ (depth + 1)) :=
  (recursiveSplitIndexSuccEquiv depth).symm (Sum.inr position)

@[simp] theorem leftChildHalf_apply {depth : ℕ} (parent : RecursiveSplitWord (depth + 1))
    (position : Fin (2 ^ depth)) :
    leftChildHalf parent position = parent (leftChildPosition depth position) :=
  rfl

@[simp] theorem rightChildHalf_apply {depth : ℕ} (parent : RecursiveSplitWord (depth + 1))
    (position : Fin (2 ^ depth)) :
    rightChildHalf parent position = parent (rightChildPosition depth position) :=
  rfl

/-! ## Labelled child sequences -/

/-- The left-child sequence obtained by splitting every encoded parent chunk. -/
def positiveWordLeftChildren {A : Type u} {depth n : ℕ}
    (encode : A → RecursiveSplitWord (depth + 1)) (word : PositiveWord A n) :
    Fin (n + 1) → RecursiveSplitWord depth :=
  fun sample ↦ leftChildHalf (encode (positiveWordEquiv A n word sample))

/-- The right-child sequence obtained by splitting every encoded parent chunk. -/
def positiveWordRightChildren {A : Type u} {depth n : ℕ}
    (encode : A → RecursiveSplitWord (depth + 1)) (word : PositiveWord A n) :
    Fin (n + 1) → RecursiveSplitWord depth :=
  fun sample ↦ rightChildHalf (encode (positiveWordEquiv A n word sample))

/-- The paper's `2 n_t` labelled child positions, ordered as all left occurrences followed by
all right occurrences. -/
def positiveWordLabelledChildren {A : Type u} {depth n : ℕ}
    (encode : A → RecursiveSplitWord (depth + 1)) (word : PositiveWord A n) :
    Fin ((n + 1) + (n + 1)) → RecursiveSplitWord depth :=
  Fin.append (positiveWordLeftChildren encode word) (positiveWordRightChildren encode word)

@[simp] theorem positiveWordLabelledChildren_left {A : Type u} {depth n : ℕ}
    (encode : A → RecursiveSplitWord (depth + 1)) (word : PositiveWord A n)
    (sample : Fin (n + 1)) :
    positiveWordLabelledChildren encode word (Fin.castAdd (n + 1) sample) =
      leftChildHalf (encode (positiveWordEquiv A n word sample)) := by
  simp [positiveWordLabelledChildren, positiveWordLeftChildren]

@[simp] theorem positiveWordLabelledChildren_right {A : Type u} {depth n : ℕ}
    (encode : A → RecursiveSplitWord (depth + 1)) (word : PositiveWord A n)
    (sample : Fin (n + 1)) :
    positiveWordLabelledChildren encode word (Fin.natAdd (n + 1) sample) =
      rightChildHalf (encode (positiveWordEquiv A n word sample)) := by
  change Fin.append (positiveWordLeftChildren encode word)
      (positiveWordRightChildren encode word) (Fin.natAdd (n + 1) sample) = _
  rw [Fin.append_right]
  rfl

/-- Duplicate a per-parent tag on the two labelled child sequences. -/
def labelledChildParts {Part : Type v} {samples : ℕ}
    (partAt : Fin samples → Part) : Fin (samples + samples) → Part :=
  Fin.append partAt partAt

@[simp] theorem labelledChildParts_left {Part : Type v} {samples : ℕ}
    (partAt : Fin samples → Part) (sample : Fin samples) :
    labelledChildParts partAt (Fin.castAdd samples sample) = partAt sample := by
  simp [labelledChildParts]

@[simp] theorem labelledChildParts_right {Part : Type v} {samples : ℕ}
    (partAt : Fin samples → Part) (sample : Fin samples) :
    labelledChildParts partAt (Fin.natAdd samples sample) = partAt sample := by
  change Fin.append partAt partAt (Fin.natAdd samples sample) = _
  rw [Fin.append_right]

/-! ## Fine legality -/

/-- Fine legality of encoded parent chunks on a positive-word address. -/
def IsParentFineLegal {A : Leg → Type u} {depth n : ℕ}
    (encode : ∀ c, A c → RecursiveSplitWord (depth + 1))
    (address : ∀ c, PositiveWord (A c) n) : Prop :=
  ∀ sample position,
    (encode .X (positiveWordEquiv (A .X) n (address .X) sample) position : ℕ) +
      (encode .Y (positiveWordEquiv (A .Y) n (address .Y) sample) position : ℕ) +
      (encode .Z (positiveWordEquiv (A .Z) n (address .Z) sample) position : ℕ) = 2

/-- The three labelled child sequences remain coordinatewise legal at every child position. -/
theorem labelledChildren_fineLegal
    {A : Leg → Type u} {depth n : ℕ}
    (encode : ∀ c, A c → RecursiveSplitWord (depth + 1))
    (address : ∀ c, PositiveWord (A c) n)
    (hlegal : IsParentFineLegal encode address) :
    ∀ occurrence position,
      (positiveWordLabelledChildren (encode .X) (address .X) occurrence position : ℕ) +
        (positiveWordLabelledChildren (encode .Y) (address .Y) occurrence position : ℕ) +
        (positiveWordLabelledChildren (encode .Z) (address .Z) occurrence position : ℕ) = 2 := by
  intro occurrence position
  refine Fin.addCases ?_ ?_ occurrence
  · intro sample
    simpa using hlegal sample (leftChildPosition depth position)
  · intro sample
    rw [positiveWordLabelledChildren_right,
      positiveWordLabelledChildren_right,
      positiveWordLabelledChildren_right]
    exact hlegal sample (rightChildPosition depth position)

end AlgebraicComplexity
