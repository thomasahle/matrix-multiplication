/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Combinatorics.MappedType
import Mathlib.Data.Fintype.Prod

/-!
# Definitions for labelled complementary occurrences

This file defines the two labelled sides of a complementary pair, the resulting occurrence
alphabet, and its integral cell profiles.  Proofs are kept in downstream modules so this reusable
definition layer has a small elaboration and axiom-export footprint.
-/

open scoped BigOperators

namespace AlgebraicComplexity

universe u v

/-- The two labelled sides of a complementary pair. -/
inductive ComplementarySide where
  | left
  | right
  deriving DecidableEq

instance : Fintype ComplementarySide where
  elems := {.left, .right}
  complete side := by cases side <;> simp

/-- A state together with one of its two labelled child occurrences. -/
abbrev ComplementaryOccurrence (State : Type*) := State × ComplementarySide

namespace ComplementaryOccurrence

variable {State : Type u}

/-- Ordered state which generated an occurrence. -/
def orderedState (occurrence : ComplementaryOccurrence State) : State := occurrence.1

/-- Label of an occurrence inside its complementary pair. -/
def side (occurrence : ComplementaryOccurrence State) : ComplementarySide := occurrence.2

/-- Child state seen at an occurrence. -/
def childState (complement : Equiv.Perm State)
    (occurrence : ComplementaryOccurrence State) : State :=
  match occurrence.side with
  | .left => occurrence.orderedState
  | .right => complement occurrence.orderedState

/-- Integral mass of a labelled child occurrence.  Both sides receive the full mass of their
ordered state. -/
def integralMass (profile : State → ℕ) (occurrence : ComplementaryOccurrence State) : ℕ :=
  profile occurrence.orderedState

end ComplementaryOccurrence

section CellProfiles

variable {State : Type u} [Fintype State]
variable {Cell : Type v}

/-- Push the integral profile of labelled child occurrences to compatibility cells. -/
noncomputable def complementaryOccurrenceCellProfile
    (profile : State → ℕ) (complement : Equiv.Perm State)
    (cellOf : State → Cell) : Cell → ℕ :=
  WordType.mappedType
    (fun occurrence : ComplementaryOccurrence State ↦
      cellOf (occurrence.childState complement))
    (fun occurrence ↦ occurrence.integralMass profile)

/-- Evaluator form of the integral cell profile.  A child state receives the sum of its left
mass and the mass of the right occurrence indexed by its preimage under complementation. -/
noncomputable def evaluatorComplementaryCellProfile [DecidableEq Cell]
    (profile : State → ℕ) (complement : Equiv.Perm State)
    (cellOf : State → Cell) : Cell → ℕ :=
  fun cell ↦ ∑ child,
    if cellOf child = cell then profile child + profile (complement.symm child) else 0

end CellProfiles

end AlgebraicComplexity
