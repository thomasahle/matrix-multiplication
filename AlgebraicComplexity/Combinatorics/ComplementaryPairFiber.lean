/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Combinatorics.MappedType

/-!
# A two-point complementary fiber

This file computes the pushed mass of one fiber known to be exactly `{u, dual u}`.  The result is
kept separate from the more general representative-set decomposition because clients with a
literal two-point fiber should not pay for or instantiate that stronger enumeration theorem.

A fixed point contributes once, as appropriate for an unlabelled set-valued fiber.  This remains
different from the labelled-occurrence boundary law, where the two child occurrences count twice
even if their states agree.
-/

open scoped BigOperators

namespace AlgebraicComplexity.WordType

universe u v

variable {Split : Type u} [Fintype Split] [DecidableEq Split] {Cell : Type v}

/-- The mass of the unlabelled set `{u, dual u}`; a fixed point occurs once.

Proof sketch: the fiber hypothesis and invariance identify `letterFiber cellMap (cellMap u)` with
the two-element finset `{u, dual u}`.  Summing that finset gives either one term at a fixed point or
the two complementary terms otherwise. -/
theorem mappedType_apply_of_complementary_pair
    (cellMap : Split → Cell) (dual : Split → Split) (_hdual : Function.Involutive dual)
    (hinv : ∀ u, cellMap (dual u) = cellMap u)
    (p : Split → ℕ) (u : Split)
    (hfiber : ∀ v, cellMap v = cellMap u → v = u ∨ v = dual u) :
    mappedType cellMap p (cellMap u) =
      if dual u = u then p u else p u + p (dual u) := by
  classical
  have hfiberSet : letterFiber cellMap (cellMap u) = {u, dual u} := by
    ext v
    rw [mem_letterFiber]
    simp only [Finset.mem_insert, Finset.mem_singleton]
    constructor
    · exact hfiber v
    · intro hv
      rcases hv with rfl | rfl
      · rfl
      · exact hinv u
  change (∑ v ∈ letterFiber cellMap (cellMap u), p v) = _
  rw [hfiberSet]
  by_cases hfixed : dual u = u
  · simp [hfixed]
  · simp [hfixed, Ne.symm hfixed]

end AlgebraicComplexity.WordType
