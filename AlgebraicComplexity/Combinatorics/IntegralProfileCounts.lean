/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Basic

/-!
# Integral profile counts

This module contains the two arithmetic primitives shared by rational typed leaves and normalized
probability profiles. It intentionally has no probability, entropy, word, or tensor imports.
-/

namespace AlgebraicComplexity.WordType

open scoped BigOperators

universe u

variable {I : Type u} [Fintype I]

/-- Multiplicities obtained by repeating a fixed integral profile `k` times. -/
def proportionalCounts (a : I → ℕ) (k : ℕ) : I → ℕ :=
  fun i ↦ a i * k

/-- Total mass of an integral multiplicity profile. -/
def profileMass (a : I → ℕ) : ℕ :=
  ∑ i, a i

end AlgebraicComplexity.WordType
