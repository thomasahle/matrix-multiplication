/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoOrientationTypical
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoCounting
import AlgebraicComplexity.Combinatorics.MappedTypeIdentities

/-!
# The three leg marginals of the fifteen-cell distribution

Layer 4 (`AlgebraicComplexity/Examples/`).  `dwz63Alpha` has three coordinate marginals, and
`dwz63AlphaAddress` --- the same distribution on the coarse square's own address space --- has the
corresponding three leg marginals.  This module is nothing but those, together with the fact that
`dwz63AlphaAddress` charges only the fifteen coarse cells.

It exists to sit **below the orientation machinery**.  The same three marginals are read by the
six-orientation development and by the plain fifteen-block one, and neither should have to import
the other to get them: the statements mention `dwz63AlphaAddress`, `cwSquareSupport` and the
committed coordinate marginals of `Examples/DuanWuZhouLevelTwoCounting.lean`, and nothing about
digits, orientations or block words.  So the cone here is exactly `DuanWuZhouLevelTwoCounting`,
`DuanWuZhouLevelTwoOrientationTypical` (for `dwz63AlphaAddress` and `dwz63CellAddress`) and
`Combinatorics/MappedTypeIdentities`.

Primary source: Ran Duan, Hongxun Wu and Renfei Zhou, *Faster Matrix Multiplication via Asymmetric
Hashing*, arXiv:2210.10173, section 6.3 and `table:result-2nd`.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor

open scoped BigOperators

universe u

/-! ## The three coordinate marginals, bundled by leg -/

/-- **The three coordinate marginals of the fifteen-cell distribution, bundled by leg.**  The
level-two distribution is symmetric in its first two coordinates, so the `X` and `Y` legs carry the
same five-letter table. -/
def dwz63AlphaMarginal : Leg → Fin 5 → ℕ
  | .X => dwz63AlphaX
  | .Y => dwz63AlphaX
  | .Z => dwz63AlphaZ

@[simp] theorem dwz63AlphaMarginal_X : dwz63AlphaMarginal .X = dwz63AlphaX := rfl

@[simp] theorem dwz63AlphaMarginal_Y : dwz63AlphaMarginal .Y = dwz63AlphaX := rfl

@[simp] theorem dwz63AlphaMarginal_Z : dwz63AlphaMarginal .Z = dwz63AlphaZ := rfl

theorem profileMass_dwz63AlphaMarginal (c : Leg) :
    WordType.profileMass (dwz63AlphaMarginal c) = 100000000 := by
  cases c
  · exact profileMass_dwz63AlphaX
  · exact profileMass_dwz63AlphaX
  · exact profileMass_dwz63AlphaZ

-- ELABORATION RISK: the three `exact`s below need `(fun s ↦ s c) ∘ dwz63CellAddress` to reduce to
-- `dwz63XIndex` / `dwz63YIndex` / `dwz63ZIndex` definitionally, which it does because
-- `dwz63CellAddress` matches on the leg.  Fallback if it does not: precede each by
-- `refine (WordType.mappedType_congr (fun _ ↦ rfl) dwz63Alpha).trans ?_`.
/-- **Reading one leg of the coarse-address profile is the corresponding coordinate marginal.**
This is `mappedType_dwz63XIndex_dwz63Alpha` and its two siblings, transported from the fifteen-cell
alphabet to the coarse square's own address space along `dwz63CellAddress`. -/
theorem mappedType_legRead_dwz63AlphaAddress (c : Leg) :
    WordType.mappedType (fun s : CWSquareAddress ↦ s c) dwz63AlphaAddress =
      dwz63AlphaMarginal c := by
  unfold dwz63AlphaAddress
  rw [WordType.mappedType_comp]
  cases c
  · exact mappedType_dwz63XIndex_dwz63Alpha
  · exact mappedType_dwz63YIndex_dwz63Alpha
  · exact mappedType_dwz63ZIndex_dwz63Alpha

/-- The repeated form, which is what a typical word's marginal type is. -/
theorem mappedType_legRead_proportionalCounts (c : Leg) (t : ℕ) :
    WordType.mappedType (fun s : CWSquareAddress ↦ s c)
        (WordType.proportionalCounts dwz63AlphaAddress t) =
      WordType.proportionalCounts (dwz63AlphaMarginal c) t := by
  rw [mappedType_proportionalCounts, mappedType_legRead_dwz63AlphaAddress]

/-! ## The address-space profile is supported on the fifteen coarse cells -/

/-- **Only the fifteen coarse cells carry mass.**  The address-space profile is a pushforward along
`dwz63CellAddress`, whose image is the degree-four antidiagonal. -/
theorem mem_cwSquareSupport_of_dwz63AlphaAddress_ne_zero {s : CWSquareAddress}
    (hs : dwz63AlphaAddress s ≠ 0) : s ∈ cwSquareSupport := by
  unfold dwz63AlphaAddress at hs
  obtain ⟨i, hi, -⟩ := WordType.exists_of_mappedType_ne_zero hs
  rw [← hi, cwSquareSupport_eq_antidiagonal]
  fin_cases i <;> decide

end AlgebraicComplexity.Examples
