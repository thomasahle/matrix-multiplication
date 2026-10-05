/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoSupportBridge
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoCountingSplit
import AlgebraicComplexity.MatrixMultiplication.MoreAsymmetryCompatibilityAggregation

/-!
# The depth-one `Z` compatibility tables of section 6.3, and their pooled-all decomposition

`Examples/DuanWuZhouLevelTwoCountingSplit.lean` records `[DuanWuZhou2022]`'s three section 6.3
split tables as bare integer matrices over `Fin 3`, the *ordered left half* of a `Z`-index:

* `dwz63SplitCount : Fin 15 → Fin 3 → ℕ` --- each component's own prescribed split;
* `dwz63PooledCount : Fin 5 → Fin 3 → ℕ` --- the pooled interior requirement at each `Z`-index;
* `dwz63AverageCount : Fin 5 → Fin 3 → ℕ` --- the typicalness rows, pooling *all* components.

`MatrixMultiplication/MoreAsymmetryCompatibilityAggregation.lean` states the compatibility
zero-out over `SplitWord depth` tables instead, and its `PooledAllTargets.z_decompose` field is the
one equation tying the three of them together.  This module builds the bridge at the global stage's
own parameters --- `depth = 1`, `Part = PUnit` --- and proves that equation.

## The ordered-left-digit bridge

At `depth = 1` a split word is a pair of digits, `SplitWord 1 = Fin 2 → Fin 3`, and its weight is
the sum of the two.  A word of prescribed weight is therefore determined by its left digit
(`splitWord_one_eq_of_left_of_weight`), which is exactly `Combinatorics/CompatibleSplitCount.lean`'s
`Fin 3` letter.  `dwz63LiftSplitRow` lifts a row indexed by that letter to a split-word table
supported on the corresponding weight fiber, and this is how all three tables are transported.

## The load-bearing finite identity

`coarseTotal 1 = 4`, so the section 6.3 coarse indices are exactly the triples `(i, j, k)` with
`i + j + k = 4`, and the two canonical boundary constituents of the pooled-all `Z` cell at index
`k` are

`zXBoundaryIndex 1 () k = (0, 4 - k, k)` and `zYBoundaryIndex 1 () k = (4 - k, 0, k)`.

These are precisely the two boundary components of `Z`-index `k` --- `i = 0` forces `j = 4 - k`,
`j = 0` forces `i = 4 - k` --- and they coincide exactly when `k = 4`, which is why
`zBoundaryAggregate` guards the second summand by `k < coarseTotal depth`.  So the equation
`z_decompose` demands is the fifteen-entry integer identity

`average(k, l) = split((0, 4 - k, k), l) + [k < 4] * split((4 - k, 0, k), l) + pooled(k, l)`,

proved here as `dwz63_zAll_eq_zBoundaryAggregate_add_zPooled` and checked against the committed
tables cell by cell.  It is the exact finite shadow of the paper's statement that the typicalness
distribution at a `Z`-index is the `alpha`-weighted mixture of the boundary components' own splits
with the pooled interior split.

## Scope, and what is deliberately absent

This module supplies the `Z` half only: `dwz63ZExact`, `dwz63ZPooled`, `dwz63ZAll` and the
decomposition between them.  It does **not** construct a `CompatibilityTargets PUnit 1`, because
that structure also demands `xExact` and `yExact` tables together with the three
complementation laws `yBoundary`, `zBoundaryOfX`, `zBoundaryOfY`, and section 6.3 has **no
committed `X`/`Y` split tables** --- `better_bound/dwz_endpoint_prep/PREP.md` section 6's data
appendix lists the `Z`-side splits (`a`, `b`, the pooled and average rows) and the free interior
parameter `beta`, but no `X`- or `Y`-indexed split matrix.  Building those tables, and the fine
configuration table that generates all three legs coherently, is genuine additional section 6.3
data; it is recorded as the remaining half of the compatibility tranche rather than assumed here.

## Position in the library

Layer 4 (a client).  Every declaration is either a definitional lift of a committed section 6.3
table or a finite integer identity between committed tables.

Primary source: Ran Duan, Hongxun Wu and Renfei Zhou, *Faster Matrix Multiplication via Asymmetric
Hashing*, arXiv:2210.10173, section 6.3.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor MoreAsymmetryCompatibility

noncomputable section

/-! ## Depth-one split words -/

/-- At depth one the total digit weight is the sum of the two digits. -/
theorem splitWordWeight_one (word : SplitWord 1) :
    splitWordWeight word = (word 0 : ℕ) + (word 1 : ℕ) := by
  show (∑ i : Fin 2, ((word i : Fin 3) : ℕ)) = _
  rw [Fin.sum_univ_two]

/-- A depth-one split word weighs at most `coarseTotal 1 = 4`. -/
theorem splitWordWeight_one_le (word : SplitWord 1) : splitWordWeight word ≤ 4 := by
  rw [splitWordWeight_one]
  have h0 := (word 0).isLt
  have h1 := (word 1).isLt
  omega

/-- **The ordered-left-digit bridge.**  Two depth-one split words of the same weight that agree on
their left digit are equal: on the weight fiber the right digit is determined.  This is what
identifies `SplitWord 1` data with `Combinatorics/CompatibleSplitCount.lean`'s `Fin 3` letter. -/
theorem splitWord_one_eq_of_left_of_weight {left right : SplitWord 1}
    (hleft : left 0 = right 0) (hweight : splitWordWeight left = splitWordWeight right) :
    left = right := by
  rw [splitWordWeight_one, splitWordWeight_one, hleft] at hweight
  have h1 : left 1 = right 1 := Fin.ext (by omega)
  funext position
  fin_cases position
  · exact hleft
  · exact h1

/-- Lift a row indexed by the ordered left half to a depth-one split-word table, supported on the
words of the prescribed weight. -/
def dwz63LiftSplitRow (total : ℕ) (row : Fin 3 → ℕ) (word : SplitWord 1) : ℕ :=
  if splitWordWeight word = total then row (word 0) else 0

@[simp] theorem dwz63LiftSplitRow_of_weight {total : ℕ} {word : SplitWord 1}
    (hweight : splitWordWeight word = total) (row : Fin 3 → ℕ) :
    dwz63LiftSplitRow total row word = row (word 0) := by
  simp [dwz63LiftSplitRow, hweight]

@[simp] theorem dwz63LiftSplitRow_of_weight_ne {total : ℕ} {word : SplitWord 1}
    (hweight : splitWordWeight word ≠ total) (row : Fin 3 → ℕ) :
    dwz63LiftSplitRow total row word = 0 := by
  simp [dwz63LiftSplitRow, hweight]

/-! ## Section 6.3 components as coarse indices -/

/-- The coarse constituent index of a section 6.3 component at the global stage, where the part
tag is trivial. -/
def dwz63CoarseIndex (c : Fin 15) : CoarseIndex PUnit where
  part := PUnit.unit
  x := (dwz63XIndex c : ℕ)
  y := (dwz63YIndex c : ℕ)
  z := (dwz63ZIndex c : ℕ)

/-- Distinct components have distinct coarse indices: the first two coordinates already separate
them, by the lexicographic position map of the support bridge. -/
theorem dwz63CoarseIndex_injective : Function.Injective dwz63CoarseIndex := by
  intro a b h
  have hx : dwz63XIndex a = dwz63XIndex b :=
    Fin.ext (congrArg CoarseIndex.x h)
  have hy : dwz63YIndex a = dwz63YIndex b :=
    Fin.ext (congrArg CoarseIndex.y h)
  have ha := dwz63CellIndex_dwz63Cell a
  have hb := dwz63CellIndex_dwz63Cell b
  have hX : dwz63Cell a Leg.X = dwz63Cell b Leg.X := hx
  have hY : dwz63Cell a Leg.Y = dwz63Cell b Leg.Y := hy
  have hcell : dwz63CellIndex (dwz63Cell a) = dwz63CellIndex (dwz63Cell b) := by
    simp only [dwz63CellIndex, hX, hY]
  rw [← ha, ← hb, hcell]

/-- The prescribed split row of the section 6.3 component sitting at a given coarse index, and
zero at coarse indices that are not components. -/
def dwz63SplitRow (q : CoarseIndex PUnit) (l : Fin 3) : ℕ :=
  ∑ c : Fin 15, if dwz63CoarseIndex c = q then dwz63SplitCount c l else 0

/-- At the coarse index of a component the split row is that component's own prescribed split. -/
theorem dwz63SplitRow_dwz63CoarseIndex (c : Fin 15) (l : Fin 3) :
    dwz63SplitRow (dwz63CoarseIndex c) l = dwz63SplitCount c l := by
  classical
  rw [dwz63SplitRow, Finset.sum_eq_single c]
  · simp
  · intro other _ hother
    have hne : dwz63CoarseIndex other ≠ dwz63CoarseIndex c := fun heq ↦
      hother (dwz63CoarseIndex_injective heq)
    exact if_neg hne
  · intro hc
    exact absurd (Finset.mem_univ c) hc

/-! ## The three depth-one `Z` tables -/

/-- **The exact `Z` target table of section 6.3 at depth one.**  A coarse index that is one of the
fifteen components contributes that component's own prescribed split, on the words whose weight is
its `Z`-index; every other coarse index contributes nothing. -/
def dwz63ZExact (k : ℕ) (q : CoarseIndex PUnit) (word : SplitWord 1) : ℕ :=
  dwz63LiftSplitRow q.z (fun l ↦ dwz63SplitRow q l * k) word

/-- **The positive pooled `Z` target table of section 6.3 at depth one**: the interior components
sharing a `Z`-index are pooled into one requirement whose split is `dwz63PooledCount`. -/
def dwz63ZPooled (k : ℕ) (_part : PUnit) (z : ℕ) (word : SplitWord 1) : ℕ :=
  if hz : z < 5 then
    dwz63LiftSplitRow z (fun l ↦ dwz63PooledCount ⟨z, hz⟩ l * k) word
  else 0

/-- **The pooled-all `Z` target table of section 6.3 at depth one**: the typicalness rows
`dwz63AverageCount`, which pool boundary and interior components alike. -/
def dwz63ZAll (k : ℕ) (_part : PUnit) (z : ℕ) (word : SplitWord 1) : ℕ :=
  if hz : z < 5 then
    dwz63LiftSplitRow z (fun l ↦ dwz63AverageCount ⟨z, hz⟩ l * k) word
  else 0

/-! ## The two canonical boundary constituents -/

/-- `coarseTotal 1` is the level-two total degree `4`. -/
@[simp] theorem coarseTotal_one : coarseTotal 1 = 4 := rfl

@[simp] theorem dwz63_zXBoundaryIndex_z (z : ℕ) :
    (zXBoundaryIndex (Part := PUnit) 1 PUnit.unit z).z = z := rfl

@[simp] theorem dwz63_zYBoundaryIndex_z (z : ℕ) :
    (zYBoundaryIndex (Part := PUnit) 1 PUnit.unit z).z = z := rfl

/-- The `i = 0` boundary constituent of the pooled-all `Z` cell at index `z` is the section 6.3
component `(0, 4 - z, z)`. -/
theorem dwz63CoarseIndex_zXBoundary (c : Fin 15) (z : Fin 5)
    (hx : dwz63XIndex c = 0) (hz : dwz63ZIndex c = z)
    (hy : (dwz63YIndex c : ℕ) = 4 - (z : ℕ)) :
    dwz63CoarseIndex c = zXBoundaryIndex 1 PUnit.unit (z : ℕ) := by
  refine CoarseIndex.ext rfl ?_ ?_ ?_
  · show (dwz63XIndex c : ℕ) = 0
    rw [hx]; rfl
  · show (dwz63YIndex c : ℕ) = coarseTotal 1 - (z : ℕ)
    rw [coarseTotal_one]; exact hy
  · show (dwz63ZIndex c : ℕ) = (z : ℕ)
    rw [hz]

/-- The `j = 0` boundary constituent of the pooled-all `Z` cell at index `z` is the section 6.3
component `(4 - z, 0, z)`. -/
theorem dwz63CoarseIndex_zYBoundary (c : Fin 15) (z : Fin 5)
    (hy : dwz63YIndex c = 0) (hz : dwz63ZIndex c = z)
    (hx : (dwz63XIndex c : ℕ) = 4 - (z : ℕ)) :
    dwz63CoarseIndex c = zYBoundaryIndex 1 PUnit.unit (z : ℕ) := by
  refine CoarseIndex.ext rfl ?_ ?_ ?_
  · show (dwz63XIndex c : ℕ) = coarseTotal 1 - (z : ℕ)
    rw [coarseTotal_one]; exact hx
  · show (dwz63YIndex c : ℕ) = 0
    rw [hy]; rfl
  · show (dwz63ZIndex c : ℕ) = (z : ℕ)
    rw [hz]

/-- The section 6.3 component realizing the `i = 0` boundary constituent at `Z`-index `z`. -/
def dwz63ZXBoundaryCell : Fin 5 → Fin 15 :=
  ![4, 3, 2, 1, 0]

/-- The section 6.3 component realizing the `j = 0` boundary constituent at `Z`-index `z`. -/
def dwz63ZYBoundaryCell : Fin 5 → Fin 15 :=
  ![14, 12, 9, 5, 0]

theorem dwz63SplitRow_zXBoundaryIndex (z : Fin 5) (l : Fin 3) :
    dwz63SplitRow (zXBoundaryIndex 1 PUnit.unit (z : ℕ)) l =
      dwz63SplitCount (dwz63ZXBoundaryCell z) l := by
  have hcell : dwz63CoarseIndex (dwz63ZXBoundaryCell z) =
      zXBoundaryIndex 1 PUnit.unit (z : ℕ) := by
    fin_cases z <;> rfl
  rw [← hcell, dwz63SplitRow_dwz63CoarseIndex]

theorem dwz63SplitRow_zYBoundaryIndex (z : Fin 5) (l : Fin 3) :
    dwz63SplitRow (zYBoundaryIndex 1 PUnit.unit (z : ℕ)) l =
      dwz63SplitCount (dwz63ZYBoundaryCell z) l := by
  have hcell : dwz63CoarseIndex (dwz63ZYBoundaryCell z) =
      zYBoundaryIndex 1 PUnit.unit (z : ℕ) := by
    fin_cases z <;> rfl
  rw [← hcell, dwz63SplitRow_dwz63CoarseIndex]

/-! ## The load-bearing decomposition -/

/-- **The fifteen-entry integer identity behind `PooledAllTargets.z_decompose`.**  At every
`Z`-index and every ordered left half, section 6.3's typicalness row is the sum of the two boundary
components' own prescribed splits --- the second one present exactly when the index is below the
total degree --- and the pooled interior requirement. -/
theorem dwz63AverageCount_eq_boundary_add_pooled (z : Fin 5) (l : Fin 3) :
    dwz63AverageCount z l =
      dwz63SplitCount (dwz63ZXBoundaryCell z) l +
        (if (z : ℕ) < 4 then dwz63SplitCount (dwz63ZYBoundaryCell z) l else 0) +
        dwz63PooledCount z l := by
  fin_cases z <;> fin_cases l <;>
    simp [dwz63AverageCount, dwz63SplitCount, dwz63PooledCount,
      dwz63ZXBoundaryCell, dwz63ZYBoundaryCell]

/-- **`z_decompose` for the section 6.3 depth-one tables.**  The pooled-all `Z` table is the
boundary aggregate of the exact table plus the positive pooled table, in exactly the shape
`MoreAsymmetryCompatibility.CompatibilityTargets.zBoundaryAggregate` prescribes. -/
theorem dwz63_zAll_eq_zBoundaryAggregate_add_zPooled (k : ℕ) (part : PUnit) (z : ℕ)
    (word : SplitWord 1) :
    dwz63ZAll k part z word =
      (dwz63ZExact k (zXBoundaryIndex 1 part z) word +
          (if z < coarseTotal 1 then dwz63ZExact k (zYBoundaryIndex 1 part z) word else 0)) +
        dwz63ZPooled k part z word := by
  cases part
  rcases lt_or_ge z 5 with hz | hz
  · lift z to Fin 5 using hz with z hz
    by_cases hweight : splitWordWeight word = (z : ℕ)
    · have hexactX : dwz63ZExact k (zXBoundaryIndex 1 PUnit.unit (z : ℕ)) word =
          dwz63SplitCount (dwz63ZXBoundaryCell z) (word 0) * k := by
        rw [dwz63ZExact, dwz63_zXBoundaryIndex_z, dwz63LiftSplitRow_of_weight hweight,
          dwz63SplitRow_zXBoundaryIndex]
      have hexactY : dwz63ZExact k (zYBoundaryIndex 1 PUnit.unit (z : ℕ)) word =
          dwz63SplitCount (dwz63ZYBoundaryCell z) (word 0) * k := by
        rw [dwz63ZExact, dwz63_zYBoundaryIndex_z, dwz63LiftSplitRow_of_weight hweight,
          dwz63SplitRow_zYBoundaryIndex]
      have hpooled : dwz63ZPooled k PUnit.unit (z : ℕ) word =
          dwz63PooledCount z (word 0) * k := by
        rw [dwz63ZPooled, dif_pos z.isLt, dwz63LiftSplitRow_of_weight hweight]
      have hall : dwz63ZAll k PUnit.unit (z : ℕ) word =
          dwz63AverageCount z (word 0) * k := by
        rw [dwz63ZAll, dif_pos z.isLt, dwz63LiftSplitRow_of_weight hweight]
      rw [hall, hexactX, hexactY, hpooled, coarseTotal_one,
        dwz63AverageCount_eq_boundary_add_pooled z (word 0)]
      by_cases hlt : (z : ℕ) < 4 <;> simp [hlt, add_mul]
    · rw [dwz63ZAll, dif_pos z.isLt, dwz63LiftSplitRow_of_weight_ne hweight,
        dwz63ZExact, dwz63_zXBoundaryIndex_z, dwz63LiftSplitRow_of_weight_ne hweight,
        dwz63ZExact, dwz63_zYBoundaryIndex_z, dwz63LiftSplitRow_of_weight_ne hweight,
        dwz63ZPooled, dif_pos z.isLt, dwz63LiftSplitRow_of_weight_ne hweight]
      simp only [add_zero, zero_add]
      split <;> rfl
  · have hweight : splitWordWeight word ≠ z := by
      have := splitWordWeight_one_le word
      omega
    rw [dwz63ZAll, dif_neg (by omega),
      dwz63ZExact, dwz63_zXBoundaryIndex_z, dwz63LiftSplitRow_of_weight_ne hweight,
      dwz63ZExact, dwz63_zYBoundaryIndex_z, dwz63LiftSplitRow_of_weight_ne hweight,
      dwz63ZPooled, dif_neg (by omega)]
    simp only [add_zero, zero_add]
    split <;> rfl

end

end AlgebraicComplexity.Examples
