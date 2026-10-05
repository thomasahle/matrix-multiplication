/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoCounting
import AlgebraicComplexity.Examples.CoppersmithWinogradSquare

/-!
# The fifteen `alphaTilde` rows of `[DuanWuZhou2022]` section 6.3

Layer 4 (`AlgebraicComplexity/Examples/`).  The `Z`-marginal split distribution of each level-two
component, as an **integral left-digit profile** over `CWBlock`, ready for the segmented Hole
Lemma's `alpha : Fin m -> CWBlock -> ℕ`.

## What the paper actually specifies

`global_value.tex:336-348` fixes all fifteen rows explicitly, and only **three** carry a parameter:

* `(0,2,2)` and `(2,0,2)`: `α̃(0) = α̃(2) = a`, `α̃(1) = 1 - 2a`, with `a = dwz63A`;
* `(1,1,2)`: `α̃(0) = α̃(2) = b`, `α̃(1) = 1 - 2b`, with `b = dwz63B`;
* **all others**: "we use the symmetric `Z`-marginal split distributions, that is,
  `α̃_{i,j,1}(0) = α̃_{i,j,1}(1) = 1/2` and `α̃_{i,j,3}(1) = α̃_{i,j,3}(2) = 1/2` for all valid
  `i,j`; for components `(i,j,0)` or `(i,j,4)` there is only one `Z`-marginal split distribution."

That sentence names `(2,2,0)`, `(1,2,1)` and `(2,1,1)` among the components whose values "do not
change", so **`(1,2,1)` and `(2,1,1)` are symmetric-split cells, not parameterised ones**, and
`lem:non-rot-values` (`second_power.tex:145-158`) likewise restricts only the `k = 2` components.
`hole_lemma.tex:7` says the same: "we are only restricting the `Z`-split distribution of those
`T_{i,j,k}`'s with `k = 2`".

**`dwz63Beta` is therefore not a split parameter and does not appear below.**  It is the free
rationalisation parameter of the `(1,2,1)`/`(2,1,1)` *value* bound --- its own docstring in
`Examples/DuanWuZhouLevelTwoGlobalArithmetic.lean` derives it from the `lem:non-rot-values` (d)
formula `(4 / ((1-2β)^{1-2β} β^{2β}))^{1/3} q^{(2-2β)τ}`, which is a value, not a distribution
over `CWBlock`.  Putting `β` into a split row would be a category error.

## Why the common mass is `2 * 10 ^ 8`

`a` and `b` have denominator `10 ^ 8`; the symmetric rows have denominator `2`.  The least common
denominator is `2 * 10 ^ 8`, so every row below is an integral profile of that one mass and no row
needs rescaling relative to another.  A client at `dwz63Alpha`-scale `s` uses
`α̃_t(d) * dwz63Alpha t * s / (2 * 10 ^ 8)` counts in segment `t`, which is integral once
`2 * 10 ^ 8` divides `dwz63Alpha t * s` --- one further factor of `2 * 10 ^ 8` beyond the
`10 ^ 8` that `dwz63CofinalIndex` already carries.

## One fine letter is a pair

`cwSquarePartitionedTensor = ((cwPartitionedTensor K q).positivePower 1).coarsen cwSquareDegreeMap`
(`Examples/CoppersmithWinogradSquare.lean:204-207`), so the fine block alphabet is
`PositiveWord CWBlock 1` --- an ordered pair `(k_l, k_r)` of base degrees, which is DWZ's
`(K̂_{2s-1}, K̂_{2s})` at `hole_lemma.tex:40`.  A coarse word of `n + 1` letters therefore has
`n + 1` fine letters, not `2n + 2`, and there are fifteen segments, one per cell.

Each row below is the distribution over those pairs: the paper's `α̃_{i,j,k}(k_l)` placed on the
pair `(k_l, k - k_l)`.  Every row is invariant under swapping the pair
(`dwz63AlphaTilde_swap`), which is the formal content of the reflection symmetry `k_l ↔ k_r`.

Primary source: Ran Duan, Hongxun Wu and Renfei Zhou, *Faster Matrix Multiplication via Asymmetric
Hashing*, arXiv:2210.10173, section 6.3 and `hole_lemma.tex`.
-/

set_option autoImplicit false

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor

/-! ## Profiles over the three level-one degrees, and over pairs of them -/

/-- A `CWBlock`-indexed profile, listed by degree `0, 1, 2`. -/
def cwProfile (p q r : ℕ) : CWBlock → ℕ
  | .zero => p
  | .middle => q
  | .last => r

/-- The identically zero row. -/
def cwZeroProfile : CWBlock → ℕ := cwProfile 0 0 0

theorem cwBlock_univ : (Finset.univ : Finset CWBlock) = {.zero, .middle, .last} := by decide

theorem profileMass_cwProfile (p q r : ℕ) :
    WordType.profileMass (cwProfile p q r) = p + q + r := by
  unfold WordType.profileMass
  rw [cwBlock_univ, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton]
  simp only [cwProfile]
  ring

/-- **A profile on one fine letter**, as a `3 x 3` table: `r_d` is the distribution of the right
digit given left digit `d`.  `PositiveWord CWBlock 1` is definitionally `CWBlock x CWBlock`, with
`.1` the left digit and `.2` the right. -/
def cwPairProfile (r0 r1 r2 : CWBlock → ℕ) : PositiveWord CWBlock 1 → ℕ :=
  fun p => cwProfile (r0 p.2) (r1 p.2) (r2 p.2) p.1

/-! ## The fifteen rows -/

/-- **The common mass of every row**, the least common denominator of `a`, `b` and `1/2`. -/
def dwz63AlphaTildeMass : ℕ := 200000000

/-- **The `Z`-marginal split distribution of each level-two component**, as an integral profile on
one fine letter `(k_l, k_r)` of mass `2 * 10 ^ 8`, in the cell order of `dwz63Alpha`:

`(0,0,4) (0,1,3) (0,2,2) (0,3,1) (0,4,0) (1,0,3) (1,1,2) (1,2,1) (1,3,0) (2,0,2) (2,1,1) (2,2,0)
(3,0,1) (3,1,0) (4,0,0)`.

Only indices `2`, `6` and `9` --- the components `(0,2,2)`, `(1,1,2)`, `(2,0,2)` --- are
parameterised, by `a = dwz63A` and `b = dwz63B`; every other row is the symmetric split of its own
`Z`-degree, supported on the pairs summing to that degree. -/
def dwz63AlphaTilde : Fin 15 → PositiveWord CWBlock 1 → ℕ :=
  ![cwPairProfile cwZeroProfile cwZeroProfile (cwProfile 0 0 200000000),
    cwPairProfile cwZeroProfile (cwProfile 0 0 100000000) (cwProfile 0 100000000 0),
    cwPairProfile (cwProfile 0 0 6954806) (cwProfile 0 186090388 0) (cwProfile 6954806 0 0),
    cwPairProfile (cwProfile 0 100000000 0) (cwProfile 100000000 0 0) cwZeroProfile,
    cwPairProfile (cwProfile 200000000 0 0) cwZeroProfile cwZeroProfile,
    cwPairProfile cwZeroProfile (cwProfile 0 0 100000000) (cwProfile 0 100000000 0),
    cwPairProfile (cwProfile 0 0 42030) (cwProfile 0 199915940 0) (cwProfile 42030 0 0),
    cwPairProfile (cwProfile 0 100000000 0) (cwProfile 100000000 0 0) cwZeroProfile,
    cwPairProfile (cwProfile 200000000 0 0) cwZeroProfile cwZeroProfile,
    cwPairProfile (cwProfile 0 0 6954806) (cwProfile 0 186090388 0) (cwProfile 6954806 0 0),
    cwPairProfile (cwProfile 0 100000000 0) (cwProfile 100000000 0 0) cwZeroProfile,
    cwPairProfile (cwProfile 200000000 0 0) cwZeroProfile cwZeroProfile,
    cwPairProfile (cwProfile 0 100000000 0) (cwProfile 100000000 0 0) cwZeroProfile,
    cwPairProfile (cwProfile 200000000 0 0) cwZeroProfile cwZeroProfile,
    cwPairProfile (cwProfile 200000000 0 0) cwZeroProfile cwZeroProfile]

/-- **Every row is a distribution of the common mass**, stated as the explicit sum over the nine
pairs.  This avoids `Finset.univ` on `PositiveWord CWBlock 1`, whose `Fintype` instance is the
`positiveWordFintype` one rather than the product instance; the tensor lane owns that type and can
restate this through `WordType.profileMass` on its own side. -/
theorem dwz63AlphaTilde_sum (t : Fin 15) :
    dwz63AlphaTilde t (.zero, .zero) + dwz63AlphaTilde t (.zero, .middle)
        + dwz63AlphaTilde t (.zero, .last)
      + (dwz63AlphaTilde t (.middle, .zero) + dwz63AlphaTilde t (.middle, .middle)
        + dwz63AlphaTilde t (.middle, .last))
      + (dwz63AlphaTilde t (.last, .zero) + dwz63AlphaTilde t (.last, .middle)
        + dwz63AlphaTilde t (.last, .last)) = dwz63AlphaTildeMass := by
  fin_cases t <;> rfl

/-! ## The two parameterised rows, tied to `dwz63A` and `dwz63B` -/

/-- `2 * a` and `2 * (1 - 2a)` over the denominator `10 ^ 8`, as the `(0,2,2)` and `(2,0,2)` rows
state them. -/
theorem dwz63AlphaTilde_a_entries :
    6954806 = 2 * 3477403 ∧ 186090388 = 2 * (100000000 - 2 * 3477403) :=
  ⟨by norm_num, by norm_num⟩

/-- `2 * b` and `2 * (1 - 2b)` over the denominator `10 ^ 8`, as the `(1,1,2)` row states them. -/
theorem dwz63AlphaTilde_b_entries :
    42030 = 2 * 21015 ∧ 199915940 = 2 * (100000000 - 2 * 21015) :=
  ⟨by norm_num, by norm_num⟩

/-- The `(0,2,2)` and `(2,0,2)` rows are the same profile. -/
theorem dwz63AlphaTilde_two_eq_nine : dwz63AlphaTilde 2 = dwz63AlphaTilde 9 := rfl

/-! ## Reflection symmetry -/

/-- **Every row is invariant under swapping the two digits of a fine letter.**  This is the
formal content of `k_l ↔ k_r`, and it is why no separate right-digit table is needed. -/
theorem dwz63AlphaTilde_swap (t : Fin 15) (l r : CWBlock) :
    dwz63AlphaTilde t (r, l) = dwz63AlphaTilde t (l, r) := by
  fin_cases t <;> cases l <;> cases r <;> rfl

end AlgebraicComplexity.Examples
