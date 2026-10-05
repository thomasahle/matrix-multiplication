/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoFineConfiguration

/-!
# A satisfying fine configuration for the Duan--Wu--Zhou level-two split

`Examples/DuanWuZhouLevelTwoFineConfiguration.lean` exposes `Dwz63FineConfiguration` --- forty-five
exact natural-number equalities on a thirty-six-entry table --- as a *data boundary*, and says so:
"It intentionally does not select a satisfying table."  Every client of that boundary, including
the committed `dwz63FineMarkedXYFixedTargetCleanup_to_indexedDirectSum`, therefore carries an
undischarged premise.  This module selects a table and discharges it.

## Why a witness exists at all, and why it is essentially unique

`[DuanWuZhou2022]` section 6.3 fixes the `Z` split of each of the fifteen coarse square
constituents but records no division of the multiplicity inside a coarse `Z`-word fibre among the
thirty-six ordered pairs of base Coppersmith--Winograd addresses.  The constraint each pair must
meet is indexed by the pair `(component, left Z digit)` it realizes.  The key structural fact is
that **each fine letter realizes exactly one such pair**, so the forty-five equations do not
interact: they are forty-five independent one-dimensional problems, and a witness exists if and
only if every group carrying a nonzero target is nonempty.

Enumerating the thirty-six letters against `dwz63SplitCount` settles that affirmatively, and more
sharply than feasibility alone requires:

* twenty-seven of the forty-five `(component, left digit)` groups are realized by some letter;
* every realized group carries a **nonzero** target, and every unrealized group carries a **zero**
  target --- so the realized groups match the nonzero table entries exactly, with no slack in
  either direction;
* every target is divisible by the size of its group, so the *even* split is integral.

`dwz63FineCountTable` is that even split.  Nothing in the construction imposes symmetry, yet the
resulting table satisfies `M i j = M j i` at all thirty-six entries --- the independent check that
it is the intended datum, since the committed `dwz63SplitCount` is itself symmetric under
exchanging the two Coppersmith--Winograd factors.

## The one bridge the proof needs

`dwz63FineComponent` is defined through `dwz63CellEquiv.symm`, and `dwz63CellEquiv` is an
`Equiv.ofBijective`, whose inverse is classical: no kernel reduction can evaluate it.
`dwz63FineComponent_eq_dwz63CellIndex` replaces it by the committed *computable* left inverse
`dwz63CellIndex`, which is what makes the forty-five equations decidable by reflection.  The
replacement is justified by `dwz63Cell_dwz63CellIndex`, the right-inverse property of
`dwz63CellIndex` on the fifteen supported addresses.

## Position in the library

Layer 4 (a client).  It imports the fine-configuration data boundary and nothing else, defines no
tensor, and assumes nothing: `dwz63FineConfiguration_dwz63FineCountWitness` is unconditional.

Primary source: Ran Duan, Hongxun Wu and Renfei Zhou, *Faster Matrix Multiplication via
Asymmetric Hashing*, arXiv:2210.10173, section 6.3.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor MoreAsymmetryCompatibility

/-! ## Indexing the six base Coppersmith--Winograd addresses -/

/-- **A computable code for a base CW address.**  A supported base address is determined by its
`X` and `Y` degrees, so `3 x + y` separates the six of them: `cw002, cw011, cw020, cw101, cw110,
cw200` receive `0, 1, 2, 3, 4, 6`.  The truncation keeps the function total; its value off the
six used codes is irrelevant. -/
def dwz63BaseCode (address : cwBlockSupport) : Fin 9 :=
  ⟨min 8 (3 * cwBlockDegree (address.1 .X) + cwBlockDegree (address.1 .Y)), by omega⟩

/-- **Position of a base CW address among the six**, in the listing order
`cw200, cw020, cw002, cw011, cw101, cw110` of `cwBlockSupport`. -/
def dwz63BaseIndex (address : cwBlockSupport) : Fin 6 :=
  ![2, 3, 1, 4, 5, 0, 0, 0, 0] (dwz63BaseCode address)

/-! ## The witness table -/

/-- **The even split of `dwz63SplitCount` over the fine letters realizing each requirement.**

Rows and columns are indexed by `dwz63BaseIndex`, in the order
`cw200, cw020, cw002, cw011, cw101, cw110`.  Entry `(i, j)` is the target of the
`(component, left Z digit)` group realized by the ordered pair `(i, j)`, divided by the number of
ordered pairs realizing that same group.

The table is symmetric; see `dwz63FineCountTable_symm`. -/
def dwz63FineCountTable : Fin 6 → Fin 6 → ℕ :=
  ![![4946200000000, 669719400000000, 72100091287670,
      1036722900000000, 133331800000000, 125175800000000],
    ![669719400000000, 4946200000000, 72100091287670,
      133331800000000, 1036722900000000, 125175800000000],
    ![72100091287670, 72100091287670, 4172000000000,
      121115300000000, 121115300000000, 844324824690],
    ![1036722900000000, 133331800000000, 121115300000000,
      1929188817424660, 2008017975175310, 1036722900000000],
    ![133331800000000, 1036722900000000, 121115300000000,
      2008017975175310, 1929188817424660, 1036722900000000],
    ![125175800000000, 125175800000000, 844324824690,
      1036722900000000, 1036722900000000, 669719400000000]]

/-- **The fine configuration selected by this module.** -/
def dwz63FineCountWitness (letter : CWDepthOneFineLetter) : ℕ :=
  dwz63FineCountTable (dwz63BaseIndex letter.1) (dwz63BaseIndex letter.2)

/-- The witness table is symmetric under exchanging the two Coppersmith--Winograd factors.  This
is not imposed by the construction: it is inherited from the symmetry of `dwz63SplitCount`, and is
the independent check that the even split is the intended section 6.3 datum. -/
theorem dwz63FineCountTable_symm (i j : Fin 6) :
    dwz63FineCountTable i j = dwz63FineCountTable j i := by
  fin_cases i <;> fin_cases j <;> decide

/-- Every fine letter receives a positive count: the witness is genuinely a splitting of the
committed table and not a degenerate one supported on a few letters. -/
theorem dwz63FineCountWitness_pos (letter : CWDepthOneFineLetter) :
    0 < dwz63FineCountWitness letter := by
  revert letter
  decide

/-! ## Replacing the classical inverse by the committed computable one -/

/-- **`dwz63CellIndex` is a right inverse on the supported addresses.**  The committed
`dwz63CellIndex_dwz63Cell` is the left-inverse direction; this is the other one, and it is what
lets a classical `Equiv.symm` be replaced by a reducible lookup. -/
theorem dwz63Cell_dwz63CellIndex {s : CWSquareAddress} (hs : s ∈ cwSquareSupport) :
    dwz63Cell (dwz63CellIndex s) = s := by
  rw [cwSquareSupport_eq_antidiagonal] at hs
  fin_cases hs <;> decide

/-- **The component of a fine letter, computably.**  `dwz63FineComponent` goes through
`dwz63CellEquiv.symm`, which is an `Equiv.ofBijective` inverse and therefore classical; this
identifies it with the committed lookup `dwz63CellIndex`. -/
theorem dwz63FineComponent_eq_dwz63CellIndex (letter : CWDepthOneFineLetter) :
    dwz63FineComponent letter = dwz63CellIndex (cwDepthOneCoarseShape letter) := by
  unfold dwz63FineComponent
  rw [Equiv.symm_apply_eq]
  apply Subtype.ext
  rw [dwz63CellEquiv_coe]
  exact (dwz63Cell_dwz63CellIndex (cwDepthOneCoarseShape_mem_cwSquareSupport letter)).symm

/-- The counting functional, with the classical component map eliminated. -/
theorem dwz63FineZLeftCount_eq_cellIndex (fineCount : CWDepthOneFineLetter → ℕ)
    (component : Fin 15) (left : Fin 3) :
    dwz63FineZLeftCount fineCount component left =
      ∑ letter, if dwz63CellIndex (cwDepthOneCoarseShape letter) = component ∧
          dwz63FineSplit .Z letter 0 = left then fineCount letter else 0 := by
  unfold dwz63FineZLeftCount
  simp only [dwz63FineComponent_eq_dwz63CellIndex]

/-! ## The forty-five equations -/

/-- **The section 6.3 fine-configuration premise is satisfiable, and this table satisfies it.**

All forty-five equations hold by reflection over the thirty-six fine letters, once
`dwz63FineComponent_eq_dwz63CellIndex` has removed the one classical step.  Consequently every
client of `Dwz63FineConfiguration` --- in particular
`dwz63FineMarkedXYFixedTargetCleanup_to_indexedDirectSum` --- can now be instantiated
unconditionally. -/
theorem dwz63FineConfiguration_dwz63FineCountWitness :
    Dwz63FineConfiguration dwz63FineCountWitness := by
  intro component left
  rw [dwz63FineZLeftCount_eq_cellIndex]
  fin_cases component <;> fin_cases left <;> decide

/-- **The premise is not vacuous**: a satisfying fine configuration exists. -/
theorem exists_dwz63FineConfiguration :
    ∃ fineCount : CWDepthOneFineLetter → ℕ, Dwz63FineConfiguration fineCount :=
  ⟨dwz63FineCountWitness, dwz63FineConfiguration_dwz63FineCountWitness⟩

end AlgebraicComplexity.Examples
