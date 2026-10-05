/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoOrientationTypical
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoOrbitCounting
import AlgebraicComplexity.Examples.CoppersmithWinogradSquareSymmetry

/-!
# The `alpha` profile at the exceptional coarse addresses

Layer 4 (a client).  Five small identities evaluating `dwz63AlphaAddress` — the pushforward of the
fifteen-cell profile onto coarse `CWSquareAddress`es — at the three addresses of the exceptional
orbit.

They were extracted verbatim from `Examples/DuanWuZhouLevelTwoOrbitAssemblyValue.lean` so that the
live plain-partition value client can use them **without importing the six-orientation value
chain**: `OrbitAssemblyValue` pulls in `OrbitAssembly`, `TargetWordCount` and
`IntegrationMarkedFamily`, none of which these five lemmas need, and only these four
(`dwz63AlphaAddress_112`, `_121`, `_211`, `_cellAddress`) were ever used downstream.

Primary source: Ran Duan, Hongxun Wu and Renfei Zhou, *Faster Matrix Multiplication via Asymmetric
Hashing*, arXiv:2210.10173, `global_value.tex` section 6.3.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor
open scoped BigOperators

set_option autoImplicit false

/-! ## The profile at a coarse address -/

/-- `dwz63AlphaAddress` as an indicator sum over the fifteen cells. -/
theorem dwz63AlphaAddress_apply (a : CWSquareAddress) :
    dwz63AlphaAddress a = ∑ i : Fin 15, if dwz63CellAddress i = a then dwz63Alpha i else 0 := by
  classical
  unfold dwz63AlphaAddress
  exact WordType.mappedType_eq_sum_ite _ _ _

/-- The profile at a cell of the fifteen-cell table is that cell's `dwz63Alpha` entry. -/
theorem dwz63AlphaAddress_cellAddress (i : Fin 15)
    (hinj : ∀ j : Fin 15, j ≠ i → dwz63CellAddress j ≠ dwz63CellAddress i) :
    dwz63AlphaAddress (dwz63CellAddress i) = dwz63Alpha i := by
  classical
  rw [dwz63AlphaAddress_apply, Finset.sum_eq_single i]
  · rw [if_pos rfl]
  · intro j _ hj
    rw [if_neg (hinj j hj)]
  · intro h
    exact absurd (Finset.mem_univ i) h

theorem dwz63AlphaAddress_112 : dwz63AlphaAddress cwSquare112 = dwz63Alpha112 := by
  have h : cwSquare112 = dwz63CellAddress 6 := by decide
  rw [h, dwz63AlphaAddress_cellAddress 6 (by decide)]
  exact dwz63Alpha_six

theorem dwz63AlphaAddress_121 : dwz63AlphaAddress cwSquare121 = dwz63Alpha121 := by
  have h : cwSquare121 = dwz63CellAddress 7 := by decide
  rw [h, dwz63AlphaAddress_cellAddress 7 (by decide)]
  exact dwz63Alpha_seven

theorem dwz63AlphaAddress_211 : dwz63AlphaAddress cwSquare211 = dwz63Alpha121 := by
  have h : cwSquare211 = dwz63CellAddress 10 := by decide
  rw [h, dwz63AlphaAddress_cellAddress 10 (by decide)]
  exact dwz63Alpha_ten

end AlgebraicComplexity.Examples
