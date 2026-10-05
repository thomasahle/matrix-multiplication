/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoLeafTauWeight

set_option autoImplicit false

/-!
# The `(1,1,2)` split parameter of the leaf chain **is** the paper's `b`

Layer 4 (`AlgebraicComplexity/Examples/`).  `[duan2023faster]` section 6.3 splits the `(1,1,2)`
component at `b = 21015 / 10 ^ 8` (`dwz63B`).  The committed Coppersmith--Winograd `(1,1,2)` chain
carries its own split parameter, `cw112Mu L G = L / (2 (L + G))`
(`Examples/CoppersmithWinograd112TypedLeaf.lean`), and the level-two lane instantiates it at
`L = dwz112L = 4203`, `G = dwz112G = 9995797`.

That the two are the *same number* is what makes the chain a proof about the paper's component and
not about a neighbouring one.  Until now it was nowhere stated: the coupling lived only inside the
`ring` call of `dwz63LogVal112_eq_dwz112LogValue`
(`Examples/DuanWuZhouLevelTwoSixOrientationValues.lean`), which rewrites `dwz112LogValue`'s
already-cleared numerals against `dwz63B` and never mentions `cw112Mu` at all.  So the chain's
*entropy* input --- `cw112MuEntropyBits dwz112L dwz112G`, the only place `cw112Mu` enters the leaf
value --- was never visibly tied to `b`.

`dwz63_cw112Mu_eq_dwz63B` is that tie, as one named equation.  It is a numeral identity
(`4203 / (2 * 10 ^ 7) = 21015 / 10 ^ 8`) and the committed `dwz112Stride_eq` already supplies the
denominator, so nothing is recomputed.

## Proposed repoint (not applied)

`dwz63LogVal112_eq_dwz112LogValue` should read this lemma rather than expand `dwz63B` inline; that
file belongs to another lane and is at its accepted image, so the change is proposed here rather
than made.

Primary source: Ran Duan, Hongxun Wu and Renfei Zhou, *Faster Matrix Multiplication via Asymmetric
Hashing*, arXiv:2210.10173, `global_value.tex` section 6.3 and `second_power.tex`.

Exact source lines: `papers/sources/2210.10173/global_value.tex:332-378` (§6.3),
`papers/sources/2210.10173/second_power.tex:1-637` (whole file).
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity

/-- **The `(1,1,2)` chain's split parameter is the section 6.3 constant `b`.**

`cw112Mu dwz112L dwz112G = 4203 / (2 * 10 ^ 7) = 21015 / 10 ^ 8 = dwz63B`.  The stride is the
committed `dwz112Stride_eq`, so the only arithmetic left is the numeral. -/
theorem dwz63_cw112Mu_eq_dwz63B : cw112Mu dwz112L dwz112G = dwz63B := by
  rw [cw112Mu, dwz112Stride_eq, dwz63B, dwz112L]
  norm_num

/-- **The complementary weight of the split is `1 - 2 b`.**  The immediate corollary, recorded
because the chain's entropy `cw112MuEntropyBits` reads exactly this expression, and the paper's
`(1,1,2)` value formula `(4 / ((1-2b)^(1-2b) b^(2b)))^(1/3) q^((2-2b) tau)` reads the same one. -/
theorem dwz63_one_sub_two_cw112Mu_eq : 1 - 2 * cw112Mu dwz112L dwz112G = 1 - 2 * dwz63B := by
  rw [dwz63_cw112Mu_eq_dwz63B]

end AlgebraicComplexity.Examples
