/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoFineCellLiveLegs
import AlgebraicComplexity.Combinatorics.WordTypeStatistics

set_option autoImplicit false

/-!
# `dwz63CellOnes` is a statistic of the word's type

Layer 4 (`AlgebraicComplexity/Examples/`).  The last structural step towards `huniform` for the
`(0,2,2)`-type cells is that the exponent `dwz63CellOnes` --- a sum over the positions of a cell
word --- depends only on the word's **empirical type**, and not on the order of its letters.

That is exactly `WordType.sum_word_eq_sum_multiplicity_mul` and
`WordType.sum_word_eq_of_multiplicity_eq` (`Combinatorics/WordTypeStatistics.lean`), the additive
counterparts of `WordType.prod_word_eq_prod_pow` that the multiplicative value law
`positiveSupportWordWeight_eq_prod_pow` uses.  `dwz63CellOnes` is literally
`∑ position, cwWordMiddleCount 1 (word position)`, so both apply on the nose with the statistic
taken to be the fine letter's middle count.

Note that the alphabet `PositiveWord CWBlock 1` carries the **noncomputable** `positiveWordFintype`
instance.  That is harmless here --- these are propositions, and `Finset.univ` over the alphabet
occurs only inside their statements and proofs --- but it is why the same regrouping must never be
attempted by `decide`.

Primary source: Ran Duan, Hongxun Wu and Renfei Zhou, *Faster Matrix Multiplication via Asymmetric
Hashing*, arXiv:2210.10173, `global_value.tex` section 6.3.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor MoreAsymmetryCompatibility
open scoped BigOperators

/-- **The cell exponent, regrouped by empirical type.**  The multiplicity-weighted total of the
per-letter middle count. -/
theorem dwz63_cellOnes_eq_sum_multiplicity (zero : Leg) (m : ℕ)
    (S : BlockAddress (fun _ : Leg ↦ PositiveWord (PositiveWord CWBlock 1) m)) :
    dwz63CellOnes zero m S =
      ∑ p : PositiveWord CWBlock 1,
        WordType.multiplicity
            (positiveWordEquiv (PositiveWord CWBlock 1) m (S (firstLiveLeg zero))) p *
          cwWordMiddleCount 1 p :=
  WordType.sum_word_eq_sum_multiplicity_mul (cwWordMiddleCount 1)
    (positiveWordEquiv (PositiveWord CWBlock 1) m (S (firstLiveLeg zero)))

/-- **`huniform`'s engine.**  Two cell words whose first-live-leg words have the same empirical
type have the same exponent, hence the same one-slice dimension `q ^ ones`. -/
theorem dwz63_cellOnes_eq_of_multiplicity_eq (zero : Leg) (m : ℕ)
    (S S' : BlockAddress (fun _ : Leg ↦ PositiveWord (PositiveWord CWBlock 1) m))
    (h : WordType.multiplicity
          (positiveWordEquiv (PositiveWord CWBlock 1) m (S (firstLiveLeg zero))) =
        WordType.multiplicity
          (positiveWordEquiv (PositiveWord CWBlock 1) m (S' (firstLiveLeg zero)))) :
    dwz63CellOnes zero m S = dwz63CellOnes zero m S' :=
  WordType.sum_word_eq_of_multiplicity_eq (cwWordMiddleCount 1) h

end AlgebraicComplexity.Examples
