/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoAlphaTilde
import AlgebraicComplexity.Combinatorics.TypeClassCounting

set_option autoImplicit false

/-!
# Sums over the fine-letter alphabet, and the mass of every `alphatilde` row

Layer 4 (`AlgebraicComplexity/Examples/`).  `WordType.profileMass` and
`WordType.profileEntropyNats` are sums over `Finset.univ`, and on the fine-letter alphabet
`PositiveWord CWBlock 1` the `Fintype` instance Lean finds is the noncomputable
`positiveWordFintype`.  `decide` is therefore unavailable, which is exactly why
`dwz63AlphaTilde_sum` (`Examples/DuanWuZhouLevelTwoAlphaTilde.lean`) is stated as an explicit
nine-term sum and its own docstring defers the `profileMass` reading to another lane.

This module supplies that reading, once, for an arbitrary `AddCommMonoid` --- so the same two
lemmas serve the natural-number mass and the real-valued entropy.

## The transport

`PositiveWord CWBlock 1` **is** `CWBlock × CWBlock`: `PositiveWord I (n+1) = PositiveWord I n × I`
and `PositiveWord I 0 = I` (`Tensor/PositiveWordDefs.lean`), a definitional equality that
`cwPairProfile`'s docstring already relies on.  No transporting equivalence is needed, and none
should be written: instance resolution unfolds the definition and finds the *product* `Fintype`
instance, so the two sums are literally the same term.  What is needed is only that the
expansion be *stated* over the pair alphabet: then `Fintype.sum_prod_type` matches, the committed
`cwBlock_univ` expands each factor, and a client holding a `PositiveWord CWBlock 1 → M` applies it
by definitional unfolding.  Two things that do **not** work, recorded because each costs a build:
an `Equiv.refl`-based `Fintype.sum_equiv` step is a no-op (the two sums are the same term), and a
`show` that retypes only the binder still leaves `f p` ill-typed at reducible transparency, so the
rewrite's motive fails.  There is no `decide` over a noncomputable instance anywhere.

`dwz63_profileMass_alphaTilde` then holds for **all fifteen** rows, not only the eleven with a
nonzero `Z` profile: `dwz63AlphaTilde_sum` is stated for every `t : Fin 15`, and the three corner
rows and the five degenerate ones all carry their whole mass on a single pair.

## What is reusable, and what is project-specific

`dwz63_sum_cwBlock` and `dwz63_sum_finePair_expand` are reusable expansion lemmas over an arbitrary
`AddCommMonoid`: they say a sum over `CWBlock` is its three terms and a sum over
`PositiveWord CWBlock 1` its nine.  `dwz63_profileMass_alphaTilde` and its positivity are
**project-specific**: they read the fifteen normalized level-two `α̃` rows of the section 6.3
example table, `papers/sources/2210.10173/global_value.tex:332-375`, and record that each row has
mass `2 · 10^8`.  Neither is a theorem the paper states; the table is.

Primary source `[duan2023faster]`: Ran Duan, Hongxun Wu and Renfei Zhou, *Faster Matrix
Multiplication via Asymmetric Hashing*, arXiv:2210.10173, section 6.3
`sec:level-2-global`, `papers/sources/2210.10173/global_value.tex:332-375`.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor
open scoped BigOperators

/-- A sum over one level-one block, expanded.  The committed `cwBlock_univ` is the whole content. -/
theorem dwz63_sum_cwBlock {M : Type*} [AddCommMonoid M] (g : CWBlock → M) :
    ∑ x : CWBlock, g x = g .zero + g .middle + g .last := by
  rw [cwBlock_univ, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton]
  abel

/-- **A sum over the fine-letter alphabet, as the nine-term table** --- the grouping
`dwz63AlphaTilde_sum` uses.  Stated over `CWBlock × CWBlock`, which is what
`PositiveWord CWBlock 1` unfolds to; a client with a fine-letter profile supplies it directly. -/
theorem dwz63_sum_finePair_expand {M : Type*} [AddCommMonoid M]
    (f : CWBlock × CWBlock → M) :
    ∑ p : CWBlock × CWBlock, f p =
      f (.zero, .zero) + f (.zero, .middle) + f (.zero, .last)
        + (f (.middle, .zero) + f (.middle, .middle) + f (.middle, .last))
        + (f (.last, .zero) + f (.last, .middle) + f (.last, .last)) := by
  rw [Fintype.sum_prod_type]
  simp only [dwz63_sum_cwBlock]

/-- **Every one of the fifteen `alphatilde` rows has mass `2 * 10 ^ 8`.**

This is the `profileMass` reading of the committed `dwz63AlphaTilde_sum`, and it is the hypothesis
`hmass` of `dwz63_exists_zeroXFineCellWeight`
(`Examples/DuanWuZhouLevelTwoFineCellEntropy.lean`). -/
theorem dwz63_profileMass_alphaTilde (t : Fin 15) :
    WordType.profileMass (dwz63AlphaTilde t) = 200000000 := by
  rw [WordType.profileMass]
  exact (dwz63_sum_finePair_expand (M := ℕ)
    (fun p ↦ dwz63AlphaTilde t p)).trans (dwz63AlphaTilde_sum t)

/-- The mass is positive, in the form the counting lemma takes. -/
theorem dwz63_profileMass_alphaTilde_pos (t : Fin 15) :
    0 < WordType.profileMass (dwz63AlphaTilde t) := by
  rw [dwz63_profileMass_alphaTilde]
  norm_num

end AlgebraicComplexity.Examples
