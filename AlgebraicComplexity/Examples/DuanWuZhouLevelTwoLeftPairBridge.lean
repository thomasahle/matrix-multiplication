/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoSplitAlphabetBridge
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoFineComplementaryLetter
import AlgebraicComplexity.MatrixMultiplication.SegmentedSplitRestriction

set_option autoImplicit false

/-!
# `split` is the left digit, and on a fixed level-two index it determines the pair

Layer 4 (`AlgebraicComplexity/Examples/`).  `[duan2023faster]`, section 6.1 `sec:global-algo`,
`papers/sources/2210.10173/global_value.tex:35`:

> For a fixed small block `Z_K̂ ∈ Z_K` and a set `S ⊆ S_{*,*,k}` for some `k`, we will use
> `split_k(K̂, S)` to denote the distribution of `K̂_{2t-1}` over all `t ∈ S`.  **(Note that for
> those `t ∈ S`, we always have `K̂_{2t} = k - K̂_{2t-1}`.  Hence such distribution captures how
> those `k`'s split into `K̂_{2t-1} + K̂_{2t}`.)**  (`:35`)

The paper's `split` is therefore the distribution of the **left** level-one digit, and the
parenthetical is the paper's own statement of why nothing is lost: `split` is only ever applied to
a set `S ⊆ S_{*,*,k}`, on which the level-two index is the constant `k`, and there the right digit
is `k` minus the left.  Both uses obey that restriction --- `item:split-match` (`:47`) takes
`S = S_{*,*,k}`, and `item:average` (`:48`) takes `S = S_{i,j,k} ⊆ S_{*,*,k}`.

This module proves that sentence at level two, in the form the hole side needs: on the fibre
`cwSquareBlockDegree p = k` the left digit determines the pair, so a profile supported there is
determined by its left-digit pushforward.  Consequently the tree's pair-valued Step-1 rules
(`Examples/DuanWuZhouLevelTwoStepOneKeep.lean`) and the paper's left-digit rules (`:54`, `:57`,
`:60`) cut the same tensor, and the pair-valued compatibility conclusion
(`Examples/DuanWuZhouLevelTwoStepOneCompatibleCut.lean`) is the paper's `def:global-compatible`
(`:44-50`).

The forward direction --- pair counts determine left-digit counts --- is image 123's
`dwz63_splitPair_letterPushforward`
(`Examples/DuanWuZhouLevelTwoSplitAlphabetBridge.lean:140`).  What is added here is the reverse,
which is what `:35`'s parenthetical asserts.

## The argument, and why it needs no enumeration

At level two `2^{ℓ-1} = 2`, a small letter is a pair of `CWBlock`s, and
`cwSquareBlockDegree (a, b) = cwBlockDegree a + cwBlockDegree b`.  Fixing that sum to `k` and the
left degree to `l` fixes `cwBlockDegree a = l` and `cwBlockDegree b = k - l`, and
`cwBlockDegree_injective` (image 137) turns each degree back into its letter.  So the left-digit
fibre meets the degree-`k` fibre in at most one letter, and a pushforward sum over it has at most
one nonzero term.  Only `CWBlock` is enumerated (81 cases); `PositiveWord CWBlock 1` never is.

Primary source `[duan2023faster]`: Ran Duan, Hongxun Wu and Renfei Zhou, *Faster Matrix
Multiplication via Asymmetric Hashing*, arXiv:2210.10173, section 6.1 `sec:global-algo`,
`papers/sources/2210.10173/global_value.tex:35, 44-50, 52-61`.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor WordType
open scoped BigOperators

/-! ## The left digit determines the pair on a fixed level-two index (`global_value.tex:35`) -/

/-- **`K̂_{2t} = k - K̂_{2t-1}`** (`global_value.tex:35`), as injectivity.

Two small letters of the same level-two degree with the same left digit are equal: the left degree
fixes the left letter and the total fixes the right one.

Proof sketch: destructure both pairs and decide the resulting statement over `CWBlock`, which has
three elements; the trap recorded on the board --- `decide` failing on an equality in
`PositiveWord CWBlock 1` stated inside the proposition --- is avoided exactly by destructuring
first. -/
theorem dwz63_finePair_of_leftDegree_of_degree {k : Fin 5} {p q : PositiveWord CWBlock 1}
    (hp : cwSquareBlockDegree p = k) (hq : cwSquareBlockDegree q = k)
    (h : dwz63FineLeftDegree p = dwz63FineLeftDegree q) : p = q := by
  obtain ⟨p₁, p₂⟩ := p
  obtain ⟨q₁, q₂⟩ := q
  have key : ∀ a b c d : CWBlock,
      cwSquareBlockDegree ((a, b) : PositiveWord CWBlock 1) =
          cwSquareBlockDegree ((c, d) : PositiveWord CWBlock 1) →
        dwz63FineLeftDegree ((a, b) : PositiveWord CWBlock 1) =
          dwz63FineLeftDegree ((c, d) : PositiveWord CWBlock 1) →
        a = c ∧ b = d := by decide
  obtain ⟨h₁, h₂⟩ := key p₁ p₂ q₁ q₂ (hp.trans hq.symm) h
  rw [h₁, h₂]

/-- **A degree-supported profile is determined by its left-digit pushforward.**

`global_value.tex:35`: on `S ⊆ S_{*,*,k}` the left-digit distribution "captures how those `k`'s
split".  Here that is: two profiles supported on the level-two degree `k` with equal left-digit
pushforwards are equal.

Proof sketch: at a letter `p` of degree `k`, the left-digit fibre of `dwz63FineLeftDegree p` carries
at most one letter of degree `k` (the previous lemma), so each pushforward sum collapses to its
value at `p` by `Finset.sum_eq_single`. -/
theorem dwz63_profile_of_leftDegree_pushforward {k : Fin 5}
    {f g : PositiveWord CWBlock 1 → ℕ}
    (hf : ∀ p, f p ≠ 0 → cwSquareBlockDegree p = k)
    (hg : ∀ p, g p ≠ 0 → cwSquareBlockDegree p = k)
    (h : WordType.mappedType dwz63FineLeftDegree f =
      WordType.mappedType dwz63FineLeftDegree g) :
    f = g := by
  classical
  have hsum : ∀ (u : PositiveWord CWBlock 1 → ℕ),
      (∀ q, u q ≠ 0 → cwSquareBlockDegree q = k) →
      ∀ p, cwSquareBlockDegree p = k →
        WordType.mappedType dwz63FineLeftDegree u (dwz63FineLeftDegree p) = u p := by
    intro u hu p hp
    show ∑ x ∈ WordType.letterFiber dwz63FineLeftDegree (dwz63FineLeftDegree p), u x = u p
    refine Finset.sum_eq_single p ?_ ?_
    · intro q hq hqp
      by_contra hne
      exact hqp (dwz63_finePair_of_leftDegree_of_degree (hu q hne) hp
        (WordType.mem_letterFiber.mp hq))
    · intro hnp
      exact absurd (WordType.mem_letterFiber.mpr rfl) hnp
  funext p
  rcases eq_or_ne (f p) 0 with h1 | h1
  · rcases eq_or_ne (g p) 0 with h2 | h2
    · rw [h1, h2]
    · have hp := hg p h2
      rw [← hsum f hf p hp, ← hsum g hg p hp, h]
  · have hp := hf p h1
    rw [← hsum f hf p hp, ← hsum g hg p hp, h]

/-! ## The two readings of a Step-1 rule agree (`global_value.tex:35, 54, 57, 60`) -/

section Segment

variable {N : ℕ}

/-- **A pair-valued split rule and the paper's left-digit split rule are the same condition**, on a
segment whose letters all carry the level-two index `k` and against a target supported there.

This is `global_value.tex:35` in the form the Step-1 rules (`:54`, `:57`, `:60`) are stated in: the
left-hand side is the tree's pair-valued equality and the right-hand side is the paper's
`split(·, S) = ·`, with `split` the left-digit distribution.  Both support hypotheses are
available
where the tree uses the rules --- the observed one because the level-two index word of a supported
address *is* its degree word, the target one from `dwz63_alphaTilde_zDegree`.

Proof sketch: forward is `congrArg`; backward is
`dwz63_profile_of_leftDegree_pushforward`, whose support hypothesis for the observed profile comes
from a nonzero count exhibiting a position of the segment. -/
theorem dwz63_segmentMultiplicity_eq_iff_leftDegree {k : Fin 5} {m : ℕ}
    (seg : Fin N → Fin m) (w : Fin N → PositiveWord CWBlock 1) (t : Fin m)
    (α : PositiveWord CWBlock 1 → ℕ)
    (hw : ∀ i, seg i = t → cwSquareBlockDegree (w i) = k)
    (hα : ∀ p, α p ≠ 0 → cwSquareBlockDegree p = k) :
    segmentMultiplicity seg w t = α ↔
      WordType.mappedType dwz63FineLeftDegree (segmentMultiplicity seg w t) =
        WordType.mappedType dwz63FineLeftDegree α := by
  classical
  constructor
  · intro hEq
    rw [hEq]
  · intro hEq
    refine dwz63_profile_of_leftDegree_pushforward ?_ hα hEq
    intro p hp
    have hcard : (Finset.univ.filter fun i ↦ seg i = t ∧ w i = p).Nonempty := by
      rw [← Finset.card_pos]
      exact Nat.pos_of_ne_zero hp
    obtain ⟨i, hi⟩ := hcard
    obtain ⟨hseg, hwi⟩ := (Finset.mem_filter.mp hi).2
    rw [← hwi]
    exact hw i hseg

end Segment

end AlgebraicComplexity.Examples
