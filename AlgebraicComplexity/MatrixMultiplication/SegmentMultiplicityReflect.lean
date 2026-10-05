/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.SegmentedSplitRestriction

set_option autoImplicit false

/-!
# Reflecting a segment distribution along an involution of the alphabet

Layer 3 (`AlgebraicComplexity/MatrixMultiplication/`).  One counting step, isolated because it is
generic: if two words agree on a segment up to an involution `f` of the letter alphabet, their
segment distributions there agree up to `f`.

This is the arithmetic of `[duan2023faster]`'s `global_value.tex:70`, the displayed chain

`split(K̂, S_{i,0,k})(k') = split(Î, S_{i,0,k})(2^{ℓ-1} - k')`,

whose input is the letterwise identity `Î_s = 2^{ℓ-1} - K̂_s` holding on the positions of the
segment.  Nothing about `[duan2023faster]`'s alphabet or split tables enters here.

Primary source `[duan2023faster]`: Ran Duan, Hongxun Wu and Renfei Zhou, *Faster Matrix
Multiplication via Asymmetric Hashing*, arXiv:2210.10173, section 6.1 `sec:global-algo`,
`global_value.tex:70`.
-/

namespace AlgebraicComplexity

open scoped BigOperators

universe w

variable {I : Type w} [Fintype I] [DecidableEq I] {n m : ℕ}

omit [Fintype I] in
/-- **A segment distribution reflects along an involution.**

If `w i = f (v i)` at every position of segment `t`, then the segment-`t` distribution of `w` is
that of `v` composed with `f`.  `[duan2023faster]`'s `global_value.tex:70` is this at
`f = (2^{ℓ-1} - ·)`. -/
theorem segmentMultiplicity_comp_involutive (seg : Fin n → Fin m) (w v : Fin n → I) (t : Fin m)
    (f : I → I) (hf : Function.Involutive f) (h : ∀ i, seg i = t → w i = f (v i)) :
    segmentMultiplicity seg w t = fun a ↦ segmentMultiplicity seg v t (f a) := by
  classical
  funext a
  unfold segmentMultiplicity
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hseg, hwi⟩
    refine ⟨hseg, ?_⟩
    have hvi : f (v i) = a := by rw [← h i hseg]; exact hwi
    have := congrArg f hvi
    rwa [hf (v i)] at this
  · rintro ⟨hseg, hvi⟩
    refine ⟨hseg, ?_⟩
    rw [h i hseg, hvi, hf a]

end AlgebraicComplexity
