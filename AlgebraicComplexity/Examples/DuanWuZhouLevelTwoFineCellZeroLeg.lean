/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoFineCellSupport
import AlgebraicComplexity.Examples.CoppersmithWinogradSquare

set_option autoImplicit false

/-!
# The shared leg of a zero-coordinate cell is constant

Layer 4 (`AlgebraicComplexity/Examples/`).  The one-slice fusion's third support hypothesis is
`hz : ∀ address ∈ support, address (e.symm .Z) = zLabel`: the fibre carries **one** label on its
shared leg.  For `[DuanWuZhou2022]` section 6.3's localized leaf that hypothesis is not an extra
assumption --- it is forced by the coarsening half of `segmentedLocalizedKeep`.

A kept fine word lies over the fixed coarse target, so on a leg where the target's coarse word is
constantly the degree `0`, every fine letter has square-block degree zero.  A fine letter is a pair
of level-one blocks and its square degree is the *sum* of their degrees
(`cwSquareBlockDegree_val`), so degree zero forces both to be `CWBlock.zero`: the letter is the
constant zero pair, and the whole word is the constant word.

That is the content below, split into the tiny arithmetic fact about one pair, a generic word-level
lift, and their composite in the shape the fusion consumes.

Primary source: Ran Duan, Hongxun Wu and Renfei Zhou, *Faster Matrix Multiplication via Asymmetric
Hashing*, arXiv:2210.10173, `global_value.tex` section 6.3.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor

/-- **A fine letter of square degree zero is the constant zero pair.**  The square degree is the
sum of the two level-one degrees, and only `CWBlock.zero` has degree zero. -/
theorem cwSquareBlockDegree_eq_zero_iff (p : PositiveWord CWBlock 1) :
    cwSquareBlockDegree p = 0 ↔ p = positiveWordConst CWBlock.zero 1 := by
  obtain ⟨a, b⟩ := p
  constructor
  · intro h
    have hval : cwBlockDegree a + cwBlockDegree b = 0 := by
      simpa [cwSquareBlockDegree, Fin.ext_iff] using h
    have ha : a = CWBlock.zero := by cases a <;> first | rfl | simp_all [cwBlockDegree]
    have hb : b = CWBlock.zero := by cases b <;> first | rfl | simp_all [cwBlockDegree]
    rw [ha, hb]
    rfl
  · intro h
    have ha : a = CWBlock.zero := congrArg Prod.fst h
    have hb : b = CWBlock.zero := congrArg Prod.snd h
    rw [ha, hb]
    rfl

/-- **A letterwise-determined constant image forces a constant word.**  Generic: if `f` sends only
`a₀` to `c`, a word whose letterwise image is constantly `c` is constantly `a₀`. -/
theorem positiveWordConst_of_positiveWordMap_const {I J : Type*} (f : I → J) (n : ℕ) (w : PositiveWord I n) (c : J) (a₀ : I)
    (hdet : ∀ a : I, f a = c → a = a₀)
    (h : positiveWordMap f n w = positiveWordConst c n) :
    w = positiveWordConst a₀ n := by
  refine (positiveWordEquiv I n).injective ?_
  funext position
  have hpos := congrFun (congrArg (positiveWordEquiv J n) h) position
  rw [positiveWordEquiv_map] at hpos
  simp only [positiveWordEquiv_const, Function.comp_apply] at hpos ⊢
  exact hdet _ hpos

/-- **The shared leg of a zero-coordinate cell, in the shape `hz` needs.**  A fine word whose
coarse image on leg `zero` is the constant degree-zero word is itself the constant zero-pair
word. -/
theorem dwz63_zeroLegWord_eq_const (zero : Leg) (n : ℕ)
    (w : PositiveWord (PositiveWord CWBlock 1) n)
    (h : positiveWordMap (cwSquareDegreeMap zero) n w = positiveWordConst (0 : Fin 5) n) :
    w = positiveWordConst (positiveWordConst CWBlock.zero 1) n :=
  positiveWordConst_of_positiveWordMap_const (cwSquareDegreeMap zero) n w 0
    (positiveWordConst CWBlock.zero 1)
    (fun p hp ↦ (cwSquareBlockDegree_eq_zero_iff p).mp hp) h

end AlgebraicComplexity.Examples
