/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import Mathlib.Analysis.MeanInequalities
import AlgebraicComplexity.Tensor.IndependenceMeasure

/-!
# The splitting bound: deleting one variable from a coefficient table

This file is the fourth partitioning tool of the Alman--Vassilevska Williams barrier framework:

> J. Alman and V. Vassilevska Williams, *Limits on All Known (and Some Unknown) Approaches to
> Matrix Multiplication*, arXiv:1810.08671, Section 5 --- Definition 5.1, Theorem 5.1 and
> Remark 5.1.

AVW's first partitioning tool splits a coefficient table `T` at a *single variable* `x₁` of one
leg: `T = A + B`, where `A` collects the terms using `x₁` and `B = T|_{X ∖ {x₁}}` those avoiding
it.  Both halves are cheap to control --- `A` has one `x`-variable, `B` has one fewer than `T` ---
and Theorem 5.1 turns a bound on `Ī(B)` into a bound on `Ī(T)` that is *strictly below* the trivial
`Ī(T) ≤ |X|`, no matter what the terms using `x₁` are.

## The definitions being transcribed

`coordinateFixVariable i₀ a T` and `coordinateEraseVariable i₀ a T` are AVW's `A = T|_{x₁}` and
`B = T|_{X ∖ {x₁}}`, written for an arbitrary leg `i₀` and variable `a`; they sum to `T`
(`coordinateFixVariable_add_coordinateEraseVariable`), so they are literally a two-part partition
in the sense of AVW Definition 5.1, and `B` is a zeroing out of `T`
(`coordinateEraseVariable_eq_coordinateZeroOut`).

`splittingExponent Q c` and `splittingBound Q c` are AVW's

```
p = log((q-1)/c) / (log q + log((q-1)/c)),      ((q-1)/(1-p))^{1-p} · p^{-p}.
```

The parameter `Q` is an arbitrary **real**: nothing in the optimization uses integrality, and the
tensor-facing hypotheses are two counting bounds, not an equation `|X| = q`.

## Main results

The finite core, and the family of bounds it produces:

* `IndependentSet.card_le_pow_of_splitVariable`: if at most `M` terms of `T` use `a`, `T` has at
  most `R` other leg-`i₀` variables, `I(B^{⊗l}) ≤ c^l` for all `l`, and `u, v ≥ 0` satisfy
  `min {R^l, M^k c^l} ≤ u^k v^l` for all `k, l`, then every independent set of `T^{⊗n}` has at
  most `(u+v)^n` elements.  Fully explicit, no loss, every finite `n`.
* `asymptoticIndependenceNumber_le_of_splitVariable`: hence `Ī(T) ≤ u + v`.
* `asymptoticIndependenceNumber_le_rpow_of_splitVariable`: the one-parameter family
  `Ī(T) ≤ M^{1-θ} + R^θ c^{1-θ}`, valid for every `θ ∈ [0,1]`.

Theorem 5.1 and its interpretation:

* `exists_rpow_add_eq_splittingBound`: the optimization --- the family attains `splittingBound Q c`
  at some `θ ∈ [0,1]`, given AVW's hypothesis `c ≤ (Q-1)/Q^{1/(Q-1)}`.
* `asymptoticIndependenceNumber_le_splittingBound`: **AVW Theorem 5.1**.
* `splittingBound_le`, `splittingBound_lt`: **AVW Remark 5.1**, `splittingBound Q c ≤ Q`, with
  strictness away from the extremal case `p·Q = 1`.

Two exact numerical certificates, the ones AVW use in the second proof of their Lemma 7.2 to reach
`q ≥ 6`:

* `asymptoticIndependenceNumber_le_of_splitVariable_seven`: counts `7`, `6` and `Ī(B) ≤ 1` give
  `Ī(T) ≤ 5.08` (AVW's `5.07905`);
* `asymptoticIndependenceNumber_lt_eight_of_splitVariable`: counts `8`, `7` and `Ī(B) ≤ 5.08` give
  `Ī(T) < 8` (AVW's `7.9973 < 8`).

## The proof, and how it differs from AVW's

AVW argue by a greedy walk over the `n` coordinates of `T^{⊗n}`, replacing the `j`-th tensor factor
by whichever of `A`, `B` retains a `p`- resp. `(1-p)`-fraction of the independent triples, and
finish with two counts on the resulting `A^{⊗k} ⊗ B^{⊗(n-k)}`.  The walk needs the fact
`IndependentSet.of_subSupport`, and it produces the constant `p` before the optimization is done.

The proof formalized here replaces the walk by a *sum over colour words*, exactly as
`IndependentSet.card_le_pow_of_cover` does for Theorem 5.3:

* fix `n` and an independent set `S` of `T^{⊗n}`.  Each `p ∈ S` determines its own colour word
  `w : Fin n → Bool`, recording at which positions the leg-`i₀` letter is `a`; so the classes
  genuinely partition `S`, with no choices to make.  Write `k` and `l` for the numbers of positions
  coloured `true` and `false`;
* *first count*: `p ↦ p i₀` is injective on `S` (`IndependentSet.injOn`) and maps the class into
  the words that are `a` at the `k` chosen positions and a *minimal* leg-`i₀` variable of `T` other
  than `a` elsewhere (`minimalLegSet`), so the class has at most `R^l` elements;
* *second count*: group the class by its letters at the `k` positions coloured `true`.  There are
  at most `M^k` groups, because those letters are terms of `A`; and each group has at most
  `I(B^{⊗l})` elements, because reading off the letters at the remaining `l` positions embeds it
  into an independent set of `B^{⊗l}` (`card_filter_le_independenceNumber_erase`).  So the class
  has at most `M^k c^l` elements;
* summing `min {R^l, M^k c^l} ≤ u^k v^l` over the `2^n` colour words, `Finset.prod_univ_sum` gives
  `|S| ≤ (u+v)^n`.

Two consequences of this reorganization.  There is **no loss at any finite `n`** --- not even a
polynomial one --- so the asymptotic statements follow from the definition of `Ī` as a supremum of
roots.  And the optimization is *separated* from the counting: the counting produces the whole
family `min {R^l, M^k c^l} ≤ u^k v^l`, and the choice `u = M^{1-θ}`, `v = R^θ c^{1-θ}` (legitimate
because `min {x, y} ≤ x^θ y^{1-θ}`) turns it into a one-parameter family of bounds.  AVW's `p` is
recovered as the *fraction* `M^{1-θ}/(M^{1-θ} + R^θ c^{1-θ})` at the optimal `θ`, and the
verification that the optimum equals `((Q-1)/(1-p))^{1-p} p^{-p}` is a self-contained computation
with logarithms (`exists_rpow_add_eq_splittingBound`).

A practical dividend of the same separation: a **rational** `θ` makes every numerical instance a
finite exact computation in `ℚ`, with no logarithm enclosures at all.  The two certificates above
are proved that way, at the price of a few units in the fifth decimal.

## Hypotheses, and what is deliberately not proved

* `NoZeroDivisors K` and `Nontrivial K` appear in the counting theorems and cannot be removed.
  They are used exactly once, in `card_filter_le_independenceNumber_erase`, to know that a triple
  whose `l` letters are all terms of `B` is a term of `B^{⊗l}`; over a ring with zero divisors the
  closure clause of `IndependentSet` for the reconstructed triple genuinely fails.  Contrast
  Theorem 5.3 in `Tensor/IndependenceMeasure.lean`, which needs no ring hypothesis because it only
  ever passes from a nonzero product to its nonzero factors.
* The counting hypotheses are stated with `≤` on the *minimal* leg sets, not with AVW's equation
  `|X| = q` on the ambient variable type; and `Q` is real.  AVW's literal hypotheses imply these.
* The equivalence between AVW's extremal case `c = (Q-1)/Q^{1/(Q-1)}` and `p·Q = 1`, mentioned in
  Remark 5.1, is not formalized: `splittingBound_lt` takes the hypothesis on `p`.
* The applications --- AVW Lemma 7.2 for the generalized Coppersmith--Winograd tensors, which is
  where the counts `7, 6` and `8, 7` come from --- name a construction and belong to a client
  module.  See `BARRIER_FRAMEWORK.md` §6, milestone K.

## Position in the library

Layer 1.  It imports `Tensor/IndependenceMeasure.lean` (for `coordinateMeasure`) and, through it,
`Tensor/AsymptoticIndependenceNumber.lean` and `Tensor/IndependenceNumber.lean` (which own
`coordinateSupport` and `minimalLegSet`), plus Mathlib's weighted AM--GM inequality for Remark 5.1.
It mentions no named matrix-multiplication construction.
-/

namespace AlgebraicComplexity.Tensor

universe u v w

section Split

variable {K : Type u} [CommSemiring K] {κ : Leg → Type v}
variable [∀ i, Fintype (κ i)] [∀ i, DecidableEq (κ i)]

/-- The part of `T` made of the terms that *use* the leg-`i₀` variable `a`. -/
def coordinateFixVariable (i₀ : Leg) (a : κ i₀) (T : (∀ i, κ i) → K) : (∀ i, κ i) → K :=
  fun p ↦ if p i₀ = a then T p else 0

/-- The part of `T` made of the terms that *avoid* the leg-`i₀` variable `a`. -/
def coordinateEraseVariable (i₀ : Leg) (a : κ i₀) (T : (∀ i, κ i) → K) : (∀ i, κ i) → K :=
  fun p ↦ if p i₀ = a then 0 else T p

variable {i₀ : Leg} {a : κ i₀} {T : (∀ i, κ i) → K}

omit [∀ i, Fintype (κ i)] in
theorem coordinateFixVariable_of_eq {p : ∀ i, κ i} (h : p i₀ = a) :
    coordinateFixVariable i₀ a T p = T p := by
  simp [coordinateFixVariable, h]

omit [∀ i, Fintype (κ i)] in
theorem coordinateFixVariable_of_ne {p : ∀ i, κ i} (h : p i₀ ≠ a) :
    coordinateFixVariable i₀ a T p = 0 := by
  simp [coordinateFixVariable, h]

omit [∀ i, Fintype (κ i)] in
theorem coordinateEraseVariable_of_eq {p : ∀ i, κ i} (h : p i₀ = a) :
    coordinateEraseVariable i₀ a T p = 0 := by
  simp [coordinateEraseVariable, h]

omit [∀ i, Fintype (κ i)] in
theorem coordinateEraseVariable_of_ne {p : ∀ i, κ i} (h : p i₀ ≠ a) :
    coordinateEraseVariable i₀ a T p = T p := by
  simp [coordinateEraseVariable, h]

omit [∀ i, Fintype (κ i)] in
theorem coordinateFixVariable_ne_zero {p : ∀ i, κ i}
    (h : coordinateFixVariable i₀ a T p ≠ 0) : T p ≠ 0 ∧ p i₀ = a := by
  by_cases hp : p i₀ = a
  · exact ⟨by rwa [coordinateFixVariable_of_eq hp] at h, hp⟩
  · exact absurd (coordinateFixVariable_of_ne hp) h

omit [∀ i, Fintype (κ i)] in
theorem coordinateEraseVariable_ne_zero {p : ∀ i, κ i}
    (h : coordinateEraseVariable i₀ a T p ≠ 0) : T p ≠ 0 ∧ p i₀ ≠ a := by
  by_cases hp : p i₀ = a
  · exact absurd (coordinateEraseVariable_of_eq hp) h
  · exact ⟨by rwa [coordinateEraseVariable_of_ne hp] at h, hp⟩

omit [∀ i, Fintype (κ i)] in
/-- **`T = A + B`**: the two parts of the splitting are a genuine partition of `T` in the sense of
AVW Definition 5.1. -/
theorem coordinateFixVariable_add_coordinateEraseVariable (i₀ : Leg) (a : κ i₀)
    (T : (∀ i, κ i) → K) :
    coordinateFixVariable i₀ a T + coordinateEraseVariable i₀ a T = T := by
  funext p
  by_cases h : p i₀ = a <;>
    simp [coordinateFixVariable, coordinateEraseVariable, h]

/-- `B = T|_{X ∖ {x₁}}` really is a zeroing out of `T`: it is `coordinateZeroOut` for any family of
variable sets that deletes `a` on leg `i₀` and keeps everything else. -/
theorem coordinateEraseVariable_eq_coordinateZeroOut {A : ∀ i, Finset (κ i)}
    (hA₀ : A i₀ = Finset.univ.erase a) (hA : ∀ i, i ≠ i₀ → A i = Finset.univ) :
    coordinateEraseVariable i₀ a T = coordinateZeroOut T A := by
  funext p
  by_cases h : p i₀ = a
  · rw [coordinateEraseVariable_of_eq h, coordinateZeroOut_of_notMem]
    intro hmem
    have := hmem i₀
    rw [hA₀, h] at this
    exact (Finset.notMem_erase a _) this
  · rw [coordinateEraseVariable_of_ne h, coordinateZeroOut_of_mem]
    intro i
    by_cases hi : i = i₀
    · subst hi; rw [hA₀]; exact Finset.mem_erase.mpr ⟨h, Finset.mem_univ _⟩
    · rw [hA i hi]; exact Finset.mem_univ _

end Split

section FiniteCore

variable {K : Type u} [CommSemiring K] {κ : Leg → Type v}
variable [∀ i, Fintype (κ i)] [∀ i, DecidableEq (κ i)]

/-- Splitting a product over `Fin n` according to a two-colouring of the positions. -/
private theorem prod_bool_word {M : Type*} [CommMonoid M] {n : ℕ} (w : Fin n → Bool)
    (t : Bool → M) :
    ∏ pos : Fin n, t (w pos) =
      t true ^ ({pos | w pos = true} : Finset (Fin n)).card *
        t false ^ ({pos | w pos = false} : Finset (Fin n)).card := by
  classical
  rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ (fun pos ↦ w pos = true) (t <| w ·)]
  have h₁ : ∏ pos ∈ Finset.univ.filter (fun pos : Fin n ↦ w pos = true), t (w pos)
      = t true ^ ({pos | w pos = true} : Finset (Fin n)).card := by
    rw [Finset.prod_congr rfl fun pos hpos ↦ by rw [(Finset.mem_filter.mp hpos).2],
      Finset.prod_const]
  have h₂ : (Finset.univ.filter fun pos : Fin n ↦ ¬ (w pos = true))
      = Finset.univ.filter fun pos ↦ w pos = false := by
    refine Finset.filter_congr fun pos _ ↦ ?_
    simp
  rw [h₁, h₂, Finset.prod_congr rfl fun pos hpos ↦ by rw [(Finset.mem_filter.mp hpos).2],
    Finset.prod_const]

/-- **Fixing the letters outside a set of positions.**  Let `S` be an independent set of terms of
`T^{⊗n}`, let `p₀ ∈ S`, and let `Kf` be a set of positions at which `p₀` avoids the leg-`i₀`
variable `a`.  The elements of `S` that agree with `p₀` outside `Kf` and avoid `a` on leg `i₀`
inside `Kf` are at most `I(B^{⊗|Kf|})` in number, where `B` is `T` with `a` zeroed out.

This is the step of AVW's proof of Theorem 5.1 that turns the `n − k` coordinates carrying no `x₁`
into a genuine independent set of `B^{⊗(n−k)}`; it is the only place where the closure clause of
`IndependentSet` has to be re-established.

Proof sketch: choose a bijection `Fin |Kf| ≃ Kf` and read off the letters of the elements at the
positions of `Kf`.  That map is injective on the set in question (two elements agreeing on `Kf`
agree everywhere, since they agree with `p₀` outside `Kf`), and its image is an independent set of
`B^{⊗|Kf|}`: the terms are terms of `B` because they avoid `a`; distinctness is inherited from `S`;
and for closure, a boxed term of `B^{⊗|Kf|}` is spliced with the letters of `p₀` outside `Kf` into
a term of `T^{⊗n}` boxed by `S`, which the closure clause for `S` puts back into `S`. -/
private theorem card_filter_le_independenceNumber_erase [NoZeroDivisors K] [Nontrivial K]
    {T : (∀ i, κ i) → K} {i₀ : Leg} {a : κ i₀} {n : ℕ}
    {S : Finset (∀ i, Fin n → κ i)} (hS : IndependentSet (coordinatePower T n) S)
    {p₀ : ∀ i, Fin n → κ i} (hp₀ : p₀ ∈ S) (Kf : Finset (Fin n)) :
    (S.filter fun p ↦ (∀ pos ∈ Kf, p i₀ pos ≠ a) ∧
        ∀ pos, pos ∉ Kf → ∀ i, p i pos = p₀ i pos).card ≤
      independenceNumber (coordinatePower (coordinateEraseVariable i₀ a T) Kf.card) := by
  classical
  set Bt := coordinateEraseVariable i₀ a T with hBt
  set l := Kf.card with hl
  set F := S.filter fun p ↦ (∀ pos ∈ Kf, p i₀ pos ≠ a) ∧
      ∀ pos, pos ∉ Kf → ∀ i, p i pos = p₀ i pos with hF
  have hmemF : ∀ p, p ∈ F ↔ p ∈ S ∧ (∀ pos ∈ Kf, p i₀ pos ≠ a) ∧
      ∀ pos, pos ∉ Kf → ∀ i, p i pos = p₀ i pos := by
    intro p; rw [hF, Finset.mem_filter]
  have hletter : ∀ p ∈ S, ∀ pos : Fin n, T (fun i ↦ p i pos) ≠ 0 := by
    intro p hp pos h0
    refine hS.ne_zero p hp ?_
    rw [coordinatePower_apply]
    exact Finset.prod_eq_zero (Finset.mem_univ pos) h0
  -- an enumeration of the positions of `Kf`
  set eF : Fin l ≃ {x // x ∈ Kf} :=
    (Fintype.equivFinOfCardEq (by simp [hl])).symm with heF
  set ix : Fin l → Fin n := fun j ↦ (eF j).1 with hix
  have hixmem : ∀ j, ix j ∈ Kf := fun j ↦ (eF j).2
  set Bmap : (∀ i, Fin n → κ i) → (∀ i, Fin l → κ i) := fun p i j ↦ p i (ix j) with hBmap
  have hsymm : ∀ (pos : Fin n) (h : pos ∈ Kf), ix (eF.symm ⟨pos, h⟩) = pos := by
    intro pos h
    simp [hix]
  -- `Bmap` is injective on `F`
  have hinj : Set.InjOn Bmap (F : Set (∀ i, Fin n → κ i)) := by
    intro p hp p' hp' hpp'
    have hpF := (hmemF p).mp (Finset.mem_coe.mp hp)
    have hp'F := (hmemF p').mp (Finset.mem_coe.mp hp')
    funext i pos
    by_cases hpos : pos ∈ Kf
    · have := congrFun (congrFun hpp' i) (eF.symm ⟨pos, hpos⟩)
      simpa [hBmap, hsymm pos hpos] using this
    · rw [hpF.2.2 pos hpos i, hp'F.2.2 pos hpos i]
  -- the image is an independent set of `B^{⊗l}`
  have hnz : ∀ p ∈ F, ∀ j : Fin l, Bt (fun i ↦ p i (ix j)) ≠ 0 := by
    intro p hp j
    have hpF := (hmemF p).mp hp
    rw [hBt, coordinateEraseVariable_of_ne (hpF.2.1 _ (hixmem j))]
    exact hletter p hpF.1 _
  have himage : IndependentSet (coordinatePower Bt l) (F.image Bmap) := by
    refine ⟨?_, ?_, ?_⟩
    · intro q hq
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hq
      rw [coordinatePower_apply]
      exact Finset.prod_ne_zero_iff.mpr fun j _ ↦ hnz p hp j
    · intro q hq q' hq' i hii
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hq
      obtain ⟨p', hp', rfl⟩ := Finset.mem_image.mp hq'
      have hpF := (hmemF p).mp hp
      have hp'F := (hmemF p').mp hp'
      have hleg : p i = p' i := by
        funext pos
        by_cases hpos : pos ∈ Kf
        · have := congrFun hii (eF.symm ⟨pos, hpos⟩)
          simpa [hBmap, hsymm pos hpos] using this
        · rw [hpF.2.2 pos hpos i, hp'F.2.2 pos hpos i]
      rw [hS.distinct p hpF.1 p' hp'F.1 i hleg]
    · intro q hq hbox
      set ptilde : ∀ i, Fin n → κ i :=
        fun i pos ↦ if h : pos ∈ Kf then q i (eF.symm ⟨pos, h⟩) else p₀ i pos with hptilde
      have hqletter : ∀ j : Fin l, Bt (fun i ↦ q i j) ≠ 0 := by
        intro j h0
        refine hq ?_
        rw [coordinatePower_apply]
        exact Finset.prod_eq_zero (Finset.mem_univ j) h0
      have hpt_in : ∀ (pos : Fin n) (h : pos ∈ Kf),
          (fun i ↦ ptilde i pos) = fun i ↦ q i (eF.symm ⟨pos, h⟩) := by
        intro pos h; funext i; simp [hptilde, h]
      have hpt_out : ∀ (pos : Fin n), pos ∉ Kf → ∀ i, ptilde i pos = p₀ i pos := by
        intro pos h i; simp [hptilde, h]
      -- `ptilde` is a term of `T^{⊗n}`
      have hptT : coordinatePower T n ptilde ≠ 0 := by
        rw [coordinatePower_apply]
        refine Finset.prod_ne_zero_iff.mpr fun pos _ ↦ ?_
        by_cases hpos : pos ∈ Kf
        · rw [hpt_in pos hpos]
          exact (coordinateEraseVariable_ne_zero (hqletter (eF.symm ⟨pos, hpos⟩))).1
        · have : (fun i ↦ ptilde i pos) = fun i ↦ p₀ i pos := funext (hpt_out pos hpos)
          rw [this]
          exact hletter p₀ hp₀ pos
      -- `ptilde` is boxed by `S`
      have hptbox : ∀ i, ∃ s ∈ S, s i = ptilde i := by
        intro i
        obtain ⟨q'', hq'', hq''i⟩ := hbox i
        obtain ⟨p₁, hp₁, rfl⟩ := Finset.mem_image.mp hq''
        have hp₁F := (hmemF p₁).mp hp₁
        refine ⟨p₁, hp₁F.1, ?_⟩
        funext pos
        by_cases hpos : pos ∈ Kf
        · have := congrFun hq''i (eF.symm ⟨pos, hpos⟩)
          simp only [hBmap, hsymm pos hpos] at this
          simp [hptilde, hpos, this]
        · rw [hp₁F.2.2 pos hpos i, hpt_out pos hpos i]
      have hptS : ptilde ∈ S := hS.closed ptilde hptT hptbox
      have hptF : ptilde ∈ F := by
        refine (hmemF ptilde).mpr ⟨hptS, ?_, hpt_out⟩
        intro pos hpos
        have := (coordinateEraseVariable_ne_zero (hqletter (eF.symm ⟨pos, hpos⟩))).2
        simpa [hptilde, hpos] using this
      refine Finset.mem_image.mpr ⟨ptilde, hptF, ?_⟩
      funext i j
      have hj : ix j ∈ Kf := hixmem j
      have : eF.symm ⟨ix j, hj⟩ = j := by
        rw [show (⟨ix j, hj⟩ : {x // x ∈ Kf}) = eF j from Subtype.ext rfl, Equiv.symm_apply_apply]
      simp [hBmap, hptilde, hj, this]
  calc F.card = (F.image Bmap).card := (Finset.card_image_of_injOn hinj).symm
    _ ≤ independenceNumber (coordinatePower Bt l) := himage.card_le_independenceNumber

/-- **The finite core of AVW Theorem 5.1.**  Let `T` be a coefficient table, `a` a variable of leg
`i₀`, `A` the part of `T` made of the terms using `a` and `B = T|_{X ∖ {a}}` the part avoiding it.
Suppose

* `A` has at most `m` terms;
* `T` uses at most `r` variables other than `a` on leg `i₀`;
* `I(B^{⊗l}) ≤ c^l` for every `l`;
* `u, v` are reals with `min {r^l, m^k c^l} ≤ u^k v^l` for all `k, l`.

Then every independent set of terms of `T^{⊗n}` has at most `(u + v)^n` elements.

The two-parameter form is what removes all real-exponent bookkeeping from the counting argument:
the hypothesis on `u` and `v` is satisfied by `u = m^{1-θ}`, `v = r^θ c^{1-θ}` for every
`θ ∈ [0,1]`, because `min {A, B} ≤ A^θ B^{1-θ}`
(`asymptoticIndependenceNumber_le_rpow_of_splitVariable`).

Proof sketch, following AVW but replacing their greedy walk by a sum over colour words in the
style of `IndependentSet.card_le_pow_of_cover`.  Classify the elements of an independent set `S`
of `T^{⊗n}` by the *colour word* `w : Fin n → Bool` recording at which positions the leg-`i₀`
letter is `a`; the classification is a function of the element, so the classes partition `S`.  Fix
a word `w`, and let `k` and `l` be the numbers of positions coloured `true` and `false`.

*First count, on leg `i₀`*: the projection `p ↦ p i₀` is injective on `S`, and on the class it
lands in the words whose letters are `a` at the `k` chosen positions and one of the `r` other
leg-`i₀` variables of `T` elsewhere.  So the class has at most `r^l` elements.

*Second count*: group the class by the letters at the `k` positions coloured `true`.  There are at
most `m^k` such groups, since each of those letters is a term of `A`; and one group has at most
`I(B^{⊗l})  ≤ c^l` elements, by `card_filter_le_independenceNumber_erase`.  So the class has at
most `m^k c^l` elements.

Combining, the class has at most `u^k v^l` elements, and summing over the `2^n` colour words the
expansion `Finset.prod_univ_sum` gives `(u + v)^n`. -/
theorem IndependentSet.card_le_pow_of_splitVariable [NoZeroDivisors K] [Nontrivial K]
    {T : (∀ i, κ i) → K} {i₀ : Leg} {a : κ i₀} {M R c u v : ℝ} (hc : 0 ≤ c)
    (hm : ((coordinateSupport (coordinateFixVariable i₀ a T)).card : ℝ) ≤ M)
    (hr : (((minimalLegSet T i₀).erase a).card : ℝ) ≤ R)
    (hB : ∀ l : ℕ, ((independenceNumber
        (coordinatePower (coordinateEraseVariable i₀ a T) l) : ℕ) : ℝ) ≤ c ^ l)
    (hsplit : ∀ k l : ℕ, min (R ^ l) (M ^ k * c ^ l) ≤ u ^ k * v ^ l)
    {n : ℕ} {S : Finset (∀ i, Fin n → κ i)}
    (hS : IndependentSet (coordinatePower T n) S) :
    (S.card : ℝ) ≤ (u + v) ^ n := by
  classical
  have hletter : ∀ p ∈ S, ∀ pos : Fin n, T (fun i ↦ p i pos) ≠ 0 := by
    intro p hp pos h0
    refine hS.ne_zero p hp ?_
    rw [coordinatePower_apply]
    exact Finset.prod_eq_zero (Finset.mem_univ pos) h0
  set cls : (Fin n → Bool) → Finset (∀ i, Fin n → κ i) :=
    fun w ↦ S.filter fun p ↦ ∀ pos, (p i₀ pos = a) ↔ w pos = true with hcls
  have hclsmem : ∀ (w : Fin n → Bool) (p : ∀ i, Fin n → κ i),
      p ∈ cls w ↔ p ∈ S ∧ ∀ pos, (p i₀ pos = a) ↔ w pos = true := by
    intro w p; rw [hcls, Finset.mem_filter]
  have hcov : S ⊆ Finset.univ.biUnion cls := by
    intro p hp
    refine Finset.mem_biUnion.mpr ⟨fun pos ↦ decide (p i₀ pos = a), Finset.mem_univ _, ?_⟩
    exact (hclsmem _ p).mpr ⟨hp, fun pos ↦ by simp⟩
  -- the count on one colour class
  have hclass : ∀ w : Fin n → Bool, ((cls w).card : ℝ) ≤
      ∏ pos : Fin n, (fun b : Bool ↦ if b = true then u else v) (w pos) := by
    intro w
    set Kt : Finset (Fin n) := Finset.univ.filter (fun pos ↦ w pos = true) with hKt
    set Kf : Finset (Fin n) := Finset.univ.filter (fun pos ↦ w pos = false) with hKf
    have hmemKf : ∀ pos : Fin n, pos ∈ Kf ↔ w pos = false := by intro pos; simp [hKf]
    have hnotKf : ∀ pos : Fin n, pos ∉ Kf ↔ w pos = true := by
      intro pos; rw [hmemKf]; cases h : w pos <;> simp
    have hclsS : cls w ⊆ S := Finset.filter_subset _ _
    have hprod : ∏ pos : Fin n, (fun b : Bool ↦ if b = true then u else v) (w pos)
        = u ^ Kt.card * v ^ Kf.card := by
      rw [prod_bool_word w (fun b : Bool ↦ if b = true then u else v)]; simp [hKt, hKf]
    rw [hprod]
    -- first count: the variables of leg `i₀`
    have hb1 : ((cls w).card : ℝ) ≤ R ^ Kf.card := by
      have hcard : (cls w).card ≤ (Fintype.piFinset fun pos : Fin n ↦
          if w pos = true then ({a} : Finset (κ i₀))
          else (minimalLegSet T i₀).erase a).card := by
        refine Finset.card_le_card_of_injOn (fun p ↦ p i₀) (fun p hp ↦ ?_) ?_
        · obtain ⟨hpS, hpc⟩ := (hclsmem w p).mp (Finset.mem_coe.mp hp)
          refine Finset.mem_coe.mpr (Fintype.mem_piFinset.mpr fun pos ↦ ?_)
          by_cases hw : w pos = true
          · simp only [if_pos hw, Finset.mem_singleton]
            exact (hpc pos).mpr hw
          · rw [if_neg hw]
            exact Finset.mem_erase.mpr ⟨fun hh ↦ hw ((hpc pos).mp hh),
              mem_minimalLegSet_of_ne_zero (hletter p hpS pos) i₀⟩
        · exact (hS.injOn i₀).mono (Finset.coe_subset.mpr hclsS)
      have hpi : (Fintype.piFinset fun pos : Fin n ↦
          if w pos = true then ({a} : Finset (κ i₀))
          else (minimalLegSet T i₀).erase a).card
          = ((minimalLegSet T i₀).erase a).card ^ Kf.card := by
        rw [Fintype.card_piFinset]
        simp only [apply_ite Finset.card, Finset.card_singleton]
        rw [prod_bool_word w (fun b : Bool ↦
          if b = true then 1 else ((minimalLegSet T i₀).erase a).card)]
        simp [hKf]
      rw [hpi] at hcard
      calc ((cls w).card : ℝ) ≤ ((((minimalLegSet T i₀).erase a).card ^ Kf.card : ℕ) : ℝ) := by
            exact_mod_cast hcard
        _ ≤ R ^ Kf.card := by
            push_cast
            exact pow_le_pow_left₀ (by positivity) hr _
    -- second count: the terms using `a`, and the independence number of `B`
    have hb2 : ((cls w).card : ℝ) ≤ M ^ Kt.card * c ^ Kf.card := by
      set key : (∀ i, Fin n → κ i) → (Fin n → Option (∀ i, κ i)) :=
        fun p pos ↦ if w pos = false then none else some fun i ↦ p i pos with hkey
      have himg : (((cls w).image key).card : ℝ) ≤ M ^ Kt.card := by
        have hsub : (cls w).image key ⊆ Fintype.piFinset fun pos : Fin n ↦
            if w pos = false then ({none} : Finset (Option (∀ i, κ i)))
            else (coordinateSupport (coordinateFixVariable i₀ a T)).image some := by
          intro y hy
          obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hy
          obtain ⟨hpS, hpc⟩ := (hclsmem w p).mp hp
          refine Fintype.mem_piFinset.mpr fun pos ↦ ?_
          by_cases hw : w pos = false
          · simp [hkey, hw]
          · rw [if_neg hw]
            refine Finset.mem_image.mpr ⟨fun i ↦ p i pos, ?_, ?_⟩
            · have hpa : p i₀ pos = a := (hpc pos).mpr (by cases h : w pos <;> simp_all)
              rw [mem_coordinateSupport, coordinateFixVariable_of_eq hpa]
              exact hletter p hpS pos
            · simp [hkey, hw]
        have hcardpi : (Fintype.piFinset fun pos : Fin n ↦
            if w pos = false then ({none} : Finset (Option (∀ i, κ i)))
            else (coordinateSupport (coordinateFixVariable i₀ a T)).image some).card
            = (coordinateSupport (coordinateFixVariable i₀ a T)).card ^ Kt.card := by
          rw [Fintype.card_piFinset]
          simp only [apply_ite Finset.card, Finset.card_singleton,
            Finset.card_image_of_injective _ (Option.some_injective _)]
          rw [prod_bool_word w (fun b : Bool ↦ if b = false then 1 else
            (coordinateSupport (coordinateFixVariable i₀ a T)).card)]
          simp [hKt]
        have := Finset.card_le_card hsub
        rw [hcardpi] at this
        calc (((cls w).image key).card : ℝ)
            ≤ (((coordinateSupport (coordinateFixVariable i₀ a T)).card ^ Kt.card : ℕ) : ℝ) := by
              exact_mod_cast this
          _ ≤ M ^ Kt.card := by
              push_cast
              exact pow_le_pow_left₀ (by positivity) hm _
      have hfib : ∀ y ∈ (cls w).image key,
          ((((cls w).filter fun p ↦ key p = y).card : ℕ) : ℝ) ≤ c ^ Kf.card := by
        intro y hy
        obtain ⟨p₀, hp₀, rfl⟩ := Finset.mem_image.mp hy
        have hsub : ((cls w).filter fun p ↦ key p = key p₀) ⊆
            S.filter (fun p ↦ (∀ pos ∈ Kf, p i₀ pos ≠ a) ∧
              ∀ pos, pos ∉ Kf → ∀ i, p i pos = p₀ i pos) := by
          intro p hp
          rw [Finset.mem_filter] at hp
          obtain ⟨hpcls, hpkey⟩ := hp
          obtain ⟨hpS, hpc⟩ := (hclsmem w p).mp hpcls
          refine Finset.mem_filter.mpr ⟨hpS, fun pos hpos hh ↦ ?_, fun pos hpos i ↦ ?_⟩
          · rw [hmemKf] at hpos
            rw [(hpc pos).mp hh] at hpos
            exact Bool.noConfusion hpos
          · have hw : ¬ (w pos = false) := by
              rw [(hnotKf pos).mp hpos]; exact Bool.noConfusion
            have h := congrFun hpkey pos
            rw [hkey] at h
            simp only [if_neg hw, Option.some.injEq] at h
            exact congrFun h i
        calc ((((cls w).filter fun p ↦ key p = key p₀).card : ℕ) : ℝ)
            ≤ (((S.filter (fun p ↦ (∀ pos ∈ Kf, p i₀ pos ≠ a) ∧
                ∀ pos, pos ∉ Kf → ∀ i, p i pos = p₀ i pos)).card : ℕ) : ℝ) := by
              exact_mod_cast Finset.card_le_card hsub
          _ ≤ ((independenceNumber
                (coordinatePower (coordinateEraseVariable i₀ a T) Kf.card) : ℕ) : ℝ) := by
              exact_mod_cast card_filter_le_independenceNumber_erase hS (hclsS hp₀) Kf
          _ ≤ c ^ Kf.card := hB _
      calc ((cls w).card : ℝ)
          = ∑ y ∈ (cls w).image key, (((cls w).filter fun p ↦ key p = y).card : ℝ) := by
            rw [Finset.card_eq_sum_card_image key (cls w)]; push_cast; ring
        _ ≤ ∑ _y ∈ (cls w).image key, c ^ Kf.card := Finset.sum_le_sum hfib
        _ = (((cls w).image key).card : ℝ) * c ^ Kf.card := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ M ^ Kt.card * c ^ Kf.card :=
            mul_le_mul_of_nonneg_right himg (by positivity)
    exact le_trans (le_min hb1 hb2) (hsplit Kt.card Kf.card)
  -- sum over the colour words
  have hexpand : ∑ w : Fin n → Bool,
      ∏ pos : Fin n, (fun b : Bool ↦ if b = true then u else v) (w pos) = (u + v) ^ n := by
    have h := Finset.prod_univ_sum (fun _ : Fin n ↦ (Finset.univ : Finset Bool))
      fun _ (b : Bool) ↦ (if b = true then u else v)
    rw [Fintype.piFinset_univ] at h
    rw [← h, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    congr 1
    rw [Fintype.sum_bool]
    simp
  calc (S.card : ℝ) ≤ (((Finset.univ.biUnion cls).card : ℕ) : ℝ) := by
        exact_mod_cast Finset.card_le_card hcov
    _ ≤ ((∑ w : Fin n → Bool, (cls w).card : ℕ) : ℝ) := by
        exact_mod_cast Finset.card_biUnion_le
    _ = ∑ w : Fin n → Bool, ((cls w).card : ℝ) := by push_cast; ring
    _ ≤ ∑ w : Fin n → Bool,
          ∏ pos : Fin n, (fun b : Bool ↦ if b = true then u else v) (w pos) :=
        Finset.sum_le_sum fun w _ ↦ hclass w
    _ = (u + v) ^ n := hexpand

end FiniteCore

section Asymptotic

variable {K : Type u} [CommSemiring K] {κ : Leg → Type v}
variable [∀ i, Fintype (κ i)] [∀ i, DecidableEq (κ i)]

/-- **The splitting bound at a fixed Kronecker power**: the finite core applied to a largest
independent set. -/
theorem independenceNumber_coordinatePower_le_pow_of_splitVariable
    [NoZeroDivisors K] [Nontrivial K]
    {T : (∀ i, κ i) → K} {i₀ : Leg} {a : κ i₀} {M R c u v : ℝ} (hc : 0 ≤ c)
    (hm : ((coordinateSupport (coordinateFixVariable i₀ a T)).card : ℝ) ≤ M)
    (hr : (((minimalLegSet T i₀).erase a).card : ℝ) ≤ R)
    (hB : ∀ l : ℕ, ((independenceNumber
        (coordinatePower (coordinateEraseVariable i₀ a T) l) : ℕ) : ℝ) ≤ c ^ l)
    (hsplit : ∀ k l : ℕ, min (R ^ l) (M ^ k * c ^ l) ≤ u ^ k * v ^ l) (n : ℕ) :
    ((independenceNumber (coordinatePower T n) : ℕ) : ℝ) ≤ (u + v) ^ n := by
  obtain ⟨S, hS, hcard⟩ := exists_independentSet_card_eq (coordinatePower T n)
  rw [← hcard]
  exact hS.card_le_pow_of_splitVariable hc hm hr hB hsplit

/-- **The splitting bound, asymptotic form.**  With the notation of
`IndependentSet.card_le_pow_of_splitVariable`, `Ī(T) ≤ u + v`. -/
theorem asymptoticIndependenceNumber_le_of_splitVariable [NoZeroDivisors K] [Nontrivial K]
    {T : (∀ i, κ i) → K} {i₀ : Leg} {a : κ i₀} {M R c u v : ℝ} (hc : 0 ≤ c)
    (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hm : ((coordinateSupport (coordinateFixVariable i₀ a T)).card : ℝ) ≤ M)
    (hr : (((minimalLegSet T i₀).erase a).card : ℝ) ≤ R)
    (hB : asymptoticIndependenceNumber (coordinateEraseVariable i₀ a T) ≤ c)
    (hsplit : ∀ k l : ℕ, min (R ^ l) (M ^ k * c ^ l) ≤ u ^ k * v ^ l) :
    asymptoticIndependenceNumber T ≤ u + v :=
  asymptoticIndependenceNumber_le_of_pow (by positivity) fun n ↦
    independenceNumber_coordinatePower_le_pow_of_splitVariable hc hm hr
      (independenceNumber_coordinatePower_le_pow_of_asymptotic hB) hsplit n

/-! ### The one-parameter family of splitting bounds -/

/-- Commuting a natural power past a real power on a nonnegative base. -/
private theorem rpow_natPow_comm {x : ℝ} (hx : 0 ≤ x) (θ : ℝ) (k : ℕ) :
    (x ^ k) ^ θ = (x ^ θ) ^ k := by
  rw [← Real.rpow_natCast x k, ← Real.rpow_natCast (x ^ θ) k, ← Real.rpow_mul hx,
    ← Real.rpow_mul hx, mul_comm]

/-- The minimum of two nonnegative reals is at most any weighted geometric mean of them. -/
private theorem min_le_rpow_mul_rpow {A B θ : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hθ₀ : 0 ≤ θ) (hθ₁ : θ ≤ 1) : min A B ≤ A ^ θ * B ^ (1 - θ) := by
  have hmin : 0 ≤ min A B := le_min hA hB
  calc min A B = min A B ^ θ * min A B ^ (1 - θ) := by
        rw [← Real.rpow_add' hmin (by norm_num), add_sub_cancel, Real.rpow_one]
    _ ≤ A ^ θ * B ^ (1 - θ) :=
        mul_le_mul (Real.rpow_le_rpow hmin (min_le_left _ _) hθ₀)
          (Real.rpow_le_rpow hmin (min_le_right _ _) (by linarith))
          (Real.rpow_nonneg hmin _) (Real.rpow_nonneg hA _)

/-- **The one-parameter splitting bound.**  For every `θ ∈ [0,1]`,

```
Ī(T) ≤ m^{1-θ} + r^θ · c^{1-θ},
```

where `m` bounds the number of terms of `T` using the leg-`i₀` variable `a`, `r` bounds the number
of other leg-`i₀` variables of `T`, and `c` bounds `Ī` of the table obtained by deleting `a`.

Choosing `θ` optimally gives AVW Theorem 5.1
(`asymptoticIndependenceNumber_le_splittingBound`); the whole family is recorded because a
*rational* `θ` turns any numerical instance into exact rational arithmetic, with no logarithms.

Proof sketch: `min {r^l, m^k c^l} ≤ (r^l)^θ (m^k c^l)^{1-θ} = (m^{1-θ})^k (r^θ c^{1-θ})^l`. -/
theorem asymptoticIndependenceNumber_le_rpow_of_splitVariable [NoZeroDivisors K] [Nontrivial K]
    {T : (∀ i, κ i) → K} {i₀ : Leg} {a : κ i₀} {M R c θ : ℝ} (hc : 0 ≤ c)
    (hθ₀ : 0 ≤ θ) (hθ₁ : θ ≤ 1)
    (hm : ((coordinateSupport (coordinateFixVariable i₀ a T)).card : ℝ) ≤ M)
    (hr : (((minimalLegSet T i₀).erase a).card : ℝ) ≤ R)
    (hB : asymptoticIndependenceNumber (coordinateEraseVariable i₀ a T) ≤ c) :
    asymptoticIndependenceNumber T ≤ M ^ (1 - θ) + R ^ θ * c ^ (1 - θ) := by
  have hM0 : 0 ≤ M := le_trans (by positivity) hm
  have hR0 : 0 ≤ R := le_trans (by positivity) hr
  refine asymptoticIndependenceNumber_le_of_splitVariable hc (by positivity) (by positivity)
    hm hr hB fun k l ↦ ?_
  have hkey : (R ^ l) ^ θ * (M ^ k * c ^ l) ^ (1 - θ)
      = (M ^ (1 - θ)) ^ k * (R ^ θ * c ^ (1 - θ)) ^ l := by
    rw [Real.mul_rpow (by positivity) (by positivity), rpow_natPow_comm (by positivity) θ l,
      rpow_natPow_comm (by positivity) (1 - θ) k, rpow_natPow_comm hc (1 - θ) l, mul_pow]
    ring
  rw [← hkey]
  exact min_le_rpow_mul_rpow (by positivity) (by positivity) hθ₀ hθ₁

end Asymptotic

section ClosedForm

/-- **AVW's exponent `p`** of Theorem 5.1:
`p = log((q-1)/c) / (log q + log((q-1)/c))`.  The parameter `Q` plays the role of AVW's `q`; it is
allowed to be an arbitrary real, since nothing in the optimization uses integrality. -/
noncomputable def splittingExponent (Q c : ℝ) : ℝ :=
  Real.log ((Q - 1) / c) / (Real.log Q + Real.log ((Q - 1) / c))

/-- **AVW's splitting bound** of Theorem 5.1: `((q-1)/(1-p))^{1-p} · p^{-p}`, written as a
quotient. -/
noncomputable def splittingBound (Q c : ℝ) : ℝ :=
  ((Q - 1) / (1 - splittingExponent Q c)) ^ (1 - splittingExponent Q c) /
    splittingExponent Q c ^ splittingExponent Q c

/-- **The optimization behind AVW Theorem 5.1.**  If `2 ≤ Q`, `0 < c` and
`c ≤ (Q-1)/Q^{1/(Q-1)}`, then the one-parameter family `θ ↦ Q^{1-θ} + (Q-1)^θ c^{1-θ}` attains the
value `splittingBound Q c` at some `θ ∈ [0,1]`.

AVW state the optimum through the *fractions* `p` and `1-p` of the two counts; the parameter here
is instead the exponent `θ`, related to `p` by `Q^{1-θ} = p · splittingBound Q c`.  The proof
verifies that this `θ` splits the bound in the ratio `p : 1-p`, which is the content of AVW's
"setting the two terms equal and solving for `k`".

The hypothesis `c ≤ (Q-1)/Q^{1/(Q-1)}` is used exactly once, to give `1 ≤ pQ`
(AVW's Remark 5.1), which is what makes `θ ≤ 1`.  That `0 ≤ θ` needs no hypothesis beyond
`0 < c`: it follows from `log x ≤ x - 1` twice, once for `x = (Q-1)/c` and once for `x = 1/Q`. -/
theorem exists_rpow_add_eq_splittingBound {Q c : ℝ} (hQ : 2 ≤ Q) (hc0 : 0 < c)
    (hcq : c ≤ (Q - 1) / Q ^ (Q - 1)⁻¹) :
    ∃ θ : ℝ, 0 ≤ θ ∧ θ ≤ 1 ∧
      Q ^ (1 - θ) + (Q - 1) ^ θ * c ^ (1 - θ) = splittingBound Q c := by
  have hQ1 : (1 : ℝ) < Q := by linarith
  have hQ0 : (0 : ℝ) < Q := by linarith
  have hQm0 : (0 : ℝ) < Q - 1 := by linarith
  set Lq := Real.log Q with hLqdef
  set Mc := Real.log ((Q - 1) / c) with hMcdef
  have hLq : 0 < Lq := Real.log_pos hQ1
  have hLqne : Lq ≠ 0 := ne_of_gt hLq
  -- AVW's Remark 5.1, in the form `Lq ≤ (Q-1) · Mc`
  have hMclb : Lq / (Q - 1) ≤ Mc := by
    have hpow : (0 : ℝ) < Q ^ (Q - 1)⁻¹ := Real.rpow_pos_of_pos hQ0 _
    have h1 : Q ^ (Q - 1)⁻¹ ≤ (Q - 1) / c := by
      rw [le_div_iff₀ hc0, mul_comm]
      rw [le_div_iff₀ hpow] at hcq
      exact hcq
    have h2 := Real.log_le_log hpow h1
    rw [Real.log_rpow hQ0] at h2
    calc Lq / (Q - 1) = (Q - 1)⁻¹ * Lq := by ring
      _ ≤ Mc := h2
  have hMc : 0 < Mc := lt_of_lt_of_le (by positivity) hMclb
  have hsum : 0 < Lq + Mc := by linarith
  have hpeq : splittingExponent Q c = Mc / (Lq + Mc) := by
    rw [splittingExponent, hLqdef, hMcdef]
  set p := splittingExponent Q c with hpdef
  have hp : p * (Lq + Mc) = Mc := by rw [hpeq]; field_simp
  have hp0 : 0 < p := by rw [hpeq]; positivity
  have h1p : (1 - p) * (Lq + Mc) = Lq := by linear_combination -hp
  have hp1 : p < 1 := by nlinarith
  have h1p0 : 0 < 1 - p := by linarith
  have hratio : p * Lq = (1 - p) * Mc := by linear_combination hp
  -- `1 ≤ p · Q`
  have hpQ : 1 ≤ p * Q := by
    have hstep : Lq ≤ (Q - 1) * Mc := by
      rw [div_le_iff₀ hQm0] at hMclb; linarith
    rw [hpeq, div_mul_eq_mul_div, le_div_iff₀ hsum]
    nlinarith [hstep]
  -- the bound and its two pieces
  set G := splittingBound Q c with hGdef
  have hGeq : G = ((Q - 1) / (1 - p)) ^ (1 - p) / p ^ p := by rw [hGdef, splittingBound]
  have hG0 : 0 < G := by rw [hGeq]; positivity
  set A := p * G with hAdef
  set B := (1 - p) * G with hBdef
  have hA0 : 0 < A := by rw [hAdef]; positivity
  have hB0 : 0 < B := by rw [hBdef]; positivity
  have hAB : A + B = G := by rw [hAdef, hBdef]; ring
  have hlogG : Real.log G = (1 - p) * (Real.log (Q - 1) - Real.log (1 - p)) - p * Real.log p := by
    rw [hGeq, Real.log_div (by positivity) (by positivity), Real.log_rpow (by positivity),
      Real.log_rpow hp0, Real.log_div (ne_of_gt hQm0) (ne_of_gt h1p0)]
  have hlogA : Real.log A = (1 - p) * (Real.log p - Real.log (1 - p) + Real.log (Q - 1)) := by
    rw [hAdef, Real.log_mul (ne_of_gt hp0) (ne_of_gt hG0), hlogG]; ring
  have hlogB : Real.log B
      = p * Real.log (1 - p) + (1 - p) * Real.log (Q - 1) - p * Real.log p := by
    rw [hBdef, Real.log_mul (ne_of_gt h1p0) (ne_of_gt hG0), hlogG]; ring
  -- `0 ≤ log A`, i.e. `θ ≤ 1`
  have hcomb : Real.log p - Real.log (1 - p) + Real.log (Q - 1)
      = Real.log (p * (Q - 1) / (1 - p)) := by
    rw [Real.log_div (by positivity) (ne_of_gt h1p0), Real.log_mul (ne_of_gt hp0) (ne_of_gt hQm0)]
    ring
  have hlogAnn : 0 ≤ Real.log A := by
    rw [hlogA, hcomb]
    refine mul_nonneg (le_of_lt h1p0) (Real.log_nonneg ?_)
    rw [le_div_iff₀ h1p0]
    nlinarith [hpQ]
  -- `log A ≤ Lq`, i.e. `0 ≤ θ`
  have hcMc : c * Mc ≤ Q * Lq := by
    have h1 : Mc ≤ (Q - 1) / c - 1 := Real.log_le_sub_one_of_pos (by positivity)
    have h2 : Real.log Q⁻¹ ≤ Q⁻¹ - 1 := Real.log_le_sub_one_of_pos (by positivity)
    rw [Real.log_inv, ← hLqdef] at h2
    have h3 : Q - 1 ≤ Q * Lq := by
      have := mul_le_mul_of_nonneg_left (by linarith : (1 : ℝ) - Q⁻¹ ≤ Lq) (le_of_lt hQ0)
      rw [mul_sub, mul_inv_cancel₀ (ne_of_gt hQ0)] at this
      linarith
    have h4 : c * Mc ≤ c * ((Q - 1) / c - 1) := mul_le_mul_of_nonneg_left h1 (le_of_lt hc0)
    rw [mul_sub, mul_div_cancel₀ _ (ne_of_gt hc0)] at h4
    linarith
  have hMcsplit : Mc = Real.log (Q - 1) - Real.log c :=
    Real.log_div (ne_of_gt hQm0) (ne_of_gt hc0)
  have hpq : p * (Q - 1) / (1 - p) = (Q - 1) * Mc / Lq := by
    rw [div_eq_div_iff (ne_of_gt h1p0) hLqne]
    linear_combination (Q - 1) * hratio
  have h1peq : 1 - p = Lq / (Lq + Mc) := by
    rw [eq_div_iff (ne_of_gt hsum)]; exact h1p
  have hlogAle : Real.log A ≤ Lq := by
    have hsumlog : Lq + Mc = Real.log (Q * ((Q - 1) / c)) := by
      rw [Real.log_mul (ne_of_gt hQ0) (by positivity), hLqdef, hMcdef]
    have hstep : (Q - 1) * (c * Mc) ≤ (Q - 1) * (Q * Lq) :=
      mul_le_mul_of_nonneg_left hcMc (le_of_lt hQm0)
    have hle : (Q - 1) * Mc / Lq ≤ Q * ((Q - 1) / c) := by
      rw [div_le_iff₀ hLq]
      have h6 : Q * ((Q - 1) / c) * Lq = (Q - 1) * (Q * Lq) / c := by field_simp
      rw [h6, le_div_iff₀ hc0]
      calc (Q - 1) * Mc * c = (Q - 1) * (c * Mc) := by ring
        _ ≤ (Q - 1) * (Q * Lq) := hstep
    have hlogle : Real.log ((Q - 1) * Mc / Lq) ≤ Lq + Mc := by
      rw [hsumlog]
      exact Real.log_le_log (by positivity) hle
    rw [hlogA, hcomb, hpq, h1peq, div_mul_eq_mul_div, div_le_iff₀ hsum]
    exact mul_le_mul_of_nonneg_left hlogle (le_of_lt hLq)
  refine ⟨1 - Real.log A / Lq, by
      have : Real.log A / Lq ≤ 1 := (div_le_one hLq).mpr hlogAle
      linarith, by
      have : 0 ≤ Real.log A / Lq := div_nonneg hlogAnn (le_of_lt hLq)
      linarith, ?_⟩
  have hQrpow : Q ^ (1 - (1 - Real.log A / Lq)) = A := by
    rw [show (1 : ℝ) - (1 - Real.log A / Lq) = Real.log A / Lq by ring,
      Real.rpow_def_of_pos hQ0, ← hLqdef,
      show Lq * (Real.log A / Lq) = Real.log A by field_simp]
    exact Real.exp_log hA0
  have hBrpow : (Q - 1) ^ (1 - Real.log A / Lq) * c ^ (1 - (1 - Real.log A / Lq)) = B := by
    rw [Real.rpow_def_of_pos hQm0, Real.rpow_def_of_pos hc0, ← Real.exp_add, ← Real.exp_log hB0]
    congr 1
    have hd : Lq * (Real.log A / Lq) = Real.log A := by field_simp
    have hratio' : p * Lq = (1 - p) * (Real.log (Q - 1) - Real.log c) := by
      rw [← hMcsplit]; exact hratio
    refine mul_left_cancel₀ hLqne ?_
    calc Lq * (Real.log (Q - 1) * (1 - Real.log A / Lq)
            + Real.log c * (1 - (1 - Real.log A / Lq)))
        = Lq * Real.log (Q - 1)
            - Lq * (Real.log A / Lq) * (Real.log (Q - 1) - Real.log c) := by ring
      _ = Lq * Real.log (Q - 1) - Real.log A * (Real.log (Q - 1) - Real.log c) := by rw [hd]
      _ = Lq * Real.log B := by
          rw [hlogA, hlogB]
          linear_combination (Real.log p - Real.log (1 - p) + Real.log (Q - 1)) * hratio'
  rw [hQrpow, hBrpow]
  exact hAB

/-! ### AVW Remark 5.1: the bound is at most `Q` -/

/-- AVW's exponent is positive as soon as `2 ≤ Q` and `0 < c < Q - 1`. -/
theorem splittingExponent_pos {Q c : ℝ} (hc0 : 0 < c) (hcQ : c < Q - 1) :
    0 < splittingExponent Q c := by
  have hLq : 0 < Real.log Q := Real.log_pos (by linarith)
  have hMc : 0 < Real.log ((Q - 1) / c) := Real.log_pos ((one_lt_div hc0).mpr hcQ)
  rw [splittingExponent]; positivity

/-- AVW's exponent is less than `1` as soon as `2 ≤ Q` and `0 < c < Q - 1`. -/
theorem splittingExponent_lt_one {Q c : ℝ} (hc0 : 0 < c) (hcQ : c < Q - 1) :
    splittingExponent Q c < 1 := by
  have hLq : 0 < Real.log Q := Real.log_pos (by linarith)
  have hMc : 0 < Real.log ((Q - 1) / c) := Real.log_pos ((one_lt_div hc0).mpr hcQ)
  rw [splittingExponent, div_lt_one (by linarith)]
  linarith

/-- The splitting bound written as a weighted geometric mean of `1/p` and `(Q-1)/(1-p)`. -/
private theorem splittingBound_eq_geomMean {Q c : ℝ} (hc0 : 0 < c) (hcQ : c < Q - 1) :
    splittingBound Q c = (splittingExponent Q c)⁻¹ ^ splittingExponent Q c *
      ((Q - 1) / (1 - splittingExponent Q c)) ^ (1 - splittingExponent Q c) := by
  rw [splittingBound, Real.inv_rpow (le_of_lt (splittingExponent_pos hc0 hcQ))]
  ring

/-- **AVW Remark 5.1**, in its non-strict form: the splitting bound never exceeds `Q`.

This is what makes Theorem 5.1 a barrier statement at all: `Ī(T) ≤ splittingBound Q c ≤ Q`
sharpens the trivial `Ī(T) ≤ |X|`.  Equality holds exactly when `p = 1/Q`, that is when
`c = (Q-1)/Q^{1/(Q-1)}`, the extreme case allowed by Theorem 5.1's hypothesis.

Proof: with `p = splittingExponent Q c`, the bound is the weighted geometric mean
`(1/p)^p · ((Q-1)/(1-p))^{1-p}`, which the weighted AM--GM inequality bounds by
`p·(1/p) + (1-p)·(Q-1)/(1-p) = 1 + (Q-1) = Q`. -/
theorem splittingBound_le {Q c : ℝ} (hc0 : 0 < c) (hcQ : c < Q - 1) :
    splittingBound Q c ≤ Q := by
  have hp0 := splittingExponent_pos hc0 hcQ
  have hp1 := splittingExponent_lt_one hc0 hcQ
  set p := splittingExponent Q c with hpdef
  have hpne : p ≠ 0 := ne_of_gt hp0
  have h1p : (1 : ℝ) - p ≠ 0 := by intro h; linarith [h]
  rw [splittingBound_eq_geomMean hc0 hcQ, ← hpdef]
  refine le_trans (Real.geom_mean_le_arith_mean2_weighted (le_of_lt hp0) (by linarith)
    (by positivity) (div_nonneg (by linarith) (by linarith)) (by ring)) (le_of_eq ?_)
  field_simp
  ring

/-- **AVW Remark 5.1**, strict form: the splitting bound is *strictly* less than `Q` unless
`p · Q = 1`.

AVW phrase the exceptional case as `c = (Q-1)/Q^{1/(Q-1)}`, which is indeed equivalent to
`p · Q = 1`; that equivalence is a computation with logarithms and is not formalized here, so the
hypothesis is stated on `p` directly. -/
theorem splittingBound_lt {Q c : ℝ} (hc0 : 0 < c) (hcQ : c < Q - 1)
    (hne : splittingExponent Q c * Q ≠ 1) : splittingBound Q c < Q := by
  have hp0 := splittingExponent_pos hc0 hcQ
  have hp1 := splittingExponent_lt_one hc0 hcQ
  set p := splittingExponent Q c with hpdef
  have hpne : p ≠ 0 := ne_of_gt hp0
  have h1p : (1 : ℝ) - p ≠ 0 := by intro h; linarith [h]
  have hne' : p⁻¹ ≠ (Q - 1) / (1 - p) := by
    intro h
    refine hne ?_
    rw [eq_div_iff h1p] at h
    have h2 : p * (p⁻¹ * (1 - p)) = p * (Q - 1) := by rw [h]
    rw [← mul_assoc, mul_inv_cancel₀ hpne, one_mul] at h2
    linear_combination -h2
  rw [splittingBound_eq_geomMean hc0 hcQ, ← hpdef]
  refine lt_of_lt_of_eq
    ((Real.geom_mean_lt_arith_mean2_weighted_iff_of_pos hp0 (by linarith)
      (by positivity) (div_nonneg (by linarith) (by linarith)) (by ring)).mpr hne') ?_
  field_simp
  ring

end ClosedForm

section TheoremFiveOne

variable {K : Type u} [CommSemiring K] {κ : Leg → Type v}
variable [∀ i, Fintype (κ i)] [∀ i, DecidableEq (κ i)]

/-- **AVW Theorem 5.1, the splitting bound.**  Let `T` be a coefficient table, `a` a variable of
leg `i₀` (AVW's `x₁ ∈ X`), and `B = T|_{X ∖ {x₁}}` the table obtained by zeroing out `a`.  Suppose

* at most `Q` terms of `T` use `a` (AVW: "`x₁` is in at most `q` terms in `T`");
* `T` uses at most `Q - 1` variables other than `a` on leg `i₀` (AVW: `|X| = q`);
* `c := Ī(B)` satisfies `0 < c ≤ (Q-1)/Q^{1/(Q-1)}`.

Then

```
Ī(T) ≤ ((Q-1)/(1-p))^{1-p} · p^{-p},   p = log((Q-1)/c) / (log Q + log((Q-1)/c)).
```

Two deliberate deviations from the letter of the source, both weakenings of the hypotheses.  AVW
require `|X| = q` exactly; only the two counts above are used, and both are stated with `≤`, on the
*minimal* leg sets of `Tensor/IndependenceMeasure.lean` rather than on the ambient variable type.
And `Q` is an arbitrary real with `2 ≤ Q`: nothing in the optimization uses integrality.

Proof: the one-parameter family `asymptoticIndependenceNumber_le_rpow_of_splitVariable`, evaluated
at the `θ` produced by `exists_rpow_add_eq_splittingBound`. -/
theorem asymptoticIndependenceNumber_le_splittingBound [NoZeroDivisors K] [Nontrivial K]
    {T : (∀ i, κ i) → K} {i₀ : Leg} {a : κ i₀} {Q c : ℝ} (hQ : 2 ≤ Q) (hc0 : 0 < c)
    (hm : ((coordinateSupport (coordinateFixVariable i₀ a T)).card : ℝ) ≤ Q)
    (hr : (((minimalLegSet T i₀).erase a).card : ℝ) ≤ Q - 1)
    (hB : asymptoticIndependenceNumber (coordinateEraseVariable i₀ a T) ≤ c)
    (hcq : c ≤ (Q - 1) / Q ^ (Q - 1)⁻¹) :
    asymptoticIndependenceNumber T ≤ splittingBound Q c := by
  obtain ⟨θ, hθ₀, hθ₁, hθ⟩ := exists_rpow_add_eq_splittingBound hQ hc0 hcq
  rw [← hθ]
  exact asymptoticIndependenceNumber_le_rpow_of_splitVariable (le_of_lt hc0) hθ₀ hθ₁ hm hr hB

/-! ### Numerical instances

The two certificates AVW use in the second proof of their Lemma 7.2 (Section 7.1), which is the
route to `ω_g(CW_q^σ) > 2` for `q ≥ 6`.  Both are stated here as instances of the *rational*
one-parameter bound: choosing `θ` rational turns each of them into a finite exact computation in
`ℚ`, with no logarithms and no floating point, at the cost of a slightly weaker constant than the
optimum of `splittingBound`.  The tensors themselves (the generalized Coppersmith--Winograd
tensor `CW_q^σ` and the intermediate `A`, `B` of AVW's proof) name a construction and belong to a
client module; only the counts enter here. -/

/-- A rational exponent bound: `x ^ (j/N) ≤ y` follows from the exact inequality `x^j ≤ y^N`. -/
private theorem rpow_le_of_pow_le_pow {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) {j N : ℕ} (hN : N ≠ 0)
    {e : ℝ} (he : e = (j : ℝ) / (N : ℝ)) (h : x ^ j ≤ y ^ N) : x ^ e ≤ y := by
  subst he
  refine le_of_pow_le_pow_left₀ hN hy ?_
  rw [← Real.rpow_natCast (x ^ ((j : ℝ) / (N : ℝ))) N, ← Real.rpow_mul hx,
    div_mul_cancel₀ _ (Nat.cast_ne_zero.mpr hN), Real.rpow_natCast]
  exact h

/-- **AVW's first numerical certificate** (Section 7.1, second proof of Lemma 7.2).  If at most
`7` terms of `T` use the leg-`i₀` variable `a`, `T` has at most `6` other leg-`i₀` variables, and
the table with `a` deleted has `Ī ≤ 1`, then `Ī(T) ≤ 5.08`.

AVW report the optimum of `splittingBound 7 1` as `5.07905`; the certificate below uses the
rational exponent `θ = 27/50` and the exact enclosures `7^{23/50} ≤ 2.4477` and
`6^{27/50} ≤ 2.6316`, which sum to `5.0793`. -/
theorem asymptoticIndependenceNumber_le_of_splitVariable_seven [NoZeroDivisors K] [Nontrivial K]
    {T : (∀ i, κ i) → K} {i₀ : Leg} {a : κ i₀}
    (hm : ((coordinateSupport (coordinateFixVariable i₀ a T)).card : ℝ) ≤ 7)
    (hr : (((minimalLegSet T i₀).erase a).card : ℝ) ≤ 6)
    (hB : asymptoticIndependenceNumber (coordinateEraseVariable i₀ a T) ≤ 1) :
    asymptoticIndependenceNumber T ≤ 5.08 := by
  refine le_trans (asymptoticIndependenceNumber_le_rpow_of_splitVariable (c := 1)
    (θ := 27 / 50) zero_le_one (by norm_num) (by norm_num) hm hr hB) ?_
  rw [Real.one_rpow, mul_one]
  have h1 : (7 : ℝ) ^ (1 - (27 : ℝ) / 50) ≤ 2.4477 :=
    rpow_le_of_pow_le_pow (by norm_num) (by norm_num) (j := 23) (N := 50) (by norm_num)
      (by norm_num) (by norm_num)
  have h2 : (6 : ℝ) ^ ((27 : ℝ) / 50) ≤ 2.6316 :=
    rpow_le_of_pow_le_pow (by norm_num) (by norm_num) (j := 27) (N := 50) (by norm_num)
      (by norm_num) (by norm_num)
  norm_num at h1 h2 ⊢
  linarith

/-- **AVW's second numerical certificate** (Section 7.1, second proof of Lemma 7.2), the one that
yields their headline `Ī(CW_6^σ) < 8`.  If at most `8` terms of `T` use the leg-`i₀` variable `a`,
`T` has at most `7` other leg-`i₀` variables, and the table with `a` deleted has `Ī ≤ 5.08`, then
`Ī(T) < 8`.

AVW report the optimum of `splittingBound 8 5.07905` as `7.9973`; the certificate below uses the
rational exponent `θ = 31/32` and the exact enclosures `8^{1/32} ≤ 1.06715`, `7^{31/32} ≤ 6.5871`
and `5.08^{1/32} ≤ 1.05211`, giving `1.06715 + 6.5871 · 1.05211 < 7.99751 < 8`. -/
theorem asymptoticIndependenceNumber_lt_eight_of_splitVariable [NoZeroDivisors K] [Nontrivial K]
    {T : (∀ i, κ i) → K} {i₀ : Leg} {a : κ i₀}
    (hm : ((coordinateSupport (coordinateFixVariable i₀ a T)).card : ℝ) ≤ 8)
    (hr : (((minimalLegSet T i₀).erase a).card : ℝ) ≤ 7)
    (hB : asymptoticIndependenceNumber (coordinateEraseVariable i₀ a T) ≤ 5.08) :
    asymptoticIndependenceNumber T < 8 := by
  refine lt_of_le_of_lt (asymptoticIndependenceNumber_le_rpow_of_splitVariable (c := 5.08)
    (θ := 31 / 32) (by norm_num) (by norm_num) (by norm_num) hm hr hB) ?_
  have h1 : (8 : ℝ) ^ (1 - (31 : ℝ) / 32) ≤ 1.06715 :=
    rpow_le_of_pow_le_pow (by norm_num) (by norm_num) (j := 1) (N := 32) (by norm_num)
      (by norm_num) (by norm_num)
  have h2 : (7 : ℝ) ^ ((31 : ℝ) / 32) ≤ 6.5871 :=
    rpow_le_of_pow_le_pow (by norm_num) (by norm_num) (j := 31) (N := 32) (by norm_num)
      (by norm_num) (by norm_num)
  have h3 : (5.08 : ℝ) ^ (1 - (31 : ℝ) / 32) ≤ 1.05211 :=
    rpow_le_of_pow_le_pow (by norm_num) (by norm_num) (j := 1) (N := 32) (by norm_num)
      (by norm_num) (by norm_num)
  have h2' : (0 : ℝ) ≤ (7 : ℝ) ^ ((31 : ℝ) / 32) := Real.rpow_nonneg (by norm_num) _
  have h3' : (0 : ℝ) ≤ (5.08 : ℝ) ^ (1 - (31 : ℝ) / 32) := Real.rpow_nonneg (by norm_num) _
  have hmul : (7 : ℝ) ^ ((31 : ℝ) / 32) * (5.08 : ℝ) ^ (1 - (31 : ℝ) / 32)
      ≤ 6.5871 * 1.05211 := mul_le_mul h2 h3 h3' (by norm_num)
  norm_num at h1 hmul ⊢
  linarith

end TheoremFiveOne

end AlgebraicComplexity.Tensor

