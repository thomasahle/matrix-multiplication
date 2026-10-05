/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.BilinearAlgorithm
import AlgebraicComplexity.Tensor.IndependenceNumber
import AlgebraicComplexity.Tensor.MonomialIndependence
import Mathlib.Data.Finset.NatAntidiagonal

/-!
# Strassen's weights and the independent diagonal of `⟨m,n,p⟩` (AVW Lemma 4.2)

This module is milestone **E** (finite half) of `BARRIER_FRAMEWORK.md`: the finite,
purely combinatorial content of

> J. Alman and V. Vassilevska Williams, *Limits on All Known (and Some Unknown) Approaches to
> Matrix Multiplication*, arXiv:1810.08671v1, **Lemma 4.2**.

## What Lemma 4.2 actually says, and what is proved here

AVW's statement is: *for positive integers `a, b, c` there is a monomial degeneration of
`⟨a,b,c⟩` into an independent tensor of size `(3/4)·abc/max{a,b,c}`.*  Their proof assigns
Strassen's weights

```text
α(x_{ij}) = i² + 2ij,   β(y_{jk}) = j² + 2jk,   γ(z_{ki}) = k² + 2ki
```

to the three legs, with the indices `i, j, k` running over ranges centred symmetrically about
`0`.  On a term `x_{ij} y_{jk} z_{ki}` the three weights sum to `(i+j+k)² ≥ 0`, so the tensor
`D` surviving the monomial degeneration is supported exactly on the *minimum-weight* triples
`{i + j + k = 0}`, and `D` is independent because any two of `i, j, k` determine the third.

The independent tensor is therefore `D`, **not** `⟨a,b,c⟩` itself: passing from `⟨a,b,c⟩` to `D`
deletes terms, which a zeroing out cannot do, and it is exactly the step for which AVW need a
monomial degeneration.  This distinction is not cosmetic.  The set of minimum-weight triples is
*not* an independent set of terms of `⟨a,b,c⟩`: the closure clause of `Tensor.IndependentSet`
fails already for `⟨3,3,3⟩`, and `not_independentSet_mmCoefficients_mmMinWeightSupport` proves
that failure.  Accordingly this file proves

* `independentSet_mmMinWeightSupport` — the minimum-weight level set is an independent set of
  terms of the minimum-weight coefficient table `mmMinWeightCoefficients`, verifying the three
  clauses of `Tensor.IndependentSet` directly; and
* `independenceNumber_mmMinWeightCoefficients` — in fact `I` of that table *equals* the size of
  the level set, since every independent set is contained in the support; together with
* `exists_three_mul_le_independenceNumber_mmMinWeight` — for suitable `s`,
  `3·m·n·p ≤ 4·I(D_s)·max{m,n,p}`, i.e. `I(D_s) ≥ (3/4)·mnp/max{m,n,p}`; and
* `independenceNumber_mmMinWeightCoefficients_le` — the trivial upper bound
  `I(D_s) ≤ min{mn, np, pm}` from `Tensor.independenceNumber_le_card`, sandwiching `I(D_s)`.

The monomial degeneration `⟨m,n,p⟩ ⟶ D_s` itself is deliberately **not** defined here: the
degeneration API (`Tensor.MonomialDegenerates`, `monomialDegenerates_fintype_sum_basis`) and the
`Ī`-monotonicity of AVW Lemma 4.3 / Corollary 4.2 are owned by the concurrent modules (C) of
`BARRIER_FRAMEWORK.md` §5.  What this file exports for them is the weight data itself —
`strassenWeightX/Y/Z` with `strassenWeight_add`, `strassenWeight_add_nonneg` and
`strassenWeight_add_eq_zero_iff` — which is a `ℤ`-valued leg weighting that is `≥ 0` on the whole
support of `⟨m,n,p⟩` and `= 0` exactly on `mmMinWeightSupport`.  That is literally the
combinatorial form of monomial degeneration recorded in `BARRIER_FRAMEWORK.md` §2.1 (the `ℕ`-valued
shift with a threshold `d` is a constant shift per leg, performed by the consumer).

## Feeding AVW Lemma 4.4

Lemma 4.4's single-copy form (`Ī(⟨a,b,c⟩) = abc/max{a,b,c}`) is proved in the final section of
this file, `Lemma44`, once `Ī` (`Tensor/AsymptoticIndependenceNumber.lean`) and Corollary 4.1
(`Tensor/MonomialIndependence.lean`) are available; the displayed `F`-copies form
`Ī(F ⊙ ⟨a,b,c⟩) = F·abc/max{a,b,c}` follows there from the coordinate-level block table of
`Tensor/IndependenceNumber.lean`.  The statements above are shaped so that Lemma 4.4 can
consume them verbatim: it needs, for a single `n`, a lower bound on `I` of a table reached from
`(F ⊙ ⟨a,b,c⟩)^{⊗n} ≅ Fⁿ ⊙ ⟨aⁿ,bⁿ,cⁿ⟩` by a monomial degeneration.  Applying
`exists_three_mul_le_independenceNumber_mmMinWeight` at `(aⁿ, bⁿ, cⁿ)` supplies exactly that
lower bound, in the multiplied-out `ℕ` form `3·mnp ≤ 4·I·max` that avoids any division, and
`independenceNumber_mmMinWeightCoefficients` even gives the exact value.

## Two honest deviations from the paper, recorded

1. **Generality of the dimensions.**  AVW prove the case `a = 2m+1, b = 2n+1, c = 2p+1` all odd
   and write "the cases where `a, b, c` are not all odd are similar".  Here the *general* case is
   proved, with the *same* constant `3/4` and no parity hypothesis, by working in the repository's
   `Fin`-based `MMIndex` coordinates and taking the minimum-weight set to be a level set
   `{i + j + k = s}` for an optimally chosen level `s : ℕ` rather than insisting on the level `0`
   of a symmetric centring.  Recentring is an affine renaming of indices, and choosing `s` is what
   replaces it: for `s = 0` the weights below are literally AVW's, and for general `s` they are
   AVW's weights translated so that the level set `{i+j+k = s}` is the zero set.  No monotonicity
   argument and no weakened constant are needed.
2. **Which tensor carries the independent set.**  As explained above, the independent set is a set
   of terms of the minimum-weight table, not of `⟨m,n,p⟩`; the counterexample is proved.

## The lattice-point count

The counting heart of the lemma — AVW's "there are at least `(3/4)ab` pairs `(i,j)` with
`|i+j| ≤ p`" — is isolated in the `SumLevel` namespace as a standalone statement about `ℕ × ℕ`
(`SumLevel.exists_three_mul_le_card_band`), with no tensor content.  It is a plausible future
citizen of `AlgebraicComplexity/Combinatorics/`; it is kept here for now because nothing else
consumes it and `DESIGN.md` prefers adding a leaf to refactoring shared foundations during
parallel work.  The boundary care AVW gloss over is where the constant `3/4` comes from: the
pairs missed by the best window of `w ≥ max{u,v}` consecutive values of `x + y` form two corner
triangles whose leg lengths add up to `d = u + v - 1 - w ≤ min{u,v} - 1`, so splitting `d` as
evenly as possible the missed count is at most `(d+1)²/4 ≤ min{u,v}²/4 ≤ uv/4`.
-/

namespace AlgebraicComplexity

open Tensor

universe u

/-! ### The lattice-point count

Everything in this section is elementary counting in `ℕ × ℕ` and `ℕ × ℕ × ℕ`; no tensor,
coefficient table or matrix-multiplication notion appears. -/

namespace SumLevel

/-- The **band** of the rectangle `[0,u) × [0,v)` cut out by the `w` consecutive values
`s - w + 1, …, s` of the coordinate sum: the pairs `(x, y)` with `x + y ≤ s < x + y + w`.

This is the fibre count of a level set of a triple sum: `(x, y)` lies in the band exactly when
the third coordinate `z := s - x - y` forced by `x + y + z = s` satisfies `0 ≤ z < w`. -/
def band (u v w s : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range u ×ˢ Finset.range v).filter fun q ↦ q.1 + q.2 ≤ s ∧ s < q.1 + q.2 + w

@[simp] theorem mem_band {u v w s : ℕ} {q : ℕ × ℕ} :
    q ∈ band u v w s ↔ q.1 < u ∧ q.2 < v ∧ q.1 + q.2 ≤ s ∧ s < q.1 + q.2 + w := by
  simp only [band, Finset.mem_filter, Finset.mem_product, Finset.mem_range, and_assoc]

/-- The Gauss sum in the form used below: `2·(1 + 2 + ⋯ + c) = c·(c+1)`. -/
private theorem two_mul_sum_range_succ (c : ℕ) :
    2 * ∑ t ∈ Finset.range c, (t + 1) = c * (c + 1) := by
  induction c with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, Nat.mul_add, ih]
    ring

/-- **Triangle bound.**  A finite set of pairs of natural numbers whose coordinate sums are all
`< c` has at most `c(c+1)/2` elements, stated without division as `2·|A| ≤ c(c+1)`.

Proof sketch: `A` is contained in the union over `t < c` of the antidiagonals `{x + y = t}`, and
the `t`-th antidiagonal has `t + 1` elements. -/
theorem two_mul_card_le_of_add_lt {A : Finset (ℕ × ℕ)} {c : ℕ}
    (h : ∀ q ∈ A, q.1 + q.2 < c) : 2 * A.card ≤ c * (c + 1) := by
  classical
  have hsub : A ⊆ (Finset.range c).biUnion fun t ↦ Finset.antidiagonal t := by
    intro q hq
    simp only [Finset.mem_biUnion, Finset.mem_range, Finset.mem_antidiagonal]
    exact ⟨q.1 + q.2, h q hq, rfl⟩
  have hcard : A.card ≤ ∑ t ∈ Finset.range c, (t + 1) := by
    refine le_trans (Finset.card_le_card hsub) (le_trans Finset.card_biUnion_le (le_of_eq ?_))
    exact Finset.sum_congr rfl fun t _ ↦ Finset.Nat.card_antidiagonal t
  calc 2 * A.card ≤ 2 * ∑ t ∈ Finset.range c, (t + 1) := Nat.mul_le_mul_left 2 hcard
    _ = c * (c + 1) := two_mul_sum_range_succ c

/-- **The lattice-point count behind AVW Lemma 4.2.**  If the window length `w` is at least both
side lengths `u` and `v`, then some window of `w` consecutive coordinate sums catches at least
three quarters of the rectangle `[0,u) × [0,v)`, stated without division as
`3·u·v ≤ 4·|band u v w s|`.

In AVW's centred notation with `u = a`, `v = b` and `w = c = max{a,b,c}` this is the assertion
that there are at least `(3/4)ab` pairs `(i,j)` with `|i + j| ≤ p`.

Proof sketch: put `d := u + v - 1 - w`, the number of coordinate sums the window has to miss, and
split it as evenly as possible, `L := ⌈d/2⌉` sums missed below and `R := ⌊d/2⌋ ` above, i.e.
`s := L + w - 1`.  The missed pairs below form the triangle `{x + y < L}` and the missed pairs
above are carried by the reflection `(x, y) ↦ (u-1-x, v-1-y)` into the triangle `{x + y < R}`, so
by `two_mul_card_le_of_add_lt` four times the number of missed pairs is at most
`2L(L+1) + 2R(R+1) = (d+1)²` up to one unit, and `d + 1 ≤ min{u,v}` because `w ≥ max{u,v}`.  Hence
the missed pairs number at most `uv/4`. -/
theorem exists_three_mul_le_card_band (u v w : ℕ) (hu : u ≤ w) (hv : v ≤ w) :
    ∃ s, 3 * (u * v) ≤ 4 * (band u v w s).card := by
  classical
  -- Degenerate rectangles are trivial.
  rcases Nat.eq_zero_or_pos u with rfl | hupos
  · exact ⟨0, by simp⟩
  rcases Nat.eq_zero_or_pos v with rfl | hvpos
  · exact ⟨0, by simp⟩
  have hwpos : 0 < w := lt_of_lt_of_le hupos hu
  -- Opaque names for the window data, so that `omega` can reason about them.
  obtain ⟨d, hd⟩ : ∃ d, d = u + v - 1 - w := ⟨_, rfl⟩
  obtain ⟨L, hL⟩ : ∃ L, L = (d + 1) / 2 := ⟨_, rfl⟩
  obtain ⟨R, hR⟩ : ∃ R, R = d / 2 := ⟨_, rfl⟩
  obtain ⟨s, hs⟩ : ∃ s, s = L + w - 1 := ⟨_, rfl⟩
  refine ⟨s, ?_⟩
  set rect : Finset (ℕ × ℕ) := Finset.range u ×ˢ Finset.range v with hrect
  set P : ℕ × ℕ → Prop := fun q ↦ q.1 + q.2 ≤ s with hP
  set Q : ℕ × ℕ → Prop := fun q ↦ s < q.1 + q.2 + w with hQ
  have hmemrect : ∀ q ∈ rect, q.1 < u ∧ q.2 < v := by
    intro q hq
    simpa [hrect, Finset.mem_product, Finset.mem_range] using hq
  -- The rectangle splits into the band and the two corner triangles.
  have hcardrect : rect.card = u * v := by simp [hrect]
  have hband : rect.filter (fun q ↦ P q ∧ Q q) = band u v w s := by
    simp [band, hrect, hP, hQ]
  have hlowfilter : (rect.filter P).filter (fun q ↦ ¬ Q q) = rect.filter (fun q ↦ ¬ Q q) := by
    rw [Finset.filter_filter]
    refine Finset.filter_congr fun q _ ↦ ?_
    simp only [hP, hQ, and_iff_right_iff_imp]
    omega
  have hsplit :
      (band u v w s).card + (rect.filter (fun q ↦ ¬ Q q)).card
        + (rect.filter (fun q ↦ ¬ P q)).card = u * v := by
    have h1 := Finset.card_filter_add_card_filter_not (s := rect) P
    have h2 := Finset.card_filter_add_card_filter_not (s := rect.filter P) Q
    rw [Finset.filter_filter, hband, hlowfilter] at h2
    omega
  -- The lower corner triangle.
  have hlow : 2 * (rect.filter (fun q ↦ ¬ Q q)).card ≤ L * (L + 1) := by
    refine two_mul_card_le_of_add_lt fun q hq ↦ ?_
    rw [Finset.mem_filter] at hq
    have := hmemrect q hq.1
    have hq2 := hq.2
    simp only [hQ, not_lt] at hq2
    omega
  -- The upper corner triangle, via the reflection of the rectangle.
  have hhigh : 2 * (rect.filter (fun q ↦ ¬ P q)).card ≤ R * (R + 1) := by
    set f : ℕ × ℕ → ℕ × ℕ := fun q ↦ (u - 1 - q.1, v - 1 - q.2) with hf
    have hinj : Set.InjOn f (rect.filter (fun q ↦ ¬ P q)) := by
      intro q hq q' hq' hqq'
      rw [Finset.mem_coe, Finset.mem_filter] at hq hq'
      have h1 := hmemrect q hq.1
      have h2 := hmemrect q' hq'.1
      have e1 : u - 1 - q.1 = u - 1 - q'.1 := congrArg Prod.fst hqq'
      have e2 : v - 1 - q.2 = v - 1 - q'.2 := congrArg Prod.snd hqq'
      have : q.1 = q'.1 := by omega
      have : q.2 = q'.2 := by omega
      exact Prod.ext (by omega) (by omega)
    rw [← Finset.card_image_of_injOn hinj]
    refine two_mul_card_le_of_add_lt fun q hq ↦ ?_
    rw [Finset.mem_image] at hq
    obtain ⟨q', hq', rfl⟩ := hq
    rw [Finset.mem_filter] at hq'
    have := hmemrect q' hq'.1
    have hq'2 := hq'.2
    simp only [hP, not_le] at hq'2
    simp only [hf]
    omega
  -- The two triangles together miss at most a quarter of the rectangle.
  have hquad : 2 * (L * (L + 1)) + 2 * (R * (R + 1)) ≤ (d + 1) * (d + 1) := by
    rcases Nat.even_or_odd d with ⟨e, he⟩ | ⟨e, he⟩
    · have hLe : L = e := by omega
      have hRe : R = e := by omega
      have hexp : (d + 1) * (d + 1) = 2 * (e * (e + 1)) + 2 * (e * (e + 1)) + 1 := by
        subst he; ring
      rw [hLe, hRe]
      omega
    · have hLe : L = e + 1 := by omega
      have hRe : R = e := by omega
      have hexp : (d + 1) * (d + 1) = 2 * ((e + 1) * (e + 1 + 1)) + 2 * (e * (e + 1)) := by
        subst he; ring
      rw [hLe, hRe]
      omega
  have hdu : d + 1 ≤ u := by omega
  have hdv : d + 1 ≤ v := by omega
  have hsq : (d + 1) * (d + 1) ≤ u * v := Nat.mul_le_mul hdu hdv
  have hmiss :
      4 * ((rect.filter (fun q ↦ ¬ Q q)).card + (rect.filter (fun q ↦ ¬ P q)).card) ≤ u * v := by
    calc 4 * ((rect.filter (fun q ↦ ¬ Q q)).card + (rect.filter (fun q ↦ ¬ P q)).card)
        = 2 * (2 * (rect.filter (fun q ↦ ¬ Q q)).card)
            + 2 * (2 * (rect.filter (fun q ↦ ¬ P q)).card) := by ring
      _ ≤ 2 * (L * (L + 1)) + 2 * (R * (R + 1)) :=
          Nat.add_le_add (Nat.mul_le_mul_left 2 hlow) (Nat.mul_le_mul_left 2 hhigh)
      _ ≤ (d + 1) * (d + 1) := hquad
      _ ≤ u * v := hsq
  obtain ⟨N, hN⟩ : ∃ N, N = u * v := ⟨_, rfl⟩
  rw [← hN]
  rw [← hN] at hsplit hmiss
  omega

/-- The level set of the coordinate sum inside a box of natural numbers: the triples
`(x, y, z)` with `x < m`, `y < n`, `z < p` and `x + y + z = s`.  It is the index set of the
minimum-weight sub-support of `⟨m,n,p⟩`, transported to raw natural-number coordinates. -/
def natTripleLevel (m n p s : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  (Finset.range m ×ˢ Finset.range n ×ˢ Finset.range p).filter
    fun t ↦ t.1 + t.2.1 + t.2.2 = s

@[simp] theorem mem_natTripleLevel {m n p s : ℕ} {t : ℕ × ℕ × ℕ} :
    t ∈ natTripleLevel m n p s ↔
      t.1 < m ∧ t.2.1 < n ∧ t.2.2 < p ∧ t.1 + t.2.1 + t.2.2 = s := by
  simp only [natTripleLevel, Finset.mem_filter, Finset.mem_product, Finset.mem_range, and_assoc]

/-- The level set is counted by the band of its first two coordinates: the third coordinate is
determined by the other two. -/
theorem card_natTripleLevel (m n p s : ℕ) :
    (natTripleLevel m n p s).card = (band m n p s).card := by
  refine Finset.card_nbij' (fun t ↦ (t.1, t.2.1)) (fun q ↦ (q.1, q.2, s - q.1 - q.2))
    ?_ ?_ ?_ ?_
  · intro t ht
    rw [Finset.mem_coe, mem_natTripleLevel] at ht
    simp only [Finset.mem_coe, mem_band]
    omega
  · intro q hq
    rw [Finset.mem_coe, mem_band] at hq
    simp only [Finset.mem_coe, mem_natTripleLevel]
    omega
  · intro t ht
    rw [Finset.mem_coe, mem_natTripleLevel] at ht
    obtain ⟨x, y, z⟩ := t
    simp only at ht ⊢
    have : s - x - y = z := by omega
    rw [this]
  · intro q hq
    rfl

/-- The level set count is invariant under cyclically rotating the three side lengths. -/
theorem card_natTripleLevel_rotate (m n p s : ℕ) :
    (natTripleLevel m n p s).card = (natTripleLevel n p m s).card := by
  refine Finset.card_nbij' (fun t ↦ (t.2.1, t.2.2, t.1)) (fun t ↦ (t.2.2, t.1, t.2.1))
    ?_ ?_ ?_ ?_
  · intro t ht
    rw [Finset.mem_coe, mem_natTripleLevel] at ht
    simp only [Finset.mem_coe, mem_natTripleLevel]
    omega
  · intro t ht
    rw [Finset.mem_coe, mem_natTripleLevel] at ht
    simp only [Finset.mem_coe, mem_natTripleLevel]
    omega
  · intro t _
    rfl
  · intro t _
    rfl

/-- **Three quarters of the box lies on one level.**  For all side lengths there is a level `s`
with `3·m·n·p ≤ 4·|natTripleLevel m n p s|·max{m,n,p}`, that is,
`|natTripleLevel m n p s| ≥ (3/4)·mnp/max{m,n,p}`.

Proof sketch: rotate the three side lengths cyclically until the largest is last, so that the
level set is counted by a band of window length `max{m,n,p}` over the other two sides, and apply
`exists_three_mul_le_card_band`; multiplying the resulting inequality
`3·(product of the two smaller sides) ≤ 4·|level set|` by the largest side gives the claim. -/
theorem exists_three_mul_le_card_natTripleLevel (m n p : ℕ) :
    ∃ s, 3 * (m * n * p) ≤ 4 * (natTripleLevel m n p s).card * max m (max n p) := by
  have key : ∀ x y z : ℕ, x ≤ z → y ≤ z →
      ∃ s, 3 * (x * y) ≤ 4 * (natTripleLevel x y z s).card := by
    intro x y z hx hy
    obtain ⟨s, hs⟩ := exists_three_mul_le_card_band x y z hx hy
    exact ⟨s, by rw [card_natTripleLevel]; exact hs⟩
  rcases le_total n p with hnp | hpn
  · rcases le_total m p with hmp | hpm
    · -- `p` is the largest side.
      obtain ⟨s, hs⟩ := key m n p hmp hnp
      refine ⟨s, ?_⟩
      have hmax : max m (max n p) = p := by omega
      rw [hmax]
      calc 3 * (m * n * p) = 3 * (m * n) * p := by ring
        _ ≤ 4 * (natTripleLevel m n p s).card * p := Nat.mul_le_mul_right p hs
    · -- `m` is the largest side.
      obtain ⟨s, hs⟩ := key n p m (le_trans hnp hpm) hpm
      refine ⟨s, ?_⟩
      have hmax : max m (max n p) = m := by omega
      rw [hmax, card_natTripleLevel_rotate m n p s]
      calc 3 * (m * n * p) = 3 * (n * p) * m := by ring
        _ ≤ 4 * (natTripleLevel n p m s).card * m := Nat.mul_le_mul_right m hs
  · rcases le_total m n with hmn | hnm
    · -- `n` is the largest side.
      obtain ⟨s, hs⟩ := key p m n hpn hmn
      refine ⟨s, ?_⟩
      have hmax : max m (max n p) = n := by omega
      rw [hmax, card_natTripleLevel_rotate m n p s, card_natTripleLevel_rotate n p m s]
      calc 3 * (m * n * p) = 3 * (p * m) * n := by ring
        _ ≤ 4 * (natTripleLevel p m n s).card * n := Nat.mul_le_mul_right n hs
    · -- `m` is the largest side.
      obtain ⟨s, hs⟩ := key n p m hnm (le_trans hpn hnm)
      refine ⟨s, ?_⟩
      have hmax : max m (max n p) = m := by omega
      rw [hmax, card_natTripleLevel_rotate m n p s]
      calc 3 * (m * n * p) = 3 * (n * p) * m := by ring
        _ ≤ 4 * (natTripleLevel n p m s).card * m := Nat.mul_le_mul_right m hs

end SumLevel

/-! ### The coefficient table of `⟨m,n,p⟩` and its minimum-weight sub-support -/

section Tables

variable {K : Type u} [CommSemiring K]

/-- The index triple of `⟨m,n,p⟩` selected by the summation indices `(i, j, k)`: the `X`-variable
`x_{ij}`, the `Y`-variable `y_{jk}` and the `Z`-variable `z_{ki}`.  It is the index-level
counterpart of `mmTerm`. -/
def mmIndexOfTriple (m n p : ℕ) (i : Fin m) (j : Fin n) (k : Fin p) : ∀ c, MMIndex m n p c
  | .X => (i, j)
  | .Y => (j, k)
  | .Z => (k, i)

@[simp] theorem mmCompatible_mmIndexOfTriple {m n p : ℕ} (i : Fin m) (j : Fin n) (k : Fin p) :
    MMCompatible (mmIndexOfTriple m n p i j k) :=
  ⟨rfl, rfl, rfl⟩

/-- The **level** of an index triple: the sum `i + j + k` of its three summation indices, read off
the `X` and `Y` legs.  On the support of `⟨m,n,p⟩` all three legs agree about `i`, `j` and `k`, so
this is the symmetric quantity `i + j + k`. -/
def mmLevel {m n p : ℕ} (a : ∀ c, MMIndex m n p c) : ℕ :=
  (a .X).1.val + (a .X).2.val + (a .Y).2.val

@[simp] theorem mmLevel_mmIndexOfTriple {m n p : ℕ} (i : Fin m) (j : Fin n) (k : Fin p) :
    mmLevel (mmIndexOfTriple m n p i j k) = i.val + j.val + k.val :=
  rfl

/-- A term of `⟨m,n,p⟩` is determined by its three summation indices: two compatible index triples
agreeing in `i`, `j` and `k` are equal. -/
theorem mmIndex_ext {m n p : ℕ} {a b : ∀ c, MMIndex m n p c}
    (ha : MMCompatible a) (hb : MMCompatible b)
    (h1 : (a .X).1 = (b .X).1) (h2 : (a .X).2 = (b .X).2) (h3 : (a .Y).2 = (b .Y).2) :
    a = b := by
  obtain ⟨ha1, ha2, ha3⟩ := ha
  obtain ⟨hb1, hb2, hb3⟩ := hb
  funext c
  cases c
  · exact Prod.ext h1 h2
  · exact Prod.ext (by rw [← ha1, ← hb1, h2]) h3
  · exact Prod.ext (by rw [← ha2, ← hb2, h3]) (by rw [ha3, hb3]; exact h1)

/-- The `val`-level form of `mmIndex_ext`. -/
theorem mmIndex_ext_val {m n p : ℕ} {a b : ∀ c, MMIndex m n p c}
    (ha : MMCompatible a) (hb : MMCompatible b)
    (h1 : (a .X).1.val = (b .X).1.val) (h2 : (a .X).2.val = (b .X).2.val)
    (h3 : (a .Y).2.val = (b .Y).2.val) : a = b :=
  mmIndex_ext ha hb (Fin.ext h1) (Fin.ext h2) (Fin.ext h3)

/-- **The coefficient table of `⟨m,n,p⟩`**: the indicator of `MMCompatible`, i.e. the coefficient
`1` on the terms `x_{ij} y_{jk} z_{ki}` and `0` elsewhere.  This is the shape the independence
number API of `Tensor/IndependenceNumber.lean` consumes, and it is the uncurried form of `mmCoeff`
(`mmCoefficients_apply`). -/
def mmCoefficients (K : Type u) [CommSemiring K] (m n p : ℕ) : (∀ c, MMIndex m n p c) → K :=
  fun a ↦ if MMCompatible a then 1 else 0

/-- The bridge to the bilinear-algorithm coefficient array: `mmCoefficients` is `mmCoeff` with the
three leg indices bundled into one function on `Leg`. -/
theorem mmCoefficients_apply (m n p : ℕ) (a : ∀ c, MMIndex m n p c) :
    mmCoefficients K m n p a = mmCoeff (K := K) m n p (a .X) (a .Y) (a .Z) := rfl

/-- The abstract tensor of the coefficient table `mmCoefficients` is `⟨m,n,p⟩`, so all statements
below about `mmCoefficients` really are statements about `matrixMultiplication`. -/
theorem coordinateTensor_mmCoefficients (m n p : ℕ) :
    coordinateTensor (mmCoefficients K m n p) = matrixMultiplication (K := K) m n p := by
  refine standardCoordinate_ext (K := K) (κ := MMIndex m n p) fun a ↦ ?_
  rw [standardCoordinateEquiv_coordinateTensor, standardCoordinateEquiv_matrixMultiplication]
  rfl

/-- Reindex the coordinates of a matrix-multiplication tensor along equalities of its three
dimensions. -/
def mmIndexCongr {m n p m' n' p' : ℕ} (hm : m = m') (hn : n = n') (hp : p = p') :
    ∀ c, MMIndex m n p c ≃ MMIndex m' n' p' c
  | .X => Equiv.prodCongr (finCongr hm) (finCongr hn)
  | .Y => Equiv.prodCongr (finCongr hn) (finCongr hp)
  | .Z => Equiv.prodCongr (finCongr hp) (finCongr hm)

/-- Reindexing along equalities of the dimensions does not change the coefficient table. -/
theorem mmCoefficients_mmIndexCongr {m n p m' n' p' : ℕ} (hm : m = m') (hn : n = n')
    (hp : p = p') (u : ∀ c, MMIndex m n p c) :
    mmCoefficients K m' n' p' (fun c ↦ mmIndexCongr hm hn hp c (u c))
      = mmCoefficients K m n p u := by
  subst hm
  subst hn
  subst hp
  congr 1
  funext c
  cases c <;> simp [mmIndexCongr]

/-- **The minimum-weight sub-support of `⟨m,n,p⟩` at level `s`**: the terms
`x_{ij} y_{jk} z_{ki}` with `i + j + k = s`.  By `strassenWeight_add_eq_zero_iff` this is exactly
the set of terms of minimum total Strassen weight, hence the support of the tensor `D` produced by
AVW's monomial degeneration (Lemma 4.2). -/
def mmMinWeightSupport (m n p s : ℕ) : Finset (∀ c, MMIndex m n p c) :=
  Finset.univ.filter fun a ↦ MMCompatible a ∧ mmLevel a = s

@[simp] theorem mem_mmMinWeightSupport {m n p s : ℕ} {a : ∀ c, MMIndex m n p c} :
    a ∈ mmMinWeightSupport m n p s ↔ MMCompatible a ∧ mmLevel a = s := by
  simp [mmMinWeightSupport]

/-- **The coefficient table of the minimum-weight sub-tensor `D`** of `⟨m,n,p⟩` at level `s`: the
indicator of `mmMinWeightSupport`.  It is a sub-tensor of `mmCoefficients` in the sense of AVW
Section 3.1.2, obtained from it by *deleting* terms — an operation available to a monomial
degeneration but not to a zeroing out. -/
def mmMinWeightCoefficients (K : Type u) [CommSemiring K] (m n p s : ℕ) :
    (∀ c, MMIndex m n p c) → K :=
  fun a ↦ if MMCompatible a ∧ mmLevel a = s then 1 else 0

/-- The support of the minimum-weight table is `mmMinWeightSupport`. -/
theorem mmMinWeightCoefficients_ne_zero_iff [Nontrivial K] {m n p s : ℕ}
    {a : ∀ c, MMIndex m n p c} :
    mmMinWeightCoefficients K m n p s a ≠ 0 ↔ a ∈ mmMinWeightSupport m n p s := by
  rw [mem_mmMinWeightSupport, mmMinWeightCoefficients]
  split_ifs with h
  · exact iff_of_true one_ne_zero h
  · simp [h]

/-- The minimum-weight table is a sub-tensor of the table of `⟨m,n,p⟩`: every term of the former
is a term of the latter, with the same coefficient. -/
theorem mmMinWeightCoefficients_eq_of_ne_zero [Nontrivial K] {m n p s : ℕ}
    {a : ∀ c, MMIndex m n p c} (h : mmMinWeightCoefficients K m n p s a ≠ 0) :
    mmMinWeightCoefficients K m n p s a = mmCoefficients K m n p a := by
  rw [mmMinWeightCoefficients_ne_zero_iff, mem_mmMinWeightSupport] at h
  simp [mmMinWeightCoefficients, mmCoefficients, h.2]

end Tables

/-! ### Strassen's weights

The `ℤ`-valued leg weights of AVW Lemma 4.2, translated so that the level set `{i + j + k = s}` is
the zero set.  At `s = 0` they are literally AVW's `α(x_{ij}) = i² + 2ij`, `β(y_{jk}) = j² + 2jk`,
`γ(z_{ki}) = k² + 2ki`.

These are exported as data for the monomial-degeneration module (`BARRIER_FRAMEWORK.md` §5 (C));
no degeneration relation is defined here. -/

section StrassenWeights

variable {m n p : ℕ}

/-- Strassen's `X`-leg weight `α(x_{ij}) = i² + 2ij - 2si + s²`. -/
def strassenWeightX (s : ℕ) (x : MMIndex m n p .X) : ℤ :=
  (x.1.val : ℤ) ^ 2 + 2 * (x.1.val : ℤ) * (x.2.val : ℤ) - 2 * (s : ℤ) * (x.1.val : ℤ) + (s : ℤ) ^ 2

/-- Strassen's `Y`-leg weight `β(y_{jk}) = j² + 2jk - 2sj`. -/
def strassenWeightY (s : ℕ) (y : MMIndex m n p .Y) : ℤ :=
  (y.1.val : ℤ) ^ 2 + 2 * (y.1.val : ℤ) * (y.2.val : ℤ) - 2 * (s : ℤ) * (y.1.val : ℤ)

/-- Strassen's `Z`-leg weight `γ(z_{ki}) = k² + 2ki - 2sk`. -/
def strassenWeightZ (s : ℕ) (z : MMIndex m n p .Z) : ℤ :=
  (z.1.val : ℤ) ^ 2 + 2 * (z.1.val : ℤ) * (z.2.val : ℤ) - 2 * (s : ℤ) * (z.1.val : ℤ)

/-- **The Strassen weight identity.**  On a term `x_{ij} y_{jk} z_{ki}` of `⟨m,n,p⟩` the three leg
weights sum to the perfect square `(i + j + k - s)²`.

Proof sketch: substitute the compatibility equations, so that the three leg weights are functions
of `i`, `j`, `k` alone, and expand: the quadratic terms assemble into `(i+j+k)²`, the linear terms
into `-2s(i+j+k)` and the constant is `s²`. -/
theorem strassenWeight_add (s : ℕ) {a : ∀ c, MMIndex m n p c} (h : MMCompatible a) :
    strassenWeightX s (a .X) + strassenWeightY s (a .Y) + strassenWeightZ s (a .Z)
      = ((mmLevel a : ℤ) - (s : ℤ)) ^ 2 := by
  obtain ⟨h1, h2, h3⟩ := h
  simp only [strassenWeightX, strassenWeightY, strassenWeightZ, mmLevel, ← h1, ← h2, ← h3]
  push_cast
  ring

/-- Strassen's weights are nonnegative on the whole support of `⟨m,n,p⟩`: this is the inequality
`a + b + c ≥ 0` required of a monomial degeneration. -/
theorem strassenWeight_add_nonneg (s : ℕ) {a : ∀ c, MMIndex m n p c} (h : MMCompatible a) :
    0 ≤ strassenWeightX s (a .X) + strassenWeightY s (a .Y) + strassenWeightZ s (a .Z) := by
  rw [strassenWeight_add s h]
  positivity

/-- Strassen's weights vanish exactly on the level set `{i + j + k = s}`: this is the equality
`a + b + c = 0` characterizing the surviving terms of a monomial degeneration, and it identifies
`mmMinWeightSupport` as the minimum-weight sub-support. -/
theorem strassenWeight_add_eq_zero_iff (s : ℕ) {a : ∀ c, MMIndex m n p c} (h : MMCompatible a) :
    strassenWeightX s (a .X) + strassenWeightY s (a .Y) + strassenWeightZ s (a .Z) = 0 ↔
      mmLevel a = s := by
  rw [strassenWeight_add s h, sq_eq_zero_iff, sub_eq_zero, Nat.cast_inj]

end StrassenWeights

/-! ### The independent set (AVW Lemma 4.2) -/

section Independence

variable {K : Type u} [CommSemiring K]

/-- **AVW Lemma 4.2, the independence clause.**  The minimum-weight level set is an independent
set of terms of the minimum-weight table `D`.

All three clauses of `Tensor.IndependentSet` are checked directly:

* *support membership*: the coefficient of a level triple is `1`;
* *pairwise distinct coordinates*: two level triples sharing a variable on some leg share two of
  the three summation indices `i`, `j`, `k`, and `i + j + k = s` then forces the third to agree,
  so the triples are equal (`mmIndex_ext_val`);
* *closure*: every term of `D` lies in the level set by construction, so the clause is vacuous.

The closure clause is exactly where `⟨m,n,p⟩` itself would fail — see
`not_independentSet_mmCoefficients_mmMinWeightSupport`. -/
theorem independentSet_mmMinWeightSupport [Nontrivial K] (m n p s : ℕ) :
    IndependentSet (mmMinWeightCoefficients K m n p s) (mmMinWeightSupport m n p s) where
  ne_zero _ ha := mmMinWeightCoefficients_ne_zero_iff.mpr ha
  distinct a ha b hb c hc := by
    rw [mem_mmMinWeightSupport] at ha hb
    obtain ⟨hca, hla⟩ := ha
    obtain ⟨hcb, hlb⟩ := hb
    simp only [mmLevel] at hla hlb
    cases c with
    | X =>
      have h1 : (a .X).1.val = (b .X).1.val := by rw [hc]
      have h2 : (a .X).2.val = (b .X).2.val := by rw [hc]
      exact mmIndex_ext_val hca hcb h1 h2 (by omega)
    | Y =>
      have h2 : (a .X).2.val = (b .X).2.val := by
        rw [hca.1, hcb.1, hc]
      have h3 : (a .Y).2.val = (b .Y).2.val := by rw [hc]
      exact mmIndex_ext_val hca hcb (by omega) h2 h3
    | Z =>
      have h1 : (a .X).1.val = (b .X).1.val := by
        rw [← hca.2.2, ← hcb.2.2, hc]
      have h3 : (a .Y).2.val = (b .Y).2.val := by
        rw [hca.2.1, hcb.2.1, hc]
      exact mmIndex_ext_val hca hcb h1 (by omega) h3
  closed _ hne _ := mmMinWeightCoefficients_ne_zero_iff.mp hne

/-- **The independence number of the minimum-weight table is the size of the level set.**  The
lower bound is the independent set above; the upper bound holds because every independent set of
terms is contained in the support, which *is* the level set. -/
theorem independenceNumber_mmMinWeightCoefficients [Nontrivial K] (m n p s : ℕ) :
    independenceNumber (mmMinWeightCoefficients K m n p s)
      = (mmMinWeightSupport m n p s).card := by
  refine le_antisymm (independenceNumber_le fun S hS ↦ ?_)
    (independentSet_mmMinWeightSupport (K := K) m n p s).card_le_independenceNumber
  exact Finset.card_le_card fun a ha ↦ mmMinWeightCoefficients_ne_zero_iff.mp (hS.ne_zero a ha)

/-- The minimum-weight support is counted by the natural-number level set: a term is determined by
its three summation indices `(i, j, k)`, which range over the box `[0,m) × [0,n) × [0,p)`. -/
theorem card_mmMinWeightSupport (m n p s : ℕ) :
    (mmMinWeightSupport m n p s).card = (SumLevel.natTripleLevel m n p s).card := by
  refine Finset.card_bij (fun a _ ↦ ((a .X).1.val, (a .X).2.val, (a .Y).2.val)) ?_ ?_ ?_
  · intro a ha
    rw [mem_mmMinWeightSupport] at ha
    simp only [SumLevel.mem_natTripleLevel]
    exact ⟨(a .X).1.isLt, (a .X).2.isLt, (a .Y).2.isLt, ha.2⟩
  · intro a ha b hb hab
    rw [mem_mmMinWeightSupport] at ha hb
    exact mmIndex_ext_val ha.1 hb.1 (congrArg Prod.fst hab)
      (congrArg (fun q ↦ q.2.1) hab) (congrArg (fun q ↦ q.2.2) hab)
  · intro t ht
    rw [SumLevel.mem_natTripleLevel] at ht
    obtain ⟨h1, h2, h3, h4⟩ := ht
    refine ⟨mmIndexOfTriple m n p ⟨t.1, h1⟩ ⟨t.2.1, h2⟩ ⟨t.2.2, h3⟩, ?_, rfl⟩
    rw [mem_mmMinWeightSupport]
    exact ⟨mmCompatible_mmIndexOfTriple _ _ _, h4⟩

/-- **AVW Lemma 4.2 (finite half), as a bound on the independence number.**  For every triple of
dimensions there is a level `s` whose minimum-weight table `D` satisfies

```text
3·m·n·p ≤ 4·I(D)·max{m,n,p},   i.e.   I(D) ≥ (3/4)·mnp/max{m,n,p}.
```

The bound holds for *all* `m, n, p`, with no parity hypothesis and with AVW's constant `3/4`; see
the module header for how this differs from the paper's argument.

Proof sketch: `I(D)` is the size of the level set (`independenceNumber_mmMinWeightCoefficients`),
which is the number of lattice points of the box `[0,m) × [0,n) × [0,p)` on the plane
`i + j + k = s` (`card_mmMinWeightSupport`); `SumLevel.exists_three_mul_le_card_natTripleLevel`
supplies the level achieving three quarters of the box, divided by the largest side. -/
theorem exists_three_mul_le_independenceNumber_mmMinWeight [Nontrivial K] (m n p : ℕ) :
    ∃ s, 3 * (m * n * p) ≤
      4 * independenceNumber (mmMinWeightCoefficients K m n p s) * max m (max n p) := by
  obtain ⟨s, hs⟩ := SumLevel.exists_three_mul_le_card_natTripleLevel m n p
  exact ⟨s, by rw [independenceNumber_mmMinWeightCoefficients, card_mmMinWeightSupport]; exact hs⟩

/-- The matching trivial upper bound: an independent set cannot use more variables than a single
leg has, so `I(D) ≤ min{mn, np, pm}`.  Together with
`exists_three_mul_le_independenceNumber_mmMinWeight` this sandwiches `I(D)`; for `m = n = p = q`
it reads `(3/4)q² ≤ I(D) ≤ q²`. -/
theorem independenceNumber_mmMinWeightCoefficients_le (m n p s : ℕ) :
    independenceNumber (mmMinWeightCoefficients K m n p s) ≤ min (m * n) (min (n * p) (p * m)) := by
  refine le_min ?_ (le_min ?_ ?_)
  · simpa using independenceNumber_le_card (mmMinWeightCoefficients K m n p s) .X
  · simpa using independenceNumber_le_card (mmMinWeightCoefficients K m n p s) .Y
  · simpa using independenceNumber_le_card (mmMinWeightCoefficients K m n p s) .Z

/-- **The minimum-weight level set is not an independent set of `⟨m,n,p⟩` itself.**  For
`⟨3,3,3⟩` at the middle level `s = 3` the closure clause fails: the term with summation indices
`(i,j,k) = (2,1,1)` has level `4`, yet each of its three variables is used by a level-`3` term,
namely `(2,1,0)` on the `X` leg, `(1,1,1)` on the `Y` leg and `(2,0,1)` on the `Z` leg.

This is why AVW's Lemma 4.2 is a statement about a monomial degeneration rather than a zeroing
out, and why the theorems above are stated for `mmMinWeightCoefficients` rather than for
`mmCoefficients`.  It is a `Tensor.IndependentSet` counterexample, not a computation of
`I(⟨3,3,3⟩)`. -/
theorem not_independentSet_mmCoefficients_mmMinWeightSupport [Nontrivial K] :
    ¬ IndependentSet (mmCoefficients K 3 3 3) (mmMinWeightSupport 3 3 3 3) := by
  intro h
  have hne : mmCoefficients K 3 3 3 (mmIndexOfTriple 3 3 3 2 1 1) ≠ 0 := by
    simp [mmCoefficients, mmCompatible_mmIndexOfTriple]
  have hbox : ∀ c : Leg, ∃ q ∈ mmMinWeightSupport 3 3 3 3,
      q c = mmIndexOfTriple 3 3 3 2 1 1 c := by
    intro c
    cases c with
    | X =>
      exact ⟨mmIndexOfTriple 3 3 3 2 1 0,
        mem_mmMinWeightSupport.mpr ⟨mmCompatible_mmIndexOfTriple _ _ _, by decide⟩, rfl⟩
    | Y =>
      exact ⟨mmIndexOfTriple 3 3 3 1 1 1,
        mem_mmMinWeightSupport.mpr ⟨mmCompatible_mmIndexOfTriple _ _ _, by decide⟩, rfl⟩
    | Z =>
      exact ⟨mmIndexOfTriple 3 3 3 2 0 1,
        mem_mmMinWeightSupport.mpr ⟨mmCompatible_mmIndexOfTriple _ _ _, by decide⟩, rfl⟩
  have hmem := h.closed _ hne hbox
  rw [mem_mmMinWeightSupport] at hmem
  simp at hmem

end Independence

/-! ### Word products of matrix-multiplication coefficient tables

Two constructions below are the same positionwise product of coefficient tables: the Kronecker
power `⟨m,n,p⟩^{⊗k}` of the next section, and the heterogeneous product
`⨂_{t < k} ⟨m t, n t, p t⟩` of milestone **M4** at the end of the file.  Both are
`Tensor.coordinateWordProduct` applied to the family `fun t ↦ mmCoefficients K (m t) (n t) (p t)`;
`mmWordCoefficients` names that product, and `mmWordCoefficients_const` records that a constant
family gives `Tensor.coordinatePower` on the nose, in the same index convention (leg first,
position second).

Both sections then identify the word product with a *single* matrix-multiplication table, after a
legwise renaming of index words by a digit encoding: the fixed-radix base-`m` expansion
`finFunctionFinEquiv` in the homogeneous case, the mixed-radix `finPiFinEquiv` in the heterogeneous
one.  The only property of the encoding that the identification uses is that compatibility is
*letterwise*, so the identification is proved once here, as
`coordinateRelabel_eq_mmCoefficients_of_mmCompatible_iff`, parameterized by an arbitrary legwise
renaming `E` together with that hypothesis.  Each section supplies its own `E` and discharges the
hypothesis from `eq_iff_forall_of_injective`, the single fact about a digit encoding that both
compatibility computations need. -/

section WordProducts

variable {k : ℕ}

/-- **The positionwise product of the coefficient tables of `⟨m t, n t, p t⟩`, `t : Fin k`.**

A variable of leg `c` is a *word* assigning to each position `t` a variable of leg `c` of
`⟨m t, n t, p t⟩`, and the coefficient of a triple of words is the product of its `k` letterwise
coefficients.  This is `Tensor.coordinateWordProduct` at the family of matrix-multiplication
tables; at a constant family it is `Tensor.coordinatePower`. -/
def mmWordCoefficients (K : Type u) [CommSemiring K] (m n p : Fin k → ℕ) :
    (∀ c, ∀ t, MMIndex (m t) (n t) (p t) c) → K :=
  coordinateWordProduct fun t ↦ mmCoefficients K (m t) (n t) (p t)

/-- The coefficient of a triple of words is the product of the coefficients of its letters. -/
@[simp] theorem mmWordCoefficients_apply (K : Type u) [CommSemiring K] (m n p : Fin k → ℕ)
    (v : ∀ c, ∀ t, MMIndex (m t) (n t) (p t) c) :
    mmWordCoefficients K m n p v
      = ∏ t, mmCoefficients K (m t) (n t) (p t) fun c ↦ v c t :=
  coordinateWordProduct_apply _ v

/-- **At a constant family of dimensions the word product is the Kronecker power**, on the nose:
the index type `∀ t : Fin k, MMIndex m n p c` of a word is the index type `Fin k → MMIndex m n p c`
of `Tensor.coordinatePower`, and both tables are the same product over positions.  This is
`Tensor.coordinateWordProduct_const`. -/
theorem mmWordCoefficients_const (K : Type u) [CommSemiring K] (k m n p : ℕ) :
    mmWordCoefficients K (fun _ : Fin k ↦ m) (fun _ ↦ n) (fun _ ↦ p)
      = coordinatePower (mmCoefficients K m n p) k :=
  coordinateWordProduct_const _ k

/-- **An injective encoding of words is letterwise.**  Two words have the same encoding exactly
when they agree at every position.  This is the only property of a digit expansion used by the
compatibility computations for `mmPowerIndexEquiv` and `mmWordIndexEquiv`. -/
private theorem eq_iff_forall_of_injective {ι : Type*} {α : ι → Type*} {β : Sort*}
    {enc : (∀ t, α t) → β} (henc : Function.Injective enc) {u v : ∀ t, α t} :
    enc u = enc v ↔ ∀ t, u t = v t :=
  ⟨fun h t ↦ congrFun (henc h) t, fun h ↦ congrArg enc (funext h)⟩

/-- **A word product of matrix-multiplication tables is a matrix-multiplication table**, for every
legwise renaming `E` of index words under which compatibility is letterwise: with
`E c : (∀ t, MMIndex (m t) (n t) (p t) c) ≃ MMIndex M N P c` on each leg,

```text
coordinateRelabel E (⨂_{t} ⟨m t, n t, p t⟩) = ⟨M, N, P⟩
```

as coefficient tables.  Both digit encodings used in this file — the fixed-radix
`mmPowerIndexEquiv` and the mixed-radix `mmWordIndexEquiv` — are instances.

Proof sketch: every index triple of the target is `E`-encoded from a unique triple `q` of words.
The coefficient of `q` in the word product is the product of the `k` letterwise indicators of
`MMCompatible`, hence `1` when every letter is compatible and `0` as soon as one letter is not;
by the hypothesis that is exactly the indicator of compatibility of the encoded triple, which is
the coefficient of `⟨M,N,P⟩` there. -/
theorem coordinateRelabel_eq_mmCoefficients_of_mmCompatible_iff (K : Type u) [CommSemiring K]
    {m n p : Fin k → ℕ} {M N P : ℕ}
    (E : ∀ c, (∀ t, MMIndex (m t) (n t) (p t) c) ≃ MMIndex M N P c)
    (h : ∀ q : ∀ c, ∀ t, MMIndex (m t) (n t) (p t) c,
      MMCompatible (fun c ↦ E c (q c)) ↔ ∀ t : Fin k, MMCompatible (fun c ↦ q c t)) :
    coordinateRelabel E (mmWordCoefficients K m n p) = mmCoefficients K M N P := by
  funext a
  obtain ⟨q, rfl⟩ :
      ∃ q : ∀ c, ∀ t, MMIndex (m t) (n t) (p t) c, a = fun c ↦ E c (q c) :=
    ⟨fun c ↦ (E c).symm (a c), by funext c; simp⟩
  rw [coordinateRelabel_apply]
  simp only [Equiv.symm_apply_apply]
  have hiff := h q
  by_cases hall : ∀ t : Fin k, MMCompatible (fun c ↦ q c t)
  · have hcomp : MMCompatible (fun c ↦ E c (q c)) := hiff.mpr hall
    have hone : ∀ t : Fin k, mmCoefficients K (m t) (n t) (p t) (fun c ↦ q c t) = 1 :=
      fun t ↦ if_pos (hall t)
    rw [mmWordCoefficients_apply, Finset.prod_congr rfl fun t _ ↦ hone t, Finset.prod_const_one]
    exact (if_pos hcomp).symm
  · obtain ⟨t₀, ht₀⟩ := not_forall.mp hall
    have hcomp : ¬ MMCompatible (fun c ↦ E c (q c)) := fun hc ↦ hall (hiff.mp hc)
    have hzero : mmCoefficients K (m t₀) (n t₀) (p t₀) (fun c ↦ q c t₀) = 0 := if_neg ht₀
    rw [mmWordCoefficients_apply, Finset.prod_eq_zero (Finset.mem_univ t₀) hzero]
    exact (if_neg hcomp).symm

end WordProducts

/-! ### AVW Lemma 4.4: the exact asymptotic independence number of `⟨m,n,p⟩`

*This section post-dates the module header above, which records that Lemma 4.4 "is not in scope
here" because `Ī` was still being built as milestone (B).  Milestones (B) and (C) are now proved,
so the promised consumer of the data exported above is written here rather than in a fourth
module; the header's forward-looking sentence should be read as the design note it was.*

What is added:

1. **The `ℤ → ℕ` shift of `BARRIER_FRAMEWORK.md` §2.1.**  `strassenNatWeight` is
   `strassenWeightX/Y/Z` with the constant `2sm`, `2sn`, `2sp` added to the respective legs, so
   that it is a genuine `ℕ`-valued weighting, and `strassenThreshold m n p s = 2s(m+n+p)` is the
   sum of the three shifts.  `strassenThreshold_le_monomialTotalWeight` is the hypothesis `hmin`
   of the milestone-(C) API, and `minimumWeightPart_strassenNatWeight` identifies the degenerated
   table: the minimum-weight part of `⟨m,n,p⟩` for these weights *is*
   `mmMinWeightCoefficients K m n p s`.

2. **The finite-constant form of the lower bound.**  Feeding the independent set of Lemma 4.2 to
   AVW Corollary 4.1 (`Tensor.card_le_asymptoticIndependenceNumber`) gives, with no division,
   `3·mnp ≤ 4·Ī(⟨m,n,p⟩)·max{m,n,p}`.

3. **The exact value (AVW Lemma 4.4 for one copy).**  The constant `3/4` is then removed by
   powering.  `⟨m,n,p⟩^{⊗k}` is `⟨m^k,n^k,p^k⟩` after the legwise renaming
   `mmPowerIndexEquiv` of index words as base-`m` (resp. `n`, `p`) digit expansions, so
   `Ī(⟨m^k,n^k,p^k⟩) = Ī(⟨m,n,p⟩)^k` and item 2 applied at `(m^k, n^k, p^k)` reads
   `3·(mnp/max)^k ≤ 4·Ī(⟨m,n,p⟩)^k`.  A fixed constant does not survive `k`-th roots
   (`Growth.le_of_pow_succ_le_const_mul_pow_succ`), so `mnp/max ≤ Ī`; the reverse inequality is
   `Ī ≤ min{mn, np, pm} = mnp/max` from `Tensor.asymptoticIndependenceNumber_le_card`.  Hence

   ```text
   Ī(⟨m,n,p⟩) = m·n·p / max{m,n,p}
   ```

   for *all* `m, n, p`, with the degenerate convention `0/0 = 0` covering `m = n = p = 0`.

### The `F`-copies form

AVW display Lemma 4.4 as `Ī(F ⊙ ⟨a,b,c⟩) = F·abc/max{a,b,c}` for a direct sum of `F` disjoint
copies.  That form is proved here as `asymptoticIndependenceNumber_mmCoefficients_copies`, now that
the tensor layer carries the coordinate-level block table `Tensor.coordinateDirectSum` and the
structural law `Tensor.asymptoticIndependenceNumber_coordinateDirectSum_const`
(`Ī(F ⊙ A) = F · Ī(A)` for *every* table `A`).  The two halves are cleanly separated: the block law
is tensor-layer bookkeeping about `I` and its Kronecker powers, and the single-copy value below is
the matrix-multiplication content.

### A general lemma that belongs one layer down

The relabelling invariance of `Ī` used below,
`Tensor.asymptoticIndependenceNumber_coordinateRelabel`, has been promoted to
`Tensor/AsymptoticIndependenceNumber.lean`, where it sits next to the corresponding statement for
`I`. -/

section Lemma44

universe v

open MonomialIndependence

/-! #### Strassen's weights as `ℕ`-valued weights with a threshold -/

section NatWeights

variable {m n p : ℕ}

/-- **Strassen's weights, shifted to `ℕ`** (`BARRIER_FRAMEWORK.md` §2.1).  Each leg weight of
`strassenWeightX/Y/Z` is increased by a constant depending only on the leg — `2sm` on `X`, `2sn`
on `Y`, `2sp` on `Z` — which makes it nonnegative on *every* index, not only on the support, and
therefore expressible in `ℕ` with no truncated subtraction beyond `m - i ≥ 0`, `n - j ≥ 0`,
`p - k ≥ 0`.

The corresponding threshold is `strassenThreshold m n p s = 2s(m+n+p)`, the sum of the three
shifts, so that the pair `(strassenNatWeight s, strassenThreshold m n p s)` carries exactly the
information of the `ℤ`-valued weighting with threshold `0`. -/
def strassenNatWeight (s : ℕ) : ∀ c, MMIndex m n p c → ℕ
  | .X => fun x ↦ x.1.val ^ 2 + 2 * x.1.val * x.2.val + s ^ 2 + 2 * s * (m - x.1.val)
  | .Y => fun y ↦ y.1.val ^ 2 + 2 * y.1.val * y.2.val + 2 * s * (n - y.1.val)
  | .Z => fun z ↦ z.1.val ^ 2 + 2 * z.1.val * z.2.val + 2 * s * (p - z.1.val)

@[simp] theorem strassenNatWeight_X (s : ℕ) (x : MMIndex m n p .X) :
    strassenNatWeight (m := m) (n := n) (p := p) s .X x
      = x.1.val ^ 2 + 2 * x.1.val * x.2.val + s ^ 2 + 2 * s * (m - x.1.val) := rfl

@[simp] theorem strassenNatWeight_Y (s : ℕ) (y : MMIndex m n p .Y) :
    strassenNatWeight (m := m) (n := n) (p := p) s .Y y
      = y.1.val ^ 2 + 2 * y.1.val * y.2.val + 2 * s * (n - y.1.val) := rfl

@[simp] theorem strassenNatWeight_Z (s : ℕ) (z : MMIndex m n p .Z) :
    strassenNatWeight (m := m) (n := n) (p := p) s .Z z
      = z.1.val ^ 2 + 2 * z.1.val * z.2.val + 2 * s * (p - z.1.val) := rfl

/-- The threshold matching `strassenNatWeight`: the sum `2s(m+n+p)` of the three constant leg
shifts. -/
def strassenThreshold (m n p s : ℕ) : ℕ := 2 * s * (m + n + p)

theorem strassenNatWeight_X_cast (s : ℕ) (x : MMIndex m n p .X) :
    ((strassenNatWeight (m := m) (n := n) (p := p) s .X x : ℕ) : ℤ)
      = strassenWeightX s x + 2 * (s : ℤ) * (m : ℤ) := by
  rw [strassenNatWeight_X, strassenWeightX]
  push_cast [Nat.cast_sub x.1.isLt.le]
  ring

theorem strassenNatWeight_Y_cast (s : ℕ) (y : MMIndex m n p .Y) :
    ((strassenNatWeight (m := m) (n := n) (p := p) s .Y y : ℕ) : ℤ)
      = strassenWeightY s y + 2 * (s : ℤ) * (n : ℤ) := by
  rw [strassenNatWeight_Y, strassenWeightY]
  push_cast [Nat.cast_sub y.1.isLt.le]
  ring

theorem strassenNatWeight_Z_cast (s : ℕ) (z : MMIndex m n p .Z) :
    ((strassenNatWeight (m := m) (n := n) (p := p) s .Z z : ℕ) : ℤ)
      = strassenWeightZ s z + 2 * (s : ℤ) * (p : ℤ) := by
  rw [strassenNatWeight_Z, strassenWeightZ]
  push_cast [Nat.cast_sub z.1.isLt.le]
  ring

/-- **The shifted weight identity.**  On a term of `⟨m,n,p⟩` the total `ℕ`-weight is the perfect
square `(i+j+k-s)²` plus the threshold; this is `strassenWeight_add` with the three constant leg
shifts added back. -/
theorem monomialTotalWeight_strassenNatWeight (s : ℕ) {a : ∀ c, MMIndex m n p c}
    (h : MMCompatible a) :
    ((monomialTotalWeight (strassenNatWeight s) a : ℕ) : ℤ)
      = ((mmLevel a : ℤ) - (s : ℤ)) ^ 2 + ((strassenThreshold m n p s : ℕ) : ℤ) := by
  have hkey := strassenWeight_add s h
  rw [monomialTotalWeight, Nat.cast_add, Nat.cast_add, strassenNatWeight_X_cast,
    strassenNatWeight_Y_cast, strassenNatWeight_Z_cast, strassenThreshold]
  push_cast
  linear_combination hkey

/-- **The `hmin` hypothesis of AVW Lemma 4.3, for Strassen's weights.**  Every occurring term of
`⟨m,n,p⟩` has total weight at least the threshold. -/
theorem strassenThreshold_le_monomialTotalWeight {K : Type u} [CommSemiring K] (s : ℕ)
    (a : ∀ c, MMIndex m n p c) (ha : mmCoefficients K m n p a ≠ 0) :
    strassenThreshold m n p s ≤ monomialTotalWeight (strassenNatWeight s) a := by
  have hc : MMCompatible a := by
    by_contra hc
    exact ha (by simp [mmCoefficients, hc])
  have hz := monomialTotalWeight_strassenNatWeight s hc
  have hle : ((strassenThreshold m n p s : ℕ) : ℤ)
      ≤ ((monomialTotalWeight (strassenNatWeight s) a : ℕ) : ℤ) := by
    rw [hz]
    nlinarith [sq_nonneg ((mmLevel a : ℤ) - (s : ℤ))]
  exact_mod_cast hle

/-- The total weight of a term of `⟨m,n,p⟩` meets the threshold exactly on the level set
`{i + j + k = s}`; this is `strassenWeight_add_eq_zero_iff` after the shift. -/
theorem monomialTotalWeight_strassenNatWeight_eq_iff (s : ℕ) {a : ∀ c, MMIndex m n p c}
    (h : MMCompatible a) :
    monomialTotalWeight (strassenNatWeight s) a = strassenThreshold m n p s ↔ mmLevel a = s := by
  have hz := monomialTotalWeight_strassenNatWeight s h
  constructor
  · intro he
    rw [he] at hz
    have hsq : ((mmLevel a : ℤ) - (s : ℤ)) ^ 2 = 0 := by linarith
    have := sub_eq_zero.mp (sq_eq_zero_iff.mp hsq)
    exact_mod_cast this
  · intro he
    have hz0 : ((mmLevel a : ℤ) - (s : ℤ)) = 0 := by rw [he]; ring
    have : ((monomialTotalWeight (strassenNatWeight s) a : ℕ) : ℤ)
        = ((strassenThreshold m n p s : ℕ) : ℤ) := by rw [hz, hz0]; ring
    exact_mod_cast this

/-- **The minimum-weight part of `⟨m,n,p⟩` for Strassen's weights is the level-`s` table.**  This
is the identification the milestone-(C) API needs: the abstract `minimumWeightPart` of
`Tensor/MonomialIndependence.lean`, instantiated at `strassenNatWeight s`, is literally the
concrete `mmMinWeightCoefficients` on which Lemma 4.2's independent set lives.

Proof sketch: off the support of `⟨m,n,p⟩` both sides vanish; on it the weight meets the threshold
exactly on the level set (`monomialTotalWeight_strassenNatWeight_eq_iff`). -/
theorem minimumWeightPart_strassenNatWeight (K : Type u) [CommSemiring K] (m n p s : ℕ) :
    minimumWeightPart (strassenNatWeight s) (strassenThreshold m n p s) (mmCoefficients K m n p)
      = mmMinWeightCoefficients K m n p s := by
  funext a
  simp only [minimumWeightPart]
  by_cases h : MMCompatible a
  · by_cases hl : mmLevel a = s
    · rw [if_pos ((monomialTotalWeight_strassenNatWeight_eq_iff s h).mpr hl)]
      simp [mmCoefficients, mmMinWeightCoefficients, hl]
    · rw [if_neg fun hc ↦ hl ((monomialTotalWeight_strassenNatWeight_eq_iff s h).mp hc)]
      simp [mmMinWeightCoefficients, hl]
  · simp [mmCoefficients, mmMinWeightCoefficients, h]

end NatWeights

/-! #### The lower bound with AVW's constant `3/4` -/

/-- **AVW Lemma 4.2 fed to Corollary 4.1.**  The asymptotic independence number of `⟨m,n,p⟩`
satisfies `3·m·n·p ≤ 4·Ī(⟨m,n,p⟩)·max{m,n,p}`, i.e. `Ī(⟨m,n,p⟩) ≥ (3/4)·mnp/max{m,n,p}`.

This is the honest half of Lemma 4.4 obtainable from a *single* application of the monomial
degeneration; the constant is removed in `le_asymptoticIndependenceNumber_mmCoefficients` by
applying this bound to the Kronecker powers.

Proof sketch: `minimumWeightPart_strassenNatWeight` turns the independent set
`independentSet_mmMinWeightSupport` of Lemma 4.2 into an independent set of the minimum-weight
part of the table of `⟨m,n,p⟩`, and `Tensor.card_le_asymptoticIndependenceNumber` (AVW Corollary
4.1) bounds `Ī` below by its size, which
`SumLevel.exists_three_mul_le_card_natTripleLevel` counts. -/
theorem three_mul_le_asymptoticIndependenceNumber_mmCoefficients
    (K : Type u) [CommSemiring K] [NoZeroDivisors K] [Nontrivial K] (m n p : ℕ) :
    3 * ((m * n * p : ℕ) : ℝ)
      ≤ 4 * asymptoticIndependenceNumber (mmCoefficients K m n p)
          * ((max m (max n p) : ℕ) : ℝ) := by
  obtain ⟨s, hs⟩ := SumLevel.exists_three_mul_le_card_natTripleLevel m n p
  have hind : IndependentSet
      (minimumWeightPart (strassenNatWeight s) (strassenThreshold m n p s)
        (mmCoefficients K m n p))
      (mmMinWeightSupport m n p s) := by
    rw [minimumWeightPart_strassenNatWeight]
    exact independentSet_mmMinWeightSupport (K := K) m n p s
  have hle : (((mmMinWeightSupport m n p s).card : ℕ) : ℝ)
      ≤ asymptoticIndependenceNumber (mmCoefficients K m n p) :=
    card_le_asymptoticIndependenceNumber (strassenNatWeight s) (strassenThreshold m n p s)
      (strassenThreshold_le_monomialTotalWeight s) hind
  have hsR : 3 * ((m * n * p : ℕ) : ℝ)
      ≤ 4 * (((mmMinWeightSupport m n p s).card : ℕ) : ℝ) * ((max m (max n p) : ℕ) : ℝ) := by
    rw [card_mmMinWeightSupport]
    exact_mod_cast hs
  refine hsR.trans (mul_le_mul_of_nonneg_right ?_ (by positivity))
  linarith

/-! #### `⟨m,n,p⟩^{⊗k}` is `⟨m^k, n^k, p^k⟩` -/

/-- **The Kronecker power of `⟨m,n,p⟩` in matrix coordinates.**  A variable of the `X` leg of
`⟨m,n,p⟩^{⊗k}` is a word of `k` pairs `(i_t, j_t)`; reading the two coordinate sequences as
base-`m` and base-`n` digit expansions (`finFunctionFinEquiv`) turns it into a single pair
`(I, J) ∈ Fin (m^k) × Fin (n^k)`, and similarly on the other two legs.  Splitting a word of pairs
into a pair of words is `Tensor.splitIndexEquiv`. -/
def mmPowerIndexEquiv (k m n p : ℕ) :
    ∀ c, (Fin k → MMIndex m n p c) ≃ MMIndex (m ^ k) (n ^ k) (p ^ k) c
  | .X => (splitIndexEquiv (Fin m) (Fin n) k).trans
      (Equiv.prodCongr finFunctionFinEquiv finFunctionFinEquiv)
  | .Y => (splitIndexEquiv (Fin n) (Fin p) k).trans
      (Equiv.prodCongr finFunctionFinEquiv finFunctionFinEquiv)
  | .Z => (splitIndexEquiv (Fin p) (Fin m) k).trans
      (Equiv.prodCongr finFunctionFinEquiv finFunctionFinEquiv)

@[simp] theorem mmPowerIndexEquiv_X (k m n p : ℕ) (q : Fin k → MMIndex m n p .X) :
    mmPowerIndexEquiv k m n p .X q
      = (finFunctionFinEquiv fun t ↦ (q t).1, finFunctionFinEquiv fun t ↦ (q t).2) := rfl

@[simp] theorem mmPowerIndexEquiv_Y (k m n p : ℕ) (q : Fin k → MMIndex m n p .Y) :
    mmPowerIndexEquiv k m n p .Y q
      = (finFunctionFinEquiv fun t ↦ (q t).1, finFunctionFinEquiv fun t ↦ (q t).2) := rfl

@[simp] theorem mmPowerIndexEquiv_Z (k m n p : ℕ) (q : Fin k → MMIndex m n p .Z) :
    mmPowerIndexEquiv k m n p .Z q
      = (finFunctionFinEquiv fun t ↦ (q t).1, finFunctionFinEquiv fun t ↦ (q t).2) := rfl

/-- **Compatibility is letterwise.**  A triple of digit-encoded indices is a term of
`⟨m^k,n^k,p^k⟩` exactly when each of its `k` letters is a term of `⟨m,n,p⟩`, because the digit
encoding is injective, so an equality of encoded index sequences is an equality of the sequences
themselves (`eq_iff_forall_of_injective`). -/
theorem mmCompatible_mmPowerIndexEquiv (k m n p : ℕ) (q : ∀ c, Fin k → MMIndex m n p c) :
    MMCompatible (fun c ↦ mmPowerIndexEquiv k m n p c (q c)) ↔
      ∀ t : Fin k, MMCompatible (fun c ↦ q c t) := by
  have hinj : ∀ {N : ℕ} {u v : Fin k → Fin N},
      (finFunctionFinEquiv u = finFunctionFinEquiv v) ↔ ∀ t, u t = v t := fun {_ _ _} ↦
    eq_iff_forall_of_injective finFunctionFinEquiv.injective
  constructor
  · rintro ⟨h1, h2, h3⟩ t
    exact ⟨(hinj (u := fun t ↦ (q Leg.X t).2) (v := fun t ↦ (q Leg.Y t).1)).mp h1 t,
      (hinj (u := fun t ↦ (q Leg.Y t).2) (v := fun t ↦ (q Leg.Z t).1)).mp h2 t,
      (hinj (u := fun t ↦ (q Leg.Z t).2) (v := fun t ↦ (q Leg.X t).1)).mp h3 t⟩
  · intro h
    exact ⟨(hinj (u := fun t ↦ (q Leg.X t).2) (v := fun t ↦ (q Leg.Y t).1)).mpr fun t ↦ (h t).1,
      (hinj (u := fun t ↦ (q Leg.Y t).2) (v := fun t ↦ (q Leg.Z t).1)).mpr fun t ↦ (h t).2.1,
      (hinj (u := fun t ↦ (q Leg.Z t).2) (v := fun t ↦ (q Leg.X t).1)).mpr fun t ↦ (h t).2.2⟩

/-- **The coefficient table of `⟨m,n,p⟩^{⊗k}` is that of `⟨m^k, n^k, p^k⟩`,** after the legwise
renaming `mmPowerIndexEquiv` of index words by their digit expansions.

Proof sketch: the Kronecker power is the word product at a constant family
(`mmWordCoefficients_const`), so this is
`coordinateRelabel_eq_mmCoefficients_of_mmCompatible_iff` at `E = mmPowerIndexEquiv`, whose
letterwise-compatibility hypothesis is `mmCompatible_mmPowerIndexEquiv`. -/
theorem coordinateRelabel_mmPowerIndexEquiv (K : Type u) [CommSemiring K] (k m n p : ℕ) :
    coordinateRelabel (mmPowerIndexEquiv k m n p) (coordinatePower (mmCoefficients K m n p) k)
      = mmCoefficients K (m ^ k) (n ^ k) (p ^ k) :=
  coordinateRelabel_eq_mmCoefficients_of_mmCompatible_iff K
    (m := fun _ : Fin k ↦ m) (n := fun _ ↦ n) (p := fun _ ↦ p)
    (mmPowerIndexEquiv k m n p) (mmCompatible_mmPowerIndexEquiv k m n p)

/-- **The power law for matrix-multiplication tensors**: `Ī(⟨m^k,n^k,p^k⟩) = Ī(⟨m,n,p⟩)^k` for
`k ≥ 1`, by `Tensor.asymptoticIndependenceNumber_coordinatePower` through the renaming above. -/
theorem asymptoticIndependenceNumber_mmCoefficients_pow
    (K : Type u) [CommSemiring K] [NoZeroDivisors K] [Nontrivial K] (m n p : ℕ) {k : ℕ}
    (hk : k ≠ 0) :
    asymptoticIndependenceNumber (mmCoefficients K (m ^ k) (n ^ k) (p ^ k))
      = asymptoticIndependenceNumber (mmCoefficients K m n p) ^ k := by
  rw [← coordinateRelabel_mmPowerIndexEquiv K k m n p, asymptoticIndependenceNumber_coordinateRelabel,
    asymptoticIndependenceNumber_coordinatePower _ hk]

/-! #### The exact value -/

/-- The trivial upper bound `Ī(⟨m,n,p⟩) ≤ min{mn, np, pm} = mnp/max{m,n,p}`: an independent
zeroing out uses at most all the variables of any one leg.  The `max = 0` case, where all three
dimensions vanish, is covered by Lean's `x / 0 = 0`. -/
theorem asymptoticIndependenceNumber_mmCoefficients_le
    (K : Type u) [CommSemiring K] (m n p : ℕ) :
    asymptoticIndependenceNumber (mmCoefficients K m n p)
      ≤ ((m * n * p : ℕ) : ℝ) / ((max m (max n p) : ℕ) : ℝ) := by
  have hX : asymptoticIndependenceNumber (mmCoefficients K m n p) ≤ ((m * n : ℕ) : ℝ) := by
    simpa using asymptoticIndependenceNumber_le_card (mmCoefficients K m n p) Leg.X
  have hY : asymptoticIndependenceNumber (mmCoefficients K m n p) ≤ ((n * p : ℕ) : ℝ) := by
    simpa using asymptoticIndependenceNumber_le_card (mmCoefficients K m n p) Leg.Y
  have hZ : asymptoticIndependenceNumber (mmCoefficients K m n p) ≤ ((p * m : ℕ) : ℝ) := by
    simpa using asymptoticIndependenceNumber_le_card (mmCoefficients K m n p) Leg.Z
  rcases Nat.eq_zero_or_pos (max m (max n p)) with hM | hM
  · have hm : m = 0 := by omega
    have hn : n = 0 := by omega
    have hp : p = 0 := by omega
    subst hm; subst hn; subst hp
    simpa using hX
  · have hMpos : (0 : ℝ) < ((max m (max n p) : ℕ) : ℝ) := by exact_mod_cast hM
    rw [le_div_iff₀ hMpos]
    have hstep : ∀ A B : ℕ, max m (max n p) = B → m * n * p = A * B →
        asymptoticIndependenceNumber (mmCoefficients K m n p) ≤ ((A : ℕ) : ℝ) →
        asymptoticIndependenceNumber (mmCoefficients K m n p) * ((max m (max n p) : ℕ) : ℝ)
          ≤ ((m * n * p : ℕ) : ℝ) := by
      intro A B hB hAB hA
      rw [hB, hAB]
      push_cast
      exact mul_le_mul_of_nonneg_right hA (by positivity)
    rcases le_total n p with h1 | h1
    · rcases le_total m p with h2 | h2
      · exact hstep (m * n) p (by omega) (by ring) hX
      · exact hstep (n * p) m (by omega) (by ring) hY
    · rcases le_total m n with h2 | h2
      · exact hstep (p * m) n (by omega) (by ring) hZ
      · exact hstep (n * p) m (by omega) (by ring) hY

/-- **The matching lower bound `mnp/max{m,n,p} ≤ Ī(⟨m,n,p⟩)`**, with AVW's constant `3/4`
removed.

Proof sketch: `three_mul_le_asymptoticIndependenceNumber_mmCoefficients` applied at
`(m^k, n^k, p^k)` reads `3·(mnp)^k ≤ 4·Ī(⟨m^k,n^k,p^k⟩)·(max{m,n,p})^k`, because the maximum of
the `k`th powers is the `k`th power of the maximum; the middle factor is `Ī(⟨m,n,p⟩)^k` by
`asymptoticIndependenceNumber_mmCoefficients_pow`.  Dividing by `(max{m,n,p})^k` gives
`(mnp/max)^{k} ≤ (4/3)·Ī^{k}` for every `k ≥ 1`, and a fixed multiplicative constant does not
survive taking `k`th roots (`Growth.le_of_pow_succ_le_const_mul_pow_succ`). -/
theorem le_asymptoticIndependenceNumber_mmCoefficients
    (K : Type u) [CommSemiring K] [NoZeroDivisors K] [Nontrivial K] (m n p : ℕ) :
    ((m * n * p : ℕ) : ℝ) / ((max m (max n p) : ℕ) : ℝ)
      ≤ asymptoticIndependenceNumber (mmCoefficients K m n p) := by
  have hI0 : 0 ≤ asymptoticIndependenceNumber (mmCoefficients K m n p) :=
    asymptoticIndependenceNumber_nonneg _
  rcases Nat.eq_zero_or_pos (max m (max n p)) with hM | hM
  · rw [hM]
    simpa using hI0
  · have hMpos : (0 : ℝ) < ((max m (max n p) : ℕ) : ℝ) := by exact_mod_cast hM
    have hmaxpow : ∀ j : ℕ, max (m ^ j) (max (n ^ j) (p ^ j)) = (max m (max n p)) ^ j := by
      intro j
      have h2 : ∀ a b : ℕ, max (a ^ j) (b ^ j) = (max a b) ^ j := by
        intro a b
        rcases le_total a b with h | h
        · rw [max_eq_right h, max_eq_right (Nat.pow_le_pow_left h j)]
        · rw [max_eq_left h, max_eq_left (Nat.pow_le_pow_left h j)]
      rw [h2, h2]
    refine Growth.le_of_pow_succ_le_const_mul_pow_succ hI0 (A := 4 / 3) fun k ↦ ?_
    have hbase := three_mul_le_asymptoticIndependenceNumber_mmCoefficients K
      (m ^ (k + 1)) (n ^ (k + 1)) (p ^ (k + 1))
    rw [asymptoticIndependenceNumber_mmCoefficients_pow K m n p (k := k + 1) (by omega),
      hmaxpow (k + 1)] at hbase
    have hprod : m ^ (k + 1) * n ^ (k + 1) * p ^ (k + 1) = (m * n * p) ^ (k + 1) := by
      rw [mul_pow, mul_pow]
    rw [hprod] at hbase
    push_cast at hbase
    have hMk : (0 : ℝ) < ((max m (max n p) : ℕ) : ℝ) ^ (k + 1) := by positivity
    rw [div_pow, div_le_iff₀ hMk]
    push_cast
    linarith

/-- **AVW Lemma 4.4, single-copy form.**  The asymptotic independence number of the
matrix-multiplication tensor is exactly

```text
Ī(⟨m,n,p⟩) = m·n·p / max{m,n,p}
```

for all dimensions `m, n, p` — with no parity hypothesis and no lost constant.  (For
`m = n = p = 0` both sides are `0` under Lean's `x / 0 = 0`.)

The hypotheses are the weakest under which the two halves are available: `NoZeroDivisors` and
`Nontrivial` are what AVW Lemma 4.3 and Corollary 4.1 need, through the supermultiplicativity of
`I` under Kronecker products and the nonvanishing of a product of coefficients; the upper bound
`asymptoticIndependenceNumber_mmCoefficients_le` needs neither.

The `F`-copies form `Ī(F ⊙ ⟨a,b,c⟩) = F·abc/max{a,b,c}` displayed by AVW is
`asymptoticIndependenceNumber_mmCoefficients_copies` below. -/
theorem asymptoticIndependenceNumber_mmCoefficients
    (K : Type u) [CommSemiring K] [NoZeroDivisors K] [Nontrivial K] (m n p : ℕ) :
    asymptoticIndependenceNumber (mmCoefficients K m n p)
      = ((m * n * p : ℕ) : ℝ) / ((max m (max n p) : ℕ) : ℝ) :=
  le_antisymm (asymptoticIndependenceNumber_mmCoefficients_le K m n p)
    (le_asymptoticIndependenceNumber_mmCoefficients K m n p)

/-- The square case, in the form the barrier framework consumes: `Ī(⟨q,q,q⟩) = q²`. -/
theorem asymptoticIndependenceNumber_mmCoefficients_self
    (K : Type u) [CommSemiring K] [NoZeroDivisors K] [Nontrivial K] (q : ℕ) :
    asymptoticIndependenceNumber (mmCoefficients K q q q) = (q : ℝ) ^ 2 := by
  rw [asymptoticIndependenceNumber_mmCoefficients]
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · norm_num
  · have hmax : max q (max q q) = q := by omega
    rw [hmax]
    have hq0 : ((q : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hq.ne'
    push_cast
    field_simp

/-- **AVW Lemma 4.4**, in the displayed `F`-copies form.  For the block table of `F` disjoint
copies of `⟨m,n,p⟩`,

```text
Ī(F ⊙ ⟨m,n,p⟩) = F · m·n·p / max{m,n,p}.
```

The `F` copies are `Tensor.coordinateDirectSum` of the constant family, the coordinate-level
counterpart of `Tensor.indexedDirectSum`; `Tensor.coordinateTensor_coordinateDirectSum_eq_sum`
identifies its abstract tensor with the sum of the `F` embedded copies of `⟨m,n,p⟩`.

Proof sketch: `Tensor.asymptoticIndependenceNumber_coordinateDirectSum_const` is the exact
additivity `Ī(F ⊙ A) = F · Ī(A)`, valid for every coefficient table, and
`asymptoticIndependenceNumber_mmCoefficients` is the single-copy value. -/
theorem asymptoticIndependenceNumber_mmCoefficients_copies
    (K : Type u) [CommSemiring K] [NoZeroDivisors K] [Nontrivial K] (F m n p : ℕ) :
    asymptoticIndependenceNumber
        (coordinateDirectSum (fun _ : Fin F ↦ mmCoefficients K m n p))
      = (F : ℝ) * (((m * n * p : ℕ) : ℝ) / ((max m (max n p) : ℕ) : ℝ)) := by
  rw [asymptoticIndependenceNumber_coordinateDirectSum_const,
    asymptoticIndependenceNumber_mmCoefficients, Fintype.card_fin]

end Lemma44

/-! ### Heterogeneous word products of matrix-multiplication tensors

This section is milestone **M4** of `BARRIER_FRAMEWORK.md`: the generalization of
`mmPowerIndexEquiv` / `coordinateRelabel_mmPowerIndexEquiv` from a *constant* family of dimensions
to an arbitrary one.  Where the Kronecker power `⟨m,n,p⟩^{⊗k}` reads a length-`k` index word in a
fixed base and produces `⟨m^k, n^k, p^k⟩`, a product `⨂_{t < k} ⟨m t, n t, p t⟩` over *varying*
dimensions reads a mixed-radix index word and produces `⟨∏ m t, ∏ n t, ∏ p t⟩`.  The mixed-radix
digit bijection is Mathlib's `finPiFinEquiv`, in place of the fixed-radix `finFunctionFinEquiv`.

The consumers are the coordinate shadows of the barrier framework's extraction chains (milestones
M5 and M6), where the tensor at a node of the chain is a product of matrix-multiplication tensors
of *different* shapes and only the total dimensions matter for `Ī`.

**What is shared with the homogeneous case, and what is not.**  The coefficient table itself is
shared: `mmWordCoefficients` is defined once in "Word products of matrix-multiplication coefficient
tables" above, and the Kronecker power is its constant-family case (`mmWordCoefficients_const`).
So is the identification of a word product with a single matrix-multiplication table, proved once
as `coordinateRelabel_eq_mmCoefficients_of_mmCompatible_iff`; only the digit encoding and its
letterwise-compatibility check are supplied separately here.

The *index bijections* are deliberately not shared: `∏ t : Fin k, m` and `m ^ k` are equal naturals
but not the same type, so `mmPowerIndexEquiv` would have to be transported along
`Finset.prod_const` in all three dimensions simultaneously, and the resulting statement of
`coordinateRelabel_mmPowerIndexEquiv` would carry three `Fin.cast`s. -/

section HeterogeneousWords

variable {k : ℕ}

/-- **The mixed-radix index bijection of a heterogeneous matrix-multiplication word product.**

A variable of the `X` leg of `⨂_{t < k} ⟨m t, n t, p t⟩` is a word of `k` pairs `(i_t, j_t)` with
`i_t : Fin (m t)` and `j_t : Fin (n t)`; reading the two coordinate sequences as mixed-radix digit
expansions (`finPiFinEquiv`) turns it into a single pair `(I, J) ∈ Fin (∏ m t) × Fin (∏ n t)`, and
similarly on the other two legs.  For a constant family this is `mmPowerIndexEquiv` up to the
identification `∏ t : Fin k, m = m ^ k`. -/
def mmWordIndexEquiv (m n p : Fin k → ℕ) :
    ∀ c, (∀ t, MMIndex (m t) (n t) (p t) c) ≃ MMIndex (∏ t, m t) (∏ t, n t) (∏ t, p t) c
  | .X => (Equiv.arrowProdEquivProdArrow (Fin k) (fun t ↦ Fin (m t)) (fun t ↦ Fin (n t))).trans
      (Equiv.prodCongr finPiFinEquiv finPiFinEquiv)
  | .Y => (Equiv.arrowProdEquivProdArrow (Fin k) (fun t ↦ Fin (n t)) (fun t ↦ Fin (p t))).trans
      (Equiv.prodCongr finPiFinEquiv finPiFinEquiv)
  | .Z => (Equiv.arrowProdEquivProdArrow (Fin k) (fun t ↦ Fin (p t)) (fun t ↦ Fin (m t))).trans
      (Equiv.prodCongr finPiFinEquiv finPiFinEquiv)

@[simp] theorem mmWordIndexEquiv_X (m n p : Fin k → ℕ)
    (q : ∀ t, MMIndex (m t) (n t) (p t) .X) :
    mmWordIndexEquiv m n p .X q
      = (finPiFinEquiv fun t ↦ (q t).1, finPiFinEquiv fun t ↦ (q t).2) := rfl

@[simp] theorem mmWordIndexEquiv_Y (m n p : Fin k → ℕ)
    (q : ∀ t, MMIndex (m t) (n t) (p t) .Y) :
    mmWordIndexEquiv m n p .Y q
      = (finPiFinEquiv fun t ↦ (q t).1, finPiFinEquiv fun t ↦ (q t).2) := rfl

@[simp] theorem mmWordIndexEquiv_Z (m n p : Fin k → ℕ)
    (q : ∀ t, MMIndex (m t) (n t) (p t) .Z) :
    mmWordIndexEquiv m n p .Z q
      = (finPiFinEquiv fun t ↦ (q t).1, finPiFinEquiv fun t ↦ (q t).2) := rfl

/-- **Compatibility is letterwise, in the heterogeneous case too.**  A triple of mixed-radix
encoded indices is a term of `⟨∏ m t, ∏ n t, ∏ p t⟩` exactly when each of its `k` letters is a term
of `⟨m t, n t, p t⟩`, because `finPiFinEquiv` is injective, so an equality of encoded index
sequences is an equality of the sequences themselves (`eq_iff_forall_of_injective`). -/
theorem mmCompatible_mmWordIndexEquiv (m n p : Fin k → ℕ)
    (q : ∀ c, ∀ t, MMIndex (m t) (n t) (p t) c) :
    MMCompatible (fun c ↦ mmWordIndexEquiv m n p c (q c)) ↔
      ∀ t : Fin k, MMCompatible (fun c ↦ q c t) := by
  have hinj : ∀ {N : Fin k → ℕ} {u v : ∀ t, Fin (N t)},
      (finPiFinEquiv u = finPiFinEquiv v) ↔ ∀ t, u t = v t := fun {_ _ _} ↦
    eq_iff_forall_of_injective finPiFinEquiv.injective
  constructor
  · rintro ⟨h1, h2, h3⟩ t
    exact ⟨(hinj (u := fun t ↦ (q Leg.X t).2) (v := fun t ↦ (q Leg.Y t).1)).mp h1 t,
      (hinj (u := fun t ↦ (q Leg.Y t).2) (v := fun t ↦ (q Leg.Z t).1)).mp h2 t,
      (hinj (u := fun t ↦ (q Leg.Z t).2) (v := fun t ↦ (q Leg.X t).1)).mp h3 t⟩
  · intro h
    exact ⟨(hinj (u := fun t ↦ (q Leg.X t).2) (v := fun t ↦ (q Leg.Y t).1)).mpr fun t ↦ (h t).1,
      (hinj (u := fun t ↦ (q Leg.Y t).2) (v := fun t ↦ (q Leg.Z t).1)).mpr fun t ↦ (h t).2.1,
      (hinj (u := fun t ↦ (q Leg.Z t).2) (v := fun t ↦ (q Leg.X t).1)).mpr fun t ↦ (h t).2.2⟩

/-- **The positionwise product of the tables of `⟨m t, n t, p t⟩` is the table of
`⟨∏ m t, ∏ n t, ∏ p t⟩`,** after the legwise renaming `mmWordIndexEquiv` of index words by their
mixed-radix expansions.  This is the heterogeneous form of
`coordinateRelabel_mmPowerIndexEquiv`.

Proof sketch: this is `coordinateRelabel_eq_mmCoefficients_of_mmCompatible_iff` at
`E = mmWordIndexEquiv`, whose letterwise-compatibility hypothesis is
`mmCompatible_mmWordIndexEquiv`. -/
theorem coordinateRelabel_mmWordIndexEquiv (K : Type u) [CommSemiring K] (m n p : Fin k → ℕ) :
    coordinateRelabel (mmWordIndexEquiv m n p) (mmWordCoefficients K m n p)
      = mmCoefficients K (∏ t, m t) (∏ t, n t) (∏ t, p t) :=
  coordinateRelabel_eq_mmCoefficients_of_mmCompatible_iff K (mmWordIndexEquiv m n p)
    (mmCompatible_mmWordIndexEquiv m n p)

/-! #### The independence numbers of a heterogeneous word product -/

/-- **`I` of a heterogeneous matrix-multiplication word product is `I` of the product
dimensions.**  Independence numbers are basis-dependent but invariant under a legwise renaming of
the variables (`Tensor.independenceNumber_coordinateRelabel`), and `mmWordIndexEquiv` is such a
renaming by `coordinateRelabel_mmWordIndexEquiv`. -/
theorem independenceNumber_mmWordCoefficients_eq_mmCoefficients
    (K : Type u) [CommSemiring K] (m n p : Fin k → ℕ) :
    independenceNumber (mmWordCoefficients K m n p)
      = independenceNumber (mmCoefficients K (∏ t, m t) (∏ t, n t) (∏ t, p t)) := by
  rw [← coordinateRelabel_mmWordIndexEquiv K m n p, independenceNumber_coordinateRelabel]

/-- **`Ī` of a heterogeneous matrix-multiplication word product is `Ī` of the product
dimensions**, by the same renaming invariance
(`Tensor.asymptoticIndependenceNumber_coordinateRelabel`). -/
theorem asymptoticIndependenceNumber_mmWordCoefficients_eq_mmCoefficients
    (K : Type u) [CommSemiring K] (m n p : Fin k → ℕ) :
    asymptoticIndependenceNumber (mmWordCoefficients K m n p)
      = asymptoticIndependenceNumber (mmCoefficients K (∏ t, m t) (∏ t, n t) (∏ t, p t)) := by
  rw [← coordinateRelabel_mmWordIndexEquiv K m n p,
    asymptoticIndependenceNumber_coordinateRelabel]

/-- **AVW Lemma 4.4 for a heterogeneous word product**: with `M = ∏ m t`, `N = ∏ n t` and
`P = ∏ p t`,

```text
Ī(⨂_{t < k} ⟨m t, n t, p t⟩) = M·N·P / max{M, N, P}
```

in the coordinates of the word indexing.  Combines
`asymptoticIndependenceNumber_mmWordCoefficients_eq_mmCoefficients` with the single-tensor value
`asymptoticIndependenceNumber_mmCoefficients`. -/
theorem asymptoticIndependenceNumber_mmWordCoefficients
    (K : Type u) [CommSemiring K] [NoZeroDivisors K] [Nontrivial K] (m n p : Fin k → ℕ) :
    asymptoticIndependenceNumber (mmWordCoefficients K m n p)
      = ((((∏ t, m t) * (∏ t, n t) * (∏ t, p t) : ℕ) : ℝ))
          / ((max (∏ t, m t) (max (∏ t, n t) (∏ t, p t)) : ℕ) : ℝ) := by
  rw [asymptoticIndependenceNumber_mmWordCoefficients_eq_mmCoefficients,
    asymptoticIndependenceNumber_mmCoefficients]

/-- **AVW Lemma 4.4 for `F` disjoint copies of a heterogeneous word product**: with `M = ∏ m t`,
`N = ∏ n t` and `P = ∏ p t`,

```text
Ī(F ⊙ ⨂_{t < k} ⟨m t, n t, p t⟩) = F · M·N·P / max{M, N, P}.
```

Proof sketch: `Tensor.asymptoticIndependenceNumber_coordinateDirectSum_const` is the exact
additivity `Ī(F ⊙ A) = F · Ī(A)`, valid for every coefficient table, and
`asymptoticIndependenceNumber_mmWordCoefficients` is the single-copy value. -/
theorem asymptoticIndependenceNumber_mmWordCoefficients_copies
    (K : Type u) [CommSemiring K] [NoZeroDivisors K] [Nontrivial K] (F : ℕ) (m n p : Fin k → ℕ) :
    asymptoticIndependenceNumber
        (coordinateDirectSum (fun _ : Fin F ↦ mmWordCoefficients K m n p))
      = (F : ℝ) * (((((∏ t, m t) * (∏ t, n t) * (∏ t, p t) : ℕ) : ℝ))
          / ((max (∏ t, m t) (max (∏ t, n t) (∏ t, p t)) : ℕ) : ℝ)) := by
  rw [asymptoticIndependenceNumber_coordinateDirectSum_const,
    asymptoticIndependenceNumber_mmWordCoefficients, Fintype.card_fin]

end HeterogeneousWords

end AlgebraicComplexity
