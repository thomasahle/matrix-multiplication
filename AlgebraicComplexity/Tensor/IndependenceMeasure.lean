/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Tensor.AsymptoticIndependenceNumber

/-!
# The measure of a coefficient table and the partition bound

This file is the third partitioning tool of the Alman--Vassilevska Williams barrier framework:

> J. Alman and V. Vassilevska Williams, *Limits on All Known (and Some Unknown) Approaches to
> Matrix Multiplication*, arXiv:1810.08671, Section 5 --- Definition 5.2, Claim 5.1 and
> Theorem 5.3.

AVW's third tool generalizes the trivial bound `Ī(T) ≤ min{|X|, |Y|, |Z|}`: a tensor whose support
is *covered* by finitely many sub-tables, none of which has many variables of some one type, still
has small asymptotic independence number.  The quantity that makes this precise is the *measure*
of a coefficient table.

## The definitions being transcribed

**Definition 5.2.**  `X' ⊆ X`, `Y' ⊆ Y`, `Z' ⊆ Z` are *minimal for `T`* if they are the smallest
subsets outside of which every coefficient of `T` vanishes; equivalently, `X'` is the projection
of the support of `T` onto the `X`-leg, and similarly for `Y'` and `Z'`.  The **measure** of `T`
is `μ(T) := |X'| · |Y'| · |Z'|`.

Here the minimal sets are `minimalLegSet T i = legImage (coordinateSupport T) i`, the projection
of the support onto leg `i` --- `legImage` and `mem_legImage` are the projection API already
provided by `Tensor/IndependenceNumber.lean` --- and `coordinateMeasure T = ∏ i, |minimalLegSet T i|`,
which `coordinateMeasure_eq_mul` unfolds to AVW's `|X'| · |Y'| · |Z'|`.

**The partition hypothesis.**  AVW write `T = P₁ + ⋯ + P_k` with the `Pᵢ` supported on the parts
of a partition of the support of `T`.  The proof only ever uses that *every* term of `T` is a term
of *some* part, so the theorems below are stated for a **cover**
`hcover : ∀ p, T p ≠ 0 → ∃ j, P j p ≠ 0`, indexed by an arbitrary finite type of labels; neither
disjointness nor the equation `T = ∑ P j` is needed.  The literal AVW form is recovered by
`asymptoticIndependenceNumber_le_sum_rpow_coordinateMeasure`, whose hypothesis is `T = ∑ j, P j`,
and `coordinatePart` builds a genuine partition out of an arbitrary colouring of the index
triples.

## Main definitions

* `coordinateMeasure T`: the measure `μ(T) = |X'| · |Y'| · |Z'|` (AVW Definition 5.2).
* `coordinatePart c T j`: the part of `T` cut out by a colouring `c` of the index triples; the
  `coordinatePart c T` are a partition of `T` in AVW's sense (`sum_coordinatePart`).

## Main results

The calculus of `μ` --- AVW appeal to the multiplicativity in the proof of Theorem 5.3, and the
monotonicity is what makes `μ` usable at all on the parts of a partition:

* `coordinateMeasure_mono_of_subSupport`: **`μ` is monotone under passing to sub-supports**, and
  hence `coordinateMeasure_coordinateZeroOut_le` under zeroing outs.  Contrast with `I`, which is
  monotone under zeroing outs but *not* under sub-supports (`Tensor/IndependenceNumber.lean`).
* `coordinateMeasure_coordinateRelabel`: `μ` is invariant under relabelling the leg variables.
* `coordinateMeasure_coordinateProduct`: **`μ` is multiplicative**, `μ(T ⊗ T') = μ(T) · μ(T')`,
  over a coefficient ring without zero divisors.
* `coordinateMeasure_coordinatePower`: hence `μ(T^{⊗n}) = μ(T)^n`; the inequality
  `coordinateMeasure_coordinatePower_le`, which is all the barrier proofs need, holds over any
  commutative semiring.

Claim 5.1 and its finite form:

* `independenceNumber_le_card_minimalLegSet`: `I(T) ≤ |X'|`, and the same on each leg --- the
  sharpening of `independenceNumber_le_card` from all variables to the minimal ones, obtained by
  injecting an independent set into a *projection of the support*.
* `independenceNumber_pow_three_le_coordinateMeasure`: `I(T)³ ≤ μ(T)`, since the minimum of the
  three leg counts is at most their geometric mean.
* `asymptoticIndependenceNumber_le_card_minimalLegSet` and
  `asymptoticIndependenceNumber_le_rpow_coordinateMeasure` (**AVW Claim 5.1**):
  `Ī(T) ≤ min{|X'|, |Y'|, |Z'|} ≤ μ(T)^{1/3}`.

Theorem 5.3:

* `IndependentSet.card_le_pow_of_cover`: the finite core.  If the support of `T` is covered by
  the parts `P j` and `t j` is any nonnegative real with `μ(P j) ≤ t j³`, then **every** independent
  set of `T^{⊗n}` has at most `(∑ j t j)^n` elements.
* `independenceNumber_coordinatePower_le_pow_sum_rpow_coordinateMeasure_of_cover`:
  `I(T^{⊗n}) ≤ (∑ⱼ μ(Pⱼ)^{1/3})^n`, the same statement for the independence number itself.
* `asymptoticIndependenceNumber_le_sum_rpow_coordinateMeasure_of_cover` and
  `asymptoticIndependenceNumber_le_sum_rpow_coordinateMeasure` (**AVW Theorem 5.3**):
  `Ī(T) ≤ ∑ⱼ μ(Pⱼ)^{1/3}`.

## The proof of Theorem 5.3, and how it differs from AVW's

AVW argue by a greedy walk: over the `n` coordinates of `T^{⊗n}` they replace the `j`-th tensor
factor by whichever part `Pᵢ` retains a `pᵢ`-fraction of the independent triples, keeping the
*same* zeroing out, and finish with Claim 5.1 applied to the resulting `⨂ⱼ Qⱼ` together with the
multiplicativity of `μ`.  That walk needs the fact --- true, and available here as
`IndependentSet.of_subSupport` --- that re-applying a zeroing out to a sub-support of a tensor
still leaves an independent tensor.

The proof formalized here replaces the walk by a *sum over colour words*, which is shorter, has no
loss at all (not even a polynomial one), and needs no hypothesis on the coefficient ring:

* fix `n` and an independent set `S` of `T^{⊗n}`.  Every letter of every element of `S` is a term
  of `T`, hence a term of some part; choosing one part per letter assigns to each element of `S` a
  *colour word* `w : Fin n → ι`, so `S` is covered by the classes
  `cls w = {p ∈ S : every letter of p is a term of the part named by w}`;
* on one class the count is elementary.  For each leg `i` the projection `p ↦ p i` is injective on
  `S` (that is `IndependentSet.injOn`) and lands in the product of the minimal leg sets
  `∏ pos |minimalLegSet (P (w pos)) i|`, so `|cls w|` is at most each of the three products;
  multiplying the three gives `|cls w|³ ≤ ∏ pos μ(P (w pos)) ≤ ∏ pos t (w pos)³`, whence
  `|cls w| ≤ ∏ pos t (w pos)`;
* summing over all `|ι|^n` colour words, `Finset.prod_univ_sum` turns
  `∑_w ∏_pos t (w pos)` into `(∑ⱼ t j)^n`, which is the theorem.

Three remarks on what this proof does *not* need.  No independent set is ever restricted to a
smaller tensor, so `IndependentSet.of_subSupport` --- the step AVW's walk turns on --- does not
appear; the monotonicity of `I` under sub-supports, which is false, is of course never used
either.  The multiplicativity of `μ` is not invoked as a lemma: the class bound produces the
product `∏ pos μ(P (w pos))` directly from the three leg counts, which is the same computation
`coordinateMeasure_coordinateProduct` performs once and for all for two factors.  And summing over
*all* `|ι|^n` colour words, rather than grouping them into the `O(n^{|ι|})` multiplicity types, is
what removes the polynomial factor that a type-counting argument in the style of
`Tensor/MonomialIndependence.lean` would carry; the bound `I(T^{⊗n}) ≤ (∑ⱼ μ(Pⱼ)^{1/3})^n` is
clean at every finite `n`, so the asymptotic statement follows from the definition of `Ī` as a
supremum of roots, with no appeal to the constant-tolerant `Growth.exponentialRate`.

## Deliberately not proved

* **No finite partition bound for `I` itself of the form `I(T) ≤ ∑ μ(Pⱼ)^{1/3}`.**  The finite
  core `IndependentSet.card_le_pow_of_cover` is stated at the level of `T^{⊗n}` because that is
  where it is true and where it is used; its `n = 1` instance is the finite statement, and nothing
  stronger is claimed.
* The applications of Theorem 5.3 --- AVW Lemma 7.2 and the generalized Coppersmith--Winograd
  bounds of Section 7 --- name a matrix-multiplication construction and belong to a client module.
* AVW's other two partitioning tools (Theorem 5.1, Theorem 5.2 and the binomial-tail Lemma 5.1)
  are separate modules; see `BARRIER_FRAMEWORK.md` §5, milestones H--J.

## Position in the library

Layer 1.  It imports only `Tensor/AsymptoticIndependenceNumber.lean` (and through it
`Tensor/IndependenceNumber.lean`), and mentions no named matrix-multiplication construction and no
numerical bound.  The definitions are support-combinatorial and need only a commutative semiring;
`NoZeroDivisors` (with `Nontrivial`) appears exactly where a product of coefficients must be shown
*nonzero*, namely in the multiplicativity of `μ` under Kronecker products and powers.
-/

namespace AlgebraicComplexity.Tensor

universe u v w

/-! ## Real cube roots

Two elementary facts about `x ↦ x^{1/3}` on the nonnegative reals, isolated so that the
mathematical arguments below are not interrupted by `rpow` bookkeeping. -/

section CubeRoot

/-- The cube of the cube root of a nonnegative real is that real. -/
private theorem rpow_inv_three_pow_three {x : ℝ} (hx : 0 ≤ x) : (x ^ ((3 : ℝ)⁻¹)) ^ 3 = x := by
  rw [show ((3 : ℝ))⁻¹ = ((3 : ℕ) : ℝ)⁻¹ by norm_num]
  exact Real.rpow_inv_natCast_pow hx (by norm_num)

/-- Taking cube roots in an inequality `x³ ≤ y` between reals with `y` nonnegative. -/
private theorem le_rpow_inv_three {x y : ℝ} (hy : 0 ≤ y) (h : x ^ 3 ≤ y) :
    x ≤ y ^ ((3 : ℝ)⁻¹) := by
  refine le_of_pow_le_pow_left₀ (n := 3) (by norm_num) (Real.rpow_nonneg hy _) ?_
  rwa [rpow_inv_three_pow_three hy]

end CubeRoot

/-! ## The measure of a coefficient table

The support `coordinateSupport` and the minimal variable sets `minimalLegSet` themselves live in
`Tensor/IndependenceNumber.lean`, next to `legImage`. -/

section Measure

variable {K : Type u} [CommSemiring K] {κ : Leg → Type v}
variable [∀ i, Fintype (κ i)] [∀ i, DecidableEq (κ i)]

/-- **The measure `μ(T)`** of a coefficient table (Alman--Vassilevska Williams,
arXiv:1810.08671, Definition 5.2): the product `|X'| · |Y'| · |Z'|` of the sizes of the three
minimal variable sets. -/
noncomputable def coordinateMeasure (T : (∀ i, κ i) → K) : ℕ :=
  ∏ i : Leg, (minimalLegSet T i).card

/-- The measure written out as AVW write it, `μ(T) = |X'| · |Y'| · |Z'|`. -/
theorem coordinateMeasure_eq_mul (T : (∀ i, κ i) → K) :
    coordinateMeasure T = (minimalLegSet T Leg.X).card * (minimalLegSet T Leg.Y).card *
      (minimalLegSet T Leg.Z).card :=
  prod_leg _

/-- **Minimal variable sets shrink along sub-supports.**  If every term of `T'` is a term of `T`,
then every variable minimal for `T'` is minimal for `T`. -/
theorem minimalLegSet_subset_of_subSupport {T T' : (∀ i, κ i) → K}
    (hsub : ∀ p, T' p ≠ 0 → T p ≠ 0) (i : Leg) : minimalLegSet T' i ⊆ minimalLegSet T i := by
  intro a ha
  obtain ⟨p, hp, rfl⟩ := mem_minimalLegSet.mp ha
  exact mem_minimalLegSet_of_ne_zero (hsub p hp) i

/-- **The measure is monotone under passing to sub-supports**: deleting terms cannot increase
`μ`.  This is the property that `I` conspicuously lacks --- deleting terms *can* increase the
independence number (`independenceNumber_const_one` versus
`independenceNumber_diagonalCoefficients`) --- and it is why the partition bound below can be
proved without ever restricting an independent set. -/
theorem coordinateMeasure_mono_of_subSupport {T T' : (∀ i, κ i) → K}
    (hsub : ∀ p, T' p ≠ 0 → T p ≠ 0) : coordinateMeasure T' ≤ coordinateMeasure T :=
  Finset.prod_le_prod' fun i _ ↦
    Finset.card_le_card (minimalLegSet_subset_of_subSupport hsub i)

/-- **The measure is monotone under zeroing outs**, the special case of sub-support monotonicity
in which the deleted terms are those using a discarded variable. -/
theorem coordinateMeasure_coordinateZeroOut_le (T : (∀ i, κ i) → K) (A : ∀ i, Finset (κ i)) :
    coordinateMeasure (coordinateZeroOut T A) ≤ coordinateMeasure T :=
  coordinateMeasure_mono_of_subSupport fun _ hp ↦ (coordinateZeroOut_ne_zero hp).1

end Measure

/-! ### Relabelling, products and powers -/

section MeasureCalculus

variable {K : Type u} [CommSemiring K] {κ κ' : Leg → Type v}
variable [∀ i, Fintype (κ i)] [∀ i, DecidableEq (κ i)]
variable [∀ i, Fintype (κ' i)] [∀ i, DecidableEq (κ' i)]

/-- Relabelling the variables of the legs relabels the minimal variable sets.

Proof sketch: both directions transport a witnessing term along the legwise bijection. -/
theorem minimalLegSet_coordinateRelabel (e : ∀ i, κ i ≃ κ' i) (T : (∀ i, κ i) → K) (i : Leg) :
    minimalLegSet (coordinateRelabel e T) i = (minimalLegSet T i).image (e i) := by
  ext a
  simp only [mem_minimalLegSet, Finset.mem_image, coordinateRelabel_apply]
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact ⟨(e i).symm (p i), ⟨_, hp, rfl⟩, by simp⟩
  · rintro ⟨b, ⟨q, hq, rfl⟩, rfl⟩
    exact ⟨fun j ↦ e j (q j), by simpa using hq, rfl⟩

/-- **The measure is invariant under relabelling the variables of the legs.**  As for `I`, this
is invariance under bijective renamings only, not under legwise isomorphism. -/
theorem coordinateMeasure_coordinateRelabel (e : ∀ i, κ i ≃ κ' i) (T : (∀ i, κ i) → K) :
    coordinateMeasure (coordinateRelabel e T) = coordinateMeasure T := by
  simp only [coordinateMeasure]
  refine Finset.prod_congr rfl fun i _ ↦ ?_
  rw [minimalLegSet_coordinateRelabel, Finset.card_image_of_injective _ (e i).injective]

/-- The minimal variable sets of a Kronecker product are the products of the minimal variable
sets.

Proof sketch: a term of `T ⊗ T'` is a pair of terms, which gives the inclusion `⊆` over any
commutative semiring; conversely a term of `T` and a term of `T'` pair into a term of `T ⊗ T'`
precisely because the coefficient ring has no zero divisors. -/
theorem minimalLegSet_coordinateProduct [NoZeroDivisors K]
    (T : (∀ i, κ i) → K) (T' : (∀ i, κ' i) → K) (i : Leg) :
    minimalLegSet (coordinateProduct T T') i = (minimalLegSet T i) ×ˢ (minimalLegSet T' i) := by
  ext a
  simp only [mem_minimalLegSet, Finset.mem_product]
  constructor
  · rintro ⟨p, hp, rfl⟩
    have hp' : T (fun j ↦ (p j).1) * T' (fun j ↦ (p j).2) ≠ 0 := hp
    rw [mul_ne_zero_iff] at hp'
    exact ⟨⟨_, hp'.1, rfl⟩, ⟨_, hp'.2, rfl⟩⟩
  · rintro ⟨⟨p, hp, hpi⟩, ⟨q, hq, hqi⟩⟩
    exact ⟨fun j ↦ (p j, q j), mul_ne_zero hp hq, Prod.ext hpi hqi⟩

/-- **The measure is multiplicative under Kronecker products**, `μ(T ⊗ T') = μ(T) · μ(T')`.  This
is the fact AVW use, without comment, in the proof of Theorem 5.3. -/
theorem coordinateMeasure_coordinateProduct [NoZeroDivisors K]
    (T : (∀ i, κ i) → K) (T' : (∀ i, κ' i) → K) :
    coordinateMeasure (coordinateProduct T T') = coordinateMeasure T * coordinateMeasure T' := by
  simp only [coordinateMeasure]
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ ↦ ?_
  rw [minimalLegSet_coordinateProduct, Finset.card_product]

/-- Every variable minimal for a Kronecker power is a word of variables minimal for the base
table.  This inclusion holds over any commutative semiring, because a nonzero product has no zero
factor. -/
theorem minimalLegSet_coordinatePower_subset (T : (∀ i, κ i) → K) (n : ℕ) (i : Leg) :
    minimalLegSet (coordinatePower T n) i ⊆
      Fintype.piFinset fun _ : Fin n ↦ minimalLegSet T i := by
  intro q hq
  obtain ⟨p, hp, rfl⟩ := mem_minimalLegSet.mp hq
  refine Fintype.mem_piFinset.mpr fun pos ↦ ?_
  have hletter : T (fun j ↦ p j pos) ≠ 0 := by
    intro h0
    refine hp ?_
    rw [coordinatePower_apply]
    exact Finset.prod_eq_zero (Finset.mem_univ pos) h0
  exact mem_minimalLegSet_of_ne_zero hletter i

/-- **The measure of a Kronecker power is at most the power of the measure**, `μ(T^{⊗n}) ≤ μ(T)^n`.
This is the half of multiplicativity that the barrier arguments consume, and it is free of
hypotheses on the coefficient ring. -/
theorem coordinateMeasure_coordinatePower_le (T : (∀ i, κ i) → K) (n : ℕ) :
    coordinateMeasure (coordinatePower T n) ≤ coordinateMeasure T ^ n := by
  have hstep : ∀ i : Leg, (minimalLegSet (coordinatePower T n) i).card ≤
      (minimalLegSet T i).card ^ n := by
    intro i
    calc (minimalLegSet (coordinatePower T n) i).card
        ≤ (Fintype.piFinset fun _ : Fin n ↦ minimalLegSet T i).card :=
          Finset.card_le_card (minimalLegSet_coordinatePower_subset T n i)
      _ = (minimalLegSet T i).card ^ n := by simp [Fintype.card_piFinset]
  calc coordinateMeasure (coordinatePower T n)
      ≤ ∏ i : Leg, (minimalLegSet T i).card ^ n := Finset.prod_le_prod' fun i _ ↦ hstep i
    _ = coordinateMeasure T ^ n := Finset.prod_pow _ _ _

/-- The minimal variable sets of a Kronecker power are exactly the words of minimal variables.

Proof sketch: the inclusion `⊆` is `minimalLegSet_coordinatePower_subset`; conversely, choosing
for each letter a term of `T` using it and reading the chosen terms as the letters of a triple of
words produces a term of `T^{⊗n}`, whose coefficient is a product of nonzero coefficients and
hence nonzero. -/
theorem minimalLegSet_coordinatePower [NoZeroDivisors K] [Nontrivial K]
    (T : (∀ i, κ i) → K) (n : ℕ) (i : Leg) :
    minimalLegSet (coordinatePower T n) i =
      Fintype.piFinset fun _ : Fin n ↦ minimalLegSet T i := by
  refine Finset.Subset.antisymm (minimalLegSet_coordinatePower_subset T n i) ?_
  intro q hq
  have hq' := Fintype.mem_piFinset.mp hq
  choose p hp hpi using fun pos ↦ mem_minimalLegSet.mp (hq' pos)
  refine mem_minimalLegSet.mpr ⟨fun j pos ↦ p pos j, ?_, funext fun pos ↦ hpi pos⟩
  rw [coordinatePower_apply]
  exact Finset.prod_ne_zero_iff.mpr fun pos _ ↦ hp pos

/-- **The measure is multiplicative along Kronecker powers**, `μ(T^{⊗n}) = μ(T)^n`. -/
theorem coordinateMeasure_coordinatePower [NoZeroDivisors K] [Nontrivial K]
    (T : (∀ i, κ i) → K) (n : ℕ) :
    coordinateMeasure (coordinatePower T n) = coordinateMeasure T ^ n := by
  simp only [coordinateMeasure]
  rw [← Finset.prod_pow]
  refine Finset.prod_congr rfl fun i _ ↦ ?_
  rw [minimalLegSet_coordinatePower, Fintype.card_piFinset]
  simp

end MeasureCalculus

/-! ## Claim 5.1: the independence number and the measure -/

section ClaimFiveOne

variable {K : Type u} [CommSemiring K] {κ : Leg → Type v}
variable [∀ i, Fintype (κ i)] [∀ i, DecidableEq (κ i)]

/-- **An independent set injects into every minimal variable set.**  This sharpens
`IndependentSet.card_le_card` from all variables of a leg to the ones actually used by `T`:
the `i`-th coordinate projection is injective on an independent set and lands in
`minimalLegSet T i`. -/
theorem IndependentSet.card_le_card_minimalLegSet {T : (∀ i, κ i) → K} {S : Finset (∀ i, κ i)}
    (h : IndependentSet T S) (i : Leg) : S.card ≤ (minimalLegSet T i).card :=
  Finset.card_le_card_of_injOn (fun p ↦ p i)
    (fun p hp ↦ Finset.mem_coe.mpr
      (mem_minimalLegSet_of_ne_zero (h.ne_zero p (Finset.mem_coe.mp hp)) i))
    (h.injOn i)

/-- **`I(T) ≤ |X'|`, and the same on each leg** --- the minimal-variable sharpening of
`independenceNumber_le_card`, which is the first step of AVW's proof of Claim 5.1. -/
theorem independenceNumber_le_card_minimalLegSet (T : (∀ i, κ i) → K) (i : Leg) :
    independenceNumber T ≤ (minimalLegSet T i).card :=
  independenceNumber_le fun _ hS ↦ hS.card_le_card_minimalLegSet i

/-- **The finite form of Claim 5.1**: `I(T)³ ≤ μ(T)`.  The minimum of the three minimal-leg
counts is at most their geometric mean, and `I(T)` is at most each of them. -/
theorem independenceNumber_pow_three_le_coordinateMeasure (T : (∀ i, κ i) → K) :
    independenceNumber T ^ 3 ≤ coordinateMeasure T := by
  have hconst : independenceNumber T ^ 3 = ∏ _i : Leg, independenceNumber T := by
    rw [Finset.prod_const, Finset.card_univ]
    rfl
  rw [hconst, coordinateMeasure]
  exact Finset.prod_le_prod' fun i _ ↦ independenceNumber_le_card_minimalLegSet T i

/-- **`Ī(T) ≤ |X'|`, and the same on each leg**: the asymptotic form of the minimal-variable
bound, which is the first step of AVW's proof of Claim 5.1 applied to every Kronecker power at
once.

Proof sketch: a variable of leg `i` of `T^{⊗n}` that is minimal for `T^{⊗n}` is a word of
variables minimal for `T` (`minimalLegSet_coordinatePower_subset`), so
`I(T^{⊗n}) ≤ |minimalLegSet T i|^n`, and `Ī` is the supremum of the `n`th roots. -/
theorem asymptoticIndependenceNumber_le_card_minimalLegSet (T : (∀ i, κ i) → K) (i : Leg) :
    asymptoticIndependenceNumber T ≤ ((minimalLegSet T i).card : ℝ) := by
  refine asymptoticIndependenceNumber_le_of_pow (by positivity) fun n ↦ ?_
  have h : independenceNumber (coordinatePower T n) ≤ (minimalLegSet T i).card ^ n := by
    calc independenceNumber (coordinatePower T n)
        ≤ (minimalLegSet (coordinatePower T n) i).card :=
          independenceNumber_le_card_minimalLegSet _ i
      _ ≤ (Fintype.piFinset fun _ : Fin n ↦ minimalLegSet T i).card :=
          Finset.card_le_card (minimalLegSet_coordinatePower_subset T n i)
      _ = (minimalLegSet T i).card ^ n := by simp [Fintype.card_piFinset]
  exact_mod_cast h

/-- The cube of the asymptotic independence number is at most the measure, `Ī(T)³ ≤ μ(T)`. -/
theorem asymptoticIndependenceNumber_pow_three_le_coordinateMeasure (T : (∀ i, κ i) → K) :
    asymptoticIndependenceNumber T ^ 3 ≤ ((coordinateMeasure T : ℕ) : ℝ) := by
  have hconst : asymptoticIndependenceNumber T ^ 3 =
      ∏ _i : Leg, asymptoticIndependenceNumber T := by
    rw [Finset.prod_const, Finset.card_univ]
    rfl
  rw [hconst, coordinateMeasure, Nat.cast_prod]
  exact Finset.prod_le_prod (fun i _ ↦ asymptoticIndependenceNumber_nonneg T)
    fun i _ ↦ asymptoticIndependenceNumber_le_card_minimalLegSet T i

/-- **AVW Claim 5.1**: `Ī(T) ≤ μ(T)^{1/3}` for every coefficient table `T`.

This is exactly AVW's one-line argument: `Ī(T) ≤ min{|X'|, |Y'|, |Z'|}` for the minimal variable
sets `X'`, `Y'`, `Z'`, and the minimum of three numbers is at most their geometric mean
`(|X'| · |Y'| · |Z'|)^{1/3} = μ(T)^{1/3}`. -/
theorem asymptoticIndependenceNumber_le_rpow_coordinateMeasure (T : (∀ i, κ i) → K) :
    asymptoticIndependenceNumber T ≤ ((coordinateMeasure T : ℕ) : ℝ) ^ ((3 : ℝ)⁻¹) :=
  le_rpow_inv_three (by positivity)
    (asymptoticIndependenceNumber_pow_three_le_coordinateMeasure T)

end ClaimFiveOne

/-! ## Theorem 5.3: the partition bound -/

section Partition

variable {K : Type u} [CommSemiring K] {κ : Leg → Type v}
variable [∀ i, Fintype (κ i)] [∀ i, DecidableEq (κ i)]
variable {ι : Type w} [Fintype ι]

/-- The **part of `T` cut out by a colouring** `c` of the index triples: the sub-table supported
on the triples of colour `j`.  Colouring the support and taking the parts is the general way to
produce a partition of `T` in AVW's sense; `sum_coordinatePart` checks that the parts sum to `T`
and `exists_coordinatePart_ne_zero` that they cover its support. -/
def coordinatePart [DecidableEq ι] (c : (∀ i, κ i) → ι) (T : (∀ i, κ i) → K) (j : ι) :
    (∀ i, κ i) → K :=
  fun p ↦ if c p = j then T p else 0

omit [∀ i, Fintype (κ i)] [∀ i, DecidableEq (κ i)] in
/-- The parts cut out by a colouring sum to the original table: `T = P₁ + ⋯ + P_k`. -/
theorem sum_coordinatePart [DecidableEq ι] (c : (∀ i, κ i) → ι) (T : (∀ i, κ i) → K) :
    ∑ j, coordinatePart c T j = T := by
  funext p
  simp [coordinatePart, Finset.sum_apply]

omit [∀ i, Fintype (κ i)] [∀ i, DecidableEq (κ i)] [Fintype ι] in
/-- The parts cut out by a colouring cover the support of `T`: a term of `T` is a term of the part
carrying its own colour. -/
theorem exists_coordinatePart_ne_zero [DecidableEq ι] (c : (∀ i, κ i) → ι)
    (T : (∀ i, κ i) → K) {p : ∀ i, κ i} (hp : T p ≠ 0) :
    ∃ j, coordinatePart c T j p ≠ 0 :=
  ⟨c p, by simpa [coordinatePart] using hp⟩

/-- **The finite core of AVW Theorem 5.3.**  Suppose the support of `T` is covered by the parts
`P j`, `j` ranging over a finite type of labels, and let `t j ≥ 0` be reals with `μ(P j) ≤ t j³`.
Then every independent set of terms of `T^{⊗n}` has at most `(∑ⱼ t j)^n` elements.

Taking `t j = μ(P j)^{1/3}` gives the bound of Theorem 5.3; the formulation with arbitrary upper
bounds `t j` is what makes the cube roots disappear from the counting argument.

Proof sketch.  Each element `p` of the independent set `S` has all its `n` letters in the support
of `T` (a nonzero product has no zero factor), so each letter lies in some part; choosing one part
per letter attaches to `p` a *colour word* `w : Fin n → ι`, and `S` is covered by the classes
`cls w` of elements all of whose letters are terms of the parts named by `w`.

On one class the count is elementary.  Fix a leg `i`.  The projection `p ↦ p i` is injective on
`S`, hence on `cls w` (`IndependentSet.injOn`), and it maps `cls w` into the set of words whose
`pos`-th letter is minimal for `P (w pos)` on leg `i`; therefore
`|cls w| ≤ ∏_pos |minimalLegSet (P (w pos)) i|`.  Multiplying the three legs gives
`|cls w|³ ≤ ∏_pos μ(P (w pos)) ≤ ∏_pos t (w pos)³`, hence `|cls w| ≤ ∏_pos t (w pos)`.

Finally `|S| ≤ ∑_w |cls w| ≤ ∑_w ∏_pos t (w pos) = (∑ⱼ t j)^n`, the last equality being the
expansion `Finset.prod_univ_sum` of a product of `n` identical sums.  Note that no part of the
argument restricts an independent set to a smaller tensor, and that no loss --- not even a
polynomial one --- is incurred. -/
theorem IndependentSet.card_le_pow_of_cover
    {T : (∀ i, κ i) → K} {P : ι → (∀ i, κ i) → K}
    (hcover : ∀ p, T p ≠ 0 → ∃ j, P j p ≠ 0)
    {t : ι → ℝ} (ht : ∀ j, 0 ≤ t j)
    (hmeasure : ∀ j, ((coordinateMeasure (P j) : ℕ) : ℝ) ≤ t j ^ 3)
    {n : ℕ} {S : Finset (∀ i, Fin n → κ i)}
    (hS : IndependentSet (coordinatePower T n) S) :
    (S.card : ℝ) ≤ (∑ j, t j) ^ n := by
  classical
  set cls : (Fin n → ι) → Finset (∀ i, Fin n → κ i) :=
    fun w ↦ S.filter fun p ↦ ∀ pos, P (w pos) (fun i ↦ p i pos) ≠ 0 with hclsdef
  -- Every element of `S` gets a colour word.
  have hcov : S ⊆ Finset.univ.biUnion cls := by
    intro p hp
    have hletter : ∀ pos : Fin n, T (fun i ↦ p i pos) ≠ 0 := by
      intro pos h0
      refine hS.ne_zero p hp ?_
      rw [coordinatePower_apply]
      exact Finset.prod_eq_zero (Finset.mem_univ pos) h0
    choose w hw using fun pos ↦ hcover _ (hletter pos)
    exact Finset.mem_biUnion.mpr ⟨w, Finset.mem_univ w, Finset.mem_filter.mpr ⟨hp, hw⟩⟩
  -- Each colour class is small.
  have hclass : ∀ w : Fin n → ι, ((cls w).card : ℝ) ≤ ∏ pos, t (w pos) := by
    intro w
    have hsubS : cls w ⊆ S := Finset.filter_subset _ _
    have hleg : ∀ i : Leg,
        (cls w).card ≤ ∏ pos : Fin n, (minimalLegSet (P (w pos)) i).card := by
      intro i
      have hcard : (cls w).card ≤
          (Fintype.piFinset fun pos : Fin n ↦ minimalLegSet (P (w pos)) i).card := by
        refine Finset.card_le_card_of_injOn (fun p ↦ p i) (fun p hp ↦ ?_) ?_
        · have hp' := (Finset.mem_filter.mp (Finset.mem_coe.mp hp)).2
          exact Finset.mem_coe.mpr
            (Fintype.mem_piFinset.mpr fun pos ↦ mem_minimalLegSet_of_ne_zero (hp' pos) i)
        · exact (hS.injOn i).mono (Finset.coe_subset.mpr hsubS)
      simpa [Fintype.card_piFinset] using hcard
    have hcube : ((cls w).card : ℝ) ^ 3 ≤ (∏ pos, t (w pos)) ^ 3 := by
      calc ((cls w).card : ℝ) ^ 3
          = ∏ _i : Leg, ((cls w).card : ℝ) := by
            rw [Finset.prod_const, Finset.card_univ]
            rfl
        _ ≤ ∏ i : Leg, ∏ pos : Fin n, ((minimalLegSet (P (w pos)) i).card : ℝ) := by
            refine Finset.prod_le_prod (fun i _ ↦ by positivity) fun i _ ↦ ?_
            exact_mod_cast hleg i
        _ = ∏ pos : Fin n, ((coordinateMeasure (P (w pos)) : ℕ) : ℝ) := by
            rw [Finset.prod_comm]
            refine Finset.prod_congr rfl fun pos _ ↦ ?_
            rw [coordinateMeasure, Nat.cast_prod]
        _ ≤ ∏ pos : Fin n, t (w pos) ^ 3 :=
            Finset.prod_le_prod (fun pos _ ↦ by positivity)
              fun pos _ ↦ hmeasure (w pos)
        _ = (∏ pos : Fin n, t (w pos)) ^ 3 := Finset.prod_pow _ _ _
    exact le_of_pow_le_pow_left₀ (by norm_num)
      (Finset.prod_nonneg fun pos _ ↦ ht (w pos)) hcube
  -- Sum over the colour words.
  have hexpand : ∑ w : Fin n → ι, ∏ pos : Fin n, t (w pos) = (∑ j, t j) ^ n := by
    have h := Finset.prod_univ_sum (fun _ : Fin n ↦ (Finset.univ : Finset ι)) fun _ j ↦ t j
    rw [Fintype.piFinset_univ] at h
    rw [← h, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  calc (S.card : ℝ) ≤ (((Finset.univ.biUnion cls).card : ℕ) : ℝ) := by
        exact_mod_cast Finset.card_le_card hcov
    _ ≤ ((∑ w : Fin n → ι, (cls w).card : ℕ) : ℝ) := by
        exact_mod_cast Finset.card_biUnion_le
    _ = ∑ w : Fin n → ι, ((cls w).card : ℝ) := by push_cast; ring
    _ ≤ ∑ w : Fin n → ι, ∏ pos : Fin n, t (w pos) := Finset.sum_le_sum fun w _ ↦ hclass w
    _ = (∑ j, t j) ^ n := hexpand

/-- **The partition bound at a fixed Kronecker power**: if the support of `T` is covered by the
parts `P j`, then `I(T^{⊗n}) ≤ (∑ⱼ μ(Pⱼ)^{1/3})^n` for every `n`.

Proof sketch: apply `IndependentSet.card_le_pow_of_cover` to a largest independent set of
`T^{⊗n}`, with `t j = μ(P j)^{1/3}`, for which the hypothesis `μ(P j) ≤ t j³` holds with
equality. -/
theorem independenceNumber_coordinatePower_le_pow_sum_rpow_coordinateMeasure_of_cover
    {T : (∀ i, κ i) → K} {P : ι → (∀ i, κ i) → K}
    (hcover : ∀ p, T p ≠ 0 → ∃ j, P j p ≠ 0) (n : ℕ) :
    ((independenceNumber (coordinatePower T n) : ℕ) : ℝ) ≤
      (∑ j, ((coordinateMeasure (P j) : ℕ) : ℝ) ^ ((3 : ℝ)⁻¹)) ^ n := by
  obtain ⟨S, hS, hcard⟩ := exists_independentSet_card_eq (coordinatePower T n)
  rw [← hcard]
  exact hS.card_le_pow_of_cover hcover (fun j ↦ Real.rpow_nonneg (by positivity) _)
    fun j ↦ (rpow_inv_three_pow_three (x := ((coordinateMeasure (P j) : ℕ) : ℝ))
      (by positivity)).ge

/-- **AVW Theorem 5.3, in its covering form.**  If every term of `T` is a term of one of the parts
`P j` --- in particular if the `P j` are the parts of a partition of the support of `T` --- then

```
Ī(T) ≤ ∑ⱼ μ(Pⱼ)^{1/3}.
```

Neither disjointness of the parts nor the equation `T = ∑ⱼ Pⱼ` is used; see
`asymptoticIndependenceNumber_le_sum_rpow_coordinateMeasure` for AVW's literal hypothesis.

Proof sketch: the previous theorem bounds `I(T^{⊗n})` by the `n`th power of the right-hand side
for every `n`, and `Ī` is the supremum of the `n`th roots of `I(T^{⊗n})`. -/
theorem asymptoticIndependenceNumber_le_sum_rpow_coordinateMeasure_of_cover
    {T : (∀ i, κ i) → K} {P : ι → (∀ i, κ i) → K}
    (hcover : ∀ p, T p ≠ 0 → ∃ j, P j p ≠ 0) :
    asymptoticIndependenceNumber T ≤
      ∑ j, ((coordinateMeasure (P j) : ℕ) : ℝ) ^ ((3 : ℝ)⁻¹) :=
  asymptoticIndependenceNumber_le_of_pow
    (Finset.sum_nonneg fun j _ ↦ Real.rpow_nonneg (by positivity) _)
    fun n ↦ independenceNumber_coordinatePower_le_pow_sum_rpow_coordinateMeasure_of_cover
      hcover n

/-- **AVW Theorem 5.3.**  If the coefficient table `T` is partitioned into `k` parts,
`T = P₁ + P₂ + ⋯ + P_k`, then

```
Ī(T) ≤ ∑ᵢ μ(Pᵢ)^{1/3}.
```

Proof sketch: a term of a sum of tables is a term of at least one summand, so the parts cover the
support of `T` and the covering form applies. -/
theorem asymptoticIndependenceNumber_le_sum_rpow_coordinateMeasure
    {T : (∀ i, κ i) → K} {P : ι → (∀ i, κ i) → K} (hT : T = ∑ j, P j) :
    asymptoticIndependenceNumber T ≤
      ∑ j, ((coordinateMeasure (P j) : ℕ) : ℝ) ^ ((3 : ℝ)⁻¹) := by
  refine asymptoticIndependenceNumber_le_sum_rpow_coordinateMeasure_of_cover fun p hp ↦ ?_
  by_contra hcon
  refine hp ?_
  rw [hT]
  simp only [Finset.sum_apply]
  refine Finset.sum_eq_zero fun j _ ↦ ?_
  by_contra hj
  exact hcon ⟨j, hj⟩

end Partition

end AlgebraicComplexity.Tensor
