/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Tensor.AsymptoticIndependenceNumber
import AlgebraicComplexity.Tensor.Monomial

/-!
# Minimum-weight monomial degenerations and the asymptotic independence number

This file proves the one lemma that lets *monomial degenerations* --- which are not zeroing outs,
and under which the finite independence number is **not** monotone --- feed the asymptotic
independence number:

> J. Alman and V. Vassilevska Williams, *Limits on All Known (and Some Unknown) Approaches to
> Matrix Multiplication*, arXiv:1810.08671, Lemma 4.3 (a special case of
> J. Alman and V. Vassilevska Williams, ITCS 2018, Lemma 5.1) and Corollary 4.1.

AVW's statement: *if `A` has a monomial degeneration into `f` independent triples, then `A^{⊗n}`
has a zeroing out into `Ω(f^n / n²)` independent triples*; hence `Ī(A) ≥ f`.

## The set-up transcribed

A monomial degeneration in the combinatorial form of `Tensor/Monomial.lean` is given by
`ℕ`-valued weights `w i : κ i → ℕ` on the variables of each leg and a threshold `d` such that
every *occurring* term `p` of the coefficient table `A` has total weight
`monomialTotalWeight w p = w_X(p_X) + w_Y(p_Y) + w_Z(p_Z)` at least `d`.  (AVW use `ℤ`-valued
weights with threshold `0`; shifting each leg weight by a constant and taking `d` to be the sum of
the three shifts is the same data, see `BARRIER_FRAMEWORK.md` §2.1.)  The *degenerated* table is
the minimum-weight part

```
minimumWeightPart w d A p = if monomialTotalWeight w p = d then A p else 0,
```

and `monomialDegenerates_coordinateTensor_minimumWeightPart` proves that `coordinateTensor A`
really does monomially degenerate onto `coordinateTensor (minimumWeightPart w d A)` in the sense
of `Tensor.MonomialDegenerates`.

**The hypothesis of the main theorem is about the degenerated table, not about `A`.**  "The
minimum-weight triples are independent" must be read as: the whole support of
`minimumWeightPart w d A` is an `IndependentSet` *of that table*.  It is in general false that the
same set is an `IndependentSet` of `A`: the closure clause of `IndependentSet` can fail, because a
heavier term of `A` may use only variables occurring in minimum-weight terms.  A formal witness
lives in `MatrixMultiplication/IndependentDiagonal.lean`
(`not_independentSet_mmCoefficients_mmMinWeightSupport`).

## Main results

* `monomialDegenerates_coordinateTensor_minimumWeightPart`: the bridge to `Tensor/Monomial.lean`.
* `pow_card_le_mul_independenceNumber_coordinatePower` (**AVW Lemma 4.3**): if the support of
  `minimumWeightPart w d A` is an independent set `S`, then for every `n`

  ```
  |S|^n ≤ (n·M_X + 1)·(n·M_Y + 1) · I(A^{⊗n}),
  ```

  where `M_i = weightBound w i` is the largest weight occurring on leg `i`.  `S` may be any
  independent set of the degenerated table, not only its whole support, which is what makes
  Corollary 4.2 below available.
* `card_le_asymptoticIndependenceNumber` (**AVW Corollary 4.1**): consequently
  `|S| ≤ Ī(A)`.
* `minimumWeightPart_coordinatePowerWeight`: minimum-weight parts commute with Kronecker powers,
  `minimumWeightPart (summed word weights) (m·d) (A^{⊗m}) = (minimumWeightPart w d A)^{⊗m}`.
* `asymptoticIndependenceNumber_minimumWeightPart_le` (**AVW Corollary 4.2**): `Ī` *is* monotone
  under monomial degeneration, `Ī(minimumWeightPart w d A) ≤ Ī(A)` --- asymptotically only.

## The proof, and the shape of the polynomial loss

Fix `n`.  A triple of words surviving in `A^{⊗n}` has total weight
`∑_k monomialTotalWeight w (p·k) ≥ n·d`, with equality exactly when every one of the `n` letters is
a minimum-weight term.  Zero out, on leg `X`, all words of `X`-weight different from `α`, on leg
`Y` all words of `Y`-weight different from `β`, and on leg `Z` all words whose `Z`-weight does not
make the total exactly `n·d` (`weightClassSet`).  Every triple surviving this zeroing out then has
total weight exactly `n·d`, so all of its letters are minimum-weight terms; that is, the surviving
support is contained in the support of `(minimumWeightPart w d A)^{⊗n}`, on which
`independentSet_powerIndependentSet` provides an independent set, and
`IndependentSet.of_subSupport` restricts it.  Every element of `S^n` survives for exactly one
pair `(α, β)`, so the `S^n` are covered by the classes and pigeonhole gives the count.

The number of classes is where the honest statement differs from the printed one.  AVW write
`Ω(f^n/n²)`, with an implicit constant depending on `A`: the `X`-weight of an `n`-letter word runs
over `0, …, n·M_X`, so there are `(n·M_X + 1)·(n·M_Y + 1)` classes, not `(n+1)²`.  The constant is
recorded explicitly above rather than hidden, and it is harmless: a fixed polynomial loss does not
move an exponential rate, which is exactly what
`Growth.le_exponentialRate_of_pow_succ_le_mul_polynomial` says, so Corollary 4.1 is unaffected.

## Deliberately not proved

* **No finite statement `I(minimumWeightPart w d A) ≤ I(A)`.**  It is false in general: `I` is not
  monotone under monomial degeneration, and AVW never claim it (`BARRIER_FRAMEWORK.md` §2.3).  Only
  the asymptotic consequence above is available.
* Corollary 4.2 is proved only in the *minimum-weight* formulation above, which is the
  combinatorial content of a monomial degeneration; it is not restated for the relation
  `Tensor.MonomialDegenerates`, whose certificates carry a leading term but not the identification
  of that leading term with a minimum-weight part.
* The named applications (Strassen's weights on a matrix-multiplication tensor, AVW Lemma 4.2 and
  Lemma 4.4) belong one layer up, with the matrix-multiplication tensor; this module is layer 1 and
  must not import them.

## Position in the library

Layer 1.  It imports `Tensor/AsymptoticIndependenceNumber.lean` for `Ī` and its identification with
`Growth.exponentialRate`, and `Tensor/Monomial.lean` for the monomial-degeneration certificate
former.  It mentions no named matrix-multiplication construction and no numerical bound.
-/

namespace AlgebraicComplexity.Tensor

universe u v w

namespace MonomialIndependence

variable {K : Type u} [CommSemiring K] {κ : Leg → Type v}
variable [∀ i, Fintype (κ i)] [∀ i, DecidableEq (κ i)]

/-! ## The minimum-weight part of a coefficient table -/

/-- The **minimum-weight part** of a coefficient table for the weights `w` and threshold `d`: the
sub-table supported on the terms of total weight exactly `d`.  When every occurring term of `A` has
weight at least `d` this is the target of the monomial degeneration determined by `w`
(`monomialDegenerates_coordinateTensor_minimumWeightPart`). -/
def minimumWeightPart (w : ∀ i, κ i → ℕ) (d : ℕ) (A : (∀ i, κ i) → K) : (∀ i, κ i) → K :=
  fun p ↦ if monomialTotalWeight w p = d then A p else 0

omit [∀ i, Fintype (κ i)] [∀ i, DecidableEq (κ i)] in
/-- On a term of minimum weight the minimum-weight part agrees with the original table. -/
theorem minimumWeightPart_of_weight {w : ∀ i, κ i → ℕ} {d : ℕ} {A : (∀ i, κ i) → K}
    {p : ∀ i, κ i} (h : monomialTotalWeight w p = d) : minimumWeightPart w d A p = A p :=
  if_pos h

omit [∀ i, Fintype (κ i)] [∀ i, DecidableEq (κ i)] in
/-- A term of the minimum-weight part has weight exactly `d` and is a term of the original
table. -/
theorem minimumWeightPart_ne_zero {w : ∀ i, κ i → ℕ} {d : ℕ} {A : (∀ i, κ i) → K}
    {p : ∀ i, κ i} (h : minimumWeightPart w d A p ≠ 0) :
    monomialTotalWeight w p = d ∧ A p ≠ 0 := by
  by_cases hc : monomialTotalWeight w p = d
  · rw [minimumWeightPart, if_pos hc] at h
    exact ⟨hc, h⟩
  · rw [minimumWeightPart, if_neg hc] at h
    exact absurd rfl h

/-- **The bridge to `Tensor/Monomial.lean`.**  If every occurring term of `A` has total weight at
least `d`, then the abstract tensor of `A` monomially degenerates onto the abstract tensor of its
minimum-weight part, with the very weights `w` and threshold `d`.

Proof sketch: `coordinateTensor_eq_sum` writes both tables as sums of scaled standard-basis pure
tensors indexed by all triples, and
`monomialDegenerates_fintype_sum_basis_of_support` --- the support form of the certificate former,
which only constrains the weights of terms with nonzero coefficient --- produces the certificate,
its leading term being the sum of the summands of weight exactly `d`. -/
theorem monomialDegenerates_coordinateTensor_minimumWeightPart
    (w : ∀ i, κ i → ℕ) (d : ℕ) (A : (∀ i, κ i) → K)
    (hmin : ∀ p, A p ≠ 0 → d ≤ monomialTotalWeight w p) :
    MonomialDegenerates (coordinateTensor A) (coordinateTensor (minimumWeightPart w d A)) := by
  classical
  have hsrc := coordinateTensor_eq_sum A
  have htgt : coordinateTensor (minimumWeightPart w d A) =
      ∑ p : (∀ i, κ i), if monomialTotalWeight w p = d then
        A p • pure (K := K) (fun i ↦ Pi.single (p i) (1 : K)) else 0 := by
    rw [coordinateTensor_eq_sum]
    refine Finset.sum_congr rfl fun p _ ↦ ?_
    by_cases hc : monomialTotalWeight w p = d <;>
      simp [minimumWeightPart, hc]
  rw [hsrc, htgt]
  exact monomialDegenerates_fintype_sum_basis_of_support w A (fun p ↦ p) d hmin

/-! ## Weights of words -/

/-- The largest weight occurring on leg `i`.  It is the constant hidden in AVW's `O(n²)`. -/
def weightBound (w : ∀ i, κ i → ℕ) (i : Leg) : ℕ := Finset.univ.sup (w i)

omit [∀ i, DecidableEq (κ i)] in
/-- Every variable weighs at most the leg bound. -/
theorem le_weightBound (w : ∀ i, κ i → ℕ) (i : Leg) (a : κ i) : w i a ≤ weightBound w i :=
  Finset.le_sup (Finset.mem_univ a)

/-- The weight of an `n`-letter word on leg `i`: the sum of the weights of its letters.  These are
the leg weights of the Kronecker power `A^{⊗n}`. -/
def coordinatePowerWeight (w : ∀ i, κ i → ℕ) (n : ℕ) : ∀ i, (Fin n → κ i) → ℕ :=
  fun i q ↦ ∑ k : Fin n, w i (q k)

omit [∀ i, Fintype (κ i)] [∀ i, DecidableEq (κ i)] in
/-- The total weight of a triple of words is the sum of the total weights of its `n` letters. -/
theorem monomialTotalWeight_coordinatePowerWeight (w : ∀ i, κ i → ℕ) (n : ℕ)
    (p : ∀ i, Fin n → κ i) :
    monomialTotalWeight (coordinatePowerWeight w n) p =
      ∑ k : Fin n, monomialTotalWeight w fun i ↦ p i k := by
  simp only [monomialTotalWeight, coordinatePowerWeight]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]

omit [∀ i, DecidableEq (κ i)] in
/-- An `n`-letter word weighs at most `n` times the leg bound. -/
theorem coordinatePowerWeight_le (w : ∀ i, κ i → ℕ) (n : ℕ) (i : Leg) (q : Fin n → κ i) :
    coordinatePowerWeight w n i q ≤ n * weightBound w i := by
  calc coordinatePowerWeight w n i q ≤ ∑ _k : Fin n, weightBound w i :=
        Finset.sum_le_sum fun k _ ↦ le_weightBound w i (q k)
    _ = n * weightBound w i := by simp

/-- If `n` numbers each at least `d` sum to `n · d`, each of them is `d`. -/
private theorem eq_of_sum_eq_mul {n : ℕ} {f : Fin n → ℕ} {d : ℕ}
    (hge : ∀ k, d ≤ f k) (hsum : (∑ k : Fin n, f k) = n * d) (k : Fin n) : f k = d := by
  have hconst : (∑ _k : Fin n, d) = n * d := by simp
  have h := (Finset.sum_eq_sum_iff_of_le (fun i _ ↦ hge i)).mp (by rw [hconst, hsum])
  exact (h k (Finset.mem_univ k)).symm

/-! ## Weight classes and the pigeonhole -/

/-- The variables of leg `i` that survive the zeroing out to the weight class `(α, β)` of the
`n`th Kronecker power: on leg `X` the words of weight `α`, on leg `Y` the words of weight `β`, and
on leg `Z` the words whose weight completes the total to `n · d`.

The `Z` condition is written as the equation `α + β + weight = n · d` rather than as an assignment
`weight = n·d − α − β`, so that no truncated natural subtraction occurs and the class is empty
whenever `α + β` already exceeds `n · d`. -/
def weightClassSet (w : ∀ i, κ i → ℕ) (n d α β : ℕ) : ∀ i, Finset (Fin n → κ i)
  | .X => Finset.univ.filter fun q ↦ coordinatePowerWeight w n Leg.X q = α
  | .Y => Finset.univ.filter fun q ↦ coordinatePowerWeight w n Leg.Y q = β
  | .Z => Finset.univ.filter fun q ↦ α + β + coordinatePowerWeight w n Leg.Z q = n * d

omit [∀ i, DecidableEq (κ i)] in
/-- A triple of words all of whose legs survive the zeroing out to the class `(α, β)` has total
weight exactly `n · d`. -/
theorem monomialTotalWeight_of_mem_weightClassSet {w : ∀ i, κ i → ℕ} {n d α β : ℕ}
    {p : ∀ i, Fin n → κ i} (h : ∀ i, p i ∈ weightClassSet w n d α β i) :
    monomialTotalWeight (coordinatePowerWeight w n) p = n * d := by
  have hX : coordinatePowerWeight w n Leg.X (p Leg.X) = α := by
    simpa [weightClassSet] using h Leg.X
  have hY : coordinatePowerWeight w n Leg.Y (p Leg.Y) = β := by
    simpa [weightClassSet] using h Leg.Y
  have hZ : α + β + coordinatePowerWeight w n Leg.Z (p Leg.Z) = n * d := by
    simpa [weightClassSet] using h Leg.Z
  rw [monomialTotalWeight, hX, hY]
  exact hZ

end MonomialIndependence

open MonomialIndependence in
/-- **AVW Lemma 4.3 (= Alman--Vassilevska Williams ITCS 2018, Lemma 5.1).**  Let `w` be
`ℕ`-valued leg weights and `d` a threshold such that every occurring term of the coefficient table
`A` has total weight at least `d`, so that `A` monomially degenerates onto its minimum-weight part
`D = minimumWeightPart w d A` (`monomialDegenerates_coordinateTensor_minimumWeightPart`).  If the
support of `D` is an independent set `S` of `D` --- of size `f = |S|` --- then for every `n` the
`n`th Kronecker power of `A` has a zeroing out to an independent set of size at least
`f^n / ((n·M_X + 1)·(n·M_Y + 1))`, where `M_i` is the largest weight on leg `i`:

```
f^n ≤ (n·M_X + 1)·(n·M_Y + 1) · I(A^{⊗n}).
```

Note that the hypothesis is independence **in `D`**, not in `A`; see the module header.

Proof sketch.  Fix `n` and consider the `(n·M_X+1)·(n·M_Y+1)` weight classes `(α, β)` of
`weightClassSet`, and for each of them the zeroing out of `A^{⊗n}` to that class.

*Every surviving triple lies in the support of `D^{⊗n}`.*  Its total weight is `n·d`
(`monomialTotalWeight_of_mem_weightClassSet`) and equals the sum of the total weights of its `n`
letters (`monomialTotalWeight_coordinatePowerWeight`), each of which is at least `d` because the
letters are terms of `A`; so each letter has weight exactly `d` (`eq_of_sum_eq_mul`) and is
therefore a term of `D`.

*Hence each class carries an independent set.*  `independentSet_powerIndependentSet` makes `S^n`
an independent set of `D^{⊗n}`, and `IndependentSet.of_subSupport` --- the *true* neighbour of the
false sub-support monotonicity of `I` --- restricts it to the surviving part of the class.  Since
zeroing outs cannot increase the independence number, each class contributes at most `I(A^{⊗n})`.

*The classes cover `S^n`.*  A triple of words with all letters in `S` has all letters of weight
`d`, so taking `α` and `β` to be its own `X`- and `Y`-weights (both at most `n·M`) puts it in that
class, where it survives because a product of nonzero coefficients is nonzero.  Pigeonhole over the
classes finishes the count. -/
theorem pow_card_le_mul_independenceNumber_coordinatePower
    {K : Type u} [CommSemiring K] [NoZeroDivisors K] [Nontrivial K] {κ : Leg → Type v}
    [∀ i, Fintype (κ i)] [∀ i, DecidableEq (κ i)]
    {A : (∀ i, κ i) → K} (w : ∀ i, κ i → ℕ) (d : ℕ)
    (hmin : ∀ p, A p ≠ 0 → d ≤ monomialTotalWeight w p)
    {S : Finset (∀ i, κ i)} (hS : IndependentSet (minimumWeightPart w d A) S) (n : ℕ) :
    S.card ^ n ≤
      (n * weightBound w Leg.X + 1) * (n * weightBound w Leg.Y + 1) *
        independenceNumber (coordinatePower A n) := by
  classical
  set D := minimumWeightPart w d A with hD
  -- the independent set of the power of the degenerated table
  have hPind : IndependentSet (coordinatePower D n) (powerIndependentSet S n) :=
    independentSet_powerIndependentSet hS n
  -- the zeroing out to a weight class
  set cls : ℕ → ℕ → (∀ i, Fin n → κ i) → K :=
    fun α β ↦ coordinateZeroOut (coordinatePower A n) (weightClassSet w n d α β) with hcls
  -- surviving triples of a class are terms of the power of the degenerated table
  have hsub : ∀ α β, ∀ p : ∀ i, Fin n → κ i,
      cls α β p ≠ 0 → coordinatePower D n p ≠ 0 := by
    intro α β p hp
    obtain ⟨hne, hmem⟩ := coordinateZeroOut_ne_zero hp
    have hletters : ∀ k : Fin n, A (fun i ↦ p i k) ≠ 0 := by
      intro k
      rw [coordinatePower_apply] at hne
      exact Finset.prod_ne_zero_iff.mp hne k (Finset.mem_univ k)
    have hsum : (∑ k : Fin n, monomialTotalWeight w fun i ↦ p i k) = n * d := by
      rw [← monomialTotalWeight_coordinatePowerWeight]
      exact monomialTotalWeight_of_mem_weightClassSet hmem
    have hexact : ∀ k : Fin n, (monomialTotalWeight w fun i ↦ p i k) = d :=
      eq_of_sum_eq_mul (fun k ↦ hmin _ (hletters k)) hsum
    rw [coordinatePower_apply]
    refine Finset.prod_ne_zero_iff.mpr fun k _ ↦ ?_
    rw [hD, minimumWeightPart_of_weight (hexact k)]
    exact hletters k
  -- the part of `S^n` surviving in a class
  set part : ℕ → ℕ → Finset (∀ i, Fin n → κ i) :=
    fun α β ↦ (powerIndependentSet S n).filter fun p ↦ cls α β p ≠ 0 with hpart
  have hpartCard : ∀ α β, (part α β).card ≤ independenceNumber (coordinatePower A n) := by
    intro α β
    have hind : IndependentSet (cls α β) (part α β) :=
      hPind.of_subSupport (hsub α β) fun p ↦ by simp [hpart]
    calc (part α β).card ≤ independenceNumber (cls α β) := hind.card_le_independenceNumber
      _ ≤ independenceNumber (coordinatePower A n) :=
          independenceNumber_coordinateZeroOut_le _ _
  -- the classes cover `S^n`
  set classes : Finset (ℕ × ℕ) :=
    Finset.range (n * weightBound w Leg.X + 1) ×ˢ Finset.range (n * weightBound w Leg.Y + 1)
    with hclasses
  have hcover : powerIndependentSet S n ⊆ classes.biUnion fun ab ↦ part ab.1 ab.2 := by
    intro p hp
    have hletter : ∀ k : Fin n, (fun i ↦ p i k) ∈ S := mem_powerIndependentSet.mp hp
    have hDne : ∀ k : Fin n, D (fun i ↦ p i k) ≠ 0 := fun k ↦ hS.ne_zero _ (hletter k)
    have hweight : ∀ k : Fin n, (monomialTotalWeight w fun i ↦ p i k) = d := fun k ↦
      (minimumWeightPart_ne_zero (hDne k)).1
    have hAne : ∀ k : Fin n, A (fun i ↦ p i k) ≠ 0 := fun k ↦
      (minimumWeightPart_ne_zero (hDne k)).2
    set α := coordinatePowerWeight w n Leg.X (p Leg.X) with hα
    set β := coordinatePowerWeight w n Leg.Y (p Leg.Y) with hβ
    have htotal : monomialTotalWeight (coordinatePowerWeight w n) p = n * d := by
      rw [monomialTotalWeight_coordinatePowerWeight]
      simp [hweight, mul_comm]
    have hmem : ∀ i, p i ∈ weightClassSet w n d α β i := by
      intro i
      cases i with
      | X => simp [weightClassSet, hα]
      | Y => simp [weightClassSet, hβ]
      | Z =>
          have : α + β + coordinatePowerWeight w n Leg.Z (p Leg.Z) = n * d := by
            rw [← htotal, monomialTotalWeight]
          simpa [weightClassSet] using this
    have hclsne : cls α β p ≠ 0 := by
      show coordinateZeroOut (coordinatePower A n) (weightClassSet w n d α β) p ≠ 0
      rw [coordinateZeroOut_of_mem hmem, coordinatePower_apply]
      exact Finset.prod_ne_zero_iff.mpr fun k _ ↦ hAne k
    refine Finset.mem_biUnion.mpr ⟨(α, β), ?_, ?_⟩
    · refine Finset.mem_product.mpr ⟨?_, ?_⟩
      · exact Finset.mem_range.mpr (Nat.lt_succ_of_le (coordinatePowerWeight_le w n Leg.X _))
      · exact Finset.mem_range.mpr (Nat.lt_succ_of_le (coordinatePowerWeight_le w n Leg.Y _))
    · exact Finset.mem_filter.mpr ⟨hp, hclsne⟩
  -- pigeonhole
  calc S.card ^ n = (powerIndependentSet S n).card := (card_powerIndependentSet S n).symm
    _ ≤ (classes.biUnion fun ab ↦ part ab.1 ab.2).card := Finset.card_le_card hcover
    _ ≤ ∑ ab ∈ classes, (part ab.1 ab.2).card := Finset.card_biUnion_le
    _ ≤ classes.card * independenceNumber (coordinatePower A n) := by
        simpa [smul_eq_mul] using
          Finset.sum_le_card_nsmul classes (fun ab ↦ (part ab.1 ab.2).card)
            (independenceNumber (coordinatePower A n)) fun ab _ ↦ hpartCard ab.1 ab.2
    _ = (n * weightBound w Leg.X + 1) * (n * weightBound w Leg.Y + 1) *
          independenceNumber (coordinatePower A n) := by
        rw [hclasses, Finset.card_product, Finset.card_range, Finset.card_range]

open MonomialIndependence in
/-- **AVW Corollary 4.1.**  If the coefficient table `A` monomially degenerates, through
`ℕ`-valued weights `w` and threshold `d`, onto a minimum-weight part whose support is an
independent set `S`, then `|S| ≤ Ī(A)`.

This is the only way monomial degenerations enter the barrier framework: no finite comparison of
independence numbers is available, but the asymptotic independence number does see the degenerated
table.

Proof sketch: `pow_card_le_mul_independenceNumber_coordinatePower` gives
`|S|^{n+1} ≤ C · (n+2)² · I(A^{⊗(n+1)})` with the fixed constant
`C = (M_X + 1)·(M_Y + 1)`, because `(n+1)·M + 1 ≤ (n+2)·(M+1)`.  A fixed polynomial loss does not
move an exponential rate, which is
`Growth.le_exponentialRate_of_pow_succ_le_mul_polynomial`; and `Ī` *is* that exponential rate by
`asymptoticIndependenceNumber_eq_exponentialRate`. -/
theorem card_le_asymptoticIndependenceNumber
    {K : Type u} [CommSemiring K] [NoZeroDivisors K] [Nontrivial K] {κ : Leg → Type v}
    [∀ i, Fintype (κ i)] [∀ i, DecidableEq (κ i)]
    {A : (∀ i, κ i) → K} (w : ∀ i, κ i → ℕ) (d : ℕ)
    (hmin : ∀ p, A p ≠ 0 → d ≤ monomialTotalWeight w p)
    {S : Finset (∀ i, κ i)} (hS : IndependentSet (minimumWeightPart w d A) S) :
    (S.card : ℝ) ≤ asymptoticIndependenceNumber A := by
  classical
  set MX := weightBound w Leg.X with hMX
  set MY := weightBound w Leg.Y with hMY
  rw [asymptoticIndependenceNumber_eq_exponentialRate]
  refine Growth.le_exponentialRate_of_pow_succ_le_mul_polynomial
    (exists_exponentialBound_independenceNumberPowerSequence A)
    (C := ((MX + 1) * (MY + 1) : ℕ)) (k := 2) (by positivity) fun n ↦ ?_
  have hmain := pow_card_le_mul_independenceNumber_coordinatePower w d hmin hS (n + 1)
  have hstep : ((n + 1) * MX + 1) * ((n + 1) * MY + 1) ≤ (MX + 1) * (MY + 1) * (n + 2) ^ 2 := by
    have h1 : (n + 1) * MX + 1 ≤ (MX + 1) * (n + 2) := by nlinarith
    have h2 : (n + 1) * MY + 1 ≤ (MY + 1) * (n + 2) := by nlinarith
    calc ((n + 1) * MX + 1) * ((n + 1) * MY + 1) ≤ ((MX + 1) * (n + 2)) * ((MY + 1) * (n + 2)) :=
          Nat.mul_le_mul h1 h2
      _ = (MX + 1) * (MY + 1) * (n + 2) ^ 2 := by ring
  have hnat : S.card ^ (n + 1) ≤
      (MX + 1) * (MY + 1) * (n + 2) ^ 2 * independenceNumberPowerSequence A (n + 1) := by
    refine hmain.trans ?_
    exact Nat.mul_le_mul_right _ hstep
  have hreal : ((S.card : ℝ)) ^ (n + 1) ≤
      (((MX + 1) * (MY + 1) : ℕ) : ℝ) * (((n + 2 : ℕ) : ℝ)) ^ 2 *
        ((independenceNumberPowerSequence A (n + 1) : ℕ) : ℝ) := by
    have := (Nat.cast_le (α := ℝ)).mpr hnat
    push_cast at this ⊢
    linarith
  exact hreal


open MonomialIndependence in
/-- **Minimum-weight parts commute with Kronecker powers.**  Weighting the `m`th Kronecker power of
`A` by the summed word weights, with threshold `m·d`, produces exactly the `m`th Kronecker power of
the minimum-weight part of `A`.

Proof sketch: if all `m` letters of a triple have weight `d` both sides are the product of the `m`
coefficients of `A`.  Otherwise the right-hand side vanishes at the offending letter, and so does
the left-hand side: either its total weight misses `m·d`, or all its letters are terms of `A`, hence
of weight at least `d`, and a sum of `m` such numbers equal to `m·d` forces every one of them to be
`d` (`eq_of_sum_eq_mul`) --- contradicting the choice of the offending letter. -/
theorem minimumWeightPart_coordinatePowerWeight
    {K : Type u} [CommSemiring K] [NoZeroDivisors K] [Nontrivial K] {κ : Leg → Type v}
    [∀ i, Fintype (κ i)] [∀ i, DecidableEq (κ i)]
    {A : (∀ i, κ i) → K} (w : ∀ i, κ i → ℕ) (d : ℕ)
    (hmin : ∀ p, A p ≠ 0 → d ≤ monomialTotalWeight w p) (m : ℕ) :
    minimumWeightPart (coordinatePowerWeight w m) (m * d) (coordinatePower A m) =
      coordinatePower (minimumWeightPart w d A) m := by
  funext p
  by_cases hall : ∀ k : Fin m, (monomialTotalWeight w fun i ↦ p i k) = d
  · have hsum : monomialTotalWeight (coordinatePowerWeight w m) p = m * d := by
      rw [monomialTotalWeight_coordinatePowerWeight]
      simp [hall]
    rw [minimumWeightPart_of_weight hsum, coordinatePower_apply, coordinatePower_apply]
    exact Finset.prod_congr rfl fun k _ ↦ (minimumWeightPart_of_weight (hall k)).symm
  · rw [not_forall] at hall
    obtain ⟨k₀, hk₀⟩ := hall
    have hRHS : coordinatePower (minimumWeightPart w d A) m p = 0 := by
      rw [coordinatePower_apply]
      refine Finset.prod_eq_zero (Finset.mem_univ k₀) ?_
      simp [minimumWeightPart, hk₀]
    rw [hRHS]
    by_cases hcond : monomialTotalWeight (coordinatePowerWeight w m) p = m * d
    · rw [minimumWeightPart_of_weight hcond, coordinatePower_apply]
      by_contra hne
      have hletters : ∀ k : Fin m, A (fun i ↦ p i k) ≠ 0 := fun k ↦
        Finset.prod_ne_zero_iff.mp hne k (Finset.mem_univ k)
      have hsum : (∑ k : Fin m, monomialTotalWeight w fun i ↦ p i k) = m * d := by
        rw [← monomialTotalWeight_coordinatePowerWeight]
        exact hcond
      exact hk₀ (eq_of_sum_eq_mul (fun k ↦ hmin _ (hletters k)) hsum k₀)
    · rw [minimumWeightPart, if_neg hcond]

open MonomialIndependence in
/-- **AVW Corollary 4.2.**  The asymptotic independence number is monotone under monomial
degeneration: the minimum-weight part of `A` has asymptotic independence number at most that
of `A`.

Contrast with the finite level, where nothing of the sort holds: `I` is not monotone under
monomial degeneration (see the module header).

Proof sketch: fix `m ≥ 1` and a largest independent set `S` of `D^{⊗m}`, where
`D = minimumWeightPart w d A`.  By `minimumWeightPart_coordinatePowerWeight`, `D^{⊗m}` *is* the
minimum-weight part of `A^{⊗m}` for the summed word weights and threshold `m·d`, so Corollary 4.1
applied to `A^{⊗m}` gives `|S| ≤ Ī(A^{⊗m})`, which is `Ī(A)^m` by the power law
`asymptoticIndependenceNumber_coordinatePower`.  Taking `m`th roots bounds every root of the power
sequence of `D` by `Ī(A)`, and `Ī(D)` is the supremum of those roots. -/
theorem asymptoticIndependenceNumber_minimumWeightPart_le
    {K : Type u} [CommSemiring K] [NoZeroDivisors K] [Nontrivial K] {κ : Leg → Type v}
    [∀ i, Fintype (κ i)] [∀ i, DecidableEq (κ i)]
    {A : (∀ i, κ i) → K} (w : ∀ i, κ i → ℕ) (d : ℕ)
    (hmin : ∀ p, A p ≠ 0 → d ≤ monomialTotalWeight w p) :
    asymptoticIndependenceNumber (minimumWeightPart w d A) ≤ asymptoticIndependenceNumber A := by
  classical
  refine Growth.supermultiplicativeLimit_le fun m hm ↦ ?_
  have hm0 : m ≠ 0 := by omega
  obtain ⟨S, hSind, hScard⟩ :=
    exists_independentSet_card_eq (coordinatePower (minimumWeightPart w d A) m)
  have hminm : ∀ p, coordinatePower A m p ≠ 0 →
      m * d ≤ monomialTotalWeight (coordinatePowerWeight w m) p := by
    intro p hp
    rw [coordinatePower_apply] at hp
    have hletters : ∀ k : Fin m, A (fun i ↦ p i k) ≠ 0 := fun k ↦
      Finset.prod_ne_zero_iff.mp hp k (Finset.mem_univ k)
    rw [monomialTotalWeight_coordinatePowerWeight]
    calc m * d = ∑ _k : Fin m, d := by simp
      _ ≤ ∑ k : Fin m, monomialTotalWeight w fun i ↦ p i k :=
          Finset.sum_le_sum fun k _ ↦ hmin _ (hletters k)
  have hSind' : IndependentSet
      (minimumWeightPart (coordinatePowerWeight w m) (m * d) (coordinatePower A m)) S := by
    rw [minimumWeightPart_coordinatePowerWeight w d hmin m]
    exact hSind
  have h := card_le_asymptoticIndependenceNumber (coordinatePowerWeight w m) (m * d) hminm hSind'
  rw [asymptoticIndependenceNumber_coordinatePower A hm0] at h
  have hgoal : Growth.nthRootSeq
      (fun j ↦ ((independenceNumberPowerSequence (minimumWeightPart w d A) j : ℕ) : ℝ)) m =
      ((S.card : ℕ) : ℝ) ^ ((m : ℝ)⁻¹) := by
    simp only [Growth.nthRootSeq, independenceNumberPowerSequence, hScard]
  rw [hgoal]
  calc ((S.card : ℕ) : ℝ) ^ ((m : ℝ)⁻¹)
      ≤ (asymptoticIndependenceNumber A ^ m) ^ ((m : ℝ)⁻¹) :=
        Real.rpow_le_rpow (by positivity) h (by positivity)
    _ = asymptoticIndependenceNumber A :=
        Real.pow_rpow_inv_natCast (asymptoticIndependenceNumber_nonneg A) hm0

/-! ## Relabelling the variables

Minimum-weight parts commute with a legwise relabelling of the variables, and the abstract tensor
of a relabelled table restricts onto the abstract tensor of the original.  These are the transport
lemmas a coordinate-level certificate needs when it is read in a different presentation of the same
tensor. -/

section RelabelWeights

variable {K : Type u} [CommSemiring K] {κ : Leg → Type v} {κ' : Leg → Type w}
variable [∀ i, Fintype (κ i)] [∀ i, DecidableEq (κ i)]
variable [∀ i, Fintype (κ' i)] [∀ i, DecidableEq (κ' i)]

namespace MonomialIndependence

omit [∀ i, Fintype (κ i)] [∀ i, DecidableEq (κ i)] [∀ i, Fintype (κ' i)]
  [∀ i, DecidableEq (κ' i)] in
/-- Relabelling the variables transports a weighting. -/
theorem monomialTotalWeight_coordinateRelabel (e : ∀ i, κ i ≃ κ' i) (w : ∀ i, κ i → ℕ)
    (p : ∀ i, κ' i) :
    monomialTotalWeight (fun i y ↦ w i ((e i).symm y)) p =
      monomialTotalWeight w (fun i ↦ (e i).symm (p i)) := rfl

omit [∀ i, Fintype (κ i)] [∀ i, DecidableEq (κ i)] [∀ i, Fintype (κ' i)]
  [∀ i, DecidableEq (κ' i)] in
/-- **Minimum-weight parts commute with relabelling the variables.** -/
theorem minimumWeightPart_coordinateRelabel (e : ∀ i, κ i ≃ κ' i) (w : ∀ i, κ i → ℕ) (d : ℕ)
    (A : (∀ i, κ i) → K) :
    minimumWeightPart (fun i y ↦ w i ((e i).symm y)) d (coordinateRelabel e A) =
      coordinateRelabel e (minimumWeightPart w d A) := by
  funext p
  by_cases h : monomialTotalWeight w (fun i ↦ (e i).symm (p i)) = d
  · rw [minimumWeightPart_of_weight (by rw [monomialTotalWeight_coordinateRelabel]; exact h),
      coordinateRelabel_apply, coordinateRelabel_apply, minimumWeightPart_of_weight h]
  · rw [minimumWeightPart, if_neg (by rw [monomialTotalWeight_coordinateRelabel]; exact h),
      coordinateRelabel_apply, minimumWeightPart, if_neg h]

end MonomialIndependence

omit [∀ i, DecidableEq (κ i)] [∀ i, DecidableEq (κ' i)] in
/-- Relabelling the variables of the legs is an exact restriction of the abstract tensors, in the
direction that forgets the relabelling.

This lemma stays in `AlgebraicComplexity.Tensor`, where the `Restricts` dot-namespace of the
library lives (`Restricts.coordinateTensor_pullback`); only the weight lemmas above belong to
`MonomialIndependence`. -/
theorem Restricts.coordinateTensor_coordinateRelabel (e : ∀ i, κ i ≃ κ' i) (A : (∀ i, κ i) → K) :
    Restricts (coordinateTensor (coordinateRelabel e A)) (coordinateTensor A) := by
  have h := Tensor.Restricts.coordinateTensor_pullback (K := K) (fun i ↦ (e i : κ i → κ' i))
    (coordinateRelabel e A)
  have hA : (fun q : ∀ i, κ i ↦ coordinateRelabel e A fun i ↦ e i (q i)) = A := by
    funext q
    simp [coordinateRelabel]
  rwa [hA] at h

end RelabelWeights
/-! ## Zeroing out as a minimum-weight part

A zeroing out is the special case of a monomial degeneration in which the weights are indicator
weights: give every surviving variable weight `0` and every deleted variable weight `1`, and take
the threshold `0`.  This identification is what lets a client that has produced an explicit
zeroing out of a Kronecker power feed it to the minimum-weight machinery of this module, and hence
to `asymptoticIndependenceNumber_minimumWeightPart_le`.
-/

section IndicatorWeights

variable {K : Type u} [CommSemiring K] {κ : Leg → Type v} [∀ i, DecidableEq (κ i)]

namespace MonomialIndependence

/-- The total indicator weight of a triple vanishes exactly when all three of its variables
survive.  Here the weight of a variable is `0` if it lies in `A i` and `1` otherwise. -/
theorem monomialTotalWeight_indicator_eq_zero_iff (A : ∀ i, Finset (κ i)) (p : ∀ i, κ i) :
    monomialTotalWeight (fun i v ↦ if v ∈ A i then 0 else 1) p = 0 ↔ ∀ i, p i ∈ A i := by
  constructor
  · intro h i
    by_contra hi
    have hone : (if p i ∈ A i then 0 else 1) = 1 := if_neg hi
    have hle : (if p i ∈ A i then 0 else 1) ≤
        monomialTotalWeight (fun i v ↦ if v ∈ A i then 0 else 1) p := by
      cases i <;> simp only [monomialTotalWeight] <;> omega
    rw [hone, h] at hle
    exact absurd hle (by omega)
  · intro h
    simp only [monomialTotalWeight, if_pos (h Leg.X), if_pos (h Leg.Y), if_pos (h Leg.Z)]

/-- **A zeroing out is a minimum-weight part.**  With the indicator weights `w i v = 0` for
`v ∈ A i` and `w i v = 1` otherwise, and threshold `d = 0`, the minimum-weight part of `T` is
exactly the zeroing out of `T` to the coordinate subsets `A`:

```text
minimumWeightPart (indicator of A) 0 T = coordinateZeroOut T A.
```

Since every weight is nonnegative, the threshold `0` is automatically a lower bound for the
weights of all occurring terms, so the accompanying monomial degeneration is unconditional. -/
theorem minimumWeightPart_indicator_eq_coordinateZeroOut (T : (∀ i, κ i) → K)
    (A : ∀ i, Finset (κ i)) :
    minimumWeightPart (fun i v ↦ if v ∈ A i then 0 else 1) 0 T = coordinateZeroOut T A := by
  funext p
  by_cases hmem : ∀ i, p i ∈ A i
  · rw [minimumWeightPart_of_weight
      ((monomialTotalWeight_indicator_eq_zero_iff A p).mpr hmem), coordinateZeroOut_of_mem hmem]
  · rw [minimumWeightPart, if_neg (fun hw ↦ hmem
      ((monomialTotalWeight_indicator_eq_zero_iff A p).mp hw)), coordinateZeroOut_of_notMem hmem]

end MonomialIndependence

end IndicatorWeights

end AlgebraicComplexity.Tensor
