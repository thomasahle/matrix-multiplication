/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Combinatorics.BinomialTail
import AlgebraicComplexity.Tensor.IndependenceMeasure

/-!
# Near-uniform mass distributions and corner terms

This module proves the two tensor-facing results of Section 5 of

> J. Alman and V. Vassilevska Williams, *Limits on All Known (and Some Unknown) Approaches to
> Matrix Multiplication*, arXiv:1810.08671v1

that turn a *large* asymptotic independence number into a *probability distribution on the terms*
of a table:

* **Theorem 5.2** (`exists_probabilityVector_uniformWindow_le_supportMarginal`): if every leg of
  `T` carries `q` variables and `Ī(T) ≥ q^{1-δ}`, then for every `ρ > 0` there is a probability
  distribution on the terms of `T` whose marginal mass on *each* variable of *each* leg is at
  least `1/q - sqrt((δ + ρ) log q)`.
* **Corollary 5.1** (`asymptoticIndependenceNumber_le_cornerBound`): a table with two *corner
  terms* — one term monopolising an `x`-variable, one monopolising a `y`-variable, both using the
  same `z`-variable — has `Ī(T) ≤ c_q` for the explicit constant
  `c_q = q^{1 - 1/(q²(q+1)² log q)} < q` (`cornerBound`).

## Placement: layer 3, not layer 1

`BARRIER_FRAMEWORK.md` §6 milestone I (and the "Interface for milestone I" section of
`Combinatorics/BinomialTail.lean`) provisionally named this module
`Tensor/IndependenceMassDistribution.lean`.  That placement is not possible: Theorem 5.2 consumes
both the layer-1 independence API (`Tensor/IndependenceNumber.lean`,
`Tensor/AsymptoticIndependenceNumber.lean`, `Tensor/IndependenceMeasure.lean`) *and* the layer-2
binomial tail `Combinatorics/BinomialTail.lean`, and `DESIGN.md` forbids a tensor-layer module
from importing the combinatorics layer.  The file therefore lives in layer 3, following the
precedent of `MatrixMultiplication/HashingExtraction.lean`.

Nothing here mentions a matrix-multiplication tensor, an exponent, or a numerical bound, so the
module is a candidate for a future shared "layer 2.5" (tensor results that need finite
combinatorics) should one be created; the only obstruction to moving it back into `Tensor/` is the
import of `Combinatorics/BinomialTail.lean`.

## Main declarations

* `supportMarginal T m c` --- AVW's `p(xᵢ)`: the marginal of a mass distribution `m` on the terms
  of `T` along leg `c`, as a `ProbabilityVector` on the variables of that leg.
* `empiricalMass T hn S hS hsupp` --- the distribution built in AVW's proof: a uniformly random
  position of a uniformly random element of a family `S` of terms of `T^{⊗n}`.
* `supportMarginal_empiricalMass_weight` --- its marginal is the average letter frequency.
* `exists_probabilityVector_uniformWindow_le_supportMarginal` --- **AVW Theorem 5.2**.
* `cornerExponent`, `cornerBound`, `cornerBound_lt`, `cornerExponent_anti` --- the explicit
  constant `c_q < q`, and the antitonicity of its exponent gap on `[2, ∞)`.
* `cornerExponent_le_of_asymptoticIndependenceNumber_ge` --- the quantitative core of
  **AVW Corollary 5.1**: two corner terms force `δ ≥ cornerExponent q`.
* `asymptoticIndependenceNumber_le_cornerBound` and
  `asymptoticIndependenceNumber_le_cornerBound_of_corner_terms` --- **AVW Corollary 5.1**, in a
  weak-hypothesis form and in the literal form of the paper.
* `twoCornerTable`, `asymptoticIndependenceNumber_twoCornerTable_lt_two` --- the smallest corner
  configuration, as a regression client.

## What the hypothesis "`|X| = |Y| = |Z| = q`" means here

AVW say "`T` is a tensor over `X, Y, Z` with `|X| = |Y| = |Z| = q`".  That is transcribed as
`Fintype.card (κ c) = q` for each leg `c`, i.e. the *ambient* number of variables of the
presentation, not `(minimalLegSet T c).card = q`.  The two differ exactly when some variable
occurs in no term of `T`, and the ambient reading is the one the argument uses: a variable of
mass `0` is a legitimate conclusion of Theorem 5.2 and is what makes Corollary 5.1 bite even for
degenerate tables.

## The mass distribution is a `ProbabilityVector` on the support

AVW's `p : X ⊗ Y ⊗ Z → [0,1]` supported on the terms of `T` is transcribed as a
`ProbabilityVector` (`Probability/Finite.lean`) on the subtype of the support
`Tensor.coordinateSupport T`; no new probabilistic notion is introduced.  AVW's quantity `p(xᵢ)`
— the total mass of the terms using the variable `xᵢ` — is the pushforward of that vector along
the `i`-th coordinate projection, i.e. `supportMarginal T m c` evaluated at the variable, again
reusing `ProbabilityVector.pushforward` verbatim.

## Proof of Theorem 5.2, and the honest constants

AVW's argument, transcribed:

1. `Ī(T) ≥ q^{1-δ}` and Fekete (`tendsto_asymptoticIndependenceNumber`) give, for every `δ' > 0`
   and all large `n`, an independent set `S` of `T^{⊗n}` with `|S| ≥ q^{n(1-δ-δ')}`
   (`exists_independentSet_card_eq`).
2. Each element of `S` is a triple of length-`n` words; the three coordinate projections are
   injective on `S` (`IndependentSet.injOn`), so the `c`-th projection `S_c` also has `|S|`
   elements.  Applying `BinomialTail.card_sub_bound_le_card_concentrated` to `S_c` and a fixed
   variable `a` of leg `c` shows that all but `(n+1)·q^n·exp(-n·tailExponent ε)` of the words in
   `S_c` have `a` occurring within `ε·n` of `n/q` times.
3. The distribution is the empirical distribution of the `n` letters of a uniformly random element
   of `S` at a uniformly random position (`empiricalMass`); its `c`-marginal at `a` is exactly the
   average letter frequency `(∑_{s ∈ S} mult(s_c, a)) / (n·|S|)`
   (`supportMarginal_empiricalMass_weight`).  Bounding that average below by the contribution of
   the concentrated words gives `(1/q - ε)(1 - (n+1)q^{-n(δ+δ')})`, and `n → ∞` removes the second
   factor.

The window is AVW's, with no loss: the deviation `ε := sqrt((δ + δ') log q)` fed to the tail
satisfies `tailExponent ε = 2ε² = 2(δ + δ') log q` *exactly*, which is precisely the exponent the
counting step needs, because `Combinatorics/BinomialTail.lean` proves the sharp Pinsker exponent
`tailExponent ε = 2ε²` (from `ProbabilityVector.two_mul_sq_sub_weight_le_klDiv`).  An earlier
version of this module, written against a Hoeffding-strength tail, carried an extra factor `2`
under the square root and therefore halved every constant derived from it; that factor is gone,
and `cornerExponent q = 1/(q² (q+1)² log q)` below is exactly AVW's printed constant.

One honest deviation from the printed statement remains:

* **The hypothesis is `≥`, not `=`.**  AVW write `Ī(T) = q^{1-δ}`; the proof uses only
  `Ī(T) ≥ q^{1-δ}`, which is also the monotone-consistent form (a larger `δ` weakens both
  hypothesis and conclusion).  Corollary 5.1 recovers the equality form by choosing `δ`
  from `Ī(T)`.

## Corollary 5.1 and its constant

With `p(x_q), p(y_q) ≥ 1/q - w` and `p(z₁) ≥ p(x_q) + p(y_q)` (the two corner terms are the only
terms using `x_q` or `y_q`, and both use `z₁`), while `p(z₁) ≤ 1 - (q-1)(1/q - w)` because the
other `q - 1` `z`-variables also carry mass at least `1/q - w`, one gets `1/q ≤ (q+1)w`, that is
`(δ + ρ) log q ≥ 1/(q(q+1))²`.  Letting `ρ → 0`,

```text
δ ≥ 1 / (q² (q+1)² log q) =: cornerExponent q,
```

so `Ī(T) ≤ q^{1 - cornerExponent q} = cornerBound q < q`.  This is exactly AVW's printed constant.
All arithmetic is exact: `cornerExponent` is a closed rational multiple of `(log q)⁻¹`.

## How AVW Lemma 7.1 will consume Corollary 5.1

Lemma 7.1 (small `q`; **not** proved here, and not to be proved in this module) is the missing
half of AVW Theorem 7.1, the other half being
`Examples/GeneralizedCoppersmithWinogradBarrier.lean`'s `avw_lemma_seven_two`.  The intended
consumption, matching the way Lemma 7.2 consumed Theorem 5.3 there, is:

1. The generalized CW table `gcwTable K μ σ` of AVW Definition 3.1 has `q + 2` variables on each
   leg (`GenCWIndex μ`, with `Fintype.card μ = q`).  It satisfies the corner hypotheses of
   `asymptoticIndependenceNumber_le_cornerBound_of_corner_terms` with
   `xOne = x₀, xLast = x_{q+1}, yOne = y₀, yLast = y_{q+1}, zOne = z₀`: the displayed support
   contains `x_{q+1} y₀ z₀` and `x₀ y_{q+1} z₀`, and `x_{q+1}` and `y_{q+1}` occur in no other
   term of Definition 3.1.
2. Hence `Ī(CW_q^σ) ≤ cornerBound (q + 2) = (q+2)^{1 - cornerExponent (q+2)}`, uniformly in `σ`.
3. `Examples/GeneralizedCoppersmithWinogradBarrier.lean` already provides the remaining inputs of
   AVW Corollary 4.3: `isCoordinateConcise_gcwTable` and
   `card_le_asymptoticRank_gcwTable : (q : ℝ) + 2 ≤ R̃(CW_q^σ)`.  With
   `s := 1 - cornerExponent (q+2) < 1` those give
   `Ī(T) ≤ R̃(T)^s`, and `six_div_add_two_le_coordinateGalacticExponent_of_concise`
   (`MatrixMultiplication/IndependenceBarrier.lean`) yields
   `ω_g^{coord}(CW_q^σ) ≥ 6/(s + 2) > 2`, which is AVW Lemma 7.1 with the explicit constant
   `c_q = 6/(3 - cornerExponent (q+2))`.

Only step 3's `Ī(T) ≤ R̃(T)^s` needs care: `cornerBound (q+2) ≤ ((q:ℝ)+2)^s` is an identity, but
transporting it to `R̃` uses monotonicity of `x ↦ x^s` and `(q:ℝ)+2 ≤ R̃`, so it needs `s ≥ 0`,
i.e. `cornerExponent (q+2) ≤ 1`, which holds for every `q ≥ 0`.  Combining with Lemma 7.2 gives a
universal constant only after taking the minimum over `q < 24`, which is a finite but genuinely
`q`-dependent computation and belongs to the client module.

## Non-goals

AVW Theorem 5.1 (the splitting bound) is a separate milestone and lives in
`Tensor/IndependenceSplitting.lean`; nothing here refers to it.  Lemma 7.1 itself, and any
generalized-CW-specific data, are deliberately absent: this module mentions no named tensor.

## References

* J. Alman and V. Vassilevska Williams, *Limits on All Known (and Some Unknown) Approaches to
  Matrix Multiplication*, arXiv:1810.08671v1, Section 5 (Theorem 5.2, Corollary 5.1) and
  Section 7.1 (Lemma 7.1).
-/

open scoped BigOperators

namespace AlgebraicComplexity.Tensor

open AlgebraicComplexity

universe u v

/-! ## Marginals of a mass distribution on the terms of a table -/

section Marginal

variable {K : Type u} [CommSemiring K] {κ : Leg → Type v}
variable [∀ i, Fintype (κ i)] [∀ i, DecidableEq (κ i)]

/-- **AVW's `p(xᵢ)`**: the marginal of a mass distribution on the terms of `T` along leg `c`.
The mass assigned to a variable `a` of leg `c` is the total mass of the terms of `T` using `a`,
which is exactly the pushforward of the distribution along the `c`-th coordinate projection. -/
noncomputable def supportMarginal (T : (∀ i, κ i) → K)
    (m : ProbabilityVector {p // p ∈ coordinateSupport T}) (c : Leg) :
    ProbabilityVector (κ c) :=
  m.pushforward fun s ↦ s.val c

/-- The marginal mass of a variable is the sum of the masses of the terms using it. -/
theorem supportMarginal_weight (T : (∀ i, κ i) → K)
    (m : ProbabilityVector {p // p ∈ coordinateSupport T}) (c : Leg) (a : κ c) :
    (supportMarginal T m c).weight a =
      ∑ s : {p // p ∈ coordinateSupport T}, if s.val c = a then m.weight s else 0 :=
  rfl

/-- Marginal masses are nonnegative. -/
theorem supportMarginal_weight_nonneg (T : (∀ i, κ i) → K)
    (m : ProbabilityVector {p // p ∈ coordinateSupport T}) (c : Leg) (a : κ c) :
    0 ≤ (supportMarginal T m c).weight a :=
  (supportMarginal T m c).nonneg a

end Marginal

/-! ## Cell masses of a mass distribution on the terms of a table

A *cell* of a table is the set of its terms with a prescribed variable on each of two chosen
legs; a *fiber* is the set of its terms with a prescribed variable on one chosen leg.  Fiber
masses are the marginals `supportMarginal` above; cell masses are AVW's `p(xᵢ yⱼ z_{f(i,j)})`,
which is a mass of a *single* term whenever the table has at most one `z`-variable per pair
`(xᵢ, yⱼ)`, but is defined here without that hypothesis.

The three facts below are the whole bookkeeping calculus AVW use in Section 7.4: a fiber is the
disjoint union of the cells inside it, two cells in a common fiber cannot exceed the fiber's mass,
and a family of pairwise disjoint cells together with a disjoint fiber cannot exceed `1`. -/

section Cell

variable {K : Type u} [CommSemiring K] {κ : Leg → Type v}
variable [∀ i, Fintype (κ i)] [∀ i, DecidableEq (κ i)]

/-- The **cell** `(c = a, d = b)` of `T`: the terms of `T` using the variable `a` on leg `c` and
the variable `b` on leg `d`. -/
noncomputable def supportCell (T : (∀ i, κ i) → K) (c d : Leg) (a : κ c) (b : κ d) :
    Finset {p // p ∈ coordinateSupport T} :=
  Finset.univ.filter fun s ↦ s.val c = a ∧ s.val d = b

/-- The **fiber** `c = a` of `T`: the terms of `T` using the variable `a` on leg `c`. -/
noncomputable def supportFiber (T : (∀ i, κ i) → K) (c : Leg) (a : κ c) :
    Finset {p // p ∈ coordinateSupport T} :=
  Finset.univ.filter fun s ↦ s.val c = a

@[simp] theorem mem_supportCell {T : (∀ i, κ i) → K} {c d : Leg} {a : κ c} {b : κ d}
    {s : {p // p ∈ coordinateSupport T}} :
    s ∈ supportCell T c d a b ↔ s.val c = a ∧ s.val d = b := by
  simp [supportCell]

@[simp] theorem mem_supportFiber {T : (∀ i, κ i) → K} {c : Leg} {a : κ c}
    {s : {p // p ∈ coordinateSupport T}} :
    s ∈ supportFiber T c a ↔ s.val c = a := by
  simp [supportFiber]

/-- **AVW's `p(xᵢ yⱼ z_{f(i,j)})`**: the total mass a distribution on the terms of `T` puts on the
cell `(c = a, d = b)`.  For a table with at most one `z`-variable per `(x, y)`-pair — AVW
Definition 7.1's first clause — the cell `(X = a, Y = b)` has at most one term, so this is the
mass of that term. -/
noncomputable def supportCellMass (T : (∀ i, κ i) → K)
    (m : ProbabilityVector {p // p ∈ coordinateSupport T}) (c d : Leg) (a : κ c) (b : κ d) : ℝ :=
  m.eventMass (supportCell T c d a b)

/-- The marginal mass of a variable is the mass of its fiber. -/
theorem supportMarginal_weight_eq_eventMass (T : (∀ i, κ i) → K)
    (m : ProbabilityVector {p // p ∈ coordinateSupport T}) (c : Leg) (a : κ c) :
    (supportMarginal T m c).weight a = m.eventMass (supportFiber T c a) := by
  rw [supportMarginal_weight, ProbabilityVector.eventMass, supportFiber, Finset.sum_filter]

/-- The cell mass, written out as a sum over the terms of `T`. -/
theorem supportCellMass_eq_sum (T : (∀ i, κ i) → K)
    (m : ProbabilityVector {p // p ∈ coordinateSupport T}) (c d : Leg) (a : κ c) (b : κ d) :
    supportCellMass T m c d a b =
      ∑ s : {p // p ∈ coordinateSupport T},
        if s.val c = a ∧ s.val d = b then m.weight s else 0 := by
  rw [supportCellMass, ProbabilityVector.eventMass, supportCell, Finset.sum_filter]

/-- Cell masses are nonnegative. -/
theorem supportCellMass_nonneg (T : (∀ i, κ i) → K)
    (m : ProbabilityVector {p // p ∈ coordinateSupport T}) (c d : Leg) (a : κ c) (b : κ d) :
    0 ≤ supportCellMass T m c d a b :=
  m.eventMass_nonneg _

/-- **An empty cell has mass zero.**  If no term of `T` uses `a` on leg `c` together with `b` on
leg `d`, the corresponding cell carries no mass. -/
theorem supportCellMass_eq_zero {T : (∀ i, κ i) → K}
    (m : ProbabilityVector {p // p ∈ coordinateSupport T}) {c d : Leg} {a : κ c} {b : κ d}
    (h : ∀ p, T p ≠ 0 → p c = a → p d ≠ b) :
    supportCellMass T m c d a b = 0 := by
  rw [supportCellMass_eq_sum]
  refine Finset.sum_eq_zero fun s _ ↦ if_neg ?_
  rintro ⟨hc, hd⟩
  exact h s.val (mem_coordinateSupport.mp s.2) hc hd

/-- **A fiber is the disjoint union of the cells it contains**: the marginal mass of `a` on leg
`c` is the sum of the masses of the cells `(c = a, d = b)` over all variables `b` of leg `d`. -/
theorem supportMarginal_weight_eq_sum_supportCellMass (T : (∀ i, κ i) → K)
    (m : ProbabilityVector {p // p ∈ coordinateSupport T}) (c d : Leg) (a : κ c) :
    (supportMarginal T m c).weight a = ∑ b : κ d, supportCellMass T m c d a b := by
  classical
  rw [supportMarginal_weight]
  simp_rw [supportCellMass_eq_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun s _ ↦ ?_
  by_cases h : s.val c = a
  · rw [Finset.sum_eq_single (s.val d)]
    · simp [h]
    · exact fun b _ hb ↦ if_neg fun hc ↦ hb hc.2.symm
    · exact fun hb ↦ absurd (Finset.mem_univ (s.val d)) hb
  · simp [h]

/-- **Two cells inside one fiber.**  Cells with the same variable `b` on leg `d` and *different*
variables on leg `c` are disjoint subsets of the fiber `d = b`, so their masses add up to at most
the marginal mass of `b`. -/
theorem add_supportCellMass_le_supportMarginal_weight (T : (∀ i, κ i) → K)
    (m : ProbabilityVector {p // p ∈ coordinateSupport T}) {c d : Leg} {a a' : κ c} {b : κ d}
    (haa : a ≠ a') :
    supportCellMass T m c d a b + supportCellMass T m c d a' b ≤
      (supportMarginal T m d).weight b := by
  classical
  have hdisj : Disjoint (supportCell T c d a b) (supportCell T c d a' b) := by
    rw [Finset.disjoint_left]
    intro s hs hs'
    rw [mem_supportCell] at hs hs'
    exact haa (hs.1.symm.trans hs'.1)
  have hsub : supportCell T c d a b ∪ supportCell T c d a' b ⊆ supportFiber T d b := by
    intro s hs
    rw [Finset.mem_union] at hs
    rw [mem_supportFiber]
    rcases hs with hs | hs <;> exact (mem_supportCell.mp hs).2
  calc supportCellMass T m c d a b + supportCellMass T m c d a' b
      = m.eventMass (supportCell T c d a b ∪ supportCell T c d a' b) :=
        (Finset.sum_union hdisj).symm
    _ ≤ m.eventMass (supportFiber T d b) := m.eventMass_mono hsub
    _ = (supportMarginal T m d).weight b := (supportMarginal_weight_eq_eventMass T m d b).symm

/-- **Disjoint cells and a disjoint fiber.**  Let `f` be an injective family of variables of
leg `c`, `g` an arbitrary family of variables of leg `d`, and `b` a variable of a third leg `e`
used by no term lying in one of the cells `(c = f i, d = g i)`.  Then those cells and the fiber
`e = b` are pairwise disjoint, so their masses add up to at most `1`.

This is the last step of AVW's proof of Theorem 7.6: the `q` diagonal cells of a lower triangular
table have distinct `x`-variables, and a `z`-variable missed by all of them gives a fiber disjoint
from every one of them. -/
theorem sum_supportCellMass_add_supportMarginal_le_one {T : (∀ i, κ i) → K}
    (m : ProbabilityVector {p // p ∈ coordinateSupport T}) {c d e : Leg}
    {ι : Type*} [Fintype ι] {f : ι → κ c} (hf : Function.Injective f) (g : ι → κ d) (b : κ e)
    (hmiss : ∀ p, T p ≠ 0 → ∀ i, p c = f i → p d = g i → p e ≠ b) :
    (∑ i, supportCellMass T m c d (f i) (g i)) + (supportMarginal T m e).weight b ≤ 1 := by
  classical
  have hdisj : ∀ j j' : Option ι, j ≠ j' →
      Disjoint (j.elim (supportFiber T e b) fun i ↦ supportCell T c d (f i) (g i))
        (j'.elim (supportFiber T e b) fun i ↦ supportCell T c d (f i) (g i)) := by
    have hcell : ∀ (i : ι), Disjoint (supportCell T c d (f i) (g i)) (supportFiber T e b) := by
      intro i
      rw [Finset.disjoint_left]
      intro s hs hs'
      rw [mem_supportCell] at hs
      rw [mem_supportFiber] at hs'
      exact hmiss s.val (mem_coordinateSupport.mp s.2) i hs.1 hs.2 hs'
    rintro (_ | i) (_ | i') hne
    · exact absurd rfl hne
    · exact (hcell i').symm
    · exact hcell i
    · show Disjoint (supportCell T c d (f i) (g i)) (supportCell T c d (f i') (g i'))
      rw [Finset.disjoint_left]
      intro s hs hs'
      rw [mem_supportCell] at hs hs'
      exact hne (congrArg some (hf (hs.1.symm.trans hs'.1)))
  have h := m.sum_eventMass_le_one
    (fun j : Option ι ↦ j.elim (supportFiber T e b) fun i ↦ supportCell T c d (f i) (g i)) hdisj
  rw [Fintype.sum_option] at h
  rw [supportMarginal_weight_eq_eventMass]
  simpa [supportCellMass, add_comm] using h

end Cell

/-! ## The empirical mass distribution of a finite family of terms of `T^{⊗n}` -/

section Empirical

variable {K : Type u} [CommSemiring K] {κ : Leg → Type v}
variable [∀ i, Fintype (κ i)] [∀ i, DecidableEq (κ i)]

/-- **The mass distribution built in AVW's proof of Theorem 5.2.**  Given a nonempty finite family
`S` of terms of `T^{⊗n}`, draw a uniformly random position `k ∈ {1,…,n}` and a uniformly random
element `s ∈ S`, and return the `k`-th letter of `s`.  Since every letter of a term of `T^{⊗n}` is
a term of `T` (hypothesis `hsupp`, supplied in practice by
`ne_zero_of_coordinatePower_ne_zero`), this is a probability distribution on the terms of `T`.

The weights are written out as the normalized counting function
`(number of pairs (s, k) with k-th letter of s equal to the given term) / (n · |S|)`. -/
noncomputable def empiricalMass (T : (∀ i, κ i) → K) {n : ℕ} (hn : 0 < n)
    (S : Finset (∀ i, Fin n → κ i)) (hS : S.Nonempty)
    (hsupp : ∀ s ∈ S, ∀ k, T (powerLetter s k) ≠ 0) :
    ProbabilityVector {p // p ∈ coordinateSupport T} where
  weight p :=
    (∑ s ∈ S, ∑ k : Fin n, if powerLetter s k = p.val then (1 : ℝ) else 0) / ((n : ℝ) * S.card)
  nonneg p := by
    refine div_nonneg (Finset.sum_nonneg fun s _ ↦ Finset.sum_nonneg fun k _ ↦ ?_) (by positivity)
    split_ifs <;> norm_num
  total := by
    have hcard : (0 : ℝ) < (S.card : ℝ) := by
      exact_mod_cast Finset.card_pos.mpr hS
    have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hd : ((n : ℝ) * S.card) ≠ 0 := by positivity
    rw [← Finset.sum_div, div_eq_one_iff_eq hd]
    rw [Finset.sum_comm]
    have hinner : ∀ s ∈ S, ∀ k : Fin n,
        (∑ p : {p // p ∈ coordinateSupport T},
          if powerLetter s k = p.val then (1 : ℝ) else 0) = 1 := by
      intro s hs k
      rw [Finset.sum_coe_sort (coordinateSupport T)
        (fun x ↦ if powerLetter s k = x then (1 : ℝ) else 0), Finset.sum_ite_eq]
      rw [if_pos (mem_coordinateSupport.mpr (hsupp s hs k))]
    calc (∑ s ∈ S, ∑ p : {p // p ∈ coordinateSupport T},
            ∑ k : Fin n, if powerLetter s k = p.val then (1 : ℝ) else 0)
        = ∑ s ∈ S, ∑ k : Fin n, ∑ p : {p // p ∈ coordinateSupport T},
            if powerLetter s k = p.val then (1 : ℝ) else 0 :=
          Finset.sum_congr rfl fun s _ ↦ Finset.sum_comm
      _ = ∑ _s ∈ S, ∑ _k : Fin n, (1 : ℝ) :=
          Finset.sum_congr rfl fun s hs ↦ Finset.sum_congr rfl fun k _ ↦ hinner s hs k
      _ = (n : ℝ) * S.card := by
          simp [Finset.sum_const, mul_comm]

/-- **The marginal of the empirical distribution is the average letter frequency.**  The mass that
`empiricalMass` puts on a variable `a` of leg `c` is the average, over the chosen terms `s ∈ S`,
of the frequency with which `a` occurs in the `c`-th word of `s`.

This is the identity AVW use when they say that `p(xᵢ)` is "the probability, upon drawing a random
`α` and a random `X_s ∈ S_X`, that the `α`th coordinate of `X_s` is `xᵢ`". -/
theorem supportMarginal_empiricalMass_weight (T : (∀ i, κ i) → K) {n : ℕ} (hn : 0 < n)
    (S : Finset (∀ i, Fin n → κ i)) (hS : S.Nonempty)
    (hsupp : ∀ s ∈ S, ∀ k, T (powerLetter s k) ≠ 0) (c : Leg) (a : κ c) :
    (supportMarginal T (empiricalMass T hn S hS hsupp) c).weight a =
      (∑ s ∈ S, (WordType.multiplicity (s c) a : ℝ)) / ((n : ℝ) * S.card) := by
  classical
  rw [supportMarginal_weight]
  have hstep : ∀ p : {p // p ∈ coordinateSupport T},
      (if p.val c = a then (empiricalMass T hn S hS hsupp).weight p else 0) =
        (if p.val c = a then
            ∑ s ∈ S, ∑ k : Fin n, if powerLetter s k = p.val then (1 : ℝ) else 0
          else 0) / ((n : ℝ) * S.card) := by
    intro p
    by_cases h : p.val c = a <;> simp [h, empiricalMass]
  rw [Finset.sum_congr rfl fun p _ ↦ hstep p, ← Finset.sum_div]
  congr 1
  -- the numerator: count the positions carrying the letter `a`
  have hpush : ∀ p : {p // p ∈ coordinateSupport T},
      (if p.val c = a then
          ∑ s ∈ S, ∑ k : Fin n, if powerLetter s k = p.val then (1 : ℝ) else 0 else 0) =
        ∑ s ∈ S, ∑ k : Fin n,
          (if p.val c = a then (if powerLetter s k = p.val then (1 : ℝ) else 0) else 0) := by
    intro p
    by_cases h : p.val c = a <;> simp [h]
  have hswap : (∑ p : {p // p ∈ coordinateSupport T},
        if p.val c = a then
          ∑ s ∈ S, ∑ k : Fin n, if powerLetter s k = p.val then (1 : ℝ) else 0 else 0) =
      ∑ s ∈ S, ∑ k : Fin n, ∑ p : {p // p ∈ coordinateSupport T},
        if p.val c = a then (if powerLetter s k = p.val then (1 : ℝ) else 0) else 0 := by
    rw [Finset.sum_congr rfl fun p _ ↦ hpush p, Finset.sum_comm]
    exact Finset.sum_congr rfl fun s _ ↦ Finset.sum_comm
  have hinner : ∀ (s : ∀ i, Fin n → κ i), s ∈ S → ∀ k : Fin n,
      (∑ p : {p // p ∈ coordinateSupport T},
        if p.val c = a then (if powerLetter s k = p.val then (1 : ℝ) else 0) else 0) =
        if s c k = a then (1 : ℝ) else 0 := by
    intro s hs k
    have hre : (∑ p : {p // p ∈ coordinateSupport T},
        if p.val c = a then (if powerLetter s k = p.val then (1 : ℝ) else 0) else 0) =
        ∑ x ∈ coordinateSupport T,
          if powerLetter s k = x then (if x c = a then (1 : ℝ) else 0) else 0 := by
      rw [← Finset.sum_coe_sort (coordinateSupport T)
        (fun x ↦ if powerLetter s k = x then (if x c = a then (1 : ℝ) else 0) else 0)]
      refine Finset.sum_congr rfl fun p _ ↦ ?_
      by_cases h1 : p.val c = a <;> by_cases h2 : powerLetter s k = p.val <;> simp [h1, h2]
    rw [hre, Finset.sum_ite_eq, if_pos (mem_coordinateSupport.mpr (hsupp s hs k))]
    rfl
  rw [hswap]
  refine Finset.sum_congr rfl fun s hs ↦ ?_
  rw [Finset.sum_congr rfl fun k _ ↦ hinner s hs k, Finset.sum_boole]
  simp [WordType.multiplicity_eq_card_fiber, Fintype.card_subtype]

end Empirical

/-! ## AVW Theorem 5.2: near-uniform mass distributions -/

section MassDistribution

open AlgebraicComplexity.BinomialTail

variable {K : Type u} [CommSemiring K] [NoZeroDivisors K] {κ : Leg → Type v}
variable [∀ i, Fintype (κ i)] [∀ i, DecidableEq (κ i)]

/-- **AVW Theorem 5.2** (near-uniform mass distributions).  Let `T` be a nonzero coefficient table
whose three legs each carry `q ≥ 2` variables, and suppose `q^{1-δ} ≤ Ī(T)` for some `δ ≥ 0`.
Then for every `ρ > 0` there is a probability distribution on the *terms* of `T` whose marginal
mass on every variable of every leg is at least

```text
1/q - sqrt((δ + ρ) · log q).
```

This is AVW's printed window.  One deliberate deviation from the printed statement remains, and is
explained in the module header: AVW assume the equality `Ī(T) = q^{1-δ}` where only `≥` is used.
`ρ` is AVW's `κ`, renamed because `κ` names the leg variable types here.

Proof sketch: if the window is nonpositive the claim is vacuous and a point mass works.
Otherwise put `δ' := ρ/4` and `ε := sqrt((δ + δ') log q) < sqrt((δ + ρ) log q)`.  Fekete
(`tendsto_asymptoticIndependenceNumber`) makes `I(T^{⊗n})^{1/n}` converge to `Ī(T) ≥ q^{1-δ}`, so
for all large `n` there is an independent set `S` of `T^{⊗n}` with `|S| > q^{(1-δ-δ')n}`; enlarging
`n` further also makes `(n+1)·q^{-(δ+δ')n} ≤ sqrt((δ+ρ)log q) - ε`.  Take the empirical
distribution `empiricalMass` of the letters of `S`.  Its `c`-marginal at a variable `a` is the
average frequency of `a` in the `c`-th words of `S` (`supportMarginal_empiricalMass_weight`);
the `c`-th projection is injective on `S` (`IndependentSet.distinct`), so
`card_sub_bound_mul_le_sum_multiplicity` bounds that average below by
`(|S| - B)(1/q - ε)/|S|` with `B = (n+1)q^n exp(-n·tailExponent ε)`.  Here the sharp Pinsker
exponent gives `tailExponent ε = 2ε² = 2(δ+δ') log q` exactly, which is what makes
`B ≤ q^{-(δ+δ')n}·(n+1)·q^{(1-δ-δ')n}` and hence, by the choice of `n`,
`B ≤ (sqrt((δ+ρ)log q) - ε)·|S|`, which is exactly what is needed. -/
theorem exists_probabilityVector_uniformWindow_le_supportMarginal
    (T : (∀ i, κ i) → K) {p₀ : ∀ i, κ i} (hp₀ : T p₀ ≠ 0)
    {q : ℕ} (hq : 2 ≤ q) (hcard : ∀ c, Fintype.card (κ c) = q)
    {δ : ℝ} (hδ : 0 ≤ δ) (hI : (q : ℝ) ^ (1 - δ) ≤ asymptoticIndependenceNumber T)
    {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ m : ProbabilityVector {p // p ∈ coordinateSupport T},
      ∀ (c : Leg) (a : κ c),
        1 / (q : ℝ) - Real.sqrt ((δ + ρ) * Real.log q) ≤
          (supportMarginal T m c).weight a := by
  classical
  have hqR : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hqpos : (0 : ℝ) < (q : ℝ) := by linarith
  have hlogpos : 0 < Real.log q := Real.log_pos (by linarith)
  set w : ℝ := Real.sqrt ((δ + ρ) * Real.log q) with hwdef
  have hwnn : 0 ≤ w := Real.sqrt_nonneg _
  by_cases hcase : 1 / (q : ℝ) - w ≤ 0
  · exact ⟨ProbabilityVector.pointMass ⟨p₀, mem_coordinateSupport.mpr hp₀⟩,
      fun c a ↦ le_trans hcase (supportMarginal_weight_nonneg _ _ _ _)⟩
  replace hcase : 0 < 1 / (q : ℝ) - w := not_le.mp hcase
  -- the slack parameter `δ'` and the deviation `ε` actually fed to the binomial tail
  set δ' : ℝ := ρ / 4 with hδ'def
  have hδ'pos : (0 : ℝ) < δ' := by positivity
  have harg : (0 : ℝ) ≤ (δ + δ') * Real.log q :=
    mul_nonneg (by linarith) hlogpos.le
  set ε : ℝ := Real.sqrt ((δ + δ') * Real.log q) with hεdef
  have hεnn : 0 ≤ ε := Real.sqrt_nonneg _
  have hεsq : ε ^ 2 = (δ + δ') * Real.log q := Real.sq_sqrt harg
  have hεw : ε < w := by
    rw [hεdef, hwdef]
    refine Real.sqrt_lt_sqrt harg ?_
    have h2 : δ' < ρ := by rw [hδ'def]; linarith
    nlinarith
  have hεq : ε ≤ 1 / (q : ℝ) := by linarith
  have hhalf : 1 / (q : ℝ) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hqR
  -- the sharp Pinsker exponent turns this into an *equality*, which is AVW's constant
  have htail : (2 * δ + 2 * δ') * Real.log q ≤ tailExponent ε :=
    le_of_eq (by unfold tailExponent; rw [hεsq]; ring)
  -- choose a large power `n`
  set r : ℝ := (q : ℝ) ^ (-(δ + δ')) with hrdef
  have hr0 : (0 : ℝ) < r := Real.rpow_pos_of_pos hqpos _
  have hr1 : r < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by linarith) (by linarith)
  have hlim : Filter.Tendsto (fun n : ℕ ↦ ((n : ℝ) + 1) * r ^ n) Filter.atTop (nhds 0) := by
    have h := tendsto_self_mul_const_pow_of_lt_one hr0.le hr1
    have h2 := tendsto_pow_atTop_nhds_zero_of_lt_one hr0.le hr1
    simpa [add_mul] using h.add h2
  have hev1 : ∀ᶠ n : ℕ in Filter.atTop, ((n : ℝ) + 1) * r ^ n ≤ w - ε :=
    (hlim.eventually_lt_const (by linarith)).mono fun _ h ↦ h.le
  have hIlt : (q : ℝ) ^ (1 - δ - δ') < asymptoticIndependenceNumber T :=
    lt_of_lt_of_le (Real.rpow_lt_rpow_of_exponent_lt (by linarith) (by linarith)) hI
  have hev2 := (tendsto_asymptoticIndependenceNumber (T := T) hp₀).eventually_const_lt hIlt
  obtain ⟨n, ⟨hnA, hnB⟩, hn1⟩ := ((hev1.and hev2).and (Filter.eventually_ge_atTop 1)).exists
  have hn0 : 0 < n := hn1
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn0
  -- the independent set of `T^{⊗n}` supplied by the hypothesis on `Ī(T)`
  set N : ℝ := ((independenceNumberPowerSequence T n : ℕ) : ℝ) with hNdef
  have hNnn : (0 : ℝ) ≤ N := by positivity
  have hNbig : (q : ℝ) ^ ((1 - δ - δ') * (n : ℝ)) < N := by
    have hroot : (q : ℝ) ^ (1 - δ - δ') < N ^ ((n : ℝ)⁻¹) := hnB
    have hstep := Real.rpow_lt_rpow (Real.rpow_nonneg hqpos.le _) hroot hnR
    rwa [← Real.rpow_mul hqpos.le, ← Real.rpow_mul hNnn, inv_mul_cancel₀ (ne_of_gt hnR),
      Real.rpow_one] at hstep
  obtain ⟨S, hSind, hScard⟩ := exists_independentSet_card_eq (coordinatePower T n)
  have hScardR : (S.card : ℝ) = N := by rw [hScard]; rfl
  have hSpos : (0 : ℝ) < (S.card : ℝ) := by
    rw [hScardR]; exact lt_of_le_of_lt (Real.rpow_nonneg hqpos.le _) hNbig
  have hSne : S.Nonempty := Finset.card_pos.mp (by exact_mod_cast hSpos)
  have hsupp : ∀ s ∈ S, ∀ k, T (powerLetter s k) ≠ 0 :=
    fun s hs k ↦ ne_zero_of_coordinatePower_ne_zero (hSind.ne_zero s hs) k
  refine ⟨empiricalMass T hn0 S hSne hsupp, fun c a ↦ ?_⟩
  rw [supportMarginal_empiricalMass_weight]
  -- pass to the `c`-th leg projection of `S`, on which the projection is injective
  have hinjOn : Set.InjOn (fun s : ∀ i, Fin n → κ i ↦ s c) (S : Set (∀ i, Fin n → κ i)) :=
    hSind.injOn c
  have hsum : ∑ s ∈ S, (WordType.multiplicity (s c) a : ℝ) =
      ∑ ww ∈ S.image fun s ↦ s c, (WordType.multiplicity ww a : ℝ) :=
    (Finset.sum_image (f := fun ww ↦ ((WordType.multiplicity ww a : ℕ) : ℝ)) hinjOn).symm
  have hWcard : ((S.image fun s ↦ s c).card : ℝ) = (S.card : ℝ) := by
    exact_mod_cast congrArg (Nat.cast : ℕ → ℝ) (Finset.card_image_of_injOn hinjOn)
  have hcardc : Fintype.card (κ c) = q := hcard c
  have hconc := card_sub_bound_mul_le_sum_multiplicity (ι := κ c)
    (by rw [hcardc]; exact hq) (S.image fun s ↦ s c) a hεnn (by rw [hcardc]; exact hεq)
  rw [hcardc, hWcard, ← hsum] at hconc
  set B : ℝ := ((n : ℝ) + 1) * (q : ℝ) ^ n * Real.exp (-(n : ℝ) * tailExponent ε) with hBdef
  have hB0 : (0 : ℝ) ≤ B := by rw [hBdef]; positivity
  -- the tail bound, in the exponential form
  have hexp : (q : ℝ) ^ n * Real.exp (-(n : ℝ) * tailExponent ε) ≤
      (q : ℝ) ^ ((1 - 2 * (δ + δ')) * (n : ℝ)) := by
    have hpow : (q : ℝ) ^ n = Real.exp ((n : ℝ) * Real.log q) := by
      rw [← Real.rpow_natCast (q : ℝ) n, Real.rpow_def_of_pos hqpos]; ring_nf
    have hrpow : (q : ℝ) ^ ((1 - 2 * (δ + δ')) * (n : ℝ)) =
        Real.exp (Real.log q * ((1 - 2 * (δ + δ')) * (n : ℝ))) := Real.rpow_def_of_pos hqpos _
    rw [hpow, hrpow, ← Real.exp_add]
    refine Real.exp_le_exp.mpr ?_
    have hmul : (n : ℝ) * ((2 * δ + 2 * δ') * Real.log q) ≤ (n : ℝ) * tailExponent ε :=
      mul_le_mul_of_nonneg_left htail hnR.le
    linarith [hmul]
  have hsplit : (q : ℝ) ^ ((1 - 2 * (δ + δ')) * (n : ℝ)) =
      r ^ n * (q : ℝ) ^ ((1 - δ - δ') * (n : ℝ)) := by
    rw [hrdef, ← Real.rpow_natCast ((q : ℝ) ^ (-(δ + δ'))) n, ← Real.rpow_mul hqpos.le,
      ← Real.rpow_add hqpos]
    congr 1
    ring
  have hQpos : (0 : ℝ) < (q : ℝ) ^ ((1 - δ - δ') * (n : ℝ)) := Real.rpow_pos_of_pos hqpos _
  have hBle : B ≤ (w - ε) * (q : ℝ) ^ ((1 - δ - δ') * (n : ℝ)) := by
    have h1 : B ≤ ((n : ℝ) + 1) * ((q : ℝ) ^ ((1 - 2 * (δ + δ')) * (n : ℝ))) := by
      rw [hBdef, mul_assoc]
      exact mul_le_mul_of_nonneg_left hexp (by positivity)
    rw [hsplit] at h1
    have h3 := mul_le_mul_of_nonneg_right hnA hQpos.le
    linarith
  -- assemble
  have hbfinal : B * (1 / (q : ℝ) - ε) ≤ (w - ε) * (S.card : ℝ) := by
    have hle1 : B * (1 / (q : ℝ) - ε) ≤ B := by
      have hone : 1 / (q : ℝ) - ε ≤ 1 := by linarith
      calc B * (1 / (q : ℝ) - ε) ≤ B * 1 := mul_le_mul_of_nonneg_left hone hB0
        _ = B := mul_one B
    have hQle : (q : ℝ) ^ ((1 - δ - δ') * (n : ℝ)) ≤ (S.card : ℝ) := by
      rw [hScardR]; exact hNbig.le
    have h4 : (w - ε) * (q : ℝ) ^ ((1 - δ - δ') * (n : ℝ)) ≤ (w - ε) * (S.card : ℝ) :=
      mul_le_mul_of_nonneg_left hQle (by linarith)
    linarith
  have hden : (0 : ℝ) < (n : ℝ) * (S.card : ℝ) := mul_pos hnR hSpos
  rw [le_div_iff₀ hden]
  have h5 : (0 : ℝ) ≤ (n : ℝ) * ((w - ε) * (S.card : ℝ) - B * (1 / (q : ℝ) - ε)) :=
    mul_nonneg hnR.le (sub_nonneg.mpr hbfinal)
  have hring : ((S.card : ℝ) - B) * ((n : ℝ) * (1 / (q : ℝ) - ε)) -
      (1 / (q : ℝ) - w) * ((n : ℝ) * (S.card : ℝ)) =
      (n : ℝ) * ((w - ε) * (S.card : ℝ) - B * (1 / (q : ℝ) - ε)) := by ring
  linarith [hconc, h5, hring]

end MassDistribution

end AlgebraicComplexity.Tensor

/-! ## AVW Corollary 5.1: two corner terms force `Ī(T) < q`

Corollary 5.1 and the constants it produces are stated in `AlgebraicComplexity`, not in
`AlgebraicComplexity.Tensor`: `cornerBound` is an input of the barrier calculus of
`MatrixMultiplication/IndependenceBarrier.lean`, which lives in the outer namespace, and the two
are combined in `MatrixMultiplication/CornerBarrier.lean`. -/

namespace AlgebraicComplexity

open Tensor

universe u v

section Corner

/-- **The explicit exponent gap of AVW Corollary 5.1**, `1/(q² (q+1)² log q)`.

This is AVW's printed constant, recovered exactly: the window of Theorem 5.2 is theirs, because
the binomial tail's exponent `BinomialTail.tailExponent ε = 2ε²` is the sharp Pinsker exponent
rather than a Hoeffding-strength substitute. -/
noncomputable def cornerExponent (q : ℕ) : ℝ :=
  1 / ((q : ℝ) ^ 2 * ((q : ℝ) + 1) ^ 2 * Real.log q)

/-- **The constant `c_q` of AVW Corollary 5.1**: `c_q = q^{1 - cornerExponent q}`, which is
strictly below `q` (`cornerBound_lt`). -/
noncomputable def cornerBound (q : ℕ) : ℝ := (q : ℝ) ^ (1 - cornerExponent q)

/-- The exponent gap is positive for every alphabet size `q ≥ 2`. -/
theorem cornerExponent_pos {q : ℕ} (hq : 2 ≤ q) : 0 < cornerExponent q := by
  have hqR : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hlog : 0 < Real.log q := Real.log_pos (by linarith)
  rw [cornerExponent]
  positivity

/-- `1/2 ≤ log q` for every `q ≥ 2`; the elementary estimate shared by the corner and
diagonal exponent bounds below.  Certified `log 2` enclosures live in
`Analysis/LogConstants.lean`, but importing that module here would newly pull
`Mathlib.Analysis.SpecialFunctions.Log.Deriv` into this file, so the one-line
`log_le_sub_one_of_pos` estimate is kept local. -/
private theorem half_le_log {q : ℕ} (hq : 2 ≤ q) : (1 : ℝ) / 2 ≤ Real.log q := by
  have hqR : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hlog2 : (1 : ℝ) / 2 ≤ Real.log 2 := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2⁻¹ by norm_num)
    rw [Real.log_inv] at h
    norm_num at h
    linarith
  exact le_trans hlog2 (Real.log_le_log (by norm_num) hqR)

/-- The exponent gap is below `1` for every `q ≥ 2`, so `1 - cornerExponent q ≥ 0`.

Proof sketch: the denominator `q²(q+1)² log q` is at least `36 log 2 > 1`. -/
theorem cornerExponent_le_one {q : ℕ} (hq : 2 ≤ q) : cornerExponent q ≤ 1 := by
  have hqR : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hlq := half_le_log hq
  have hq2 : (4 : ℝ) ≤ (q : ℝ) ^ 2 := by nlinarith
  have hq3 : (9 : ℝ) ≤ ((q : ℝ) + 1) ^ 2 := by nlinarith
  have hA : (36 : ℝ) ≤ (q : ℝ) ^ 2 * ((q : ℝ) + 1) ^ 2 := by
    have := mul_le_mul hq2 hq3 (by norm_num) (by positivity)
    linarith
  have hprod : (36 : ℝ) * (1 / 2) ≤ ((q : ℝ) ^ 2 * ((q : ℝ) + 1) ^ 2) * Real.log q :=
    mul_le_mul hA hlq (by norm_num) (by positivity)
  have hden : (1 : ℝ) ≤ (q : ℝ) ^ 2 * ((q : ℝ) + 1) ^ 2 * Real.log q := by linarith
  rw [cornerExponent, div_le_one (by linarith)]
  linarith

/-- **`c_q < q`**: the corner bound is a genuine saving over the trivial bound `Ī(T) ≤ q`. -/
theorem cornerBound_lt {q : ℕ} (hq : 2 ≤ q) : cornerBound q < (q : ℝ) := by
  have hqR : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hpos := cornerExponent_pos hq
  have h : (q : ℝ) ^ (1 - cornerExponent q) < (q : ℝ) ^ (1 : ℝ) :=
    Real.rpow_lt_rpow_of_exponent_lt (by linarith) (by linarith)
  rwa [Real.rpow_one] at h

/-- **The exponent gap is antitone on `[2, ∞)`**: a larger alphabet gives a smaller saving.  The
denominator `q²(q+1)² log q` is monotone in `q` and positive from `q = 2` on. -/
theorem cornerExponent_anti {a b : ℕ} (ha : 2 ≤ a) (hab : a ≤ b) :
    cornerExponent b ≤ cornerExponent a := by
  have haR : (2 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
  have habR : (a : ℝ) ≤ (b : ℝ) := by exact_mod_cast hab
  have hla : 0 < Real.log a := Real.log_pos (by linarith)
  have hda : (0 : ℝ) < (a : ℝ) ^ 2 * ((a : ℝ) + 1) ^ 2 * Real.log a := by positivity
  have hle : (a : ℝ) ^ 2 * ((a : ℝ) + 1) ^ 2 * Real.log a ≤
      (b : ℝ) ^ 2 * ((b : ℝ) + 1) ^ 2 * Real.log b := by
    gcongr
  rw [cornerExponent, cornerExponent]
  exact one_div_le_one_div_of_le hda hle

variable {K : Type u} [CommSemiring K] [NoZeroDivisors K] {κ : Leg → Type v}
variable [∀ i, Fintype (κ i)] [∀ i, DecidableEq (κ i)]

/-- **The quantitative core of AVW Corollary 5.1.**  Suppose `T` has `q ≥ 2` variables on each
leg, `T` is nonzero, and there are variables `xLast, yLast, zOne` such that

* every term using `xLast` uses `zOne` (`hxz`),
* every term using `yLast` uses `zOne` (`hyz`), and
* no term uses both `xLast` and `yLast` (`hxy`).

Then every `δ ≥ 0` with `q^{1-δ} ≤ Ī(T)` satisfies `cornerExponent q ≤ δ`.

These hypotheses are weaker than AVW's "`x_q` and `y_q` each occur in exactly one term, and those
two terms are `x_q y₁ z₁` and `x₁ y_q z₁`"; the literal form is
`asymptoticIndependenceNumber_le_cornerBound_of_corner_terms` below.

Proof sketch: fix `ρ > 0` and take the near-uniform mass distribution `m` of Theorem 5.2, whose
window is `1/q - w` with `w = sqrt((δ+ρ) log q)`.  The three hypotheses make the indicator
inequality `[p uses xLast] + [p uses yLast] ≤ [p uses zOne]` hold term by term, so summing against
`m` gives `p(zOne) ≥ p(xLast) + p(yLast) ≥ 2(1/q - w)`.  On the other hand the other `q-1`
`z`-variables also carry mass at least `1/q - w`, so `p(zOne) ≤ 1 - (q-1)(1/q - w)`.  Comparing
the two gives `1/q ≤ (q+1)w`, i.e. `1/(q(q+1)) ≤ sqrt((δ+ρ) log q)`.  Squaring and letting
`ρ → 0` gives `1/(q(q+1))² ≤ δ log q`, which is the claim. -/
theorem cornerExponent_le_of_asymptoticIndependenceNumber_ge
    (T : (∀ i, κ i) → K) {p₀ : ∀ i, κ i} (hp₀ : T p₀ ≠ 0)
    {q : ℕ} (hq : 2 ≤ q) (hcard : ∀ c, Fintype.card (κ c) = q)
    {xLast : κ Leg.X} {yLast : κ Leg.Y} {zOne : κ Leg.Z}
    (hxz : ∀ p, T p ≠ 0 → p Leg.X = xLast → p Leg.Z = zOne)
    (hyz : ∀ p, T p ≠ 0 → p Leg.Y = yLast → p Leg.Z = zOne)
    (hxy : ∀ p, T p ≠ 0 → p Leg.X = xLast → p Leg.Y ≠ yLast)
    {δ : ℝ} (hδ : 0 ≤ δ) (hI : (q : ℝ) ^ (1 - δ) ≤ asymptoticIndependenceNumber T) :
    cornerExponent q ≤ δ := by
  classical
  have hqR : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hqpos : (0 : ℝ) < (q : ℝ) := by linarith
  have hlogpos : 0 < Real.log q := Real.log_pos (by linarith)
  -- Step 1: for every `ρ > 0` the window forces `1/(q(q+1)) ≤ sqrt((δ+ρ) log q)`.
  have key : ∀ ρ : ℝ, 0 < ρ →
      1 / ((q : ℝ) * ((q : ℝ) + 1)) ≤ Real.sqrt ((δ + ρ) * Real.log q) := by
    intro ρ hρ
    obtain ⟨m, hm⟩ :=
      exists_probabilityVector_uniformWindow_le_supportMarginal T hp₀ hq hcard hδ hI hρ
    set w : ℝ := Real.sqrt ((δ + ρ) * Real.log q) with hwdef
    have hwnn : 0 ≤ w := Real.sqrt_nonneg _
    -- the corner inequality `p(zOne) ≥ p(xLast) + p(yLast)`
    have hcorner : (supportMarginal T m Leg.X).weight xLast +
        (supportMarginal T m Leg.Y).weight yLast ≤ (supportMarginal T m Leg.Z).weight zOne := by
      rw [supportMarginal_weight, supportMarginal_weight, supportMarginal_weight,
        ← Finset.sum_add_distrib]
      refine Finset.sum_le_sum fun p _ ↦ ?_
      have hTp : T p.val ≠ 0 := mem_coordinateSupport.mp p.2
      by_cases hx : p.val Leg.X = xLast
      · simp [hx, hxy _ hTp hx, hxz _ hTp hx]
      · by_cases hy : p.val Leg.Y = yLast
        · simp [hx, hy, hyz _ hTp hy]
        · have hnn : (0 : ℝ) ≤ (if p.val Leg.Z = zOne then m.weight p else 0) := by
            split_ifs
            · exact m.nonneg p
            · exact le_rfl
          simpa [hx, hy] using hnn
    -- the remaining `z`-variables also carry mass, so `p(zOne)` cannot be too big
    have hZle : (supportMarginal T m Leg.Z).weight zOne ≤
        1 - ((q : ℝ) - 1) * (1 / (q : ℝ) - w) := by
      have h := (supportMarginal T m Leg.Z).weight_le_one_sub_of_forall_le
        (fun a ↦ hm Leg.Z a) zOne
      rwa [hcard Leg.Z] at h
    have hX := hm Leg.X xLast
    have hY := hm Leg.Y yLast
    have hqi : (q : ℝ) * (1 / (q : ℝ)) = 1 := by field_simp
    have hfinal : 1 / (q : ℝ) ≤ ((q : ℝ) + 1) * w := by
      linarith [hX, hY, hcorner, hZle, hqi]
    have hqq : (0 : ℝ) < (q : ℝ) * ((q : ℝ) + 1) := by positivity
    rw [div_le_iff₀ hqq]
    have hscale := mul_le_mul_of_nonneg_left hfinal hqpos.le
    rw [hqi] at hscale
    linarith [hscale]
  -- Step 2: square, and let `ρ` tend to `0`.
  have hsq : ∀ ρ : ℝ, 0 < ρ →
      1 / ((q : ℝ) ^ 2 * ((q : ℝ) + 1) ^ 2) ≤ (δ + ρ) * Real.log q := by
    intro ρ hρ
    have h := key ρ hρ
    have harg : (0 : ℝ) ≤ (δ + ρ) * Real.log q := mul_nonneg (by linarith) hlogpos.le
    have hsqrt : Real.sqrt ((δ + ρ) * Real.log q) ^ 2 = (δ + ρ) * Real.log q :=
      Real.sq_sqrt harg
    have hnn : (0 : ℝ) ≤ 1 / ((q : ℝ) * ((q : ℝ) + 1)) := by positivity
    have hA2 : (1 / ((q : ℝ) * ((q : ℝ) + 1))) ^ 2 = 1 / ((q : ℝ) ^ 2 * ((q : ℝ) + 1) ^ 2) := by
      rw [div_pow, one_pow, mul_pow]
    have hpow : (1 / ((q : ℝ) * ((q : ℝ) + 1))) ^ 2 ≤
        Real.sqrt ((δ + ρ) * Real.log q) ^ 2 := by
      rw [sq, sq]; exact mul_self_le_mul_self hnn h
    rwa [hA2, hsqrt] at hpow
  have hlim : 1 / ((q : ℝ) ^ 2 * ((q : ℝ) + 1) ^ 2) ≤ δ * Real.log q := by
    refine le_of_forall_pos_le_add fun η hη ↦ ?_
    have h := hsq (η / Real.log q) (by positivity)
    have hexp : (δ + η / Real.log q) * Real.log q = δ * Real.log q + η := by
      field_simp
    rwa [hexp] at h
  -- Step 3: rearrange into the stated exponent gap.
  have hP : (0 : ℝ) < (q : ℝ) ^ 2 * ((q : ℝ) + 1) ^ 2 := by positivity
  have h2 := mul_le_mul_of_nonneg_left hlim hP.le
  have hid : ((q : ℝ) ^ 2 * ((q : ℝ) + 1) ^ 2) * (1 / ((q : ℝ) ^ 2 * ((q : ℝ) + 1) ^ 2)) = 1 := by
    field_simp
  rw [hid] at h2
  rw [cornerExponent, div_le_iff₀ (by positivity)]
  linarith [h2]

/-- **AVW Corollary 5.1**, in the weak-hypothesis form: a table on `q ≥ 2` variables per leg whose
`xLast`- and `yLast`-terms all use the same `z`-variable, and never occur together, satisfies
`Ī(T) ≤ c_q = q^{1 - 1/(q²(q+1)² log q)} < q`.

Proof sketch: `Ī(T)` lies in `[1, q]`, so it is `q^{1-δ}` for `δ := 1 - log_q Ī(T) ≥ 0`;
`cornerExponent_le_of_asymptoticIndependenceNumber_ge` bounds that `δ` below by
`cornerExponent q`, and `x ↦ q^x` is monotone. -/
theorem asymptoticIndependenceNumber_le_cornerBound
    (T : (∀ i, κ i) → K) {p₀ : ∀ i, κ i} (hp₀ : T p₀ ≠ 0)
    {q : ℕ} (hq : 2 ≤ q) (hcard : ∀ c, Fintype.card (κ c) = q)
    {xLast : κ Leg.X} {yLast : κ Leg.Y} {zOne : κ Leg.Z}
    (hxz : ∀ p, T p ≠ 0 → p Leg.X = xLast → p Leg.Z = zOne)
    (hyz : ∀ p, T p ≠ 0 → p Leg.Y = yLast → p Leg.Z = zOne)
    (hxy : ∀ p, T p ≠ 0 → p Leg.X = xLast → p Leg.Y ≠ yLast) :
    asymptoticIndependenceNumber T ≤ cornerBound q := by
  have hqR : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hqpos : (0 : ℝ) < (q : ℝ) := by linarith
  have h1 : (1 : ℝ) ≤ asymptoticIndependenceNumber T := by
    refine le_trans ?_ (independenceNumber_le_asymptoticIndependenceNumber T)
    exact_mod_cast one_le_independenceNumber hp₀
  have hIq : asymptoticIndependenceNumber T ≤ (q : ℝ) := by
    have h := asymptoticIndependenceNumber_le_card T Leg.X
    rwa [hcard Leg.X] at h
  have hlogpos : 0 < Real.log q := Real.log_pos (by linarith)
  set L : ℝ := Real.log (asymptoticIndependenceNumber T) / Real.log q with hLdef
  have hrl : (q : ℝ) ^ L = asymptoticIndependenceNumber T := by
    have hmul : Real.log q * (Real.log (asymptoticIndependenceNumber T) / Real.log q) =
        Real.log (asymptoticIndependenceNumber T) := by
      field_simp
    rw [Real.rpow_def_of_pos hqpos, hLdef, hmul, Real.exp_log (by linarith)]
  have hL1 : L ≤ 1 := by
    rw [hLdef, div_le_one hlogpos]
    exact Real.log_le_log (by linarith) hIq
  have hδ : (0 : ℝ) ≤ 1 - L := by linarith
  have hI' : (q : ℝ) ^ (1 - (1 - L)) ≤ asymptoticIndependenceNumber T := by
    rw [show (1 : ℝ) - (1 - L) = L by ring, hrl]
  have he := cornerExponent_le_of_asymptoticIndependenceNumber_ge T hp₀ hq hcard hxz hyz hxy hδ hI'
  rw [cornerBound, ← hrl]
  exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)

/-- **AVW Corollary 5.1, as printed.**  Suppose `T` has `q ≥ 2` variables on each leg, contains
the two *corner terms* `x_q y₁ z₁` and `x₁ y_q z₁`, and neither `x_q` nor `y_q` occurs in any
other term.  Then `Ī(T) ≤ c_q < q` for the explicit constant `cornerBound q` depending only
on `q`.

The only extra hypothesis is `x₁ ≠ x_q`, which AVW leave implicit in the phrase "`x₁, x_q ∈ X`"
together with `q ≥ 2`; it is what makes the two displayed terms distinct.  Note that `y₁ ≠ y_q` is
*derived*, not assumed.

The hypothesis `_hyterm`, that `x₁ y_q z₁` really is a term of `T`, is kept for faithfulness to
the printed statement but is **not used**: if `y_q` occurred in no term at all its marginal mass
would be `0`, which contradicts the Theorem 5.2 window even more strongly.  The general form
`asymptoticIndependenceNumber_le_cornerBound` therefore drops it.

Proof sketch: the "occurs in no other term" hypotheses turn the displayed terms into the general
corner hypotheses of `asymptoticIndependenceNumber_le_cornerBound`; `y₁ ≠ y_q` follows because
otherwise the term `x_q y₁ z₁` would also be the unique term using `y_q`, forcing `x_q = x₁`. -/
theorem asymptoticIndependenceNumber_le_cornerBound_of_corner_terms
    (T : (∀ i, κ i) → K) {q : ℕ} (hq : 2 ≤ q) (hcard : ∀ c, Fintype.card (κ c) = q)
    {xOne xLast : κ Leg.X} {yOne yLast : κ Leg.Y} {zOne : κ Leg.Z}
    (hxne : xOne ≠ xLast)
    (hxterm : T (ofLegs xLast yOne zOne) ≠ 0)
    (_hyterm : T (ofLegs xOne yLast zOne) ≠ 0)
    (hxonly : ∀ p, T p ≠ 0 → p Leg.X = xLast → p = ofLegs xLast yOne zOne)
    (hyonly : ∀ p, T p ≠ 0 → p Leg.Y = yLast → p = ofLegs xOne yLast zOne) :
    asymptoticIndependenceNumber T ≤ cornerBound q := by
  have hyne : yOne ≠ yLast := by
    intro h
    have := hyonly (ofLegs xLast yOne zOne) hxterm (by simp [h])
    exact hxne (congrFun this Leg.X).symm
  refine asymptoticIndependenceNumber_le_cornerBound T hxterm hq hcard
    (xLast := xLast) (yLast := yLast) (zOne := zOne) ?_ ?_ ?_
  · intro p hp hx
    rw [hxonly p hp hx]
    rfl
  · intro p hp hy
    rw [hyonly p hp hy]
    rfl
  · intro p hp hx
    rw [hxonly p hp hx]
    exact hyne

end Corner

/-! ## The explicit constants of AVW Theorem 7.6

The hard half of AVW Theorem 7.6 (`Examples/LowerTriangularDiagonal.lean`) runs the same
`ρ → 0` squeeze as Corollary 5.1 above, but with a window deficit that doubles at each of the `q`
steps of its induction.  The resulting constants are collected here, beside `cornerExponent`,
because they are of the same kind — closed rational multiples of `(log q)⁻¹` — and because the
barrier calculus of `MatrixMultiplication/IndependenceBarrier.lean` consumes them in the outer
namespace.

AVW state the induction with an unspecified `O_q(κ)`; the closed form proved downstream is
`p(x_{q-1-j} y_j z_{f(q-1-j,j)}) ≥ 1/q - (q·2^j - q + 1)·u`, whose sum over `j < q` is
`1 - (q·2^q - q²)·u`.  Adding the mass `1/q - u` of a missed `z`-variable and comparing with the
total mass `1` gives `1 ≤ q·(1 + q·2^q - q²)·u`, i.e. `u ≥ 1/diagonalWindowBound q`. -/

section Diagonal

/-- **The window bound of AVW Theorem 7.6**, `q·(1 + q·2^q - q²)`.

It is the reciprocal of the smallest near-uniform window that a lower triangular table with
`Ī(T) = q` can tolerate while missing a `z`-variable on its diagonal.  Note that it is
*exponential* in `q`, so the gap `diagonalExponent q` below is exponentially small; for the
particular table `T_q^lower` the corner bound of `Examples/LowerTriangularBarrier.lean` (AVW
Theorem 7.5) is far sharper. -/
noncomputable def diagonalWindowBound (q : ℕ) : ℝ :=
  (q : ℝ) * (1 + (q : ℝ) * 2 ^ q - (q : ℝ) ^ 2)

/-- **The exponent gap of AVW Theorem 7.6**, `1/(diagonalWindowBound q ² · log q)`: a lower
triangular table on `q` variables per leg whose diagonal misses a `z`-variable has
`Ī(T) ≤ q^{1 - diagonalExponent q}`. -/
noncomputable def diagonalExponent (q : ℕ) : ℝ :=
  1 / (diagonalWindowBound q ^ 2 * Real.log q)

/-- **The constant of AVW Theorem 7.6**: `q^{1 - diagonalExponent q}`, which is strictly below `q`
(`diagonalBound_lt`). -/
noncomputable def diagonalBound (q : ℕ) : ℝ := (q : ℝ) ^ (1 - diagonalExponent q)

/-- `q ≤ 2^q` in `ℝ`, the one arithmetic input to the positivity of the window bound. -/
theorem cast_le_two_pow (q : ℕ) : (q : ℝ) ≤ 2 ^ q := by
  have h : q < 2 ^ q := Nat.lt_two_pow_self
  have : ((q : ℕ) : ℝ) ≤ ((2 ^ q : ℕ) : ℝ) := by exact_mod_cast h.le
  simpa using this

/-- **The window bound is at least `q`**, hence positive for `q ≥ 1`.

Proof sketch: `1 + q·2^q - q² = 1 + q·(2^q - q) ≥ 1` because `q ≤ 2^q`. -/
theorem le_diagonalWindowBound (q : ℕ) : (q : ℝ) ≤ diagonalWindowBound q := by
  have h := cast_le_two_pow q
  have hq : (0 : ℝ) ≤ (q : ℝ) := Nat.cast_nonneg q
  have hfac : (1 : ℝ) ≤ 1 + (q : ℝ) * 2 ^ q - (q : ℝ) ^ 2 := by nlinarith
  calc (q : ℝ) = (q : ℝ) * 1 := (mul_one _).symm
    _ ≤ (q : ℝ) * (1 + (q : ℝ) * 2 ^ q - (q : ℝ) ^ 2) := by
        exact mul_le_mul_of_nonneg_left hfac hq
    _ = diagonalWindowBound q := rfl

/-- The window bound is positive for every alphabet size `q ≥ 2`. -/
theorem diagonalWindowBound_pos {q : ℕ} (hq : 2 ≤ q) : 0 < diagonalWindowBound q := by
  have hqR : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have := le_diagonalWindowBound q
  linarith

/-- The exponent gap is positive for every alphabet size `q ≥ 2`. -/
theorem diagonalExponent_pos {q : ℕ} (hq : 2 ≤ q) : 0 < diagonalExponent q := by
  have hqR : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hlog : 0 < Real.log q := Real.log_pos (by linarith)
  have hD := diagonalWindowBound_pos hq
  rw [diagonalExponent]
  positivity

/-- The exponent gap is below `1` for every `q ≥ 2`, so `1 - diagonalExponent q ≥ 0`.

Proof sketch: the denominator is at least `q² · log q ≥ 4 · (1/2) = 2 > 1`. -/
theorem diagonalExponent_le_one {q : ℕ} (hq : 2 ≤ q) : diagonalExponent q ≤ 1 := by
  have hqR : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hlq := half_le_log hq
  have hD := le_diagonalWindowBound q
  have hDpos := diagonalWindowBound_pos hq
  have hsq : (4 : ℝ) ≤ diagonalWindowBound q ^ 2 := by nlinarith
  have hden : (1 : ℝ) ≤ diagonalWindowBound q ^ 2 * Real.log q := by nlinarith
  rw [diagonalExponent, div_le_one (by linarith)]
  linarith

/-- **The diagonal bound is a genuine saving over the trivial bound `Ī(T) ≤ q`.** -/
theorem diagonalBound_lt {q : ℕ} (hq : 2 ≤ q) : diagonalBound q < (q : ℝ) := by
  have hqR : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hpos := diagonalExponent_pos hq
  have h : (q : ℝ) ^ (1 - diagonalExponent q) < (q : ℝ) ^ (1 : ℝ) :=
    Real.rpow_lt_rpow_of_exponent_lt (by linarith) (by linarith)
  rwa [Real.rpow_one] at h

/-- `2^a - a ≤ 2^b - b` for `a ≤ b`: the natural-number monotonicity behind
`diagonalWindowBound_mono`. -/
private theorem two_pow_sub_mono {a b : ℕ} (hab : a ≤ b) : 2 ^ a - a ≤ 2 ^ b - b := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hab
  have hk : k < 2 ^ k := Nat.lt_two_pow_self
  have ha : a < 2 ^ a := Nat.lt_two_pow_self
  have hmul : 2 ^ a * 2 ^ k = 2 ^ (a + k) := (pow_add 2 a k).symm
  have hge : 2 ^ k - 1 ≤ 2 ^ (a + k) - 2 ^ a := by
    have h1 : 2 ^ a * (2 ^ k - 1) = 2 ^ (a + k) - 2 ^ a := by
      rw [Nat.mul_sub, mul_one, hmul]
    rw [← h1]
    exact Nat.le_mul_of_pos_left _ (by positivity)
  have hle : 2 ^ a ≤ 2 ^ (a + k) := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

/-- **The window bound is monotone.**  Writing `diagonalWindowBound q = q + q²·(2^q - q)`, both
factors are monotone and nonnegative. -/
theorem diagonalWindowBound_mono {a b : ℕ} (hab : a ≤ b) :
    diagonalWindowBound a ≤ diagonalWindowBound b := by
  have hcast : ∀ n : ℕ, diagonalWindowBound n = (n : ℝ) + (n : ℝ) ^ 2 * ((2 : ℝ) ^ n - n) := by
    intro n
    rw [diagonalWindowBound]
    ring
  have habR : (a : ℝ) ≤ (b : ℝ) := by exact_mod_cast hab
  have ha0 : (0 : ℝ) ≤ (a : ℝ) := Nat.cast_nonneg a
  have hsub : (2 : ℝ) ^ a - (a : ℝ) ≤ (2 : ℝ) ^ b - (b : ℝ) := by
    have hN := two_pow_sub_mono hab
    have ha : a ≤ 2 ^ a := Nat.lt_two_pow_self.le
    have hb : b ≤ 2 ^ b := Nat.lt_two_pow_self.le
    have := (Nat.cast_le (α := ℝ)).mpr hN
    rw [Nat.cast_sub ha, Nat.cast_sub hb] at this
    simpa using this
  have hnn : (0 : ℝ) ≤ (2 : ℝ) ^ a - (a : ℝ) := by
    have := cast_le_two_pow a
    linarith
  rw [hcast, hcast]
  gcongr

/-- **The exponent gap is antitone on `[2, ∞)`**: a larger alphabet gives a smaller saving.  Both
`diagonalWindowBound` and `log` are monotone, and the denominator is positive from `q = 2` on. -/
theorem diagonalExponent_anti {a b : ℕ} (ha : 2 ≤ a) (hab : a ≤ b) :
    diagonalExponent b ≤ diagonalExponent a := by
  have haR : (2 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
  have habR : (a : ℝ) ≤ (b : ℝ) := by exact_mod_cast hab
  have hla : 0 < Real.log a := Real.log_pos (by linarith)
  have hDa := diagonalWindowBound_pos ha
  have hDb := diagonalWindowBound_mono hab
  have hlog : Real.log a ≤ Real.log b := Real.log_le_log (by linarith) habR
  have hden : (0 : ℝ) < diagonalWindowBound a ^ 2 * Real.log a := by positivity
  have hle : diagonalWindowBound a ^ 2 * Real.log a ≤
      diagonalWindowBound b ^ 2 * Real.log b := by
    gcongr
  rw [diagonalExponent, diagonalExponent]
  exact one_div_le_one_div_of_le hden hle

end Diagonal

/-! ## A tiny regression client -/

section Sanity

/-- The two-term table `x₁y₀z₀ + x₀y₁z₀` over three two-element legs, written over `ℚ`.  Both
`x₁` and `y₁` occur in exactly one term, and those two terms share the variable `z₀`, so this is
the smallest instance of AVW's corner configuration.  It exists to check the direction and the
usability of the hypotheses of `asymptoticIndependenceNumber_le_cornerBound_of_corner_terms`. -/
def twoCornerTable : (∀ _ : Leg, Fin 2) → ℚ :=
  fun p ↦ if p Leg.Z = 0 ∧ p Leg.X ≠ p Leg.Y then 1 else 0

/-- The support of the two-corner table is `{x₁y₀z₀, x₀y₁z₀}`. -/
theorem twoCornerTable_ne_zero_iff (p : ∀ _ : Leg, Fin 2) :
    twoCornerTable p ≠ 0 ↔ (p Leg.Z = 0 ∧ p Leg.X ≠ p Leg.Y) := by
  unfold twoCornerTable
  by_cases h : p Leg.Z = 0 ∧ p Leg.X ≠ p Leg.Y <;> simp [h]

/-- **Regression test for AVW Corollary 5.1**: the two-corner table has asymptotic independence
number at most `c₂ = 2^{1 - 1/(36 log 2)} < 2`, even though it has two variables on each leg. -/
theorem asymptoticIndependenceNumber_twoCornerTable_le :
    asymptoticIndependenceNumber twoCornerTable ≤ cornerBound 2 := by
  have hterm : ∀ x y : Fin 2, x ≠ y → twoCornerTable (ofLegs x y (0 : Fin 2)) ≠ 0 := by
    intro x y h
    rw [twoCornerTable_ne_zero_iff]
    exact ⟨rfl, h⟩
  refine asymptoticIndependenceNumber_le_cornerBound_of_corner_terms twoCornerTable le_rfl
    (fun _ ↦ by simp) (xOne := 0) (xLast := 1) (yOne := 0) (yLast := 1) (zOne := 0)
    (by decide) (hterm 1 0 (by decide)) (hterm 0 1 (by decide)) ?_ ?_
  · intro p hp hx
    rw [twoCornerTable_ne_zero_iff] at hp
    have hy : p Leg.Y = 0 := by
      have h1 : (1 : Fin 2) ≠ p Leg.Y := hx ▸ hp.2
      revert h1
      generalize p Leg.Y = y
      revert y
      decide
    funext i
    cases i <;> simp [ofLegs, hx, hy, hp.1]
  · intro p hp hy
    rw [twoCornerTable_ne_zero_iff] at hp
    have hx : p Leg.X = 0 := by
      have h1 : p Leg.X ≠ (1 : Fin 2) := hy ▸ hp.2
      revert h1
      generalize p Leg.X = x
      revert x
      decide
    funext i
    cases i <;> simp [ofLegs, hx, hy, hp.1]

/-- The two-corner table really is bounded away from the trivial bound `Ī ≤ 2`. -/
theorem asymptoticIndependenceNumber_twoCornerTable_lt_two :
    asymptoticIndependenceNumber twoCornerTable < 2 := by
  have h := asymptoticIndependenceNumber_twoCornerTable_le
  have h2 := cornerBound_lt (q := 2) le_rfl
  norm_num at h2
  linarith

end Sanity

end AlgebraicComplexity
