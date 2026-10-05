/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.LowerTriangularBarrier
import AlgebraicComplexity.Tensor.MonomialIndependence

/-!
# AVW Theorem 7.6: which lower triangular tensors have `Ī(T) = q`

This file is the second half of milestone **N** of `BARRIER_FRAMEWORK.md`.  It proves, in both
directions,

> J. Alman and V. Vassilevska Williams, *Limits on All Known (and Some Unknown) Approaches to
> Matrix Multiplication*, arXiv:1810.08671v1, Section 7.4, **Theorem 7.6**:
>
> a lower triangular tensor `T` over `X = {x_0,…,x_{q-1}}`, `Y = {y_0,…,y_{q-1}}`,
> `Z = {z_0,…,z_{q-1}}` has `Ī(T) = q` if and only if it has `q` diagonal terms, no two of which
> share a `z`-variable.

AVW Definition 7.1 (`IsLowerTriangular`) and the trivial bound `Ī(T) ≤ q` are already recorded in
`Examples/LowerTriangularBarrier.lean`, which this module imports unchanged.

## The criterion, formally

A *diagonal term* is a term `x_i y_j z_k` with `i + j = q - 1`.  Since a lower triangular table has
at most one `z`-variable per `(x, y)`-pair, there is at most one diagonal term for each `j`, namely
the one in the cell `(x_{q-1-j}, y_j)`; `Fin.rev j` is the repository's `q - 1 - j`.  AVW's "`q`
diagonal terms no two of which share a `z`-variable" is therefore

```text
HasIndependentDiagonal T : ∃ g : Fin q ≃ Fin q, ∀ j, T (x_{rev j} y_j z_{g j}) ≠ 0,
```

an *equivalence* `g`, not merely an injection: `q` distinct `z`-variables among `q` available ones
exhaust them.  The dual formulation `DiagonalCoversZ T` — every `z`-variable occurs in some
diagonal term — is equivalent (`hasIndependentDiagonal_iff_diagonalCoversZ`) and is the form the
hard direction refutes.

## Main results

* `HasIndependentDiagonal`, `DiagonalCoversZ`, `hasIndependentDiagonal_iff_diagonalCoversZ`.
* `diagonalCellMass_ge` --- **the inductive core**, with the closed-form constant AVW leave as
  `O_q(κ)`: for a near-uniform mass distribution with window `1/q - u`,
  ```text
  p(x_{q-1-j} y_j z_{f(q-1-j,j)}) ≥ 1/q - (q·2^j - q + 1)·u.
  ```
* `diagonalExponent_le_of_asymptoticIndependenceNumber_ge` --- the quantitative core: a lower
  triangular table whose diagonal misses a `z`-variable and satisfies `q^{1-δ} ≤ Ī(T)` has
  `δ ≥ diagonalExponent q = 1/(diagonalWindowBound q ² · log q)`, with
  `diagonalWindowBound q = q(1 + q·2^q - q²)`.
* `asymptoticIndependenceNumber_le_diagonalBound_of_not_hasIndependentDiagonal` --- the
  quantitative form of the hard direction, `Ī(T) ≤ q^{1 - diagonalExponent q} < q`.
* `le_asymptoticIndependenceNumber_of_hasIndependentDiagonal` --- the easy direction, `q ≤ Ī(T)`.
* `avw_theorem_seven_six` --- **AVW Theorem 7.6**, `Ī(T) = q ↔ HasIndependentDiagonal T`.
* `independentDiagonalTable`, `asymptoticIndependenceNumber_independentDiagonalTable` and the
  regression clients at `q = 2, 3`; `not_hasIndependentDiagonal_lowerTriangularTable`, the check
  that `T_q^lower` fails the criterion, consistently with AVW Theorem 7.5.

## The proof of the hard direction, and the explicit constant

Fix `δ ≥ 0` with `q^{1-δ} ≤ Ī(T)` and `ρ > 0`.  AVW Theorem 5.2
(`Tensor.exists_probabilityVector_uniformWindow_le_supportMarginal`) supplies a probability
distribution `m` on the terms of `T` whose marginal on every variable of every leg is at least
`1/q - u`, where `u = sqrt((δ + ρ) log q)`.  Dually every marginal is at most
`1 - (q-1)(1/q - u) = 1/q + (q-1)u` (`ProbabilityVector.weight_le_one_sub_of_forall_le`).

Write `P(j)` for the mass of the cell `(x_{rev j}, y_j)` and `Q(i, j')` for the mass of the cell
`(x_i, y_{j'})` (`Tensor.supportCellMass`; by AVW Definition 7.1's first clause each cell holds at
most one term, so these are the masses of individual terms).  Triangularity gives two facts:

* `p(x_{rev j}) = ∑_{j' ≤ j} Q(rev j, j')`, because a term with `x`-index `q-1-j` and `y`-index
  `j' > j` would have `i + j' ≥ q`; and
* `Q(rev j, j') + P(j') ≤ p(y_{j'})` for `j' < j`, because those are two *distinct* cells of the
  `y_{j'}`-fiber (`rev j ≠ rev j'`).

Ordinary induction on `j` with the invariant `P(j) ≥ 1/q - c_j·u` then works with the closed form
`c_j = q·2^j - q + 1`: the step bound is `Q(rev j, j') ≤ (q - 1 + c_{j'})·u = q·2^{j'}·u`, and
`∑_{j' < j} q·2^{j'} = q·(2^j - 1)`, so `c_j = 1 + q(2^j - 1)`, which is the same number.

Finally, if some `z_k` occurs in no diagonal term, the `q` diagonal cells (pairwise disjoint,
since `rev` is injective) and the `z_k`-fiber are pairwise disjoint families of terms
(`Tensor.sum_supportCellMass_add_supportMarginal_le_one`), so

```text
1/q - u ≤ p(z_k) ≤ 1 - ∑_j P(j) ≤ (∑_j c_j)·u = (q·2^q - q²)·u,
```

that is `1 ≤ q(1 + q·2^q - q²)·u = diagonalWindowBound q · u`.  Squaring and letting `ρ → 0` gives
`δ ≥ 1/(diagonalWindowBound q ² · log q) = diagonalExponent q`.

**The constant is exponentially small in `q`.**  The window deficit doubles at every step of the
induction, so `diagonalWindowBound q` is exponential and the gap `q - diagonalBound q` is tiny.
For the specific table `T_q^lower` the corner bound of `Examples/LowerTriangularBarrier.lean` (AVW
Theorem 7.5, gap `1/(q²(q+1)² log q)`) is far sharper; Theorem 7.6 buys generality, not strength.
AVW themselves only claim `O_q(κ)`.

## The easy direction

Give the `ℕ`-weights `w_X(x_i) = q-1-i`, `w_Y(y_j) = q-1-j`, `w_Z(z_k) = 0` and threshold
`d = q-1`.  A term of a lower triangular table has `i + j ≤ q - 1`, so its total weight
`2(q-1) - (i+j)` is at least `q - 1`, with equality exactly on the diagonal.  Hence
`Tensor.MonomialIndependence.minimumWeightPart w (q-1) T` is the sub-table of diagonal terms, and
the `q` diagonal terms of the criterion form an `IndependentSet` of it: their `x`-, `y`- and
`z`-variables are pairwise distinct (the last by the criterion), and closure holds because
`i + j = q - 1` determines `j` from `i` and Definition 7.1's first clause then determines the
term.  AVW Corollary 4.1 (`Tensor.card_le_asymptoticIndependenceNumber`) gives `q ≤ Ī(T)`, and
`Tensor.asymptoticIndependenceNumber_le_card` gives the equality.

## Errata in the printed proof

Seven small discrepancies between AVW's text and what is proved here.

* **(a)** Definition 7.1's second clause quantifies `k` over `{1, …, q}` where the variable set is
  `{z_0, …, z_{q-1}}`; the intended range is `{0, …, q-1}`.  Immaterial: the clause says the term
  is absent for *every* `k`.
* **(b)** Theorem 5.2 is quoted with a bare `κ > 0` playing simultaneously the role of the
  slack parameter and of the window deficit.  They are different: the deficit is
  `u = sqrt((δ + ρ) log q)`, and it is `u`, not `ρ`, that the induction multiplies.  Here `ρ` is
  AVW's `κ`, renamed because `κ` names the leg variable types.
* **(c)** The inductive step displays `p(x_{q-1-j} y_{j'} z_{f(i,j')})` with a free index `i`; it
  should be `f(q-1-j, j')`.  The formal statement has no such index because the quantity is the
  mass of a *cell*, not of a named term.
* **(d)** The proof assumes "such a term exists for each `i, j`" and remarks that otherwise the
  argument is simpler.  No case split is needed: an absent term is an empty cell of mass `0`, and
  the induction proves `P(j) ≥ 1/q - c_j u > 0` for small `u` regardless, so the terms are in fact
  forced to exist.  `diagonalCellMass_ge` is stated for arbitrary lower triangular tables.
* **(e)** The easy direction uses the `ℤ`-valued monomial weights `a(x_i) = b(y_i) = -i`,
  `c(z_i) = q-1`.  `Tensor/Monomial.lean` takes `ℕ`-valued weights with a threshold; the shifted
  weights `q-1-i, q-1-j, 0` with threshold `q-1` are the same monomial degeneration
  (`BARRIER_FRAMEWORK.md` §2.1).
* **(f)** The proof says "lower diagonal tensor" twice for "lower triangular tensor".
* **(g)** The statement is an equality `Ī(T) = q`, but only `Ī(T) ≥ q` has content: `Ī(T) ≤ q`
  holds for every table on `q` variables per leg (`asymptoticIndependenceNumber_le_card`, recorded
  as `asymptoticIndependenceNumber_le_card_of_isLowerTriangular`).

## Hypotheses

The coefficient ring is a commutative semiring throughout.  `NoZeroDivisors` is what AVW
Theorem 5.2 needs (products of coefficients of a Kronecker power must not vanish), and the easy
direction adds `Nontrivial` for the same reason through AVW Corollary 4.1.  **No field is
required**, unlike the surrounding barrier chain, because neither slice rank nor asymptotic rank
appears.

## Layer placement

Layer 4 (`AlgebraicComplexity/Examples/`).  It consumes AVW Theorem 5.2 and the cell-mass calculus
of `MatrixMultiplication/IndependenceMassDistribution.lean`, AVW Corollary 4.1 of
`Tensor/MonomialIndependence.lean`, and Definition 7.1 of `Examples/LowerTriangularBarrier.lean`.

## References

* J. Alman and V. Vassilevska Williams, *Limits on All Known (and Some Unknown) Approaches to
  Matrix Multiplication*, arXiv:1810.08671v1, Section 7.4 (Definition 7.1, Theorem 7.6), Section 5
  (Theorem 5.2) and Section 4 (Corollary 4.1).
-/

open scoped BigOperators

namespace AlgebraicComplexity.Examples

open Tensor

universe u

/-! ## AVW's criterion -/

section Criterion

variable {K : Type u} [CommSemiring K] {q : ℕ}

/-- **AVW Theorem 7.6's criterion**: `T` has `q` diagonal terms, no two of which share a
`z`-variable.

A diagonal term is a term `x_i y_j z_k` with `i + j = q - 1`, i.e. `i = Fin.rev j`.  A family of
`q` of them, one for each `j`, with pairwise distinct `z`-variables is the same thing as a
*bijection* `g : Fin q ≃ Fin q` with `x_{rev j} y_j z_{g j}` a term for every `j`, because `q`
distinct `z`-variables out of `q` available ones exhaust them. -/
def HasIndependentDiagonal (T : (∀ i, LowerTriangularIndex q i) → K) : Prop :=
  ∃ g : Fin q ≃ Fin q, ∀ j : Fin q, T (ofLegs (Fin.rev j) j (g j)) ≠ 0

/-- The dual form of AVW's criterion: every `z`-variable occurs in some diagonal term.  For a
lower triangular table this is equivalent to `HasIndependentDiagonal`
(`hasIndependentDiagonal_iff_diagonalCoversZ`), and it is the form the hard direction refutes. -/
def DiagonalCoversZ (T : (∀ i, LowerTriangularIndex q i) → K) : Prop :=
  ∀ k : Fin q, ∃ j : Fin q, T (ofLegs (Fin.rev j) j k) ≠ 0

/-- The `x`- and `y`-indices of a diagonal term add up to `q - 1`. -/
theorem val_rev_add_val (j : Fin q) : (Fin.rev j : ℕ) + (j : ℕ) = q - 1 := by
  have h := j.isLt
  rw [Fin.val_rev]
  omega

/-- **Cells strictly below the diagonal band are empty.**  A term of a lower triangular table with
`x`-index `q-1-j` has `y`-index at most `j`: a larger one would make `i + j' ≥ q`. -/
theorem IsLowerTriangular.cell_eq_zero_of_lt {T : (∀ i, LowerTriangularIndex q i) → K}
    (h : IsLowerTriangular T) {j j' : Fin q} (hlt : j < j')
    (p : ∀ i, LowerTriangularIndex q i) (hp : T p ≠ 0) (hx : p .X = Fin.rev j) :
    p .Y ≠ j' := by
  intro hy
  have htri := h.triangular p hp
  rw [hx, hy, Fin.val_rev] at htri
  have h1 := j.isLt
  have h2 : (j : ℕ) < (j' : ℕ) := hlt
  omega

/-- **The two forms of AVW's criterion agree** for a lower triangular table: a bijective family of
diagonal terms exists exactly when every `z`-variable occurs in a diagonal term.

Proof sketch: `unique_z` makes the assignment `j ↦ (the `z`-variable of the diagonal term in cell
`(x_{rev j}, y_j)`)` a partial function, so a surjective choice `k ↦ j(k)` is injective, hence
bijective on the finite type `Fin q`, and its inverse is the required equivalence. -/
theorem hasIndependentDiagonal_iff_diagonalCoversZ {T : (∀ i, LowerTriangularIndex q i) → K}
    (h : IsLowerTriangular T) :
    HasIndependentDiagonal T ↔ DiagonalCoversZ T := by
  constructor
  · rintro ⟨g, hg⟩ k
    refine ⟨g.symm k, ?_⟩
    simpa using hg (g.symm k)
  · intro hcov
    choose j hj using hcov
    have hinj : Function.Injective j := by
      intro k k' hkk
      have heq := h.unique_z _ _ (hj k) (hj k') (by simp [hkk]) (by simp [hkk])
      simpa using congrFun heq Leg.Z
    let e : Fin q ≃ Fin q := Equiv.ofBijective j (Finite.injective_iff_bijective.mp hinj)
    refine ⟨e.symm, fun i ↦ ?_⟩
    have hji : j (e.symm i) = i := e.apply_symm_apply i
    have := hj (e.symm i)
    rwa [hji] at this

end Criterion

/-! ## The inductive core (AVW's `p(x_{q-1-j} y_j z_{f(q-1-j,j)}) ≥ 1/q - O_q(κ)`) -/

section Induction

variable {K : Type u} [CommSemiring K] {q : ℕ}

/-- **The inductive core of AVW Theorem 7.6, with the closed-form constant.**  Let `T` be lower
triangular over `q ≥ 2` variables per leg and let `m` be a mass distribution on its terms whose
marginal on every variable of every leg is at least `1/q - u`.  Then the diagonal cell
`(x_{q-1-j}, y_j)` carries mass at least

```text
1/q - (q·2^j - q + 1)·u.
```

AVW write `1/q - O_q(κ)`; the constant `c_j = q·2^j - q + 1` is what their induction produces, and
it doubles at every step, which is why the resulting exponent gap is exponentially small in `q`.

Proof sketch (ordinary induction on `j`, AVW use strong induction but only `j' < j` is needed).
Triangularity empties the cells `(x_{rev j}, y_{j'})` with `j' > j`, so the `x_{rev j}`-fiber is
the disjoint union of the cells `(x_{rev j}, y_{j'})` with `j' ≤ j`, one of which is the diagonal
cell.  For `j' < j`, the cells `(x_{rev j}, y_{j'})` and `(x_{rev j'}, y_{j'})` are two distinct
cells of the `y_{j'}`-fiber, so the first has mass at most
`p(y_{j'}) - P(j') ≤ (1/q + (q-1)u) - (1/q - c_{j'}u) = q·2^{j'}·u` by the induction hypothesis and
the dual window bound `ProbabilityVector.weight_le_one_sub_of_forall_le`.  Summing the geometric
series `∑_{j' < j} q·2^{j'} = q(2^j - 1)` and subtracting from `p(x_{rev j}) ≥ 1/q - u` gives
`1/q - (1 + q(2^j - 1))·u`, and `1 + q·2^j - q = c_j`. -/
theorem diagonalCellMass_ge (hq : 2 ≤ q) {T : (∀ i, LowerTriangularIndex q i) → K}
    (hT : IsLowerTriangular T) (m : ProbabilityVector {p // p ∈ coordinateSupport T}) {u : ℝ}
    (hm : ∀ (c : Leg) (a : LowerTriangularIndex q c),
      1 / (q : ℝ) - u ≤ (supportMarginal T m c).weight a)
    (j : Fin q) :
    1 / (q : ℝ) - ((q : ℝ) * 2 ^ (j : ℕ) - (q : ℝ) + 1) * u ≤
      supportCellMass T m Leg.X Leg.Y (Fin.rev j) j := by
  classical
  have hqR : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hqpos : (0 : ℝ) < (q : ℝ) := by linarith
  have hqi : (q : ℝ) * (1 / (q : ℝ)) = 1 := by field_simp
  -- the dual window: every marginal is also bounded above
  have hup : ∀ (c : Leg) (a : LowerTriangularIndex q c),
      (supportMarginal T m c).weight a ≤ 1 - ((q : ℝ) - 1) * (1 / (q : ℝ) - u) := by
    intro c a
    have h := (supportMarginal T m c).weight_le_one_sub_of_forall_le (fun b ↦ hm c b) a
    simpa using h
  -- the cell masses of the `x_{rev jj}`-fiber, indexed by natural numbers
  set C : Fin q → ℕ → ℝ := fun jj i ↦
    if h : i < q then supportCellMass T m Leg.X Leg.Y (Fin.rev jj) ⟨i, h⟩ else 0 with hC
  have hCval : ∀ (jj : Fin q) (b : Fin q),
      C jj (b : ℕ) = supportCellMass T m Leg.X Leg.Y (Fin.rev jj) b := by
    intro jj b
    rw [hC]
    simp only [dif_pos b.isLt]
  -- the fiber splits into the diagonal cell and the cells to its left
  have hsplit : ∀ jj : Fin q,
      (supportMarginal T m Leg.X).weight (Fin.rev jj) =
        supportCellMass T m Leg.X Leg.Y (Fin.rev jj) jj
          + ∑ i ∈ Finset.range (jj : ℕ), C jj i := by
    intro jj
    have h1 : (supportMarginal T m Leg.X).weight (Fin.rev jj) =
        ∑ b : Fin q, supportCellMass T m Leg.X Leg.Y (Fin.rev jj) b :=
      supportMarginal_weight_eq_sum_supportCellMass T m Leg.X Leg.Y (Fin.rev jj)
    have h2 : ∑ b : Fin q, supportCellMass T m Leg.X Leg.Y (Fin.rev jj) b =
        ∑ i ∈ Finset.range q, C jj i := by
      rw [← Fin.sum_univ_eq_sum_range (C jj) q]
      exact Finset.sum_congr rfl fun b _ ↦ (hCval jj b).symm
    have h3 : ∑ i ∈ Finset.range q, C jj i = ∑ i ∈ Finset.range ((jj : ℕ) + 1), C jj i := by
      refine (Finset.sum_subset ?_ ?_).symm
      · intro i hi
        rw [Finset.mem_range] at hi
        rw [Finset.mem_range]
        have := jj.isLt
        omega
      · intro i hi hnot
        rw [Finset.mem_range] at hi
        rw [Finset.mem_range] at hnot
        have hiq : i < q := hi
        have hlt : jj < (⟨i, hiq⟩ : Fin q) := by
          simp only [Fin.lt_def]
          omega
        rw [hC]
        simp only [dif_pos hiq]
        exact supportCellMass_eq_zero m fun p hp hx ↦
          hT.cell_eq_zero_of_lt hlt p hp hx
    rw [h1, h2, h3, Finset.sum_range_succ, hCval jj jj]
    ring
  -- the geometric sum appearing in the step
  have hgeom : ∀ n : ℕ, ∑ i ∈ Finset.range n, ((q : ℝ) * 2 ^ i * u) =
      (q : ℝ) * u * (2 ^ n - 1) := by
    intro n
    have h1 : ∑ i ∈ Finset.range n, ((q : ℝ) * 2 ^ i * u) =
        ((q : ℝ) * u) * ∑ i ∈ Finset.range n, (2 : ℝ) ^ i := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ ↦ by ring
    rw [h1, geom_sum_eq (by norm_num : (2 : ℝ) ≠ 1) n]
    norm_num
  -- the induction proper
  have main : ∀ n : ℕ, ∀ jj : Fin q, (jj : ℕ) = n →
      1 / (q : ℝ) - ((q : ℝ) * 2 ^ (jj : ℕ) - (q : ℝ) + 1) * u ≤
        supportCellMass T m Leg.X Leg.Y (Fin.rev jj) jj := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro jj hjj
      have hcell : ∀ i ∈ Finset.range (jj : ℕ), C jj i ≤ (q : ℝ) * 2 ^ i * u := by
        intro i hi
        rw [Finset.mem_range] at hi
        have hiq : i < q := lt_trans hi jj.isLt
        have hprev := ih i (by omega) ⟨i, hiq⟩ rfl
        have hne : Fin.rev jj ≠ Fin.rev (⟨i, hiq⟩ : Fin q) := by
          intro hEq
          have := Fin.rev_injective hEq
          have : (jj : ℕ) = i := congrArg Fin.val this
          omega
        have hadd := add_supportCellMass_le_supportMarginal_weight T m
          (c := Leg.X) (d := Leg.Y) (a := Fin.rev jj) (a' := Fin.rev (⟨i, hiq⟩ : Fin q))
          (b := (⟨i, hiq⟩ : Fin q)) hne
        have hupY := hup Leg.Y (⟨i, hiq⟩ : Fin q)
        rw [hC]
        simp only [dif_pos hiq]
        linarith [hqi, hadd, hupY, hprev]
      have hsum : ∑ i ∈ Finset.range (jj : ℕ), C jj i ≤ (q : ℝ) * u * (2 ^ (jj : ℕ) - 1) := by
        rw [← hgeom]
        exact Finset.sum_le_sum hcell
      have hlow := hm Leg.X (Fin.rev jj)
      have hfib := hsplit jj
      linarith
  exact main (j : ℕ) j rfl

end Induction

/-! ## The quantitative hard direction -/

section Quantitative

variable {K : Type u} [CommSemiring K] [NoZeroDivisors K] {q : ℕ}

/-- **The quantitative core of AVW Theorem 7.6.**  Let `T` be a nonzero lower triangular table on
`q ≥ 2` variables per leg some of whose `z`-variables occurs in no diagonal term.  Then every
`δ ≥ 0` with `q^{1-δ} ≤ Ī(T)` satisfies `diagonalExponent q ≤ δ`.

Proof sketch: fix `ρ > 0` and take the near-uniform mass distribution `m` of AVW Theorem 5.2, with
window `1/q - u`, `u = sqrt((δ + ρ) log q)`.  `diagonalCellMass_ge` bounds each of the `q` diagonal
cells below by `1/q - c_j u`; the missed `z`-variable `k` gives a fiber disjoint from all of them
(`Tensor.sum_supportCellMass_add_supportMarginal_le_one`, whose injectivity hypothesis is
injectivity of `Fin.rev`), so the `q + 1` masses sum to at most `1`.  Since
`∑_{j<q} c_j = q·2^q - q²` and `p(z_k) ≥ 1/q - u`, this reads `1 ≤ diagonalWindowBound q · u`.
Squaring and letting `ρ → 0` gives `1/diagonalWindowBound q ² ≤ δ log q`. -/
theorem diagonalExponent_le_of_asymptoticIndependenceNumber_ge (hq : 2 ≤ q)
    {T : (∀ i, LowerTriangularIndex q i) → K} (hT : IsLowerTriangular T)
    {p₀ : ∀ i, LowerTriangularIndex q i} (hp₀ : T p₀ ≠ 0) (hbad : ¬ DiagonalCoversZ T)
    {δ : ℝ} (hδ : 0 ≤ δ) (hI : (q : ℝ) ^ (1 - δ) ≤ asymptoticIndependenceNumber T) :
    diagonalExponent q ≤ δ := by
  classical
  have hqR : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hqpos : (0 : ℝ) < (q : ℝ) := by linarith
  have hqi : (q : ℝ) * (1 / (q : ℝ)) = 1 := by field_simp
  have hlogpos : 0 < Real.log q := Real.log_pos (by linarith)
  have hDpos := diagonalWindowBound_pos hq
  have hcard : ∀ c : Leg, Fintype.card (LowerTriangularIndex q c) = q :=
    fun _ ↦ Fintype.card_fin q
  obtain ⟨k, hk⟩ : ∃ k : Fin q, ∀ j : Fin q, T (ofLegs (Fin.rev j) j k) = 0 := by
    rw [DiagonalCoversZ] at hbad
    push Not at hbad
    exact hbad
  -- the geometric total of the induction constants
  have hgeom : ∑ j : Fin q, (2 : ℝ) ^ (j : ℕ) = 2 ^ q - 1 := by
    rw [Fin.sum_univ_eq_sum_range (fun i ↦ (2 : ℝ) ^ i) q,
      geom_sum_eq (by norm_num : (2 : ℝ) ≠ 1) q]
    norm_num
  -- Step 1: for every `ρ > 0` the window forces `1/diagonalWindowBound q ≤ u`.
  have key : ∀ ρ : ℝ, 0 < ρ →
      1 / diagonalWindowBound q ≤ Real.sqrt ((δ + ρ) * Real.log q) := by
    intro ρ hρ
    obtain ⟨m, hm⟩ :=
      exists_probabilityVector_uniformWindow_le_supportMarginal T hp₀ hq hcard hδ hI hρ
    set u : ℝ := Real.sqrt ((δ + ρ) * Real.log q) with hu
    have hcells := fun j ↦ diagonalCellMass_ge hq hT m hm j
    have hz := hm Leg.Z k
    -- the `q` diagonal cells and the `z_k`-fiber are pairwise disjoint
    have hone := sum_supportCellMass_add_supportMarginal_le_one (T := T) m
      (c := Leg.X) (d := Leg.Y) (e := Leg.Z) (f := Fin.rev) Fin.rev_injective id k ?_
    case refine_1 =>
      intro p hp i hx hy hz'
      have hpe : p = ofLegs (Fin.rev i) i k := by
        funext c
        cases c with
        | X => exact hx
        | Y => exact hy
        | Z => exact hz'
      rw [hpe] at hp
      exact hp (hk i)
    -- add up the lower bounds
    have hsumle : ∑ j : Fin q, (1 / (q : ℝ) - ((q : ℝ) * 2 ^ (j : ℕ) - (q : ℝ) + 1) * u) ≤
        ∑ j : Fin q, supportCellMass T m Leg.X Leg.Y (Fin.rev j) (id j) :=
      Finset.sum_le_sum fun j _ ↦ hcells j
    have hsumval : ∑ j : Fin q, (1 / (q : ℝ) - ((q : ℝ) * 2 ^ (j : ℕ) - (q : ℝ) + 1) * u) =
        (q : ℝ) * (1 / (q : ℝ)) - ((q : ℝ) * 2 ^ q - (q : ℝ) ^ 2) * u := by
      have hstep : ∀ j : Fin q,
          (1 / (q : ℝ) - ((q : ℝ) * 2 ^ (j : ℕ) - (q : ℝ) + 1) * u) =
            (1 / (q : ℝ) + ((q : ℝ) - 1) * u) - ((q : ℝ) * u) * 2 ^ (j : ℕ) := by
        intro j; ring
      rw [Finset.sum_congr rfl fun j _ ↦ hstep j, Finset.sum_sub_distrib, ← Finset.mul_sum,
        hgeom, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring
    rw [hsumval] at hsumle
    have hstep : 1 / (q : ℝ) ≤ ((q : ℝ) * 2 ^ q - (q : ℝ) ^ 2 + 1) * u := by
      linarith [hone, hsumle, hz, hqi]
    have hDu : 1 ≤ diagonalWindowBound q * u := by
      have h := mul_le_mul_of_nonneg_left hstep hqpos.le
      rw [hqi] at h
      rw [diagonalWindowBound]
      linarith
    rw [div_le_iff₀ hDpos]
    linarith
  -- Step 2: square, and let `ρ` tend to `0`.
  have hsq : ∀ ρ : ℝ, 0 < ρ →
      1 / diagonalWindowBound q ^ 2 ≤ (δ + ρ) * Real.log q := by
    intro ρ hρ
    have h := key ρ hρ
    have harg : (0 : ℝ) ≤ (δ + ρ) * Real.log q := mul_nonneg (by linarith) hlogpos.le
    have hsqrt : Real.sqrt ((δ + ρ) * Real.log q) ^ 2 = (δ + ρ) * Real.log q :=
      Real.sq_sqrt harg
    have hnn : (0 : ℝ) ≤ 1 / diagonalWindowBound q := by positivity
    have hpow : (1 / diagonalWindowBound q) ^ 2 ≤
        Real.sqrt ((δ + ρ) * Real.log q) ^ 2 := by
      rw [sq, sq]; exact mul_self_le_mul_self hnn h
    rw [div_pow, one_pow, hsqrt] at hpow
    exact hpow
  have hlim : 1 / diagonalWindowBound q ^ 2 ≤ δ * Real.log q := by
    refine le_of_forall_pos_le_add fun η hη ↦ ?_
    have h := hsq (η / Real.log q) (by positivity)
    have hexp : (δ + η / Real.log q) * Real.log q = δ * Real.log q + η := by field_simp
    rwa [hexp] at h
  -- Step 3: rearrange into the stated exponent gap.
  have hP : (0 : ℝ) < diagonalWindowBound q ^ 2 := by positivity
  have h2 := mul_le_mul_of_nonneg_left hlim hP.le
  rw [mul_one_div, div_self (ne_of_gt hP)] at h2
  rw [diagonalExponent, div_le_iff₀ (mul_pos hP hlogpos)]
  linarith

omit [NoZeroDivisors K] in
/-- A table with no terms at all has `Ī(T) ≤ 1`: every Kronecker power of positive exponent is
identically zero, so it admits no nonempty independent set. -/
theorem asymptoticIndependenceNumber_le_one_of_forall_eq_zero
    {κ : Leg → Type*} [∀ i, Fintype (κ i)] [∀ i, DecidableEq (κ i)]
    {T : (∀ i, κ i) → K} (hzero : ∀ p, T p = 0) :
    asymptoticIndependenceNumber T ≤ 1 := by
  classical
  refine Growth.supermultiplicativeLimit_le fun n hn ↦ ?_
  have hn0 : 0 < n := hn
  have hI : independenceNumberPowerSequence T n = 0 := by
    refine Nat.le_zero.mp (independenceNumber_le fun S hS ↦ ?_)
    have hempty : S = ∅ := by
      refine Finset.eq_empty_of_forall_notMem fun p hp ↦ ?_
      have hne := hS.ne_zero p hp
      rw [coordinatePower_apply] at hne
      exact hne (Finset.prod_eq_zero (Finset.mem_univ (⟨0, hn0⟩ : Fin n)) (hzero _))
    simp [hempty]
  have hne : ((n : ℝ))⁻¹ ≠ 0 := by
    have : (0 : ℝ) < n := by exact_mod_cast hn0
    positivity
  simp [Growth.nthRootSeq, hI, Real.zero_rpow hne]

/-- **The quantitative form of the hard direction of AVW Theorem 7.6.**  A lower triangular table
on `q ≥ 2` variables per leg whose diagonal misses a `z`-variable satisfies

```text
Ī(T) ≤ diagonalBound q = q^{1 - diagonalExponent q} < q.
```

Proof sketch: if `T` has no terms then `Ī(T) ≤ 1 ≤ diagonalBound q`.  Otherwise `Ī(T)` lies in
`[1, q]`, so it is `q^{1-δ}` for `δ = 1 - log_q Ī(T) ≥ 0`;
`diagonalExponent_le_of_asymptoticIndependenceNumber_ge` bounds that `δ` below by
`diagonalExponent q`, and `x ↦ q^x` is monotone. -/
theorem asymptoticIndependenceNumber_le_diagonalBound_of_not_diagonalCoversZ (hq : 2 ≤ q)
    {T : (∀ i, LowerTriangularIndex q i) → K} (hT : IsLowerTriangular T)
    (hbad : ¬ DiagonalCoversZ T) :
    asymptoticIndependenceNumber T ≤ diagonalBound q := by
  have hqR : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hqpos : (0 : ℝ) < (q : ℝ) := by linarith
  have hone : (1 : ℝ) ≤ diagonalBound q := by
    have h : (q : ℝ) ^ (0 : ℝ) ≤ (q : ℝ) ^ (1 - diagonalExponent q) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith)
        (by have := diagonalExponent_le_one hq; linarith)
    rwa [Real.rpow_zero] at h
  by_cases hzero : ∀ p, T p = 0
  · exact le_trans (asymptoticIndependenceNumber_le_one_of_forall_eq_zero hzero) hone
  push Not at hzero
  obtain ⟨p₀, hp₀⟩ := hzero
  have h1 : (1 : ℝ) ≤ asymptoticIndependenceNumber T := by
    refine le_trans ?_ (independenceNumber_le_asymptoticIndependenceNumber T)
    exact_mod_cast one_le_independenceNumber hp₀
  have hIq : asymptoticIndependenceNumber T ≤ (q : ℝ) :=
    asymptoticIndependenceNumber_le_card_of_isLowerTriangular hT
  have hlogpos : 0 < Real.log q := Real.log_pos (by linarith)
  set L : ℝ := Real.log (asymptoticIndependenceNumber T) / Real.log q with hLdef
  have hrl : (q : ℝ) ^ L = asymptoticIndependenceNumber T := by
    have hmul : Real.log q * (Real.log (asymptoticIndependenceNumber T) / Real.log q) =
        Real.log (asymptoticIndependenceNumber T) := by field_simp
    rw [Real.rpow_def_of_pos hqpos, hLdef, hmul, Real.exp_log (by linarith)]
  have hL1 : L ≤ 1 := by
    rw [hLdef, div_le_one hlogpos]
    exact Real.log_le_log (by linarith) hIq
  have hδ : (0 : ℝ) ≤ 1 - L := by linarith
  have hI' : (q : ℝ) ^ (1 - (1 - L)) ≤ asymptoticIndependenceNumber T := by
    rw [show (1 : ℝ) - (1 - L) = L by ring, hrl]
  have he := diagonalExponent_le_of_asymptoticIndependenceNumber_ge hq hT hp₀ hbad hδ hI'
  rw [diagonalBound, ← hrl]
  exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)

/-- **The quantitative form of the hard direction of AVW Theorem 7.6**, stated with AVW's own
criterion: a lower triangular table on `q ≥ 2` variables per leg *without* `q` diagonal terms of
pairwise distinct `z`-variables has `Ī(T) ≤ q^{1 - diagonalExponent q} < q`. -/
theorem asymptoticIndependenceNumber_le_diagonalBound_of_not_hasIndependentDiagonal (hq : 2 ≤ q)
    {T : (∀ i, LowerTriangularIndex q i) → K} (hT : IsLowerTriangular T)
    (hbad : ¬ HasIndependentDiagonal T) :
    asymptoticIndependenceNumber T ≤ diagonalBound q :=
  asymptoticIndependenceNumber_le_diagonalBound_of_not_diagonalCoversZ hq hT
    fun hcov ↦ hbad ((hasIndependentDiagonal_iff_diagonalCoversZ hT).mpr hcov)

end Quantitative

/-! ## The easy direction -/

section Easy

variable {K : Type u} [CommSemiring K] [NoZeroDivisors K] [Nontrivial K] {q : ℕ}

/-- The `ℕ`-valued monomial weights of AVW's easy direction, shifted to be nonnegative:
`w_X(x_i) = q-1-i`, `w_Y(y_j) = q-1-j`, `w_Z(z_k) = 0`.  With threshold `q-1` these define the
same monomial degeneration as AVW's `a(x_i) = b(y_i) = -i`, `c(z_i) = q-1`. -/
def diagonalWeight (q : ℕ) : ∀ i, LowerTriangularIndex q i → ℕ :=
  ofLegs (V := fun i ↦ LowerTriangularIndex q i → ℕ)
    (fun a ↦ q - 1 - (a : ℕ)) (fun a ↦ q - 1 - (a : ℕ)) (fun _ ↦ 0)

/-- The total `diagonalWeight` of a triple is `(q-1-i) + (q-1-j)`. -/
theorem monomialTotalWeight_diagonalWeight (p : ∀ i, LowerTriangularIndex q i) :
    monomialTotalWeight (diagonalWeight q) p =
      (q - 1 - (p .X : ℕ)) + (q - 1 - (p .Y : ℕ)) := by
  simp [monomialTotalWeight, diagonalWeight]

omit [NoZeroDivisors K] [Nontrivial K] in
/-- **Every term of a lower triangular table has total weight at least `q-1`**, with equality
exactly on the diagonal: `i + j ≤ q - 1` gives `(q-1-i) + (q-1-j) ≥ q-1`. -/
theorem le_monomialTotalWeight_diagonalWeight {T : (∀ i, LowerTriangularIndex q i) → K}
    (hT : IsLowerTriangular T) (p : ∀ i, LowerTriangularIndex q i) (hp : T p ≠ 0) :
    q - 1 ≤ monomialTotalWeight (diagonalWeight q) p := by
  have htri := hT.triangular p hp
  have h1 := (p .X).isLt
  have h2 := (p .Y).isLt
  rw [monomialTotalWeight_diagonalWeight]
  omega

/-- **The easy direction of AVW Theorem 7.6**: a lower triangular table with `q` diagonal terms of
pairwise distinct `z`-variables has `q ≤ Ī(T)`.

Proof sketch: the weights `diagonalWeight q` with threshold `q-1` degenerate `T` onto the sub-table
of its diagonal terms (`le_monomialTotalWeight_diagonalWeight`, and the total weight is exactly
`q-1` precisely when `i + j = q-1`).  The `q` terms `x_{rev j} y_j z_{g j}` form an independent set
of that minimum-weight part: their `x`-, `y`- and `z`-variables are pairwise distinct, and closure
holds because a diagonal term with `x`-index `rev j` has `y`-index `j`, whence Definition 7.1's
first clause identifies it with the chosen one.  AVW Corollary 4.1
(`Tensor.card_le_asymptoticIndependenceNumber`) concludes. -/
theorem le_asymptoticIndependenceNumber_of_hasIndependentDiagonal
    {T : (∀ i, LowerTriangularIndex q i) → K} (hT : IsLowerTriangular T)
    (hd : HasIndependentDiagonal T) :
    (q : ℝ) ≤ asymptoticIndependenceNumber T := by
  classical
  obtain ⟨g, hg⟩ := hd
  set term : Fin q → (∀ i, LowerTriangularIndex q i) :=
    fun j ↦ ofLegs (Fin.rev j) j (g j) with hterm
  have htermInj : Function.Injective term := by
    intro j j' h
    have := congrFun h Leg.Y
    simpa [hterm] using this
  set S : Finset (∀ i, LowerTriangularIndex q i) := Finset.image term Finset.univ with hS
  have hmemS : ∀ p, p ∈ S ↔ ∃ j : Fin q, term j = p := by
    intro p
    simp [hS]
  -- the weight of a diagonal term is exactly the threshold
  have hwterm : ∀ j : Fin q,
      monomialTotalWeight (diagonalWeight q) (term j) = q - 1 := by
    intro j
    rw [monomialTotalWeight_diagonalWeight]
    have h1 : (term j Leg.X : ℕ) = (Fin.rev j : ℕ) := rfl
    have h2 : (term j Leg.Y : ℕ) = (j : ℕ) := rfl
    have h3 := val_rev_add_val (q := q) j
    have h4 := j.isLt
    omega
  have hind : IndependentSet
      (MonomialIndependence.minimumWeightPart (diagonalWeight q) (q - 1) T) S := by
    constructor
    · intro p hp
      obtain ⟨j, rfl⟩ := (hmemS p).mp hp
      rw [MonomialIndependence.minimumWeightPart_of_weight (hwterm j)]
      exact hg j
    · intro p hp p' hp' i hpi
      obtain ⟨j, rfl⟩ := (hmemS p).mp hp
      obtain ⟨j', rfl⟩ := (hmemS p').mp hp'
      refine congrArg term ?_
      cases i with
      | X =>
          have : Fin.rev j = Fin.rev j' := hpi
          exact Fin.rev_injective this
      | Y => exact hpi
      | Z =>
          have : g j = g j' := hpi
          exact g.injective this
    · intro p hp hcov
      obtain ⟨hw, hTp⟩ := MonomialIndependence.minimumWeightPart_ne_zero hp
      obtain ⟨e, he, hex⟩ := hcov Leg.X
      obtain ⟨j, rfl⟩ := (hmemS e).mp he
      -- the diagonal equation determines the `y`-index from the `x`-index
      have hx : p Leg.X = Fin.rev j := hex.symm
      have hdiag : (p Leg.X : ℕ) + (p Leg.Y : ℕ) = q - 1 := by
        rw [monomialTotalWeight_diagonalWeight] at hw
        have h1 := (p Leg.X).isLt
        have h2 := (p Leg.Y).isLt
        have h3 := hT.triangular p hTp
        omega
      have hy : p Leg.Y = j := by
        refine Fin.ext ?_
        have h1 : (Fin.rev j : ℕ) + (j : ℕ) = q - 1 := val_rev_add_val j
        have h2 : (p Leg.X : ℕ) = (Fin.rev j : ℕ) := by rw [hx]
        have h3 := j.isLt
        omega
      have := hT.unique_z p (term j) hTp (hg j) (by rw [hx]; rfl) (by rw [hy]; rfl)
      rw [this]
      exact (hmemS (term j)).mpr ⟨j, rfl⟩
  have hcard : S.card = q := by
    rw [hS, Finset.card_image_of_injective _ htermInj, Finset.card_univ, Fintype.card_fin]
  have h := Tensor.card_le_asymptoticIndependenceNumber (A := T) (diagonalWeight q) (q - 1)
    (fun p hp ↦ le_monomialTotalWeight_diagonalWeight hT p hp) hind
  rwa [hcard] at h

end Easy

/-! ## AVW Theorem 7.6 -/

section Main

variable {K : Type u} [CommSemiring K] [NoZeroDivisors K] [Nontrivial K] {q : ℕ}

/-- **AVW Theorem 7.6.**  A lower triangular tensor `T` over `X = {x_0,…,x_{q-1}}`,
`Y = {y_0,…,y_{q-1}}`, `Z = {z_0,…,z_{q-1}}` with `q ≥ 2` has `Ī(T) = q` if and only if it has `q`
diagonal terms, no two of which share a `z`-variable.

Proof sketch.  *If*: `le_asymptoticIndependenceNumber_of_hasIndependentDiagonal` gives `q ≤ Ī(T)`
through the monomial degeneration onto the diagonal, and `Ī(T) ≤ q` always.  *Only if*: if the
criterion fails then
`asymptoticIndependenceNumber_le_diagonalBound_of_not_hasIndependentDiagonal` gives
`Ī(T) ≤ diagonalBound q < q`, contradicting `Ī(T) = q`. -/
theorem avw_theorem_seven_six (hq : 2 ≤ q) {T : (∀ i, LowerTriangularIndex q i) → K}
    (hT : IsLowerTriangular T) :
    asymptoticIndependenceNumber T = (q : ℝ) ↔ HasIndependentDiagonal T := by
  constructor
  · intro heq
    by_contra hbad
    have h := asymptoticIndependenceNumber_le_diagonalBound_of_not_hasIndependentDiagonal hq hT hbad
    rw [heq] at h
    exact absurd h (not_le.mpr (diagonalBound_lt hq))
  · intro hd
    refine le_antisymm (asymptoticIndependenceNumber_le_card_of_isLowerTriangular hT) ?_
    exact le_asymptoticIndependenceNumber_of_hasIndependentDiagonal hT hd

end Main

/-! ## The barrier corollary

AVW's Section 7.4 is a *characterization*, not a barrier theorem, but the failing half feeds the
Galactic barrier chain exactly as AVW Corollary 5.1 does in Theorem 7.5: an explicit gap `g` in
`Ī(T) ≤ q^{1-g}` gives `ω_g^{coord}(T) ≥ 6/(3-g) > 2`.  The chain itself is the gap-parametric
`AlgebraicComplexity.six_div_sub_le_coordinateGalacticExponent_of_le_rpow_card`
(`MatrixMultiplication/CornerBarrier.lean`).

Unlike Theorem 7.5, the criterion alone does not make the table concise or bound its asymptotic
rank, so those two inputs of AVW Corollary 4.3 remain hypotheses; for `T_q^lower` they are
supplied by `isCoordinateConcise_lowerTriangularTable` and
`card_le_asymptoticRank_lowerTriangularTable`. -/

section Barrier

variable {q : ℕ}

/-- **The Galactic barrier for a lower triangular table failing AVW's criterion.**  A concise
lower triangular table on `q ≥ 2` variables per leg with `q ≤ R̃(T)`, without `q` diagonal terms of
pairwise distinct `z`-variables, admits no Galactic exponent below

```text
6 / (3 − diagonalExponent q) > 2,   diagonalExponent q = 1/((q(1 + q·2^q − q²))² log q).
```

Proof sketch: `asymptoticIndependenceNumber_le_diagonalBound_of_not_hasIndependentDiagonal` is the
absolute bound `Ī(T) ≤ q^{1 − diagonalExponent q}` that the gap-parametric barrier chain of
`MatrixMultiplication/CornerBarrier.lean` consumes, with `g = diagonalExponent q ∈ (0, 1]`. -/
theorem six_div_sub_diagonalExponent_le_coordinateGalacticExponent (K : Type u) [Field K]
    (hq : 2 ≤ q) {T : (∀ i, LowerTriangularIndex q i) → K} (hT : IsLowerTriangular T)
    (hbad : ¬ HasIndependentDiagonal T)
    (hconc : ∀ i, Tensor.IsCoordinateConcise T i)
    (hcard : (q : ℝ) ≤ Tensor.asymptoticRank (coordinateTensor T))
    (hne : (coordinateGalacticValues K T).Nonempty) :
    6 / (3 - diagonalExponent q) ≤ coordinateGalacticExponent K T := by
  haveI : ∀ i, Nonempty (LowerTriangularIndex q i) := fun _ ↦ ⟨(⟨0, by omega⟩ : Fin q)⟩
  exact six_div_sub_le_coordinateGalacticExponent_of_le_rpow_card K hq
    (diagonalExponent_le_one hq) hconc hcard
    (asymptoticIndependenceNumber_le_diagonalBound_of_not_hasIndependentDiagonal hq hT hbad) hne

/-- **The Galactic method cannot prove `ω = 2` through a lower triangular table failing AVW's
criterion.**  The constant is the explicit `6/(3 − diagonalExponent q)` above. -/
theorem two_lt_coordinateGalacticExponent_of_not_hasIndependentDiagonal (K : Type u) [Field K]
    (hq : 2 ≤ q) {T : (∀ i, LowerTriangularIndex q i) → K} (hT : IsLowerTriangular T)
    (hbad : ¬ HasIndependentDiagonal T)
    (hconc : ∀ i, Tensor.IsCoordinateConcise T i)
    (hcard : (q : ℝ) ≤ Tensor.asymptoticRank (coordinateTensor T))
    (hne : (coordinateGalacticValues K T).Nonempty) :
    2 < coordinateGalacticExponent K T :=
  lt_of_lt_of_le
    (two_lt_six_div_sub (diagonalExponent_pos hq) (diagonalExponent_le_one hq))
    (six_div_sub_diagonalExponent_le_coordinateGalacticExponent K hq hT hbad hconc hcard hne)

end Barrier

/-! ## Sanity checks and regression clients

`T_q^lower` itself fails the criterion in the strongest possible way — *all* of its diagonal terms
use `z_{q-1}` (`lowerTriangularTable_diagonal_z`) — so Theorem 7.6 reproves
`Ī(T_q^lower) < q`, consistently with AVW Theorem 7.5 (which is sharper: see the module header).
The smallest tables *satisfying* the criterion are the pure-diagonal tables below. -/

section Sanity

variable {K : Type u} [CommSemiring K] {q : ℕ}

/-- **`T_q^lower` fails the criterion of AVW Theorem 7.6** for every `q ≥ 2`: its diagonal terms all
use `z_{q-1}`, so no two of them have distinct `z`-variables. -/
theorem not_hasIndependentDiagonal_lowerTriangularTable [Nontrivial K] (hq : 2 ≤ q) :
    ¬ HasIndependentDiagonal (lowerTriangularTable K q) := by
  rintro ⟨g, hg⟩
  have hval : ∀ j : Fin q, (g j : ℕ) = q - 1 := by
    intro j
    have h := hg j
    rw [lowerTriangularTable_ne_zero_iff] at h
    have h1 : (Fin.rev j : ℕ) + (j : ℕ) = q - 1 := val_rev_add_val j
    simp only [ofLegs_X, ofLegs_Y, ofLegs_Z] at h
    omega
  have hz : g (⟨0, by omega⟩ : Fin q) = g (⟨1, by omega⟩ : Fin q) :=
    Fin.ext ((hval _).trans (hval _).symm)
  have hv := congrArg Fin.val (g.injective hz)
  simp at hv

/-- **The pure-diagonal lower triangular table** `∑_j x_{q-1-j} y_j z_j`: the `q` diagonal terms,
with the `j`th one using the `z`-variable `z_j`.  It is the simplest table satisfying the criterion
of AVW Theorem 7.6, and hence has `Ī = q`. -/
def independentDiagonalTable (K : Type u) [CommSemiring K] (q : ℕ) :
    (∀ i, LowerTriangularIndex q i) → K :=
  fun p ↦ if (p .X : ℕ) + (p .Y : ℕ) = q - 1 ∧ (p .Z : ℕ) = (p .Y : ℕ) then 1 else 0

/-- The support of the pure-diagonal table is `{(rev j, j, j)}`. -/
theorem independentDiagonalTable_ne_zero_iff [Nontrivial K] (p : ∀ i, LowerTriangularIndex q i) :
    independentDiagonalTable K q p ≠ 0 ↔
      ((p .X : ℕ) + (p .Y : ℕ) = q - 1 ∧ (p .Z : ℕ) = (p .Y : ℕ)) := by
  rw [independentDiagonalTable]
  by_cases h : (p .X : ℕ) + (p .Y : ℕ) = q - 1 ∧ (p .Z : ℕ) = (p .Y : ℕ) <;> simp [h]

/-- **The pure-diagonal table is lower triangular** for every `q ≥ 1`: its `z`-index is determined
by its `y`-index, and `i + j = q - 1 < q`. -/
theorem isLowerTriangular_independentDiagonalTable [Nontrivial K] (hq : 1 ≤ q) :
    IsLowerTriangular (independentDiagonalTable K q) := by
  constructor
  · intro p p' hp hp' hX hY
    rw [independentDiagonalTable_ne_zero_iff] at hp hp'
    funext i
    cases i with
    | X => exact hX
    | Y => exact hY
    | Z => exact Fin.ext (by rw [hp.2, hp'.2, hY])
  · intro p hp
    rw [independentDiagonalTable_ne_zero_iff] at hp
    omega

/-- **The pure-diagonal table satisfies the criterion of AVW Theorem 7.6**, with the identity as
the `z`-assignment. -/
theorem hasIndependentDiagonal_independentDiagonalTable [Nontrivial K] :
    HasIndependentDiagonal (independentDiagonalTable K q) := by
  refine ⟨Equiv.refl (Fin q), fun j ↦ ?_⟩
  rw [independentDiagonalTable_ne_zero_iff]
  exact ⟨by simpa using val_rev_add_val j, rfl⟩

variable [NoZeroDivisors K] [Nontrivial K]

/-- **Regression client for AVW Theorem 7.6**: the pure-diagonal table attains the trivial bound,
`Ī(∑_j x_{q-1-j} y_j z_j) = q` for every `q ≥ 2`. -/
theorem asymptoticIndependenceNumber_independentDiagonalTable (hq : 2 ≤ q) :
    asymptoticIndependenceNumber (independentDiagonalTable K q) = (q : ℝ) :=
  (avw_theorem_seven_six hq (isLowerTriangular_independentDiagonalTable (by omega))).mpr
    hasIndependentDiagonal_independentDiagonalTable

end Sanity

/-! ## Tiny clients at `q = 2` and `q = 3` -/

section Tiny

/-- **`q = 2`**: `Ī(x_1y_0z_0 + x_0y_1z_1) = 2`. -/
theorem asymptoticIndependenceNumber_independentDiagonalTable_two :
    asymptoticIndependenceNumber (independentDiagonalTable ℚ 2) = 2 := by
  have h := asymptoticIndependenceNumber_independentDiagonalTable (K := ℚ) (q := 2) le_rfl
  norm_num at h
  exact h

/-- **`q = 3`**: `Ī(x_2y_0z_0 + x_1y_1z_1 + x_0y_2z_2) = 3`. -/
theorem asymptoticIndependenceNumber_independentDiagonalTable_three :
    asymptoticIndependenceNumber (independentDiagonalTable ℚ 3) = 3 := by
  have h := asymptoticIndependenceNumber_independentDiagonalTable (K := ℚ) (q := 3) (by norm_num)
  norm_num at h
  exact h

/-- **`q = 2`, the failing case**: `T_2^lower` does not satisfy the criterion of AVW Theorem 7.6,
consistently with `asymptoticIndependenceNumber_lowerTriangularTable_two_lt`. -/
theorem not_hasIndependentDiagonal_lowerTriangularTable_two :
    ¬ HasIndependentDiagonal (lowerTriangularTable ℚ 2) :=
  not_hasIndependentDiagonal_lowerTriangularTable le_rfl

/-- **`q = 2`, the quantitative bound**: `Ī(T_2^lower) ≤ diagonalBound 2 < 2`.  This is AVW
Theorem 7.6 applied to `T_2^lower`; the corner bound of `Examples/LowerTriangularBarrier.lean`
gives a much sharper constant for this particular table. -/
theorem asymptoticIndependenceNumber_lowerTriangularTable_two_le_diagonalBound :
    asymptoticIndependenceNumber (lowerTriangularTable ℚ 2) ≤ diagonalBound 2 :=
  asymptoticIndependenceNumber_le_diagonalBound_of_not_hasIndependentDiagonal le_rfl
    (isLowerTriangular_lowerTriangularTable 2) not_hasIndependentDiagonal_lowerTriangularTable_two

end Tiny

end AlgebraicComplexity.Examples
