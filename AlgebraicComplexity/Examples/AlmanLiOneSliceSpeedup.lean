/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.DirectSum
import AlgebraicComplexity.MatrixMultiplication.NonminimalBorderRankSpeedup
import AlgebraicComplexity.MatrixMultiplication.NonminimalRankSpeedup
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Alman–Li §§5–7: the one-slice speedup layer, and what is still open

`Tensor/FreeLunchSpeedup.lean` proves the *free-lunch speedup theorem*
([AlmanLi2026], Theorem 5.1, p. 14) and its degeneration bootstrap (Corollary 5.1, p. 15).
Everything else in Sections 5–7 of that paper is built on top of it.  This file states the
remaining results as `Prop` definitions with the exact hypothesis shape, so that downstream
interfaces can be designed against them, and discharges the ones that are proved: a statement
`P K` below is **proved** exactly when a theorem `… : P K` follows it, and is otherwise a named
proof obligation.  None of them is an `axiom`, an unproved declaration, or an instance.

## Inventory of the constructive layer

| Result | Page | Content | Status |
| --- | --- | --- | --- |
| Theorem 5.1 | 14 | Free-lunch speedup, restriction form | **Proved**, `Tensor/FreeLunchSpeedup.lean` |
| Corollary 5.1 | 15 | Free-lunch speedup, degeneration form | **Proved**, same file, without a second parameter |
| Prop. 5.1, 5.2 | 16 | Isolated summands, stability under `⊗` | Bookkeeping for Theorem 6.2 only; not recorded |
| Prop. 5.3 | 17 | The extracted summand is `⟨1,t,1⟩` with `t ≥ r − n − m` | **Proved**, `MatrixMultiplication/OneSliceSpeedup.lean` |
| Prop. 5.4 | 17 | One-slice speedup, `[Str88, Lemma 3.12]` | **Proved**, `MatrixMultiplication/OneSliceAppend.lean` |
| Prop. 5.5, 5.6 | 18 | Fullness index and its multiplicativity | Bookkeeping for Theorem 6.2 only; not recorded |
| Prop. 5.7 | 18 | One-slice compression, `[Str88, Prop. 6.4]` | `OneSliceCompression` |
| Theorem 6.1 | 19 | One-slice speedup for nonminimal rank | **Proved**, `MatrixMultiplication/NonminimalRankSpeedup.lean` |
| Theorem 6.1 | 19 | …for nonminimal *border* rank | **Proved**, `nonminimalBorderRankSpeedup` below, from `MatrixMultiplication/NonminimalBorderRankSpeedup.lean` |
| Theorem 6.2 | 20 | Iterated version | Out of scope (needs Prop. 5.1/5.2/5.5/5.6) |
| Theorem 6.3 | 21 | Grouped (multi-slice) speedup | `GroupedOneSliceSpeedup` |
| Theorem 7.3 | 29 | Direct-sum identity generalizing `[Sch81, Lemma 6.1]` | `DirectSumIdentity` |

The numerical headlines of Sections 6 and 7 (`R̃(cw₂) < 3.931`, `σ(d) < 2ω/3`, Corollary 6.1) all
pass through Proposition 4.5 and Strassen duality, which `Examples/AlmanLiSpeedup.lean` records as
research-scale and out of scope.  The results above are the *constructive* layer beneath them:
each is an explicit degeneration or restriction with no spectral argument.

## Infrastructure verdict: no function-field layer is needed

A `Tensor/FunctionFieldDegeneration.lean` was proposed for the two-parameter argument of
[AlmanLi2026, Corollary 5.1].  It is not needed.  The paper introduces a second parameter `ε`
only because it treats a degeneration `T ⊴ S` as an opaque restriction of `F(λ)`-tensors and then
has to substitute `ε = λ^k` for an unquantified large `k`.  In this library the `λ`-orders are
explicit data (`HasLeadingTerm … d …`), so the required exponents can simply be *computed*:
`polynomialDegeneratesAt_add_of_mixed_eq_zero` shifts the two block families by
`(0, 0, d + d' + 2)` and `(d + 1, d + 1, 0)` and lands at leading degree `2d + d' + 2` with every
junk block strictly above.  Consequently the whole in-scope layer is provable inside the existing
single-parameter `PolynomialDegenerates` calculus.

## The two-legged rank interface, and the two routes to Theorem 6.1

Propositions 5.3 and 5.4 quantify over the **rank of a contracted slice**: for a functional
`f : W → K` on the third leg, `M = (id ⊗ id ⊗ f) S` is an element of `U ⊗ V` and the statements
constrain `rank M`.  That interface now exists and introduces **no new tensor space**:
`Tensor/MatrixFlattening.lean` reads the contraction as a linear map
`matrixFlatten f S : (V .Y)ᵛ →ₗ[K] V .X` and defines `matrixRank f S` as the `finrank` of its
range, so a "two-legged tensor" is just a `Tensor3` together with a functional on its `Z` leg.
Its structure theorem `map_ofLegs_eq_sum_pure_of_flatten` supplies both directions of the
`⟨1,t,1⟩` identification (`MatrixMultiplication/OneSliceNormalForm.lean`) and the rank-drop bound
`matrixRank_le_add_of_map` used by Proposition 5.3.

* **Proposition 5.3** (p. 17) is `polynomialDegenerates_directSum_oneSlice` in
  `MatrixMultiplication/OneSliceSpeedup.lean`, stated composed with Theorem 5.1: with the
  *maximal* choices `A' = {u : (u ⊗ B ⊗ f)S = 0}` and `B' = {v : (A ⊗ v ⊗ f)S = 0}`,
  `S ⊵ T ⊕ ⟨1, r − n − m, 1⟩` for `r = matrixRank f S`, `n = dim U'`, `m = dim V'`.  The
  hypothesis `C' ⊆ Cᗮ` is taken in its flattened form `A ∘ φ ∘ Bᵛ = 0`; the bridge from the
  tensor form `(A ⊗ B ⊗ f)S = 0` is `Tensor.flatten_comp_eq_zero_of_map_eq_zero`.  The paper's
  conclusion "`T' ≅ ⟨1,t,1⟩`" is stated here as the (correct, and the only usable) restriction
  `T' ⤳ ⟨1,t,1⟩`: `T'` is a rank-`t'` matrix on legs of dimension `dim A'`, `dim B'`, so it is
  isomorphic to `⟨1,t',1⟩` only after discarding the kernels.
* **Proposition 5.4** (p. 17) is `exists_oneSliceAppend` in
  `MatrixMultiplication/OneSliceAppend.lean`.  Let `T ≤ S` by `(A,B,C)`, let `ζ : W → K`, put
  `q = matrixRank ζ S` and let `s` bound the rank of `M = A ∘ (matrixFlatten ζ S) ∘ Bᵛ`.  Then
  `A`, `B`, `C` extend to a restriction `T ≤ S ⊕ ⟨1,s,1⟩` and there is a `Z`-leg functional `ζ'`
  in the corresponding kernel with `matrixRank ζ' (S ⊕ ⟨1,s,1⟩) = q + s`.  Two remarks on the
  formalization:
  * the paper fixes `s = rank M`, but the version proved here allows any `s ≥ rank M`, which is
    what Theorem 6.1 consumes.  The padding **cannot** be done afterwards: a larger `s` enlarges
    the extracted summand as well, so `⟨1,s,1⟩` must enter the factorization at the padded size;
  * the non-formal ingredient `M = (A₁ ⊗ B₁)⟨1,s,1⟩` is *not*
    `restricts_matrixMultiplication_matrixRank`.  That theorem's size parameter is the ambient
    `matrixRank ζ S = q`, not `rank M`, and its target family would need a `Z` component equal to
    `K`.  The usable form is the flattened `exists_oneSlice_factorization`, proved from a basis of
    the range of `M` and reflexivity of the finite-dimensional `Y` leg.  The remaining
    bookkeeping is `Tensor.matrixRank_directSum` (`Tensor/MatrixFlatteningDirectSum.lean`).

**Theorem 6.1** (p. 19) is proved in both forms, by two different routes.

* The **restriction form** is `polynomialDegenerates_diagonalTensor_directSum_oneSlice` in
  `MatrixMultiplication/NonminimalRankSpeedup.lean`: from a restriction `T ≤ ⟨r⟩` of an
  `n × n × n` tensor and any `s ≥ rank M`, `⟨r⟩ ⊕ ⟨1,s,1⟩ ⊵ T ⊕ ⟨1, r + s − 2n, 1⟩`; the
  companion `polynomialDegenerates_diagonalTensor_oneSlice_of_rankLE` is the `s = n` clause from
  a bare `RankLE r T`.  The `s = n` clause is unconditional, as claimed: `M = Σ aᵢbᵢc'ᵢ` lives in
  `U' ⊗ V'` with `dim U' = dim V' = n`, so `Submodule.finrank_le` bounds its rank by `n`.
  Fixing the all-ones contraction loses no generality: rescaling `aᵢ ↦ c'ᵢaᵢ`, `cᵢ ↦ c'ᵢ⁻¹cᵢ`
  turns any nonzero `(c'ᵢ)` into it while preserving both `T` and `M`.  This route follows the
  paper through Propositions 5.3 and 5.4, which are dimension counts over the base field.
* The **border-rank form** — the one the paper states, and the one that says a nonminimal
  *border*-rank bound is never tight — is
  `polynomialDegenerates_diagonalTensor_oneSlice_of_borderRankLE` in
  `MatrixMultiplication/NonminimalBorderRankSpeedup.lean`, and discharges
  `NonminimalBorderRankSpeedup` below.  It does **not** run Propositions 5.3 and 5.4 over
  `F(λ)`, and needs no scalar extension of the tensor layer to `RatFunc K`.  Instead
  `Tensor/OneSliceBorderSpeedup.lean` applies the polynomial free-lunch theorem to two explicit
  polynomial families of leg maps on `⟨r⟩ ⊕ ⟨1,n,1⟩`; the dimension count survives as a
  *kernel frame* of the polynomial coordinate matrix of the certificate
  (`Tensor/PolynomialKernelFrame.lean`), which is found over the fraction field of `K[X]` and
  returned, denominators cleared, as a statement about polynomials.  The `s = n` clause needs no
  rank hypothesis in this form either: an `n × n` polynomial matrix factors through its `n`
  columns.

Theorem 6.3 follows either by summing Theorem 6.1 over a partition of `[r]` (the paper's first
proof, p. 21) or through `OneSliceCompression` (its second proof, p. 21–22).

## References

* J. Alman and B. Li, *Asymptotic rank speedup theorems, revisited*, arXiv:2605.21738
  ([AlmanLi2026]), Sections 5–7.
* V. Strassen, *The asymptotic spectrum of tensors*, J. reine angew. Math. 384 (1988)
  ([Strassen1988]), Lemma 3.12 and Proposition 6.4.
* A. Schönhage, *Partial and total matrix multiplication*, SIAM J. Comput. 10 (1981)
  ([Schonhage1981]), Lemma 6.1.
-/

namespace AlgebraicComplexity.AlmanLi

open Tensor

universe u

/-- The unit (diagonal) tensor `⟨r⟩`, presented as the direct sum of `r` copies of `⟨1,1,1⟩`. -/
noncomputable abbrev unitTensor (K : Type u) [CommSemiring K] (r : ℕ) :
    Tensor3 K (MMDirectSumSpace K (ι := Fin r) (fun _ ↦ 1) (fun _ ↦ 1) (fun _ ↦ 1)) :=
  matrixMultiplicationDirectSum K (ι := Fin r) (fun _ ↦ 1) (fun _ ↦ 1) (fun _ ↦ 1)

/-- A direct sum `⊕_{i} ⟨1, n i, 1⟩` of one-slice matrix-multiplication tensors. -/
noncomputable abbrev oneSliceDirectSum (K : Type u) [CommSemiring K]
    {ι : Type*} [Fintype ι] (n : ι → ℕ) :
    Tensor3 K (MMDirectSumSpace K (fun _ : ι ↦ 1) n (fun _ ↦ 1)) :=
  matrixMultiplicationDirectSum K (fun _ : ι ↦ 1) n (fun _ ↦ 1)

/-- **Obligation: one-slice compression** ([AlmanLi2026], Proposition 5.7, p. 18; Strassen
[Strassen1988], Proposition 6.4).

Let `T = ⊕_{i<k} ⟨1, n i, 1⟩` and let `A` act on the `X` leg alone, with image of codimension `p`.
Then `(A ⊗ id ⊗ id) T` still restricts onto a direct sum of one-slice tensors, and the total loss
is exactly `p`, distributed as `q i ≤ n i` with `∑ q i = p`.

The intended proof is the paper's: choose a subset `D` of the `X`-basis of `T` of size
`dim U − p` on which `A` is injective, zero out every basis vector outside `D` on the `X` and `Y`
legs, and compose with a left inverse of `A|_{span D}`. -/
def OneSliceCompression (K : Type u) [Field K] : Prop :=
  ∀ (k p : ℕ) (n : Fin k → ℕ)
    (A : MMDirectSumSpace K (fun _ : Fin k ↦ 1) n (fun _ ↦ 1) .X →ₗ[K]
      MMDirectSumSpace K (fun _ : Fin k ↦ 1) n (fun _ ↦ 1) .X),
    Module.finrank K (LinearMap.range A) + p = ∑ i, n i →
    ∃ q : Fin k → ℕ, (∀ i, q i ≤ n i) ∧ (∑ i, q i = p) ∧
      Restricts
        (Tensor.map (ofLegs (V := fun c ↦
            MMDirectSumSpace K (fun _ : Fin k ↦ 1) n (fun _ ↦ 1) c →ₗ[K]
              MMDirectSumSpace K (fun _ : Fin k ↦ 1) n (fun _ ↦ 1) c)
            A LinearMap.id LinearMap.id)
          (oneSliceDirectSum K n))
        (oneSliceDirectSum K fun i ↦ n i - q i)

/-- **Statement: one-slice speedup for nonminimal border rank** ([AlmanLi2026], Theorem 6.1,
p. 19, the displayed `s = n` specialization).  Proved: `nonminimalBorderRankSpeedup`.

If `T` is an `n × n × n` tensor with a border-rank-`r` certificate, then

```text
T ⊕ ⟨1, r − n, 1⟩ ⊴ ⟨r⟩ ⊕ ⟨1, n, 1⟩.
```

This is the statement of `polynomialDegenerates_diagonalTensor_oneSlice_of_rankLE`
(`MatrixMultiplication/NonminimalRankSpeedup.lean`) with `RankLE` weakened to `BorderRankLE`.

The hypothesis `n ≤ r` of the earlier draft is unnecessary — natural-number subtraction truncates
the conclusion correctly — and finite-dimensionality of the legs is now demanded explicitly, since
`finrank = n` alone does not imply it when `n = 0`. -/
def NonminimalBorderRankSpeedup (K : Type u) [Field K] : Prop :=
  ∀ (n r : ℕ) (V : Leg → Type u),
    ∀ [∀ c, AddCommGroup (V c)] [∀ c, Module K (V c)]
      [FiniteDimensional K (V .X)] [FiniteDimensional K (V .Y)] (T : Tensor3 K V),
      Module.finrank K (V .X) = n → Module.finrank K (V .Y) = n → BorderRankLE r T →
      PolynomialDegenerates
        (Tensor.directSum (diagonalTensor K (Fin r)) (matrixMultiplication (K := K) 1 n 1))
        (Tensor.directSum T (matrixMultiplication (K := K) 1 (r - n) 1))

/-- **Alman–Li Theorem 6.1, border-rank form** ([AlmanLi2026], p. 19): a tensor with `n`-dimensional
`X` and `Y` legs and border rank at most `r` satisfies `⟨r⟩ ⊕ ⟨1,n,1⟩ ⊵ T ⊕ ⟨1, r − n, 1⟩`. -/
theorem nonminimalBorderRankSpeedup (K : Type u) [Field K] : NonminimalBorderRankSpeedup K := by
  intro n r V _ _ _ _ T hX hY hT
  exact polynomialDegenerates_diagonalTensor_oneSlice_of_borderRankLE n n r T hX hY hT

/-- **Obligation: grouped one-slice speedup** ([AlmanLi2026], Theorem 6.3, p. 21, in the
quantitative form displayed on p. 22).

Partitioning a border-rank-`r` certificate of an `n × n × n` tensor into `p` groups of size at
least `3n` and applying Theorem 6.1 groupwise gives

```text
T ⊕ (p ⊙ ⟨1, 2n, 1⟩) ⊴ ⟨r⟩ ⊕ (p ⊙ ⟨1, n, 1⟩),
```

which is the source of the `r − Ω(r / n^{1/3})` asymptotic-rank bound.  The fully parametrized
statement with group sizes `rα` and slice sizes `sα ≥ R(Mα)` again needs a two-legged rank
interface. -/
def GroupedOneSliceSpeedup (K : Type u) [Field K] : Prop :=
  ∀ (n r p : ℕ) (V : Leg → Type u),
    ∀ [∀ c, AddCommGroup (V c)] [∀ c, Module K (V c)] (T : Tensor3 K V),
      (∀ c, Module.finrank K (V c) = n) → BorderRankLE r T → 3 * n * p ≤ r →
      PolynomialDegenerates
        (Tensor.directSum (unitTensor K r)
          (oneSliceDirectSum K (fun _ : Fin p ↦ n)))
        (Tensor.directSum T (oneSliceDirectSum K (fun _ : Fin p ↦ 2 * n)))

/-- **Obligation: the Alman–Li direct-sum identity** ([AlmanLi2026], Theorem 7.3, p. 29).

For positive integers `nα` (`α < p`) and `mβ` (`β < q`) with `n = ∑ nα` and `m = ∑ mβ`,

```text
⟨n,1,m⟩ ⊕ ⊕_{α,β} ⟨1, (nα − 1)(mβ − 1), 1⟩  ⊴  ⟨nm⟩ ⊕ ⟨p,1,q⟩.
```

At `p = q = 1` this is Schönhage's identity `⟨n,1,m⟩ ⊕ ⟨1,(n−1)(m−1),1⟩ ⊴ ⟨nm+1⟩`
([Schonhage1981], Lemma 6.1).

The intended proof is a direct application of the *restriction* form of the free-lunch theorem
(`Tensor.polynomialDegeneratesAt_two_directSum_of_mixed_map_eq_zero`) to the redundant restriction
`⟨n,1,m⟩ ≤ ⟨nm⟩ ⊕ ⟨p,1,q⟩` given by `A : u_{ij} ↦ x_i, u'_α ↦ ∑_{i ∈ Iα} x_i`,
`B : v_{ij} ↦ y_j, v'_β ↦ ∑_{j ∈ Jβ} y_j`, `C : w_{ij} ↦ z_{ij}, w'_{αβ} ↦ 0`, together with the
explicit second family `g` obtained from the paper's `C' : w_{ij} ↦ w'_{α(i)β(j)}` and the
projections `π_U`, `π_V` that delete one distinguished row and column from each block.  No
degeneration parameter beyond the one supplied by Theorem 5.1 is required. -/
def DirectSumIdentity (K : Type u) [Field K] : Prop :=
  ∀ (p q : ℕ) (n : Fin p → ℕ) (m : Fin q → ℕ),
    (∀ a, 0 < n a) → (∀ b, 0 < m b) →
    PolynomialDegenerates
      (Tensor.directSum (unitTensor K ((∑ a, n a) * ∑ b, m b))
        (matrixMultiplication (K := K) p 1 q))
      (Tensor.directSum (matrixMultiplication (K := K) (∑ a, n a) 1 (∑ b, m b))
        (oneSliceDirectSum K (ι := Fin p × Fin q)
          fun ab ↦ (n ab.1 - 1) * (m ab.2 - 1)))

end AlgebraicComplexity.AlmanLi
