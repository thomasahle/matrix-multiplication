/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.OneSliceSpeedup
import AlgebraicComplexity.Tensor.MatrixFlatteningDirectSum

/-!
# Appending a one-slice tensor to both sides of a restriction

This file proves [AlmanLi2026, Proposition 5.4, p. 17] (Strassen [Strassen1988], Lemma 3.12): a
restriction `T ≤ S` can always be extended, for free, to a restriction `T ≤ S ⊕ ⟨1,s,1⟩` on which
some `Z`-leg functional satisfies the hypothesis of Proposition 5.3 with the *larger* contracted
rank `q + s`.  Composed with `polynomialDegenerates_directSum_oneSlice`
(`MatrixMultiplication/OneSliceSpeedup.lean`) this is the constructive core of
[AlmanLi2026, Theorem 6.1, p. 19].

## The construction

Let `f = (A,B,C)` restrict `S` to `T`, let `ζ` be a functional on the `Z` leg of `S`, and write

```text
φ = matrixFlatten ζ S,   M = A ∘ φ ∘ Bᵛ,   q = matrixRank ζ S,
```

so that `M` is the paper's matrix `(A ⊗ B ⊗ f) S ∈ U' ⊗ V'`.  For any `s ≥ rank M` the matrix
factors as `M = (A₁ ⊗ B₁) ⟨1,s,1⟩` (`exists_oneSlice_factorization`), and the extended family

```text
F = (A A₁ ⊕ 0 (−A₁), B B₁, C 0),      ζ' = (ζ, 1)
```

on `S ⊕ ⟨1,s,1⟩` reproduces `T`, kills the flattened block condition, and has contracted rank
exactly `q + s`.  The paper puts the sign on the functional (`f' = (f, −1)`); putting it on the
`X`-leg map instead is the same construction and avoids negating a functional.

## Deviations from the paper

* The paper fixes `s = rank M` exactly.  The version proved here takes any `s ≥ rank M`, which is
  what [AlmanLi2026, Theorem 6.1] actually consumes ("has rank at most `s`").  The padding cannot
  be performed afterwards on the tensors: enlarging `s` enlarges the *extracted* summand
  `⟨1, q + s − 2n, 1⟩` as well, so `⟨1,s,1⟩` must enter the factorization at the padded size.
* The paper's `M = (A₁ ⊗ B₁)⟨1,s,1⟩` is stated here in flattened form,
  `A₁ ∘ (matrixFlatten ζ₁ ⟨1,s,1⟩) ∘ B₁ᵛ = M`.  The tensor-level
  `restricts_matrixMultiplication_matrixRank` cannot serve directly: its size parameter is the
  ambient `matrixRank ζ S`, not `rank M`, and its target would have to be a `Leg`-indexed family
  whose `Z` component is `K`, the family shape `Tensor/MatrixFlattening.lean` deliberately
  rejects.

## Main results

* `matrixFlatten_matrixMultiplication_one`, `matrixRank_matrixMultiplication_one`: the contracted
  slice of `⟨1,s,1⟩` at its unique `Z` coordinate, and its rank `s`.
* `exists_oneSlice_factorization`: a matrix of rank at most `s` factors through `⟨1,s,1⟩`.
* `exists_oneSliceAppend`: **Proposition 5.4**.
* `polynomialDegenerates_directSum_oneSliceAppend`: Proposition 5.4 composed with
  Proposition 5.3, i.e. `S ⊕ ⟨1,s,1⟩ ⊵ T ⊕ ⟨1, q + s − n − m, 1⟩`.

## References

* J. Alman and B. Li, *Asymptotic rank speedup theorems, revisited*, arXiv:2605.21738
  ([AlmanLi2026]), Proposition 5.4, p. 17.
* V. Strassen, *The asymptotic spectrum of tensors*, J. reine angew. Math. 384 (1988)
  ([Strassen1988]), Lemma 3.12.
-/

namespace AlgebraicComplexity

open Tensor Module

universe u v w

section OneSlice

variable {K : Type u} [CommSemiring K]

/-- The unique `Z`-leg coordinate functional of a one-slice matrix-multiplication tensor. -/
def oneSliceZ (K : Type u) [CommSemiring K] (s : ℕ) : MMSpace K 1 s 1 .Z →ₗ[K] K :=
  LinearMap.proj ((0 : Fin 1), (0 : Fin 1))

/-- **The contracted slice of `⟨1,s,1⟩`**: contracting the unique `Z` coordinate turns the
one-slice matrix-multiplication tensor into the `s × s` identity matrix, read as the map sending
the `j`-th `Y`-coordinate functional to the `j`-th `X`-basis vector. -/
theorem matrixFlatten_matrixMultiplication_one (s : ℕ) (β : Dual K (MMSpace K 1 s 1 .Y)) :
    matrixFlatten (oneSliceZ K s) (matrixMultiplication (K := K) 1 s 1) β =
      ∑ j : Fin s, β (Pi.single (j, 0) 1) • (Pi.single (0, j) 1 : MMSpace K 1 s 1 .X) := by
  classical
  rw [matrixMultiplication_one_eq_sum, matrixFlatten_finset_sum, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [matrixFlatten_pure]
  simp [oneSliceZ]

end OneSlice

section Field

variable {K : Type u} [Field K]

/-- The contracted slice of `⟨1,s,1⟩` has rank `s`. -/
theorem matrixRank_matrixMultiplication_one (s : ℕ) :
    matrixRank (oneSliceZ K s) (matrixMultiplication (K := K) 1 s 1) = s := by
  classical
  have hsurj : LinearMap.range (matrixFlatten (oneSliceZ K s)
      (matrixMultiplication (K := K) 1 s 1)) = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro v
    refine ⟨∑ j : Fin s, v ((0 : Fin 1), j) •
      LinearMap.proj (R := K) (φ := fun _ : Fin s × Fin 1 ↦ K) (j, (0 : Fin 1)), ?_⟩
    rw [matrixFlatten_matrixMultiplication_one]
    funext p
    obtain ⟨p₁, p₂⟩ := p
    have hp₁ : p₁ = 0 := Subsingleton.elim _ _
    subst hp₁
    simp [Pi.single_apply, Prod.ext_iff, eq_comm]
  rw [matrixRank, hsurj, finrank_top]
  simp

/-- Summing a `Fin s`-family whose entries vanish outside an initial segment of length `r`. -/
private theorem sum_fin_dite_of_le {M : Type*} [AddCommMonoid M] {r s : ℕ} (hrs : r ≤ s)
    (g : Fin r → M) :
    ∑ j : Fin s, (if hj : (j : ℕ) < r then g ⟨j, hj⟩ else 0) = ∑ k : Fin r, g k := by
  classical
  have key : ∀ n : ℕ, ∑ j : Fin n, (if hj : (j : ℕ) < r then g ⟨j, hj⟩ else 0)
      = ∑ j ∈ Finset.range n, (if hj : j < r then g ⟨j, hj⟩ else 0) := fun n ↦
    Fin.sum_univ_eq_sum_range (fun j ↦ if hj : j < r then g ⟨j, hj⟩ else 0) n
  have hsub : ∑ j ∈ Finset.range r, (if hj : j < r then g ⟨j, hj⟩ else 0)
      = ∑ j ∈ Finset.range s, (if hj : j < r then g ⟨j, hj⟩ else 0) := by
    refine Finset.sum_subset
      (Finset.range_subset.2 fun x hx ↦ Finset.mem_range.2 (hx.trans_le hrs))
      fun x _ hx ↦ ?_
    rw [dif_neg (by simpa [Finset.mem_range] using hx)]
  rw [key s, ← hsub, ← key r]
  exact Finset.sum_congr rfl fun k _ ↦ by rw [dif_pos k.isLt]

/-- A linear map out of a dual space whose range has dimension at most `s` is an explicit sum of
`s` rank-one maps `β ↦ β (y j) • u j`. -/
private theorem exists_fin_factorization {X Y : Type*} [AddCommGroup X] [Module K X]
    [AddCommGroup Y] [Module K Y] [FiniteDimensional K Y]
    (M : Dual K Y →ₗ[K] X) (s : ℕ) (hs : finrank K (LinearMap.range M) ≤ s) :
    ∃ (u : Fin s → X) (y : Fin s → Y), ∀ β, M β = ∑ j, β (y j) • u j := by
  classical
  set r := finrank K (LinearMap.range M) with hr
  haveI : Module.Free K (LinearMap.range M) := Module.Free.of_divisionRing K _
  set ub : Basis (Fin r) K (LinearMap.range M) := Module.finBasis K _ with hub
  set y' : Fin r → Y := fun k ↦
    (Module.evalEquiv K Y).symm (ub.coord k ∘ₗ M.rangeRestrict) with hy'
  refine ⟨fun j ↦ if hj : (j : ℕ) < r then ((ub ⟨j, hj⟩ : LinearMap.range M) : X) else 0,
    fun j ↦ if hj : (j : ℕ) < r then y' ⟨j, hj⟩ else 0, ?_⟩
  intro β
  have hb : ∀ k, β (y' k) = ub.repr (M.rangeRestrict β) k := by
    intro k
    rw [hy']
    simp [Module.apply_evalEquiv_symm_apply, Basis.coord_apply]
  have hterm : ∀ j : Fin s,
      β (if hj : (j : ℕ) < r then y' ⟨j, hj⟩ else 0) •
          (if hj : (j : ℕ) < r then ((ub ⟨j, hj⟩ : LinearMap.range M) : X) else 0)
        = if hj : (j : ℕ) < r then
            β (y' ⟨j, hj⟩) • ((ub ⟨j, hj⟩ : LinearMap.range M) : X) else 0 := by
    intro j
    by_cases hj : (j : ℕ) < r
    · rw [dif_pos hj, dif_pos hj, dif_pos hj]
    · rw [dif_neg hj, dif_neg hj, dif_neg hj, smul_zero]
  rw [Finset.sum_congr rfl fun j (_ : j ∈ Finset.univ) ↦ hterm j,
    sum_fin_dite_of_le hs (fun k ↦ β (y' k) • ((ub k : LinearMap.range M) : X))]
  calc M β = ((M.rangeRestrict β : LinearMap.range M) : X) := rfl
    _ = ((∑ k, ub.repr (M.rangeRestrict β) k • ub k : LinearMap.range M) : X) := by
        rw [ub.sum_repr]
    _ = ∑ k, ub.repr (M.rangeRestrict β) k • ((ub k : LinearMap.range M) : X) := by
        rw [Submodule.coe_sum]
        exact Finset.sum_congr rfl fun k _ ↦ rfl
    _ = ∑ k, β (y' k) • ((ub k : LinearMap.range M) : X) :=
        Finset.sum_congr rfl fun k _ ↦ by rw [hb k]

/-- **A matrix of rank at most `s` factors through `⟨1,s,1⟩`**
([AlmanLi2026], Proposition 5.4, p. 17: "there exist linear maps `A₁`, `B₁` such that
`M = (A₁ ⊗ B₁)⟨1,s,1⟩`").

The statement is the flattened form of the paper's factorization: `M` is a linear map from the
dual of the `Y` space to the `X` space, and `matrixFlatten (oneSliceZ K s) ⟨1,s,1⟩` is the
contracted slice of the one-slice tensor. -/
theorem exists_oneSlice_factorization {X Y : Type*} [AddCommGroup X] [Module K X]
    [AddCommGroup Y] [Module K Y] [FiniteDimensional K Y]
    (M : Dual K Y →ₗ[K] X) (s : ℕ) (hs : finrank K (LinearMap.range M) ≤ s) :
    ∃ (A₁ : MMSpace K 1 s 1 .X →ₗ[K] X) (B₁ : MMSpace K 1 s 1 .Y →ₗ[K] Y),
      A₁ ∘ₗ matrixFlatten (oneSliceZ K s) (matrixMultiplication (K := K) 1 s 1) ∘ₗ
        B₁.dualMap = M := by
  classical
  obtain ⟨u, y, huy⟩ := exists_fin_factorization M s hs
  refine ⟨∑ j : Fin s, LinearMap.smulRight
      (LinearMap.proj (R := K) (φ := fun _ : Fin 1 × Fin s ↦ K) ((0 : Fin 1), j)) (u j),
    ∑ j : Fin s, LinearMap.smulRight
      (LinearMap.proj (R := K) (φ := fun _ : Fin s × Fin 1 ↦ K) (j, (0 : Fin 1))) (y j), ?_⟩
  have hA : ∀ j : Fin s, (∑ j' : Fin s, LinearMap.smulRight
      (LinearMap.proj (R := K) (φ := fun _ : Fin 1 × Fin s ↦ K) ((0 : Fin 1), j')) (u j'))
      (Pi.single ((0 : Fin 1), j) 1) = u j := by
    intro j
    simp [Pi.single_apply, Prod.ext_iff, eq_comm]
  have hB : ∀ j : Fin s, (∑ j' : Fin s, LinearMap.smulRight
      (LinearMap.proj (R := K) (φ := fun _ : Fin s × Fin 1 ↦ K) (j', (0 : Fin 1))) (y j'))
      (Pi.single (j, (0 : Fin 1)) 1) = y j := by
    intro j
    simp [Pi.single_apply, Prod.ext_iff, eq_comm]
  ext β
  rw [LinearMap.comp_apply, LinearMap.comp_apply, matrixFlatten_matrixMultiplication_one,
    map_sum, huy β]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [map_smul, hA j, LinearMap.dualMap_apply, hB j]

variable {V : Leg → Type v} [∀ c, AddCommGroup (V c)] [∀ c, Module K (V c)]
variable {W : Leg → Type w} [∀ c, AddCommGroup (W c)] [∀ c, Module K (W c)]

/-- **One-slice speedup: appending `⟨1,s,1⟩` to both sides**
([AlmanLi2026], Proposition 5.4, p. 17; [Strassen1988], Lemma 3.12).

Let `f = (A,B,C)` restrict `S` to `T = f S`, let `ζ` be a functional on the `Z` leg of `S`, and
let `s` bound the rank of the contracted matrix `M = A ∘ (matrixFlatten ζ S) ∘ Bᵛ`.  Then `f`
extends to a family `F` on `S ⊕ ⟨1,s,1⟩` which

* agrees with `f` on the first summand and still produces exactly `T`;
* satisfies the flattened block condition of Proposition 5.3 for the functional `ζ' = (ζ, 1)`; and
* has contracted rank exactly `matrixRank ζ S + s`.

The last two clauses are precisely "`f'` satisfies the conditions of Proposition 5.3 with
`r = q + s`". -/
theorem exists_oneSliceAppend
    [FiniteDimensional K (V .X)] [FiniteDimensional K (W .Y)]
    (S : Tensor3 K V) (f : ∀ c, V c →ₗ[K] W c) (ζ : V .Z →ₗ[K] K) (s : ℕ)
    (hs : finrank K (LinearMap.range (f .X ∘ₗ matrixFlatten ζ S ∘ₗ (f .Y).dualMap)) ≤ s) :
    ∃ (F : ∀ c, (V c × MMSpace K 1 s 1 c) →ₗ[K] W c)
      (ζ' : (V .Z × MMSpace K 1 s 1 .Z) →ₗ[K] K),
      (∀ c, F c ∘ₗ LinearMap.inl K (V c) (MMSpace K 1 s 1 c) = f c) ∧
      Tensor.map F (Tensor.directSum S (matrixMultiplication (K := K) 1 s 1)) =
        Tensor.map f S ∧
      F .X ∘ₗ
          matrixFlatten ζ' (Tensor.directSum S (matrixMultiplication (K := K) 1 s 1)) ∘ₗ
          (F .Y).dualMap = 0 ∧
      matrixRank ζ' (Tensor.directSum S (matrixMultiplication (K := K) 1 s 1))
        = matrixRank ζ S + s := by
  classical
  obtain ⟨A₁, B₁, hAB⟩ :=
    exists_oneSlice_factorization (f .X ∘ₗ matrixFlatten ζ S ∘ₗ (f .Y).dualMap) s hs
  set F : ∀ c, (V c × MMSpace K 1 s 1 c) →ₗ[K] W c :=
    ofLegs (V := fun c ↦ (V c × MMSpace K 1 s 1 c) →ₗ[K] W c)
      ((f .X).coprod (-A₁)) ((f .Y).coprod B₁) ((f .Z).coprod 0) with hF
  set ζ' : (V .Z × MMSpace K 1 s 1 .Z) →ₗ[K] K := ζ.coprod (oneSliceZ K s) with hζ'
  have hζinl : ζ' ∘ₗ LinearMap.inl K (V .Z) (MMSpace K 1 s 1 .Z) = ζ :=
    LinearMap.coprod_inl _ _
  have hζinr : ζ' ∘ₗ LinearMap.inr K (V .Z) (MMSpace K 1 s 1 .Z) = oneSliceZ K s :=
    LinearMap.coprod_inr _ _
  have hinl : ∀ c, F c ∘ₗ LinearMap.inl K (V c) (MMSpace K 1 s 1 c) = f c := by
    intro c
    cases c <;> exact LinearMap.coprod_inl _ _
  refine ⟨F, ζ', hinl, ?_, ?_, ?_⟩
  · -- the extended family still produces `T`
    have hleft :
        Tensor.map F (Tensor.map (Tensor.includeLeft (K := K) (V := V)
          (W := MMSpace K 1 s 1)) S) = Tensor.map f S := by
      have hc := Tensor.map_comp (K := K)
        (Tensor.includeLeft (K := K) (V := V) (W := MMSpace K 1 s 1)) F
      rw [show (fun c ↦ F c ∘ₗ Tensor.includeLeft (K := K) (V := V)
        (W := MMSpace K 1 s 1) c) = f from funext hinl] at hc
      exact (LinearMap.congr_fun hc S).symm
    have hright :
        Tensor.map F (Tensor.map (Tensor.includeRight (K := K) (V := V)
          (W := MMSpace K 1 s 1)) (matrixMultiplication (K := K) 1 s 1)) = 0 := by
      have hc := Tensor.map_comp (K := K)
        (Tensor.includeRight (K := K) (V := V) (W := MMSpace K 1 s 1)) F
      have hz : Tensor.map (fun c ↦ F c ∘ₗ Tensor.includeRight (K := K) (V := V)
          (W := MMSpace K 1 s 1) c) (matrixMultiplication (K := K) 1 s 1) = 0 := by
        refine Tensor.map_eq_zero_of_coord _ _ .Z ?_
        simp only [hF, ofLegs_Z]
        exact LinearMap.coprod_inr _ _
      rw [hc] at hz
      exact hz
    rw [Tensor.directSum, LinearMap.map_add, hleft, hright, add_zero]
  · -- the flattened block condition
    rw [matrixFlatten_directSum, hζinl, hζinr]
    ext β
    have hbY : ∀ β : Dual K (W .Y),
        (LinearMap.inl K (V .Y) (MMSpace K 1 s 1 .Y)).dualMap ((F .Y).dualMap β)
          = (f .Y).dualMap β := by
      intro β
      ext v
      simp [hF]
    have hbY' : ∀ β : Dual K (W .Y),
        (LinearMap.inr K (V .Y) (MMSpace K 1 s 1 .Y)).dualMap ((F .Y).dualMap β)
          = B₁.dualMap β := by
      intro β
      ext v
      simp [hF]
    have hM := LinearMap.congr_fun hAB β
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.zero_apply,
      LinearMap.prod_apply, Function.prod, LinearMap.prodMap_apply, hbY, hbY']
    simp only [hF, ofLegs_X, LinearMap.coprod_apply, LinearMap.neg_apply]
    simp only [LinearMap.coe_comp, Function.comp_apply] at hM
    rw [hM]
    abel
  · -- the contracted rank
    rw [matrixRank_directSum, hζinl, hζinr, matrixRank_matrixMultiplication_one]

/-- **Proposition 5.4 composed with Proposition 5.3**
([AlmanLi2026], p. 17, the chain used to prove Theorem 6.1, p. 19).

For any `s` bounding the rank of the contracted matrix `M = A ∘ (matrixFlatten ζ S) ∘ Bᵛ`,

```text
S ⊕ ⟨1,s,1⟩  ⊵  T ⊕ ⟨1, q + s − n − m, 1⟩,
```

with `q = matrixRank ζ S`, `n = dim (W .X)` and `m = dim (W .Y)`.  Nothing is assumed about `ζ`
beyond finite-dimensionality of the legs: the block condition that Proposition 5.3 needs is
produced by the appended summand. -/
theorem polynomialDegenerates_directSum_oneSliceAppend
    [FiniteDimensional K (V .X)] [FiniteDimensional K (V .Y)]
    [FiniteDimensional K (W .X)] [FiniteDimensional K (W .Y)]
    (S : Tensor3 K V) (f : ∀ c, V c →ₗ[K] W c) (ζ : V .Z →ₗ[K] K) (s : ℕ)
    (hs : finrank K (LinearMap.range (f .X ∘ₗ matrixFlatten ζ S ∘ₗ (f .Y).dualMap)) ≤ s) :
    PolynomialDegenerates
      (Tensor.directSum S (matrixMultiplication (K := K) 1 s 1))
      (Tensor.directSum (Tensor.map f S)
        (matrixMultiplication (K := K) 1
          (matrixRank ζ S + s - finrank K (W .X) - finrank K (W .Y)) 1)) := by
  obtain ⟨F, ζ', -, hmap, hzero, hrank⟩ := exists_oneSliceAppend S f ζ s hs
  have hmain := polynomialDegenerates_directSum_oneSlice
    (Tensor.directSum S (matrixMultiplication (K := K) 1 s 1)) F ζ' hzero
  rw [hmap, hrank] at hmain
  exact hmain

end Field

end AlgebraicComplexity
