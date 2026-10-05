/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.Core
import AlgebraicComplexity.Tensor.MatrixFlattening
import AlgebraicComplexity.Tensor.Restriction

/-!
# The one-slice normal form of a contracted matrix

`Tensor/MatrixFlattening.lean` reads a tensor `S` contracted on its `Z` leg by a functional `ζ`
as a linear map `matrixFlatten ζ S` and defines its `matrixRank`.  This file supplies the missing
half of that interface, the one that has to mention the matrix-multiplication tensor: a matrix of
rank at least `t` **restricts onto `⟨1,t,1⟩`**.

This is the sentence "a rank-`t` matrix (viewed as a tensor) is isomorphic to `⟨1,t,1⟩`" at the
end of the proof of [AlmanLi2026, Proposition 5.3, p. 17].  The restriction direction stated here
is the one clients need: it converts a *lower* bound on the rank of the extracted summand of the
free-lunch speedup theorem into a genuine `⟨1,t,1⟩` direct summand.

## Main results

* `matrixMultiplication_one_eq_sum`: `⟨1,t,1⟩` as the explicit sum of its `t` pure terms.
* `restricts_matrixMultiplication_of_matrixRank`: `t ≤ matrixRank ζ S → S ⤳ ⟨1,t,1⟩`.
* `restricts_matrixMultiplication_matrixRank`: the converse half of the identification.  A
  contracted slice is *restricted from* `⟨1,r,1⟩` at its exact rank `r = matrixRank ζ S`, so
  `⟨1,s,1⟩ ⤳ (a ⊗ b ⊗ c) S` for every `s ≥ r` by composing with
  `matrixMultiplication_restricts` (`AlgebraicComplexity/MatrixMultiplication.lean`).  This is
  the input of [AlmanLi2026, Proposition 5.4]: the factorization `M = (A₁ ⊗ B₁) ⟨1,s,1⟩`.

## References

* J. Alman and B. Li, *Asymptotic rank speedup theorems, revisited*, arXiv:2605.21738
  ([AlmanLi2026]), Proposition 5.3, p. 17.
-/

namespace AlgebraicComplexity

open Tensor Module

universe u v

section

variable {K : Type u} [CommSemiring K]

/-- The one-slice matrix-multiplication tensor `⟨1,t,1⟩` as the sum of its `t` pure terms. -/
theorem matrixMultiplication_one_eq_sum (t : ℕ) :
    matrixMultiplication (K := K) 1 t 1 =
      ∑ j : Fin t, pure (K := K) (ofLegs (V := MMSpace K 1 t 1)
        (Pi.single (0, j) 1) (Pi.single (j, 0) 1) (Pi.single (0, 0) 1)) := by
  classical
  rw [matrixMultiplication]
  simp only [Fintype.sum_prod_type, Fin.sum_univ_one]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  refine congrArg _ ?_
  funext c
  cases c <;> rfl

end

section

variable {K : Type u} [Field K] {V : Leg → Type v}
variable [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]

/-- **A contracted slice of rank at least `t` restricts onto `⟨1,t,1⟩`**
([AlmanLi2026], Proposition 5.3, p. 17, final sentence of the proof).

`S` is contracted on its `Z` leg by `ζ`; if the resulting matrix has rank at least `t`, then
three leg maps carry `S` itself onto the one-slice matrix-multiplication tensor `⟨1,t,1⟩`.  The
maps are explicit: `t` functionals `β j` on the `Y` leg whose flattening values are linearly
independent, a dual family `α i` on the `X` leg, and `ζ` on the `Z` leg. -/
theorem restricts_matrixMultiplication_of_matrixRank
    (S : Tensor3 K V) (ζ : V .Z →ₗ[K] K) (t : ℕ) (ht : t ≤ matrixRank ζ S) :
    Restricts S (matrixMultiplication (K := K) 1 t 1) := by
  classical
  obtain ⟨β, α, hαβ⟩ := exists_flatten_dual_family ζ S t ht
  set aX : V .X →ₗ[K] MMSpace K 1 t 1 .X := LinearMap.pi fun p : Fin 1 × Fin t ↦ α p.2 with haX
  set bY : V .Y →ₗ[K] MMSpace K 1 t 1 .Y := LinearMap.pi fun p : Fin t × Fin 1 ↦ β p.1 with hbY
  set cZ : V .Z →ₗ[K] MMSpace K 1 t 1 .Z := LinearMap.pi fun _ : Fin 1 × Fin 1 ↦ ζ with hcZ
  have hb : ∀ v, bY v = ∑ j : Fin t, β j v • (Pi.single (j, 0) 1 : MMSpace K 1 t 1 .Y) := by
    intro v
    funext p
    obtain ⟨p₁, p₂⟩ := p
    have hp₂ : p₂ = 0 := Subsingleton.elim _ _
    subst hp₂
    simp [hbY, Pi.single_apply, Prod.ext_iff]
  have hc : ∀ z, cZ z = ζ z • (Pi.single (0, 0) 1 : MMSpace K 1 t 1 .Z) := by
    intro z
    funext p
    obtain ⟨p₁, p₂⟩ := p
    have hp₁ : p₁ = 0 := Subsingleton.elim _ _
    have hp₂ : p₂ = 0 := Subsingleton.elim _ _
    subst hp₁
    subst hp₂
    simp [hcZ]
  have hA : ∀ j : Fin t, aX (matrixFlatten ζ S (β j)) =
      (Pi.single (0, j) 1 : MMSpace K 1 t 1 .X) := by
    intro j
    funext p
    obtain ⟨p₁, p₂⟩ := p
    have hp₁ : p₁ = 0 := Subsingleton.elim _ _
    subst hp₁
    rw [haX]
    simp only [LinearMap.pi_apply, hαβ, Pi.single_apply, Prod.ext_iff]
    by_cases h : p₂ = j <;> simp [h]
  refine ⟨ofLegs aX bY cZ, ?_⟩
  rw [map_ofLegs_eq_sum_pure_of_flatten S ζ β
      (fun j ↦ (Pi.single (j, 0) 1 : MMSpace K 1 t 1 .Y))
      (Pi.single (0, 0) 1 : MMSpace K 1 t 1 .Z) aX bY cZ hb hc,
    matrixMultiplication_one_eq_sum]
  exact Finset.sum_congr rfl fun j _ ↦ by rw [hA j]

/-- **A contracted slice of rank `r` is restricted from `⟨1,r,1⟩`**
([AlmanLi2026], Proposition 5.4, p. 17: the factorization `M = (A₁ ⊗ B₁)⟨1,s,1⟩`).

Here `S` is contracted on its `Z` leg by `ζ`, and the legwise maps `(a,b,c)` are applied, with
the `Z`-leg map factoring through `ζ` with image spanned by `w₀`; the resulting matrix is the
image of `⟨1,r,1⟩` under explicit maps, where `r` is its exact rank.  For any `s ≥ r`, composing
with `matrixMultiplication_restricts (le_refl 1) h (le_refl 1)` gives
`⟨1,s,1⟩ ⤳ (a ⊗ b ⊗ c) S`. -/
theorem restricts_matrixMultiplication_matrixRank
    [FiniteDimensional K (V .X)] [FiniteDimensional K (V .Y)]
    {W : Leg → Type v} [∀ c, AddCommGroup (W c)] [∀ c, Module K (W c)]
    (S : Tensor3 K V) (ζ : V .Z →ₗ[K] K)
    (a : V .X →ₗ[K] W .X) (b : V .Y →ₗ[K] W .Y) (c : V .Z →ₗ[K] W .Z) (w₀ : W .Z)
    (hc : ∀ z, c z = ζ z • w₀) :
    Restricts (matrixMultiplication (K := K) 1 (matrixRank ζ S) 1)
      (map (ofLegs a b c) S) := by
  classical
  set φ := matrixFlatten ζ S with hφ
  set ρ := matrixRank ζ S with hρ
  set bs : Basis (Fin (finrank K (V .Y))) K (V .Y) := Module.finBasis K (V .Y) with hbs
  haveI : Module.Free K (LinearMap.range φ) := Module.Free.of_divisionRing K _
  set ub : Basis (Fin ρ) K (LinearMap.range φ) :=
    Module.finBasis K (LinearMap.range φ) with hub
  set u : Fin ρ → V .X := fun k ↦ ((ub k : LinearMap.range φ) : V .X) with hu
  set μ : Fin (finrank K (V .Y)) → Fin ρ → K :=
    fun j k ↦ ub.repr ⟨φ (bs.coord j), LinearMap.mem_range_self _ _⟩ k with hμ
  have hdecomp : ∀ j, φ (bs.coord j) = ∑ k, μ j k • u k := by
    intro j
    have hsum := ub.sum_repr ⟨φ (bs.coord j), LinearMap.mem_range_self _ _⟩
    have hcoe : ((∑ k, ub.repr ⟨φ (bs.coord j), LinearMap.mem_range_self _ _⟩ k •
        ub k : LinearMap.range φ) : V .X) = φ (bs.coord j) := by rw [hsum]
    rw [← hcoe, Submodule.coe_sum]
    rfl
  have hbfac : ∀ w, b w = ∑ j, bs.coord j w • b (bs j) := by
    intro w
    conv_lhs => rw [← bs.sum_repr w]
    rw [map_sum]
    exact Finset.sum_congr rfl fun j _ ↦ by rw [map_smul, Basis.coord_apply]
  set v : Fin ρ → W .Y := fun k ↦ ∑ j, μ j k • b (bs j) with hv
  have hmain : map (ofLegs a b c) S = ∑ k, pure (K := K) (ofLegs (a (u k)) (v k) w₀) := by
    rw [map_ofLegs_eq_sum_pure_of_flatten S ζ (fun j ↦ bs.coord j) (fun j ↦ b (bs j)) w₀
      a b c hbfac hc, ← hφ]
    have hterm : ∀ j, pure (K := K) (ofLegs (a (φ (bs.coord j))) (b (bs j)) w₀)
        = ∑ k, μ j k • pure (K := K) (ofLegs (a (u k)) (b (bs j)) w₀) := by
      intro j
      rw [hdecomp j, map_sum, pure_ofLegs_fintype_sum_X]
      exact Finset.sum_congr rfl fun k _ ↦ by rw [map_smul, pure_ofLegs_smul_X]
    rw [Finset.sum_congr rfl fun j (_ : j ∈ Finset.univ) ↦ hterm j, Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [hv, pure_ofLegs_fintype_sum_Y]
    exact Finset.sum_congr rfl fun j _ ↦ (pure_ofLegs_smul_Y _ _ _ _).symm
  set pX : Fin 1 × Fin ρ → (MMSpace K 1 ρ 1 .X →ₗ[K] K) :=
    fun q ↦ LinearMap.proj (R := K) (φ := fun _ : Fin 1 × Fin ρ ↦ K) q with hpX
  set pY : Fin ρ × Fin 1 → (MMSpace K 1 ρ 1 .Y →ₗ[K] K) :=
    fun q ↦ LinearMap.proj (R := K) (φ := fun _ : Fin ρ × Fin 1 ↦ K) q with hpY
  set pZ : Fin 1 × Fin 1 → (MMSpace K 1 ρ 1 .Z →ₗ[K] K) :=
    fun q ↦ LinearMap.proj (R := K) (φ := fun _ : Fin 1 × Fin 1 ↦ K) q with hpZ
  refine ⟨ofLegs
    (∑ k, LinearMap.smulRight (pX ((0 : Fin 1), k)) (a (u k)))
    (∑ k, LinearMap.smulRight (pY (k, (0 : Fin 1))) (v k))
    (LinearMap.smulRight (pZ ((0 : Fin 1), (0 : Fin 1))) w₀), ?_⟩
  rw [matrixMultiplication_one_eq_sum, map_sum, hmain]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [Tensor.map_pure, pure_ofLegs_linearMap_apply]
  simp only [ofLegs_X, ofLegs_Y, ofLegs_Z]
  have hX : (∑ k', LinearMap.smulRight (pX ((0 : Fin 1), k')) (a (u k')))
      (Pi.single (0, k) 1 : MMSpace K 1 ρ 1 .X) = a (u k) := by
    simp [hpX, Pi.single_apply, Prod.ext_iff]
  have hY : (∑ k', LinearMap.smulRight (pY (k', (0 : Fin 1))) (v k'))
      (Pi.single (k, 0) 1 : MMSpace K 1 ρ 1 .Y) = v k := by
    simp [hpY, Pi.single_apply, Prod.ext_iff]
  have hZ : (LinearMap.smulRight (pZ ((0 : Fin 1), (0 : Fin 1))) w₀)
      (Pi.single (0, 0) 1 : MMSpace K 1 ρ 1 .Z) = w₀ := by
    simp [hpZ]
  rw [hX, hY, hZ]

end

end AlgebraicComplexity
