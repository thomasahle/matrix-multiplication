/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.OneSliceNormalForm
import AlgebraicComplexity.Tensor.FreeLunchSpeedup

/-!
# Speedup by one slice: the maximal free-lunch choice

`Tensor/FreeLunchSpeedup.lean` proves [AlmanLi2026, Theorem 5.1]: for *any* second family of leg
maps `g` whose three mixed blocks annihilate `S`, the source degenerates to `T ⊕ (g S)`.  It says
nothing about how big the extracted summand `g S` is, because that is a statement about matrix
rank ([AlmanLi2026, Proposition 5.3, p. 17]).

This file makes the maximal choice and proves the size bound.  Fix a functional `ζ` on the `Z`
leg of `S` in the kernel of the restriction — the paper's one-dimensional `C' ⊆ Cᗮ` — and write
`φ = matrixFlatten ζ S` for the contracted matrix.  The paper's maximal annihilator subspaces are

```text
A' = {u ∈ Uᵛ : (u ⊗ B ⊗ ζ) S = 0},   B' = {v ∈ Vᵛ : (A ⊗ v ⊗ ζ) S = 0},
```

and the structure theorem `map_ofLegs_eq_sum_pure_of_flatten` turns both descriptions into
kernel conditions on `φ`: `A'` is cut out by `range (φ ∘ Bᵛ)`, and `B' = ker (A ∘ φ)`.  Their
aggregate maps therefore have kernels of dimension at most `dim V'` and `dim U'`, and
`matrixRank_le_add_of_map` bounds the rank loss by exactly those two numbers.

## Main result

* `polynomialDegenerates_directSum_oneSlice`: **Theorem 5.1 composed with Proposition 5.3**.  If
  `f = (A,B,C)` restricts `S` to `T` and `A ∘ φ ∘ Bᵛ = 0`, then

  ```text
  S ⊵ T ⊕ ⟨1, r − n − m, 1⟩,   r = matrixRank ζ S, n = dim (W .X), m = dim (W .Y).
  ```

The hypothesis is stated on the flattening rather than as `(A ⊗ B ⊗ ζ) S = 0` because that is
what the proof uses and because it is basis-free; `flatten_comp_eq_zero_of_map_eq_zero` in
`Tensor/MatrixFlattening.lean` derives it from any tensor-level realization of the paper's
condition.

## References

* J. Alman and B. Li, *Asymptotic rank speedup theorems, revisited*, arXiv:2605.21738
  ([AlmanLi2026]), Theorem 5.1 (p. 14) and Proposition 5.3 (p. 17).
* V. Strassen, *The asymptotic spectrum of tensors*, J. reine angew. Math. 384 (1988)
  ([Strassen1988]), Lemma 3.11.
-/

namespace AlgebraicComplexity

open Tensor Module

universe u v w

section

variable {K : Type u} [Field K]

/-- Coordinate indices of the extracted one-slice summand: `dX` rows, `dY` columns, one slice. -/
private abbrev SliceIndex (dX dY : ℕ) : Leg → Type
  | .X => Fin dX
  | .Y => Fin dY
  | .Z => Fin 1

/-- Leg spaces of the extracted summand.  These are coordinate spaces, so all their algebraic
instances are the uniform `Pi` ones. -/
private abbrev SliceSpace (K : Type u) (dX dY : ℕ) : Leg → Type u :=
  CoordinateSpace K (SliceIndex dX dY)

/-- A tuple of functionals, expanded in the standard basis of its coordinate target. -/
private theorem pi_eq_sum_smul_single {M : Type*} [AddCommGroup M] [Module K M] {d : ℕ}
    (γ : Fin d → Dual K M) (v : M) :
    LinearMap.pi γ v = ∑ k, γ k v • (Pi.single k 1 : Fin d → K) := by
  classical
  funext k
  simp [Pi.single_apply]

/-- A subspace `Φ` of the dual of a finite-dimensional space is the span of a finite family of
functionals whose common kernel is the coannihilator of `Φ`.  This is the "aggregate linear map"
of a subspace of `Uᵛ` in the sense of [AlmanLi2026, §5.1, p. 14]. -/
private theorem exists_dual_family_span {M : Type*} [AddCommGroup M] [Module K M]
    [FiniteDimensional K M] (Φ : Submodule K (Dual K M)) :
    ∃ (d : ℕ) (γ : Fin d → Dual K M), (∀ k, γ k ∈ Φ) ∧
      LinearMap.ker (LinearMap.pi γ) = Φ.dualCoannihilator := by
  classical
  haveI : Module.Free K Φ := Module.Free.of_divisionRing K ↥Φ
  set bs : Basis (Fin (finrank K Φ)) K Φ := Module.finBasis K Φ with hbs
  refine ⟨finrank K Φ, fun k ↦ ((bs k : Dual K M)), fun k ↦ (bs k).2, ?_⟩
  have hspan : Submodule.span K (Set.range fun k ↦ ((bs k : Dual K M))) = Φ := by
    have hrange : (Set.range fun k ↦ ((bs k : Dual K M))) = Φ.subtype '' Set.range bs := by
      rw [← Set.range_comp]
      rfl
    rw [hrange, ← Submodule.map_span, Basis.span_eq, Submodule.map_top,
      Submodule.range_subtype]
  ext x
  simp only [LinearMap.mem_ker, Submodule.mem_dualCoannihilator, LinearMap.pi_apply,
    funext_iff, Pi.zero_apply]
  constructor
  · intro h q hq
    rw [← hspan] at hq
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hq
    · rintro _ ⟨k, rfl⟩
      exact h k
    · simp
    · intro q₁ q₂ _ _ h₁ h₂
      simp [h₁, h₂]
    · intro a q _ h₁
      simp [h₁]
  · intro h k
    have hmem : ((bs k : Dual K M)) ∈
        Submodule.span K (Set.range fun k ↦ ((bs k : Dual K M))) :=
      Submodule.subset_span ⟨k, rfl⟩
    rw [hspan] at hmem
    exact h _ hmem

variable {V : Leg → Type v} [∀ c, AddCommGroup (V c)] [∀ c, Module K (V c)]
variable {W : Leg → Type w} [∀ c, AddCommGroup (W c)] [∀ c, Module K (W c)]

/-- **One-slice speedup, maximal free-lunch choice**
([AlmanLi2026], Theorem 5.1, p. 14, composed with Proposition 5.3, p. 17).

Let `f = (A,B,C)` restrict `S` to `T = f S`, let `ζ` be a functional on the `Z` leg of `S` whose
contracted matrix `φ = matrixFlatten ζ S` satisfies `A ∘ φ ∘ Bᵛ = 0` (the paper's `C' ⊆ Cᗮ` for
the one-dimensional `C' = ⟨ζ⟩`), and write `r` for the rank of that matrix, `n = dim U'`,
`m = dim V'`.  Then

```text
S ⊵ T ⊕ ⟨1, r − n − m, 1⟩.
```

The extracted summand is obtained for free: nothing is added to the source. -/
theorem polynomialDegenerates_directSum_oneSlice
    [FiniteDimensional K (V .X)] [FiniteDimensional K (V .Y)]
    [FiniteDimensional K (W .X)] [FiniteDimensional K (W .Y)]
    (S : Tensor3 K V) (f : ∀ c, V c →ₗ[K] W c) (ζ : V .Z →ₗ[K] K)
    (hAB : f .X ∘ₗ matrixFlatten ζ S ∘ₗ (f .Y).dualMap = 0) :
    PolynomialDegenerates S
      (Tensor.directSum (map f S)
        (matrixMultiplication (K := K) 1
          (matrixRank ζ S - finrank K (W .X) - finrank K (W .Y)) 1)) := by
  classical
  set φ := matrixFlatten ζ S with hφ
  set n := finrank K (W .X) with hn
  set m := finrank K (W .Y) with hm
  -- The `Y` leg map of the restriction, expanded in a basis of its target.
  set bY : Basis (Fin m) K (W .Y) := Module.finBasis K (W .Y) with hbY
  set β : Fin m → Dual K (V .Y) := fun j ↦ (f .Y).dualMap (bY.coord j) with hβ
  have hfY : ∀ v, f .Y v = ∑ j, β j v • bY j := by
    intro v
    conv_lhs => rw [← bY.sum_repr (f .Y v)]
    simp [hβ, Basis.coord_apply]
  -- The maximal `A'`: kernel exactly the span of the flattening values used by `B`.
  set R : Submodule K (V .X) := LinearMap.range (φ ∘ₗ (f .Y).dualMap) with hR
  have hRm : finrank K R ≤ m := by
    have h₁ : R = Submodule.map φ (LinearMap.range (f .Y).dualMap) := by
      rw [hR, LinearMap.range_comp]
    have h₂ : finrank K (LinearMap.range (f .Y).dualMap) = finrank K (LinearMap.range (f .Y)) :=
      LinearMap.finrank_range_dualMap_eq_finrank_range _
    calc finrank K R ≤ finrank K (LinearMap.range (f .Y).dualMap) := by
          rw [h₁]; exact Submodule.finrank_map_le _ _
      _ = finrank K (LinearMap.range (f .Y)) := h₂
      _ ≤ m := by rw [hm]; exact Submodule.finrank_le _
  obtain ⟨dX, γX, hγXmem, hγXker⟩ := exists_dual_family_span (K := K) R.dualAnnihilator
  have hkerX : LinearMap.ker (LinearMap.pi γX) = R := by
    rw [hγXker, Subspace.dualAnnihilator_dualCoannihilator_eq]
  -- The maximal `B'`: kernel the coannihilator of `ker (A ∘ φ)`.
  set Q : Submodule K (Dual K (V .Y)) := LinearMap.ker (f .X ∘ₗ φ) with hQ
  obtain ⟨dY, γY, hγYmem, hγYker⟩ := exists_dual_family_span (K := K) Q
  have hkerY : finrank K (LinearMap.ker (LinearMap.pi γY)) ≤ n := by
    have h₁ : finrank K Q + finrank K Q.dualCoannihilator = finrank K (V .Y) :=
      Subspace.finrank_add_finrank_dualCoannihilator_eq Q
    have h₂ : finrank K (LinearMap.range (f .X ∘ₗ φ)) + finrank K Q = finrank K (V .Y) := by
      rw [hQ]
      have := LinearMap.finrank_range_add_finrank_ker (f .X ∘ₗ φ)
      rwa [Subspace.dual_finrank_eq] at this
    have h₃ : finrank K (LinearMap.range (f .X ∘ₗ φ)) ≤ n := by
      rw [hn]; exact Submodule.finrank_le _
    rw [hγYker]
    omega
  -- The extracted family of leg maps.
  set aX : V .X →ₗ[K] SliceSpace K dX dY .X := LinearMap.pi γX with haX
  set bYY : V .Y →ₗ[K] SliceSpace K dX dY .Y := LinearMap.pi γY with hbYY
  set cZ : V .Z →ₗ[K] SliceSpace K dX dY .Z :=
    LinearMap.pi (fun _ : Fin 1 ↦ ζ) with hcZ
  set g : ∀ c, V c →ₗ[K] SliceSpace K dX dY c := ofLegs aX bYY cZ with hg
  -- The three mixed blocks vanish.
  have hcZ' : ∀ z, cZ z = ζ z • (Pi.single (0 : Fin 1) 1 : SliceSpace K dX dY .Z) := by
    intro z
    funext p
    have hp : p = 0 := Subsingleton.elim _ _
    subst hp
    simp [hcZ]
  have hcInr : ∀ z, (LinearMap.inr K (W .Z) (SliceSpace K dX dY .Z) ∘ₗ cZ) z =
      ζ z • LinearMap.inr K (W .Z) (SliceSpace K dX dY .Z) (Pi.single 0 1) := by
    intro z
    rw [LinearMap.comp_apply, hcZ' z, map_smul]
  have hbInl : ∀ v, (LinearMap.inl K (W .Y) (SliceSpace K dX dY .Y) ∘ₗ f .Y) v =
      ∑ j, β j v • (LinearMap.inl K (W .Y) (SliceSpace K dX dY .Y) (bY j)) := by
    intro v
    rw [LinearMap.comp_apply, hfY v, map_sum]
    exact Finset.sum_congr rfl fun j _ ↦ by rw [map_smul]
  have h₁ : map (ofLegs (V := fun c ↦ V c →ₗ[K] W c × SliceSpace K dX dY c)
      (directSumLeftMaps (K := K) (SliceSpace K dX dY) f .X)
      (directSumLeftMaps (K := K) (SliceSpace K dX dY) f .Y)
      (directSumRightMaps (K := K) W g .Z)) S = 0 := by
    rw [show (directSumRightMaps (K := K) W g .Z) =
        LinearMap.inr K (W .Z) (SliceSpace K dX dY .Z) ∘ₗ cZ from rfl]
    rw [map_ofLegs_eq_sum_pure_of_flatten S ζ β
      (fun j ↦ LinearMap.inl K (W .Y) (SliceSpace K dX dY .Y) (bY j))
      (LinearMap.inr K (W .Z) (SliceSpace K dX dY .Z) (Pi.single 0 1)) _ _ _ hbInl hcInr]
    rw [← hφ]
    refine Finset.sum_eq_zero fun j _ ↦ ?_
    have hzero : f .X (φ (β j)) = 0 := by
      have := LinearMap.congr_fun hAB (bY.coord j)
      simpa [hβ, hφ] using this
    simp only [directSumLeftMaps, LinearMap.coe_comp, Function.comp_apply, hzero, map_zero]
    exact pure_ofLegs_zero_X _ _
  have h₂ : map (ofLegs (V := fun c ↦ V c →ₗ[K] W c × SliceSpace K dX dY c)
      (directSumRightMaps (K := K) W g .X)
      (directSumLeftMaps (K := K) (SliceSpace K dX dY) f .Y)
      (directSumRightMaps (K := K) W g .Z)) S = 0 := by
    rw [show (directSumRightMaps (K := K) W g .Z) =
        LinearMap.inr K (W .Z) (SliceSpace K dX dY .Z) ∘ₗ cZ from rfl]
    rw [map_ofLegs_eq_sum_pure_of_flatten S ζ β
      (fun j ↦ LinearMap.inl K (W .Y) (SliceSpace K dX dY .Y) (bY j))
      (LinearMap.inr K (W .Z) (SliceSpace K dX dY .Z) (Pi.single 0 1)) _ _ _ hbInl hcInr]
    rw [← hφ]
    refine Finset.sum_eq_zero fun j _ ↦ ?_
    have hmem : φ (β j) ∈ R := by
      rw [hR]
      exact ⟨bY.coord j, rfl⟩
    have hzero : aX (φ (β j)) = 0 := by
      rw [haX, ← LinearMap.mem_ker, hkerX]
      exact hmem
    simp only [directSumRightMaps, LinearMap.coe_comp, Function.comp_apply, hg, ofLegs_X,
      hzero, map_zero]
    exact pure_ofLegs_zero_X _ _
  have h₃ : map (ofLegs (V := fun c ↦ V c →ₗ[K] W c × SliceSpace K dX dY c)
      (directSumLeftMaps (K := K) (SliceSpace K dX dY) f .X)
      (directSumRightMaps (K := K) W g .Y)
      (directSumRightMaps (K := K) W g .Z)) S = 0 := by
    have hb : ∀ v, (LinearMap.inr K (W .Y) (SliceSpace K dX dY .Y) ∘ₗ bYY) v =
        ∑ k, γY k v •
          (LinearMap.inr K (W .Y) (SliceSpace K dX dY .Y) (Pi.single k 1)) := by
      intro v
      rw [LinearMap.comp_apply, hbYY, pi_eq_sum_smul_single γY v, map_sum]
      exact Finset.sum_congr rfl fun k _ ↦ by rw [map_smul]
    rw [show (directSumRightMaps (K := K) W g .Y) =
        LinearMap.inr K (W .Y) (SliceSpace K dX dY .Y) ∘ₗ bYY from rfl,
      show (directSumRightMaps (K := K) W g .Z) =
        LinearMap.inr K (W .Z) (SliceSpace K dX dY .Z) ∘ₗ cZ from rfl]
    rw [map_ofLegs_eq_sum_pure_of_flatten S ζ γY
      (fun k ↦ LinearMap.inr K (W .Y) (SliceSpace K dX dY .Y) (Pi.single k 1))
      (LinearMap.inr K (W .Z) (SliceSpace K dX dY .Z) (Pi.single 0 1)) _ _ _ hb hcInr]
    rw [← hφ]
    refine Finset.sum_eq_zero fun k _ ↦ ?_
    have hzero : f .X (φ (γY k)) = 0 := by
      have := hγYmem k
      rw [hQ, LinearMap.mem_ker] at this
      simpa using this
    simp only [directSumLeftMaps, LinearMap.coe_comp, Function.comp_apply, hzero, map_zero]
    exact pure_ofLegs_zero_X _ _
  -- Free-lunch speedup.
  have hfree := polynomialDegeneratesAt_two_directSum_of_mixed_map_eq_zero
    (K := K) (V := V) (W := W) (W' := SliceSpace K dX dY) (S := S) f g h₁ h₂ h₃
  -- The extracted summand has large rank.
  set ζ' : SliceSpace K dX dY .Z →ₗ[K] K := LinearMap.proj (0 : Fin 1) with hζ'
  have hζc : ζ' ∘ₗ cZ = ζ := by
    ext z
    simp [hζ', hcZ]
  have hgeq : map g S = map (ofLegs aX bYY cZ) S := by rw [hg]
  have hrank := matrixRank_le_add_of_map (K := K) S ζ ζ' aX bYY cZ hζc
  have hbound : matrixRank ζ S - n - m ≤ matrixRank ζ' (map g S) := by
    rw [hgeq]
    have hA : finrank K (LinearMap.ker aX) ≤ m := by
      rw [haX, hkerX]
      exact hRm
    have hB : finrank K (LinearMap.ker bYY) ≤ n := by
      rw [hbYY]
      exact hkerY
    omega
  have hnf : Restricts (map g S)
      (matrixMultiplication (K := K) 1 (matrixRank ζ S - n - m) 1) :=
    restricts_matrixMultiplication_of_matrixRank (map g S) ζ' _ hbound
  exact hfree.toPolynomialDegenerates.trans
    (PolynomialDegenerates.of_restricts (Restricts.directSum (Restricts.refl _) hnf))

end

end AlgebraicComplexity
