/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Tensor.FreeLunchSpeedup
import AlgebraicComplexity.Tensor.PolynomialKernelFrame
import AlgebraicComplexity.Tensor.PolynomialScalar

/-!
# The one-slice speedup for a border-rank certificate

This file proves the *border-rank* form of the one-slice speedup of Alman and Li
([AlmanLi2026, Theorem 6.1, p. 19]) together with its grouped version (Theorem 6.3, p. 21), in a
presentation-independent form.  The matrix-multiplication statements are instances
(`MatrixMultiplication/NonminimalBorderRankSpeedup.lean`).

## Statement

Let `∑_{i<r} a_i(ε) ⊗ b_i(ε) ⊗ c_i(ε) = ε^d T + O(ε^(d+1))` be a border-rank certificate of a
tensor `T` whose `X` and `Y` legs have dimensions `nX` and `nY`.  Let `g` assign some of the `r`
terms to `p` groups, each of size at least `m + nX`.  Then

```text
⟨r⟩ ⊕ (p ⊙ ⟨1,nY,1⟩)  ⊵  T ⊕ (p ⊙ ⟨1,m,1⟩).
```

With one group containing every term and `m = r − nX` this is Theorem 6.1,
`⟨r⟩ ⊕ ⟨1,n,1⟩ ⊵ T ⊕ ⟨1,r−n,1⟩`; with `p` groups of size `3n` and `m = 2n` it is Theorem 6.3.

The source is given abstractly as `oneSliceFrameTensor βX βY βZ`: three bases indexed by
`Fin r ⊕ Fin p × Fin nY` (twice) and `Fin r ⊕ Fin p`, with the tensor the sum of the diagonal
terms and of the slice terms.  The target summand is any tensor of the form
`∑_a ∑_{k<m} x'_{a,k} ⊗ y'_{a,k} ⊗ z'_a`.  Both `⟨r⟩ ⊕ ⟨1,n,1⟩` on coordinate spaces and
`⟨r⟩ ⊕ (p ⊙ ⟨1,n,1⟩)` on indexed direct-sum spaces are of this shape.

## Why no function-field layer is needed

The paper runs Propositions 5.3 and 5.4 over `F(λ)` and descends by Corollary 5.1.  Here the
polynomial free-lunch theorem `polynomialDegeneratesAt_add_of_mixed_eq_zero` is applied directly
to two explicit *polynomial* families of leg maps on the source, described by the images of the
basis vectors `e_i` (diagonal part) and `f_{a,j}`, `g_{a,j}`, `h_a` (slices):

```text
F :  e_i ↦ (a_i, b_i, c_i),      f_{a,j} ↦ −∑_{i ∈ a} B_{ji} a_i,     g_{a,j} ↦ v_j,   h_a ↦ 0,
G :  e_i ↦ (α_i, δ_i, z'_{g i}), f_{a,j} ↦ −∑_{i ∈ a} B_{ji} α_i,     g_{a,j} ↦ 0,     h_a ↦ z'_a.
```

Here `b_i = ∑_j B_{ji} v_j` and `a_i = ∑_j P_{ji} u_j` are the coordinate expansions in bases
`v`, `u` of the two legs of `T`, with coefficients in `K[X]`, and `(δ, α)` is a kernel frame of
the polynomial matrix `P` restricted to each group
(`exists_polynomial_kernel_frame_finset`): `P δ = 0` and `αᵀ δ = q · 1` with
`q = X^D + O(X^(D+1))`.  Then

* the pure block `(F,F,F)` is the certificate itself, since `h_a ↦ 0` kills the slices;
* the mixed blocks `(F,F,G)` and `(G,F,G)` vanish because the slice terms were chosen to cancel
  the `b_i`-expansion of the diagonal terms (`sum_polynomialPure_cancel`);
* the mixed block `(F,G,G)` vanishes because `P δ = 0` (`sum_polynomialPure_kernel`);
* the pure block `(G,G,G)` is `∑_a q_a · ⟨1,m,1⟩_a` because `αᵀ δ = q · 1`
  (`sum_polynomialPure_frame`), which leads with the target summand in degree `D`.

The only use of a field of fractions is inside the kernel-frame lemma, whose conclusion is a
statement about polynomials.

## Main results

* `PolynomialLinearMap.ofBasis`, `applyVector_ofBasis`: the polynomial family of linear maps with
  prescribed polynomial images of a finite basis;
* `oneSliceFrameTensor`, `polynomialTransform_oneSliceFrameTensor`: the framed source and the
  effect of a basis-defined polynomial family on it;
* `BorderRankLE.exists_fin_family`: a border-rank certificate as a family indexed by `Fin r`;
* `polynomialDegenerates_oneSliceFrameTensor_directSum`: the grouped border-rank one-slice
  speedup.

## References

* J. Alman and B. Li, *Asymptotic rank speedup theorems, revisited*, arXiv:2605.21738
  ([AlmanLi2026]), Theorems 6.1 and 6.3.
-/

namespace AlgebraicComplexity.Tensor

open scoped Polynomial

open Module PolynomialVector

universe u v w w'

section OfBasis

variable {K : Type u} [CommSemiring K]
variable {M : Type v} {N : Type w}
variable [AddCommMonoid M] [Module K M] [AddCommMonoid N] [Module K N]

/-- The polynomial family of linear maps sending the basis vector `b i` to the polynomial vector
`v i`. -/
noncomputable def PolynomialLinearMap.ofBasis {ι : Type*} [Fintype ι] (b : Basis ι K M)
    (v : ι → PolynomialVector N) : PolynomialLinearMap K M N :=
  ∑ i, PolynomialVector.mapLinear (K := K) (LinearMap.smulRightₗ (b.coord i)) (v i)

/-- `PolynomialLinearMap.ofBasis b v` sends `b i` to `v i`. -/
theorem PolynomialLinearMap.applyVector_ofBasis {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Basis ι K M) (v : ι → PolynomialVector N) (i : ι) :
    PolynomialLinearMap.applyVector (PolynomialLinearMap.ofBasis b v) (b i) = v i := by
  ext d
  rw [PolynomialLinearMap.applyVector_coeff]
  simp [PolynomialLinearMap.ofBasis, Finsupp.single_apply]

end OfBasis

section Frame

variable {K : Type u} [CommSemiring K]
variable {S : Leg → Type v} {N : Leg → Type w}
variable [∀ c, AddCommMonoid (S c)] [∀ c, Module K (S c)]
variable [∀ c, AddCommMonoid (N c)] [∀ c, Module K (N c)]

/-- The tensor `⟨r⟩ ⊕ (p ⊙ ⟨1,n,1⟩)` presented by bases of its three legs: the diagonal terms
`e_i ⊗ e_i ⊗ e_i` and the slice terms `f_{a,j} ⊗ g_{a,j} ⊗ h_a`. -/
noncomputable def oneSliceFrameTensor {r p n : ℕ}
    (βX : Basis (Fin r ⊕ Fin p × Fin n) K (S .X)) (βY : Basis (Fin r ⊕ Fin p × Fin n) K (S .Y))
    (βZ : Basis (Fin r ⊕ Fin p) K (S .Z)) : Tensor3 K S :=
  ∑ i, pure (K := K) (ofLegs (βX (.inl i)) (βY (.inl i)) (βZ (.inl i))) +
    ∑ a, ∑ j, pure (K := K) (ofLegs (βX (.inr (a, j))) (βY (.inr (a, j))) (βZ (.inr a)))

/-- A polynomial family of leg maps defined on the three bases of a framed source transforms it
termwise. -/
theorem polynomialTransform_oneSliceFrameTensor {r p n : ℕ}
    (βX : Basis (Fin r ⊕ Fin p × Fin n) K (S .X)) (βY : Basis (Fin r ⊕ Fin p × Fin n) K (S .Y))
    (βZ : Basis (Fin r ⊕ Fin p) K (S .Z))
    (vX : Fin r ⊕ Fin p × Fin n → PolynomialVector (N .X))
    (vY : Fin r ⊕ Fin p × Fin n → PolynomialVector (N .Y))
    (vZ : Fin r ⊕ Fin p → PolynomialVector (N .Z)) :
    polynomialTransform
        (ofLegs (V := fun c ↦ PolynomialLinearMap K (S c) (N c))
          (PolynomialLinearMap.ofBasis βX vX) (PolynomialLinearMap.ofBasis βY vY)
          (PolynomialLinearMap.ofBasis βZ vZ))
        (oneSliceFrameTensor βX βY βZ) =
      ∑ i, polynomialPure (K := K) (ofLegs (vX (.inl i)) (vY (.inl i)) (vZ (.inl i))) +
        ∑ a, ∑ j, polynomialPure (K := K)
          (ofLegs (vX (.inr (a, j))) (vY (.inr (a, j))) (vZ (.inr a))) := by
  classical
  have hpure : ∀ (iX iY : Fin r ⊕ Fin p × Fin n) (iZ : Fin r ⊕ Fin p),
      polynomialTransform
          (ofLegs (V := fun c ↦ PolynomialLinearMap K (S c) (N c))
            (PolynomialLinearMap.ofBasis βX vX) (PolynomialLinearMap.ofBasis βY vY)
            (PolynomialLinearMap.ofBasis βZ vZ))
          (pure (K := K) (ofLegs (βX iX) (βY iY) (βZ iZ))) =
        polynomialPure (K := K) (ofLegs (vX iX) (vY iY) (vZ iZ)) := by
    intro iX iY iZ
    rw [polynomialTransform_pure]
    congr 1
    funext c
    cases c
    · exact PolynomialLinearMap.applyVector_ofBasis βX vX iX
    · exact PolynomialLinearMap.applyVector_ofBasis βY vY iY
    · exact PolynomialLinearMap.applyVector_ofBasis βZ vZ iZ
  rw [oneSliceFrameTensor, polynomialTransform_add, polynomialTransform_fintype_sum,
    polynomialTransform_fintype_sum]
  simp only [polynomialTransform_fintype_sum, hpure]

/-- A border-rank certificate of size at most `r` can be presented as a family of exactly `r`
polynomial pure tensors, padding with zero terms. -/
theorem BorderRankLE.exists_fin_family {V : Leg → Type v}
    [∀ c, AddCommMonoid (V c)] [∀ c, Module K (V c)] {r : ℕ} {T : Tensor3 K V}
    (h : BorderRankLE r T) :
    ∃ (d : ℕ) (x : Fin r → ∀ c, PolynomialVector (V c)),
      HasLeadingTerm (∑ i, polynomialPure (K := K) (x i)) d T := by
  classical
  obtain ⟨d, terms, hlen, hlead⟩ := h
  set terms' := terms ++ List.replicate (r - terms.length) (0 : ∀ c, PolynomialVector (V c))
    with hterms'
  have hlen' : terms'.length = r := by
    rw [hterms', List.length_append, List.length_replicate]
    omega
  have hzero : polynomialPure (K := K) (0 : ∀ c, PolynomialVector (V c)) = 0 := by
    simp [polynomialPure]
  have hsum : (terms'.map (polynomialPure (K := K))).sum =
      (terms.map (polynomialPure (K := K))).sum := by
    rw [hterms', List.map_append, List.sum_append, List.map_replicate, hzero]
    simp
  refine ⟨d, fun j ↦ terms'.get (Fin.cast hlen'.symm j), ?_⟩
  have hfin : (terms'.map (polynomialPure (K := K))).sum =
      ∑ j : Fin r, polynomialPure (K := K) (terms'.get (Fin.cast hlen'.symm j)) := by
    rw [Tensor.list_map_sum_eq_fin_sum]
    exact Fintype.sum_equiv (finCongr hlen') _ _ fun j ↦ rfl
  rw [← hfin, hsum]
  exact hlead

end Frame

/-- Regroup a sum over `ι` along a partial assignment `g : ι → Option κ` of its indices to
groups: indices sent to `none` must contribute zero. -/
theorem sum_eq_sum_fiber_option {ι κ A : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    [AddCommMonoid A] (g : ι → Option κ) (F : ι → A) (G : κ → ι → A)
    (h0 : ∀ i, g i = none → F i = 0) (h1 : ∀ i a, g i = some a → F i = G a i) :
    ∑ i, F i = ∑ a, ∑ i ∈ Finset.univ.filter (fun i ↦ g i = some a), G a i := by
  classical
  have h : ∀ a, ∑ i ∈ Finset.univ.filter (fun i ↦ g i = some a), G a i =
      ∑ i, if g i = some a then F i else 0 := by
    intro a
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    split_ifs with hi
    · exact (h1 i a hi).symm
    · rfl
  simp only [h]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  cases hgi : g i with
  | none => simp [h0 i hgi]
  | some b => simp

section Core

variable {K : Type u} [CommRing K]
variable {N : Leg → Type w} [∀ c, AddCommGroup (N c)] [∀ c, Module K (N c)]

/-- **Cancellation of the `Y`-expansion.**  If `η i = ∑_j B j i • v_j` over `K[X]`, then the
diagonal terms `ξ_i ⊗ η_i ⊗ ζ_{g i}` are cancelled by the slice terms
`(−∑_{i ∈ a} B j i • ξ_i) ⊗ v_j ⊗ ζ_a`.  This is the vanishing of the mixed blocks `(F,F,G)` and
`(G,F,G)` of the border-rank one-slice speedup. -/
theorem sum_polynomialPure_cancel {r p n : ℕ} (g : Fin r → Option (Fin p))
    (ξ : Fin r → PolynomialVector (N .X)) (η : Fin r → PolynomialVector (N .Y))
    (v : Fin n → N .Y) (B : Fin n → Fin r → K[X])
    (hη : ∀ i, ∑ j, polySMul (B j i) (constant (v j)) = η i)
    (ζ : Fin p → PolynomialVector (N .Z)) :
    ∑ i, polynomialPure (K := K) (ofLegs (ξ i) (η i) ((g i).elim 0 ζ)) +
      ∑ a, ∑ j, polynomialPure (K := K)
        (ofLegs (∑ i ∈ Finset.univ.filter (fun i ↦ g i = some a), polySMul (-B j i) (ξ i))
          (constant (v j)) (ζ a)) = 0 := by
  classical
  have hfirst : ∑ i, polynomialPure (K := K) (ofLegs (ξ i) (η i) ((g i).elim 0 ζ)) =
      ∑ a, ∑ i ∈ Finset.univ.filter (fun i ↦ g i = some a), ∑ j,
        polySMul (B j i) (polynomialPure (K := K) (ofLegs (ξ i) (constant (v j)) (ζ a))) := by
    refine sum_eq_sum_fiber_option g _ _ (fun i hi ↦ ?_) (fun i a hi ↦ ?_)
    · simp [hi]
    · simp only [hi, Option.elim_some]
      rw [← hη i, polynomialPure_finset_sum_Y]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      rw [polynomialPure_polySMul_Y]
  have hsecond : ∀ a, ∑ j, polynomialPure (K := K)
        (ofLegs (∑ i ∈ Finset.univ.filter (fun i ↦ g i = some a), polySMul (-B j i) (ξ i))
          (constant (v j)) (ζ a)) =
      ∑ i ∈ Finset.univ.filter (fun i ↦ g i = some a), ∑ j,
        polySMul (-B j i) (polynomialPure (K := K) (ofLegs (ξ i) (constant (v j)) (ζ a))) := by
    intro a
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [polynomialPure_finset_sum_X]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [polynomialPure_polySMul_X]
  rw [hfirst]
  simp only [hsecond]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun a _ ↦ ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun i _ ↦ ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun j _ ↦ ?_
  rw [← add_polySMul, add_neg_cancel, zero_polySMul]

/-- **The kernel relation kills the mixed block.**  If `ξ i = ∑_j P j i • u_j` over `K[X]` and
`∑_{i ∈ a} P j i · δ a i k = 0` for every group `a`, then
`∑_i ξ_i ⊗ (∑_k δ_{g i} i k • y_{g i,k}) ⊗ ζ_{g i} = 0`.  This is the vanishing of the mixed
block `(F,G,G)`. -/
theorem sum_polynomialPure_kernel {r p n m : ℕ} (g : Fin r → Option (Fin p))
    (ξ : Fin r → PolynomialVector (N .X)) (u : Fin n → N .X) (P : Fin n → Fin r → K[X])
    (hξ : ∀ i, ∑ j, polySMul (P j i) (constant (u j)) = ξ i)
    (δ : Fin p → Fin r → Fin m → K[X])
    (hδ : ∀ a j k, ∑ i ∈ Finset.univ.filter (fun i ↦ g i = some a), P j i * δ a i k = 0)
    (y : Fin p → Fin m → PolynomialVector (N .Y)) (ζ : Fin p → PolynomialVector (N .Z)) :
    ∑ i, polynomialPure (K := K) (ofLegs (ξ i)
        ((g i).elim 0 fun a ↦ ∑ k, polySMul (δ a i k) (y a k)) ((g i).elim 0 ζ)) = 0 := by
  classical
  have hfirst : ∑ i, polynomialPure (K := K) (ofLegs (ξ i)
        ((g i).elim 0 fun a ↦ ∑ k, polySMul (δ a i k) (y a k)) ((g i).elim 0 ζ)) =
      ∑ a, ∑ i ∈ Finset.univ.filter (fun i ↦ g i = some a), ∑ j, ∑ k,
        polySMul (P j i * δ a i k)
          (polynomialPure (K := K) (ofLegs (constant (u j)) (y a k) (ζ a))) := by
    refine sum_eq_sum_fiber_option g _ _ (fun i hi ↦ ?_) (fun i a hi ↦ ?_)
    · simp [hi]
    · simp only [hi, Option.elim_some]
      rw [← hξ i]
      exact polynomialPure_sum_polySMul_XY _ _ _ _ _ _ _
  rw [hfirst]
  refine Finset.sum_eq_zero fun a _ ↦ ?_
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun j _ ↦ ?_
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun k _ ↦ ?_
  rw [← finset_sum_polySMul, hδ, zero_polySMul]

/-- **The frame relation produces the slices.**  If `∑_{i ∈ a} α a i l · δ a i k = q_a · [l = k]`
for every group `a`, then the pure block `(G,G,G)` is `∑_a q_a • ⟨1,m,1⟩_a`, where
`⟨1,m,1⟩_a = ∑_k x_{a,k} ⊗ y_{a,k} ⊗ z_a`. -/
theorem sum_polynomialPure_frame {r p m : ℕ} (g : Fin r → Option (Fin p))
    (α δ : Fin p → Fin r → Fin m → K[X]) (q : Fin p → K[X])
    (hαδ : ∀ a l k, ∑ i ∈ Finset.univ.filter (fun i ↦ g i = some a), α a i l * δ a i k =
      if l = k then q a else 0)
    (x : Fin p → Fin m → N .X) (y : Fin p → Fin m → N .Y) (z : Fin p → N .Z) :
    ∑ i, polynomialPure (K := K) (ofLegs
        ((g i).elim 0 fun a ↦ ∑ l, polySMul (α a i l) (constant (x a l)))
        ((g i).elim 0 fun a ↦ ∑ k, polySMul (δ a i k) (constant (y a k)))
        ((g i).elim 0 fun a ↦ constant (z a))) =
      ∑ a, polySMul (q a)
        (constant (∑ k, pure (K := K) (ofLegs (x a k) (y a k) (z a)))) := by
  classical
  have hfirst : ∑ i, polynomialPure (K := K) (ofLegs
        ((g i).elim 0 fun a ↦ ∑ l, polySMul (α a i l) (constant (x a l)))
        ((g i).elim 0 fun a ↦ ∑ k, polySMul (δ a i k) (constant (y a k)))
        ((g i).elim 0 fun a ↦ constant (z a))) =
      ∑ a, ∑ i ∈ Finset.univ.filter (fun i ↦ g i = some a), ∑ l, ∑ k,
        polySMul (α a i l * δ a i k)
          (constant (pure (K := K) (ofLegs (x a l) (y a k) (z a)))) := by
    refine sum_eq_sum_fiber_option g _ _ (fun i hi ↦ ?_) (fun i a hi ↦ ?_)
    · simp [hi]
    · simp only [hi, Option.elim_some]
      rw [polynomialPure_sum_polySMul_XY]
      simp only [polynomialPure_constant]
  rw [hfirst]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  rw [Finset.sum_comm]
  have hinner : ∀ l, ∑ i ∈ Finset.univ.filter (fun i ↦ g i = some a), ∑ k,
        polySMul (α a i l * δ a i k)
          (constant (pure (K := K) (ofLegs (x a l) (y a k) (z a)))) =
      polySMul (q a) (constant (pure (K := K) (ofLegs (x a l) (y a l) (z a)))) := by
    intro l
    rw [Finset.sum_comm]
    simp only [← finset_sum_polySMul, hαδ]
    rw [Finset.sum_eq_single l]
    · rw [if_pos rfl]
    · intro k _ hk
      rw [if_neg (Ne.symm hk), zero_polySMul]
    · intro h
      exact absurd (Finset.mem_univ l) h
  simp only [hinner]
  rw [constant_finset_sum, polySMul_finset_sum]

end Core

section Main

variable {K : Type u} [Field K]
variable {S : Leg → Type v} {V : Leg → Type w} {W' : Leg → Type w'}
variable [∀ c, AddCommGroup (S c)] [∀ c, Module K (S c)]
variable [∀ c, AddCommGroup (V c)] [∀ c, Module K (V c)]
variable [∀ c, AddCommGroup (W' c)] [∀ c, Module K (W' c)]

/-- **The grouped one-slice speedup for a border-rank certificate**
([AlmanLi2026], Theorems 6.1 and 6.3, pp. 19–21).

Let `x` be a border-rank certificate of `T` with `r` terms, let `bX`, `bY` be bases of the `X`
and `Y` legs of `T` of sizes `nX` and `nY`, and let `g` assign some of the terms to `p` groups,
each of size at least `m + nX` (stated with truncated subtraction, so that `m = 0` needs no
hypothesis).  Then the framed source `⟨r⟩ ⊕ (p ⊙ ⟨1,nY,1⟩)` degenerates to
`T ⊕ ∑_a ∑_{k<m} x'_{a,k} ⊗ y'_{a,k} ⊗ z'_a`, i.e. to `T ⊕ (p ⊙ ⟨1,m,1⟩)`.

Nothing is assumed about the vectors `x'`, `y'`, `z'`, and terms that `g` sends to `none` belong
to no group. -/
theorem polynomialDegenerates_oneSliceFrameTensor_directSum {r p nX nY m : ℕ}
    (βX : Basis (Fin r ⊕ Fin p × Fin nY) K (S .X))
    (βY : Basis (Fin r ⊕ Fin p × Fin nY) K (S .Y))
    (βZ : Basis (Fin r ⊕ Fin p) K (S .Z))
    (bX : Basis (Fin nX) K (V .X)) (bY : Basis (Fin nY) K (V .Y))
    (x : Fin r → ∀ c, PolynomialVector (V c)) {d : ℕ} {T : Tensor3 K V}
    (hT : HasLeadingTerm (∑ i, polynomialPure (K := K) (x i)) d T)
    (g : Fin r → Option (Fin p))
    (hg : ∀ a, m ≤ (Finset.univ.filter fun i ↦ g i = some a).card - nX)
    (x' : Fin p → Fin m → W' .X) (y' : Fin p → Fin m → W' .Y) (z' : Fin p → W' .Z) :
    PolynomialDegenerates (oneSliceFrameTensor βX βY βZ)
      (directSum T (∑ a, ∑ k, pure (K := K) (ofLegs (x' a k) (y' a k) (z' a)))) := by
  classical
  -- Coordinate polynomials of the certificate in the two bases.
  let P : Fin nX → Fin r → K[X] :=
    fun j i ↦ toPolynomial (mapLinear (K := K) (bX.coord j) (x i .X))
  let B : Fin nY → Fin r → K[X] :=
    fun j i ↦ toPolynomial (mapLinear (K := K) (bY.coord j) (x i .Y))
  -- One kernel frame per group, brought to a common leading degree `D`.
  have hframe := fun a ↦ exists_polynomial_kernel_frame_finset
    (Finset.univ.filter fun i ↦ g i = some a) nX m P (hg a)
  choose δ hδ d₀ hD using hframe
  let D : ℕ := ∑ a, d₀ a
  have hle : ∀ a, d₀ a ≤ D := fun a ↦
    Finset.single_le_sum (f := d₀) (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ a)
  choose α q hαδ hq1 hqlow using fun a ↦ hD a D (hle a)
  -- The two inclusions into the block sum.
  let il : ∀ c, V c →ₗ[K] V c × W' c := includeLeft (K := K) (V := V) (W := W')
  let ir : ∀ c, W' c →ₗ[K] V c × W' c := includeRight (K := K) (V := V) (W := W')
  -- The images of the basis vectors under the two families.
  let ζ : Fin p → PolynomialVector (V .Z × W' .Z) := fun a ↦ constant (ir .Z (z' a))
  let aX : Fin r → PolynomialVector (V .X × W' .X) :=
    fun i ↦ mapLinear (K := K) (il .X) (x i .X)
  let aY : Fin r → PolynomialVector (V .Y × W' .Y) :=
    fun i ↦ mapLinear (K := K) (il .Y) (x i .Y)
  let gX : Fin r → PolynomialVector (V .X × W' .X) :=
    fun i ↦ (g i).elim 0 fun a ↦ ∑ l, polySMul (α a i l) (constant (ir .X (x' a l)))
  let gY : Fin r → PolynomialVector (V .Y × W' .Y) :=
    fun i ↦ (g i).elim 0 fun a ↦ ∑ k, polySMul (δ a i k) (constant (ir .Y (y' a k)))
  let FvX : Fin r ⊕ Fin p × Fin nY → PolynomialVector (V .X × W' .X) :=
    Sum.elim aX fun aj ↦
      ∑ i ∈ Finset.univ.filter (fun i ↦ g i = some aj.1), polySMul (-B aj.2 i) (aX i)
  let FvY : Fin r ⊕ Fin p × Fin nY → PolynomialVector (V .Y × W' .Y) :=
    Sum.elim aY fun aj ↦ constant (il .Y (bY aj.2))
  let FvZ : Fin r ⊕ Fin p → PolynomialVector (V .Z × W' .Z) :=
    Sum.elim (fun i ↦ mapLinear (K := K) (il .Z) (x i .Z)) fun _ ↦ 0
  let GvX : Fin r ⊕ Fin p × Fin nY → PolynomialVector (V .X × W' .X) :=
    Sum.elim gX fun aj ↦
      ∑ i ∈ Finset.univ.filter (fun i ↦ g i = some aj.1), polySMul (-B aj.2 i) (gX i)
  let GvY : Fin r ⊕ Fin p × Fin nY → PolynomialVector (V .Y × W' .Y) :=
    Sum.elim gY fun _ ↦ 0
  let GvZ : Fin r ⊕ Fin p → PolynomialVector (V .Z × W' .Z) :=
    Sum.elim (fun i ↦ (g i).elim 0 ζ) ζ
  let F : ∀ c, PolynomialLinearMap K (S c) (V c × W' c) :=
    ofLegs (V := fun c ↦ PolynomialLinearMap K (S c) (V c × W' c))
      (PolynomialLinearMap.ofBasis βX FvX) (PolynomialLinearMap.ofBasis βY FvY)
      (PolynomialLinearMap.ofBasis βZ FvZ)
  let G : ∀ c, PolynomialLinearMap K (S c) (V c × W' c) :=
    ofLegs (V := fun c ↦ PolynomialLinearMap K (S c) (V c × W' c))
      (PolynomialLinearMap.ofBasis βX GvX) (PolynomialLinearMap.ofBasis βY GvY)
      (PolynomialLinearMap.ofBasis βZ GvZ)
  -- The two coordinate expansions, pushed into the block sum.
  have haY : ∀ i, ∑ j, polySMul (B j i) (constant (il .Y (bY j))) = aY i :=
    fun i ↦ sum_polySMul_basis_mapLinear bY (il .Y) (x i .Y)
  have haX : ∀ i, ∑ j, polySMul (P j i) (constant (il .X (bX j))) = aX i :=
    fun i ↦ sum_polySMul_basis_mapLinear bX (il .X) (x i .X)
  -- The pure block `(F,F,F)` is the certificate.
  have hF : HasLeadingTerm (polynomialTransform F (oneSliceFrameTensor βX βY βZ)) d
      (map (includeLeft (K := K) (V := V) (W := W')) T) := by
    show HasLeadingTerm (polynomialTransform
      (ofLegs (V := fun c ↦ PolynomialLinearMap K (S c) (V c × W' c))
        (PolynomialLinearMap.ofBasis βX FvX) (PolynomialLinearMap.ofBasis βY FvY)
        (PolynomialLinearMap.ofBasis βZ FvZ)) (oneSliceFrameTensor βX βY βZ)) d _
    rw [polynomialTransform_oneSliceFrameTensor]
    have hslices : ∑ a, ∑ j, polynomialPure (K := K)
        (ofLegs (V := fun c ↦ PolynomialVector (V c × W' c))
          (FvX (.inr (a, j))) (FvY (.inr (a, j))) (FvZ (.inr a))) = 0 := by
      refine Finset.sum_eq_zero fun a _ ↦ Finset.sum_eq_zero fun j _ ↦ ?_
      simp only [FvZ, Sum.elim_inr, polynomialPure_zero_Z]
    have hmain : ∑ i, polynomialPure (K := K)
        (ofLegs (V := fun c ↦ PolynomialVector (V c × W' c))
          (FvX (.inl i)) (FvY (.inl i)) (FvZ (.inl i))) =
        mapLinear (K := K) (map (includeLeft (K := K) (V := V) (W := W')))
          (∑ i, polynomialPure (K := K) (x i)) := by
      rw [map_sum]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [polynomialPure_mapLinear]
      congr 1
      funext c
      cases c <;> rfl
    rw [hslices, add_zero, hmain]
    exact hT.mapLinear _
  -- The pure block `(G,G,G)` is the sum of the slices, each scaled by its pivot polynomial.
  have hG : HasLeadingTerm (polynomialTransform G (oneSliceFrameTensor βX βY βZ)) D
      (map (includeRight (K := K) (V := V) (W := W'))
        (∑ a, ∑ k, pure (K := K) (ofLegs (x' a k) (y' a k) (z' a)))) := by
    show HasLeadingTerm (polynomialTransform
      (ofLegs (V := fun c ↦ PolynomialLinearMap K (S c) (V c × W' c))
        (PolynomialLinearMap.ofBasis βX GvX) (PolynomialLinearMap.ofBasis βY GvY)
        (PolynomialLinearMap.ofBasis βZ GvZ)) (oneSliceFrameTensor βX βY βZ)) D _
    rw [polynomialTransform_oneSliceFrameTensor]
    have hmain := sum_polynomialPure_frame (N := fun c ↦ V c × W' c) g α δ q hαδ
      (fun a l ↦ ir .X (x' a l)) (fun a k ↦ ir .Y (y' a k)) (fun a ↦ ir .Z (z' a))
    have hmap : map (includeRight (K := K) (V := V) (W := W'))
        (∑ a, ∑ k, pure (K := K) (ofLegs (x' a k) (y' a k) (z' a))) =
        ∑ a, ∑ k, pure (K := K) (ofLegs (V := fun c ↦ V c × W' c)
          (ir .X (x' a k)) (ir .Y (y' a k)) (ir .Z (z' a))) := by
      simp only [map_sum, map_pure]
      refine Finset.sum_congr rfl fun a _ ↦ Finset.sum_congr rfl fun k _ ↦ ?_
      congr 1
      funext c
      cases c <;> rfl
    simp only [GvX, GvY, GvZ, gX, gY, ζ, Sum.elim_inl, Sum.elim_inr, polynomialPure_zero_Y,
      Finset.sum_const_zero, add_zero]
    rw [hmain, hmap]
    exact HasLeadingTerm.finset_sum _ fun a _ ↦
      hasLeadingTerm_polySMul_constant (hq1 a) (hqlow a) _
  -- The three mixed blocks vanish.
  have h₁ : polynomialTransform
      (ofLegs (V := fun c ↦ PolynomialLinearMap K (S c) (V c × W' c)) (F .X) (F .Y) (G .Z))
      (oneSliceFrameTensor βX βY βZ) = 0 := by
    show polynomialTransform
      (ofLegs (V := fun c ↦ PolynomialLinearMap K (S c) (V c × W' c))
        (PolynomialLinearMap.ofBasis βX FvX) (PolynomialLinearMap.ofBasis βY FvY)
        (PolynomialLinearMap.ofBasis βZ GvZ)) (oneSliceFrameTensor βX βY βZ) = 0
    rw [polynomialTransform_oneSliceFrameTensor]
    simp only [FvX, FvY, GvZ, Sum.elim_inl, Sum.elim_inr]
    exact sum_polynomialPure_cancel (N := fun c ↦ V c × W' c) g aX aY
      (fun j ↦ il .Y (bY j)) B haY ζ
  have h₂ : polynomialTransform
      (ofLegs (V := fun c ↦ PolynomialLinearMap K (S c) (V c × W' c)) (G .X) (F .Y) (G .Z))
      (oneSliceFrameTensor βX βY βZ) = 0 := by
    show polynomialTransform
      (ofLegs (V := fun c ↦ PolynomialLinearMap K (S c) (V c × W' c))
        (PolynomialLinearMap.ofBasis βX GvX) (PolynomialLinearMap.ofBasis βY FvY)
        (PolynomialLinearMap.ofBasis βZ GvZ)) (oneSliceFrameTensor βX βY βZ) = 0
    rw [polynomialTransform_oneSliceFrameTensor]
    simp only [GvX, FvY, GvZ, Sum.elim_inl, Sum.elim_inr]
    exact sum_polynomialPure_cancel (N := fun c ↦ V c × W' c) g gX aY
      (fun j ↦ il .Y (bY j)) B haY ζ
  have h₃ : polynomialTransform
      (ofLegs (V := fun c ↦ PolynomialLinearMap K (S c) (V c × W' c)) (F .X) (G .Y) (G .Z))
      (oneSliceFrameTensor βX βY βZ) = 0 := by
    show polynomialTransform
      (ofLegs (V := fun c ↦ PolynomialLinearMap K (S c) (V c × W' c))
        (PolynomialLinearMap.ofBasis βX FvX) (PolynomialLinearMap.ofBasis βY GvY)
        (PolynomialLinearMap.ofBasis βZ GvZ)) (oneSliceFrameTensor βX βY βZ) = 0
    rw [polynomialTransform_oneSliceFrameTensor]
    simp only [FvX, GvY, GvZ, gY, Sum.elim_inl, Sum.elim_inr, polynomialPure_zero_Y,
      Finset.sum_const_zero, add_zero]
    exact sum_polynomialPure_kernel (N := fun c ↦ V c × W' c) g aX (fun j ↦ il .X (bX j)) P haX
      δ hδ (fun a k ↦ constant (ir .Y (y' a k))) ζ
  exact (polynomialDegeneratesAt_add_of_mixed_eq_zero F G hF hG h₁ h₂ h₃).toPolynomialDegenerates

end Main

end AlgebraicComplexity.Tensor
