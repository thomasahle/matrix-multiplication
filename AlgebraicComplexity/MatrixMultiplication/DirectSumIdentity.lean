/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.DirectSum
import AlgebraicComplexity.Tensor.FreeLunchSpeedup
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.LinearAlgebra.StdBasis

/-!
# The Alman–Li direct-sum identity

This file proves [AlmanLi2026, Theorem 7.3, p. 29]: for block sizes `n_α ≥ 1` (`α < p`) and
`m_β ≥ 1` (`β < q`), with `N = ∑ n_α` and `M = ∑ m_β`,

```text
⟨N·M⟩ ⊕ ⟨p,1,q⟩   ⊵   ⟨N,1,M⟩ ⊕ ⊕_{α,β} ⟨1, (n_α − 1)(m_β − 1), 1⟩.
```

At `p = q = 1` this is Schönhage's identity
`⟨n,1,m⟩ ⊕ ⟨1,(n−1)(m−1),1⟩ ⊴ ⟨nm + 1⟩` ([Schonhage1981], Lemma 6.1) for *all* `n` and `m`;
`Examples/Schonhage.lean` has the instance `n = m = 3` as an explicit ten-term certificate.

## Proof

One application of the restriction form of the free-lunch theorem
(`Tensor.polynomialDegenerates_directSum_of_mixed_map_eq_zero`), which turns two families of leg
maps `f`, `g` out of a source `S` into the degeneration `S ⊵ f S ⊕ g S` as soon as the three mixed
blocks `(f,f,g)`, `(g,f,g)`, `(f,g,g)` annihilate `S`.

Write the source as `∑_{i,j} u_{ij} ⊗ v_{ij} ⊗ w_{ij} + ∑_{α,β} u'_α ⊗ v'_β ⊗ w'_{βα}`, with `i`
running over the rows (grouped into `p` blocks `I_α`) and `j` over the columns (grouped into `q`
blocks `J_β`).

* `f` is the *redundant* restriction onto `⟨N,1,M⟩ = ∑ x_i ⊗ y_j ⊗ z_{ji}`:

  ```text
  u_{ij} ↦ x_i,   v_{ij} ↦ y_j,   w_{ij} ↦ z_{ji},
  u'_α ↦ ∑_{i ∈ I_α} x_i,   v'_β ↦ ∑_{j ∈ J_β} y_j,   w'_{βα} ↦ 0.
  ```

  It does not use `⟨p,1,q⟩` at all; the values on `u'`, `v'` are what make the first mixed block
  vanish.
* `g` maps onto the slices `∑_{i ∈ I_α°, j ∈ J_β°} a_{ij} ⊗ b_{ij} ⊗ c_{αβ}`, where `I_α°` is
  `I_α` without its first element `i_α`, and likewise `J_β°`:

  ```text
  u_{ij} ↦ a_{ij}   with   a_{i_α j} = −∑_{i ∈ I_α°} a_{ij},   a_{i j_β} = 0,
  v_{ij} ↦ b_{ij}   with   b_{i j_β} = −∑_{j ∈ J_β°} b_{ij},   b_{i_α j} = 0,
  w_{ij} ↦ c_{αβ},  w'_{βα} ↦ −c_{αβ},   u'_α, v'_β ↦ 0.
  ```

  Then `g S` is exactly the slices (a term with `i = i_α` or `j = j_β` has a zero factor), the
  block `(f,f,g)` is `∑_{α,β} (∑_{I_α} x_i) ⊗ (∑_{J_β} y_j) ⊗ c_{αβ}` minus itself, and the
  blocks `(g,f,g)`, `(f,g,g)` vanish because every column sum `∑_{i ∈ I_α} a_{ij}` and every row
  sum `∑_{j ∈ J_β} b_{ij}` is zero.

These are Schönhage's correction terms, block by block.  To keep "the first element of a block"
free of subtraction, the core is stated for block sizes `n α + 1` and `m β + 1`, with slices of
size `n α · m β`; `Examples/AlmanLiOneSliceSpeedup.lean` restates it in the paper's form.

## Main results

* `dsSource`: `⟨N·M⟩ ⊕ ⟨p,1,q⟩` in standard coordinates, indexed by block and position.
* `polynomialDegenerates_dsSource`: the identity for that presentation.
* `restricts_directSum_dsSource`: the indexed-direct-sum presentation restricts onto it.
* `polynomialDegenerates_unit_directSum_matrixMultiplication`: **Theorem 7.3**.

## References

* J. Alman and B. Li, *Asymptotic rank speedup theorems, revisited*, arXiv:2605.21738
  ([AlmanLi2026]), Theorem 7.3, p. 29.
* A. Schönhage, *Partial and total matrix multiplication*, SIAM J. Comput. 10 (1981)
  ([Schonhage1981]), Lemma 6.1.
-/

namespace AlgebraicComplexity

open Tensor Module

universe u

/-! ### Multilinearity of pure tensors over finite sums -/

namespace Tensor

section PureSums

variable {K : Type u} [CommRing K]
variable {V : Leg → Type*} [∀ c, AddCommGroup (V c)] [∀ c, Module K (V c)]

/-- A pure tensor distributes over a finite sum in its `X` component. -/
theorem pure_ofLegs_sum_X {α : Type*} (s : Finset α) (x : α → V .X) (y : V .Y) (z : V .Z) :
    pure (K := K) (ofLegs (∑ a ∈ s, x a) y z) = ∑ a ∈ s, pure (K := K) (ofLegs (x a) y z) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, pure_ofLegs_add_X, ih]

/-- A pure tensor distributes over a finite sum in its `Y` component. -/
theorem pure_ofLegs_sum_Y {α : Type*} (s : Finset α) (x : V .X) (y : α → V .Y) (z : V .Z) :
    pure (K := K) (ofLegs x (∑ a ∈ s, y a) z) = ∑ a ∈ s, pure (K := K) (ofLegs x (y a) z) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, pure_ofLegs_add_Y, ih]

/-- The image of a pure tensor written with `ofLegs` under a family of leg maps. -/
theorem map_pure_ofLegs {W : Leg → Type*} [∀ c, AddCommGroup (W c)] [∀ c, Module K (W c)]
    (f : ∀ c, V c →ₗ[K] W c) (x : V .X) (y : V .Y) (z : V .Z) :
    map f (pure (K := K) (ofLegs x y z)) =
      pure (K := K) (ofLegs (V := W) (f .X x) (f .Y y) (f .Z z)) := by
  rw [map_pure]
  refine congrArg _ ?_
  funext c
  cases c <;> rfl

end PureSums

end Tensor

/-- A linear map defined on the standard basis of a coordinate space, evaluated on a basis
vector. -/
theorem basisFun_constr_single {K : Type u} [CommSemiring K] {ι : Type*} [Fintype ι]
    [DecidableEq ι] {M : Type*} [AddCommMonoid M] [Module K M] (v : ι → M) (i : ι) :
    (Pi.basisFun K ι).constr K v (Pi.single i 1) = v i := by
  rw [← Pi.basisFun_apply, Basis.constr_basis]

section Core

variable (K : Type u) [Field K] {p q : ℕ} (n : Fin p → ℕ) (m : Fin q → ℕ)

/-- Row indices: a block `α < p` and a position in that block, which has `n α + 1` rows. -/
abbrev DSRow : Type := (a : Fin p) × Fin (n a + 1)

/-- Column indices: a block `β < q` and a position in that block, which has `m β + 1` columns. -/
abbrev DSCol : Type := (b : Fin q) × Fin (m b + 1)

/-- Coordinate indices of `⟨N·M⟩ ⊕ ⟨p,1,q⟩`: a (row, column) pair of the unit tensor, or an index
of the corresponding leg of `⟨p,1,q⟩`. -/
abbrev DSIndex : Leg → Type
  | .X => (DSRow n × DSCol m) ⊕ Fin p
  | .Y => (DSRow n × DSCol m) ⊕ Fin q
  | .Z => (DSRow n × DSCol m) ⊕ (Fin q × Fin p)

instance (c : Leg) : Fintype (DSIndex n m c) := by
  cases c <;> infer_instance

instance (c : Leg) : DecidableEq (DSIndex n m c) := by
  cases c <;> infer_instance

/-- `⟨N·M⟩ ⊕ ⟨p,1,q⟩` in standard coordinates, with the unit tensor indexed by (row, column). -/
noncomputable def dsSource : Tensor3 K (CoordinateSpace K (DSIndex n m)) :=
  (∑ e : DSRow n × DSCol m, Tensor.pure (K := K)
    (ofLegs (V := CoordinateSpace K (DSIndex n m))
      (Pi.single (Sum.inl e) 1 : (DSRow n × DSCol m) ⊕ Fin p → K)
      (Pi.single (Sum.inl e) 1 : (DSRow n × DSCol m) ⊕ Fin q → K)
      (Pi.single (Sum.inl e) 1 : (DSRow n × DSCol m) ⊕ (Fin q × Fin p) → K))) +
  ∑ a : Fin p, ∑ b : Fin q, Tensor.pure (K := K)
    (ofLegs (V := CoordinateSpace K (DSIndex n m))
      (Pi.single (Sum.inr a) 1 : (DSRow n × DSCol m) ⊕ Fin p → K)
      (Pi.single (Sum.inr b) 1 : (DSRow n × DSCol m) ⊕ Fin q → K)
      (Pi.single (Sum.inr (b, a)) 1 : (DSRow n × DSCol m) ⊕ (Fin q × Fin p) → K))

/-- Leg spaces of the slices `⊕_{α,β} ⟨1, n α · m β, 1⟩`. -/
abbrev DSSliceSpace : Leg → Type u :=
  MMDirectSumSpace K (fun _ : Fin p × Fin q ↦ 1) (fun ab ↦ n ab.1 * m ab.2) (fun _ ↦ 1)

/-- The `X` basis vector `t` of slice `(α, β)`. -/
noncomputable def dsSliceX (ab : Fin p × Fin q) (t : Fin (n ab.1 * m ab.2)) :
    DSSliceSpace K n m .X :=
  indexedInclude (K := K) (V := fun ab : Fin p × Fin q ↦ MMSpace K 1 (n ab.1 * m ab.2) 1) ab .X
    (Pi.single ((0 : Fin 1), t) 1)

/-- The `Y` basis vector `t` of slice `(α, β)`. -/
noncomputable def dsSliceY (ab : Fin p × Fin q) (t : Fin (n ab.1 * m ab.2)) :
    DSSliceSpace K n m .Y :=
  indexedInclude (K := K) (V := fun ab : Fin p × Fin q ↦ MMSpace K 1 (n ab.1 * m ab.2) 1) ab .Y
    (Pi.single (t, (0 : Fin 1)) 1)

/-- The `Z` basis vector of slice `(α, β)`. -/
noncomputable def dsSliceZ (ab : Fin p × Fin q) : DSSliceSpace K n m .Z :=
  indexedInclude (K := K) (V := fun ab : Fin p × Fin q ↦ MMSpace K 1 (n ab.1 * m ab.2) 1) ab .Z
    (Pi.single ((0 : Fin 1), (0 : Fin 1)) 1)

/-- The slices `⊕_{α,β} ⟨1, n α · m β, 1⟩` as a sum of pure tensors. -/
theorem oneSliceDirectSum_eq_sum_dsSlice :
    matrixMultiplicationDirectSum K (fun _ : Fin p × Fin q ↦ 1) (fun ab ↦ n ab.1 * m ab.2)
        (fun _ ↦ 1) =
      ∑ ab : Fin p × Fin q, ∑ t : Fin (n ab.1 * m ab.2), Tensor.pure (K := K)
        (ofLegs (V := DSSliceSpace K n m)
          (dsSliceX K n m ab t) (dsSliceY K n m ab t) (dsSliceZ K n m ab)) := by
  rw [matrixMultiplicationDirectSum, indexedDirectSum]
  refine Finset.sum_congr rfl fun ab _ ↦ ?_
  rw [matrixMultiplication_outer_one, map_sum]
  refine Finset.sum_congr rfl fun t _ ↦ ?_
  rw [Tensor.map_pure]
  refine congrArg _ ?_
  funext c
  cases c <;> rfl

/-- The `X`-leg correction vectors `a_{ij}` of block `(α, β)`, for a column `j` that is not the
first of its block: a basis vector for a row that is not the first of its block, and minus the
sum of those for the first row. -/
noncomputable def dsA (a : Fin p) (b : Fin q) (k : Fin (n a + 1)) (l' : Fin (m b)) :
    DSSliceSpace K n m .X :=
  Fin.cases (motive := fun _ ↦ DSSliceSpace K n m .X)
    (-∑ k' : Fin (n a), dsSliceX K n m (a, b) (finProdFinEquiv (k', l')))
    (fun k' ↦ dsSliceX K n m (a, b) (finProdFinEquiv (k', l'))) k

/-- The `Y`-leg correction vectors `b_{ij}` of block `(α, β)`, for a row `i` that is not the
first of its block. -/
noncomputable def dsB (a : Fin p) (b : Fin q) (k' : Fin (n a)) (l : Fin (m b + 1)) :
    DSSliceSpace K n m .Y :=
  Fin.cases (motive := fun _ ↦ DSSliceSpace K n m .Y)
    (-∑ l' : Fin (m b), dsSliceY K n m (a, b) (finProdFinEquiv (k', l')))
    (fun l' ↦ dsSliceY K n m (a, b) (finProdFinEquiv (k', l'))) l

/-- Every column sum of the `X`-leg correction vectors over a block of rows vanishes. -/
theorem sum_dsA (a : Fin p) (b : Fin q) (l' : Fin (m b)) :
    ∑ k : Fin (n a + 1), dsA K n m a b k l' = 0 := by
  rw [Fin.sum_univ_succ]
  simp [dsA]

/-- Every row sum of the `Y`-leg correction vectors over a block of columns vanishes. -/
theorem sum_dsB (a : Fin p) (b : Fin q) (k' : Fin (n a)) :
    ∑ l : Fin (m b + 1), dsB K n m a b k' l = 0 := by
  rw [Fin.sum_univ_succ]
  simp [dsB]

/-- The `X`-leg value of the second family on the unit coordinate `(i, j)`. -/
noncomputable def dsGX (e : DSRow n × DSCol m) : DSSliceSpace K n m .X :=
  Fin.cases (motive := fun _ ↦ DSSliceSpace K n m .X) 0
    (fun l' ↦ dsA K n m e.1.1 e.2.1 e.1.2 l') e.2.2

/-- The `Y`-leg value of the second family on the unit coordinate `(i, j)`. -/
noncomputable def dsGY (e : DSRow n × DSCol m) : DSSliceSpace K n m .Y :=
  Fin.cases (motive := fun _ ↦ DSSliceSpace K n m .Y) 0
    (fun k' ↦ dsB K n m e.1.1 e.2.1 k' e.2.2) e.1.2

/-- The first family of leg maps: the redundant restriction onto `⟨N,1,M⟩`. -/
noncomputable def dsF : ∀ c, CoordinateSpace K (DSIndex n m) c →ₗ[K]
    MMSpace K (∑ a, (n a + 1)) 1 (∑ b, (m b + 1)) c
  | .X => (Pi.basisFun K ((DSRow n × DSCol m) ⊕ Fin p)).constr K
      (Sum.elim (fun e ↦ Pi.single (finSigmaFinEquiv e.1, (0 : Fin 1)) 1)
        (fun a ↦ ∑ k : Fin (n a + 1), Pi.single (finSigmaFinEquiv ⟨a, k⟩, (0 : Fin 1)) 1))
  | .Y => (Pi.basisFun K ((DSRow n × DSCol m) ⊕ Fin q)).constr K
      (Sum.elim (fun e ↦ Pi.single ((0 : Fin 1), finSigmaFinEquiv e.2) 1)
        (fun b ↦ ∑ l : Fin (m b + 1), Pi.single ((0 : Fin 1), finSigmaFinEquiv ⟨b, l⟩) 1))
  | .Z => (Pi.basisFun K ((DSRow n × DSCol m) ⊕ (Fin q × Fin p))).constr K
      (Sum.elim (fun e ↦ Pi.single (finSigmaFinEquiv e.2, finSigmaFinEquiv e.1) 1) (fun _ ↦ 0))

/-- The second family of leg maps: onto the slices, with Schönhage's correction terms. -/
noncomputable def dsG : ∀ c, CoordinateSpace K (DSIndex n m) c →ₗ[K] DSSliceSpace K n m c
  | .X => (Pi.basisFun K ((DSRow n × DSCol m) ⊕ Fin p)).constr K
      (Sum.elim (dsGX K n m) (fun _ ↦ 0))
  | .Y => (Pi.basisFun K ((DSRow n × DSCol m) ⊕ Fin q)).constr K
      (Sum.elim (dsGY K n m) (fun _ ↦ 0))
  | .Z => (Pi.basisFun K ((DSRow n × DSCol m) ⊕ (Fin q × Fin p))).constr K
      (Sum.elim (fun e ↦ dsSliceZ K n m (e.1.1, e.2.1))
        (fun ba ↦ -dsSliceZ K n m (ba.2, ba.1)))

/-- The first family restricts the source onto `⟨N,1,M⟩`. -/
theorem map_dsF_dsSource :
    Tensor.map (dsF K n m) (dsSource K n m) =
      matrixMultiplication (K := K) (∑ a, (n a + 1)) 1 (∑ b, (m b + 1)) := by
  classical
  rw [dsSource, map_add, map_sum, map_sum, matrixMultiplication_middle_one]
  have h2 : ∀ a : Fin p, Tensor.map (dsF K n m) (∑ b : Fin q, Tensor.pure (K := K)
      (ofLegs (V := CoordinateSpace K (DSIndex n m))
        (Pi.single (Sum.inr a) 1 : (DSRow n × DSCol m) ⊕ Fin p → K)
        (Pi.single (Sum.inr b) 1 : (DSRow n × DSCol m) ⊕ Fin q → K)
        (Pi.single (Sum.inr (b, a)) 1 : (DSRow n × DSCol m) ⊕ (Fin q × Fin p) → K))) = 0 := by
    intro a
    rw [map_sum]
    refine Finset.sum_eq_zero fun b _ ↦ ?_
    rw [map_pure_ofLegs]
    simp only [dsF, basisFun_constr_single, Sum.elim_inr]
    exact pure_ofLegs_zero_Z _ _
  rw [Finset.sum_congr rfl fun a _ ↦ h2 a, Finset.sum_const_zero, add_zero]
  rw [← Fintype.sum_prod_type',
    ← (Equiv.prodCongr (finSigmaFinEquiv (n := fun a ↦ n a + 1))
      (finSigmaFinEquiv (n := fun b ↦ m b + 1))).sum_comp]
  refine Finset.sum_congr rfl fun e _ ↦ ?_
  rw [map_pure_ofLegs]
  simp only [dsF, basisFun_constr_single, Sum.elim_inl]
  refine congrArg _ ?_
  funext c
  cases c <;> rfl

/-- The second family maps the source onto the slices. -/
theorem map_dsG_dsSource :
    Tensor.map (dsG K n m) (dsSource K n m) =
      ∑ ab : Fin p × Fin q, ∑ t : Fin (n ab.1 * m ab.2), Tensor.pure (K := K)
        (ofLegs (V := DSSliceSpace K n m)
          (dsSliceX K n m ab t) (dsSliceY K n m ab t) (dsSliceZ K n m ab)) := by
  classical
  rw [dsSource, map_add, map_sum, map_sum]
  have h2 : ∀ a : Fin p, Tensor.map (dsG K n m) (∑ b : Fin q, Tensor.pure (K := K)
      (ofLegs (V := CoordinateSpace K (DSIndex n m))
        (Pi.single (Sum.inr a) 1 : (DSRow n × DSCol m) ⊕ Fin p → K)
        (Pi.single (Sum.inr b) 1 : (DSRow n × DSCol m) ⊕ Fin q → K)
        (Pi.single (Sum.inr (b, a)) 1 : (DSRow n × DSCol m) ⊕ (Fin q × Fin p) → K))) = 0 := by
    intro a
    rw [map_sum]
    refine Finset.sum_eq_zero fun b _ ↦ ?_
    rw [map_pure_ofLegs]
    simp only [dsG, basisFun_constr_single, Sum.elim_inr]
    exact pure_ofLegs_zero_X _ _
  rw [Finset.sum_congr rfl fun a _ ↦ h2 a, Finset.sum_const_zero, add_zero]
  have h1 : ∀ e : DSRow n × DSCol m, Tensor.map (dsG K n m) (Tensor.pure (K := K)
      (ofLegs (V := CoordinateSpace K (DSIndex n m))
        (Pi.single (Sum.inl e) 1 : (DSRow n × DSCol m) ⊕ Fin p → K)
        (Pi.single (Sum.inl e) 1 : (DSRow n × DSCol m) ⊕ Fin q → K)
        (Pi.single (Sum.inl e) 1 : (DSRow n × DSCol m) ⊕ (Fin q × Fin p) → K))) =
      Tensor.pure (K := K) (ofLegs (V := DSSliceSpace K n m)
        (dsGX K n m e) (dsGY K n m e) (dsSliceZ K n m (e.1.1, e.2.1))) := by
    intro e
    rw [map_pure_ofLegs]
    simp only [dsG, basisFun_constr_single, Sum.elim_inl]
  rw [Finset.sum_congr rfl fun e _ ↦ h1 e, Fintype.sum_prod_type, Fintype.sum_prod_type]
  simp only [Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  rw [Fin.sum_univ_succ]
  have hzero : ∑ b : Fin q, ∑ l : Fin (m b + 1), Tensor.pure (K := K)
      (ofLegs (V := DSSliceSpace K n m) (dsGX K n m (⟨a, 0⟩, ⟨b, l⟩))
        (dsGY K n m (⟨a, 0⟩, ⟨b, l⟩)) (dsSliceZ K n m (a, b))) = 0 := by
    refine Finset.sum_eq_zero fun b _ ↦ Finset.sum_eq_zero fun l _ ↦ ?_
    have : dsGY K n m (⟨a, 0⟩, ⟨b, l⟩) = 0 := by simp [dsGY]
    rw [this]
    exact pure_ofLegs_zero_Y _ _
  rw [hzero, zero_add, Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ ↦ ?_
  rw [← (finProdFinEquiv (m := n a) (n := m b)).sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun k' _ ↦ ?_
  rw [Fin.sum_univ_succ]
  have hz : dsGX K n m (⟨a, k'.succ⟩, ⟨b, 0⟩) = 0 := by simp [dsGX]
  rw [hz, pure_ofLegs_zero_X, zero_add]
  refine Finset.sum_congr rfl fun l' _ ↦ ?_
  simp [dsGX, dsGY, dsA, dsB]

/-- The mixed block `(f, f, g)` annihilates the source: its unit part and its `⟨p,1,q⟩` part
cancel. -/
theorem map_dsF_dsF_dsG_dsSource :
    Tensor.map (ofLegs (V := fun c ↦ CoordinateSpace K (DSIndex n m) c →ₗ[K]
        MMSpace K (∑ a, (n a + 1)) 1 (∑ b, (m b + 1)) c × DSSliceSpace K n m c)
      (directSumLeftMaps (K := K) (DSSliceSpace K n m) (dsF K n m) .X)
      (directSumLeftMaps (K := K) (DSSliceSpace K n m) (dsF K n m) .Y)
      (directSumRightMaps (K := K) (MMSpace K (∑ a, (n a + 1)) 1 (∑ b, (m b + 1)))
        (dsG K n m) .Z)) (dsSource K n m) = 0 := by
  classical
  rw [dsSource, map_add, map_sum, map_sum]
  simp only [map_sum, map_pure_ofLegs]
  simp only [ofLegs, directSumLeftMaps, directSumRightMaps, LinearMap.comp_apply, dsF, dsG,
    basisFun_constr_single, Sum.elim_inl, Sum.elim_inr, map_sum, map_neg]
  simp only [pure_ofLegs_sum_X, pure_ofLegs_sum_Y, pure_ofLegs_neg_Z, Finset.sum_neg_distrib]
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_sigma]
  rw [add_neg_eq_zero]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ ↦ ?_
  rw [Finset.sum_comm]

/-- The mixed block `(g, f, g)` annihilates the source, because every column sum of the `X`-leg
correction vectors vanishes. -/
theorem map_dsG_dsF_dsG_dsSource :
    Tensor.map (ofLegs (V := fun c ↦ CoordinateSpace K (DSIndex n m) c →ₗ[K]
        MMSpace K (∑ a, (n a + 1)) 1 (∑ b, (m b + 1)) c × DSSliceSpace K n m c)
      (directSumRightMaps (K := K) (MMSpace K (∑ a, (n a + 1)) 1 (∑ b, (m b + 1)))
        (dsG K n m) .X)
      (directSumLeftMaps (K := K) (DSSliceSpace K n m) (dsF K n m) .Y)
      (directSumRightMaps (K := K) (MMSpace K (∑ a, (n a + 1)) 1 (∑ b, (m b + 1)))
        (dsG K n m) .Z)) (dsSource K n m) = 0 := by
  classical
  rw [dsSource, map_add, map_sum, map_sum]
  simp only [map_sum, map_pure_ofLegs]
  simp only [ofLegs, directSumLeftMaps, directSumRightMaps, LinearMap.comp_apply, dsF, dsG,
    basisFun_constr_single, Sum.elim_inl, Sum.elim_inr, map_zero, pure_ofLegs_zero_X,
    Finset.sum_const_zero, add_zero]
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_sigma]
  refine Finset.sum_eq_zero fun a _ ↦ ?_
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun b _ ↦ ?_
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun l _ ↦ ?_
  rw [← pure_ofLegs_sum_X, ← map_sum]
  have hsum : ∑ k : Fin (n a + 1), dsGX K n m (⟨a, k⟩, ⟨b, l⟩) = 0 := by
    induction l using Fin.cases with
    | zero => simp [dsGX]
    | succ l' => simpa [dsGX] using sum_dsA K n m a b l'
  rw [hsum, map_zero]
  exact pure_ofLegs_zero_X _ _

/-- The mixed block `(f, g, g)` annihilates the source, because every row sum of the `Y`-leg
correction vectors vanishes. -/
theorem map_dsF_dsG_dsG_dsSource :
    Tensor.map (ofLegs (V := fun c ↦ CoordinateSpace K (DSIndex n m) c →ₗ[K]
        MMSpace K (∑ a, (n a + 1)) 1 (∑ b, (m b + 1)) c × DSSliceSpace K n m c)
      (directSumLeftMaps (K := K) (DSSliceSpace K n m) (dsF K n m) .X)
      (directSumRightMaps (K := K) (MMSpace K (∑ a, (n a + 1)) 1 (∑ b, (m b + 1)))
        (dsG K n m) .Y)
      (directSumRightMaps (K := K) (MMSpace K (∑ a, (n a + 1)) 1 (∑ b, (m b + 1)))
        (dsG K n m) .Z)) (dsSource K n m) = 0 := by
  classical
  rw [dsSource, map_add, map_sum, map_sum]
  simp only [map_sum, map_pure_ofLegs]
  simp only [ofLegs, directSumLeftMaps, directSumRightMaps, LinearMap.comp_apply, dsF, dsG,
    basisFun_constr_single, Sum.elim_inl, Sum.elim_inr, map_zero, pure_ofLegs_zero_Y,
    Finset.sum_const_zero, add_zero]
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_sigma]
  refine Finset.sum_eq_zero fun a _ ↦ Finset.sum_eq_zero fun k _ ↦
    Finset.sum_eq_zero fun b _ ↦ ?_
  rw [← pure_ofLegs_sum_Y, ← map_sum]
  have hsum : ∑ l : Fin (m b + 1), dsGY K n m (⟨a, k⟩, ⟨b, l⟩) = 0 := by
    induction k using Fin.cases with
    | zero => simp [dsGY]
    | succ k' => simpa [dsGY] using sum_dsB K n m a b k'
  rw [hsum, map_zero]
  exact pure_ofLegs_zero_Y _ _

/-- **The direct-sum identity in standard coordinates.** -/
theorem polynomialDegenerates_dsSource :
    PolynomialDegenerates (dsSource K n m)
      (Tensor.directSum (matrixMultiplication (K := K) (∑ a, (n a + 1)) 1 (∑ b, (m b + 1)))
        (matrixMultiplicationDirectSum K (fun _ : Fin p × Fin q ↦ 1) (fun ab ↦ n ab.1 * m ab.2)
          (fun _ ↦ 1))) := by
  have h := polynomialDegenerates_directSum_of_mixed_map_eq_zero (dsF K n m) (dsG K n m)
    (map_dsF_dsF_dsG_dsSource K n m) (map_dsG_dsF_dsG_dsSource K n m)
    (map_dsF_dsG_dsG_dsSource K n m)
  rw [map_dsF_dsSource, map_dsG_dsSource, ← oneSliceDirectSum_eq_sum_dsSlice] at h
  exact h

end Core

/-! ### The indexed-direct-sum presentation -/

section Presentation

variable (K : Type u) [Field K] {p q : ℕ} (n : Fin p → ℕ) (m : Fin q → ℕ)

/-- The (row, column) pair of the `i`-th diagonal coordinate of `⟨N·M⟩`. -/
def dsUnitIndex : Fin ((∑ a, (n a + 1)) * ∑ b, (m b + 1)) ≃ DSRow n × DSCol m :=
  finProdFinEquiv.symm.trans
    (Equiv.prodCongr (finSigmaFinEquiv (n := fun a ↦ n a + 1)).symm
      (finSigmaFinEquiv (n := fun b ↦ m b + 1)).symm)

/-- The `i`-th summand `⟨1,1,1⟩` of `⟨N·M⟩` goes to its (row, column) coordinate on every leg. -/
noncomputable def dsUnitToSource (i : Fin ((∑ a, (n a + 1)) * ∑ b, (m b + 1))) :
    ∀ c, MMSpace K 1 1 1 c →ₗ[K] CoordinateSpace K (DSIndex n m) c
  | .X => (LinearMap.proj (R := K) (φ := fun _ : Fin 1 × Fin 1 ↦ K) (0, 0)).smulRight
      (Pi.single (Sum.inl (dsUnitIndex n m i)) 1 : (DSRow n × DSCol m) ⊕ Fin p → K)
  | .Y => (LinearMap.proj (R := K) (φ := fun _ : Fin 1 × Fin 1 ↦ K) (0, 0)).smulRight
      (Pi.single (Sum.inl (dsUnitIndex n m i)) 1 : (DSRow n × DSCol m) ⊕ Fin q → K)
  | .Z => (LinearMap.proj (R := K) (φ := fun _ : Fin 1 × Fin 1 ↦ K) (0, 0)).smulRight
      (Pi.single (Sum.inl (dsUnitIndex n m i)) 1 : (DSRow n × DSCol m) ⊕ (Fin q × Fin p) → K)

/-- `⟨p,1,q⟩` goes to the second block of coordinates on every leg. -/
noncomputable def dsMMToSource :
    ∀ c, MMSpace K p 1 q c →ₗ[K] CoordinateSpace K (DSIndex n m) c
  | .X => (Pi.basisFun K (Fin p × Fin 1)).constr K
      (fun ai ↦ (Pi.single (Sum.inr ai.1) 1 : (DSRow n × DSCol m) ⊕ Fin p → K))
  | .Y => (Pi.basisFun K (Fin 1 × Fin q)).constr K
      (fun jb ↦ (Pi.single (Sum.inr jb.2) 1 : (DSRow n × DSCol m) ⊕ Fin q → K))
  | .Z => (Pi.basisFun K (Fin q × Fin p)).constr K
      (fun ba ↦ (Pi.single (Sum.inr ba) 1 : (DSRow n × DSCol m) ⊕ (Fin q × Fin p) → K))

/-- The indexed-direct-sum presentation of `⟨N·M⟩ ⊕ ⟨p,1,q⟩` restricts onto the source in standard
coordinates. -/
theorem restricts_directSum_dsSource :
    Restricts
      (Tensor.directSum
        (matrixMultiplicationDirectSum K (ι := Fin ((∑ a, (n a + 1)) * ∑ b, (m b + 1)))
          (fun _ ↦ 1) (fun _ ↦ 1) (fun _ ↦ 1))
        (matrixMultiplication (K := K) p 1 q))
      (dsSource K n m) := by
  classical
  let FU := indexedFoldMap (K := K)
    (V := fun _ : Fin ((∑ a, (n a + 1)) * ∑ b, (m b + 1)) ↦ MMSpace K 1 1 1)
    (fun i c ↦ dsUnitToSource K n m i c)
  refine ⟨fun c ↦ LinearMap.coprod (FU c) (dsMMToSource K n m c), ?_⟩
  have hL : ∀ X : Tensor3 K (MMDirectSumSpace K
        (ι := Fin ((∑ a, (n a + 1)) * ∑ b, (m b + 1))) (fun _ ↦ 1) (fun _ ↦ 1) (fun _ ↦ 1)),
      Tensor.map (fun c ↦ LinearMap.coprod (FU c) (dsMMToSource K n m c))
        (Tensor.map (Tensor.includeLeft (K := K) (W := MMSpace K p 1 q)) X) =
        Tensor.map FU X := by
    intro X
    rw [← LinearMap.comp_apply, ← Tensor.map_comp]
    refine congrArg (fun G ↦ Tensor.map G X) (funext fun c ↦ LinearMap.ext fun x ↦ ?_)
    simp
  have hR : ∀ X : Tensor3 K (MMSpace K p 1 q),
      Tensor.map (fun c ↦ LinearMap.coprod (FU c) (dsMMToSource K n m c))
        (Tensor.map (Tensor.includeRight (K := K)
          (V := MMDirectSumSpace K (ι := Fin ((∑ a, (n a + 1)) * ∑ b, (m b + 1)))
            (fun _ ↦ 1) (fun _ ↦ 1) (fun _ ↦ 1))) X) =
        Tensor.map (dsMMToSource K n m) X := by
    intro X
    rw [← LinearMap.comp_apply, ← Tensor.map_comp]
    refine congrArg (fun G ↦ Tensor.map G X) (funext fun c ↦ LinearMap.ext fun x ↦ ?_)
    simp
  rw [Tensor.directSum, map_add, hL, hR, matrixMultiplicationDirectSum,
    map_indexedFoldMap_indexedDirectSum, dsSource]
  congr 1
  · rw [← (dsUnitIndex n m).sum_comp]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [matrixMultiplication_outer_one, Fin.sum_univ_one, Tensor.map_pure]
    refine congrArg _ ?_
    funext c
    cases c <;> simp [dsUnitToSource, mmTerm]
  · rw [matrixMultiplication_middle_one, map_sum]
    refine Finset.sum_congr rfl fun a _ ↦ ?_
    rw [map_sum]
    refine Finset.sum_congr rfl fun b _ ↦ ?_
    rw [Tensor.map_pure]
    refine congrArg _ ?_
    funext c
    cases c <;> simp [dsMMToSource, mmTerm]

/-- **The Alman–Li direct-sum identity** ([AlmanLi2026], Theorem 7.3, p. 29).

For block sizes `n α + 1` (`α < p`) and `m β + 1` (`β < q`), with `N = ∑ (n α + 1)` and
`M = ∑ (m β + 1)`,

```text
⟨N·M⟩ ⊕ ⟨p,1,q⟩   ⊵   ⟨N,1,M⟩ ⊕ ⊕_{α,β} ⟨1, n α · m β, 1⟩.
```

At `p = q = 1` this is Schönhage's identity `⟨n,1,m⟩ ⊕ ⟨1,(n−1)(m−1),1⟩ ⊴ ⟨nm + 1⟩`
([Schonhage1981], Lemma 6.1). -/
theorem polynomialDegenerates_unit_directSum_matrixMultiplication :
    PolynomialDegenerates
      (Tensor.directSum
        (matrixMultiplicationDirectSum K (ι := Fin ((∑ a, (n a + 1)) * ∑ b, (m b + 1)))
          (fun _ ↦ 1) (fun _ ↦ 1) (fun _ ↦ 1))
        (matrixMultiplication (K := K) p 1 q))
      (Tensor.directSum (matrixMultiplication (K := K) (∑ a, (n a + 1)) 1 (∑ b, (m b + 1)))
        (matrixMultiplicationDirectSum K (fun _ : Fin p × Fin q ↦ 1) (fun ab ↦ n ab.1 * m ab.2)
          (fun _ ↦ 1))) :=
  (PolynomialDegenerates.of_restricts (restricts_directSum_dsSource K n m)).trans
    (polynomialDegenerates_dsSource K n m)

end Presentation

end AlgebraicComplexity
