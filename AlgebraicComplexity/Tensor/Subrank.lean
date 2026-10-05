/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Tensor.Coordinates
import AlgebraicComplexity.Tensor.Power
import AlgebraicComplexity.Tensor.PowerCoherence
import AlgebraicComplexity.Tensor.Product
import AlgebraicComplexity.Tensor.SliceRank

/-!
# Diagonal tensors and the subrank

The *subrank* `subrank T` of a three-legged tensor is the largest `m` for which `T` restricts onto
the diagonal tensor `diagonalTensor K (Fin m)` --- the tensor `⟨m⟩ = ∑ i, e_i ⊗ e_i ⊗ e_i`.  It is
the standard supermultiplicative companion of tensor rank, and it is the invariant that Tao's
slice-rank method bounds.

The module has two halves.

* **Diagonal tensors.**  `diagonalTensor_fin_zero` and `diagonalTensor_fin_one` evaluate the two
  degenerate cases, `Isomorphic.diagonalTensor_congr` reindexes the index type, and the product law
  `Isomorphic.external_diagonalTensor : diag ι ⊠ diag κ ≅ diag (ι × κ)` is proved from the
  coordinate identification `(ι → K) ⊗ (κ → K) ≃ (ι × κ → K)` of `Tensor/Coordinates.lean`.  Its two
  corollaries, `Restricts.external_diagonalTensor` and `Restricts.power_diagonalTensor`, propagate
  diagonal restrictions through external products and canonical tensor powers.
* **The subrank.**  `diagonalRestrictionSet T` is the set of diagonal sizes onto which `T`
  restricts and `subrank T` its supremum.  Over a field the set is bounded above by the slice rank
  (`card_le_sliceRank_of_restricts_diagonalTensor` of `Tensor/SliceRank.lean`), so the supremum is
  attained (`restricts_diagonalTensor_subrank`); the comparison chain `subrank ≤ sliceRank ≤ rank`,
  monotonicity under restriction, and supermultiplicativity
  `subrank T * subrank S ≤ subrank (T ⊠ S)` follow.

Everything here is finite tensor algebra: no limits and no real analysis.  The asymptotic subrank
`lim_n subrank (T^{⊗n})^{1/n}` is built on top of this module in
`Tensor/AsymptoticInvariant.lean`, which is also where `subrank` is packaged as a `NatInvariant`.

## References

* T. Tao, *A symmetric formulation of the Croot-Lev-Pach-Ellenberg-Gijswijt capset bound*, blog
  post, 2016.
* V. Strassen, *Relative bilinear complexity and matrix multiplication*, J. reine angew. Math.
  375/376 (1987), 406--443.
-/

namespace AlgebraicComplexity.Tensor

universe u v w

/-! ## Diagonal tensors and their product law -/

section Diagonal

variable {K : Type u} [CommSemiring K]
variable {V : Leg → Type v} [∀ c, AddCommMonoid (V c)] [∀ c, Module K (V c)]
variable {W : Leg → Type w} [∀ c, AddCommMonoid (W c)] [∀ c, Module K (W c)]

/-- The empty diagonal tensor is zero. -/
theorem diagonalTensor_fin_zero : diagonalTensor K (Fin 0) = 0 := by
  simp [diagonalTensor]

/-- The diagonal tensor of size one is the pure tensor of the single standard basis vector. -/
theorem diagonalTensor_fin_one :
    diagonalTensor K (Fin 1) = pure (K := K) (fun _ : Leg ↦ (Pi.single 0 1 : Fin 1 → K)) := by
  simp [diagonalTensor]

/-- Every zeroth tensor power restricts onto the diagonal tensor of size one.

Proof sketch: the zeroth power is the pure tensor of scalar units, and each leg
`PowerSpace K V 0 c` is canonically the base ring through `PiTensorProduct.isEmptyEquiv`; composing
that identification with `1 ↦ e₀` sends the unit to the single standard basis vector. -/
theorem restricts_power_zero_diagonalTensor (T : Tensor3 K V) :
    Restricts (power T 0) (diagonalTensor K (Fin 1)) := by
  refine ⟨fun c ↦ (LinearMap.toSpanSingleton K (Fin 1 → K) (Pi.single 0 1)).comp
    (PiTensorProduct.isEmptyEquiv (Fin 0) (s := fun _ : Fin 0 ↦ V c)).toLinearMap, ?_⟩
  rw [power_zero, map_pure, diagonalTensor_fin_one]
  congr 1
  funext c
  simp [powerUnit, LinearMap.toSpanSingleton]

/-- Diagonal tensors of equivalent finite index types are legwise isomorphic.

Proof sketch: reindexing coordinate functions by `e` is a linear equivalence on every leg, it
carries the standard basis vector `e_i` to `e_{e i}`, and the defining sum is reindexed by `e`. -/
theorem Isomorphic.diagonalTensor_congr {ι : Type v} [Fintype ι] [DecidableEq ι]
    {ι' : Type w} [Fintype ι'] [DecidableEq ι'] (e : ι ≃ ι') :
    Isomorphic (diagonalTensor K ι) (diagonalTensor K ι') := by
  refine (Isomorphic.map _ (fun _ ↦ LinearEquiv.funCongrLeft K K e.symm)).trans
    (Isomorphic.of_eq ?_)
  rw [diagonalTensor, map_sum]
  simp only [Tensor.map_pure, LinearEquiv.coe_coe, funCongrLeft_symm_single]
  rw [diagonalTensor]
  exact Fintype.sum_equiv e _ _ fun _ ↦ rfl

/-- **The diagonal product law.**  The external product of two diagonal tensors is the diagonal
tensor on the product index type.  The source is `diag ι ⊠ diag κ`, whose legs are binary tensor
products of coordinate spaces, and the target is `diag (ι × κ)`.

Proof sketch: bilinearity expands the external product into the double sum of pure tensors
`e_i ⊗ e_j` on all three legs; the coordinate identification
`coordinateTensorEquiv : (ι → K) ⊗ (κ → K) ≃ (ι × κ → K)` sends `e_i ⊗ e_j` to `e_{(i,j)}`, so the
double sum becomes the diagonal sum over `ι × κ`. -/
theorem Isomorphic.external_diagonalTensor (ι : Type v) [Fintype ι] [DecidableEq ι]
    (κ : Type w) [Fintype κ] [DecidableEq κ] :
    Isomorphic (Tensor.external (diagonalTensor K ι) (diagonalTensor K κ))
      (diagonalTensor K (ι × κ)) := by
  refine (Isomorphic.map _ (fun _ ↦ coordinateTensorEquiv (K := K) (α := ι) (β := κ))).trans
    (Isomorphic.of_eq ?_)
  have hexpand : Tensor.external (diagonalTensor K ι) (diagonalTensor K κ)
      = ∑ i : ι, ∑ j : κ, pure (K := K)
        (fun _ : Leg ↦ (Pi.single i 1 : ι → K) ⊗ₜ[K] (Pi.single j 1 : κ → K)) := by
    unfold diagonalTensor
    rw [external_sum_sum]
    simp only [external_pure]
  rw [hexpand]
  simp only [map_sum, Tensor.map_pure, LinearEquiv.coe_coe,
    coordinateTensorEquiv_single_tmul_single]
  rw [diagonalTensor, Fintype.sum_prod_type]

/-- Diagonal restrictions multiply: if `T` restricts onto the diagonal of size `a` and `S` onto the
diagonal of size `b`, then `T ⊠ S` restricts onto the diagonal of size `a * b`. -/
theorem Restricts.external_diagonalTensor {a b : ℕ} {T : Tensor3 K V} {S : Tensor3 K W}
    (hT : Restricts T (diagonalTensor K (Fin a))) (hS : Restricts S (diagonalTensor K (Fin b))) :
    Restricts (Tensor.external T S) (diagonalTensor K (Fin (a * b))) :=
  (hT.external hS).trans
    ((Isomorphic.external_diagonalTensor (K := K) (Fin a) (Fin b)).trans
      (Isomorphic.diagonalTensor_congr finProdFinEquiv)).restricts

/-- Diagonal restrictions raise to canonical tensor powers: if `T` restricts onto the diagonal of
size `a`, then `T^{⊗n}` restricts onto the diagonal of size `a ^ n`.

Proof sketch: induction on `n`.  The base case is `restricts_power_zero_diagonalTensor`, and the
inductive step splits `T^{⊗(n+1)}` as `T^{⊗n} ⊠ T^{⊗1}` through `isomorphic_external_power` and
applies `Restricts.external_diagonalTensor`. -/
theorem Restricts.power_diagonalTensor {a : ℕ} {T : Tensor3 K V}
    (h : Restricts T (diagonalTensor K (Fin a))) (n : ℕ) :
    Restricts (Tensor.power T n) (diagonalTensor K (Fin (a ^ n))) := by
  induction n with
  | zero =>
      rw [pow_zero]
      exact restricts_power_zero_diagonalTensor T
  | succ n ih =>
      have hfirst : Restricts (Tensor.power T 1) (diagonalTensor K (Fin a)) := by
        refine Restricts.trans ?_ h
        rw [power_one_eq_powerOne]
        exact (Isomorphic.powerOneTransport T).symm.restricts
      rw [pow_succ]
      exact (isomorphic_external_power T n 1).symm.restricts.trans
        (ih.external_diagonalTensor hfirst)

/-! ### Diagonal-restriction subrank -/

/-- The set of diagonal sizes onto which `T` restricts.  Its supremum is the subrank of `T`. -/
def diagonalRestrictionSet (T : Tensor3 K V) : Set ℕ :=
  {m | Restricts T (diagonalTensor K (Fin m))}

/-- Membership in the diagonal-restriction set is exactly a restriction onto a diagonal tensor. -/
theorem mem_diagonalRestrictionSet_iff {T : Tensor3 K V} {m : ℕ} :
    m ∈ diagonalRestrictionSet T ↔ Restricts T (diagonalTensor K (Fin m)) := Iff.rfl

/-- Every tensor restricts onto the empty diagonal, so the diagonal-restriction set is nonempty. -/
theorem zero_mem_diagonalRestrictionSet (T : Tensor3 K V) : 0 ∈ diagonalRestrictionSet T := by
  rw [mem_diagonalRestrictionSet_iff, diagonalTensor_fin_zero]
  exact Restricts.zeroTarget T

/-- The diagonal-restriction subrank of `T`: the largest `m` such that `T` restricts onto the
diagonal tensor over `Fin m`.  Over a field the supremum is attained
(`restricts_diagonalTensor_subrank`); over a general commutative semiring the defining set need not
be bounded and the natural-number supremum then returns its junk value `0`. -/
noncomputable def subrank (T : Tensor3 K V) : ℕ := sSup (diagonalRestrictionSet T)

end Diagonal

/-! ## The subrank over a field

Over a field, Tao's slice-rank bound for restrictions onto diagonal tensors bounds the
diagonal-restriction set, which makes the supremum defining `subrank` attained and turns the
diagonal product law into supermultiplicativity under external products. -/

section Subrank

variable {K : Type u} [Field K]
variable {V : Leg → Type v} [∀ c, AddCommMonoid (V c)] [∀ c, Module K (V c)]
variable {W : Leg → Type w} [∀ c, AddCommMonoid (W c)] [∀ c, Module K (W c)]

/-- Tao's diagonal bound: a restriction onto the diagonal of size `m` forces `m ≤ sliceRank T`. -/
theorem le_sliceRank_of_mem_diagonalRestrictionSet {T : Tensor3 K V} {m : ℕ}
    (h : m ∈ diagonalRestrictionSet T) : m ≤ sliceRank T := by
  simpa using card_le_sliceRank_of_restricts_diagonalTensor (ι := Fin m) h

/-- Over a field the diagonal-restriction set is bounded above by the slice rank. -/
theorem bddAbove_diagonalRestrictionSet (T : Tensor3 K V) :
    BddAbove (diagonalRestrictionSet T) :=
  ⟨sliceRank T, fun _ hm ↦ le_sliceRank_of_mem_diagonalRestrictionSet hm⟩

/-- The subrank is attained: `T` really does restrict onto the diagonal tensor of size
`subrank T`.  This is where the field hypothesis enters, through boundedness of the
diagonal-restriction set. -/
theorem restricts_diagonalTensor_subrank (T : Tensor3 K V) :
    Restricts T (diagonalTensor K (Fin (subrank T))) :=
  Nat.sSup_mem ⟨0, zero_mem_diagonalRestrictionSet T⟩ (bddAbove_diagonalRestrictionSet T)

/-- Any restriction onto a diagonal tensor bounds the subrank from below. -/
theorem le_subrank_of_restricts {T : Tensor3 K V} {m : ℕ}
    (h : Restricts T (diagonalTensor K (Fin m))) : m ≤ subrank T :=
  le_csSup (bddAbove_diagonalRestrictionSet T) h

/-- Subrank is bounded by slice rank. -/
theorem subrank_le_sliceRank (T : Tensor3 K V) : subrank T ≤ sliceRank T :=
  le_sliceRank_of_mem_diagonalRestrictionSet (restricts_diagonalTensor_subrank T)

/-- Subrank is bounded by ordinary tensor rank. -/
theorem subrank_le_rank (T : Tensor3 K V) : subrank T ≤ rank T :=
  (subrank_le_sliceRank T).trans (sliceRank_le_rank T)

/-- Subrank decreases along exact restriction: the source `T` has the larger subrank. -/
theorem subrank_restricts_le {T : Tensor3 K V} {S : Tensor3 K W} (h : Restricts T S) :
    subrank S ≤ subrank T :=
  le_subrank_of_restricts (h.trans (restricts_diagonalTensor_subrank S))

/-- Legwise isomorphic tensors have the same subrank. -/
theorem subrank_isomorphic {T : Tensor3 K V} {S : Tensor3 K W} (h : Isomorphic T S) :
    subrank T = subrank S :=
  le_antisymm (subrank_restricts_le h.symm.restricts) (subrank_restricts_le h.restricts)

/-- **Supermultiplicativity of subrank.**  `subrank T * subrank S ≤ subrank (T ⊠ S)`.

Proof sketch: both subranks are attained, and the diagonal product law turns the external product
of the two witnessing diagonal restrictions into a restriction onto the diagonal of size
`subrank T * subrank S`. -/
theorem subrank_mul_le_subrank_external (T : Tensor3 K V) (S : Tensor3 K W) :
    subrank T * subrank S ≤ subrank (Tensor.external T S) :=
  le_subrank_of_restricts
    ((restricts_diagonalTensor_subrank T).external_diagonalTensor
      (restricts_diagonalTensor_subrank S))

end Subrank

end AlgebraicComplexity.Tensor
