/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.TauValueDirectSum
import AlgebraicComplexity.Tensor.IndexedDegeneration

/-!
# Weights add over an indexed direct sum of *different* summands

Layer 3 (`AlgebraicComplexity/MatrixMultiplication/`).
`MatrixMultiplication/AsymmetricGlobalValue.lean` proves `HasTauWeight.indexedDirectSum_const`,
where all summands are the same tensor and therefore share one displayed leading degree.  A laser
stage whose cleanup keeps *whole constituents* produces summands that differ, and no common degree
is available.

`HasTauWeight.indexedDirectSum` supplies the general law.  The degree synchronization it needs is
already committed: `Tensor.PolynomialDegenerates.indexedDirectSum` dilates each component
certificate to the product of the component degrees.  The rest of the proof mirrors the constant
case --- flatten the nested matrix-multiplication families with
`Isomorphic.indexedDirectSum_sigma`, reindex by `Fintype.equivFin`, and read the volume sum as a
double sum.

`HasTauWeight.map_linearEquiv` records that a weight survives a legwise change of coordinates;
this is what lets a weight be transported through the dependent casts that leg permutations of a
partitioned tensor introduce.
-/

namespace AlgebraicComplexity

open Tensor
open scoped BigOperators

universe u v w

section Map

variable {K : Type u} [CommSemiring K]
variable {V : Leg → Type v} [∀ c, AddCommMonoid (V c)] [∀ c, Module K (V c)]
variable {W : Leg → Type v} [∀ c, AddCommMonoid (W c)] [∀ c, Module K (W c)]

/-- A weight survives a legwise change of coordinates: the inverse equivalence is a legwise
restriction back to the source. -/
theorem HasTauWeight.map_linearEquiv {X : Tensor3 K V} {τ value : ℝ}
    (f : ∀ c, V c ≃ₗ[K] W c) (h : HasTauWeight K X τ value) :
    HasTauWeight K (Tensor.map (fun c ↦ (f c).toLinearMap) X) τ value := by
  refine h.of_restricts ⟨fun c ↦ (f c).symm.toLinearMap, ?_⟩
  change (Tensor.map (fun c ↦ (f c).symm.toLinearMap) ∘ₗ
    Tensor.map (fun c ↦ (f c).toLinearMap)) X = X
  rw [← Tensor.map_comp]
  have hid : (fun c ↦ (f c).symm.toLinearMap ∘ₗ (f c).toLinearMap) =
      fun c ↦ (LinearMap.id : V c →ₗ[K] V c) := by
    funext c
    exact LinearMap.ext fun x ↦ (f c).symm_apply_apply x
  rw [hid]
  simp

end Map

section IndexedWeight

variable {K : Type u} [CommSemiring K]
variable {ι : Type w} [Fintype ι] [DecidableEq ι]
variable {U : ι → Leg → Type v}
variable [∀ i c, AddCommMonoid (U i c)] [∀ i c, Module K (U i c)]

/-- **Weights add over an indexed direct sum of arbitrary summands.**

The general form of `HasTauWeight.indexedDirectSum_const`: the summands need not agree, and their
polynomial degenerations need not display a common degree.
`Tensor.PolynomialDegenerates.indexedDirectSum` performs the synchronization.

This is what a cleanup that retains *whole constituents* needs: it produces one summand per
retained address, and those constituents genuinely differ. -/
theorem HasTauWeight.indexedDirectSum
    {X : ∀ i, Tensor3 K (U i)} {τ : ℝ} {value : ι → ℝ}
    (h : ∀ i, HasTauWeight K (X i) τ (value i)) :
    HasTauWeight K (Tensor.indexedDirectSum X) τ (∑ i, value i) := by
  classical
  choose copies xs ys zs hx hy hz hdeg hval using h
  let J : Type _ := Σ i : ι, Fin (copies i)
  let e : J ≃ Fin (Fintype.card J) := Fintype.equivFin J
  let MMFamily : ∀ i : ι, Fin (copies i) → Leg → Type u :=
    fun i k ↦ MMSpace K (xs i k) (ys i k) (zs i k)
  let MM : ∀ ij : J, Tensor3 K (MMFamily ij.1 ij.2) :=
    fun ij ↦ matrixMultiplication (K := K) (xs ij.1 ij.2) (ys ij.1 ij.2) (zs ij.1 ij.2)
  let xSize : Fin (Fintype.card J) → ℕ := fun j ↦ xs (e.symm j).1 (e.symm j).2
  let ySize : Fin (Fintype.card J) → ℕ := fun j ↦ ys (e.symm j).1 (e.symm j).2
  let zSize : Fin (Fintype.card J) → ℕ := fun j ↦ zs (e.symm j).1 (e.symm j).2
  have hnested : PolynomialDegenerates (Tensor.indexedDirectSum X)
      (Tensor.indexedDirectSum fun i : ι ↦
        Tensor.indexedDirectSum fun k : Fin (copies i) ↦ MM ⟨i, k⟩) :=
    Tensor.PolynomialDegenerates.indexedDirectSum fun i ↦ hdeg i
  have hflatten : Restricts
      (Tensor.indexedDirectSum fun i : ι ↦
        Tensor.indexedDirectSum fun k : Fin (copies i) ↦ MM ⟨i, k⟩)
      (Tensor.indexedDirectSum MM) :=
    (Tensor.Isomorphic.indexedDirectSum_sigma (S := MMFamily) MM).symm.restricts
  have hreindex : Restricts (Tensor.indexedDirectSum MM)
      (matrixMultiplicationDirectSum K xSize ySize zSize) := by
    unfold matrixMultiplicationDirectSum
    apply Tensor.Restricts.indexedDirectSum_equiv e
    intro ij
    apply Tensor.Isomorphic.restricts
    change Tensor.Isomorphic (MM ij) (MM (e.symm (e ij)))
    rw [e.symm_apply_apply]
    exact Tensor.Isomorphic.refl (MM ij)
  have hsum : matrixMultiplicationVolumePowerSum xSize ySize zSize τ =
      ∑ i : ι, matrixMultiplicationVolumePowerSum (xs i) (ys i) (zs i) τ := by
    unfold matrixMultiplicationVolumePowerSum matrixMultiplicationVolume
    have hstep : ∑ j : Fin (Fintype.card J),
        ((xs (e.symm j).1 (e.symm j).2 * ys (e.symm j).1 (e.symm j).2 *
          zs (e.symm j).1 (e.symm j).2 : ℕ) : ℝ) ^ τ =
          ∑ ij : J, ((xs ij.1 ij.2 * ys ij.1 ij.2 * zs ij.1 ij.2 : ℕ) : ℝ) ^ τ :=
      Equiv.sum_comp e.symm
        fun ij : J ↦ ((xs ij.1 ij.2 * ys ij.1 ij.2 * zs ij.1 ij.2 : ℕ) : ℝ) ^ τ
    rw [hstep, Fintype.sum_sigma]
  exact ⟨Fintype.card J, xSize, ySize, zSize,
    fun j ↦ hx _ _, fun j ↦ hy _ _, fun j ↦ hz _ _,
    hnested.trans (PolynomialDegenerates.of_restricts (hflatten.trans hreindex)),
    by rw [hsum]; exact Finset.sum_le_sum fun i _ ↦ hval i⟩

/-- **A uniform lower bound on the summands gives `card * bound`.**  This is the form a laser
stage uses: every retained constituent is worth at least the leaf rate, and the number of them is
the retained copy count. -/
theorem HasTauWeight.indexedDirectSum_of_forall
    {X : ∀ i, Tensor3 K (U i)} {τ bound : ℝ}
    (h : ∀ i, HasTauWeight K (X i) τ bound) :
    HasTauWeight K (Tensor.indexedDirectSum X) τ ((Fintype.card ι : ℝ) * bound) := by
  have hsum := HasTauWeight.indexedDirectSum (value := fun _ : ι ↦ bound) h
  rwa [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hsum

end IndexedWeight

end AlgebraicComplexity
