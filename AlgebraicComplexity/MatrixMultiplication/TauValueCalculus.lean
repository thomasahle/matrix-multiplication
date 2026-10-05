/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.ExternalProduct
import AlgebraicComplexity.MatrixMultiplication.TauValueCore
import AlgebraicComplexity.Tensor.IndexedProduct
import AlgebraicComplexity.Tensor.PositiveExternalPower

/-!
# Supermultiplicativity of the `τ`-value under tensor products

Layer 3 (`AlgebraicComplexity/MatrixMultiplication/`).  Companion to
`MatrixMultiplication/TauValueCore.lean`, split off from the finite certificate definitions to
keep the structural product calculus independently importable.  It proves the
first of the three laws recorded by

> D. Coppersmith and S. Winograd, *Matrix multiplication via arithmetic progressions*,
> J. Symbolic Computation 9 (1990), 251-280, **Section 8, page 264**
> (`[CoppersmithWinograd1990]`),

namely `V_τ(A ⊗ B) ≥ V_τ(A) × V_τ(B)`, in the form available without a power-of-a-direct-sum
expansion: two extractions of the **same** power `N` of `A` and of `B` combine into one extraction
of `(A ⊗ B)^{⊗N}` whose weight is the product of the two weights.

The common-length hypothesis is a genuine restriction of the statement, not of the proof.  It is
removed in `MatrixMultiplication/TauValueDirectSum.lean`, which raises two certificates of
arbitrary lengths `N₁` and `N₂` to the common length `N₁N₂` without changing their weights and
proves the supremum-level law `mul_tauValue_le_tauValue_external`.

## Principal results

* `restricts_external_matrixMultiplicationDirectSum` — the external product of two finite
  matrix-multiplication direct sums restricts onto the Cartesian family of pairwise products,
  reindexed by the numerical copy index `Fin (F₁ * F₂)`.
* `TauValueCertificate.externalOfDegenerates`, `TauValueCertificate.term_externalOfDegenerates` —
  the combined certificate and its weight.
* `mul_tauValueTerm_le_tauValue_external` — the supremum-level reading
  `V_τ(A) · V_τ(B) ≤ V_τ(A ⊗ B)` for equal-length extractions.  The length-free form is
  `AlgebraicComplexity.mul_tauValue_le_tauValue_external` in
  `MatrixMultiplication/TauValueDirectSum.lean`.
-/

namespace AlgebraicComplexity

open Tensor
open scoped BigOperators

universe u v w

section Product

variable (K : Type u) [CommSemiring K]
variable {V : Leg → Type v} {W : Leg → Type w}
variable [∀ c, AddCommMonoid (V c)] [∀ c, Module K (V c)]
variable [∀ c, AddCommMonoid (W c)] [∀ c, Module K (W c)]

/-- **The external product of two finite matrix-multiplication direct sums is the Cartesian
family of pairwise products**, reindexed by the numerical copy index `Fin (F₁ * F₂)`.

Proof sketch: distribute the external product over both indexed direct sums
(`Tensor.Isomorphic.external_indexedDirectSum`), then apply the rectangular product law
`⟨a,b,c⟩ ⊗ ⟨a',b',c'⟩ ≅ ⟨aa',bb',cc'⟩` summandwise along `finProdFinEquiv`. -/
theorem restricts_external_matrixMultiplicationDirectSum
    {F₁ F₂ : ℕ} (m₁ n₁ p₁ : Fin F₁ → ℕ) (m₂ n₂ p₂ : Fin F₂ → ℕ) :
    Restricts
      (Tensor.external (matrixMultiplicationDirectSum K m₁ n₁ p₁)
        (matrixMultiplicationDirectSum K m₂ n₂ p₂))
      (matrixMultiplicationDirectSum K
        (fun i : Fin (F₁ * F₂) ↦
          m₁ (finProdFinEquiv.symm i).1 * m₂ (finProdFinEquiv.symm i).2)
        (fun i : Fin (F₁ * F₂) ↦
          n₁ (finProdFinEquiv.symm i).1 * n₂ (finProdFinEquiv.symm i).2)
        (fun i : Fin (F₁ * F₂) ↦
          p₁ (finProdFinEquiv.symm i).1 * p₂ (finProdFinEquiv.symm i).2)) := by
  refine (Tensor.Isomorphic.external_indexedDirectSum
    (fun i ↦ AlgebraicComplexity.matrixMultiplication (K := K) (m₁ i) (n₁ i) (p₁ i))
    (fun j ↦ AlgebraicComplexity.matrixMultiplication (K := K)
      (m₂ j) (n₂ j) (p₂ j))).restricts.trans ?_
  refine Tensor.Restricts.indexedDirectSum_equiv (finProdFinEquiv (m := F₁) (n := F₂)) ?_
  intro q
  have hq : finProdFinEquiv.symm (finProdFinEquiv q) = q :=
    Equiv.symm_apply_apply _ _
  change Restricts _ (matrixMultiplication (K := K)
    (m₁ (finProdFinEquiv.symm (finProdFinEquiv q)).1 *
      m₂ (finProdFinEquiv.symm (finProdFinEquiv q)).2)
    (n₁ (finProdFinEquiv.symm (finProdFinEquiv q)).1 *
      n₂ (finProdFinEquiv.symm (finProdFinEquiv q)).2)
    (p₁ (finProdFinEquiv.symm (finProdFinEquiv q)).1 *
      p₂ (finProdFinEquiv.symm (finProdFinEquiv q)).2))
  rw [hq]
  exact (Tensor.Isomorphic.matrixMultiplication_externalProduct (K := K)
    (m₁ q.1) (n₁ q.1) (p₁ q.1) (m₂ q.2) (n₂ q.2) (p₂ q.2)).restricts

/-- **Supermultiplicativity of the value, certificate level**
(`[CoppersmithWinograd1990]`, §8, p. 264: `V_τ(A ⊗ B) ≥ V_τ(A) × V_τ(B)`).

Two extractions of the *same* power `N` of `A` and of `B` combine into a single extraction of
`(A ⊗ B)^{⊗N}` whose summands are all pairwise products.  The common-length hypothesis is a real
restriction of this construction; see the module docstring for the length-free form. -/
noncomputable def TauValueCertificate.externalOfDegenerates
    {T : Tensor3 K V} {S : Tensor3 K W} {N F₁ F₂ : ℕ}
    (m₁ n₁ p₁ : Fin F₁ → ℕ) (m₂ n₂ p₂ : Fin F₂ → ℕ)
    (hN : 0 < N) (hF₁ : 0 < F₁) (hF₂ : 0 < F₂)
    (hm₁ : ∀ i, 0 < m₁ i) (hn₁ : ∀ i, 0 < n₁ i) (hp₁ : ∀ i, 0 < p₁ i)
    (hm₂ : ∀ j, 0 < m₂ j) (hn₂ : ∀ j, 0 < n₂ j) (hp₂ : ∀ j, 0 < p₂ j)
    (hT : PolynomialDegenerates (Tensor.power T N) (matrixMultiplicationDirectSum K m₁ n₁ p₁))
    (hS : PolynomialDegenerates (Tensor.power S N) (matrixMultiplicationDirectSum K m₂ n₂ p₂)) :
    TauValueCertificate K (Tensor.external T S) where
  power := N
  copies := F₁ * F₂
  xSize := fun i ↦ m₁ (finProdFinEquiv.symm i).1 * m₂ (finProdFinEquiv.symm i).2
  ySize := fun i ↦ n₁ (finProdFinEquiv.symm i).1 * n₂ (finProdFinEquiv.symm i).2
  zSize := fun i ↦ p₁ (finProdFinEquiv.symm i).1 * p₂ (finProdFinEquiv.symm i).2
  power_pos := hN
  copies_pos := Nat.mul_pos hF₁ hF₂
  xSize_pos := fun _ ↦ Nat.mul_pos (hm₁ _) (hm₂ _)
  ySize_pos := fun _ ↦ Nat.mul_pos (hn₁ _) (hn₂ _)
  zSize_pos := fun _ ↦ Nat.mul_pos (hp₁ _) (hp₂ _)
  degenerates :=
    (PolynomialDegenerates.of_restricts
      (Isomorphic.power_external_of_pos T S hN).restricts).trans
      ((hT.external hS).trans
        (PolynomialDegenerates.of_restricts
          (restricts_external_matrixMultiplicationDirectSum K m₁ n₁ p₁ m₂ n₂ p₂)))

/-- The Cartesian volume power sum factors into the two constituent volume power sums. -/
theorem matrixMultiplicationVolumePowerSum_finProdFinEquiv
    {F₁ F₂ : ℕ} (m₁ n₁ p₁ : Fin F₁ → ℕ) (m₂ n₂ p₂ : Fin F₂ → ℕ) (τ : ℝ) :
    matrixMultiplicationVolumePowerSum
        (fun i : Fin (F₁ * F₂) ↦
          m₁ (finProdFinEquiv.symm i).1 * m₂ (finProdFinEquiv.symm i).2)
        (fun i : Fin (F₁ * F₂) ↦
          n₁ (finProdFinEquiv.symm i).1 * n₂ (finProdFinEquiv.symm i).2)
        (fun i : Fin (F₁ * F₂) ↦
          p₁ (finProdFinEquiv.symm i).1 * p₂ (finProdFinEquiv.symm i).2) τ =
      matrixMultiplicationVolumePowerSum m₁ n₁ p₁ τ *
        matrixMultiplicationVolumePowerSum m₂ n₂ p₂ τ := by
  unfold matrixMultiplicationVolumePowerSum matrixMultiplicationVolume
  rw [← Equiv.sum_comp (finProdFinEquiv (m := F₁) (n := F₂))]
  simp only [Equiv.symm_apply_apply]
  rw [Fintype.sum_prod_type, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  have hnat : m₁ i * m₂ j * (n₁ i * n₂ j) * (p₁ i * p₂ j) =
      m₁ i * n₁ i * p₁ i * (m₂ j * n₂ j * p₂ j) := by ring
  rw [hnat, Nat.cast_mul,
    Real.mul_rpow (by positivity) (by positivity)]

/-- The weight of the product certificate is the product of the two weights. -/
theorem TauValueCertificate.term_externalOfDegenerates
    {T : Tensor3 K V} {S : Tensor3 K W} {N F₁ F₂ : ℕ}
    (m₁ n₁ p₁ : Fin F₁ → ℕ) (m₂ n₂ p₂ : Fin F₂ → ℕ)
    (hN : 0 < N) (hF₁ : 0 < F₁) (hF₂ : 0 < F₂)
    (hm₁ : ∀ i, 0 < m₁ i) (hn₁ : ∀ i, 0 < n₁ i) (hp₁ : ∀ i, 0 < p₁ i)
    (hm₂ : ∀ j, 0 < m₂ j) (hn₂ : ∀ j, 0 < n₂ j) (hp₂ : ∀ j, 0 < p₂ j)
    (hT : PolynomialDegenerates (Tensor.power T N) (matrixMultiplicationDirectSum K m₁ n₁ p₁))
    (hS : PolynomialDegenerates (Tensor.power S N) (matrixMultiplicationDirectSum K m₂ n₂ p₂))
    (τ : ℝ) :
    (TauValueCertificate.externalOfDegenerates K m₁ n₁ p₁ m₂ n₂ p₂ hN hF₁ hF₂
        hm₁ hn₁ hp₁ hm₂ hn₂ hp₂ hT hS).term τ =
      tauValueTerm τ N m₁ n₁ p₁ * tauValueTerm τ N m₂ n₂ p₂ := by
  show tauValueTerm τ N
      (fun i : Fin (F₁ * F₂) ↦
        m₁ (finProdFinEquiv.symm i).1 * m₂ (finProdFinEquiv.symm i).2)
      (fun i : Fin (F₁ * F₂) ↦
        n₁ (finProdFinEquiv.symm i).1 * n₂ (finProdFinEquiv.symm i).2)
      (fun i : Fin (F₁ * F₂) ↦
        p₁ (finProdFinEquiv.symm i).1 * p₂ (finProdFinEquiv.symm i).2) = _
  unfold tauValueTerm
  rw [matrixMultiplicationVolumePowerSum_finProdFinEquiv,
    Real.mul_rpow
      (matrixMultiplicationVolumePowerSum_pos hF₁ hm₁ hn₁ hp₁ τ).le
      (matrixMultiplicationVolumePowerSum_pos hF₂ hm₂ hn₂ hp₂ τ).le]

/-- **`V_τ(A ⊗ B) ≥ V_τ(A) · V_τ(B)`, read from two equal-length extractions.** -/
theorem mul_tauValueTerm_le_tauValue_external
    {T : Tensor3 K V} {S : Tensor3 K W} {N F₁ F₂ : ℕ}
    (m₁ n₁ p₁ : Fin F₁ → ℕ) (m₂ n₂ p₂ : Fin F₂ → ℕ)
    (hN : 0 < N) (hF₁ : 0 < F₁) (hF₂ : 0 < F₂)
    (hm₁ : ∀ i, 0 < m₁ i) (hn₁ : ∀ i, 0 < n₁ i) (hp₁ : ∀ i, 0 < p₁ i)
    (hm₂ : ∀ j, 0 < m₂ j) (hn₂ : ∀ j, 0 < n₂ j) (hp₂ : ∀ j, 0 < p₂ j)
    (hT : PolynomialDegenerates (Tensor.power T N) (matrixMultiplicationDirectSum K m₁ n₁ p₁))
    (hS : PolynomialDegenerates (Tensor.power S N) (matrixMultiplicationDirectSum K m₂ n₂ p₂))
    {τ : ℝ} (hbounded : BddAbove (tauValueValues K (Tensor.external T S) τ)) :
    tauValueTerm τ N m₁ n₁ p₁ * tauValueTerm τ N m₂ n₂ p₂ ≤
      tauValue K (Tensor.external T S) τ := by
  have hmem := (TauValueCertificate.externalOfDegenerates K m₁ n₁ p₁ m₂ n₂ p₂ hN hF₁ hF₂
    hm₁ hn₁ hp₁ hm₂ hn₂ hp₂ hT hS).le_tauValue (τ := τ) hbounded
  rwa [TauValueCertificate.term_externalOfDegenerates] at hmem

end Product

end AlgebraicComplexity
