/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.TauValueCore
import AlgebraicComplexity.Tensor.IndexedDegeneration

/-!
# Indexed direct sums of finite `τ`-value certificates

This module supplies the finite additivity operation needed after a laser-method hashing step has
already produced a genuine indexed tensor direct sum.  If every summand has a power-one
`TauValueCertificate`, their polynomial degenerations can be synchronized componentwise, their
matrix-multiplication targets flattened, and the result packaged as one power-one certificate of
the indexed direct sum.

This is intentionally weaker than the global law `V_τ(A ⊞ B) ≥ V_τ(A) + V_τ(B)`: it does not
expand a power of a binary direct sum.  It is exactly the reusable semantic operation needed by
outer hashing clients, and its finite value term is the sum of the component terms.
-/

namespace AlgebraicComplexity

open Tensor
open scoped BigOperators

universe u v w

namespace TauValueCertificate

variable {K : Type u} [CommSemiring K]
variable {ι : Type w} [Fintype ι] [DecidableEq ι] [Nonempty ι]
variable {V : ι → Leg → Type v}
variable [∀ i c, AddCommMonoid (V i c)] [∀ i c, Module K (V i c)]
variable {T : ∀ i, Tensor3 K (V i)}

/-- Dependent index of all matrix-multiplication summands occurring in a family of certificates. -/
abbrev IndexedSumIndex (certificate : ∀ i, TauValueCertificate K (T i)) :=
  Σ i, Fin (certificate i).copies

/-- Flatten a finite family of power-one value certificates into one certificate of the indexed
direct sum of their sources.

The component polynomial degenerations may have unrelated leading degrees:
`PolynomialDegenerates.indexedDirectSum` synchronizes them constructively before the nested target
sum is flattened and reindexed by `Fin`.

Proof sketch: identify `Tᵢ` with its first power, apply every component certificate independently,
flatten `⊕ᵢ (⊕ⱼ Qᵢⱼ)` to `⊕_(i,j) Qᵢⱼ`, and reindex the dependent pair by
`Fintype.equivFin`. -/
noncomputable def indexedDirectSumPowerOne
    (certificate : ∀ i, TauValueCertificate K (T i))
    (hpower : ∀ i, (certificate i).power = 1) :
    TauValueCertificate K (Tensor.indexedDirectSum T) := by
  classical
  let J := IndexedSumIndex certificate
  let e : J ≃ Fin (Fintype.card J) := Fintype.equivFin J
  let xSize : Fin (Fintype.card J) → ℕ :=
    fun j ↦ (certificate (e.symm j).1).xSize (e.symm j).2
  let ySize : Fin (Fintype.card J) → ℕ :=
    fun j ↦ (certificate (e.symm j).1).ySize (e.symm j).2
  let zSize : Fin (Fintype.card J) → ℕ :=
    fun j ↦ (certificate (e.symm j).1).zSize (e.symm j).2
  let Q : ∀ ij : J, Tensor3 K
      (MMSpace K
        ((certificate ij.1).xSize ij.2)
        ((certificate ij.1).ySize ij.2)
        ((certificate ij.1).zSize ij.2)) :=
    fun ij ↦ AlgebraicComplexity.matrixMultiplication (K := K)
      ((certificate ij.1).xSize ij.2)
      ((certificate ij.1).ySize ij.2)
      ((certificate ij.1).zSize ij.2)
  have hcomponent (i : ι) : PolynomialDegenerates (T i)
      (Tensor.indexedDirectSum (fun j : Fin (certificate i).copies ↦ Q ⟨i, j⟩)) := by
    have hi := (certificate i).degenerates
    rw [hpower i] at hi
    change PolynomialDegenerates (Tensor.power (T i) 1)
      (Tensor.indexedDirectSum (fun j : Fin (certificate i).copies ↦ Q ⟨i, j⟩)) at hi
    exact (PolynomialDegenerates.of_restricts
      (Isomorphic.power_one (T i)).symm.restricts).trans hi
  have hnested : PolynomialDegenerates (Tensor.indexedDirectSum T)
      (Tensor.indexedDirectSum (fun i ↦
        Tensor.indexedDirectSum (fun j : Fin (certificate i).copies ↦ Q ⟨i, j⟩))) :=
    PolynomialDegenerates.indexedDirectSum hcomponent
  have hflatten : PolynomialDegenerates
      (Tensor.indexedDirectSum (fun i ↦
        Tensor.indexedDirectSum (fun j : Fin (certificate i).copies ↦ Q ⟨i, j⟩)))
      (Tensor.indexedDirectSum Q) := by
    exact PolynomialDegenerates.of_restricts
      (Isomorphic.indexedDirectSum_sigma
        (K := K)
        (J := fun i : ι ↦ Fin (certificate i).copies)
        (S := fun i j ↦ MMSpace K
          ((certificate i).xSize j)
          ((certificate i).ySize j)
          ((certificate i).zSize j))
        (T := Q)).symm.restricts
  have hreindex : Restricts (Tensor.indexedDirectSum Q)
      (matrixMultiplicationDirectSum K xSize ySize zSize) := by
    unfold matrixMultiplicationDirectSum
    apply Restricts.indexedDirectSum_equiv e
    intro ij
    apply Isomorphic.restricts
    change Isomorphic (Q ij) (Q (e.symm (e ij)))
    rw [e.symm_apply_apply]
    exact Isomorphic.refl (Q ij)
  exact
    { power := 1
      copies := Fintype.card J
      xSize := xSize
      ySize := ySize
      zSize := zSize
      power_pos := Nat.one_pos
      copies_pos := Fintype.card_pos_iff.mpr ⟨⟨Classical.choice inferInstance,
        ⟨0, (certificate (Classical.choice inferInstance)).copies_pos⟩⟩⟩
      xSize_pos := fun j ↦ (certificate (e.symm j).1).xSize_pos (e.symm j).2
      ySize_pos := fun j ↦ (certificate (e.symm j).1).ySize_pos (e.symm j).2
      zSize_pos := fun j ↦ (certificate (e.symm j).1).zSize_pos (e.symm j).2
      degenerates :=
        (PolynomialDegenerates.of_restricts
          (Isomorphic.power_one (Tensor.indexedDirectSum T)).restricts).trans
          (hnested.trans (hflatten.trans
            (PolynomialDegenerates.of_restricts hreindex))) }

/-- The flattened certificate has source power one. -/
@[simp] theorem indexedDirectSumPowerOne_power
    (certificate : ∀ i, TauValueCertificate K (T i))
    (hpower : ∀ i, (certificate i).power = 1) :
    (indexedDirectSumPowerOne certificate hpower).power = 1 := rfl

/-- The flattened certificate has one numerical target index for every dependent pair of a source
summand and one of its component matrix-multiplication targets. -/
@[simp] theorem indexedDirectSumPowerOne_copies
    (certificate : ∀ i, TauValueCertificate K (T i))
    (hpower : ∀ i, (certificate i).power = 1) :
    (indexedDirectSumPowerOne certificate hpower).copies =
      Fintype.card (IndexedSumIndex certificate) := rfl

/-- The first matrix dimension of a flattened target is read from the corresponding dependent
pair of a source summand and one of its targets. -/
@[simp] theorem indexedDirectSumPowerOne_xSize
    (certificate : ∀ i, TauValueCertificate K (T i))
    (hpower : ∀ i, (certificate i).power = 1)
    (j : Fin (Fintype.card (IndexedSumIndex certificate))) :
    (indexedDirectSumPowerOne certificate hpower).xSize j =
      (certificate ((Fintype.equivFin (IndexedSumIndex certificate)).symm j).1).xSize
        ((Fintype.equivFin (IndexedSumIndex certificate)).symm j).2 := by
  rfl

/-- The second matrix dimension of a flattened target is read from its dependent-pair index. -/
@[simp] theorem indexedDirectSumPowerOne_ySize
    (certificate : ∀ i, TauValueCertificate K (T i))
    (hpower : ∀ i, (certificate i).power = 1)
    (j : Fin (Fintype.card (IndexedSumIndex certificate))) :
    (indexedDirectSumPowerOne certificate hpower).ySize j =
      (certificate ((Fintype.equivFin (IndexedSumIndex certificate)).symm j).1).ySize
        ((Fintype.equivFin (IndexedSumIndex certificate)).symm j).2 := by
  rfl

/-- The third matrix dimension of a flattened target is read from its dependent-pair index. -/
@[simp] theorem indexedDirectSumPowerOne_zSize
    (certificate : ∀ i, TauValueCertificate K (T i))
    (hpower : ∀ i, (certificate i).power = 1)
    (j : Fin (Fintype.card (IndexedSumIndex certificate))) :
    (indexedDirectSumPowerOne certificate hpower).zSize j =
      (certificate ((Fintype.equivFin (IndexedSumIndex certificate)).symm j).1).zSize
        ((Fintype.equivFin (IndexedSumIndex certificate)).symm j).2 := by
  rfl

/-- Flattening a family of power-one certificates preserves the total matrix-volume power sum:
the flat sum is exactly the sum of the component sums.

Proof sketch: reindex the flat `Fin` sum by `Fintype.equivFin`, then expand the resulting sum over
the dependent pair `Σ i, Fin copiesᵢ` with `Fintype.sum_sigma`. -/
theorem matrixMultiplicationVolumePowerSum_indexedDirectSumPowerOne
    (certificate : ∀ i, TauValueCertificate K (T i))
    (hpower : ∀ i, (certificate i).power = 1) (τ : ℝ) :
    matrixMultiplicationVolumePowerSum
        (indexedDirectSumPowerOne certificate hpower).xSize
        (indexedDirectSumPowerOne certificate hpower).ySize
        (indexedDirectSumPowerOne certificate hpower).zSize τ =
      ∑ i, matrixMultiplicationVolumePowerSum
        (certificate i).xSize (certificate i).ySize (certificate i).zSize τ := by
  classical
  unfold matrixMultiplicationVolumePowerSum matrixMultiplicationVolume
  let J := IndexedSumIndex certificate
  let e : J ≃ Fin (Fintype.card J) := Fintype.equivFin J
  let f : J → ℝ := fun ij ↦
    (((certificate ij.1).xSize ij.2 * (certificate ij.1).ySize ij.2 *
      (certificate ij.1).zSize ij.2 : ℕ) : ℝ) ^ τ
  change (∑ j, f (e.symm j)) = ∑ i, ∑ j, f ⟨i, j⟩
  rw [← Equiv.sum_comp e, Fintype.sum_sigma]
  simp only [Equiv.symm_apply_apply]

/-- **Finite additivity after an actual direct-sum extraction.**  The weight of the flattened
power-one certificate is exactly the sum of the component weights.

This is the numerical interface used by hashing clients.  It is not the global CW90 theorem
`V_τ(A ⊞ B) ≥ V_τ(A) + V_τ(B)`, because the source here is already a genuine indexed direct sum;
no binomial expansion of its powers is needed. -/
theorem indexedDirectSumPowerOne_term
    (certificate : ∀ i, TauValueCertificate K (T i))
    (hpower : ∀ i, (certificate i).power = 1) (τ : ℝ) :
    (indexedDirectSumPowerOne certificate hpower).term τ =
      ∑ i, (certificate i).term τ := by
  rw [term]
  unfold tauValueTerm
  rw [indexedDirectSumPowerOne_power, Nat.cast_one, inv_one, Real.rpow_one,
    matrixMultiplicationVolumePowerSum_indexedDirectSumPowerOne]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [term, tauValueTerm, hpower i, Nat.cast_one, inv_one, Real.rpow_one]

section SourcePower

variable {U : Leg → Type v}
variable [∀ c, AddCommMonoid (U c)] [∀ c, Module K (U c)]
variable {S : Tensor3 K U}

/-- Reinterpret a power-one certificate whose source is `S^{⊗N}` as an `N`-power certificate of
`S` itself.

This packaging operation is useful after hashing a concrete tensor power: the hashing theorem
produces an actual direct sum from `S^{⊗N}`, and the preceding constructor gives a power-one
certificate of that extracted source.  The present adapter records the same target family at the
correct base-tensor power `N`.

Proof sketch: identify `S^{⊗N}` with its first tensor power and compose with the supplied
certificate degeneration.  All target data are unchanged. -/
noncomputable def ofPowerOneOnPower
    (N : ℕ) (hN : 0 < N)
    (certificate : TauValueCertificate K (Tensor.power S N))
    (hpower : certificate.power = 1) :
    TauValueCertificate K S where
  power := N
  copies := certificate.copies
  xSize := certificate.xSize
  ySize := certificate.ySize
  zSize := certificate.zSize
  power_pos := hN
  copies_pos := certificate.copies_pos
  xSize_pos := certificate.xSize_pos
  ySize_pos := certificate.ySize_pos
  zSize_pos := certificate.zSize_pos
  degenerates := by
    have hdeg := certificate.degenerates
    rw [hpower] at hdeg
    exact (PolynomialDegenerates.of_restricts
      (Isomorphic.power_one (Tensor.power S N)).symm.restricts).trans hdeg

/-- The term of `ofPowerOneOnPower` is the `N`th root of the original power-one term. -/
theorem term_ofPowerOneOnPower
    (N : ℕ) (hN : 0 < N)
    (certificate : TauValueCertificate K (Tensor.power S N))
    (hpower : certificate.power = 1) (τ : ℝ) :
    (ofPowerOneOnPower N hN certificate hpower).term τ =
      certificate.term τ ^ ((N : ℝ)⁻¹) := by
  show tauValueTerm τ N certificate.xSize certificate.ySize certificate.zSize =
    (tauValueTerm τ certificate.power certificate.xSize certificate.ySize certificate.zSize) ^
      ((N : ℝ)⁻¹)
  unfold tauValueTerm
  rw [hpower, Nat.cast_one, inv_one, Real.rpow_one]

end SourcePower

end TauValueCertificate

end AlgebraicComplexity
