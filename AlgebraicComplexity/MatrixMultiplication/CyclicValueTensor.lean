/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.CyclicValue
import AlgebraicComplexity.MatrixMultiplication.DirectSum
import AlgebraicComplexity.MatrixMultiplication.CyclicProduct
import AlgebraicComplexity.Tensor.BorderRank

/-!
# Tensor adapters for cyclic values

This module instantiates the relation-parametric value core with two semantic relations.
`exactCyclicExtractionRelation` gives the strict exact-legwise-restriction specialization.
`polynomialCyclicExtractionRelation` gives the constructive approximate-computation relation used
by historical CW90 `V_τ`: polynomial degeneration followed by cyclic symmetrization.  The promotion
theorem is explicit: an exact restriction is a polynomial degeneration, but a general polynomial
degeneration is not silently treated as an exact restriction.

The final section proves the elementary border-rank bound for the three-orientation source. It is
an algebraic compatibility fact, not a value-to-omega theorem.
-/

namespace AlgebraicComplexity

open Tensor

universe u v

variable (K : Type u) [CommSemiring K]
variable {V : Leg → Type v}
variable [∀ c, AddCommMonoid (V c)] [∀ c, Module K (V c)]

/-- Exact legwise restriction as a cyclic extraction relation. -/
def exactCyclicExtractionRelation (T : Tensor3 K V) : CyclicExtractionRelation K T :=
  fun power _copies xSize ySize zSize =>
    Restricts (cyclicPowerProduct K T power)
      (matrixMultiplicationDirectSum K xSize ySize zSize)

/-- Polynomial degeneration as a cyclic extraction relation. -/
def polynomialCyclicExtractionRelation (T : Tensor3 K V) : CyclicExtractionRelation K T :=
  fun power _copies xSize ySize zSize =>
    PolynomialDegenerates (cyclicPowerProduct K T power)
      (matrixMultiplicationDirectSum K xSize ySize zSize)

/-- A cyclic value certificate whose finite extraction is an exact legwise restriction. -/
abbrev CyclicValueCertificate (T : Tensor3 K V) (τ : ℝ) :=
  CyclicExtractionCertificate K T τ (exactCyclicExtractionRelation K T)

/-- A cyclic value certificate whose finite extraction is a polynomial degeneration. -/
abbrev CyclicDegenerationCertificate (T : Tensor3 K V) (τ : ℝ) :=
  CyclicExtractionCertificate K T τ (polynomialCyclicExtractionRelation K T)

namespace CyclicValueCertificate

variable {T : Tensor3 K V} {τ : ℝ}

/-- Read the exact-restriction witness from an exact cyclic certificate. -/
theorem restricts (certificate : CyclicValueCertificate K T τ) :
    Restricts (cyclicPowerProduct K T certificate.power)
      (matrixMultiplicationDirectSum K certificate.xSize certificate.ySize certificate.zSize) := by
  exact certificate.extraction

/-- Promote an exact-restriction certificate to a polynomial-degeneration certificate. -/
def toDegeneration (certificate : CyclicValueCertificate K T τ) :
    CyclicDegenerationCertificate K T τ :=
  { power := certificate.power
    copies := certificate.copies
    xSize := certificate.xSize
    ySize := certificate.ySize
    zSize := certificate.zSize
    power_pos := certificate.power_pos
    copies_pos := certificate.copies_pos
    xSize_pos := certificate.xSize_pos
    ySize_pos := certificate.ySize_pos
    zSize_pos := certificate.zSize_pos
    extraction := PolynomialDegenerates.of_restricts certificate.restricts }

/-- The numerical term carried by an exact-restriction certificate. -/
noncomputable abbrev term (certificate : CyclicValueCertificate K T τ) : ℝ :=
  CyclicExtractionCertificate.term (K := K) certificate

/-- Package an exact-restriction witness with the positivity data required by a value certificate. -/
def of_restriction
    (τ : ℝ) (T : Tensor3 K V) (k F : ℕ)
    (m n p : Fin F → ℕ)
    (hk : 0 < k) (hF : 0 < F)
    (hm : ∀ i, 0 < m i) (hn : ∀ i, 0 < n i) (hp : ∀ i, 0 < p i)
    (hrestricts : Restricts (cyclicPowerProduct K T k)
      (matrixMultiplicationDirectSum K m n p)) :
    CyclicValueCertificate K T τ :=
  CyclicExtractionCertificate.of_extraction K
    (exactCyclicExtractionRelation K T) τ k F m n p hk hF hm hn hp hrestricts

/-- Package an exact extraction indexed by an arbitrary nonempty finite type as a numerical
cyclic-value certificate.

The source theorem may keep a structured survivor type.  This adapter reindexes its constant
matrix-multiplication family by `Fin (Fintype.card I)`, which is the canonical numerical copy
index used by value certificates. -/
noncomputable def of_constantIndexedDirectSum
    {I : Type*} [Fintype I] [Nonempty I]
    (τ : ℝ) (T : Tensor3 K V) (k m n p : ℕ)
    (hk : 0 < k) (hm : 0 < m) (hn : 0 < n) (hp : 0 < p)
    (hrestricts : Restricts (cyclicPowerProduct K T k)
      (Tensor.indexedDirectSum
        (fun _ : I ↦ matrixMultiplication (K := K) m n p))) :
    CyclicValueCertificate K T τ := by
  let e : I ≃ Fin (Fintype.card I) := Fintype.equivFin I
  let Q := matrixMultiplication (K := K) m n p
  have hreindex : Restricts
      (Tensor.indexedDirectSum (fun _ : I ↦ Q))
      (matrixMultiplicationDirectSum K
        (fun _ : Fin (Fintype.card I) ↦ m)
        (fun _ : Fin (Fintype.card I) ↦ n)
        (fun _ : Fin (Fintype.card I) ↦ p)) := by
    simpa only [matrixMultiplicationDirectSum, Q] using
      Tensor.Restricts.indexedDirectSum_const_equiv (K := K) e Q
  exact CyclicValueCertificate.of_restriction (K := K) τ T k (Fintype.card I)
    (fun _ ↦ m) (fun _ ↦ n) (fun _ ↦ p) hk Fintype.card_pos
    (fun _ ↦ hm) (fun _ ↦ hn) (fun _ ↦ hp)
    (hrestricts.trans (by simpa only [Q] using hreindex))

end CyclicValueCertificate

namespace CyclicDegenerationCertificate

variable {T : Tensor3 K V} {τ : ℝ}

/-- Read the polynomial-degeneration witness from a degeneration certificate. -/
theorem degenerates (certificate : CyclicDegenerationCertificate K T τ) :
    PolynomialDegenerates (cyclicPowerProduct K T certificate.power)
      (matrixMultiplicationDirectSum K certificate.xSize certificate.ySize certificate.zSize) := by
  exact certificate.extraction

/-- The numerical term carried by a polynomial-degeneration certificate. -/
noncomputable abbrev term (certificate : CyclicDegenerationCertificate K T τ) : ℝ :=
  CyclicExtractionCertificate.term (K := K) certificate

/-- Package a polynomial-degeneration witness with the positivity data required by a degeneration
value certificate. -/
def of_polynomialDegenerates
    (τ : ℝ) (T : Tensor3 K V) (k F : ℕ)
    (m n p : Fin F → ℕ)
    (hk : 0 < k) (hF : 0 < F)
    (hm : ∀ i, 0 < m i) (hn : ∀ i, 0 < n i) (hp : ∀ i, 0 < p i)
    (hdeg : PolynomialDegenerates (cyclicPowerProduct K T k)
      (matrixMultiplicationDirectSum K m n p)) :
    CyclicDegenerationCertificate K T τ :=
  CyclicExtractionCertificate.of_extraction K
    (polynomialCyclicExtractionRelation K T) τ k F m n p hk hF hm hn hp hdeg

/-- Exact restriction is the standard specialization of the degeneration certificate. -/
def of_restriction
    (τ : ℝ) (T : Tensor3 K V) (k F : ℕ)
    (m n p : Fin F → ℕ)
    (hk : 0 < k) (hF : 0 < F)
    (hm : ∀ i, 0 < m i) (hn : ∀ i, 0 < n i) (hp : ∀ i, 0 < p i)
    (hrestricts : Restricts (cyclicPowerProduct K T k)
      (matrixMultiplicationDirectSum K m n p)) :
    CyclicDegenerationCertificate K T τ :=
  of_polynomialDegenerates K τ T k F m n p hk hF hm hn hp
    (PolynomialDegenerates.of_restricts hrestricts)

/-- Package a polynomial extraction indexed by an arbitrary nonempty finite type as a numerical
cyclic-degeneration-value certificate.

Proof sketch: reindex the constant direct sum by `Fintype.equivFin`, promote that exact
reindexing to a degree-zero polynomial degeneration, and compose it with the supplied source
degeneration. -/
noncomputable def of_constantIndexedDirectSum
    {I : Type*} [Fintype I] [Nonempty I]
    (τ : ℝ) (T : Tensor3 K V) (k m n p : ℕ)
    (hk : 0 < k) (hm : 0 < m) (hn : 0 < n) (hp : 0 < p)
    (hdeg : PolynomialDegenerates (cyclicPowerProduct K T k)
      (Tensor.indexedDirectSum
        (fun _ : I ↦ matrixMultiplication (K := K) m n p))) :
    CyclicDegenerationCertificate K T τ := by
  let e : I ≃ Fin (Fintype.card I) := Fintype.equivFin I
  let Q := matrixMultiplication (K := K) m n p
  have hreindex : Restricts
      (Tensor.indexedDirectSum (fun _ : I ↦ Q))
      (matrixMultiplicationDirectSum K
        (fun _ : Fin (Fintype.card I) ↦ m)
        (fun _ : Fin (Fintype.card I) ↦ n)
        (fun _ : Fin (Fintype.card I) ↦ p)) := by
    simpa only [matrixMultiplicationDirectSum, Q] using
      Tensor.Restricts.indexedDirectSum_const_equiv (K := K) e Q
  exact CyclicDegenerationCertificate.of_polynomialDegenerates (K := K)
    τ T k (Fintype.card I) (fun _ ↦ m) (fun _ ↦ n) (fun _ ↦ p)
    hk Fintype.card_pos (fun _ ↦ hm) (fun _ ↦ hn) (fun _ ↦ hp)
    (hdeg.trans (PolynomialDegenerates.of_restricts
      (by simpa only [Q] using hreindex)))

end CyclicDegenerationCertificate

/-- The cyclic value specialized to exact legwise restrictions. -/
noncomputable def cyclicValue (T : Tensor3 K V) (τ : ℝ) : ℝ :=
  cyclicExtractionValue K T τ (exactCyclicExtractionRelation K T)

/-- The cyclic polynomial-degeneration value corresponding to historical CW90 `V_τ`. -/
noncomputable def degenerationValue (T : Tensor3 K V) (τ : ℝ) : ℝ :=
  cyclicExtractionValue K T τ (polynomialCyclicExtractionRelation K T)

/-- The set of finite terms contributing to the exact-restriction cyclic value. -/
abbrev cyclicValueValues (T : Tensor3 K V) (τ : ℝ) : Set ℝ :=
  cyclicExtractionValues K T τ (exactCyclicExtractionRelation K T)

/-- The set of finite terms contributing to the polynomial-degeneration value. -/
abbrev degenerationValueValues (T : Tensor3 K V) (τ : ℝ) : Set ℝ :=
  cyclicExtractionValues K T τ (polynomialCyclicExtractionRelation K T)

section CertificateLemmas

variable {T : Tensor3 K V} {τ : ℝ}

/-- An exact-restriction cyclic certificate has a positive term. -/
theorem CyclicValueCertificate.term_pos
    (certificate : CyclicValueCertificate K T τ) :
    0 < certificate.term :=
  CyclicExtractionCertificate.term_pos (K := K) certificate

/-- A polynomial-degeneration certificate has a positive term. -/
theorem CyclicDegenerationCertificate.term_pos
    (certificate : CyclicDegenerationCertificate K T τ) :
    0 < certificate.term :=
  CyclicExtractionCertificate.term_pos (K := K) certificate

/-- Every exact certificate contributes a member of the exact value set. -/
theorem CyclicValueCertificate.mem_cyclicValueValues
    (certificate : CyclicValueCertificate K T τ) :
    certificate.term ∈ cyclicValueValues K T τ :=
  ⟨certificate, rfl⟩

/-- Every degeneration certificate contributes a member of the degeneration value set. -/
theorem CyclicDegenerationCertificate.mem_degenerationValueValues
    (certificate : CyclicDegenerationCertificate K T τ) :
    certificate.term ∈ degenerationValueValues K T τ :=
  ⟨certificate, rfl⟩

/-- An exact certificate term is below the exact value when the exact value set is bounded above. -/
theorem CyclicValueCertificate.le_cyclicValue
    (certificate : CyclicValueCertificate K T τ)
    (hbounded : BddAbove (cyclicValueValues K T τ)) :
    certificate.term ≤ cyclicValue K T τ :=
  le_csSup hbounded certificate.mem_cyclicValueValues

/-- A degeneration certificate term is below the degeneration value when its set is bounded above. -/
theorem CyclicDegenerationCertificate.le_degenerationValue
    (certificate : CyclicDegenerationCertificate K T τ)
    (hbounded : BddAbove (degenerationValueValues K T τ)) :
    certificate.term ≤ degenerationValue K T τ :=
  le_csSup hbounded certificate.mem_degenerationValueValues

/-- An exact certificate makes the exact value set nonempty. -/
theorem cyclicValueValues_nonempty_of_certificate
    (certificate : CyclicValueCertificate K T τ) :
    (cyclicValueValues K T τ).Nonempty :=
  ⟨certificate.term, certificate.mem_cyclicValueValues⟩

/-- A degeneration certificate makes the degeneration value set nonempty. -/
theorem degenerationValueValues_nonempty_of_certificate
    (certificate : CyclicDegenerationCertificate K T τ) :
    (degenerationValueValues K T τ).Nonempty :=
  ⟨certificate.term, certificate.mem_degenerationValueValues⟩

/-- Exact-restriction terms promote pointwise to polynomial-degeneration terms. -/
theorem cyclicValueValues_subset_degenerationValueValues
    (T : Tensor3 K V) (τ : ℝ) :
    cyclicValueValues K T τ ⊆ degenerationValueValues K T τ := by
  intro x hx
  rcases hx with ⟨certificate, rfl⟩
  exact ⟨CyclicValueCertificate.toDegeneration (K := K) certificate, rfl⟩

end CertificateLemmas

section BorderRank

variable (K : Type u) [CommSemiring K]
variable {V : Leg → Type v}
variable [∀ c, AddCommMonoid (V c)] [∀ c, Module K (V c)]

/-- The cyclic three-orientation product has border rank at most the product of the three power
border-rank bounds.

Proof sketch: apply submultiplicativity twice. The inverse cyclic factor is transported through
the proved two-cycle isomorphism; the remaining arithmetic is power addition. -/
theorem borderRank_cyclicPowerProduct_le
    (T : Tensor3 K V) (k : ℕ) :
    borderRank (cyclicPowerProduct K T k) ≤ borderRank T ^ (3 * k) := by
  let P := Tensor.power T k
  have hP : borderRank P ≤ borderRank T ^ k :=
    borderRank_power_le T k
  have hForward : borderRank (Tensor.permute cycle P) ≤ borderRank T ^ k :=
    (borderRank_permute_cycle_le P).trans hP
  have hInverse : borderRank (Tensor.permute cycle.symm P) ≤ borderRank T ^ k := by
    rw [← borderRank_isomorphic (Isomorphic.permute_cycle_cycle P)]
    exact (borderRank_permute_cycle_le (Tensor.permute cycle P)).trans hForward
  have hLeft :
      borderRank (Tensor.external P (Tensor.permute cycle P)) ≤
        (borderRank T ^ k) * (borderRank T ^ k) :=
    (borderRank_external_le P (Tensor.permute cycle P)).trans
      (Nat.mul_le_mul hP hForward)
  have hAll :
      borderRank (Tensor.external
        (Tensor.external P (Tensor.permute cycle P))
        (Tensor.permute cycle.symm P)) ≤
        ((borderRank T ^ k) * (borderRank T ^ k)) * (borderRank T ^ k) :=
    (borderRank_external_le
      (Tensor.external P (Tensor.permute cycle P)) (Tensor.permute cycle.symm P)).trans
      (Nat.mul_le_mul hLeft hInverse)
  change borderRank (Tensor.external
      (Tensor.external P (Tensor.permute cycle P))
      (Tensor.permute cycle.symm P)) ≤ _
  calc
    borderRank (Tensor.external
        (Tensor.external P (Tensor.permute cycle P))
        (Tensor.permute cycle.symm P)) ≤
        ((borderRank T ^ k) * (borderRank T ^ k)) * (borderRank T ^ k) := hAll
    _ = borderRank T ^ (3 * k) := by
      rw [show 3 * k = k + k + k by omega, pow_add, pow_add]

end BorderRank

end AlgebraicComplexity
