/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.Volume
import AlgebraicComplexity.Tensor.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Relation-parametric cyclic values

This lightweight module is the numerical core of the modern laser-method value formalism. A finite
certificate records a positive source power, a finite family of positive matrix dimensions, and a
client-supplied semantic extraction relation. The relation is a parameter, so the same profile and
volume calculations work for exact restrictions, zeroing plans, monomial degenerations, and
polynomial interpolation certificates.

Tensor-specific exact and polynomial relations, named cyclicValue and degenerationValue aliases,
and border-rank consequences live in CyclicValueTensor.lean. Keeping those adapters out of this
file avoids loading tensor direct-sum and Schonhage theorem machinery for finite arithmetic clients.

The numerical term is (sum_i (m_i*n_i*p_i)^tau)^(1/(3*k)). Supremum definitions do not silently
assume boundedness; lemmas reading a certificate back from a supremum state BddAbove explicitly.
-/

namespace AlgebraicComplexity

open Tensor
open scoped BigOperators

universe u v

section Definitions

variable (K : Type u) [CommSemiring K]
variable {V : Leg → Type v}
variable [∀ c, AddCommMonoid (V c)] [∀ c, Module K (V c)]

/-- The finite tau-value term of a positive dimension family at source power k. -/
noncomputable def cyclicValueTerm
    (τ : ℝ) (k : ℕ) {F : ℕ}
    (m n p : Fin F → ℕ) : ℝ :=
  (matrixMultiplicationVolumePowerSum m n p τ) ^
    (((3 * k : ℕ) : ℝ)⁻¹)

/-- A semantic extraction relation for cyclic value certificates.

The relation is indexed by source power and all three finite dimension functions. Its body may
mention the corresponding tensor source and direct-sum target, or be a richer checked predicate
whose soundness is proved by a downstream adapter. -/
def CyclicExtractionRelation
    (_T : Tensor3 K V) :=
  ∀ (_power copies : ℕ) (_xSize _ySize _zSize : Fin copies → ℕ), Prop

/-- A finite certificate for any relation-parametric cyclic value extraction.

Positivity is stored in the structure, so logarithmic arguments cannot accidentally use an empty
family or a zero-dimensional matrix product. -/
structure CyclicExtractionCertificate (T : Tensor3 K V) (τ : ℝ)
    (Rel : CyclicExtractionRelation K T) where
  /-- Number of copies of the three-orientation source. -/
  power : ℕ
  /-- Number of matrix-multiplication summands in the target. -/
  copies : ℕ
  /-- First, second, and third matrix dimensions of each summand. -/
  xSize : Fin copies → ℕ
  ySize : Fin copies → ℕ
  zSize : Fin copies → ℕ
  power_pos : 0 < power
  copies_pos : 0 < copies
  xSize_pos : ∀ i, 0 < xSize i
  ySize_pos : ∀ i, 0 < ySize i
  zSize_pos : ∀ i, 0 < zSize i
  /-- The client-provided semantic extraction witness. -/
  extraction : Rel power copies xSize ySize zSize

namespace CyclicExtractionCertificate

variable {T : Tensor3 K V} {τ : ℝ}
variable {Rel : CyclicExtractionRelation K T}

/-- The numerical term carried by a relation-parametric certificate. -/
noncomputable def term (certificate : CyclicExtractionCertificate K T τ Rel) : ℝ :=
  cyclicValueTerm τ certificate.power certificate.xSize certificate.ySize certificate.zSize

/-- Construct a relation-parametric certificate from finite data and one semantic witness. -/
def of_extraction
    (Rel : CyclicExtractionRelation K T)
    (τ : ℝ) (k F : ℕ)
    (m n p : Fin F → ℕ)
    (hk : 0 < k) (hF : 0 < F)
    (hm : ∀ i, 0 < m i) (hn : ∀ i, 0 < n i) (hp : ∀ i, 0 < p i)
    (hRel : Rel k F m n p) :
    CyclicExtractionCertificate K T τ Rel :=
  { power := k
    copies := F
    xSize := m
    ySize := n
    zSize := p
    power_pos := hk
    copies_pos := hF
    xSize_pos := hm
    ySize_pos := hn
    zSize_pos := hp
    extraction := hRel }

end CyclicExtractionCertificate

/-- The set of finite certificate terms for an arbitrary extraction relation. -/
def cyclicExtractionValues (T : Tensor3 K V) (τ : ℝ)
    (Rel : CyclicExtractionRelation K T) : Set ℝ :=
  {x | ∃ certificate : CyclicExtractionCertificate K T τ Rel,
    certificate.term = x}

/-- The supremum of finite terms for an arbitrary extraction relation.

No boundedness assumption is built into this definition. The relation-parametric form lets clients
compare two certificate calculi before choosing a named value. -/
noncomputable def cyclicExtractionValue (T : Tensor3 K V) (τ : ℝ)
    (Rel : CyclicExtractionRelation K T) : ℝ :=
  sSup (cyclicExtractionValues K T τ Rel)

end Definitions

section CertificateLemmas

variable (K : Type u) [CommSemiring K]
variable {V : Leg → Type v}
variable [∀ c, AddCommMonoid (V c)] [∀ c, Module K (V c)]
variable {T : Tensor3 K V} {τ : ℝ}

/-- A finite positive dimension family has a positive tau-term for every real tau.

Proof sketch: every matrix-multiplication volume is positive, hence the finite sum inside the real
power is positive; Real.rpow_pos_of_pos handles the possibly nonintegral exponent. -/
theorem cyclicValueTerm_pos
    (τ : ℝ) (k F : ℕ) (m n p : Fin F → ℕ)
    (_hk : 0 < k) (hF : 0 < F)
    (hm : ∀ i, 0 < m i) (hn : ∀ i, 0 < n i) (hp : ∀ i, 0 < p i) :
    0 < cyclicValueTerm τ k m n p := by
  letI : Nonempty (Fin F) := ⟨⟨0, hF⟩⟩
  unfold cyclicValueTerm
  have hsum : 0 < matrixMultiplicationVolumePowerSum
      m n p τ := by
    unfold matrixMultiplicationVolumePowerSum
    apply Finset.sum_pos
    · intro i _
      have hvol : 0 < m i * n i * p i :=
        Nat.mul_pos (Nat.mul_pos (hm i) (hn i)) (hp i)
      exact Real.rpow_pos_of_pos (by exact_mod_cast hvol) _
    · exact Finset.univ_nonempty
  exact Real.rpow_pos_of_pos hsum _

/-- Any relation-parametric certificate has a positive numerical term. -/
theorem CyclicExtractionCertificate.term_pos
    {Rel : CyclicExtractionRelation K T}
    (certificate : CyclicExtractionCertificate K T τ Rel) :
    0 < certificate.term := by
  exact cyclicValueTerm_pos τ certificate.power certificate.copies
    certificate.xSize certificate.ySize certificate.zSize certificate.power_pos
    certificate.copies_pos certificate.xSize_pos certificate.ySize_pos certificate.zSize_pos

/-- Every relation-parametric finite certificate contributes its term to its value set. -/
theorem CyclicExtractionCertificate.mem_cyclicExtractionValues
    {Rel : CyclicExtractionRelation K T}
    (certificate : CyclicExtractionCertificate K T τ Rel) :
    certificate.term ∈ cyclicExtractionValues K T τ Rel := by
  exact ⟨certificate, rfl⟩

/-- A certificate term is below its relation-parametric supremum whenever the term set is bounded
above. -/
theorem CyclicExtractionCertificate.le_cyclicExtractionValue
    {Rel : CyclicExtractionRelation K T}
    (certificate : CyclicExtractionCertificate K T τ Rel)
    (hbounded : BddAbove (cyclicExtractionValues K T τ Rel)) :
    certificate.term ≤ cyclicExtractionValue K T τ Rel := by
  exact le_csSup hbounded certificate.mem_cyclicExtractionValues

/-- If one semantic relation implies another, every finite term for the first is also a term for the
second. -/
theorem cyclicExtractionValues_mono
    {Rel₁ Rel₂ : CyclicExtractionRelation K T}
    (hRel : ∀ power copies xSize ySize zSize,
      Rel₁ power copies xSize ySize zSize → Rel₂ power copies xSize ySize zSize) :
    cyclicExtractionValues K T τ Rel₁ ⊆ cyclicExtractionValues K T τ Rel₂ := by
  intro x hx
  rcases hx with ⟨certificate, rfl⟩
  refine ⟨CyclicExtractionCertificate.of_extraction K Rel₂ τ certificate.power certificate.copies
    certificate.xSize certificate.ySize certificate.zSize certificate.power_pos
    certificate.copies_pos certificate.xSize_pos certificate.ySize_pos certificate.zSize_pos ?_, rfl⟩
  exact hRel _ _ _ _ _ certificate.extraction

/-- A relation-parametric value set is nonempty as soon as one certificate is supplied. -/
theorem cyclicExtractionValues_nonempty_of_certificate
    {Rel : CyclicExtractionRelation K T}
    (certificate : CyclicExtractionCertificate K T τ Rel) :
    (cyclicExtractionValues K T τ Rel).Nonempty := by
  exact ⟨certificate.term, certificate.mem_cyclicExtractionValues⟩

end CertificateLemmas

end AlgebraicComplexity
