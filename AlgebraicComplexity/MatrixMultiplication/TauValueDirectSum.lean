/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.TauValueCalculus
import AlgebraicComplexity.Tensor.DirectSumPower

/-!
# Weighted extractions and the length-free laws of the `τ`-value

Layer 3 (`AlgebraicComplexity/MatrixMultiplication/`).  `MatrixMultiplication/TauValueCore.lean`
defines a value certificate as a degeneration of one *fixed* power `T^{⊗N}` onto a finite direct
sum of matrix-multiplication tensors, and `TauValueCalculus.lean` combines two such certificates
only when their lengths `N` agree.  This module removes the length restriction.

The device is a relation that forgets the power and the normalization:

`HasTauWeight K X τ v` — "`X` degenerates onto a finite family of matrix-multiplication tensors
whose `τ`-weight sum is at least `v`".

Unlike a `TauValueCertificate`, this relation is closed under all three structural operations
without any bookkeeping: external products multiply the weight, binary direct sums add it, and
tensor powers raise it.  A certificate of length `N` for `T` becomes a `HasTauWeight` statement for
`T^{⊗N}`, arbitrary powers of that statement are again `HasTauWeight` statements, and a positive
weight for `T^{⊗N}` converts back into a certificate.  Two certificates of coprime lengths `N₁` and
`N₂` therefore meet at the common length `N₁N₂` with the weights they had, which is exactly what
the equal-length hypothesis of `mul_tauValueTerm_le_tauValue_external` was standing in for.

The direct-sum closure is the one that needs new input from the tensor layer: it merges two
*polynomial* degenerations, which `Tensor/DirectSumPower.lean` supplies as
`PolynomialDegenerates.directSum`.  It is used here for the product law's bookkeeping and, in
`MatrixMultiplication/TauValueSuperadditivity.lean`, for CW90's superadditivity.

## Principal results

* `restricts_directSum_matrixMultiplicationDirectSum` — the binary direct sum of two finite
  matrix-multiplication direct sums is again one, indexed by `Fin (F₁ + F₂)`.
* `HasTauWeight` and its calculus: `zero`, `mono`, `of_polynomialDegenerates`, `external`,
  `directSum`, `power_succ`.
* `le_tauValue_of_hasTauWeight` — converting a positive weight for `T^{⊗N}` back into a value
  lower bound.
* `mul_tauValue_le_tauValue_external` — **`V_τ(A ⊗ B) ≥ V_τ(A) · V_τ(B)`**, with no restriction on
  the lengths of the two extractions.
* `tauValue_pow_le_tauValue_power` — **`V_τ(T^{⊗k}) ≥ V_τ(T)^k`**, with no divisibility
  hypothesis.

## References

* D. Coppersmith and S. Winograd, *Matrix multiplication via arithmetic progressions*,
  J. Symbolic Computation 9 (1990), 251--280, §8 (`[CoppersmithWinograd1990]`).
-/

namespace AlgebraicComplexity

open Tensor
open scoped BigOperators

universe u v w

/-! ## Merging two finite matrix-multiplication direct sums -/

section Merge

variable (K : Type u) [CommSemiring K]

/-- The legwise map merging two indexed matrix-multiplication direct sums into the direct sum
indexed by the disjoint union. -/
private noncomputable def mmDirectSumMergeMap {ι κ : Type w} [Fintype ι] [Fintype κ]
    (m₁ n₁ p₁ : ι → ℕ) (m₂ n₂ p₂ : κ → ℕ) : ∀ c : Leg,
    (MMDirectSumSpace K m₁ n₁ p₁ c × MMDirectSumSpace K m₂ n₂ p₂ c) →ₗ[K]
      MMDirectSumSpace K (Sum.elim m₁ m₂) (Sum.elim n₁ n₂) (Sum.elim p₁ p₂) c :=
  fun c ↦ LinearMap.coprod
    (Tensor.indexedFoldMap (K := K)
      (fun i c ↦ Tensor.indexedInclude
        (V := fun k ↦ MMSpace K (Sum.elim m₁ m₂ k) (Sum.elim n₁ n₂ k) (Sum.elim p₁ p₂ k))
        (Sum.inl i) c) c)
    (Tensor.indexedFoldMap (K := K)
      (fun j c ↦ Tensor.indexedInclude
        (V := fun k ↦ MMSpace K (Sum.elim m₁ m₂ k) (Sum.elim n₁ n₂ k) (Sum.elim p₁ p₂ k))
        (Sum.inr j) c) c)

/-- **The binary direct sum of two finite matrix-multiplication direct sums, indexed by the
disjoint union of the two index types.**

Proof sketch: the two summands occupy disjoint blocks of the pair space, so folding each of them
into the corresponding half of the merged direct sum is an exact legwise restriction. -/
theorem restricts_directSum_matrixMultiplicationDirectSum_sumElim
    {ι κ : Type w} [Fintype ι] [Fintype κ]
    (m₁ n₁ p₁ : ι → ℕ) (m₂ n₂ p₂ : κ → ℕ) :
    Restricts
      (Tensor.directSum (matrixMultiplicationDirectSum K m₁ n₁ p₁)
        (matrixMultiplicationDirectSum K m₂ n₂ p₂))
      (matrixMultiplicationDirectSum K (Sum.elim m₁ m₂) (Sum.elim n₁ n₂)
        (Sum.elim p₁ p₂)) := by
  classical
  refine ⟨mmDirectSumMergeMap K m₁ n₁ p₁ m₂ n₂ p₂, ?_⟩
  have hleft : (fun c ↦ mmDirectSumMergeMap K m₁ n₁ p₁ m₂ n₂ p₂ c ∘ₗ
      Tensor.includeLeft (K := K) c) =
      Tensor.indexedFoldMap (K := K) (V := fun i ↦ MMSpace K (m₁ i) (n₁ i) (p₁ i))
        (fun i c ↦ Tensor.indexedInclude
          (V := fun k ↦ MMSpace K (Sum.elim m₁ m₂ k) (Sum.elim n₁ n₂ k) (Sum.elim p₁ p₂ k))
          (Sum.inl i) c) := by
    funext c
    exact LinearMap.coprod_inl _ _
  have hright : (fun c ↦ mmDirectSumMergeMap K m₁ n₁ p₁ m₂ n₂ p₂ c ∘ₗ
      Tensor.includeRight (K := K) c) =
      Tensor.indexedFoldMap (K := K) (V := fun j ↦ MMSpace K (m₂ j) (n₂ j) (p₂ j))
        (fun j c ↦ Tensor.indexedInclude
          (V := fun k ↦ MMSpace K (Sum.elim m₁ m₂ k) (Sum.elim n₁ n₂ k) (Sum.elim p₁ p₂ k))
          (Sum.inr j) c) := by
    funext c
    exact LinearMap.coprod_inr _ _
  unfold matrixMultiplicationDirectSum
  rw [Tensor.directSum, LinearMap.map_add, Tensor.map_map_comp, Tensor.map_map_comp,
    hleft, hright]
  conv_rhs =>
    unfold Tensor.indexedDirectSum
    rw [Fintype.sum_sum_type]
  congr 1
  · exact Tensor.map_indexedFoldMap_indexedDirectSum _ _
  · exact Tensor.map_indexedFoldMap_indexedDirectSum _ _

/-- The volume power sum of a disjoint union is the sum of the two volume power sums. -/
theorem matrixMultiplicationVolumePowerSum_sumElim
    {ι κ : Type w} [Fintype ι] [Fintype κ]
    (m₁ n₁ p₁ : ι → ℕ) (m₂ n₂ p₂ : κ → ℕ) (τ : ℝ) :
    matrixMultiplicationVolumePowerSum (Sum.elim m₁ m₂) (Sum.elim n₁ n₂) (Sum.elim p₁ p₂) τ =
      matrixMultiplicationVolumePowerSum m₁ n₁ p₁ τ +
        matrixMultiplicationVolumePowerSum m₂ n₂ p₂ τ := by
  unfold matrixMultiplicationVolumePowerSum matrixMultiplicationVolume
  rw [Fintype.sum_sum_type]
  simp

/-- **The binary direct sum of two finite matrix-multiplication direct sums**, reindexed by the
numerical copy index `Fin (F₁ + F₂)`. -/
theorem restricts_directSum_matrixMultiplicationDirectSum {F₁ F₂ : ℕ}
    (m₁ n₁ p₁ : Fin F₁ → ℕ) (m₂ n₂ p₂ : Fin F₂ → ℕ) :
    Restricts
      (Tensor.directSum (matrixMultiplicationDirectSum K m₁ n₁ p₁)
        (matrixMultiplicationDirectSum K m₂ n₂ p₂))
      (matrixMultiplicationDirectSum K
        (fun k : Fin (F₁ + F₂) ↦ Sum.elim m₁ m₂ (finSumFinEquiv.symm k))
        (fun k : Fin (F₁ + F₂) ↦ Sum.elim n₁ n₂ (finSumFinEquiv.symm k))
        (fun k : Fin (F₁ + F₂) ↦ Sum.elim p₁ p₂ (finSumFinEquiv.symm k))) := by
  refine (restricts_directSum_matrixMultiplicationDirectSum_sumElim K m₁ n₁ p₁ m₂ n₂ p₂).trans ?_
  refine Tensor.Restricts.indexedDirectSum_equiv (finSumFinEquiv (m := F₁) (n := F₂)) ?_
  intro q
  have hq : finSumFinEquiv.symm (finSumFinEquiv q) = q :=
    Equiv.symm_apply_apply _ _
  change Restricts _ (matrixMultiplication (K := K)
    (Sum.elim m₁ m₂ (finSumFinEquiv.symm (finSumFinEquiv q)))
    (Sum.elim n₁ n₂ (finSumFinEquiv.symm (finSumFinEquiv q)))
    (Sum.elim p₁ p₂ (finSumFinEquiv.symm (finSumFinEquiv q))))
  rw [hq]
  exact (Tensor.Isomorphic.refl
    (matrixMultiplication (K := K) (Sum.elim m₁ m₂ q)
      (Sum.elim n₁ n₂ q) (Sum.elim p₁ p₂ q))).restricts

/-- The volume power sum of the reindexed disjoint union. -/
theorem matrixMultiplicationVolumePowerSum_finSumFinEquiv {F₁ F₂ : ℕ}
    (m₁ n₁ p₁ : Fin F₁ → ℕ) (m₂ n₂ p₂ : Fin F₂ → ℕ) (τ : ℝ) :
    matrixMultiplicationVolumePowerSum
        (fun k : Fin (F₁ + F₂) ↦ Sum.elim m₁ m₂ (finSumFinEquiv.symm k))
        (fun k : Fin (F₁ + F₂) ↦ Sum.elim n₁ n₂ (finSumFinEquiv.symm k))
        (fun k : Fin (F₁ + F₂) ↦ Sum.elim p₁ p₂ (finSumFinEquiv.symm k)) τ =
      matrixMultiplicationVolumePowerSum m₁ n₁ p₁ τ +
        matrixMultiplicationVolumePowerSum m₂ n₂ p₂ τ := by
  have hshift : matrixMultiplicationVolumePowerSum
      (fun k : Fin (F₁ + F₂) ↦ Sum.elim m₁ m₂ (finSumFinEquiv.symm k))
      (fun k : Fin (F₁ + F₂) ↦ Sum.elim n₁ n₂ (finSumFinEquiv.symm k))
      (fun k : Fin (F₁ + F₂) ↦ Sum.elim p₁ p₂ (finSumFinEquiv.symm k)) τ =
      matrixMultiplicationVolumePowerSum (Sum.elim m₁ m₂) (Sum.elim n₁ n₂) (Sum.elim p₁ p₂) τ := by
    unfold matrixMultiplicationVolumePowerSum matrixMultiplicationVolume
    rw [← Equiv.sum_comp (finSumFinEquiv (m := F₁) (n := F₂))]
    simp only [Equiv.symm_apply_apply]
  rw [hshift, matrixMultiplicationVolumePowerSum_sumElim]

/-- Every volume power sum is nonnegative. -/
theorem matrixMultiplicationVolumePowerSum_nonneg {ι : Type w} [Fintype ι]
    (m n p : ι → ℕ) (τ : ℝ) : 0 ≤ matrixMultiplicationVolumePowerSum m n p τ := by
  unfold matrixMultiplicationVolumePowerSum
  exact Finset.sum_nonneg fun i _ ↦ Real.rpow_nonneg (by positivity) _

end Merge

/-! ## Weighted extractions -/

section Weight

variable (K : Type u) [CommSemiring K]
variable {V : Leg → Type v} [∀ c, AddCommMonoid (V c)] [∀ c, Module K (V c)]
variable {W : Leg → Type w} [∀ c, AddCommMonoid (W c)] [∀ c, Module K (W c)]

/-- **`X` degenerates onto a finite family of matrix-multiplication tensors of total `τ`-weight at
least `value`.**

This is a value certificate with the power and the `N`th root removed, and with the number of
summands allowed to be zero.  Both relaxations are deliberate: forgetting the power is what makes
the relation closed under products of *unequal* lengths, and allowing the empty family is what
lets a client record "no information about this power of `A`" as the weight `0` rather than having
to exclude it from a sum. -/
def HasTauWeight (X : Tensor3 K V) (τ value : ℝ) : Prop :=
  ∃ (copies : ℕ) (xSize ySize zSize : Fin copies → ℕ),
    (∀ i, 0 < xSize i) ∧ (∀ i, 0 < ySize i) ∧ (∀ i, 0 < zSize i) ∧
      PolynomialDegenerates X (matrixMultiplicationDirectSum K xSize ySize zSize) ∧
      value ≤ matrixMultiplicationVolumePowerSum xSize ySize zSize τ

variable {K}

/-- The empty family is available for every tensor, and carries weight zero. -/
theorem HasTauWeight.zero (X : Tensor3 K V) (τ : ℝ) : HasTauWeight K X τ 0 := by
  refine ⟨0, (fun _ ↦ 1), (fun _ ↦ 1), (fun _ ↦ 1), (fun i ↦ i.elim0), (fun i ↦ i.elim0),
    (fun i ↦ i.elim0), ?_, ?_⟩
  · have hempty : matrixMultiplicationDirectSum K (fun _ : Fin 0 ↦ 1) (fun _ : Fin 0 ↦ 1)
        (fun _ : Fin 0 ↦ 1) = 0 := by
      unfold matrixMultiplicationDirectSum
      exact Tensor.indexedDirectSum_isEmpty _
    rw [hempty]
    exact PolynomialDegenerates.of_restricts (Tensor.Restricts.zeroTarget X)
  · unfold matrixMultiplicationVolumePowerSum
    simp

/-- A weighted extraction bounds every smaller weight. -/
theorem HasTauWeight.mono {X : Tensor3 K V} {τ value value' : ℝ}
    (h : HasTauWeight K X τ value) (hle : value' ≤ value) : HasTauWeight K X τ value' := by
  obtain ⟨copies, m, n, p, hm, hn, hp, hdeg, hval⟩ := h
  exact ⟨copies, m, n, p, hm, hn, hp, hdeg, hle.trans hval⟩

/-- Weighted extractions pull back along degenerations. -/
theorem HasTauWeight.of_polynomialDegenerates {X : Tensor3 K V} {Y : Tensor3 K W} {τ value : ℝ}
    (hdeg : PolynomialDegenerates X Y) (h : HasTauWeight K Y τ value) :
    HasTauWeight K X τ value := by
  obtain ⟨copies, m, n, p, hm, hn, hp, hdegY, hval⟩ := h
  exact ⟨copies, m, n, p, hm, hn, hp, hdeg.trans hdegY, hval⟩

/-- Weighted extractions pull back along exact restrictions. -/
theorem HasTauWeight.of_restricts {X : Tensor3 K V} {Y : Tensor3 K W} {τ value : ℝ}
    (hres : Restricts X Y) (h : HasTauWeight K Y τ value) : HasTauWeight K X τ value :=
  h.of_polynomialDegenerates (PolynomialDegenerates.of_restricts hres)

/-- **Weights multiply under external products.** -/
theorem HasTauWeight.external {X : Tensor3 K V} {Y : Tensor3 K W} {τ a b : ℝ}
    (hX : HasTauWeight K X τ a) (hY : HasTauWeight K Y τ b) (_ha : 0 ≤ a) (hb : 0 ≤ b) :
    HasTauWeight K (Tensor.external X Y) τ (a * b) := by
  obtain ⟨F₁, m₁, n₁, p₁, hm₁, hn₁, hp₁, hdeg₁, hval₁⟩ := hX
  obtain ⟨F₂, m₂, n₂, p₂, hm₂, hn₂, hp₂, hdeg₂, hval₂⟩ := hY
  refine ⟨F₁ * F₂,
    (fun i ↦ m₁ (finProdFinEquiv.symm i).1 * m₂ (finProdFinEquiv.symm i).2),
    (fun i ↦ n₁ (finProdFinEquiv.symm i).1 * n₂ (finProdFinEquiv.symm i).2),
    (fun i ↦ p₁ (finProdFinEquiv.symm i).1 * p₂ (finProdFinEquiv.symm i).2),
    (fun _ ↦ Nat.mul_pos (hm₁ _) (hm₂ _)), (fun _ ↦ Nat.mul_pos (hn₁ _) (hn₂ _)),
    (fun _ ↦ Nat.mul_pos (hp₁ _) (hp₂ _)), ?_, ?_⟩
  · exact (hdeg₁.external hdeg₂).trans (PolynomialDegenerates.of_restricts
      (restricts_external_matrixMultiplicationDirectSum K m₁ n₁ p₁ m₂ n₂ p₂))
  · rw [matrixMultiplicationVolumePowerSum_finProdFinEquiv]
    exact mul_le_mul hval₁ hval₂ hb (matrixMultiplicationVolumePowerSum_nonneg m₁ n₁ p₁ τ)

/-- **Weights add under binary direct sums.**

This is the step that needs `Tensor.PolynomialDegenerates.directSum`: the two blocks are
degenerated independently, at leading degrees that the indexed theory synchronizes. -/
theorem HasTauWeight.directSum {X : Tensor3 K V} {Y : Tensor3 K W} {τ a b : ℝ}
    (hX : HasTauWeight K X τ a) (hY : HasTauWeight K Y τ b) :
    HasTauWeight K (Tensor.directSum X Y) τ (a + b) := by
  obtain ⟨F₁, m₁, n₁, p₁, hm₁, hn₁, hp₁, hdeg₁, hval₁⟩ := hX
  obtain ⟨F₂, m₂, n₂, p₂, hm₂, hn₂, hp₂, hdeg₂, hval₂⟩ := hY
  have hpos : ∀ {f₁ : Fin F₁ → ℕ} {f₂ : Fin F₂ → ℕ}, (∀ i, 0 < f₁ i) → (∀ j, 0 < f₂ j) →
      ∀ k : Fin (F₁ + F₂), 0 < Sum.elim f₁ f₂ (finSumFinEquiv.symm k) := by
    intro f₁ f₂ h₁ h₂ k
    rcases finSumFinEquiv.symm k with i | j
    · exact h₁ i
    · exact h₂ j
  refine ⟨F₁ + F₂,
    (fun k ↦ Sum.elim m₁ m₂ (finSumFinEquiv.symm k)),
    (fun k ↦ Sum.elim n₁ n₂ (finSumFinEquiv.symm k)),
    (fun k ↦ Sum.elim p₁ p₂ (finSumFinEquiv.symm k)),
    hpos hm₁ hm₂, hpos hn₁ hn₂, hpos hp₁ hp₂, ?_, ?_⟩
  · exact (hdeg₁.directSum hdeg₂).trans (PolynomialDegenerates.of_restricts
      (restricts_directSum_matrixMultiplicationDirectSum K m₁ n₁ p₁ m₂ n₂ p₂))
  · rw [matrixMultiplicationVolumePowerSum_finSumFinEquiv]
    exact add_le_add hval₁ hval₂

/-- **Weights raise to powers.**  Only positive exponents are available: the zeroth power of `X`
is the tensor unit, whose value is not implied by any extraction from `X`. -/
theorem HasTauWeight.power_succ {X : Tensor3 K V} {τ value : ℝ}
    (h : HasTauWeight K X τ value) (hvalue : 0 ≤ value) (k : ℕ) :
    HasTauWeight K (Tensor.power X (k + 1)) τ (value ^ (k + 1)) := by
  induction k with
  | zero =>
      have := h.of_restricts (Tensor.Isomorphic.power_one X).restricts
      simpa using this
  | succ k ih =>
      have hres : Restricts (Tensor.power X (k + 1 + 1))
          (Tensor.external (Tensor.power X (k + 1)) X) :=
        (Tensor.isomorphic_external_power X (k + 1) 1).symm.restricts.trans
          (Tensor.Restricts.external (Tensor.Restricts.refl _)
            (Tensor.Isomorphic.power_one X).restricts)
      have hprod := (ih.external h (by positivity) hvalue).of_restricts hres
      have hpow : value ^ (k + 1) * value = value ^ (k + 1 + 1) := by ring
      rwa [hpow] at hprod

/-- A value certificate is a weighted extraction of the power it degenerates. -/
theorem TauValueCertificate.hasTauWeight {T : Tensor3 K V}
    (certificate : TauValueCertificate K T) (τ : ℝ) :
    HasTauWeight K (Tensor.power T certificate.power) τ
      (matrixMultiplicationVolumePowerSum certificate.xSize certificate.ySize
        certificate.zSize τ) :=
  ⟨certificate.copies, certificate.xSize, certificate.ySize, certificate.zSize,
    certificate.xSize_pos, certificate.ySize_pos, certificate.zSize_pos,
    certificate.degenerates, le_rfl⟩

/-- **A positive weight for `T^{⊗N}` is a value lower bound for `T`.**

Proof sketch: a positive weight forces the extracted family to be nonempty, so the extraction data
is a genuine `TauValueCertificate` of length `N`; its weight is at least `value ^ (1/N)`. -/
theorem le_tauValue_of_hasTauWeight {T : Tensor3 K V} {τ value : ℝ} {N : ℕ}
    (hN : 0 < N) (hvalue : 0 < value)
    (h : HasTauWeight K (Tensor.power T N) τ value)
    (hbounded : BddAbove (tauValueValues K T τ)) :
    value ^ ((N : ℝ)⁻¹) ≤ tauValue K T τ := by
  obtain ⟨copies, m, n, p, hm, hn, hp, hdeg, hval⟩ := h
  have hcopies : 0 < copies := by
    rcases Nat.eq_zero_or_pos copies with hzero | hpos
    · exfalso
      subst hzero
      have : matrixMultiplicationVolumePowerSum m n p τ = 0 := by
        unfold matrixMultiplicationVolumePowerSum
        simp
      rw [this] at hval
      linarith
    · exact hpos
  let certificate : TauValueCertificate K T :=
    { power := N, copies := copies, xSize := m, ySize := n, zSize := p,
      power_pos := hN, copies_pos := hcopies, xSize_pos := hm, ySize_pos := hn,
      zSize_pos := hp, degenerates := hdeg }
  refine le_trans ?_ (certificate.le_tauValue (τ := τ) hbounded)
  show value ^ ((N : ℝ)⁻¹) ≤ tauValueTerm τ N m n p
  exact Real.rpow_le_rpow hvalue.le hval (by positivity)

end Weight

/-! ## Supermultiplicativity and the power law -/

section Laws

variable {K : Type u} [CommSemiring K]
variable {V : Leg → Type v} [∀ c, AddCommMonoid (V c)] [∀ c, Module K (V c)]
variable {W : Leg → Type w} [∀ c, AddCommMonoid (W c)] [∀ c, Module K (W c)]

/-- A weighted extraction of `T^{⊗N}` gives one of every positive multiple of `N`. -/
theorem HasTauWeight.power_mul {T : Tensor3 K V} {τ value : ℝ} {N : ℕ}
    (h : HasTauWeight K (Tensor.power T N) τ value) (hvalue : 0 ≤ value) (k : ℕ) :
    HasTauWeight K (Tensor.power T ((k + 1) * N)) τ (value ^ (k + 1)) :=
  (h.power_succ hvalue k).of_restricts
    (Tensor.Isomorphic.power_power T N (k + 1)).symm.restricts

/-- Commuting a natural power past a real power. -/
private theorem rpow_natPow_comm {S : ℝ} (hS : 0 ≤ S) (k : ℕ) (x : ℝ) :
    (S ^ k) ^ x = (S ^ x) ^ k := by
  rw [← Real.rpow_natCast S k, ← Real.rpow_natCast (S ^ x) k, ← Real.rpow_mul hS,
    ← Real.rpow_mul hS, mul_comm]

/-- Two weight sums at lengths `N₁` and `N₂` meet at the length `N₁N₂` with the weights they had:
the `N₁N₂`th root of `S₁^{N₂} S₂^{N₁}` is the product of the `N₁`th root of `S₁` and the `N₂`th
root of `S₂`. -/
theorem rpow_inv_natCast_mul_pow {S₁ S₂ : ℝ} (h₁ : 0 < S₁) (h₂ : 0 < S₂) {N₁ N₂ : ℕ}
    (hN₁ : 0 < N₁) (hN₂ : 0 < N₂) :
    (S₁ ^ N₂ * S₂ ^ N₁) ^ (((N₁ * N₂ : ℕ) : ℝ))⁻¹ =
      S₁ ^ ((N₁ : ℝ))⁻¹ * S₂ ^ ((N₂ : ℝ))⁻¹ := by
  have hN₁R : (N₁ : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN₁.ne'
  have hN₂R : (N₂ : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN₂.ne'
  have e₁ : (N₂ : ℝ) * (((N₁ * N₂ : ℕ) : ℝ))⁻¹ = ((N₁ : ℝ))⁻¹ := by
    push_cast
    field_simp
  have e₂ : (N₁ : ℝ) * (((N₁ * N₂ : ℕ) : ℝ))⁻¹ = ((N₂ : ℝ))⁻¹ := by
    push_cast
    field_simp
  rw [Real.mul_rpow (by positivity) (by positivity),
    ← Real.rpow_natCast S₁ N₂, ← Real.rpow_natCast S₂ N₁,
    ← Real.rpow_mul h₁.le, ← Real.rpow_mul h₂.le, e₁, e₂]

/-- **Supermultiplicativity of the value, certificate level, with no length restriction.**

Two certificates of arbitrary lengths `N₁` and `N₂` are raised to the common length `N₁N₂` — an
operation that leaves both weights unchanged — and then multiplied.  This is the length-free
replacement for `mul_tauValueTerm_le_tauValue_external`. -/
theorem mul_term_le_tauValue_external {A : Tensor3 K V} {B : Tensor3 K W} {τ : ℝ}
    (c₁ : TauValueCertificate K A) (c₂ : TauValueCertificate K B)
    (hbounded : BddAbove (tauValueValues K (Tensor.external A B) τ)) :
    c₁.term τ * c₂.term τ ≤ tauValue K (Tensor.external A B) τ := by
  obtain ⟨k₁, hk₁⟩ : ∃ k, c₁.power = k + 1 := ⟨c₁.power - 1, by have := c₁.power_pos; omega⟩
  obtain ⟨k₂, hk₂⟩ : ∃ k, c₂.power = k + 1 := ⟨c₂.power - 1, by have := c₂.power_pos; omega⟩
  have hS₁ : 0 < matrixMultiplicationVolumePowerSum c₁.xSize c₁.ySize c₁.zSize τ :=
    matrixMultiplicationVolumePowerSum_pos c₁.copies_pos c₁.xSize_pos c₁.ySize_pos
      c₁.zSize_pos τ
  have hS₂ : 0 < matrixMultiplicationVolumePowerSum c₂.xSize c₂.ySize c₂.zSize τ :=
    matrixMultiplicationVolumePowerSum_pos c₂.copies_pos c₂.xSize_pos c₂.ySize_pos
      c₂.zSize_pos τ
  have hA : HasTauWeight K (Tensor.power A (c₁.power * c₂.power)) τ
      (matrixMultiplicationVolumePowerSum c₁.xSize c₁.ySize c₁.zSize τ ^ c₂.power) := by
    have h := (c₁.hasTauWeight τ).power_mul hS₁.le k₂
    rw [← hk₂] at h
    rwa [Nat.mul_comm] at h
  have hB : HasTauWeight K (Tensor.power B (c₁.power * c₂.power)) τ
      (matrixMultiplicationVolumePowerSum c₂.xSize c₂.ySize c₂.zSize τ ^ c₁.power) := by
    have h := (c₂.hasTauWeight τ).power_mul hS₂.le k₁
    rw [← hk₁] at h
    exact h
  have hN : 0 < c₁.power * c₂.power := Nat.mul_pos c₁.power_pos c₂.power_pos
  have hpow := (hA.external hB (by positivity) (by positivity)).of_restricts
    (Tensor.Isomorphic.power_external_of_pos A B hN).restricts
  have hle := le_tauValue_of_hasTauWeight (T := Tensor.external A B)
    (N := c₁.power * c₂.power) hN
    (by positivity) hpow hbounded
  rwa [rpow_inv_natCast_mul_pow hS₁ hS₂ c₁.power_pos c₂.power_pos] at hle

/-- Multiplying a supremum of a nonempty set by a positive constant. -/
private theorem mul_csSup_le {S : Set ℝ} (hS : S.Nonempty) {x r : ℝ} (hx : 0 < x)
    (h : ∀ y ∈ S, x * y ≤ r) : x * sSup S ≤ r := by
  have hub : ∀ y ∈ S, y ≤ r / x := by
    intro y hy
    rw [le_div_iff₀ hx]
    calc y * x = x * y := mul_comm _ _
      _ ≤ r := h y hy
  have hsup : sSup S ≤ r / x := csSup_le hS hub
  calc x * sSup S ≤ x * (r / x) := mul_le_mul_of_nonneg_left hsup hx.le
    _ = r := by field_simp

/-- **`V_τ(A ⊗ B) ≥ V_τ(A) · V_τ(B)`** (`[CoppersmithWinograd1990]`, §8, p. 264).

The extractions witnessing the two values are not required to have a common length; that
restriction of `mul_tauValueTerm_le_tauValue_external` is removed by passing through
`HasTauWeight`. -/
theorem mul_tauValue_le_tauValue_external {A : Tensor3 K V} {B : Tensor3 K W} {τ : ℝ}
    (hA : (tauValueValues K A τ).Nonempty) (hboundedA : BddAbove (tauValueValues K A τ))
    (hB : (tauValueValues K B τ).Nonempty)
    (hbounded : BddAbove (tauValueValues K (Tensor.external A B) τ)) :
    tauValue K A τ * tauValue K B τ ≤ tauValue K (Tensor.external A B) τ := by
  obtain ⟨x, cA, rfl⟩ := hA
  have hApos : 0 < tauValue K A τ :=
    lt_of_lt_of_le (cA.term_pos τ) (cA.le_tauValue hboundedA)
  refine mul_csSup_le hB hApos ?_
  rintro y ⟨c₂, rfl⟩
  rw [mul_comm]
  refine mul_csSup_le ⟨cA.term τ, cA.mem_tauValueValues τ⟩ (c₂.term_pos τ) ?_
  rintro z ⟨c₁, rfl⟩
  rw [mul_comm]
  exact mul_term_le_tauValue_external c₁ c₂ hbounded

/-- **The power law, certificate level, with no divisibility hypothesis.**  Every certificate of
`T`, of any length, has its `k`th power available as a value of `T^{⊗k}`. -/
theorem term_pow_le_tauValue_power {T : Tensor3 K V} {τ : ℝ}
    (certificate : TauValueCertificate K T) {k : ℕ} (hk : 0 < k)
    (hbounded : BddAbove (tauValueValues K (Tensor.power T k) τ)) :
    certificate.term τ ^ k ≤ tauValue K (Tensor.power T k) τ := by
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  have hS : 0 < matrixMultiplicationVolumePowerSum certificate.xSize certificate.ySize
      certificate.zSize τ :=
    matrixMultiplicationVolumePowerSum_pos certificate.copies_pos certificate.xSize_pos
      certificate.ySize_pos certificate.zSize_pos τ
  have hres : Restricts (Tensor.power (Tensor.power T (k' + 1)) certificate.power)
      (Tensor.power T ((k' + 1) * certificate.power)) :=
    ((Tensor.Isomorphic.power_power T (k' + 1) certificate.power).trans
      (Tensor.Isomorphic.power_congr T
        (Nat.mul_comm certificate.power (k' + 1)))).restricts
  have hw := ((certificate.hasTauWeight τ).power_mul hS.le k').of_restricts hres
  have hle := le_tauValue_of_hasTauWeight (T := Tensor.power T (k' + 1))
    (N := certificate.power) certificate.power_pos (by positivity) hw hbounded
  rwa [rpow_natPow_comm hS.le] at hle

/-- **`V_τ(T^{⊗k}) ≥ V_τ(T)^k`** (`[CoppersmithWinograd1990]`, §8, p. 264), with no divisibility
hypothesis on the lengths of the certificates. -/
theorem tauValue_pow_le_tauValue_power {T : Tensor3 K V} {τ : ℝ} {k : ℕ} (hk : 0 < k)
    (hne : (tauValueValues K T τ).Nonempty) (hboundedT : BddAbove (tauValueValues K T τ))
    (hbounded : BddAbove (tauValueValues K (Tensor.power T k) τ)) :
    tauValue K T τ ^ k ≤ tauValue K (Tensor.power T k) τ := by
  obtain ⟨x, cT, rfl⟩ := hne
  have hTpos : 0 < tauValue K T τ :=
    lt_of_lt_of_le (cT.term_pos τ) (cT.le_tauValue hboundedT)
  have hrpos : 0 < tauValue K (Tensor.power T k) τ :=
    lt_of_lt_of_le (pow_pos (cT.term_pos τ) k) (term_pow_le_tauValue_power cT hk hbounded)
  have hub : ∀ y ∈ tauValueValues K T τ,
      y ≤ tauValue K (Tensor.power T k) τ ^ ((k : ℝ))⁻¹ := by
    rintro y ⟨c, rfl⟩
    have h1 : c.term τ ^ k ≤ tauValue K (Tensor.power T k) τ :=
      term_pow_le_tauValue_power c hk hbounded
    have h2 := Real.rpow_le_rpow (pow_nonneg (c.term_pos τ).le k) h1
      (by positivity : (0 : ℝ) ≤ ((k : ℝ))⁻¹)
    rwa [Real.pow_rpow_inv_natCast (c.term_pos τ).le hk.ne'] at h2
  have hsup := csSup_le ⟨cT.term τ, cT.mem_tauValueValues τ⟩ hub
  have := pow_le_pow_left₀ hTpos.le hsup k
  rwa [Real.rpow_inv_natCast_pow hrpos.le hk.ne'] at this

end Laws

end AlgebraicComplexity
