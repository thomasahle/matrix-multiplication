/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.DirectSum
import AlgebraicComplexity.Tensor.PowerCoherence

/-!
# Finite certificates for the Coppersmith--Winograd τ-value

Layer 3 (`AlgebraicComplexity/MatrixMultiplication/`). This module contains the finite,
paper-independent certificate calculus underlying the value introduced by Coppersmith and
Winograd in *Matrix multiplication via arithmetic progressions*, J. Symbolic Computation 9
(1990), §8, p. 264.

A `TauValueCertificate K T` records a positive tensor power and a constructive polynomial
degeneration

`T^{⊗N} ⊵ ⊕_h ⟨m_h,n_h,p_h⟩`.

At exponent `τ`, its finite term is

`(∑_h (m_h n_h p_h)^τ)^(1/N)`.

The supremum of these terms is `tauValue K T τ`. No asymptotic-rank theorem, matrix exponent,
or Schönhage inequality is imported here. Their consequences live in
`MatrixMultiplication/TauValueSoundness.lean`; the historical path `TauValue.lean` re-exports
both halves.

## Principal results

* `tauValueTerm`, `TauValueCertificate`, `tauValueValues`, and `tauValue` define the finite
  term, semantic extraction certificate, certificate-value set, and its supremum.
* `TauValueCertificate.ofPolynomialDegenerates`, `.ofRestricts`, and `.ofIsomorphic`
  prove monotonicity under increasingly strong tensor relations.
* `TauValueCertificate.directSumLeft` and `.directSumRight` embed an extraction into either
  summand of a binary direct sum.
* `TauValueCertificate.matrixMultiplication` gives the trivial one-summand certificate for
  `⟨a,b,c⟩`.
* `TauValueCertificate.powerDvd` transports a certificate whose length is divisible by `k`
  to the `k`th power of its source.

The full tensor-product and direct-sum value laws are proved in the companion modules
`TauValueDirectSum.lean` and `TauValueSuperadditivity.lean`. Every theorem here is finite and
constructive; zeroing is not built into the definition, because the certificate relation is the
more general polynomial degeneration.
-/

namespace AlgebraicComplexity

open Tensor
open scoped BigOperators

universe u v w

/-! ## The finite value term -/

section Term

variable {copies : ℕ}

/-- The finite `τ`-value term of one CW90 value certificate:
`(∑_h (m_h n_h p_h)^τ)^{1/N}` for a degeneration of the `N`th power.

Unlike `AlgebraicComplexity.cyclicValueTerm`, the normalizing exponent is `1/N` and not
`1/(3N)`: this is the *unsymmetrized* value of CW90's first display, whose source is a plain
tensor power rather than the three-orientation product. -/
noncomputable def tauValueTerm (τ : ℝ) (power : ℕ) (m n p : Fin copies → ℕ) : ℝ :=
  matrixMultiplicationVolumePowerSum m n p τ ^ ((power : ℝ)⁻¹)

/-- Every recorded matrix-multiplication summand has volume at least one. -/
theorem one_le_matrixMultiplicationVolume {m n p : Fin copies → ℕ}
    (hm : ∀ i, 0 < m i) (hn : ∀ i, 0 < n i) (hp : ∀ i, 0 < p i) (i : Fin copies) :
    1 ≤ (matrixMultiplicationVolume m n p i : ℝ) := by
  have : 0 < matrixMultiplicationVolume m n p i :=
    Nat.mul_pos (Nat.mul_pos (hm i) (hn i)) (hp i)
  exact_mod_cast this

/-- A positive dimension family has a positive volume power sum for every real exponent. -/
theorem matrixMultiplicationVolumePowerSum_pos {m n p : Fin copies → ℕ}
    (hcopies : 0 < copies)
    (hm : ∀ i, 0 < m i) (hn : ∀ i, 0 < n i) (hp : ∀ i, 0 < p i) (τ : ℝ) :
    0 < matrixMultiplicationVolumePowerSum m n p τ := by
  letI : Nonempty (Fin copies) := ⟨⟨0, hcopies⟩⟩
  unfold matrixMultiplicationVolumePowerSum
  refine Finset.sum_pos (fun i _ ↦ ?_) Finset.univ_nonempty
  exact Real.rpow_pos_of_pos
    (lt_of_lt_of_le zero_lt_one (one_le_matrixMultiplicationVolume hm hn hp i)) _
/-- The volume power sum is monotone in the exponent, because every volume is at least one. -/
theorem matrixMultiplicationVolumePowerSum_mono_exponent {m n p : Fin copies → ℕ}
    (hm : ∀ i, 0 < m i) (hn : ∀ i, 0 < n i) (hp : ∀ i, 0 < p i) {τ σ : ℝ} (hτσ : τ ≤ σ) :
    matrixMultiplicationVolumePowerSum m n p τ ≤
      matrixMultiplicationVolumePowerSum m n p σ := by
  unfold matrixMultiplicationVolumePowerSum
  refine Finset.sum_le_sum fun i _ ↦ ?_
  exact Real.rpow_le_rpow_of_exponent_le (one_le_matrixMultiplicationVolume hm hn hp i) hτσ

/-- The finite value term is positive. -/
theorem tauValueTerm_pos {m n p : Fin copies → ℕ} {power : ℕ}
    (hcopies : 0 < copies)
    (hm : ∀ i, 0 < m i) (hn : ∀ i, 0 < n i) (hp : ∀ i, 0 < p i) (τ : ℝ) :
    0 < tauValueTerm τ power m n p :=
  Real.rpow_pos_of_pos (matrixMultiplicationVolumePowerSum_pos hcopies hm hn hp τ) _

/-- The finite value term is monotone in the exponent `τ`. -/
theorem tauValueTerm_mono_exponent {m n p : Fin copies → ℕ} {power : ℕ}
    (hm : ∀ i, 0 < m i) (hn : ∀ i, 0 < n i) (hp : ∀ i, 0 < p i) {τ σ : ℝ} (hτσ : τ ≤ σ) :
    tauValueTerm τ power m n p ≤ tauValueTerm σ power m n p := by
  refine Real.rpow_le_rpow ?_ (matrixMultiplicationVolumePowerSum_mono_exponent hm hn hp hτσ) ?_
  · unfold matrixMultiplicationVolumePowerSum
    exact Finset.sum_nonneg fun i _ ↦ Real.rpow_nonneg (by positivity) _
  · positivity

end Term

/-! ## Value certificates and the value -/

section Definitions

variable (K : Type u) [CommSemiring K]
variable {V : Leg → Type v}
variable [∀ c, AddCommMonoid (V c)] [∀ c, Module K (V c)]

/-- **A CW90 value certificate for `T`** (`[CoppersmithWinograd1990]`, §8, p. 264): a positive
power `N`, a nonempty finite family of positive rectangular matrix dimensions, and a polynomial
degeneration of `T^{⊗N}` onto their direct sum.

The exponent `τ` is deliberately *not* a field of this structure: the extraction data does not
depend on it, and keeping it out is what makes monotonicity in `τ`
(`TauValueCertificate.term_mono`) a statement about one certificate rather than a transport
between two structure types.  This differs from `AlgebraicComplexity.CyclicExtractionCertificate`,
where `τ` is a phantom parameter. -/
structure TauValueCertificate (T : Tensor3 K V) where
  /-- The length of the tensor power that is degenerated. -/
  power : ℕ
  /-- The number of matrix-multiplication summands produced. -/
  copies : ℕ
  /-- First matrix dimension of each summand. -/
  xSize : Fin copies → ℕ
  /-- Second matrix dimension of each summand. -/
  ySize : Fin copies → ℕ
  /-- Third matrix dimension of each summand. -/
  zSize : Fin copies → ℕ
  power_pos : 0 < power
  copies_pos : 0 < copies
  xSize_pos : ∀ i, 0 < xSize i
  ySize_pos : ∀ i, 0 < ySize i
  zSize_pos : ∀ i, 0 < zSize i
  /-- The semantic degeneration `T^{⊗N} ⊵ ⊕_h ⟨m_h,n_h,p_h⟩`. -/
  degenerates : PolynomialDegenerates (Tensor.power T power)
    (matrixMultiplicationDirectSum K xSize ySize zSize)

namespace TauValueCertificate

variable {K} {T : Tensor3 K V}

/-- The numerical weight `(∑_h (m_h n_h p_h)^τ)^{1/N}` of a value certificate. -/
noncomputable def term (certificate : TauValueCertificate K T) (τ : ℝ) : ℝ :=
  tauValueTerm τ certificate.power certificate.xSize certificate.ySize certificate.zSize

/-- Every value certificate has a positive weight. -/
theorem term_pos (certificate : TauValueCertificate K T) (τ : ℝ) : 0 < certificate.term τ :=
  tauValueTerm_pos certificate.copies_pos certificate.xSize_pos certificate.ySize_pos
    certificate.zSize_pos τ

/-- **The weight of a fixed certificate is monotone in `τ`.**  This is the step that makes the
value-to-exponent theorem work: the same finite extraction is worth more at a larger exponent
because every matrix volume is at least one. -/
theorem term_mono (certificate : TauValueCertificate K T) {τ σ : ℝ} (hτσ : τ ≤ σ) :
    certificate.term τ ≤ certificate.term σ :=
  tauValueTerm_mono_exponent certificate.xSize_pos certificate.ySize_pos certificate.zSize_pos hτσ

end TauValueCertificate

/-- The set of weights of the value certificates of `T` at exponent `τ`. -/
def tauValueValues (T : Tensor3 K V) (τ : ℝ) : Set ℝ :=
  {x | ∃ certificate : TauValueCertificate K T, certificate.term τ = x}

/-- **The value `V_τ(T)`** of `[CoppersmithWinograd1990]` §8, p. 264: the supremum of the weights
of all value certificates of `T`.

No boundedness is built into the definition; `tauValueValues_bddAbove` proves it for `τ ≤ ω/3`,
which is the only regime in which the classical theory reads the supremum. -/
noncomputable def tauValue (T : Tensor3 K V) (τ : ℝ) : ℝ := sSup (tauValueValues K T τ)

end Definitions

section CertificateLemmas

variable {K : Type u} [CommSemiring K]
variable {V : Leg → Type v}
variable [∀ c, AddCommMonoid (V c)] [∀ c, Module K (V c)]
variable {T : Tensor3 K V} {τ : ℝ}

/-- Every certificate contributes its weight to the value set. -/
theorem TauValueCertificate.mem_tauValueValues (certificate : TauValueCertificate K T) (τ : ℝ) :
    certificate.term τ ∈ tauValueValues K T τ :=
  ⟨certificate, rfl⟩

/-- One certificate makes the value set nonempty. -/
theorem tauValueValues_nonempty_of_certificate (certificate : TauValueCertificate K T) (τ : ℝ) :
    (tauValueValues K T τ).Nonempty :=
  ⟨certificate.term τ, certificate.mem_tauValueValues τ⟩

/-- A certificate weight is below the value whenever the value set is bounded above. -/
theorem TauValueCertificate.le_tauValue (certificate : TauValueCertificate K T)
    (hbounded : BddAbove (tauValueValues K T τ)) :
    certificate.term τ ≤ tauValue K T τ :=
  le_csSup hbounded (certificate.mem_tauValueValues τ)

/-- **The value is monotone in `τ`.** -/
theorem tauValue_mono_exponent {σ : ℝ} (hτσ : τ ≤ σ)
    (hnonempty : (tauValueValues K T τ).Nonempty)
    (hbounded : BddAbove (tauValueValues K T σ)) :
    tauValue K T τ ≤ tauValue K T σ := by
  refine csSup_le hnonempty ?_
  rintro x ⟨certificate, rfl⟩
  exact (certificate.term_mono hτσ).trans (certificate.le_tauValue hbounded)

end CertificateLemmas

/-! ## The calculus of values -/

section Calculus

variable {K : Type u} [CommSemiring K]
variable {V : Leg → Type v} {W : Leg → Type w}
variable [∀ c, AddCommMonoid (V c)] [∀ c, Module K (V c)]
variable [∀ c, AddCommMonoid (W c)] [∀ c, Module K (W c)]

/-- **CW90's reduction law, certificate level.**  If `T` degenerates to `S`, every value
certificate of `S` is a value certificate of `T` with the same data and hence the same weight.

Proof sketch: `Tensor.PolynomialDegenerates.power` degenerates `T^{⊗N}` onto `S^{⊗N}`; compose
with the certificate's own degeneration. -/
def TauValueCertificate.ofPolynomialDegenerates {T : Tensor3 K V} {S : Tensor3 K W}
    (hdeg : PolynomialDegenerates T S) (certificate : TauValueCertificate K S) :
    TauValueCertificate K T where
  power := certificate.power
  copies := certificate.copies
  xSize := certificate.xSize
  ySize := certificate.ySize
  zSize := certificate.zSize
  power_pos := certificate.power_pos
  copies_pos := certificate.copies_pos
  xSize_pos := certificate.xSize_pos
  ySize_pos := certificate.ySize_pos
  zSize_pos := certificate.zSize_pos
  degenerates := (hdeg.power certificate.power).trans certificate.degenerates

/-- Transporting a value certificate backward along a polynomial degeneration changes only its
semantic source witness; its power, matrix dimensions, and therefore its numerical term are
unchanged. -/
@[simp] theorem TauValueCertificate.term_ofPolynomialDegenerates {T : Tensor3 K V}
    {S : Tensor3 K W} (hdeg : PolynomialDegenerates T S)
    (certificate : TauValueCertificate K S) (τ : ℝ) :
    (TauValueCertificate.ofPolynomialDegenerates hdeg certificate).term τ =
      certificate.term τ := rfl

/-- The weights of the target are among the weights of the source. -/
theorem tauValueValues_subset_of_polynomialDegenerates {T : Tensor3 K V} {S : Tensor3 K W}
    (hdeg : PolynomialDegenerates T S) (τ : ℝ) :
    tauValueValues K S τ ⊆ tauValueValues K T τ := by
  rintro x ⟨certificate, rfl⟩
  exact ⟨TauValueCertificate.ofPolynomialDegenerates hdeg certificate, rfl⟩

/-- **`A ⊵ B ⟹ V_τ(A) ≥ V_τ(B)`** (`[CoppersmithWinograd1990]`, §8, p. 264). -/
theorem tauValue_le_of_polynomialDegenerates {T : Tensor3 K V} {S : Tensor3 K W} {τ : ℝ}
    (hdeg : PolynomialDegenerates T S)
    (hnonempty : (tauValueValues K S τ).Nonempty)
    (hbounded : BddAbove (tauValueValues K T τ)) :
    tauValue K S τ ≤ tauValue K T τ :=
  csSup_le_csSup hbounded hnonempty (tauValueValues_subset_of_polynomialDegenerates hdeg τ)

/-- An exact legwise restriction is in particular a degeneration. -/
def TauValueCertificate.ofRestricts {T : Tensor3 K V} {S : Tensor3 K W}
    (hres : Restricts T S) (certificate : TauValueCertificate K S) :
    TauValueCertificate K T :=
  TauValueCertificate.ofPolynomialDegenerates (PolynomialDegenerates.of_restricts hres) certificate

/-- Value certificates transport along legwise isomorphisms. -/
def TauValueCertificate.ofIsomorphic {T : Tensor3 K V} {S : Tensor3 K W}
    (hiso : Isomorphic T S) (certificate : TauValueCertificate K S) :
    TauValueCertificate K T :=
  TauValueCertificate.ofRestricts hiso.restricts certificate

/-- **A certificate for a summand is a certificate for the direct sum** (left half of CW90's
superadditivity; see the module docstring for what is missing from the full law). -/
def TauValueCertificate.directSumLeft {T : Tensor3 K V} {S : Tensor3 K W}
    (certificate : TauValueCertificate K T) :
    TauValueCertificate K (Tensor.directSum T S) :=
  TauValueCertificate.ofRestricts (Tensor.Restricts.directSum_left T S) certificate

/-- **A certificate for a summand is a certificate for the direct sum** (right half). -/
def TauValueCertificate.directSumRight {T : Tensor3 K V} {S : Tensor3 K W}
    (certificate : TauValueCertificate K S) :
    TauValueCertificate K (Tensor.directSum T S) :=
  TauValueCertificate.ofRestricts (Tensor.Restricts.directSum_right T S) certificate

/-- `V_τ(A) ≤ V_τ(A ⊞ B)`. -/
theorem tauValue_le_tauValue_directSum_left {T : Tensor3 K V} {S : Tensor3 K W} {τ : ℝ}
    (hnonempty : (tauValueValues K T τ).Nonempty)
    (hbounded : BddAbove (tauValueValues K (Tensor.directSum T S) τ)) :
    tauValue K T τ ≤ tauValue K (Tensor.directSum T S) τ :=
  tauValue_le_of_polynomialDegenerates
    (PolynomialDegenerates.of_restricts (Tensor.Restricts.directSum_left T S))
    hnonempty hbounded

/-- `V_τ(B) ≤ V_τ(A ⊞ B)`. -/
theorem tauValue_le_tauValue_directSum_right {T : Tensor3 K V} {S : Tensor3 K W} {τ : ℝ}
    (hnonempty : (tauValueValues K S τ).Nonempty)
    (hbounded : BddAbove (tauValueValues K (Tensor.directSum T S) τ)) :
    tauValue K S τ ≤ tauValue K (Tensor.directSum T S) τ :=
  tauValue_le_of_polynomialDegenerates
    (PolynomialDegenerates.of_restricts (Tensor.Restricts.directSum_right T S))
    hnonempty hbounded

/-- **The trivial certificate of a matrix-multiplication tensor**: the first power of
`⟨a,b,c⟩` is already one summand of volume `abc`. -/
noncomputable def TauValueCertificate.matrixMultiplication (K : Type u) [CommSemiring K]
    {a b c : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    TauValueCertificate K (AlgebraicComplexity.matrixMultiplication (K := K) a b c) where
  power := 1
  copies := 1
  xSize := fun _ ↦ a
  ySize := fun _ ↦ b
  zSize := fun _ ↦ c
  power_pos := Nat.one_pos
  copies_pos := Nat.one_pos
  xSize_pos := fun _ ↦ ha
  ySize_pos := fun _ ↦ hb
  zSize_pos := fun _ ↦ hc
  degenerates := by
    refine PolynomialDegenerates.of_restricts ?_
    refine (Isomorphic.power_one (AlgebraicComplexity.matrixMultiplication (K := K) a b c)).restricts.trans
      ?_
    exact (Tensor.Isomorphic.indexedDirectSum_unique (ι := Fin 1)
      (AlgebraicComplexity.matrixMultiplication (K := K) a b c)).symm.restricts

/-- The trivial matrix-multiplication certificate has weight `(abc)^τ`. -/
@[simp] theorem TauValueCertificate.term_matrixMultiplication (K : Type u) [CommSemiring K]
    {a b c : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (τ : ℝ) :
    (TauValueCertificate.matrixMultiplication K ha hb hc).term τ = ((a * b * c : ℕ) : ℝ) ^ τ := by
  have hsum : matrixMultiplicationVolumePowerSum
      (fun _ : Fin 1 ↦ a) (fun _ : Fin 1 ↦ b) (fun _ : Fin 1 ↦ c) τ =
      ((a * b * c : ℕ) : ℝ) ^ τ := by
    simp [matrixMultiplicationVolumePowerSum, matrixMultiplicationVolume]
  show tauValueTerm τ 1 (fun _ : Fin 1 ↦ a) (fun _ : Fin 1 ↦ b) (fun _ : Fin 1 ↦ c) = _
  rw [tauValueTerm, hsum, Nat.cast_one, inv_one, Real.rpow_one]

/-- **`V_τ(⟨a,b,c⟩) ≥ (abc)^τ`.** -/
theorem rpow_le_tauValue_matrixMultiplication (K : Type u) [CommSemiring K]
    {a b c : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) {τ : ℝ}
    (hbounded : BddAbove (tauValueValues K (AlgebraicComplexity.matrixMultiplication (K := K) a b c) τ)) :
    ((a * b * c : ℕ) : ℝ) ^ τ ≤
      tauValue K (AlgebraicComplexity.matrixMultiplication (K := K) a b c) τ := by
  have := (TauValueCertificate.matrixMultiplication K ha hb hc).le_tauValue (τ := τ) hbounded
  rwa [TauValueCertificate.term_matrixMultiplication] at this

/-- **The exact power law for certificates of divisible length.**  A certificate of length `N` for
`T` with `k ∣ N` is a certificate of length `N/k` for `T^{⊗k}`, carrying the same weight sum and
hence the weight `V_τ(T)^k`.

Proof sketch: `Tensor.Isomorphic.power_power` identifies `(T^{⊗k})^{⊗(N/k)}` with `T^{⊗((N/k)·k)}`,
and `Nat.div_mul_cancel` turns that exponent into `N`. -/
noncomputable def TauValueCertificate.powerDvd {T : Tensor3 K V}
    (certificate : TauValueCertificate K T) {k : ℕ} (hk : 0 < k) (hdvd : k ∣ certificate.power) :
    TauValueCertificate K (Tensor.power T k) where
  power := certificate.power / k
  copies := certificate.copies
  xSize := certificate.xSize
  ySize := certificate.ySize
  zSize := certificate.zSize
  power_pos := Nat.div_pos (Nat.le_of_dvd certificate.power_pos hdvd) hk
  copies_pos := certificate.copies_pos
  xSize_pos := certificate.xSize_pos
  ySize_pos := certificate.ySize_pos
  zSize_pos := certificate.zSize_pos
  degenerates := by
    refine PolynomialDegenerates.trans (PolynomialDegenerates.of_restricts ?_)
      certificate.degenerates
    refine (Isomorphic.power_power T k (certificate.power / k)).restricts.trans ?_
    exact (Isomorphic.power_congr T (Nat.div_mul_cancel hdvd)).restricts

/-- The weight of the power certificate is the `k`th power of the original weight. -/
theorem TauValueCertificate.term_powerDvd {T : Tensor3 K V}
    (certificate : TauValueCertificate K T) {k : ℕ} (hk : 0 < k)
    (hdvd : k ∣ certificate.power) (τ : ℝ) :
    (certificate.powerDvd hk hdvd).term τ = certificate.term τ ^ k := by
  have hsum : (0 : ℝ) ≤ matrixMultiplicationVolumePowerSum
      certificate.xSize certificate.ySize certificate.zSize τ :=
    le_of_lt (matrixMultiplicationVolumePowerSum_pos certificate.copies_pos
      certificate.xSize_pos certificate.ySize_pos certificate.zSize_pos τ)
  have hpower : (certificate.power / k) * k = certificate.power := Nat.div_mul_cancel hdvd
  have hdivpos : 0 < certificate.power / k :=
    Nat.div_pos (Nat.le_of_dvd certificate.power_pos hdvd) hk
  show tauValueTerm τ (certificate.power / k) _ _ _ = tauValueTerm τ certificate.power _ _ _ ^ k
  unfold tauValueTerm
  rw [← Real.rpow_natCast (_ ^ ((certificate.power : ℝ)⁻¹)) k, ← Real.rpow_mul hsum]
  congr 1
  have hkR : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (hk.ne')
  have hdR : ((certificate.power / k : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (hdivpos.ne')
  have hcast : ((certificate.power : ℕ) : ℝ) = ((certificate.power / k : ℕ) : ℝ) * (k : ℝ) := by
    exact_mod_cast congrArg (fun t : ℕ ↦ (t : ℝ)) hpower.symm
  rw [hcast]
  field_simp

end Calculus

end AlgebraicComplexity
