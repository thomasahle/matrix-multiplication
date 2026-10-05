/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.TauValueDirectSum
import AlgebraicComplexity.Analysis.Subexponential

/-!
# Superadditivity of the `τ`-value under direct sums

Layer 3 (`AlgebraicComplexity/MatrixMultiplication/`).  This module proves the remaining law of

> D. Coppersmith and S. Winograd, *Matrix multiplication via arithmetic progressions*,
> J. Symbolic Computation 9 (1990), 251--280, **Section 8, page 264**
> (`[CoppersmithWinograd1990]`),

namely `V_τ(A ⊞ B) ≥ V_τ(A) + V_τ(B)`.

## Why it is harder than the product law

The two comparisons `V_τ(A) ≤ V_τ(A ⊞ B)` and `V_τ(B) ≤ V_τ(A ⊞ B)` are immediate from
`Restricts.directSum_left`.  Their sum is not: a direct sum of two disjoint extractions of
`(A ⊞ B)^{⊗M}` has weight `S₁ + S₂`, whose `M`th root is `(a^M + b^M)^{1/M}`, which tends to
`max a b`, not to `a + b`.  Recovering the sum needs *all* `binom(M,j)` blocks of the expansion

`(A ⊞ B)^{⊗M} ⊵ ⊕_{j ≤ M} binom(M,j) copies of A^{⊗j} ⊗ B^{⊗(M-j)}`,

which `Tensor/DirectSumPower.lean` supplies one Pascal step at a time, and each of whose blocks
must be degenerated separately, which is what
`Tensor.PolynomialDegenerates.directSum` makes possible.

## Why no Stirling estimate is needed

Only the blocks whose `A`-degree is divisible by the length `N₁` of the certificate for `A` — and
whose `B`-degree is divisible by the length `N₂` of the certificate for `B` — carry a known
weight.  The classical treatment recovers the lost blocks with a Stirling/entropy estimate on the
maximal binomial coefficient.  The elementary argument used here (`add_pow_le_of_multiples`)
avoids that: for `N := N₁N₂` and `r := j mod N`, the recursion `C(M,j) · j = C(M,j-1) · (M-j+1)`
gives `C(M,j) ≤ M^r · C(M,j-r)`, so **every** term of `(a+b)^M` is within the factor
`M^N · max(1, a/b)^N` of a term that *is* present.  Summing the `M+1` terms costs one more factor
of `M+1`, and the total loss `(M+1) M^N max(1,a/b)^N` is polynomial in `M`, hence subexponential.

## Principal results

* `choose_le_pow_mul_choose_sub` — `C(M,j) ≤ M^r · C(M,j-r)`.
* `add_pow_le_of_multiples` — the polynomial-loss comparison of `(a+b)^M` with the terms whose
  exponent is divisible by `N`.
* `sum_choose_convolution_succ` — the Pascal identity for the weights carried by the expansion.
* `hasTauWeight_externalPrefix_power_directSum` — **the expansion, with weights**: the mixed power
  `A^{⊗k} ⊗ B^{⊗m} ⊗ (A ⊞ B)^{⊗M}` carries the binomial convolution of the two weight sequences.
* `add_term_le_tauValue_directSum` — **`V_τ(A ⊞ B) ≥ (weight of a certificate for `A`) + (weight
  of a certificate for `B`)`**, for arbitrary certificate lengths.
* `tauValue_add_le_tauValue_directSum` — **`V_τ(A ⊞ B) ≥ V_τ(A) + V_τ(B)`**.
-/

namespace AlgebraicComplexity

open Tensor
open scoped BigOperators

universe u v w

/-! ## Two binomial-coefficient estimates -/

section Binomial

/-- Removing one from the lower index of a binomial coefficient costs at most a factor `M`. -/
theorem choose_le_mul_choose_pred {M j : ℕ} (hj : 0 < j) :
    M.choose j ≤ M * M.choose (j - 1) := by
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
  have h := Nat.choose_succ_right_eq M k
  have h1 : M.choose (k + 1) ≤ M.choose (k + 1) * (k + 1) :=
    Nat.le_mul_of_pos_right _ (by omega)
  have h2 : M.choose k * (M - k) ≤ M.choose k * M :=
    Nat.mul_le_mul_left _ (by omega)
  simp only [Nat.add_sub_cancel]
  calc M.choose (k + 1) ≤ M.choose (k + 1) * (k + 1) := h1
    _ = M.choose k * (M - k) := h
    _ ≤ M.choose k * M := h2
    _ = M * M.choose k := Nat.mul_comm _ _

/-- **`C(M,j) ≤ M^r · C(M,j-r)`.**  This is the elementary replacement for a Stirling estimate:
it bounds an arbitrary binomial coefficient by a nearby one at a polynomial cost. -/
theorem choose_le_pow_mul_choose_sub (M : ℕ) : ∀ r j : ℕ, r ≤ j →
    M.choose j ≤ M ^ r * M.choose (j - r) := by
  intro r
  induction r with
  | zero => intro j _; simp
  | succ r ih =>
      intro j hj
      have h1 : M.choose j ≤ M * M.choose (j - 1) := choose_le_mul_choose_pred (by omega)
      have h2 : M.choose (j - 1) ≤ M ^ r * M.choose (j - 1 - r) := ih (j - 1) (by omega)
      have h3 : j - 1 - r = j - (r + 1) := by omega
      calc M.choose j ≤ M * M.choose (j - 1) := h1
        _ ≤ M * (M ^ r * M.choose (j - 1 - r)) := Nat.mul_le_mul_left _ h2
        _ = M ^ (r + 1) * M.choose (j - (r + 1)) := by rw [h3]; ring

/-- **The polynomial-loss comparison.**  If every term of the binomial expansion of `(a+b)^M`
whose exponent is divisible by `N` is bounded by `Q`, then the whole expansion is bounded by
`(M+1) · M^N · max(1, a/b)^N · Q`.

Proof sketch: the term at `j` is compared with the term at `j - (j mod N)`, which is present.  The
binomial factor costs `M^{j mod N} ≤ M^N` by `choose_le_pow_mul_choose_sub`, and the geometric
factor costs `(a/b)^{j mod N} ≤ max(1, a/b)^N`.  Bounding each of the `M+1` terms by the same
quantity finishes. -/
theorem add_pow_le_of_multiples {a b : ℝ} (ha : 0 < a) (hb : 0 < b) {N M : ℕ}
    (hN : 0 < N) (hM : 0 < M) {Q : ℝ}
    (hQ : ∀ j, j ≤ M → N ∣ j → a ^ j * b ^ (M - j) * (M.choose j : ℝ) ≤ Q) :
    (a + b) ^ M ≤ ((M : ℝ) + 1) * ((M : ℝ) ^ N * (max 1 (a / b)) ^ N * Q) := by
  have hγ : (1 : ℝ) ≤ max 1 (a / b) := le_max_left _ _
  have hterm : ∀ j ∈ Finset.range (M + 1),
      a ^ j * b ^ (M - j) * (M.choose j : ℝ) ≤
        (M : ℝ) ^ N * (max 1 (a / b)) ^ N * Q := by
    intro j hjmem
    have hjM : j ≤ M := Nat.lt_succ_iff.mp (Finset.mem_range.mp hjmem)
    obtain ⟨r, j', hrN, hdvdj', hj⟩ : ∃ r j', r < N ∧ N ∣ j' ∧ j = j' + r := by
      have hdm := Nat.div_add_mod j N
      exact ⟨j % N, N * (j / N), Nat.mod_lt _ hN, ⟨j / N, rfl⟩, by omega⟩
    subst hj
    have hj'M : j' ≤ M := by omega
    have hchoose : (M.choose (j' + r) : ℝ) ≤ (M : ℝ) ^ N * (M.choose j' : ℝ) := by
      have h1 : M.choose (j' + r) ≤ M ^ r * M.choose (j' + r - r) :=
        choose_le_pow_mul_choose_sub M r (j' + r) (by omega)
      have h2 : M ^ r ≤ M ^ N := Nat.pow_le_pow_right hM (by omega)
      have h3 : M.choose (j' + r) ≤ M ^ N * M.choose j' := by
        simpa using h1.trans (Nat.mul_le_mul_right _ h2)
      exact_mod_cast h3
    have hMsplit : M - j' = (M - (j' + r)) + r := by omega
    have hab : a ^ r ≤ (max 1 (a / b)) ^ N * b ^ r := by
      have hbr : (b : ℝ) ^ r ≠ 0 := by positivity
      have hd : a ^ r = (a / b) ^ r * b ^ r := by
        rw [div_pow, div_mul_cancel₀ _ hbr]
      have h2 : (a / b) ^ r ≤ (max 1 (a / b)) ^ r :=
        pow_le_pow_left₀ (by positivity) (le_max_right _ _) r
      have h3 : (max 1 (a / b)) ^ r ≤ (max 1 (a / b)) ^ N :=
        pow_le_pow_right₀ hγ (by omega)
      calc a ^ r = (a / b) ^ r * b ^ r := hd
        _ ≤ (max 1 (a / b)) ^ N * b ^ r :=
            mul_le_mul_of_nonneg_right (h2.trans h3) (by positivity)
    have hgeom : a ^ (j' + r) * b ^ (M - (j' + r)) ≤
        (max 1 (a / b)) ^ N * (a ^ j' * b ^ (M - j')) := by
      calc a ^ (j' + r) * b ^ (M - (j' + r))
          = (a ^ j' * b ^ (M - (j' + r))) * a ^ r := by rw [pow_add]; ring
        _ ≤ (a ^ j' * b ^ (M - (j' + r))) * ((max 1 (a / b)) ^ N * b ^ r) :=
            mul_le_mul_of_nonneg_left hab (by positivity)
        _ = (max 1 (a / b)) ^ N * (a ^ j' * b ^ (M - j')) := by
            rw [hMsplit, pow_add]; ring
    calc a ^ (j' + r) * b ^ (M - (j' + r)) * (M.choose (j' + r) : ℝ)
        ≤ ((max 1 (a / b)) ^ N * (a ^ j' * b ^ (M - j'))) *
            ((M : ℝ) ^ N * (M.choose j' : ℝ)) :=
          mul_le_mul hgeom hchoose (by positivity) (by positivity)
      _ = (M : ℝ) ^ N * (max 1 (a / b)) ^ N * (a ^ j' * b ^ (M - j') * (M.choose j' : ℝ)) := by
          ring
      _ ≤ (M : ℝ) ^ N * (max 1 (a / b)) ^ N * Q :=
          mul_le_mul_of_nonneg_left (hQ j' hj'M hdvdj') (by positivity)
  rw [add_pow]
  calc ∑ j ∈ Finset.range (M + 1), a ^ j * b ^ (M - j) * (M.choose j : ℝ)
      ≤ ∑ _j ∈ Finset.range (M + 1), ((M : ℝ) ^ N * (max 1 (a / b)) ^ N * Q) :=
        Finset.sum_le_sum hterm
    _ = ((M : ℝ) + 1) * ((M : ℝ) ^ N * (max 1 (a / b)) ^ N * Q) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        push_cast
        ring

/-- **The Pascal identity for shifted binomial convolutions.**  This is the numerical shadow of
one step of the direct-sum expansion: reading one more letter either lengthens the `A`-prefix or
the `B`-prefix, and the two contributions recombine into the convolution of length `M+1`. -/
theorem sum_choose_convolution_succ (u v : ℕ → ℝ) (k m M : ℕ) :
    (∑ j ∈ Finset.range (M + 1), (M.choose j : ℝ) * u (k + (j + 1)) * v (m + (M - j))) +
        (∑ j ∈ Finset.range (M + 1), (M.choose j : ℝ) * u (k + j) * v (m + (M + 1 - j))) =
      ∑ j ∈ Finset.range (M + 2), ((M + 1).choose j : ℝ) * u (k + j) * v (m + (M + 1 - j)) := by
  have hRHS : ∑ j ∈ Finset.range (M + 2), ((M + 1).choose j : ℝ) * u (k + j) *
        v (m + (M + 1 - j)) =
      (∑ j ∈ Finset.range (M + 1), ((M + 1).choose (j + 1) : ℝ) * u (k + (j + 1)) *
          v (m + (M - j))) + u (k + 0) * v (m + (M + 1)) := by
    rw [Finset.sum_range_succ'
      (fun j ↦ ((M + 1).choose j : ℝ) * u (k + j) * v (m + (M + 1 - j))) (M + 1)]
    simp [Nat.succ_sub_succ]
  have hexp : ∑ j ∈ Finset.range (M + 1), ((M + 1).choose (j + 1) : ℝ) * u (k + (j + 1)) *
        v (m + (M - j)) =
      (∑ j ∈ Finset.range (M + 1), (M.choose j : ℝ) * u (k + (j + 1)) * v (m + (M - j))) +
        ∑ j ∈ Finset.range (M + 1), (M.choose (j + 1) : ℝ) * u (k + (j + 1)) *
          v (m + (M - j)) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [Nat.choose_succ_succ]
    push_cast
    ring
  have hsecond : (∑ j ∈ Finset.range (M + 1), (M.choose (j + 1) : ℝ) * u (k + (j + 1)) *
        v (m + (M - j))) + u (k + 0) * v (m + (M + 1)) =
      ∑ j ∈ Finset.range (M + 1), (M.choose j : ℝ) * u (k + j) * v (m + (M + 1 - j)) := by
    rw [Finset.sum_range_succ' (fun j ↦ (M.choose j : ℝ) * u (k + j) * v (m + (M + 1 - j))) M,
      Finset.sum_range_succ
        (fun j ↦ (M.choose (j + 1) : ℝ) * u (k + (j + 1)) * v (m + (M - j))) M]
    simp [Nat.choose_succ_self, Nat.succ_sub_succ]
  rw [hRHS, hexp, add_assoc, hsecond]

end Binomial

/-! ## The expansion, with weights -/

section Expansion

variable {K : Type u} [CommSemiring K]
variable {V : Leg → Type v} [∀ c, AddCommMonoid (V c)] [∀ c, Module K (V c)]
variable {W : Leg → Type w} [∀ c, AddCommMonoid (W c)] [∀ c, Module K (W c)]

/-- **The binomial expansion of a power of a direct sum, carrying weights.**

If every power `A^{⊗i}` carries the weight `u i` and every power `B^{⊗i}` carries `v i`, then the
mixed power `A^{⊗k} ⊗ B^{⊗m} ⊗ (A ⊞ B)^{⊗M}` carries the binomial convolution
`∑_j C(M,j) u(k+j) v(m+M-j)`.

Proof sketch: induction on `M`, generalizing the prefix exponents `k` and `m`.  The tensor step is
`Isomorphic.externalPrefix_power_directSum_succ`, whose two summands are handled by
`HasTauWeight.directSum`; the numerical step is `sum_choose_convolution_succ`. -/
theorem hasTauWeight_externalPrefix_power_directSum {A : Tensor3 K V} {B : Tensor3 K W} {τ : ℝ}
    {u v : ℕ → ℝ} (hu : ∀ i, HasTauWeight K (Tensor.power A i) τ (u i))
    (hv : ∀ i, HasTauWeight K (Tensor.power B i) τ (v i))
    (hu0 : ∀ i, 0 ≤ u i) (hv0 : ∀ i, 0 ≤ v i) (M : ℕ) : ∀ k m : ℕ,
    HasTauWeight K
      (Tensor.external (Tensor.external (Tensor.power A k) (Tensor.power B m))
        (Tensor.power (Tensor.directSum A B) M)) τ
      (∑ j ∈ Finset.range (M + 1), (M.choose j : ℝ) * u (k + j) * v (m + (M - j))) := by
  induction M with
  | zero =>
      intro k m
      have hbase := ((hu k).external (hv m) (hu0 k) (hv0 m)).of_restricts
        (Tensor.Isomorphic.externalPrefix_power_directSum_zero A B k m).restricts
      simpa using hbase
  | succ M ih =>
      intro k m
      have hsum := ((ih (k + 1) m).directSum (ih k (m + 1))).of_restricts
        (Tensor.Isomorphic.externalPrefix_power_directSum_succ A B k m M).restricts
      have hL : (∑ j ∈ Finset.range (M + 1), (M.choose j : ℝ) * u (k + 1 + j) *
            v (m + (M - j))) =
          ∑ j ∈ Finset.range (M + 1), (M.choose j : ℝ) * u (k + (j + 1)) * v (m + (M - j)) := by
        refine Finset.sum_congr rfl fun j _ ↦ ?_
        rw [show k + 1 + j = k + (j + 1) by omega]
      have hR : (∑ j ∈ Finset.range (M + 1), (M.choose j : ℝ) * u (k + j) *
            v (m + 1 + (M - j))) =
          ∑ j ∈ Finset.range (M + 1), (M.choose j : ℝ) * u (k + j) * v (m + (M + 1 - j)) := by
        refine Finset.sum_congr rfl fun j hj ↦ ?_
        have hjM : j ≤ M := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
        rw [show m + 1 + (M - j) = m + (M + 1 - j) by omega]
      rw [hL, hR, sum_choose_convolution_succ u v k m M] at hsum
      exact hsum

end Expansion

/-! ## Superadditivity -/

section Superadditivity

variable {K : Type u} [CommSemiring K]
variable {V : Leg → Type v} [∀ c, AddCommMonoid (V c)] [∀ c, Module K (V c)]
variable {W : Leg → Type w} [∀ c, AddCommMonoid (W c)] [∀ c, Module K (W c)]

/-- The weight sequence attached to a value certificate: the certificate's own weight, raised to
the appropriate power at every positive multiple of its length, and `0` elsewhere. -/
private noncomputable def certificateWeightSequence (a : ℝ) (N : ℕ) : ℕ → ℝ :=
  fun i ↦ if N ∣ i ∧ 0 < i then a ^ i else 0

private theorem certificateWeightSequence_nonneg {a : ℝ} (ha : 0 ≤ a) (N : ℕ) (i : ℕ) :
    0 ≤ certificateWeightSequence a N i := by
  unfold certificateWeightSequence
  split
  · positivity
  · exact le_rfl

private theorem certificateWeightSequence_eq {a : ℝ} {N i : ℕ} (hdvd : N ∣ i) (hi : 0 < i) :
    certificateWeightSequence a N i = a ^ i := if_pos ⟨hdvd, hi⟩

/-- Every power of `A` carries the weight prescribed by a certificate of `A`. -/
private theorem hasTauWeight_certificateWeightSequence {A : Tensor3 K V} {τ : ℝ}
    (certificate : TauValueCertificate K A) (i : ℕ) :
    HasTauWeight K (Tensor.power A i) τ
      (certificateWeightSequence (certificate.term τ) certificate.power i) := by
  unfold certificateWeightSequence
  split
  · rename_i h
    obtain ⟨⟨t, ht⟩, hi⟩ := h
    have ht0 : 0 < t := by
      by_contra hcon
      have htzero : t = 0 := by omega
      rw [htzero, Nat.mul_zero] at ht
      omega
    obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
    have hS : 0 < matrixMultiplicationVolumePowerSum certificate.xSize certificate.ySize
        certificate.zSize τ :=
      matrixMultiplicationVolumePowerSum_pos certificate.copies_pos certificate.xSize_pos
        certificate.ySize_pos certificate.zSize_pos τ
    have hw := (certificate.hasTauWeight τ).power_mul hS.le t'
    have hi' : i = (t' + 1) * certificate.power := by rw [ht]; ring
    subst hi'
    have hterm : certificate.term τ ^ ((t' + 1) * certificate.power) =
        matrixMultiplicationVolumePowerSum certificate.xSize certificate.ySize
          certificate.zSize τ ^ (t' + 1) := by
      show (matrixMultiplicationVolumePowerSum certificate.xSize certificate.ySize
        certificate.zSize τ ^ (((certificate.power : ℕ) : ℝ))⁻¹) ^
          ((t' + 1) * certificate.power) = _
      rw [mul_comm, pow_mul, Real.rpow_inv_natCast_pow hS.le certificate.power_pos.ne']
    rw [hterm]
    exact hw
  · exact HasTauWeight.zero _ _

/-- **Superadditivity of the value, certificate level.**

Given a value certificate for `A` of weight `a` and one for `B` of weight `b`, of arbitrary and
unrelated lengths, `V_τ(A ⊞ B) ≥ a + b`.

Proof sketch: with `N := N₁N₂` and `M := N·L`, the expansion of `(A ⊞ B)^{⊗(N₁+N₂+M)}` carries the
weight `W_M = a^{N₁} b^{N₂} ∑_{N ∣ j} C(M,j) a^j b^{M-j}`.  Comparing that restricted sum with the
full binomial expansion of `(a+b)^M` costs only the polynomial factor
`(M+1) M^N max(1,a/b)^N` (`add_pow_le_of_multiples`), and such a factor is removed from an
inequality between all powers by `Growth.le_of_pow_succ_le_subexponential_mul_pow_succ`. -/
theorem add_term_le_tauValue_directSum {A : Tensor3 K V} {B : Tensor3 K W} {τ : ℝ}
    (cA : TauValueCertificate K A) (cB : TauValueCertificate K B)
    (hbounded : BddAbove (tauValueValues K (Tensor.directSum A B) τ)) :
    cA.term τ + cB.term τ ≤ tauValue K (Tensor.directSum A B) τ := by
  classical
  set N₁ := cA.power with hN₁def
  set N₂ := cB.power with hN₂def
  set a := cA.term τ with hadef
  set b := cB.term τ with hbdef
  have hN₁ : 0 < N₁ := cA.power_pos
  have hN₂ : 0 < N₂ := cB.power_pos
  have ha : 0 < a := cA.term_pos τ
  have hb : 0 < b := cB.term_pos τ
  set N := N₁ * N₂ with hNdef
  have hN : 0 < N := Nat.mul_pos hN₁ hN₂
  set u := certificateWeightSequence a N₁ with hudef
  set v := certificateWeightSequence b N₂ with hvdef
  have hu := fun i ↦ hasTauWeight_certificateWeightSequence (τ := τ) cA i
  have hv := fun i ↦ hasTauWeight_certificateWeightSequence (τ := τ) cB i
  have hu0 : ∀ i, 0 ≤ u i := certificateWeightSequence_nonneg ha.le N₁
  have hv0 : ∀ i, 0 ≤ v i := certificateWeightSequence_nonneg hb.le N₂
  set ρ := tauValue K (Tensor.directSum A B) τ with hρdef
  set D := a ^ N₁ * b ^ N₂ with hDdef
  have hD : 0 < D := by positivity
  -- The weight carried by the expansion of length `N₁ + N₂ + M`.
  set weight : ℕ → ℝ := fun M ↦
    ∑ j ∈ Finset.range (M + 1), (M.choose j : ℝ) * u (N₁ + j) * v (N₂ + (M - j)) with hweightdef
  have hweight_nonneg : ∀ M j, 0 ≤ (M.choose j : ℝ) * u (N₁ + j) * v (N₂ + (M - j)) := by
    intro M j
    have := hu0 (N₁ + j)
    have := hv0 (N₂ + (M - j))
    positivity
  have hexpansion : ∀ M : ℕ,
      HasTauWeight K (Tensor.power (Tensor.directSum A B) (N₁ + N₂ + M)) τ (weight M) := by
    intro M
    exact (hasTauWeight_externalPrefix_power_directSum hu hv hu0 hv0 M N₁ N₂).of_restricts
      (Tensor.Restricts.power_directSum_externalPrefix A B N₁ N₂ M)
  -- The terms of the expansion at exponents divisible by `N`.
  have hterm_eq : ∀ M j, N ∣ M → j ≤ M → N ∣ j →
      (M.choose j : ℝ) * u (N₁ + j) * v (N₂ + (M - j)) =
        D * (a ^ j * b ^ (M - j) * (M.choose j : ℝ)) := by
    intro M j hNM hjM hNj
    have hN₁N : N₁ ∣ N := ⟨N₂, hNdef⟩
    have hN₂N : N₂ ∣ N := ⟨N₁, by rw [hNdef]; ring⟩
    have h₁ : N₁ ∣ j := hN₁N.trans hNj
    have h₂ : N₂ ∣ (M - j) := hN₂N.trans (Nat.dvd_sub hNM hNj)
    rw [hudef, hvdef, certificateWeightSequence_eq (dvd_add (dvd_refl N₁) h₁) (by omega),
      certificateWeightSequence_eq (dvd_add (dvd_refl N₂) h₂) (by omega)]
    rw [hDdef, pow_add, pow_add]
    ring
  -- The value bound carried by each expansion length.
  have hweight_pos : ∀ M : ℕ, N ∣ M → 0 < weight M := by
    intro M hNM
    have hmem : (0 : ℕ) ∈ Finset.range (M + 1) := Finset.mem_range.mpr (by omega)
    have hzero : (0 : ℝ) < (M.choose 0 : ℝ) * u (N₁ + 0) * v (N₂ + (M - 0)) := by
      rw [hterm_eq M 0 hNM (by omega) (dvd_zero N)]
      have hone : (0 : ℝ) < a ^ 0 * b ^ (M - 0) * (M.choose 0 : ℝ) := by
        rw [pow_zero, Nat.choose_zero_right, Nat.cast_one, one_mul, mul_one]
        exact pow_pos hb _
      exact mul_pos hD hone
    exact lt_of_lt_of_le hzero
      (Finset.single_le_sum (fun j _ ↦ hweight_nonneg M j) hmem)
  have hweight_le : ∀ M : ℕ, N ∣ M → weight M ≤ ρ ^ (N₁ + N₂ + M) := by
    intro M hNM
    have hpos := hweight_pos M hNM
    have hle := le_tauValue_of_hasTauWeight (T := Tensor.directSum A B) (N := N₁ + N₂ + M)
      (by omega) hpos (hexpansion M) hbounded
    have := pow_le_pow_left₀ (Real.rpow_nonneg hpos.le _) hle (N₁ + N₂ + M)
    rwa [Real.rpow_inv_natCast_pow hpos.le (by omega : N₁ + N₂ + M ≠ 0)] at this
  have hρpos : 0 < ρ := by
    have hle := le_tauValue_of_hasTauWeight (T := Tensor.directSum A B) (N := N₁ + N₂ + N)
      (by omega) (hweight_pos N dvd_rfl) (hexpansion N) hbounded
    exact lt_of_lt_of_le (Real.rpow_pos_of_pos (hweight_pos N dvd_rfl) _) hle
  -- The polynomial loss.
  set γ := (max 1 (a / b)) ^ N with hγdef
  have hγ0 : 0 ≤ γ := by positivity
  set C := ((N : ℝ) + 1) * (N : ℝ) ^ N * γ * ρ ^ (N₁ + N₂) / D with hCdef
  have hC0 : 0 ≤ C := by
    rw [hCdef]
    positivity
  set loss : ℕ → ℝ := fun L ↦ C * (((L + 1 : ℕ) : ℝ)) ^ (N + 1) with hlossdef
  have hloss : Growth.Subexponential loss :=
    (Growth.Subexponential.natCast_succ_pow (N + 1)).const_mul hC0
  -- The main inequality, at every positive length.
  have hmain : ∀ n : ℕ, ((a + b) ^ N) ^ (n + 1) ≤ loss (n + 1) * ((ρ ^ N)) ^ (n + 1) := by
    intro n
    set L := n + 1 with hLdef
    have hL : 0 < L := by omega
    set M := N * L with hMdef
    have hM : 0 < M := Nat.mul_pos hN hL
    have hNM : N ∣ M := ⟨L, rfl⟩
    -- Every present term is below `weight M / D`.
    have hQ : ∀ j, j ≤ M → N ∣ j → a ^ j * b ^ (M - j) * (M.choose j : ℝ) ≤ weight M / D := by
      intro j hjM hNj
      have hmem : j ∈ Finset.range (M + 1) := Finset.mem_range.mpr (by omega)
      have hsingle := Finset.single_le_sum (f := fun j ↦ (M.choose j : ℝ) * u (N₁ + j) *
        v (N₂ + (M - j))) (fun j _ ↦ hweight_nonneg M j) hmem
      rw [hterm_eq M j hNM hjM hNj] at hsingle
      rw [le_div_iff₀ hD]
      calc a ^ j * b ^ (M - j) * (M.choose j : ℝ) * D
          = D * (a ^ j * b ^ (M - j) * (M.choose j : ℝ)) := by ring
        _ ≤ weight M := hsingle
    have hexp := add_pow_le_of_multiples ha hb hN hM hQ
    -- Convert to the `L`-indexed form.
    have hMpow : (a + b) ^ M = ((a + b) ^ N) ^ L := by rw [hMdef, pow_mul]
    have hρpow : ρ ^ M = ((ρ ^ N)) ^ L := by rw [hMdef, pow_mul]
    have hfactor : ((M : ℝ) + 1) * ((M : ℝ) ^ N * γ) ≤
        ((N : ℝ) + 1) * (N : ℝ) ^ N * γ * (((L + 1 : ℕ) : ℝ)) ^ (N + 1) := by
      have h1 : ((M : ℝ) + 1) ≤ ((N : ℝ) + 1) * ((L : ℝ) + 1) := by
        rw [hMdef]
        push_cast
        nlinarith [Nat.cast_nonneg (α := ℝ) N, Nat.cast_nonneg (α := ℝ) L]
      have h2 : ((M : ℝ) ^ N) ≤ (N : ℝ) ^ N * ((L : ℝ) + 1) ^ N := by
        rw [hMdef]
        push_cast
        rw [mul_pow]
        exact mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (Nat.cast_nonneg _) (by linarith) N) (by positivity)
      have hcast : (((L + 1 : ℕ) : ℝ)) = (L : ℝ) + 1 := by push_cast; ring
      rw [hcast, pow_succ]
      calc ((M : ℝ) + 1) * ((M : ℝ) ^ N * γ)
          ≤ (((N : ℝ) + 1) * ((L : ℝ) + 1)) * (((N : ℝ) ^ N * ((L : ℝ) + 1) ^ N) * γ) := by
            refine mul_le_mul h1 ?_ (by positivity) (by positivity)
            exact mul_le_mul_of_nonneg_right h2 hγ0
        _ = ((N : ℝ) + 1) * (N : ℝ) ^ N * γ * (((L : ℝ) + 1) ^ N * ((L : ℝ) + 1)) := by ring
    -- Assemble.
    have hstep : ((a + b) ^ N) ^ L * D ≤
        (((N : ℝ) + 1) * (N : ℝ) ^ N * γ * (((L + 1 : ℕ) : ℝ)) ^ (N + 1)) * ρ ^ (N₁ + N₂) *
          ((ρ ^ N)) ^ L := by
      have hchain : (a + b) ^ M ≤ ((M : ℝ) + 1) * ((M : ℝ) ^ N * γ) * (weight M / D) := by
        calc (a + b) ^ M ≤ ((M : ℝ) + 1) * ((M : ℝ) ^ N * γ * (weight M / D)) := hexp
          _ = ((M : ℝ) + 1) * ((M : ℝ) ^ N * γ) * (weight M / D) := by ring
      have hw := hweight_le M hNM
      have hdiv : weight M / D * D = weight M := by field_simp
      have hfinal : (a + b) ^ M * D ≤ ((M : ℝ) + 1) * ((M : ℝ) ^ N * γ) * weight M := by
        calc (a + b) ^ M * D
            ≤ (((M : ℝ) + 1) * ((M : ℝ) ^ N * γ) * (weight M / D)) * D :=
              mul_le_mul_of_nonneg_right hchain hD.le
          _ = ((M : ℝ) + 1) * ((M : ℝ) ^ N * γ) * weight M := by field_simp
      have hρsplit : ρ ^ (N₁ + N₂ + M) = ρ ^ (N₁ + N₂) * ((ρ ^ N)) ^ L := by
        rw [pow_add, hρpow]
      calc ((a + b) ^ N) ^ L * D = (a + b) ^ M * D := by rw [hMpow]
        _ ≤ ((M : ℝ) + 1) * ((M : ℝ) ^ N * γ) * weight M := hfinal
        _ ≤ ((M : ℝ) + 1) * ((M : ℝ) ^ N * γ) * ρ ^ (N₁ + N₂ + M) := by
            exact mul_le_mul_of_nonneg_left hw (by positivity)
        _ = ((M : ℝ) + 1) * ((M : ℝ) ^ N * γ) * (ρ ^ (N₁ + N₂) * ((ρ ^ N)) ^ L) := by
            rw [hρsplit]
        _ ≤ (((N : ℝ) + 1) * (N : ℝ) ^ N * γ * (((L + 1 : ℕ) : ℝ)) ^ (N + 1)) *
              (ρ ^ (N₁ + N₂) * ((ρ ^ N)) ^ L) := by
            refine mul_le_mul_of_nonneg_right hfactor (by positivity)
        _ = (((N : ℝ) + 1) * (N : ℝ) ^ N * γ * (((L + 1 : ℕ) : ℝ)) ^ (N + 1)) *
              ρ ^ (N₁ + N₂) * ((ρ ^ N)) ^ L := by ring
    have hDloss : loss L * D =
        (((N : ℝ) + 1) * (N : ℝ) ^ N * γ * (((L + 1 : ℕ) : ℝ)) ^ (N + 1)) * ρ ^ (N₁ + N₂) := by
      rw [hlossdef, hCdef]
      field_simp
    have := hstep
    rw [← hDloss] at this
    have hcancel : ((a + b) ^ N) ^ L * D ≤ (loss L * ((ρ ^ N)) ^ L) * D := by
      calc ((a + b) ^ N) ^ L * D ≤ loss L * D * ((ρ ^ N)) ^ L := this
        _ = (loss L * ((ρ ^ N)) ^ L) * D := by ring
    exact le_of_mul_le_mul_right hcancel hD
  have hpow := Growth.le_of_pow_succ_le_subexponential_mul_pow_succ (by positivity) hloss hmain
  -- Take `N`th roots.
  have hab : 0 ≤ a + b := by positivity
  have hroot := Real.rpow_le_rpow (by positivity) hpow (by positivity : (0 : ℝ) ≤ ((N : ℝ))⁻¹)
  rwa [Real.pow_rpow_inv_natCast hab hN.ne', Real.pow_rpow_inv_natCast hρpos.le hN.ne'] at hroot

/-- **`V_τ(A ⊞ B) ≥ V_τ(A) + V_τ(B)`** (`[CoppersmithWinograd1990]`, §8, p. 264). -/
theorem tauValue_add_le_tauValue_directSum {A : Tensor3 K V} {B : Tensor3 K W} {τ : ℝ}
    (hA : (tauValueValues K A τ).Nonempty) (hB : (tauValueValues K B τ).Nonempty)
    (hbounded : BddAbove (tauValueValues K (Tensor.directSum A B) τ)) :
    tauValue K A τ + tauValue K B τ ≤ tauValue K (Tensor.directSum A B) τ := by
  have hstep : ∀ y ∈ tauValueValues K B τ,
      tauValue K A τ + y ≤ tauValue K (Tensor.directSum A B) τ := by
    rintro y ⟨cB, rfl⟩
    have hAle : tauValue K A τ ≤ tauValue K (Tensor.directSum A B) τ - cB.term τ := by
      refine csSup_le hA ?_
      rintro x ⟨cA, rfl⟩
      have := add_term_le_tauValue_directSum cA cB hbounded
      linarith
    linarith
  have hBle : tauValue K B τ ≤ tauValue K (Tensor.directSum A B) τ - tauValue K A τ := by
    refine csSup_le hB ?_
    intro y hy
    have := hstep y hy
    linarith
  linarith

end Superadditivity

end AlgebraicComplexity
