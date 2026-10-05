/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.AsymmetricGlobalBudget
import AlgebraicComplexity.MatrixMultiplication.SixSymmetrizedValue
import AlgebraicComplexity.MatrixMultiplication.TauValue
import AlgebraicComplexity.Tensor.CompatibilityZeroing
import AlgebraicComplexity.Tensor.IndexedDegeneration

/-!
# The asymmetric global value theorem

Layer 3 (`AlgebraicComplexity/MatrixMultiplication/`).  This module assembles the stages of the
Duan--Wu--Zhou campaign into

> R. Duan, H. Wu and R. Zhou, *Faster Matrix Multiplication via Asymmetric Hashing*,
> arXiv:2210.10173v5, **§6 (`global_value.tex`)**, `eq:numeric_conclusion_g`
> (`[DuanWuZhou2022]`):
>
> `V^{(6)}_τ(T) ≥ min( ᾱ_ν·ᾱ_X / max_{α'∈D_α} ᾱ_{ν'} , ᾱ_Z/ᾱ_p ) · ᾱ_val`.

## Where the `min` comes from

`[DuanWuZhou2022]` never derive the minimum; it appears fully formed in the displayed conclusion.
It is in fact forced by the *modulus*.  Asymmetric hashing retains `N_α/M` good triples, and
`claim:hole_frac_low` needs `M ≥ M₀ = 8·max(N_triple/N_X, N_α·p_comp/N_Z)`, so the retained count
is

`N_α / max(N_triple/N_X, N_α·p_comp/N_Z) = min(N_α·N_X/N_triple, N_Z/p_comp)`,

which in rate coordinates is exactly the displayed minimum.  `GlobalRateData.copyRate` is defined
as the *quotient by the maximum* — the shape the pipeline produces — and `copyRate_eq_min` proves
that it equals `[DuanWuZhou2022]`'s minimum.  The maximum itself is
`AsymmetricGlobal.globalModulusBound`, whose two projections are consumed by two different layers
(affine hashing and the combination-loss counting).

**Watchlist item 2 is enforced by the data structure.**  §6.3's parameter table omits the
hash-loss factor `N_α / max_{α'∈D_α} N_{α'}`, although the bound it claims contains it.  Here
`GlobalRateData.hashLossRate` is a mandatory field, `GlobalRateData.hashLoss` names the omitted
ratio, and `branchHashing_eq_xRate_mul_hashLoss` displays the first branch as `ᾱ_X · (hash loss)`,
so a client cannot silently set the factor to one: it must supply an upper bound on
`max_{α'∈D_α} ᾱ_{ν'}`, which is the convex-program certificate the endpoint stage owes.

## Anti-laundering

`DESIGN.md`'s aggregate anti-laundering rule forbids storing, as a certificate field, a
degeneration from the assembled source power to the assembled target family.  That degeneration is
precisely `[DuanWuZhou2022]`'s §6 conclusion, so it is what this module must *derive*.

`Tensor.Restricts.partitionedYZCompatibilityCleanup_to_repairedRestrictedSplittingDirectSum` is
the derivation.  Its premises are finite or factorwise, in the sense DESIGN permits:

1. `hX` — injectivity of the `X` block label on the ambient support, a statement about a `Finset`;
   in a `[DuanWuZhou2022]` client it is the output of
   `Combinatorics/MarkedTwoLegHashingExtraction.exists_seed_many_markedXYIsolatedTargets`;
2. `hsoundY` / `hsoundZ` — `Tensor.IsCompatibilitySound`, pure predicates on finite address
   families; `Combinatorics/CompatibleSplitCount.lean` supplies the predicate and its soundness;
3. `hleaf` — **one exact restriction per retained constituent** onto a *broken* copy of the
   restricted-splitting power `T^{⊗(n+1)}[α̃]`.  This is the factorwise premise;
4. `hbudget` — the finite Hole-Lemma inequality per batch, discharged by
   `AsymmetricGlobal.holeBudget_of_eight_mul_card_le`.

Everything tensor-semantic is constructed: the two variable zero-outs by
`Tensor.Restricts.partitionedYZCompatibilityCleanup_to_indexedDirectSum`, the regrouping of the
retained copies into batches by `Restricts.indexedDirectSum_equiv` and
`Restricts.indexedDirectSum_sigma`, and the repair of each batch by the committed Hole Lemma
`Tensor.Restricts.indexedDirectSum_restrictedSplittingHoleRepair`.  The copy count is *not* an
input: it is `Fintype.card β`, the number of batches of the retained support, which is exactly the
cardinality the counting layer bounds from below.  This mirrors
`MatrixMultiplication/WholeConstituentExtraction.lean`.

## The value laws

The leaf enters as a `HasTauWeight` — `[DuanWuZhou2022]`'s inter-level interface is the *pair*
`(V_{i,j,k}, α̃_{i,j,k})`, i.e. a weighted extraction of a restricted-splitting power, not a bare
value.  `HasTauWeight.indexedDirectSum_const` adds the weights of the retained copies (the binary
law `HasTauWeight.directSum` of `MatrixMultiplication/TauValueDirectSum.lean` does not cover a
genuine indexed direct sum), so one assembled stage carries weight `copies · (leaf weight)` for
`sym₆(T)^{⊗N}`, i.e. `(copies · leaf weight)^{1/N}` after the `N`-th root.

Reading the value as a supremum needs `BddAbove`; `MatrixMultiplication/TauValue.lean`'s
`tauValueValues_bddAbove` discharges it whenever `τ ≤ ω/3`, and it is otherwise carried explicitly
(M-DWZ2's convention).  No attainment, limit, or supremum is claimed by the certificate-level
statements.

## Routing to `ω`

Watchlist item 14: `[DuanWuZhou2022]`'s `thm:Schonhage` is transcribed with an equality hypothesis
and a non-strict conclusion, a form `DESIGN.md` records as false in general (`T = ⟨1,1,1⟩`).  The
`ω`-facing statement here therefore routes through the strict
`omega_lt_three_mul_of_certificate` and concludes `ω < 3τ`; it never reads the supremum, so it
needs no boundedness hypothesis.

## Explicit remaining hypotheses

The theorems below take as *named hypotheses*, never as hidden assumptions:

* `hcount` — the retained copy count realizes `copyRate^{6N}`.  Establishing it for a concrete
  component is the arithmetic of the endpoint stage and needs, among other things, the asymptotic
  `p_comp = ᾱ_p^{n + o(n)}`, which `Analysis/CompatibilityRate.lean` records as an open gap
  (blocked on zero-tolerant method-of-types estimates; see the board request).
* `hvalue` — the leaf weight realizes `ᾱ_val^{6N}`; this is the restricted-splitting value input,
  supplied per component.
* `hbdd` — boundedness of the value set, discharged by `tauValueValues_bddAbove` when `τ ≤ ω/3`.
* the hash-loss bound, which enters through `GlobalRateData.hashLossRate` (watchlist item 2).
-/

namespace AlgebraicComplexity

open Tensor
open scoped BigOperators

universe u v w

namespace AsymmetricGlobal

/-! ## The two-branch rate arithmetic -/

section Rates

/-- Dividing by a maximum is taking the minimum of the two quotients.  This one-line fact is the
entire origin of the `min` in `[DuanWuZhou2022]`'s `eq:numeric_conclusion_g`. -/
theorem div_max_eq_min_div {N a b : ℝ} (hN : 0 ≤ N) (ha : 0 < a) (hb : 0 < b) :
    N / max a b = min (N / a) (N / b) := by
  rcases le_total a b with h | h
  · have hle : N / b ≤ N / a := by
      rw [div_le_div_iff₀ hb ha]
      exact mul_le_mul_of_nonneg_left h hN
    rw [max_eq_right h, min_eq_right hle]
  · have hle : N / a ≤ N / b := by
      rw [div_le_div_iff₀ ha hb]
      exact mul_le_mul_of_nonneg_left h hN
    rw [max_eq_left h, min_eq_left hle]

/-- **The numerical data of `[DuanWuZhou2022]`'s global analysis** (`global_value.tex` §6.3).

All six entries are exponential *rates*, i.e. `2^{H(·)}`-style bases.  This module never computes
them, it only combines them, so the entropy formulas stay in the analysis layer
(`Analysis/CompatibilityRate.lean` for `ᾱ_p`, `Probability/Entropy.lean` for the rest).

The field `hashLossRate` is `max_{α' ∈ D_α} ᾱ_{ν'}`, the quantity §6.3's table omits (watchlist
item 2).  It is mandatory precisely so that it cannot be dropped. -/
structure GlobalRateData where
  /-- `ᾱ_ν = 2^{H(α)}`: the rate of the good (joint-`α`-consistent) triples `N_α`. -/
  ambientRate : ℝ
  /-- `max_{α' ∈ D_α} ᾱ_{ν'}`: the rate of `N_triple`, the marginally consistent triples. -/
  hashLossRate : ℝ
  /-- `ᾱ_X = 2^{H(α_X)}`. -/
  xRate : ℝ
  /-- `ᾱ_Z = 2^{H(α_Z)}`. -/
  zRate : ℝ
  /-- `ᾱ_p`: the compatibility rate of `Analysis/CompatibilityRate.compatibilityRate`. -/
  compatRate : ℝ
  /-- `ᾱ_val = ∏ V^{(6)}(T_{i,j,k}, α̃_{i,j,k})^{α(i,j,k)}`. -/
  valRate : ℝ
  ambientRate_pos : 0 < ambientRate
  hashLossRate_pos : 0 < hashLossRate
  xRate_pos : 0 < xRate
  zRate_pos : 0 < zRate
  compatRate_pos : 0 < compatRate
  valRate_pos : 0 < valRate

namespace GlobalRateData

variable (d : GlobalRateData)

/-- The rate of `[DuanWuZhou2022]`'s modulus `M₀ = 8·max(N_triple/N_X, N_α·p_comp/N_Z)`, with the
constant `8` dropped: only the exponential rate matters. -/
noncomputable def modulusRate : ℝ :=
  max (d.hashLossRate / d.xRate) (d.ambientRate * d.compatRate / d.zRate)

/-- The rate of the retained copy count `N_α / M`. -/
noncomputable def copyRate : ℝ := d.ambientRate / d.modulusRate

/-- The full right-hand side of `eq:numeric_conclusion_g`. -/
noncomputable def globalRate : ℝ := d.copyRate * d.valRate

/-- The *hash loss* `R = N_α / N_triple` of `[DuanWuZhou2022]` §"Hash Loss".  This is the factor
that §6.3's parameter table omits; it is `1 − 4.7·10^{-13}` at the published parameters, but the
theorems below carry it symbolically. -/
noncomputable def hashLoss : ℝ := d.ambientRate / d.hashLossRate

theorem modulusRate_pos : 0 < d.modulusRate :=
  lt_of_lt_of_le (div_pos d.hashLossRate_pos d.xRate_pos) (le_max_left _ _)

theorem copyRate_pos : 0 < d.copyRate := div_pos d.ambientRate_pos d.modulusRate_pos

theorem globalRate_pos : 0 < d.globalRate := mul_pos d.copyRate_pos d.valRate_pos

/-- **`[DuanWuZhou2022]`'s `min`, derived.**  The copy rate obtained by dividing the good-triple
rate by the modulus rate is the minimum of the hashing branch `ᾱ_ν·ᾱ_X/max_{α'} ᾱ_{ν'}` and the
combination-loss branch `ᾱ_Z/ᾱ_p`.

The paper displays the minimum without comment.  It is the image of the *maximum* in
`M₀ = 8·max(N_triple/N_X, N_α·p_comp/N_Z)` under `N_α / ·`, which is why the two branches must be
carried by one modulus and not by two independent hypotheses. -/
theorem copyRate_eq_min :
    d.copyRate =
      min (d.ambientRate * d.xRate / d.hashLossRate) (d.zRate / d.compatRate) := by
  have hbranch₁ : d.ambientRate / (d.hashLossRate / d.xRate) =
      d.ambientRate * d.xRate / d.hashLossRate := by
    field_simp
  have ha : d.ambientRate ≠ 0 := d.ambientRate_pos.ne'
  have hc : d.compatRate ≠ 0 := d.compatRate_pos.ne'
  have hz : d.zRate ≠ 0 := d.zRate_pos.ne'
  have hbranch₂ : d.ambientRate / (d.ambientRate * d.compatRate / d.zRate) =
      d.zRate / d.compatRate := by
    field_simp
  rw [copyRate, modulusRate,
    div_max_eq_min_div d.ambientRate_pos.le
      (div_pos d.hashLossRate_pos d.xRate_pos)
      (div_pos (mul_pos d.ambientRate_pos d.compatRate_pos) d.zRate_pos),
    hbranch₁, hbranch₂]

/-- `eq:numeric_conclusion_g`'s right-hand side, written exactly as the paper displays it. -/
theorem globalRate_eq_min_mul :
    d.globalRate =
      min (d.ambientRate * d.xRate / d.hashLossRate) (d.zRate / d.compatRate) * d.valRate := by
  rw [globalRate, copyRate_eq_min]

/-- **Watchlist item 2, made unavoidable.**  The hashing branch is `ᾱ_X` multiplied by the hash
loss `N_α/N_triple`; a client that omits the hash loss is claiming `hashLossRate = ambientRate`,
which the field structure forces it to state. -/
theorem branchHashing_eq_xRate_mul_hashLoss :
    d.ambientRate * d.xRate / d.hashLossRate = d.xRate * d.hashLoss := by
  rw [hashLoss]
  field_simp

end GlobalRateData

end Rates

/-! ## Weights of indexed direct sums -/

section IndexedWeight

variable {K : Type u} [CommSemiring K]
variable {U : Leg → Type v} [∀ c, AddCommMonoid (U c)] [∀ c, Module K (U c)]

/-- **Weights add over an indexed direct sum of identical summands.**

`MatrixMultiplication/TauValueDirectSum.lean` proves the binary law `HasTauWeight.directSum`; a
laser stage produces a genuine `Tensor.indexedDirectSum`, and the copies it produces are identical,
so this is the form the pipeline needs.

Proof sketch: the summands share one polynomial degeneration, hence one displayed leading degree,
so `PolynomialDegeneratesAt.indexedDirectSum` applies without any degree synchronization.  The
resulting nested family of matrix-multiplication direct sums is flattened by
`Isomorphic.indexedDirectSum_sigma` and reindexed by `Fintype.equivFin`; the weight is the
corresponding double sum. -/
theorem HasTauWeight.indexedDirectSum_const {ι : Type w} [Fintype ι] [DecidableEq ι]
    {X : Tensor3 K U} {τ value : ℝ} (h : HasTauWeight K X τ value) :
    HasTauWeight K
      (Tensor.indexedDirectSum (V := fun _ : ι ↦ U) fun _ ↦ X) τ
      ((Fintype.card ι : ℝ) * value) := by
  classical
  obtain ⟨copies, xs, ys, zs, hx, hy, hz, hdeg, hval⟩ := h
  obtain ⟨A, degree, hA⟩ := hdeg
  -- The flattened index of all matrix-multiplication summands.
  let J : Type _ := Σ _ : ι, Fin copies
  let e : J ≃ Fin (Fintype.card J) := Fintype.equivFin J
  let MMFamily : ∀ _ : ι, Fin copies → Leg → Type u := fun _ k ↦ MMSpace K (xs k) (ys k) (zs k)
  let MM : ∀ ij : J, Tensor3 K (MMFamily ij.1 ij.2) :=
    fun ij ↦ matrixMultiplication (K := K) (xs ij.2) (ys ij.2) (zs ij.2)
  let xSize : Fin (Fintype.card J) → ℕ := fun j ↦ xs (e.symm j).2
  let ySize : Fin (Fintype.card J) → ℕ := fun j ↦ ys (e.symm j).2
  let zSize : Fin (Fintype.card J) → ℕ := fun j ↦ zs (e.symm j).2
  -- The nested degeneration, at the single displayed degree shared by all summands.
  have hnested : PolynomialDegeneratesAt degree
      (Tensor.indexedDirectSum (V := fun _ : ι ↦ U) fun _ ↦ X)
      (Tensor.indexedDirectSum fun i : ι ↦
        Tensor.indexedDirectSum fun k : Fin copies ↦ MM ⟨i, k⟩) :=
    Tensor.PolynomialDegeneratesAt.indexedDirectSum fun _ ↦ ⟨A, hA⟩
  -- Flattening the dependent pair and reindexing it by `Fin`.
  have hreindex : Restricts (Tensor.indexedDirectSum MM)
      (matrixMultiplicationDirectSum K xSize ySize zSize) := by
    unfold matrixMultiplicationDirectSum
    apply Tensor.Restricts.indexedDirectSum_equiv e
    intro ij
    apply Tensor.Isomorphic.restricts
    change Tensor.Isomorphic (MM ij) (MM (e.symm (e ij)))
    rw [e.symm_apply_apply]
    exact Tensor.Isomorphic.refl (MM ij)
  have hflatten : Restricts
      (Tensor.indexedDirectSum fun i : ι ↦
        Tensor.indexedDirectSum fun k : Fin copies ↦ MM ⟨i, k⟩)
      (Tensor.indexedDirectSum MM) :=
    (Tensor.Isomorphic.indexedDirectSum_sigma (S := MMFamily) MM).symm.restricts
  -- The weight is the double sum of the component weights.
  have hsum : matrixMultiplicationVolumePowerSum xSize ySize zSize τ =
      (Fintype.card ι : ℝ) * matrixMultiplicationVolumePowerSum xs ys zs τ := by
    unfold matrixMultiplicationVolumePowerSum matrixMultiplicationVolume
    have hstep : ∑ j : Fin (Fintype.card J),
        ((xs (e.symm j).2 * ys (e.symm j).2 * zs (e.symm j).2 : ℕ) : ℝ) ^ τ =
          ∑ ij : J, ((xs ij.2 * ys ij.2 * zs ij.2 : ℕ) : ℝ) ^ τ :=
      Equiv.sum_comp e.symm fun ij : J ↦ ((xs ij.2 * ys ij.2 * zs ij.2 : ℕ) : ℝ) ^ τ
    rw [hstep, Fintype.sum_sigma]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  exact ⟨Fintype.card J, xSize, ySize, zSize,
    fun j ↦ hx _, fun j ↦ hy _, fun j ↦ hz _,
    hnested.toPolynomialDegenerates.trans
      (PolynomialDegenerates.of_restricts (hflatten.trans hreindex)),
    by rw [hsum]; exact mul_le_mul_of_nonneg_left hval (Nat.cast_nonneg _)⟩

end IndexedWeight

/-! ## From a weighted power to `ω` -/

section OmegaOfWeight

variable {F : Type u} [Field F]
variable {V : Leg → Type v} [∀ c, AddCommMonoid (V c)] [∀ c, Module F (V c)]

/-- **A weighted power beating the asymptotic rank forces `ω < 3τ`.**

`MatrixMultiplication/TauValueDirectSum.le_tauValue_of_hasTauWeight` reads the same data through
the supremum, which needs `BddAbove`; that hypothesis is unavailable here without circularity,
because `tauValueValues_bddAbove` is itself conditioned on `τ ≤ ω/3`.  Extracting the finite
certificate instead and feeding it to the **strict**
`omega_lt_three_mul_of_certificate` avoids the issue entirely — and is watchlist item 14's
requirement, since `[DuanWuZhou2022]`'s transcription of `thm:Schonhage` is non-strict and
`DESIGN.md` records that form as false in general.

Proof sketch: a positive weight forces the extracted family to be nonempty, so the extraction data
is a genuine `TauValueCertificate` of length `N`, whose weight is at least `value^{1/N}`. -/
theorem omega_lt_three_mul_of_hasTauWeight {T : Tensor3 F V} {τ r value : ℝ} {N : ℕ}
    (hN : 0 < N) (hvalue : 0 < value) (hrank : Tensor.asymptoticRank T ≤ r)
    (h : HasTauWeight F (Tensor.power T N) τ value)
    (hgap : r < value ^ ((N : ℝ)⁻¹)) :
    omega F < 3 * τ := by
  obtain ⟨copies, m, n, p, hm, hn, hp, hdeg, hval⟩ := h
  have hcopies : 0 < copies := by
    rcases Nat.eq_zero_or_pos copies with hzero | hpos
    · subst hzero
      have hz : matrixMultiplicationVolumePowerSum m n p τ = 0 := by
        unfold matrixMultiplicationVolumePowerSum
        simp
      rw [hz] at hval
      linarith
    · exact hpos
  refine omega_lt_three_mul_of_certificate F hrank
    { power := N, copies := copies, xSize := m, ySize := n, zSize := p,
      power_pos := hN, copies_pos := hcopies, xSize_pos := hm, ySize_pos := hn,
      zSize_pos := hp, degenerates := hdeg } ?_
  show r < tauValueTerm τ N m n p
  exact hgap.trans_le (Real.rpow_le_rpow hvalue.le hval (by positivity))

end OmegaOfWeight

/-! ## The assembly: hashing, compatibility cleanup, and batched hole repair -/

section Assembly

variable {K : Type u} [CommSemiring K]
variable {A : Leg → Type w} [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]
variable {V : ∀ c, A c → Type (max u v)}
variable [∀ c a, AddCommMonoid (V c a)] [∀ c a, Module K (V c a)]
variable {B : Leg → Type w} [∀ c, Fintype (B c)] [∀ c, DecidableEq (B c)]
variable {W : ∀ c, B c → Type (max u v)}
variable [∀ c a, AddCommMonoid (W c a)] [∀ c a, Module K (W c a)]

/-- **The assembled degeneration of `[DuanWuZhou2022]` §6, derived.**

Given

* an `X`-isolated ambient support (the output of asymmetric hashing),
* two sound compatibility zero-outs (`Y` then `Z`),
* a partition of the retained addresses into batches, and
* one exact restriction per retained constituent onto a *broken* copy of the restricted-splitting
  power `Q^{⊗(n+1)}[α̃]`,

the ambient partitioned tensor restricts onto one intact copy of `Q^{⊗(n+1)}[α̃]` per batch,
provided each batch satisfies the finite Hole-Lemma inequality.

No relation between the assembled source and the assembled target is assumed: the conclusion is
composed from `partitionedYZCompatibilityCleanup_to_indexedDirectSum`, the factorwise `hleaf`, the
regrouping equivalence `Equiv.sigmaFiberEquiv`, and the committed Hole Lemma
`indexedDirectSum_restrictedSplittingHoleRepair`.  This is the anti-laundering discipline of
`DESIGN.md`, in the same shape as `MatrixMultiplication/WholeConstituentExtraction.lean`. -/
theorem Tensor.Restricts.partitionedYZCompatibilityCleanup_to_repairedRestrictedSplittingDirectSum
    (P : PartitionedTensor (K := K) (A := A) V)
    (hX : Set.InjOn (fun address : BlockAddress A ↦ address .X) P.support)
    (compatibleY : A .Y → BlockAddress A → Prop)
    (hsoundY : IsCompatibilitySound P.support .Y compatibleY)
    (compatibleZ : A .Z → BlockAddress A → Prop)
    (hsoundZ : IsCompatibilitySound
      (compatibilityIsolatedSupport P.support .Y compatibleY) .Z compatibleZ)
    (Q : PartitionedTensor (K := K) (A := B) W) (n : ℕ) (α : B Leg.Z → ℕ)
    {β : Type*} [Fintype β] [DecidableEq β]
    (batch : (compatibilityIsolatedSupport
        (compatibilityIsolatedSupport P.support .Y compatibleY) .Z compatibleZ) → β)
    (hbatch : Function.Surjective batch)
    (holes : (compatibilityIsolatedSupport
        (compatibilityIsolatedSupport P.support .Y compatibleY) .Z compatibleZ) →
      Finset (AvailableWord (B Leg.Z) n α))
    (hleaf : ∀ address : compatibilityIsolatedSupport
        (compatibilityIsolatedSupport P.support .Y compatibleY) .Z compatibleZ,
      Restricts (P.constituent address.1)
        ((Q.restrictedSplittingPower n (SplitRestriction.ofLeg Leg.Z α)).holeSelect Leg.Z
          fun word ↦ word ∈ (holes address).image Subtype.val).realize)
    (hbudget : ∀ b : β,
      Fintype.card (AvailableWord (B Leg.Z) n α) *
          ∏ a : {a // batch a = b}, (holes a.1).card <
        Fintype.card (AvailableWord (B Leg.Z) n α) ^ Fintype.card {a // batch a = b}) :
    Restricts P.realize
      (Tensor.indexedDirectSum
        (V := fun _ : β ↦ PartitionedSpace K (PositivePowerBlockSpace K W n))
        fun _ ↦ (Q.restrictedSplittingPower n (SplitRestriction.ofLeg Leg.Z α)).realize) := by
  classical
  -- Step 1: hashing + compatibility cleanup.  The two variable zero-outs are derived, not assumed.
  refine (Tensor.Restricts.partitionedYZCompatibilityCleanup_to_indexedDirectSum
    P hX compatibleY hsoundY compatibleZ hsoundZ).trans ?_
  -- Step 2: the factorwise leaf restrictions, one per retained constituent.
  refine (Tensor.Restricts.indexedDirectSum hleaf).trans ?_
  -- Step 3: regroup the retained copies into batches.
  refine (Tensor.Restricts.indexedDirectSum_equiv
    (J := Σ b : β, {a : (compatibilityIsolatedSupport
      (compatibilityIsolatedSupport P.support .Y compatibleY) .Z compatibleZ) // batch a = b})
    (U := fun _ ↦ PartitionedSpace K (PositivePowerBlockSpace K W n))
    (S := fun ab ↦ ((Q.restrictedSplittingPower n (SplitRestriction.ofLeg Leg.Z α)).holeSelect
      Leg.Z fun word ↦ word ∈ (holes ab.2.1).image Subtype.val).realize)
    (Equiv.sigmaFiberEquiv batch).symm fun _ ↦ Restricts.refl _).trans ?_
  -- Step 4: flatten the dependent pair into nested direct sums.
  refine (Tensor.Restricts.indexedDirectSum_sigma
    (J := fun b : β ↦ {a : (compatibilityIsolatedSupport
      (compatibilityIsolatedSupport P.support .Y compatibleY) .Z compatibleZ) // batch a = b})
    (S := fun _ _ ↦ PartitionedSpace K (PositivePowerBlockSpace K W n))
    (fun ab ↦ ((Q.restrictedSplittingPower n (SplitRestriction.ofLeg Leg.Z α)).holeSelect
      Leg.Z fun word ↦ word ∈ (holes ab.2.1).image Subtype.val).realize)).trans ?_
  -- Step 5: repair each batch by the committed Hole Lemma.
  refine Tensor.Restricts.indexedDirectSum fun b ↦ ?_
  haveI : Nonempty {a : (compatibilityIsolatedSupport
      (compatibilityIsolatedSupport P.support .Y compatibleY) .Z compatibleZ) // batch a = b} := by
    obtain ⟨a, ha⟩ := hbatch b
    exact ⟨⟨a, ha⟩⟩
  exact Tensor.Restricts.indexedDirectSum_restrictedSplittingHoleRepair
    (ι := {a : (compatibilityIsolatedSupport
      (compatibilityIsolatedSupport P.support .Y compatibleY) .Z compatibleZ) // batch a = b})
    Q n α (fun a ↦ holes a.1) (hbudget b)

end Assembly

/-! ## The master theorem -/

section Master

variable {K : Type u} [CommSemiring K]
variable {V : Leg → Type v} [∀ c, AddCommMonoid (V c)] [∀ c, Module K (V c)]
variable {W : Leg → Type v} [∀ c, AddCommMonoid (W c)] [∀ c, Module K (W c)]

/-- The weight of an assembled stage: the retained copy count times the leaf weight. -/
theorem hasTauWeight_of_repairedStage {T : Tensor3 K V} {leaf : Tensor3 K W}
    {τ leafValue : ℝ} (N : ℕ)
    {β : Type v} [Fintype β] [DecidableEq β]
    (hstage : Restricts (Tensor.power T N)
      (Tensor.indexedDirectSum (V := fun _ : β ↦ W) fun _ ↦ leaf))
    (hleaf : HasTauWeight K leaf τ leafValue) :
    HasTauWeight K (Tensor.power T N) τ ((Fintype.card β : ℝ) * leafValue) :=
  HasTauWeight.of_restricts hstage (HasTauWeight.indexedDirectSum_const (ι := β) hleaf)

/-- One assembled stage is worth at least `globalRate^6` after the `N`-th root, once the retained
copy count and the leaf weight realize their rates.

This is the numerical heart of `eq:numeric_conclusion_g`: the copy count enters linearly (it is the
number of batches surviving hashing, compatibility cleanup and hole repair) and the leaf weight
multiplicatively, and the `6N`-th root is `[DuanWuZhou2022]`'s six-symmetrized normalization. -/
theorem globalRate_pow_le_rpow_of_repairedStage
    (d : GlobalRateData) {leafValue : ℝ} (N : ℕ) (hN : 0 < N)
    {β : Type v} [Fintype β]
    (hcount : d.copyRate ^ (6 * N) ≤ (Fintype.card β : ℝ))
    (hvalue : d.valRate ^ (6 * N) ≤ leafValue) :
    d.globalRate ^ 6 ≤ ((Fintype.card β : ℝ) * leafValue) ^ ((N : ℝ)⁻¹) := by
  have hglobalPos := d.globalRate_pos
  have hprod : d.globalRate ^ (6 * N) ≤ (Fintype.card β : ℝ) * leafValue := by
    have hexpand : d.globalRate ^ (6 * N) = d.copyRate ^ (6 * N) * d.valRate ^ (6 * N) := by
      rw [GlobalRateData.globalRate, mul_pow]
    rw [hexpand]
    exact mul_le_mul hcount hvalue (pow_pos d.valRate_pos _).le (Nat.cast_nonneg _)
  have hroot : (d.globalRate ^ (6 * N)) ^ ((N : ℝ)⁻¹) = d.globalRate ^ 6 := by
    rw [← Real.rpow_natCast d.globalRate (6 * N), ← Real.rpow_mul hglobalPos.le,
      ← Real.rpow_natCast d.globalRate 6]
    congr 1
    have hNne : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
    push_cast
    field_simp
  refine le_trans (le_of_eq hroot.symm) ?_
  exact Real.rpow_le_rpow (pow_nonneg hglobalPos.le _) hprod (by positivity)

/-- **The asymmetric global value theorem** (`[DuanWuZhou2022]`, `eq:numeric_conclusion_g`).

`V^{(6)}_τ(T) ≥ min( ᾱ_ν·ᾱ_X / max_{α'∈D_α} ᾱ_{ν'} , ᾱ_Z/ᾱ_p ) · ᾱ_val`

for a tensor `T` admitting one assembled stage whose retained copy count and leaf weight realize
the two rates.

The `min` is not assumed: `GlobalRateData.copyRate_eq_min` proves that the copy rate — defined as
the good-triple rate divided by the modulus rate `max(ᾱ_ν'/ᾱ_X, ᾱ_ν·ᾱ_p/ᾱ_Z)` — *is* the paper's
minimum.  The hash-loss factor omitted by §6.3's table is the field `hashLossRate` and appears in
the first branch (`GlobalRateData.branchHashing_eq_xRate_mul_hashLoss`).

`hbdd` is the only asymptotic hypothesis; `tauValueValues_bddAbove` discharges it whenever
`τ ≤ ω/3`. -/
theorem le_sixValue_of_repairedStage
    (d : GlobalRateData) {T : Tensor3 K V} {leaf : Tensor3 K W} {τ leafValue : ℝ}
    (hbdd : BddAbove (tauValueValues K (symSix K T) τ))
    (N : ℕ) (hN : 0 < N) (hleafValue : 0 < leafValue)
    {β : Type v} [Fintype β] [DecidableEq β]
    (hstage : Restricts (Tensor.power (symSix K T) N)
      (Tensor.indexedDirectSum (V := fun _ : β ↦ W) fun _ ↦ leaf))
    (hleaf : HasTauWeight K leaf τ leafValue)
    (hcount : d.copyRate ^ (6 * N) ≤ (Fintype.card β : ℝ))
    (hvalue : d.valRate ^ (6 * N) ≤ leafValue)
    (hcards : 0 < Fintype.card β) :
    min (d.ambientRate * d.xRate / d.hashLossRate) (d.zRate / d.compatRate) * d.valRate ≤
      sixValue K T τ := by
  rw [← d.globalRate_eq_min_mul]
  have hcardPos : (0 : ℝ) < (Fintype.card β : ℝ) := by exact_mod_cast hcards
  have hterm := globalRate_pow_le_rpow_of_repairedStage d (β := β) N hN hcount hvalue
  have hvalueBound : ((Fintype.card β : ℝ) * leafValue) ^ ((N : ℝ)⁻¹) ≤
      tauValue K (symSix K T) τ :=
    le_tauValue_of_hasTauWeight hN (mul_pos hcardPos hleafValue)
      (hasTauWeight_of_repairedStage N hstage hleaf) hbdd
  have hle : d.globalRate ^ 6 ≤ tauValue K (symSix K T) τ := hterm.trans hvalueBound
  have hstep := Real.rpow_le_rpow (pow_nonneg d.globalRate_pos.le 6) hle
    (by positivity : (0 : ℝ) ≤ (((6 : ℕ) : ℝ))⁻¹)
  rw [Real.pow_rpow_inv_natCast d.globalRate_pos.le (by norm_num : (6 : ℕ) ≠ 0)] at hstep
  unfold sixValue
  rw [show ((6 : ℝ))⁻¹ = (((6 : ℕ) : ℝ))⁻¹ by norm_num]
  exact hstep

/-- **The `ω`-facing endpoint.**

Watchlist item 14: `[DuanWuZhou2022]`'s `thm:Schonhage` is transcribed with an equality hypothesis
and a non-strict conclusion, which `DESIGN.md` records as false in general (`T = ⟨1,1,1⟩`).  Their
actual use is strict, so this routes through `omega_lt_three_mul_of_certificate` and concludes
`ω < 3τ`.  Because it reads a single certificate rather than the supremum, no boundedness
hypothesis appears.

The rank hypothesis is on `sym₆(T)`: for `T = CW_q^{⊗2^{ℓ−1}}` the paper compares against
`R̃(T)^6`, which submultiplicativity of asymptotic rank supplies. -/
theorem omega_lt_three_mul_of_repairedStage
    {F : Type u} [Field F] {V : Leg → Type v}
    [∀ c, AddCommMonoid (V c)] [∀ c, Module F (V c)]
    {W : Leg → Type v} [∀ c, AddCommMonoid (W c)] [∀ c, Module F (W c)]
    (d : GlobalRateData) {T : Tensor3 F V} {leaf : Tensor3 F W} {τ r leafValue : ℝ}
    (hrank : Tensor.asymptoticRank (symSix F T) ≤ r)
    (N : ℕ) (hN : 0 < N) (hleafValue : 0 < leafValue)
    {β : Type v} [Fintype β] [DecidableEq β]
    (hstage : Restricts (Tensor.power (symSix F T) N)
      (Tensor.indexedDirectSum (V := fun _ : β ↦ W) fun _ ↦ leaf))
    (hleaf : HasTauWeight F leaf τ leafValue)
    (hcount : d.copyRate ^ (6 * N) ≤ (Fintype.card β : ℝ))
    (hvalue : d.valRate ^ (6 * N) ≤ leafValue)
    (hcards : 0 < Fintype.card β)
    (hgap : r < d.globalRate ^ 6) :
    omega F < 3 * τ := by
  have hcardPos : (0 : ℝ) < (Fintype.card β : ℝ) := by exact_mod_cast hcards
  refine omega_lt_three_mul_of_hasTauWeight hN (mul_pos hcardPos hleafValue) hrank
    (hasTauWeight_of_repairedStage N hstage hleaf) ?_
  exact hgap.trans_le (globalRate_pow_le_rpow_of_repairedStage d (β := β) N hN hcount hvalue)

end Master

/-! ## A tiny inhabited instance

The vacuity hazards of this stage are (a) an empty available-block set, which would make the Hole
Lemma budget trivially satisfiable, and (b) a `GlobalRateData` whose two branches coincide, which
would hide whether the `min` selects anything.  The instance below pins both. -/

section TinyInstance

/-- The tiny mixed split distribution really is realized: its available-block set is nonempty, so
the Hole-Lemma budget below is not vacuous. -/
theorem tiny_card_availableWord_pos :
    0 < Fintype.card (AvailableWord (Fin 2) 1 tinyMixedType) := by
  refine card_availableWord_pos 1 tinyMixedType ?_
  simp only [tinyMixedType, Pi.add_apply, tinyLetterType_apply]
  decide

/-- The budget really is satisfiable: four undamaged copies over the tiny available set clear
`[DuanWuZhou2022]`'s threshold `8(ℓ(n+1) + 1) ≤ 7s` at `ℓ = 1`, `n + 1 = 2`, `s = 4`. -/
theorem tiny_holeBudget :
    Fintype.card (AvailableWord (Fin 2) 1 tinyMixedType) *
        ∏ _t : Fin 4, (∅ : Finset (AvailableWord (Fin 2) 1 tinyMixedType)).card <
      Fintype.card (AvailableWord (Fin 2) 1 tinyMixedType) ^ Fintype.card (Fin 4) := by
  refine holeBudget_of_eight_mul_card_le (fun _ : Fin 4 ↦ ∅) 2
    tiny_card_availableWord_pos ?_ (fun _ ↦ by simp) (by simp)
  have h := card_availableWord_le_two_pow_mul (I := Fin 2) (l := 1) (by simp) 1 tinyMixedType
  simpa using h

/-- A tiny inhabited `GlobalRateData` whose two branches genuinely differ, so the `min` of
`copyRate_eq_min` is not degenerate: the hashing branch binds. -/
noncomputable def tinyRateData : GlobalRateData where
  ambientRate := 2
  hashLossRate := 8
  xRate := 4
  zRate := 2
  compatRate := 1
  valRate := 1
  ambientRate_pos := by norm_num
  hashLossRate_pos := by norm_num
  xRate_pos := by norm_num
  zRate_pos := by norm_num
  compatRate_pos := by norm_num
  valRate_pos := by norm_num

theorem tinyRateData_copyRate : tinyRateData.copyRate = 1 := by
  rw [GlobalRateData.copyRate_eq_min]
  norm_num [tinyRateData]

/-- The hashing branch is strictly smaller than the combination-loss branch at the tiny data, so
the `min` really selects a branch and the hash-loss factor genuinely lowers the bound (watchlist
item 2). -/
theorem tinyRateData_branches :
    tinyRateData.ambientRate * tinyRateData.xRate / tinyRateData.hashLossRate <
      tinyRateData.zRate / tinyRateData.compatRate := by
  norm_num [tinyRateData]

/-- The tiny hash loss is `1/4`, not `1`: the factor omitted by §6.3's table is not identically
one. -/
theorem tinyRateData_hashLoss : tinyRateData.hashLoss = 1 / 4 := by
  norm_num [GlobalRateData.hashLoss, tinyRateData]

end TinyInstance

end AsymmetricGlobal

end AlgebraicComplexity
