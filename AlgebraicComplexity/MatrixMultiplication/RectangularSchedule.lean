/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import Mathlib.NumberTheory.Bertrand
import AlgebraicComplexity.Analysis.BehrendRate
import AlgebraicComplexity.Analysis.RpowInequalities
import AlgebraicComplexity.Combinatorics.ProgressionFree
import AlgebraicComplexity.MatrixMultiplication.RectangularAsymptoticSum

/-!
# The Huang--Pan schedule over abstract geometric data

A laser-method client that wants a *rectangular* exponent bound runs the same schedule every
time: scale the selected multiplicity type by `N`, hash the positions modulo a prime `M` just
above the competitor count, extract `copies` independent constituents, compress them at a
near-optimal `κ`-rectangular algorithm, cancel the subexponential losses, and finally let the
bootstrap exponent decrease to `ω(1, 1, κ)`.  Only four things distinguish one client from
another, and this module makes all four parameters.

## The four parameters

1. **The extraction**, as `RectangularScheduleExtraction K A C R words fiber`.  This is verbatim
   the shape produced by the `exists_…_rectangularExtraction_of_fieldCard_typed` family: given a
   depth `N`, *any* finite field `F` of characteristic `≠ 2` whose size exceeds `12` times the
   competitor count, and any progression-free `B ⊆ F`, it returns an index type `ι` with the
   competitor-counting inequality `3 · #words · #B ≤ 4·|F|²·#ι` and a border-rank certificate for
   `⊕_ι ⟨A^N, A^N, C^N⟩`.  Keeping the field abstract rather than fixing `ZMod M` is free — every
   client proves the statement for an abstract field anyway — and keeping the *pair* `(words,
   fiber)` abstract is what lets a client whose word count is a product of two multinomials use
   this module.
2. **The entropy base** `E` of the selected type, with its subexponential loss `loss`, through
   the single hypothesis `E ^ N ≤ loss N * words N`.  Canonically `E` is
   `WordType.proportionalEntropyBase` of the profile and `loss` is
   `WordType.proportionalMultinomialLoss`; the pair is left abstract because a *mixed* power
   selects one profile per half and its entropy base and loss are then both products of two such
   factors ([Cop97]; see `Examples/CoppersmithMixedPowerType.lean`).
3. **The word length**, which enters only through the border-rank bound `R` and so needs no
   parameter of its own: a client whose word has length `T` over an alphabet of border rank
   `q + 2` instantiates `R := (q+2)^T`.
4. **The constituent dimensions `A`, `C` and the border-rank bound `R`**, as abstract naturals
   subject only to `1 < A`, `1 ≤ R` and the aspect-ratio inequality `A ^ κ ≤ C`.  Along the
   schedule they are used *geometrically*, as `A^N`, `C^N`, `R^N`.  This is the parameter that
   matters for reuse: a single-`q` client instantiates `A := q^m`, `C := q^p`, `R := (q+2)^T`,
   whereas Coppersmith's mixed `CW_7`/`CW_6` power instantiates
   `A := 7^{b₇}·6^{b₆}`, `C := 7^{a₇}·6^{a₆}`, `R := 9^{9a}·8^{8b}` with the *same* schedule and
   the same proof.  Hard-coding `q^(m·N)` and `(q+2)^(T·N)` — as the two rectangular
   Coppersmith--Winograd towers used to — is exactly what blocks that instantiation.

## Principal results

* `RectangularScheduleExtraction` -- the abstract extraction hypothesis;
* `rectScheduleLossAt`, `rectScheduleLossAt_subexponential` -- the collected subexponential loss
  of one pass: the type-counting loss, the Bertrand/Behrend hashing loss, and the constants `96`
  and `D`;
* `exists_rectSchedule_finite_step` -- one step of the schedule at depth `N`;
* `rectSchedule_rate_inequality` -- the rate inequality `(E/Φ)^{ω/τ} · A^ω ≤ R` at a fixed
  bootstrap exponent `τ > ω(1,1,κ)`;
* `rectSchedule_master_inequality` -- the same with `τ ↓ ω(1,1,κ)`, i.e. `(E/Φ) · A^ω ≤ R`.

Here `Φ` is *any* geometric envelope of the competitor count, `fiber N ≤ Φ^N`.  Keeping it a
parameter is what lets one schedule serve both branches of [HP98, Sections 6--7]: one branch
instantiates it at the `y`-leg fiber and the other at the `x`-leg fiber, and the entropy
comparison between the two is never needed inside the schedule.

## The three losses and how they are removed

* *type counting* -- a Stirling estimate replaces the exact multinomial word count by `E^N`, at
  the cost of the subexponential `loss`;
* *hashing* -- a prime modulus `M ≍ Φ^N` (Bertrand) and Behrend's progression-free construction
  cost `M^{1+o(1)}`, removed by `Growth.le_mul_exp_of_mul_rothNumberNat_le` together with
  `Growth.sqrt_log_le_mul_sqrt_succ`.  This is Huang--Pan's `M' ≥ M^{1-ε}, ε → 0`;
* *compression rounding* -- `exists_compressionScale` loses a factor `2^ω` and the constant `D`
  of the admissible exponent `τ`, both constant in `N`.

## The bootstrap

The compression scale of `exists_compressionScale` is built from an admissible exponent
`τ > ω(1,1,κ)`, so the rate inequality is first proved with the growth constant raised to `ω/τ`,
and only then is `τ` allowed to decrease to `ω` (`rectSchedule_master_inequality`).  Compressing
at `⟨1, F, 1⟩` instead would be blocking and would prove nothing.  This is Schönhage's device,
specialized to a family of identical rectangular constituents.

## References

* [HP98] X. Huang and V. Y. Pan, *Fast rectangular matrix multiplication and applications*,
  J. Complexity **14** (1998), 257--299, Sections 6--7.
* [Cop97] D. Coppersmith, *Rectangular matrix multiplication revisited*, J. Complexity **13**
  (1997), 42--49, Sections 4--5.
-/

namespace AlgebraicComplexity

open Tensor Growth

universe u

/-! ## The aspect ratio -/

/-- Huang--Pan's aspect ratio `r = p/m`, as a real number: the shape of the rectangular block
product a schedule compresses at.  Corner parameters of the selected type do not enter it -- they
change the *rate*, not the shape. -/
noncomputable def rectAspectRatio (p m : ℕ) : ℝ := (p : ℝ) / (m : ℝ)

/-- The aspect ratio is nonnegative: it is a quotient of two natural-number casts. -/
theorem rectAspectRatio_nonneg (p m : ℕ) : 0 ≤ rectAspectRatio p m := by
  unfold rectAspectRatio
  positivity

/-- A constituent of dimensions `q^(m·N)` and `q^(p·N)` really has aspect ratio `κ = p/m`: the
outer dimension is exactly the `κ`-th power of the inner one. -/
theorem rectAspectRatio_pow_rpow (q p m N : ℕ) (hm : 0 < m) :
    ((q : ℝ) ^ (m * N)) ^ rectAspectRatio p m = (q : ℝ) ^ (p * N) := by
  have hq : (0 : ℝ) ≤ (q : ℝ) := Nat.cast_nonneg q
  have hmR : (m : ℝ) ≠ 0 := by
    have : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
    exact this.ne'
  rw [← Real.rpow_natCast (q : ℝ) (m * N), ← Real.rpow_mul hq,
    ← Real.rpow_natCast (q : ℝ) (p * N)]
  congr 1
  unfold rectAspectRatio
  push_cast
  field_simp

/-- Reading a schedule's inner dimension `A = q^m` back as an `rpow` of `q`: the shape in which
the two Coppersmith--Winograd rectangular towers state their rate inequalities. -/
theorem natCast_pow_rpow (q m : ℕ) (ω : ℝ) :
    (((q ^ m : ℕ)) : ℝ) ^ ω = (q : ℝ) ^ ((m : ℝ) * ω) := by
  have hqnn : (0 : ℝ) ≤ (q : ℝ) := Nat.cast_nonneg q
  push_cast
  rw [← Real.rpow_natCast (q : ℝ) m, ← Real.rpow_mul hqnn]

/-- The base geometric datum of a single-`q` schedule: the constituent `⟨q^m, q^m, q^p⟩` has
aspect ratio `κ = p/m`. -/
theorem natPow_rpow_rectAspectRatio_le (q p m : ℕ) (hm : 0 < m) :
    (((q ^ m : ℕ)) : ℝ) ^ rectAspectRatio p m ≤ (((q ^ p : ℕ)) : ℝ) := by
  have h := rectAspectRatio_pow_rpow q p m 1 hm
  simp only [mul_one] at h
  push_cast
  rw [h]

/-- `κ = p/m` is the value of a positive rational at its numerator and denominator. -/
theorem rectAspectRatio_num_den {r : ℚ} (hr : 0 < r) :
    rectAspectRatio r.num.natAbs r.den = (r : ℝ) := by
  have hnum : (0 : ℤ) < r.num := Rat.num_pos.mpr hr
  have hcast : ((r.num.natAbs : ℕ) : ℝ) = ((r.num : ℤ) : ℝ) := by
    have h := congrArg (fun z : ℤ ↦ (z : ℝ)) (Int.natAbs_of_nonneg hnum.le)
    simpa using h
  show (((r.num.natAbs : ℕ)) : ℝ) / ((r.den : ℕ) : ℝ) = (r : ℝ)
  rw [hcast, Rat.cast_def]

/-! ## The abstract extraction hypothesis -/

/-- **The extraction hypothesis of a rectangular schedule.**

At every positive depth `N`, over every finite field `F` of characteristic other than two whose
size is at least `12` times the competitor count `fiber N`, and for every progression-free
`B ⊆ F`, the extraction returns an index type `ι` satisfying

* the competitor-counting inequality `3 · words N · #B ≤ 4 · |F|² · #ι`, and
* a border-rank-`R^N` certificate for `⊕_ι ⟨A^N, A^N, C^N⟩`.

This is verbatim what the `exists_…_rectangularExtraction_of_fieldCard_typed` family produces,
with the concrete `(q^(m·N), q^(p·N), (q+2)^(T·N))` replaced by the geometric data
`(A^N, C^N, R^N)` and the concrete word family replaced by its cardinality. -/
def RectangularScheduleExtraction (K : Type u) [Field K] (A C R : ℕ)
    (words fiber : ℕ → ℕ) : Prop :=
  ∀ N : ℕ, 0 < N →
    ∀ (F : Type) [Field F] [Fintype F] [NeZero (2 : F)],
      12 * fiber N ≤ Fintype.card F →
      ∀ B : Finset F, ThreeAPFree (B : Set F) →
        ∃ (ι : Type) (_ : Fintype ι),
          3 * words N * B.card ≤ 4 * (Fintype.card F * Fintype.card F) * Fintype.card ι ∧
            BorderRankLE (R ^ N)
              (Tensor.indexedDirectSum
                (fun _ : ι ↦ matrixMultiplication (K := K) (A ^ N) (A ^ N) (C ^ N)))

/-! ## The collected subexponential loss -/

/-- The subexponential loss of one pass of the schedule at depth `N`, competitor envelope `Φ` and
admissible-exponent constant `D`, before the bootstrap exponent is applied: the type-counting
loss `loss N`, the Behrend/Bertrand loss, and the constants `96` and `D`. -/
noncomputable def rectScheduleLossAt (loss : ℕ → ℝ) (Φ D : ℝ) (N : ℕ) : ℝ :=
  96 * loss N * D * Real.exp (4 * (Φ + 12) * √(((N + 1 : ℕ) : ℝ)))

/-- The one-pass loss is nonnegative whenever the type-counting loss and the constant `D` are:
every remaining factor is a positive constant or an exponential. -/
theorem rectScheduleLossAt_nonneg {loss : ℕ → ℝ} {N : ℕ} (hloss : 0 ≤ loss N)
    {Φ D : ℝ} (hD : 0 ≤ D) :
    0 ≤ rectScheduleLossAt loss Φ D N := by
  unfold rectScheduleLossAt
  positivity

/-- The collected one-pass loss is subexponential whenever the type-counting loss is.  This is what
lets the schedule's rate inequality survive the `N → ∞` limit: multiplying a subexponential
sequence by the Behrend/Bertrand factor `exp(4(Φ+12)√(N+1))` and by the constants `96` and `D`
leaves it subexponential. -/
theorem rectScheduleLossAt_subexponential {loss : ℕ → ℝ} (hloss : Growth.Subexponential loss)
    {Φ D : ℝ} (hΦ : 0 ≤ Φ) (hD : 0 ≤ D) :
    Growth.Subexponential (rectScheduleLossAt loss Φ D) := by
  have hbase : Growth.Subexponential (fun N : ℕ ↦
      loss N * Real.exp (4 * (Φ + 12) * √(((N + 1 : ℕ) : ℝ)))) :=
    hloss.mul (Growth.Subexponential.exp_mul_sqrt_succ (by positivity))
  have hscaled := hbase.const_mul (c := 96 * D) (by positivity)
  refine hscaled.mono (fun N ↦ rectScheduleLossAt_nonneg (hloss.nonneg N) hD) (fun N ↦ ?_)
  unfold rectScheduleLossAt
  ring_nf
  exact le_rfl

/-! ## The finite step of the schedule -/

section FiniteStep

variable (K : Type u) [Field K]

/-- **One step of the Huang--Pan schedule, at an arbitrary competitor bound `F`.**  At depth `N`
the extraction produces a prime hashing modulus `M ≍ F`, a copy count, and -- after compression at
a near-optimal `κ`-rectangular algorithm of exponent `τ` -- the displayed rectangular exponent
inequality.

`F` only has to dominate the competitor count at depth `N`; a smaller `F` gives a smaller modulus
and hence a better rate.  The copy count enters raised to `ω/τ`; the factor `2^ω` is the
compression rounding of `exists_compressionScale` and `D` is the constant of the admissible
exponent `τ`. -/
theorem exists_rectSchedule_finite_step {κ : ℝ} (hκ : 0 ≤ κ)
    {A C R : ℕ} (hA : 1 < A) (hR : 1 ≤ R) (hmid : ((A : ℝ)) ^ κ ≤ (C : ℝ))
    {words fiber : ℕ → ℕ} (hextract : RectangularScheduleExtraction K A C R words fiber)
    {N : ℕ} (hN : 0 < N) {τ : ℝ} (hτ : 0 < τ) {D : ℝ} (hD : 0 < D)
    (hbound : ∀ n : ℕ, 1 ≤ n →
      (rectangularMatrixRankSequence K κ n : ℝ) ≤ D * (n : ℝ) ^ τ)
    (F : ℕ) (hFpos : 0 < F) (hF : fiber N ≤ F) :
    ∃ M copies : ℕ,
      M.Prime ∧ 12 * F < M ∧ M ≤ 24 * F ∧
      3 * words N * rothNumberNat (M / 2) ≤ 4 * (M * M) * copies ∧
      (((copies : ℝ) / D) ^ (1 / τ)) ^ (rectangularOmega K κ) *
          (((A : ℝ) ^ N) ^ (rectangularOmega K κ)) ≤
        (2 : ℝ) ^ (rectangularOmega K κ) * ((R : ℝ) ^ N) := by
  classical
  set ω : ℝ := rectangularOmega K κ with hωdef
  have hωtwo : (2 : ℝ) ≤ ω := two_le_rectangularOmega K κ
  have hωpos : 0 < ω := by linarith
  -- Bertrand: a prime modulus just above the competitor bound.
  have hn : 12 * F ≠ 0 := by omega
  obtain ⟨M, hprime, hlower, hupper⟩ := Nat.exists_prime_lt_and_le_two_mul (12 * F) hn
  have hM3 : 3 ≤ M := by omega
  letI : Fact M.Prime := ⟨hprime⟩
  letI : NeZero (2 : ZMod M) := neZero_two_zmod_of_three_le hM3
  obtain ⟨B, hBcard, hB⟩ := exists_threeAPFree_zmod_half M
  obtain ⟨ι, hιfin, hcount, hborder⟩ :=
    hextract N hN (ZMod M) (by rw [ZMod.card]; omega) B hB
  letI : Fintype ι := hιfin
  refine ⟨M, Fintype.card ι, hprime, hlower, by omega, ?_, ?_⟩
  · have hc : 3 * words N * B.card ≤ 4 * (M * M) * Fintype.card ι := by
      simpa [ZMod.card] using hcount
    rwa [hBcard] at hc
  · -- The compression step.
    have hAnn : (0 : ℝ) ≤ (A : ℝ) := Nat.cast_nonneg A
    by_cases hcop : 1 ≤ Fintype.card ι
    · have hApow : 1 < A ^ N := Nat.one_lt_pow (by omega) hA
      have hRpow : 1 ≤ R ^ N := Nat.one_le_pow _ _ (by omega)
      have hcomm : ((A : ℝ) ^ N) ^ κ = ((A : ℝ) ^ κ) ^ N :=
        (Real.rpow_pow_comm hAnn κ N).symm
      have hmid' : (((A ^ N : ℕ)) : ℝ) ^ κ ≤ (((C ^ N : ℕ)) : ℝ) := by
        push_cast
        rw [hcomm, ← Real.rpow_natCast ((A : ℝ) ^ κ) N, ← Real.rpow_natCast (C : ℝ) N]
        exact Real.rpow_le_rpow (Real.rpow_nonneg hAnn κ) hmid (Nat.cast_nonneg N)
      have hstep := rpow_rectangularOmega_le_of_indexedDirectSum
        (K := K) (ι := ι) (κ := κ) (τ := τ) hκ hτ hD hbound hApow hRpow hmid' hcop hborder
      push_cast at hstep
      exact hstep
    · have hzero : Fintype.card ι = 0 := by omega
      rw [hzero]
      have h1 : ((0 : ℕ) : ℝ) / D = 0 := by simp
      rw [h1, Real.zero_rpow (one_div_ne_zero hτ.ne'), Real.zero_rpow hωpos.ne', zero_mul]
      positivity

end FiniteStep

/-! ## The rate inequality and the master scalar inequality -/

section Rate

variable (K : Type u) [Field K]

/-- **The rate inequality of the schedule, at a fixed bootstrap exponent `τ` and competitor
envelope `Φ`.**

Every subexponential loss of the schedule is removed by
`Growth.le_of_pow_succ_le_subexponential_mul_pow_succ`; what survives is the Huang--Pan growth
constant `E / Φ` raised to `ω/τ`, the price of having built the compression scale from an
admissible exponent `τ` rather than from `ω` itself. -/
theorem rectSchedule_rate_inequality {κ : ℝ} (hκ : 0 ≤ κ)
    {A C R : ℕ} (hA : 1 < A) (hR : 1 ≤ R) (hmid : ((A : ℝ)) ^ κ ≤ (C : ℝ))
    {words fiber : ℕ → ℕ} (hextract : RectangularScheduleExtraction K A C R words fiber)
    (hfiberPos : ∀ N : ℕ, 0 < N → 0 < fiber N)
    {E : ℝ} (hE : 0 < E) {loss : ℕ → ℝ} (hloss : Growth.Subexponential loss)
    (hwords : ∀ N : ℕ, 0 < N → E ^ N ≤ loss N * ((words N : ℕ) : ℝ))
    {Φ : ℝ} (hΦ : 1 ≤ Φ) (hfiber : ∀ N : ℕ, ((fiber N : ℕ) : ℝ) ≤ Φ ^ N)
    {τ : ℝ} (hτ : rectangularOmega K κ < τ) :
    (E / Φ) ^ (rectangularOmega K κ / τ) * ((A : ℝ)) ^ (rectangularOmega K κ) ≤ (R : ℝ) := by
  classical
  set ω : ℝ := rectangularOmega K κ with hωdef
  have hωtwo : (2 : ℝ) ≤ ω := two_le_rectangularOmega K κ
  have hωpos : 0 < ω := by linarith
  have hτpos : 0 < τ := hωpos.trans hτ
  set θ : ℝ := ω / τ with hθdef
  have hθpos : 0 < θ := div_pos hωpos hτpos
  have hθone : θ ≤ 1 := by
    rw [hθdef, div_le_one hτpos]
    linarith
  obtain ⟨_hτnn, D, hD, hbound⟩ := rectangularMatrixExponentLE_of_rectangularOmega_lt K hτ
  have hAnn : (0 : ℝ) ≤ (A : ℝ) := Nat.cast_nonneg A
  have hApos : (0 : ℝ) < (A : ℝ) := by
    have : (1 : ℝ) < (A : ℝ) := by exact_mod_cast hA
    linarith
  have hRpos : (0 : ℝ) < (R : ℝ) := by exact_mod_cast hR
  have hΦpos : (0 : ℝ) < Φ := by linarith
  have hG : (0 : ℝ) < E / Φ := div_pos hE hΦpos
  refine Growth.le_of_pow_succ_le_subexponential_mul_pow_succ
    (b := (E / Φ) ^ θ * ((A : ℝ)) ^ ω)
    (ρ := (R : ℝ))
    (loss := fun N ↦ rectScheduleLossAt loss Φ D N ^ θ * (2 : ℝ) ^ ω)
    (by positivity) ?_ ?_
  · have hbase := (rectScheduleLossAt_subexponential hloss hΦpos.le hD.le).add
      (Growth.Subexponential.const (c := (1 : ℝ)) zero_le_one)
    have h2 := hbase.const_mul (c := (2 : ℝ) ^ ω) (Real.rpow_nonneg (by norm_num) ω)
    refine h2.mono (fun N ↦ mul_nonneg
      (Real.rpow_nonneg (rectScheduleLossAt_nonneg (hloss.nonneg N) hD.le) θ)
      (Real.rpow_nonneg (by norm_num) ω)) (fun N ↦ ?_)
    have h3 : rectScheduleLossAt loss Φ D N ^ θ ≤ rectScheduleLossAt loss Φ D N + 1 :=
      Analysis.rpow_le_add_one (rectScheduleLossAt_nonneg (hloss.nonneg N) hD.le) hθpos.le hθone
    calc
      rectScheduleLossAt loss Φ D N ^ θ * (2 : ℝ) ^ ω
          ≤ (rectScheduleLossAt loss Φ D N + 1) * (2 : ℝ) ^ ω :=
        mul_le_mul_of_nonneg_right h3 (Real.rpow_nonneg (by norm_num) ω)
      _ = (2 : ℝ) ^ ω * (rectScheduleLossAt loss Φ D N + 1) := by ring
  · intro n
    set N : ℕ := n + 1 with hNdef
    have hNpos : 0 < N := by omega
    have hFpos : 0 < fiber N := hfiberPos N hNpos
    obtain ⟨M, copies, hprime, hlower, hupper, hcount, hstep⟩ :=
      exists_rectSchedule_finite_step K hκ hA hR hmid hextract hNpos hτpos hD hbound
        (fiber N) hFpos le_rfl
    have hM2 : 2 ≤ M := by omega
    set Y : ℝ := ((A : ℝ) ^ N) ^ ω with hYdef
    set Z : ℝ := (2 : ℝ) ^ ω * ((R : ℝ) ^ N) with hZdef
    have hYpos : 0 < Y := by
      rw [hYdef]
      exact Real.rpow_pos_of_pos (pow_pos hApos _) ω
    -- Invert the compression inequality into an upper bound on the copy count.
    set W : ℝ := (Z / Y) ^ (1 / θ) with hWdef
    have hZnn : 0 ≤ Z := by
      rw [hZdef]
      positivity
    have hWnn : (0 : ℝ) ≤ W := Real.rpow_nonneg (div_nonneg hZnn hYpos.le) _
    have hcopiesLe : (copies : ℝ) ≤ D * W := by
      have hrw : (((copies : ℝ) / D) ^ (1 / τ)) ^ ω = ((copies : ℝ) / D) ^ θ := by
        rw [← Real.rpow_mul (div_nonneg (Nat.cast_nonneg copies) hD.le)]
        congr 1
        rw [hθdef]
        field_simp
      rw [hrw] at hstep
      have hinv := Analysis.le_rpow_inv_of_rpow_mul_le (x := (copies : ℝ) / D)
        (div_nonneg (Nat.cast_nonneg copies) hD.le) hYpos hθpos hstep
      calc
        (copies : ℝ) = D * ((copies : ℝ) / D) := by field_simp
        _ ≤ D * W := mul_le_mul_of_nonneg_left hinv hD.le
    -- The Stirling estimate for the multinomial word count.
    have hloss1nn : (0 : ℝ) ≤ loss N := hloss.nonneg N
    have hwordsN : E ^ N ≤ loss N * ((words N : ℕ) : ℝ) := hwords N hNpos
    -- Behrend cancellation of the hashing modulus.
    have hcountReal : (3 : ℝ) * ((words N : ℕ) : ℝ) * (rothNumberNat (M / 2) : ℝ) ≤
        4 * ((M : ℝ) * (M : ℝ)) * (copies : ℝ) := by
      exact_mod_cast hcount
    have hrothnn : (0 : ℝ) ≤ (rothNumberNat (M / 2) : ℝ) := Nat.cast_nonneg _
    have hbeh : (3 * E ^ N) * (rothNumberNat (M / 2) : ℝ) ≤
        (4 * loss N * D * W) * ((M : ℝ) * (M : ℝ)) := by
      have h1 : (3 : ℝ) * E ^ N * (rothNumberNat (M / 2) : ℝ) ≤
          3 * (loss N * ((words N : ℕ) : ℝ)) * (rothNumberNat (M / 2) : ℝ) := by
        have := mul_le_mul_of_nonneg_left hwordsN (by norm_num : (0 : ℝ) ≤ 3)
        exact mul_le_mul_of_nonneg_right this hrothnn
      have h2 : loss N * ((3 : ℝ) * ((words N : ℕ) : ℝ) * (rothNumberNat (M / 2) : ℝ)) ≤
          loss N * (4 * ((M : ℝ) * (M : ℝ)) * (copies : ℝ)) :=
        mul_le_mul_of_nonneg_left hcountReal hloss1nn
      have h3 : loss N * (4 * ((M : ℝ) * (M : ℝ)) * (copies : ℝ)) ≤
          loss N * (4 * ((M : ℝ) * (M : ℝ)) * (D * W)) := by
        refine mul_le_mul_of_nonneg_left ?_ hloss1nn
        exact mul_le_mul_of_nonneg_left hcopiesLe (by positivity)
      nlinarith [h1, h2, h3]
    have hhalfPos : (0 : ℝ) < ((M / 2 : ℕ) : ℝ) := by
      have : 0 < M / 2 := by omega
      exact_mod_cast this
    have hΦN : (((fiber N : ℕ) : ℝ)) ≤ Φ ^ N := hfiber N
    have hhalfUpper : ((M / 2 : ℕ) : ℝ) ≤ 12 * Φ ^ (1 * N) := by
      have hnat : M / 2 ≤ 12 * fiber N := by omega
      calc
        ((M / 2 : ℕ) : ℝ) ≤ ((12 * fiber N : ℕ) : ℝ) := by exact_mod_cast hnat
        _ = 12 * ((fiber N : ℕ) : ℝ) := by push_cast; ring
        _ ≤ 12 * Φ ^ (1 * N) := by
            rw [one_mul]
            exact mul_le_mul_of_nonneg_left hΦN (by norm_num)
    have hsq := Growth.sqrt_log_le_mul_sqrt_succ (x := ((M / 2 : ℕ) : ℝ)) (c := 12)
      (G := Φ) (s := Φ + 12) (m := 1) (k := N)
      hhalfPos (by norm_num) hΦpos (by linarith) hhalfUpper
      (by nlinarith) (by push_cast; nlinarith)
    have ht4 : 4 * √(Real.log ((M / 2 : ℕ) : ℝ)) ≤
        4 * (Φ + 12) * √(((N + 1 : ℕ) : ℝ)) := by linarith
    have hMU : (M : ℝ) ≤ 24 * Φ ^ N := by
      have hnat : M ≤ 24 * fiber N := hupper
      calc
        (M : ℝ) ≤ ((24 * fiber N : ℕ) : ℝ) := by exact_mod_cast hnat
        _ = 24 * ((fiber N : ℕ) : ℝ) := by push_cast; ring
        _ ≤ 24 * Φ ^ N := mul_le_mul_of_nonneg_left hΦN (by norm_num)
    have hres := Growth.le_mul_exp_of_mul_rothNumberNat_le (M := M)
      (a := 3 * E ^ N) (b := 4 * loss N * D * W)
      (U := 24 * Φ ^ N)
      (t := 4 * (Φ + 12) * √(((N + 1 : ℕ) : ℝ)))
      hM2 (mul_nonneg (by norm_num) (pow_nonneg hE.le N))
      (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hloss1nn) hD.le) hWnn)
      hMU ht4 hbeh
    -- Divide out the geometric modulus and collect the loss.
    have hΦNpos : (0 : ℝ) < Φ ^ N := by positivity
    have hstep2 : (E / Φ) ^ N ≤ rectScheduleLossAt loss Φ D N * W := by
      have hgrowth : (E / Φ) ^ N = E ^ N / Φ ^ N := div_pow _ _ _
      rw [hgrowth, div_le_iff₀ hΦNpos]
      have hexpand : 3 * (4 * loss N * D * W) * (24 * Φ ^ N) *
          Real.exp (4 * (Φ + 12) * √(((N + 1 : ℕ) : ℝ))) =
            3 * ((rectScheduleLossAt loss Φ D N * W) * Φ ^ N) := by
        unfold rectScheduleLossAt
        ring
      rw [hexpand] at hres
      linarith
    -- Raise to the bootstrap exponent and restore the geometric shape.
    have hA1 : ((E / Φ) ^ N) ^ θ ≤ (rectScheduleLossAt loss Φ D N * W) ^ θ :=
      Real.rpow_le_rpow (pow_nonneg hG.le N) hstep2 hθpos.le
    have hA2 : (rectScheduleLossAt loss Φ D N * W) ^ θ =
        rectScheduleLossAt loss Φ D N ^ θ * (Z / Y) := by
      rw [Real.mul_rpow (rectScheduleLossAt_nonneg (hloss.nonneg N) hD.le) hWnn, hWdef,
        ← Real.rpow_mul (div_nonneg hZnn hYpos.le), one_div, inv_mul_cancel₀ hθpos.ne',
        Real.rpow_one]
    have hA3 : ((E / Φ) ^ θ) ^ N ≤ rectScheduleLossAt loss Φ D N ^ θ * (Z / Y) := by
      rw [Real.rpow_pow_comm hG.le θ N]
      exact hA1.trans_eq hA2
    have hA4 : ((E / Φ) ^ θ) ^ N * Y ≤ rectScheduleLossAt loss Φ D N ^ θ * Z := by
      have hmul := mul_le_mul_of_nonneg_right hA3 hYpos.le
      calc
        ((E / Φ) ^ θ) ^ N * Y
            ≤ (rectScheduleLossAt loss Φ D N ^ θ * (Z / Y)) * Y := hmul
        _ = rectScheduleLossAt loss Φ D N ^ θ * Z := by field_simp
    have hYeq : Y = (((A : ℝ)) ^ ω) ^ N := by
      rw [hYdef, Real.rpow_pow_comm hAnn ω N]
    rw [hYeq, hZdef, ← mul_pow] at hA4
    calc
      ((E / Φ) ^ θ * ((A : ℝ)) ^ ω) ^ (n + 1)
          = ((E / Φ) ^ θ * ((A : ℝ)) ^ ω) ^ N := by rw [hNdef]
      _ ≤ rectScheduleLossAt loss Φ D N ^ θ * ((2 : ℝ) ^ ω * ((R : ℝ)) ^ N) := hA4
      _ = (rectScheduleLossAt loss Φ D (n + 1) ^ θ * (2 : ℝ) ^ ω) *
            ((R : ℝ)) ^ (n + 1) := by rw [hNdef]; ring

/-- **The master scalar inequality of the schedule, at an arbitrary competitor envelope `Φ`.**

Letting the bootstrap exponent `τ` decrease to `ω(1,1,κ)` removes the last artefact of
`rectSchedule_rate_inequality`.  This is Huang--Pan's asymptotic sum inequality in
denominator-free form. -/
theorem rectSchedule_master_inequality {κ : ℝ} (hκ : 0 ≤ κ)
    {A C R : ℕ} (hA : 1 < A) (hR : 1 ≤ R) (hmid : ((A : ℝ)) ^ κ ≤ (C : ℝ))
    {words fiber : ℕ → ℕ} (hextract : RectangularScheduleExtraction K A C R words fiber)
    (hfiberPos : ∀ N : ℕ, 0 < N → 0 < fiber N)
    {E : ℝ} (hE : 0 < E) {loss : ℕ → ℝ} (hloss : Growth.Subexponential loss)
    (hwords : ∀ N : ℕ, 0 < N → E ^ N ≤ loss N * ((words N : ℕ) : ℝ))
    {Φ : ℝ} (hΦ : 1 ≤ Φ) (hfiber : ∀ N : ℕ, ((fiber N : ℕ) : ℝ) ≤ Φ ^ N) :
    E / Φ * ((A : ℝ)) ^ (rectangularOmega K κ) ≤ (R : ℝ) := by
  have hωtwo : (2 : ℝ) ≤ rectangularOmega K κ := two_le_rectangularOmega K κ
  have hApos : (0 : ℝ) < (A : ℝ) := by
    have : (1 : ℝ) < (A : ℝ) := by exact_mod_cast hA
    linarith
  have hΦpos : (0 : ℝ) < Φ := by linarith
  refine Analysis.le_of_rpow_div_mul_le (div_pos hE hΦpos)
    (Real.rpow_pos_of_pos hApos _) (by linarith) (fun τ hτ ↦ ?_)
  exact rectSchedule_rate_inequality K hκ hA hR hmid hextract hfiberPos hE hloss hwords hΦ
    hfiber hτ

end Rate

end AlgebraicComplexity
