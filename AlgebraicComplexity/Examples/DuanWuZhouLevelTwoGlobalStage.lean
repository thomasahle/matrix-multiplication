/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoGlobal
import AlgebraicComplexity.Examples.CoppersmithWinogradSquare
import AlgebraicComplexity.Combinatorics.TypeClassCounting
import AlgebraicComplexity.Tensor.BorderRankTransport

/-!
# Discharging the level-two endpoint's rank budget, and shrinking its count-side hypothesis

`Examples/DuanWuZhouLevelTwoGlobal.lean` reduces `[DuanWuZhou2022]`'s `omega < 2.374631` to the
single hypothesis `DwzLevelTwoAssembledStage`, a conjunction of

* a rank budget `Rtilde(sym_6 T) <= 64 ^ 6`, and
* one power of `sym_6 T` carrying a `tau`-weight at least `globalRate ^ (6 N)` at the *declared
  rational* rates.

This module discharges the first conjunct outright and replaces the second by a strictly weaker
one.

## The rank budget, discharged

`borderRankLE_symSix` is generic: a constructive border-rank certificate of size `r` for `T`
gives one of size `r ^ 6` for `sym_6 T`.  Its only new ingredient is that *every* leg permutation
preserves `BorderRankLE`, which the committed `permute_cycle` / `permute_xzy` transports supply
once `Tensor.Isomorphic.permute_cycle_cycle` and `Tensor.Isomorphic.permute_cycle_xzy` are used to
express `cycle.symm` and `swapXY` through them.  At `T = CW_6 tensor CW_6` --- the level-two
source, with the committed `cwSquarePartitionedTensor_borderRankLE` certificate of size
`(q + 2) ^ 2 = 64` --- this is exactly
`Rtilde(sym_6(CW_6 tensor CW_6)) <= 64 ^ 6 = 68719476736`, so no rank hypothesis survives.

## The count side, shrunk

`DwzLevelTwoCountingStage` asks for stages at *arbitrarily large* word lengths, whose weights
realize the **true** rate

`min (2 ^ H(alpha_X) / K) (2 ^ H(alpha_Z) / alphabar_p) * alphabar_val`

up to one named `Growth.Subexponential` loss.  That is the form `[DuanWuZhou2022]` section 6's
counting argument produces: every method-of-types step there pays a polynomial factor and lands on
an entropy exponent, never on a rational.  Three things are proved here to bridge the two:

* `dwz63_xRate_lt_exp` and `dwz63_zRate_lt_exp` --- the declared rationals are *strictly* below
  their entropy exponents (the committed enclosures certify slack `~9 * 10 ^ (-10)` nats, so the
  same `linarith` certificate that proves the committed `<=` proves `<`);
* `dwz63_globalRate_lt_trueGlobalRate` --- hence the declared global rate is strictly below the
  true one;
* `exists_cutoff_pow_le_of_pow_le_subexponential_mul` --- the real-valued form of
  `Analysis/CopyGrowth.lean`'s absorption, which turns the strict gap plus a subexponential loss
  into the exact declared-rate inequality at some large `n`.

## The method of types at the two marginals

`Combinatorics/TypeClassCounting.lean` is generic in the alphabet and the type; what is specific to
`[DuanWuZhou2022]` section 6.3 is the identification of its `profileEntropyNats` with the entropy
expressions the committed enclosures bound.  `profileEntropyNats_dwz63AlphaX` and
`profileEntropyNats_dwz63AlphaZ` are those identifications, and
`dwz63_xRate_pow_le_card_typeClass` / `dwz63_zRate_pow_le_card_typeClass` are the resulting
loss-free counting statements: from some word length on, the exact type-class cardinality of the
`X` (resp. `Z`) marginal profile is at least the declared rate raised to the word length.  These
are estimates (b) and (c) of `better_bound/dwz_endpoint_prep/PREP.md` section 4.3.

## What is still assumed

`DwzLevelTwoCountingStage` alone.  It is strictly weaker than `DwzLevelTwoAssembledStage`:
`dwzLevelTwoAssembledStage_of_countingStage` derives the latter from it *without any further
hypothesis*, so nothing here can be read as an unconditional bound on `omega` until a stage family
is constructed.  Its remaining content is the tensor-side construction of section 6 --- marked
two-leg hashing, compatibility cleanup, hole repair --- together with the four method-of-types
estimates this module does not instantiate (`N_alpha`, `N_triple`, `|compatibleSet|`,
`|typicalSet|`).

## Position in the library

Layer 4 (a client).  It imports the level-two endpoint, the Coppersmith--Winograd square, and the
generic method of types; it defines no new tensor.

Primary source: Ran Duan, Hongxun Wu and Renfei Zhou, *Faster Matrix Multiplication via Asymmetric
Hashing*, arXiv:2210.10173, sections 2.1 and 6.2--6.3.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity AsymmetricGlobal Tensor

universe u v w

noncomputable section

/-! ## Border rank under an arbitrary leg permutation -/

section Rank

variable {K : Type u} [CommSemiring K]
variable {V : Leg → Type v} [∀ c, AddCommMonoid (V c)] [∀ c, Module K (V c)]

/-- Border rank is preserved by the inverse three-cycle.  `cycle.symm` is `cycle` squared, and
`Tensor.Isomorphic.permute_cycle_cycle` records that identification legwise. -/
theorem borderRankLE_permute_cycle_symm {r : ℕ} {T : Tensor3 K V} (h : BorderRankLE r T) :
    BorderRankLE r (Tensor.permute cycle.symm T) :=
  (BorderRankLE.isomorphic (Tensor.Isomorphic.permute_cycle_cycle T)).mp
    (BorderRankLE.permute_cycle (BorderRankLE.permute_cycle h))

/-- Border rank is preserved by the `X`--`Y` transposition, the one leg permutation
`[DuanWuZhou2022]`'s `sym_6` needs beyond the cyclic ones.  It is `xzy` followed by `cycle`
(`Tensor.Isomorphic.permute_cycle_xzy`). -/
theorem borderRankLE_permute_swapXY {r : ℕ} {T : Tensor3 K V} (h : BorderRankLE r T) :
    BorderRankLE r (Tensor.permute Tensor.swapXY T) :=
  (BorderRankLE.isomorphic (Tensor.Isomorphic.permute_cycle_xzy T)).mp
    (BorderRankLE.permute_cycle (BorderRankLE.permute_xzy h))

/-- **The three-symmetrization cubes the border-rank budget.**  `sym_3 T` is the external product
of the three cyclic orientations of `T`, and each of them carries `T`'s certificate. -/
theorem borderRankLE_symThree {r : ℕ} {T : Tensor3 K V} (h : BorderRankLE r T) :
    BorderRankLE (r ^ 3) (symThree K T) := by
  have hprod : BorderRankLE (r * r * r) (symThree K T) :=
    BorderRankLE.external (BorderRankLE.external h (BorderRankLE.permute_cycle h))
      (borderRankLE_permute_cycle_symm h)
  have hpow : r * r * r = r ^ 3 := by ring
  rwa [hpow] at hprod

/-- **The six-symmetrization raises the border-rank budget to the sixth power.**

`sym_6 T = sym_3 T tensor (sym_3 T)^swap`, so the two factors both carry the cubed certificate of
`borderRankLE_symThree`, the second one through `borderRankLE_permute_swapXY`. -/
theorem borderRankLE_symSix {r : ℕ} {T : Tensor3 K V} (h : BorderRankLE r T) :
    BorderRankLE (r ^ 6) (symSix K T) := by
  have h3 := borderRankLE_symThree (K := K) h
  have hprod : BorderRankLE (r ^ 3 * r ^ 3) (symSix K T) :=
    BorderRankLE.external h3 (borderRankLE_permute_swapXY h3)
  have hpow : r ^ 3 * r ^ 3 = r ^ 6 := by ring
  rwa [hpow] at hprod

/-- **The rank input of the asymmetric global value theorem, from a border-rank certificate.**
This is the submultiplicativity step `AsymmetricGlobalValue.lean` names in prose but does not
prove: `Rtilde(sym_6 T) <= R_border(T) ^ 6`. -/
theorem asymptoticRank_symSix_le {r : ℕ} {T : Tensor3 K V} (h : BorderRankLE r T) :
    Tensor.asymptoticRank (symSix K T) ≤ (r : ℝ) ^ 6 := by
  have hle := Tensor.asymptoticRank_le_of_borderRankLE (borderRankLE_symSix (K := K) h)
  have hcast : (((r ^ 6 : ℕ) : ℝ)) = (r : ℝ) ^ 6 := by push_cast; ring
  rwa [hcast] at hle

end Rank

/-! ## The level-two source and its discharged rank budget -/

section LevelTwoRank

variable (K : Type u) [CommRing K]

/-- **The level-two source of `[DuanWuZhou2022]` section 6.3**: the Coppersmith--Winograd tensor
at `q = 6`, tensored with itself and regrouped.  This is the `T` the section 6.3 parameters are
optimized for. -/
def dwz63Source := (cwSquarePartitionedTensor K dwz63Q).realize

/-- The level-two source has constructive border rank at most `(q + 2) ^ 2 = 64`.  This is the
committed square certificate at `q = 6`. -/
theorem dwz63Source_borderRankLE : BorderRankLE 64 (dwz63Source K) := by
  have h := cwSquarePartitionedTensor_borderRankLE K dwz63Q
  have hq : (dwz63Q + 2) ^ 2 = 64 := by norm_num [dwz63Q]
  rw [hq] at h
  exact h

/-- **The rank budget of `DwzLevelTwoAssembledStage`, discharged.**

`Rtilde(sym_6(CW_6 tensor CW_6)) <= 64 ^ 6 = 68719476736`.  Nothing is assumed: the certificate is
the committed `cwSquarePartitionedTensor_borderRankLE`, and the sixth power is
`borderRankLE_symSix`. -/
theorem dwz63_asymptoticRank_symSix_le :
    Tensor.asymptoticRank (symSix K (dwz63Source K)) ≤ 68719476736 := by
  have h := asymptoticRank_symSix_le (K := K) (dwz63Source_borderRankLE K)
  have hnum : ((64 : ℕ) : ℝ) ^ 6 = 68719476736 := by norm_num
  rwa [hnum] at h

end LevelTwoRank

/-! ## The two marginal profiles of section 6.3 -/

/-- The `X` (equivalently `Y`) marginal of `[DuanWuZhou2022]` section 6.3's distribution, as an
integral profile of total mass `10 ^ 8`. -/
def dwz63AlphaX : Fin 5 → ℕ := ![12957007, 43285992, 41147194, 2585076, 24731]

/-- The `Z` marginal of `[DuanWuZhou2022]` section 6.3's distribution, as an integral profile of
total mass `10 ^ 8`. -/
def dwz63AlphaZ : Fin 5 → ℕ := ![12598769, 44135552, 40822513, 2422306, 20860]

theorem profileMass_dwz63AlphaX : WordType.profileMass dwz63AlphaX = 100000000 := by
  simp [WordType.profileMass, dwz63AlphaX, Fin.sum_univ_five]

theorem profileMass_dwz63AlphaZ : WordType.profileMass dwz63AlphaZ = 100000000 := by
  simp [WordType.profileMass, dwz63AlphaZ, Fin.sum_univ_five]

/-- **The `X` marginal's method-of-types entropy is section 6.3's `H_e(alpha_X)`.**  This is the
bridge between the generic `Combinatorics/TypeClassCounting.lean` vocabulary and the committed
enclosures of `Examples/DuanWuZhouLevelTwoGlobalArithmetic.lean`. -/
theorem profileEntropyNats_dwz63AlphaX :
    WordType.profileEntropyNats dwz63AlphaX = dwz63EntropyX := by
  have v0 : dwz63AlphaX 0 = 12957007 := by simp [dwz63AlphaX]
  have v1 : dwz63AlphaX 1 = 43285992 := by simp [dwz63AlphaX]
  have v2 : dwz63AlphaX 2 = 41147194 := by simp [dwz63AlphaX]
  have v3 : dwz63AlphaX 3 = 2585076 := by simp [dwz63AlphaX]
  have v4 : dwz63AlphaX 4 = 24731 := by simp [dwz63AlphaX]
  have h0 : Real.log ((12957007 : ℝ) / 100000000) = -Real.log (100000000 / 12957007) := by
    rw [show ((12957007 : ℝ) / 100000000) = ((100000000 : ℝ) / 12957007)⁻¹ by norm_num,
      Real.log_inv]
  have h1 : Real.log ((43285992 : ℝ) / 100000000) = -Real.log (12500000 / 5410749) := by
    rw [show ((43285992 : ℝ) / 100000000) = ((12500000 : ℝ) / 5410749)⁻¹ by norm_num,
      Real.log_inv]
  have h2 : Real.log ((41147194 : ℝ) / 100000000) = -Real.log (50000000 / 20573597) := by
    rw [show ((41147194 : ℝ) / 100000000) = ((50000000 : ℝ) / 20573597)⁻¹ by norm_num,
      Real.log_inv]
  have h3 : Real.log ((2585076 : ℝ) / 100000000) = -Real.log (25000000 / 646269) := by
    rw [show ((2585076 : ℝ) / 100000000) = ((25000000 : ℝ) / 646269)⁻¹ by norm_num,
      Real.log_inv]
  have h4 : Real.log ((24731 : ℝ) / 100000000) = -Real.log (100000000 / 24731) := by
    rw [show ((24731 : ℝ) / 100000000) = ((100000000 : ℝ) / 24731)⁻¹ by norm_num,
      Real.log_inv]
  unfold WordType.profileEntropyNats
  rw [Fin.sum_univ_five, profileMass_dwz63AlphaX, v0, v1, v2, v3, v4]
  simp only [Real.negMulLog]
  push_cast
  rw [h0, h1, h2, h3, h4]
  unfold dwz63EntropyX
  ring

/-- **The `Z` marginal's method-of-types entropy is section 6.3's `H_e(alpha_Z)`.** -/
theorem profileEntropyNats_dwz63AlphaZ :
    WordType.profileEntropyNats dwz63AlphaZ = dwz63EntropyZ := by
  have v0 : dwz63AlphaZ 0 = 12598769 := by simp [dwz63AlphaZ]
  have v1 : dwz63AlphaZ 1 = 44135552 := by simp [dwz63AlphaZ]
  have v2 : dwz63AlphaZ 2 = 40822513 := by simp [dwz63AlphaZ]
  have v3 : dwz63AlphaZ 3 = 2422306 := by simp [dwz63AlphaZ]
  have v4 : dwz63AlphaZ 4 = 20860 := by simp [dwz63AlphaZ]
  have h0 : Real.log ((12598769 : ℝ) / 100000000) = -Real.log (100000000 / 12598769) := by
    rw [show ((12598769 : ℝ) / 100000000) = ((100000000 : ℝ) / 12598769)⁻¹ by norm_num,
      Real.log_inv]
  have h1 : Real.log ((44135552 : ℝ) / 100000000) = -Real.log (781250 / 344809) := by
    rw [show ((44135552 : ℝ) / 100000000) = ((781250 : ℝ) / 344809)⁻¹ by norm_num,
      Real.log_inv]
  have h2 : Real.log ((40822513 : ℝ) / 100000000) = -Real.log (100000000 / 40822513) := by
    rw [show ((40822513 : ℝ) / 100000000) = ((100000000 : ℝ) / 40822513)⁻¹ by norm_num,
      Real.log_inv]
  have h3 : Real.log ((2422306 : ℝ) / 100000000) = -Real.log (50000000 / 1211153) := by
    rw [show ((2422306 : ℝ) / 100000000) = ((50000000 : ℝ) / 1211153)⁻¹ by norm_num,
      Real.log_inv]
  have h4 : Real.log ((20860 : ℝ) / 100000000) = -Real.log (5000000 / 1043) := by
    rw [show ((20860 : ℝ) / 100000000) = ((5000000 : ℝ) / 1043)⁻¹ by norm_num,
      Real.log_inv]
  unfold WordType.profileEntropyNats
  rw [Fin.sum_univ_five, profileMass_dwz63AlphaZ, v0, v1, v2, v3, v4]
  simp only [Real.negMulLog]
  push_cast
  rw [h0, h1, h2, h3, h4]
  unfold dwz63EntropyZ
  ring

/-! ## The declared rationals are strictly below their entropy exponents -/

/-- The committed `X` enclosures certify a positive rational slack, so the declared rational is
*strictly* below `H_e(alpha_X)`.  The same atom certificate that proves the committed
`dwz63_log_xRate_le` proves the strict form. -/
theorem dwz63_log_xRate_lt : Real.log dwz63XRate < dwz63EntropyX := by
  simp only [dwz63XRate, dwz63EntropyX]
  linarith [dwz63_atom_xRate_le, dwz63_atom_x0_ge, dwz63_atom_x1_ge, dwz63_atom_x2_ge,
    dwz63_atom_x3_ge, dwz63_atom_x4_ge]

/-- The declared `xRate` is strictly below `alphabar_X = 2 ^ H(alpha_X)`. -/
theorem dwz63_xRate_lt_exp : dwz63XRate < Real.exp dwz63EntropyX := by
  have h := Real.exp_lt_exp.mpr dwz63_log_xRate_lt
  rwa [Real.exp_log dwz63XRate_pos] at h

/-- The strict form of the committed `Z` enclosure aggregation. -/
theorem dwz63_log_zRate_lt : Real.log dwz63ZRate < dwz63EntropyZ := by
  simp only [dwz63ZRate, dwz63EntropyZ]
  linarith [dwz63_atom_zRate_le, dwz63_atom_z0_ge, dwz63_atom_z1_ge, dwz63_atom_z2_ge,
    dwz63_atom_z3_ge, dwz63_atom_z4_ge]

/-- The declared `zRate` is strictly below `alphabar_Z = 2 ^ H(alpha_Z)`. -/
theorem dwz63_zRate_lt_exp : dwz63ZRate < Real.exp dwz63EntropyZ := by
  have h := Real.exp_lt_exp.mpr dwz63_log_zRate_lt
  rwa [Real.exp_log dwz63ZRate_pos] at h

/-! ## The method of types at the two marginals -/

/-- Raising a positive real to the mass of the profile turns a per-letter rate into the rate the
proportional type class grows at. -/
private theorem exp_mass_mul (m : ℕ) (x : ℝ) : Real.exp ((m : ℝ) * x) = Real.exp x ^ m := by
  induction m with
  | zero => simp
  | succ k ih =>
      have hstep : ((k + 1 : ℕ) : ℝ) * x = (k : ℝ) * x + x := by push_cast; ring
      rw [hstep, Real.exp_add, ih, pow_succ]

/-- **Method-of-types estimate (b) of `PREP.md` section 4.3, at the declared rational.**

From some repetition count on, the exact number of length-`10 ^ 8 k` words with the `X` marginal
profile is at least `dwz63XRate ^ (10 ^ 8 k)` --- no loss factor remains.  The polynomial Stirling
loss is absorbed by the strict gap `dwz63XRate < 2 ^ H(alpha_X)`. -/
theorem dwz63_xRate_pow_le_card_typeClass :
    ∃ cutoff : ℕ, ∀ k : ℕ, cutoff ≤ k →
      dwz63XRate ^ (100000000 * k) ≤
        (((WordType.typeClass (WordType.profileMass dwz63AlphaX * k)
          (WordType.proportionalCounts dwz63AlphaX k)).card : ℕ) : ℝ) := by
  have hmass : 0 < WordType.profileMass dwz63AlphaX := by
    rw [profileMass_dwz63AlphaX]; norm_num
  have hlower : (0 : ℝ) < dwz63XRate ^ (100000000 : ℕ) := pow_pos dwz63XRate_pos _
  have hlt : dwz63XRate ^ (100000000 : ℕ) <
      (2 : ℝ) ^ ((WordType.profileMass dwz63AlphaX : ℝ) *
        WordType.profileEntropyBits dwz63AlphaX) := by
    rw [WordType.two_rpow_mul_profileEntropyBits, profileMass_dwz63AlphaX,
      profileEntropyNats_dwz63AlphaX]
    rw [exp_mass_mul]
    exact pow_lt_pow_left₀ dwz63_xRate_lt_exp dwz63XRate_pos.le (by norm_num)
  obtain ⟨cutoff, hcutoff⟩ :=
    WordType.exists_cutoff_forall_pow_le_card_proportionalTypeClass dwz63AlphaX hmass hlower hlt
  refine ⟨cutoff, fun k hk ↦ ?_⟩
  have := hcutoff k hk
  rwa [← pow_mul] at this

/-- **Method-of-types estimate (c) of `PREP.md` section 4.3, at the declared rational.** -/
theorem dwz63_zRate_pow_le_card_typeClass :
    ∃ cutoff : ℕ, ∀ k : ℕ, cutoff ≤ k →
      dwz63ZRate ^ (100000000 * k) ≤
        (((WordType.typeClass (WordType.profileMass dwz63AlphaZ * k)
          (WordType.proportionalCounts dwz63AlphaZ k)).card : ℕ) : ℝ) := by
  have hmass : 0 < WordType.profileMass dwz63AlphaZ := by
    rw [profileMass_dwz63AlphaZ]; norm_num
  have hlower : (0 : ℝ) < dwz63ZRate ^ (100000000 : ℕ) := pow_pos dwz63ZRate_pos _
  have hlt : dwz63ZRate ^ (100000000 : ℕ) <
      (2 : ℝ) ^ ((WordType.profileMass dwz63AlphaZ : ℝ) *
        WordType.profileEntropyBits dwz63AlphaZ) := by
    rw [WordType.two_rpow_mul_profileEntropyBits, profileMass_dwz63AlphaZ,
      profileEntropyNats_dwz63AlphaZ]
    rw [exp_mass_mul]
    exact pow_lt_pow_left₀ dwz63_zRate_lt_exp dwz63ZRate_pos.le (by norm_num)
  obtain ⟨cutoff, hcutoff⟩ :=
    WordType.exists_cutoff_forall_pow_le_card_proportionalTypeClass dwz63AlphaZ hmass hlower hlt
  refine ⟨cutoff, fun k hk ↦ ?_⟩
  have := hcutoff k hk
  rwa [← pow_mul] at this

/-! ## The true global rate, and the strict gap the declared one leaves -/

/-- **The true copy rate of section 6.3**, `min (alphabar_X / K) (alphabar_Z / alphabar_p)`, with
the two marginal rates at their exact entropy exponents and the compatibility rate at its exact
value.  The hash-loss multiplier `K` stays rational --- it is an *upper* bound for the true loss,
so using it here only makes the true rate smaller.  The ambient rate `2 ^ H(alpha)` has already
cancelled, exactly as in `GlobalRateData.copyRate_eq_min`. -/
def dwz63TrueCopyRate : ℝ :=
  min (Real.exp dwz63EntropyX / dwz63HashLossMultiplier)
    (Real.exp dwz63EntropyZ / Real.exp dwz63LogCompat)

/-- **The true global rate of section 6.3**: the true copy rate times the exact leaf value rate. -/
def dwz63TrueGlobalRate : ℝ := dwz63TrueCopyRate * Real.exp dwz63LogVal

theorem dwz63TrueCopyRate_pos : 0 < dwz63TrueCopyRate := by
  refine lt_min ?_ ?_
  · exact div_pos (Real.exp_pos _) dwz63HashLossMultiplier_pos
  · exact div_pos (Real.exp_pos _) (Real.exp_pos _)

theorem dwz63TrueGlobalRate_pos : 0 < dwz63TrueGlobalRate :=
  mul_pos dwz63TrueCopyRate_pos (Real.exp_pos _)

/-- **The declared rational global rate is strictly below the true one.**

Branch by branch: the hashing branch because `xRate < 2 ^ H(alpha_X)` at a common denominator,
the combination-loss branch because `zRate < 2 ^ H(alpha_Z)` and `alphabar_p <= compatRate`, and
the leaf factor because `valRate <= alphabar_val`.  This strict gap is what absorbs the whole
polynomial loss of the count side. -/
theorem dwz63_globalRate_lt_trueGlobalRate (ambient : ℝ) (hambient : 0 < ambient) :
    (dwz63RateData ambient hambient).globalRate < dwz63TrueGlobalRate := by
  have hbranch1 : dwz63XRate / dwz63HashLossMultiplier <
      Real.exp dwz63EntropyX / dwz63HashLossMultiplier := by
    rw [div_eq_mul_inv, div_eq_mul_inv]
    exact mul_lt_mul_of_pos_right dwz63_xRate_lt_exp (inv_pos.mpr dwz63HashLossMultiplier_pos)
  have hbranch2 : dwz63ZRate / dwz63CompatRate <
      Real.exp dwz63EntropyZ / Real.exp dwz63LogCompat := by
    rw [div_lt_div_iff₀ dwz63CompatRate_pos (Real.exp_pos _)]
    calc dwz63ZRate * Real.exp dwz63LogCompat
        < Real.exp dwz63EntropyZ * Real.exp dwz63LogCompat :=
          mul_lt_mul_of_pos_right dwz63_zRate_lt_exp (Real.exp_pos _)
      _ ≤ Real.exp dwz63EntropyZ * dwz63CompatRate :=
          mul_le_mul_of_nonneg_left dwz63_exp_le_compatRate (Real.exp_pos _).le
  have hmin : min (dwz63XRate / dwz63HashLossMultiplier) (dwz63ZRate / dwz63CompatRate) <
      min (Real.exp dwz63EntropyX / dwz63HashLossMultiplier)
        (Real.exp dwz63EntropyZ / Real.exp dwz63LogCompat) :=
    lt_min (lt_of_le_of_lt (min_le_left _ _) hbranch1)
      (lt_of_le_of_lt (min_le_right _ _) hbranch2)
  have hminPos : 0 < min (Real.exp dwz63EntropyX / dwz63HashLossMultiplier)
      (Real.exp dwz63EntropyZ / Real.exp dwz63LogCompat) := by
    refine lt_min ?_ ?_
    · exact div_pos (Real.exp_pos _) dwz63HashLossMultiplier_pos
    · exact div_pos (Real.exp_pos _) (Real.exp_pos _)
  rw [dwz63RateData_globalRate]
  unfold dwz63TrueGlobalRate dwz63TrueCopyRate
  calc min (dwz63XRate / dwz63HashLossMultiplier) (dwz63ZRate / dwz63CompatRate) * dwz63ValRate
      < min (Real.exp dwz63EntropyX / dwz63HashLossMultiplier)
          (Real.exp dwz63EntropyZ / Real.exp dwz63LogCompat) * dwz63ValRate :=
        mul_lt_mul_of_pos_right hmin dwz63ValRate_pos
    _ ≤ min (Real.exp dwz63EntropyX / dwz63HashLossMultiplier)
          (Real.exp dwz63EntropyZ / Real.exp dwz63LogCompat) * Real.exp dwz63LogVal :=
        mul_le_mul_of_nonneg_left dwz63_valRate_le_exp hminPos.le

/-- **Anti-vacuity: the true rate genuinely clears the square border-rank budget.**

`64 ^ 6 < dwz63TrueGlobalRate ^ 6`.  So `DwzLevelTwoCountingStage` is asking for a rate that is
*not* below the budget it has to beat --- the residual is the right shape, and the strict
comparison it needs is available before any construction is attempted. -/
theorem dwz63_rankBudget_lt_trueGlobalRate_pow :
    (68719476736 : ℝ) < dwz63TrueGlobalRate ^ 6 :=
  (dwz63_rankBudget_lt_globalRate_pow 1 one_pos).trans
    (pow_lt_pow_left₀ (dwz63_globalRate_lt_trueGlobalRate 1 one_pos)
      (dwz63RateData 1 one_pos).globalRate_pos.le (by norm_num))

/-! ## The subexponential absorption, real-valued -/

/-- The real-valued form of `Growth.Subexponential.exists_forall_pow_le_natCast_of_pow_le_mul`
(`Analysis/CopyGrowth.lean`), which states the same absorption for a natural-valued copy count.
The proof is the same: eventually `loss k <= (base / lowerBase) ^ k`, and the positive factor
`base ^ k` cancels. -/
theorem exists_cutoff_pow_le_of_pow_le_subexponential_mul
    {base lowerBase : ℝ} {loss : ℕ → ℝ} (hloss : Growth.Subexponential loss)
    (hlower : 0 < lowerBase) (hlt : lowerBase < base) :
    ∃ cutoff : ℕ, ∀ (k : ℕ) (value : ℝ), cutoff ≤ k → 0 ≤ value →
      base ^ k ≤ loss k * value → lowerBase ^ k ≤ value := by
  have hbase : 0 < base := hlower.trans hlt
  have hratio : 1 < base / lowerBase := (one_lt_div hlower).2 hlt
  obtain ⟨cutoff, hcutoff⟩ := hloss.eventually_le_pow hratio
  refine ⟨cutoff, fun k value hk hvalue hfinite ↦ ?_⟩
  have hkey : base ^ k ≤ base ^ k / lowerBase ^ k * value := by
    calc base ^ k ≤ loss k * value := hfinite
      _ ≤ (base / lowerBase) ^ k * value := mul_le_mul_of_nonneg_right (hcutoff k hk) hvalue
      _ = base ^ k / lowerBase ^ k * value := by rw [div_pow]
  have hlowerPow : 0 < lowerBase ^ k := pow_pos hlower k
  rw [div_mul_eq_mul_div, le_div_iff₀ hlowerPow] at hkey
  exact le_of_mul_le_mul_left hkey (pow_pos hbase k)

/-! ## The residual, and the reduction -/

section Reduction

variable {F : Type u} [Field F] {V : Leg → Type v}
variable [∀ c, AddCommMonoid (V c)] [∀ c, Module F (V c)]

/-- **The count-side residual of `[DuanWuZhou2022]` section 6.3.**

At arbitrarily large word lengths `n` there is a `tau`-weight on `sym_6(T)^{tensor n}` realizing
the *true* global rate `dwz63TrueGlobalRate` raised to `6 n`, up to one fixed subexponential loss
sequence.

This is exactly the shape section 6's counting argument produces: marked two-leg hashing retains
`N_alpha / (4 M)` good triples, the compatibility cleanup and the Hole Lemma batch them, and the
six method-of-types estimates identify the surviving count with an entropy exponent *up to a
polynomial factor* --- never with a rational.  Both weakenings relative to
`DwzLevelTwoAssembledStage` are in the supplier's favour: the rate is the true one rather than the
declared rational, and the bound is lossy rather than exact.  Nothing is lost by either:
`dwzLevelTwoAssembledStage_of_countingStage` below closes the gap. -/
def DwzLevelTwoCountingStage (T : Tensor3 F V) : Prop :=
  ∃ loss : ℕ → ℝ, Growth.Subexponential loss ∧
    ∀ cutoff : ℕ, ∃ n : ℕ, cutoff ≤ n ∧ 0 < n ∧ ∃ value : ℝ, 0 < value ∧
      HasTauWeight F (Tensor.power (symSix F T) n) dwz63Tau value ∧
      dwz63TrueGlobalRate ^ (6 * n) ≤ loss n * value

/-- **One length-`n` repaired stage, read at the true rates.**

The true-rate analogue of `dwzLevelTwoAssembledStage_of_repairedStage`: it consumes exactly the
premises of M-DWZ6's `AsymmetricGlobal.omega_lt_three_mul_of_repairedStage` --- a restriction of
`sym_6(T)^{tensor n}` onto `card beta` copies of a leaf, a `tau`-weight for the leaf, and the two
rate bounds --- and produces one member of `DwzLevelTwoCountingStage`'s family.  The copy count is
allowed the subexponential factor `lossN`; the leaf value is not, because the leaf's value is
exact.  This is what a count-side client has to produce at each word length. -/
theorem exists_value_of_repairedStage_true
    {T : Tensor3 F V} {W : Leg → Type v}
    [∀ c, AddCommMonoid (W c)] [∀ c, Module F (W c)]
    {leaf : Tensor3 F W} {leafValue lossN : ℝ} (n : ℕ)
    {β : Type v} [Fintype β] [DecidableEq β]
    (hstage : Restricts (Tensor.power (symSix F T) n)
      (Tensor.indexedDirectSum (V := fun _ : β ↦ W) fun _ ↦ leaf))
    (hleaf : HasTauWeight F leaf dwz63Tau leafValue)
    (hleafValue : 0 < leafValue) (hcards : 0 < Fintype.card β)
    (hcount : dwz63TrueCopyRate ^ (6 * n) ≤ lossN * (Fintype.card β : ℝ))
    (hvalue : Real.exp dwz63LogVal ^ (6 * n) ≤ leafValue) :
    ∃ value : ℝ, 0 < value ∧
      HasTauWeight F (Tensor.power (symSix F T) n) dwz63Tau value ∧
      dwz63TrueGlobalRate ^ (6 * n) ≤ lossN * value := by
  have hcardPos : (0 : ℝ) < (Fintype.card β : ℝ) := by exact_mod_cast hcards
  refine ⟨(Fintype.card β : ℝ) * leafValue, mul_pos hcardPos hleafValue,
    hasTauWeight_of_repairedStage n hstage hleaf, ?_⟩
  have hexpand : dwz63TrueGlobalRate ^ (6 * n) =
      dwz63TrueCopyRate ^ (6 * n) * Real.exp dwz63LogVal ^ (6 * n) := by
    rw [dwz63TrueGlobalRate, mul_pow]
  rw [hexpand]
  calc dwz63TrueCopyRate ^ (6 * n) * Real.exp dwz63LogVal ^ (6 * n)
      ≤ lossN * (Fintype.card β : ℝ) * leafValue :=
        mul_le_mul hcount hvalue (pow_pos (Real.exp_pos _) _).le
          ((pow_pos dwz63TrueCopyRate_pos _).le.trans hcount)
    _ = lossN * ((Fintype.card β : ℝ) * leafValue) := by ring

/-- **The count-side residual implies the assembled stage.**

Given the rank budget, `DwzLevelTwoCountingStage` supplies `DwzLevelTwoAssembledStage` with no
further hypothesis: the strict gap `globalRate < dwz63TrueGlobalRate` of
`dwz63_globalRate_lt_trueGlobalRate` absorbs the subexponential loss, and the arbitrarily large
`n` provides a word length past the resulting cutoff. -/
theorem dwzLevelTwoAssembledStage_of_countingStage
    {T : Tensor3 F V} {ambient : ℝ} (hambient : 0 < ambient)
    (hrank : Tensor.asymptoticRank (symSix F T) ≤ 68719476736)
    (hcount : DwzLevelTwoCountingStage T) :
    DwzLevelTwoAssembledStage T (dwz63RateData ambient hambient) := by
  obtain ⟨loss, hloss, hstages⟩ := hcount
  have hglobalPos := (dwz63RateData ambient hambient).globalRate_pos
  have hgap : (dwz63RateData ambient hambient).globalRate ^ 6 < dwz63TrueGlobalRate ^ 6 :=
    pow_lt_pow_left₀ (dwz63_globalRate_lt_trueGlobalRate ambient hambient) hglobalPos.le
      (by norm_num)
  obtain ⟨cutoff, hcutoff⟩ :=
    exists_cutoff_pow_le_of_pow_le_subexponential_mul hloss (pow_pos hglobalPos 6) hgap
  obtain ⟨n, hn, hnpos, value, hvaluePos, hweight, hbound⟩ := hstages cutoff
  refine ⟨hrank, n, value, hnpos, hvaluePos, hweight, ?_⟩
  have hpow : ∀ x : ℝ, x ^ (6 * n) = (x ^ 6) ^ n := by
    intro x
    rw [← pow_mul]
  rw [hpow] at hbound ⊢
  exact hcutoff n value hn hvaluePos.le hbound

/-- **`[DuanWuZhou2022]`'s level-two endpoint from the count side alone.**

The rank budget and every numerical obligation of section 6.3 are discharged; what remains is
`DwzLevelTwoCountingStage`, one hypothesis strictly weaker than the `DwzLevelTwoAssembledStage`
of `Examples/DuanWuZhouLevelTwoGlobal.lean`. -/
theorem omega_lt_2374631_of_countingStage
    {T : Tensor3 F V} {ambient : ℝ} (hambient : 0 < ambient)
    (hrank : Tensor.asymptoticRank (symSix F T) ≤ 68719476736)
    (hcount : DwzLevelTwoCountingStage T) :
    omega F < (2374631 / 1000000 : ℝ) :=
  omega_lt_2374631_of_dwzLevelTwoAssembledStage hambient
    (dwzLevelTwoAssembledStage_of_countingStage hambient hrank hcount)

end Reduction

/-! ## The endpoint at the level-two source, with no rank hypothesis -/

/-- **`omega < 2.374631` at `[DuanWuZhou2022]`'s own level-two source, modulo the count side.**

Every hypothesis of `Examples/DuanWuZhouLevelTwoGlobal.lean`'s endpoint has been discharged except
`DwzLevelTwoCountingStage`: the rank budget by `dwz63_asymptoticRank_symSix_le` (from the committed
Coppersmith--Winograd square border-rank certificate at `q = 6`) and the arithmetic by the
committed enclosure table.  The single remaining input is the tensor-side construction of section
6 together with the four method-of-types estimates this module does not instantiate.

It is stated with a free ambient rate, exactly as the endpoint is: `2 ^ H(alpha)` cancels. -/
theorem omega_lt_2374631_of_dwz63CountingStage {F : Type u} [Field F]
    (hcount : DwzLevelTwoCountingStage (dwz63Source F)) :
    omega F < (2374631 / 1000000 : ℝ) :=
  omega_lt_2374631_of_countingStage (T := dwz63Source F) (ambient := 1) one_pos
    (dwz63_asymptoticRank_symSix_le F) hcount

end

end AlgebraicComplexity.Examples
