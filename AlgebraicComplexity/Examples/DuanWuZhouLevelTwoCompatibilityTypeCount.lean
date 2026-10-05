/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoCompetitorRateBrick
import AlgebraicComplexity.Analysis.CompatibilityRate
import AlgebraicComplexity.Combinatorics.TypeClassCounting

set_option autoImplicit false

/-!
# `Dwz63CompatibleFractionUpper` from the conditional-entropy mass, generically

Layer 4 (`AlgebraicComplexity/Examples/`).  This module discharges the *method-of-types* half of
the brick named in `Examples/DuanWuZhouLevelTwoCompetitorRateBrick.lean`: it turns the exact
product closed forms of `Combinatorics/CompatibleSplitCount.lean` into the division-free
exponential bound

`|compatibleSet comp₀| ≤ slack n · ᾱ_p ^ n · |T_K|`,

for an *arbitrary* `SplitRequirements`, with an explicit polynomial `slack` and the single
hypothesis that the record's conditional-entropy mass is at most `n · log ᾱ_p`.

> R. Duan, H. Wu and R. Zhou, *Faster Matrix Multiplication via Asymmetric Hashing*,
> arXiv:2210.10173v5, **§6.2 (`global_value.tex`)**, `lemma:pcomp_g` and the compatibility-rate
> discussion around `claim:hole_frac_low` (`[DuanWuZhou2022]`).

## There is no union over types

`Analysis/CompatibilityRate.lean`'s non-goal paragraph describes the missing step as
"zero-tolerant method-of-types estimates".  It is worth recording that the *pigeonhole over joint
types* the method of types usually needs does **not** appear here, and neither does its polynomial
number-of-types factor.  `CompatibleSplit.SplitRequirements.compatibleSet` is by definition a
single `conditionalTypeClass`, and `card_compatibleSet_eq_prod` already evaluates it as one exact
product of multinomial coefficients — one factor per requirement cell — with `typicalSet` likewise
one product over the Z-indices.  So the decomposition into type classes is a committed identity
with exactly one class per side, the count of occupied types is `1`, and the only estimates left
are the two directions of Stirling on each *row*.

## The two directions, both zero-tolerant

* `dwz63_multinomial_le_exp_profileMassEntropy` — the loss-free upper bound
  `multinomial(θ) ≤ exp(mass(θ) · H(θ))`, extended to rows of mass `0` (a compatibility profile
  has structurally zero `Sum.inl` rows at every interior component, and `pooledSplit` rows of mass
  zero at every Z-index carrying no interior component).  Positive-mass rows are the committed
  `multinomial_le_exp_profileEntropy` of `Analysis/StructuralZeroMultinomialEntropy.lean`, which
  is already tolerant of structural zeroes *inside* a row.
* `dwz63_exp_profileMassEntropy_le_loss_mul_multinomial` — the matching lower bound with the
  committed Stirling loss `typeClassEntropyLoss`, again extended to mass-zero rows.

Multiplying the first over the requirement cells and the second over the Z-indices gives
`dwz63_prod_multinomial_le_exp_rowEntropyMass` and
`dwz63_exp_rowEntropyMass_le_slack_mul_prod_multinomial`; the difference of the two
`rowEntropyMass` values is by definition
`CompatibleSplit.SplitRequirements.compatibilityLogLoss`, so no entropy manipulation is needed to
combine them.

## The slack

Only the *lower* direction costs anything, and it costs one Stirling loss per Z-index:

`dwz63CompatSlack L Z n = e ^ (|L| · |Z|) · (n + 1) ^ (|L| · |Z|)`,

which is `typeClassEntropyLoss L n ^ |Z|`.  It is polynomial, hence subexponential
(`dwz63CompatSlack_subexponential`), which is all
`Examples/DuanWuZhouLevelTwoCompetitorRateBrick.lean`'s
`dwz63_eventually_subexponential_mul_pow_le_one` asks of it.

## Position in the library

Layer 4 (a client): every step instantiates a committed theorem of `Combinatorics/` or
`Analysis/`.  Nothing here is specific to section 6.3; the section 6.3 numbers enter one module
up, in `Examples/DuanWuZhouLevelTwoCompatibilityRateIdentity.lean`, which supplies the single
hypothesis `compatibilityLogLoss ≤ n · dwz63LogCompat` as an exact identity.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity AlgebraicComplexity.WordType AlgebraicComplexity.CompatibleSplit
open scoped BigOperators

universe u v w

/-! ## The polynomial slack -/

/-- **The slack of the brick**: one committed Stirling loss `typeClassEntropyLoss L n` per
Z-index.  It is the only loss the argument pays, and it is paid entirely by the *lower* bound on
the typical-block count. -/
noncomputable def dwz63CompatSlack (L : Type v) [Fintype L] (Z : Type w) [Fintype Z] :
    ℕ → ℝ :=
  fun n ↦ Real.exp 1 ^ (Fintype.card L * Fintype.card Z) *
    (((n + 1 : ℕ) : ℝ)) ^ (Fintype.card L * Fintype.card Z)

theorem dwz63CompatSlack_pos (L : Type v) [Fintype L] (Z : Type w) [Fintype Z] (n : ℕ) :
    0 < dwz63CompatSlack L Z n := by
  unfold dwz63CompatSlack
  positivity

/-- The slack is polynomial, hence subexponential: exactly what the brick's asymptotic step
`dwz63_eventually_subexponential_mul_pow_le_one` consumes. -/
theorem dwz63CompatSlack_subexponential (L : Type v) [Fintype L] (Z : Type w) [Fintype Z] :
    Growth.Subexponential (dwz63CompatSlack L Z) :=
  (Growth.Subexponential.natCast_succ_pow (Fintype.card L * Fintype.card Z)).const_mul
    (by positivity)

/-- The slack is the committed per-row Stirling loss raised to the number of rows. -/
theorem dwz63CompatSlack_eq_typeClassEntropyLoss_pow (L : Type v) [Fintype L]
    (Z : Type w) [Fintype Z] (n : ℕ) :
    dwz63CompatSlack L Z n = typeClassEntropyLoss L n ^ Fintype.card Z := by
  unfold dwz63CompatSlack typeClassEntropyLoss
  rw [mul_pow, ← pow_mul, ← pow_mul]

/-! ## The two zero-tolerant row estimates -/

/-- **Upper, loss-free, zero-tolerant.**  A row's multinomial coefficient never exceeds its own
entropy exponent, including when the row is structurally zero — the case that occurs at every
interior component of a compatibility profile. -/
theorem dwz63_multinomial_le_exp_profileMassEntropy {I : Type u} [Fintype I] (a : I → ℕ) :
    ((Nat.multinomial Finset.univ a : ℕ) : ℝ) ≤
      Real.exp (((profileMass a : ℕ) : ℝ) * profileEntropyNats a) := by
  rcases Nat.eq_zero_or_pos (profileMass a) with hzero | hpos
  · have hz : a = fun _ ↦ 0 := by
      funext i
      exact Finset.sum_eq_zero_iff.mp (show ∑ j, a j = 0 from hzero) i (Finset.mem_univ i)
    have hm : Nat.multinomial Finset.univ a = 1 := by
      rw [hz]
      simp [Nat.multinomial]
    rw [hm, hzero]
    simp
  · exact multinomial_le_exp_profileEntropy a hpos

/-- The Stirling loss is monotone in the word length. -/
theorem dwz63_typeClassEntropyLoss_mono (I : Type u) [Fintype I] {m n : ℕ} (h : m ≤ n) :
    typeClassEntropyLoss I m ≤ typeClassEntropyLoss I n := by
  unfold typeClassEntropyLoss
  refine mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) ?_ _) (by positivity)
  exact_mod_cast Nat.succ_le_succ h

/-- One is below the Stirling loss. -/
theorem dwz63_one_le_typeClassEntropyLoss (I : Type u) [Fintype I] (n : ℕ) :
    (1 : ℝ) ≤ typeClassEntropyLoss I n := by
  unfold typeClassEntropyLoss
  have h1 : (1 : ℝ) ≤ Real.exp 1 ^ Fintype.card I :=
    one_le_pow₀ (Real.one_le_exp (by norm_num))
  have h2 : (1 : ℝ) ≤ (((n + 1 : ℕ) : ℝ)) ^ Fintype.card I := by
    refine one_le_pow₀ ?_
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (by omega)
  nlinarith

/-- **Lower, with the committed Stirling loss, zero-tolerant.**  A row's entropy exponent is
below its multinomial coefficient up to `typeClassEntropyLoss`, including at mass zero. -/
theorem dwz63_exp_profileMassEntropy_le_loss_mul_multinomial {I : Type u} [Fintype I]
    (a : I → ℕ) :
    Real.exp (((profileMass a : ℕ) : ℝ) * profileEntropyNats a) ≤
      typeClassEntropyLoss I (profileMass a) *
        ((Nat.multinomial Finset.univ a : ℕ) : ℝ) := by
  rcases Nat.eq_zero_or_pos (profileMass a) with hzero | hpos
  · have hz : a = fun _ ↦ 0 := by
      funext i
      exact Finset.sum_eq_zero_iff.mp (show ∑ j, a j = 0 from hzero) i (Finset.mem_univ i)
    have hm : Nat.multinomial Finset.univ a = 1 := by
      rw [hz]
      simp [Nat.multinomial]
    rw [hm, hzero]
    simpa using dwz63_one_le_typeClassEntropyLoss I 0
  · have ha : a ∈ types I (profileMass a) := mem_types.mpr rfl
    have hbound := exp_profileEntropy_le_typeClassEntropyLoss_mul_card_typeClass a ha hpos
    rwa [card_typeClass_eq_multinomial_light a ha] at hbound

/-! ## The two product estimates -/

/-- The product of the row multinomials of a joint profile is below the exponential of its
conditional-entropy mass.  This is the loss-free direction, applied to the requirement cells. -/
theorem dwz63_prod_multinomial_le_exp_rowEntropyMass {A : Type u} [Fintype A]
    {B : Type v} [Fintype B] (θ : A × B → ℕ) :
    (∏ a : A, ((Nat.multinomial Finset.univ (fun b ↦ θ (a, b)) : ℕ) : ℝ)) ≤
      Real.exp (rowEntropyMass θ) := by
  rw [rowEntropyMass, Real.exp_sum]
  exact Finset.prod_le_prod (fun a _ ↦ by positivity)
    (fun a _ ↦ dwz63_multinomial_le_exp_profileMassEntropy fun b ↦ θ (a, b))

/-- The exponential of a joint profile's conditional-entropy mass is below the product of its row
multinomials, up to `dwz63CompatSlack`.  This is the direction that pays the slack, applied to the
Z-indices. -/
theorem dwz63_exp_rowEntropyMass_le_slack_mul_prod_multinomial {A : Type u} [Fintype A]
    {B : Type v} [Fintype B] (θ : A × B → ℕ) {n : ℕ}
    (hrow : ∀ a : A, profileMass (fun b ↦ θ (a, b)) ≤ n) :
    Real.exp (rowEntropyMass θ) ≤
      dwz63CompatSlack B A n *
        ∏ a : A, ((Nat.multinomial Finset.univ (fun b ↦ θ (a, b)) : ℕ) : ℝ) := by
  rw [rowEntropyMass, Real.exp_sum]
  have hstep : ∀ a ∈ (Finset.univ : Finset A),
      Real.exp (((profileMass (fun b ↦ θ (a, b)) : ℕ) : ℝ) *
          profileEntropyNats (fun b ↦ θ (a, b))) ≤
        typeClassEntropyLoss B n *
          ((Nat.multinomial Finset.univ (fun b ↦ θ (a, b)) : ℕ) : ℝ) := by
    intro a _
    refine (dwz63_exp_profileMassEntropy_le_loss_mul_multinomial fun b ↦ θ (a, b)).trans ?_
    exact mul_le_mul_of_nonneg_right (dwz63_typeClassEntropyLoss_mono B (hrow a))
      (by positivity)
  calc ∏ a : A, Real.exp (((profileMass (fun b ↦ θ (a, b)) : ℕ) : ℝ) *
        profileEntropyNats (fun b ↦ θ (a, b)))
      ≤ ∏ a : A, (typeClassEntropyLoss B n *
          ((Nat.multinomial Finset.univ (fun b ↦ θ (a, b)) : ℕ) : ℝ)) :=
        Finset.prod_le_prod (fun a _ ↦ (Real.exp_pos _).le) hstep
    _ = typeClassEntropyLoss B n ^ Fintype.card A *
          ∏ a : A, ((Nat.multinomial Finset.univ (fun b ↦ θ (a, b)) : ℕ) : ℝ) := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]
    _ = dwz63CompatSlack B A n *
          ∏ a : A, ((Nat.multinomial Finset.univ (fun b ↦ θ (a, b)) : ℕ) : ℝ) := by
        rw [dwz63CompatSlack_eq_typeClassEntropyLoss_pow]

/-! ## The brick, from the conditional-entropy mass -/

variable {C : Type u} [Fintype C] {L : Type v} [Fintype L] {Z : Type w} [Fintype Z]

/-- **The brick of `Examples/DuanWuZhouLevelTwoCompetitorRateBrick.lean`, generically.**

For any splitting record whose conditional-entropy mass
`compatibilityLogLoss = H-mass(compatibility profile) − H-mass(typicalness profile)` is at most
`n · rateLog`, the compatible-block count is at most `dwz63CompatSlack · e^{rateLog · n}` times the
typical-block count.  Only the *upper* half of `p_comp = ᾱ_p^{n+o(n)}` is produced, which is all
`dwz63_cofinal_competitorBound_le_degree` consumes.

The word length `n` is not a free parameter: membership of `comp₀` in `matchable αType K` forces
`n = profileMass usefulType`, so the hypothesis is stated at that mass and needs no quantifier. -/
theorem dwz63_compatibleFractionUpper_of_compatibilityLogLoss_le
    (S : SplitRequirements C L Z) {αType : C → ℕ} (href : S.RefinesType αType) {rateLog : ℝ}
    (hloss : S.compatibilityLogLoss ≤ ((profileMass S.usefulType : ℕ) : ℝ) * rateLog) :
    Dwz63CompatibleFractionUpper S αType (Real.exp rateLog) (dwz63CompatSlack L Z) := by
  classical
  intro n K comp₀ hmem
  rw [S.mem_matchable] at hmem
  obtain ⟨hmult, hK⟩ := hmem
  have hlen : ∑ c, αType c = n := by
    rw [← hmult]
    exact sum_multiplicity comp₀
  have hmass : profileMass S.usefulType = n := by
    show ∑ p, S.usefulType p = n
    rw [SplitRequirements.sum_usefulType href, hlen]
  -- the two exact product closed forms
  have hcompat : (S.compatibleSet comp₀).card =
      ∏ r : C ⊕ Z, Nat.multinomial Finset.univ fun l ↦ S.compatibleType (r, l) :=
    SplitRequirements.card_compatibleSet_eq_prod href comp₀ hmult
  have htyp : (S.typicalSet K).card =
      ∏ z : Z, Nat.multinomial Finset.univ fun l ↦ S.typicalType (z, l) := by
    rw [← hK]
    exact SplitRequirements.card_typicalSet_eq_prod href comp₀ hmult
  -- every Z-row of the typicalness profile has mass at most `n`
  have htypTypes : S.typicalType ∈ types (Z × L) n := by
    rw [mem_types, SplitRequirements.typicalType, sum_mappedType,
      SplitRequirements.sum_usefulType href, hlen]
  have htypmass : profileMass S.typicalType = n := profileMass_eq_of_mem_types htypTypes
  have hrowsum : ∑ z : Z, profileMass (fun l ↦ S.typicalType (z, l)) = n := by
    rw [← htypmass]
    show ∑ z : Z, ∑ l : L, S.typicalType (z, l) = ∑ p : Z × L, S.typicalType p
    rw [Fintype.sum_prod_type]
  have hrow : ∀ z : Z, profileMass (fun l ↦ S.typicalType (z, l)) ≤ n := by
    intro z
    rw [← hrowsum]
    exact Finset.single_le_sum (f := fun z' ↦ profileMass fun l ↦ S.typicalType (z', l))
      (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ z)
  -- the two product estimates
  have hupper : (((S.compatibleSet comp₀).card : ℕ) : ℝ) ≤
      Real.exp (rowEntropyMass S.compatibleType) := by
    rw [hcompat]
    push_cast
    exact dwz63_prod_multinomial_le_exp_rowEntropyMass S.compatibleType
  have hlower : Real.exp (rowEntropyMass S.typicalType) ≤
      dwz63CompatSlack L Z n * (((S.typicalSet K).card : ℕ) : ℝ) := by
    rw [htyp]
    push_cast
    exact dwz63_exp_rowEntropyMass_le_slack_mul_prod_multinomial S.typicalType hrow
  -- the rate step
  have hsplit : Real.exp (rowEntropyMass S.compatibleType) =
      Real.exp S.compatibilityLogLoss * Real.exp (rowEntropyMass S.typicalType) := by
    rw [← Real.exp_add]
    congr 1
    rw [SplitRequirements.compatibilityLogLoss]
    ring
  have hrate : Real.exp S.compatibilityLogLoss ≤ Real.exp rateLog ^ n := by
    have hpow : Real.exp rateLog ^ n = Real.exp ((n : ℝ) * rateLog) := by
      rw [← Real.exp_nat_mul]
    rw [hpow]
    refine Real.exp_le_exp.mpr ?_
    rw [← hmass]
    exact hloss
  calc (((S.compatibleSet comp₀).card : ℕ) : ℝ)
      ≤ Real.exp (rowEntropyMass S.compatibleType) := hupper
    _ = Real.exp S.compatibilityLogLoss * Real.exp (rowEntropyMass S.typicalType) := hsplit
    _ ≤ Real.exp rateLog ^ n * (dwz63CompatSlack L Z n * (((S.typicalSet K).card : ℕ) : ℝ)) :=
        mul_le_mul hrate hlower (Real.exp_pos _).le (pow_nonneg (Real.exp_pos _).le n)
    _ = dwz63CompatSlack L Z n * Real.exp rateLog ^ n * (((S.typicalSet K).card : ℕ) : ℝ) := by
        ring

/-- The same, phrased through the normalized rate `compatibilityRateLog = log ᾱ_p`. -/
theorem dwz63_compatibleFractionUpper_of_compatibilityRateLog_le
    (S : SplitRequirements C L Z) {αType : C → ℕ} (href : S.RefinesType αType) {rateLog : ℝ}
    (hpos : 0 < profileMass S.usefulType) (hrate : S.compatibilityRateLog ≤ rateLog) :
    Dwz63CompatibleFractionUpper S αType (Real.exp rateLog) (dwz63CompatSlack L Z) := by
  refine dwz63_compatibleFractionUpper_of_compatibilityLogLoss_le S href ?_
  have hmassR : (0 : ℝ) < ((profileMass S.usefulType : ℕ) : ℝ) := by exact_mod_cast hpos
  rw [SplitRequirements.compatibilityRateLog, div_le_iff₀ hmassR] at hrate
  linarith

end AlgebraicComplexity.Examples
