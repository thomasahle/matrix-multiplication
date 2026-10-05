/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoCountComparisonInputs
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoEntropyXUpper
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoCountComparison
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoCompatibilityRateIdentity
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoSupportBridge
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoPlainSharpDegree

set_option autoImplicit false
set_option maxRecDepth 8000

/-!
# `hVdeg`, cofinally, at the section 6.3 instance

Layer 4 (`AlgebraicComplexity/Examples/`).  `Examples/DuanWuZhouLevelTwoJointHashBranch.lean`
carries `hVdeg : Vb ≤ dwz63PlainSharpDegree K n t` as a hypothesis, "a *rate* fact whose finite
form belongs to the count lane".  This module discharges it cofinally at the section 6.3 instance,
by assembling the four inputs of
`Examples/DuanWuZhouLevelTwoCompetitorRateBrick.lean`'s `dwz63_cofinal_competitorBound_le_degree`.

## The common index

The two rate inputs live on different lattices.  The compatibility brick
`dwz63_compatibleFractionUpper_dwz63Split k` has content at the split profile's own mass
`2 · 10 ^ 16 · k`; the count-side inputs `dwz63_hupper` / `dwz63_hlower` live at multiples of the
fifteen-cell mass `10 ^ 8`.  The common refinement is the brick's own lattice, reached by taking
`Examples/DuanWuZhouLevelTwoCountComparisonInputs.lean`'s free group size to be

`blocks := 2 · 10 ^ 8`,   so   `dwz63PlainCountDepth blocks m + 1 = 2 · 10 ^ 16 · (m + 1) `,

and `k := m + 1`.  Off that lattice nothing has to be said: `matchable` is empty there, so the
brick is vacuous and the client's `compatCard` is zero.

## The `Fin 15` and square-support readings of the same distribution

`hupper` bounds `S.matchable αType K`, which is by definition
`WordType.typedWordMapFiber S.zIndex αType K`; at `S = dwz63Split k` that is the fifteen-letter
alphabet `Fin 15` with `dwz63ZIndex` and `dwz63Alpha`.  `hlower` and the sharp degree live on the
square support with `dwz63PlainLegRead` and `dwz63PlainAlpha`.  The two are the *same*
distribution read through `Examples/DuanWuZhouLevelTwoSupportBridge.lean`'s `dwz63CellEquiv`
(`dwz63_plainAlpha_eq_mappedType_cellEquiv`), and since entropy is a relabelling invariant
(`dwz63_profileEntropyNats_mappedType_equiv`) the shared rate `ᾱ_α` of `dwz63_hcount_of_rate` is
one and the same number on both sides.  That is the only place the bridge is needed; nothing else
crosses.

## The ratio

`r = ᾱ_p ᾱ_X / (ᾱ_Z · hashK)` at `hashK = 1`, raised to the group size.  It is below one
exactly
by `Examples/DuanWuZhouLevelTwoEntropyXUpper.lean`'s
`dwz63_logCompat_add_entropyX_lt_entropyZ`, whose surviving margin is `1.1192 · 10⁻⁷` per
symbol.
The hash-loss multiplier `K = 1 + 10⁻¹⁰` is not used.

Primary source: Ran Duan, Hongxun Wu and Renfei Zhou, *Faster Matrix Multiplication via Asymmetric
Hashing*, arXiv:2210.10173, §6.2 (`global_value.tex`), §6.3.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor ProgressionHash CompatibleSplit

open scoped BigOperators

universe u

/-! ## Entropy is a relabelling invariant -/

/-- Pushing a profile forward along a bijection does not move its entropy. -/
theorem dwz63_profileEntropyNats_mappedType_equiv {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq B] (e : A ≃ B) (a : A → ℕ) :
    WordType.profileEntropyNats (WordType.mappedType (e : A → B) a) =
      WordType.profileEntropyNats a := by
  classical
  have hmass : WordType.profileMass (fun b ↦ a (e.symm b)) = WordType.profileMass a := by
    have h := WordType.profileMass_mappedType (e : A → B) a
    rwa [mappedType_equiv] at h
  simp only [WordType.profileEntropyNats, mappedType_equiv, hmass]
  exact Fintype.sum_equiv e.symm _ _ (fun _ ↦ rfl)

/-! ## The two readings of `dwz63Alpha` -/

/-- The two spellings of a section 6.3 cell as a coarse square address agree. -/
theorem dwz63_cellAddress_eq_cell : dwz63CellAddress = dwz63Cell := by
  funext i leg
  cases leg <;> rfl

/-- **The plain fifteen-letter profile is `dwz63Alpha` relabelled along the bridge.** -/
theorem dwz63_plainAlpha_eq_mappedType_cellEquiv :
    dwz63PlainAlpha =
      WordType.mappedType (dwz63CellEquiv : Fin 15 → CWSquareSupport) dwz63Alpha := by
  classical
  funext s
  rw [mappedType_equiv]
  show dwz63AlphaAddress (s : CWSquareAddress) = dwz63Alpha (dwz63CellEquiv.symm s)
  have hhit : dwz63Cell (dwz63CellEquiv.symm s) = (s : CWSquareAddress) := by
    rw [← dwz63CellEquiv_coe, Equiv.apply_symm_apply]
  unfold dwz63AlphaAddress
  rw [WordType.mappedType_eq_sum_ite, dwz63_cellAddress_eq_cell]
  refine (Finset.sum_eq_single (dwz63CellEquiv.symm s) ?_ ?_).trans ?_
  · intro b _ hb
    refine if_neg ?_
    intro hcell
    exact hb (dwz63Cell_injective (hcell.trans hhit.symm))
  · intro hmem
    exact absurd (Finset.mem_univ (dwz63CellEquiv.symm s)) hmem
  · exact if_pos hhit

/-- **The shared rate `ᾱ_α`, read on the fifteen-letter alphabet.** -/
theorem dwz63_plainRateAlpha_eq_exp_entropyNats_dwz63Alpha :
    dwz63PlainRateAlpha = Real.exp (WordType.profileEntropyNats dwz63Alpha) := by
  rw [dwz63PlainRateAlpha, dwz63_plainAlpha_eq_mappedType_cellEquiv,
    dwz63_profileEntropyNats_mappedType_equiv]

/-! ## `hupper` on the fifteen-letter alphabet -/

/-- The generic form of `dwz63_card_typedWordMapFiber_Z_le`: an upper bound on one typed word-map
fibre at the pushed entropy base, with the structural-zero loss of the pushed profile as the only
slack. -/
theorem dwz63_card_typedWordMapFiber_le_pushedBase {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (f : A → B) (profile : A → ℕ) (hmass : 0 < WordType.profileMass profile)
    {t N : ℕ} (ht : 0 < t) (hlen : WordType.profileMass profile * t = N)
    (target : Fin N → B)
    (htarget : WordType.multiplicity target =
      WordType.proportionalCounts (WordType.mappedType f profile) t) :
    ((WordType.typedWordMapFiber f (WordType.proportionalCounts profile t) target).card : ℝ) ≤
      WordType.structuralZeroMultinomialLoss (WordType.mappedType f profile) t *
        WordType.pushedTypeFiberEntropyBase f profile ^ t := by
  subst hlen
  have hmem : target ∈ WordType.typeClass (WordType.profileMass profile * t)
      (WordType.proportionalCounts (WordType.mappedType f profile) t) :=
    WordType.mem_typeClass.mpr htarget
  have hfactor := WordType.card_pushedTypeClass_mul_card_typedFiber f profile t target hmem
  have hcond := WordType.proportionalEntropyBase_pow_le_structuralZeroLoss_mul_card_typeClass
    (WordType.mappedType f profile) t
  rw [WordType.profileMass_mappedType] at hcond
  have hambient := WordType.card_proportionalTypeClass_le_entropyBase_pow profile hmass t ht
  have hres := WordType.fiberCard_le_mul_div_pow_of_conditional_mul_fiber_le
    (WordType.proportionalEntropyBase (WordType.mappedType f profile))
    (WordType.proportionalEntropyBase profile)
    (WordType.structuralZeroMultinomialLoss (WordType.mappedType f profile) t)
    1 t
    (WordType.typeClass (WordType.profileMass profile * t)
      (WordType.proportionalCounts (WordType.mappedType f profile) t)).card
    (WordType.typedWordMapFiber f (WordType.proportionalCounts profile t) target).card
    (WordType.typeClass (WordType.profileMass profile * t)
      (WordType.proportionalCounts profile t)).card
    (WordType.proportionalEntropyBase_pos_zeroSafe _)
    (WordType.structuralZeroMultinomialLoss_pos _ t).le
    hcond (le_of_eq hfactor) (by rw [one_mul]; exact hambient)
  rw [mul_one] at hres
  exact hres

/-- The `Z`-leg pushed base of the fifteen-letter profile, at the forced word length. -/
theorem dwz63_pushedTypeFiberEntropyBase_zIndex_pow {t N : ℕ}
    (hlen : WordType.profileMass dwz63Alpha * t = N) :
    WordType.pushedTypeFiberEntropyBase dwz63ZIndex dwz63Alpha ^ t =
      (dwz63PlainRateAlpha / Real.exp dwz63EntropyZ) ^ N := by
  have hmass : 0 < WordType.profileMass dwz63Alpha := profileMass_dwz63Alpha_pos
  have hkey : Real.exp ((WordType.profileMass dwz63Alpha : ℝ) *
        (WordType.profileEntropyNats dwz63Alpha - dwz63EntropyZ)) ^ t =
      (dwz63PlainRateAlpha / Real.exp dwz63EntropyZ) ^ N := by
    calc Real.exp ((WordType.profileMass dwz63Alpha : ℝ) *
            (WordType.profileEntropyNats dwz63Alpha - dwz63EntropyZ)) ^ t
        = Real.exp ((t : ℝ) * ((WordType.profileMass dwz63Alpha : ℝ) *
            (WordType.profileEntropyNats dwz63Alpha - dwz63EntropyZ))) :=
          (dwz63_exp_natCast_mul t _).symm
      _ = Real.exp ((N : ℝ) *
            (WordType.profileEntropyNats dwz63Alpha - dwz63EntropyZ)) := by
          congr 1
          rw [← hlen]
          push_cast
          ring
      _ = Real.exp (WordType.profileEntropyNats dwz63Alpha - dwz63EntropyZ) ^ N :=
          dwz63_exp_natCast_mul N _
      _ = (dwz63PlainRateAlpha / Real.exp dwz63EntropyZ) ^ N := by
          rw [Real.exp_sub, dwz63_plainRateAlpha_eq_exp_entropyNats_dwz63Alpha]
  rw [WordType.pushedTypeFiberEntropyBase_eq_exp_entropyDifference _ _ hmass,
    mappedType_dwz63ZIndex_dwz63Alpha, profileEntropyNats_dwz63AlphaZ]
  exact hkey

/-! ## The assembled cofinal statement -/

-- ELABORATION RISK: `dwz63AssemblyBlocks` is deliberately **irreducible**.  `PositiveWord` is
-- defined by recursion on its length, so if the group size were a visible literal then any defeq
-- check touching `PositiveWord (Fin 5) (dwz63PlainCountDepth dwz63AssemblyBlocks m)` would try to
-- evaluate
-- `10 ^ 8 · (2 · 10 ^ 8 · (m + 1)) - 1` in unary and exhaust the recursion depth.  Keeping the
-- group size opaque leaves the length stuck; `dwz63AssemblyBlocks_eq` releases the literal in the
-- one place a literal is wanted, the `αType` argument of the compatibility brick, which sits in no
-- dependent position.
/-- The group size that lines the count lattice up with the compatibility brick's. -/
def dwz63AssemblyBlocks : ℕ := 200000000

theorem dwz63AssemblyBlocks_eq : dwz63AssemblyBlocks = 200000000 := rfl

theorem dwz63_assemblyBlocks_pos : 0 < dwz63AssemblyBlocks := by
  rw [dwz63AssemblyBlocks_eq]; norm_num

attribute [irreducible] dwz63AssemblyBlocks

theorem dwz63_assemblyDepth_succ (m : ℕ) :
    dwz63PlainCountDepth dwz63AssemblyBlocks m + 1 = 20000000000000000 * (m + 1) := by
  rw [dwz63PlainCountDepth_succ dwz63_assemblyBlocks_pos, dwz63AssemblyBlocks_eq]
  ring

/-- The per-group compatibility rate. -/
noncomputable def dwz63AssemblyRateCompat : ℝ :=
  Real.exp dwz63LogCompat ^ (100000000 * dwz63AssemblyBlocks)

theorem dwz63AssemblyRateCompat_pos : 0 < dwz63AssemblyRateCompat :=
  pow_pos (Real.exp_pos _) _

theorem dwz63AssemblyRateCompat_le_one : dwz63AssemblyRateCompat ≤ 1 := by
  refine pow_le_one₀ (Real.exp_pos _).le ?_
  refine Real.exp_le_one_iff.mpr ?_
  have := dwz63_logCompat_le_bound
  linarith

/-- **The ratio is below one**, from the strict entropy inequality and nothing else. -/
theorem dwz63_assemblyRatio_lt_one :
    dwz63AssemblyRateCompat * dwz63PlainBlockRateX dwz63AssemblyBlocks /
      (dwz63PlainBlockRateZ dwz63AssemblyBlocks * 1) < 1 := by
  have hbase : Real.exp dwz63LogCompat * Real.exp dwz63EntropyX / Real.exp dwz63EntropyZ < 1 := by
    rw [div_lt_one (Real.exp_pos _), ← Real.exp_add]
    exact Real.exp_lt_exp.mpr dwz63_logCompat_add_entropyX_lt_entropyZ
  have hpos : 0 < Real.exp dwz63LogCompat * Real.exp dwz63EntropyX / Real.exp dwz63EntropyZ := by
    positivity
  have hpow := pow_lt_one₀ hpos.le hbase
    (show 100000000 * dwz63AssemblyBlocks ≠ 0 by rw [dwz63AssemblyBlocks_eq]; norm_num)
  calc dwz63AssemblyRateCompat * dwz63PlainBlockRateX dwz63AssemblyBlocks /
        (dwz63PlainBlockRateZ dwz63AssemblyBlocks * 1)
      = (Real.exp dwz63LogCompat * Real.exp dwz63EntropyX /
          Real.exp dwz63EntropyZ) ^ (100000000 * dwz63AssemblyBlocks) := by
        unfold dwz63AssemblyRateCompat dwz63PlainBlockRateX dwz63PlainBlockRateZ
        rw [mul_one, div_pow, mul_pow]
    _ < 1 := hpow

theorem dwz63_assemblyRatio_nonneg :
    0 ≤ dwz63AssemblyRateCompat * dwz63PlainBlockRateX dwz63AssemblyBlocks /
      (dwz63PlainBlockRateZ dwz63AssemblyBlocks * 1) := by
  refine div_nonneg (mul_nonneg dwz63AssemblyRateCompat_pos.le
    (dwz63PlainBlockRateX_pos dwz63AssemblyBlocks).le) ?_
  rw [mul_one]
  exact (dwz63PlainBlockRateZ_pos dwz63AssemblyBlocks).le

/-- **The compatibility slack, re-indexed to groups.** -/
noncomputable def dwz63AssemblySlack (m : ℕ) : ℝ :=
  dwz63CompatSlack (Fin 3) (Fin 5) (20000000000000000 * (m + 1))

theorem dwz63_subexponential_assemblySlack :
    Growth.Subexponential dwz63AssemblySlack :=
  dwz63_subexponential_comp_mul (dwz63CompatSlack_subexponential (Fin 3) (Fin 5)) (by norm_num)

/-- One group peeled off a per-position power. -/
theorem dwz63_group_pow_split (b : ℝ) (blocks m : ℕ) :
    b ^ (100000000 * (blocks * (m + 1))) =
      (b ^ (100000000 * blocks)) ^ m * b ^ (100000000 * blocks) := by
  rw [show 100000000 * (blocks * (m + 1)) = 100000000 * blocks * m + 100000000 * blocks from by
      ring, pow_add, pow_mul]

/-! ## `hupper` at the section 6.3 split -/

/-- **`hupper` for `dwz63Split`'s `matchable`**, in `dwz63_hcount_of_rate`'s binder shape. -/
theorem dwz63_assembly_hupper
    (comp₀ : ∀ m : ℕ, Fin (dwz63PlainCountDepth dwz63AssemblyBlocks m + 1) → Fin 15)
    (hcomp₀ : ∀ m : ℕ, WordType.multiplicity (comp₀ m) =
      WordType.proportionalCounts dwz63Alpha (dwz63AssemblyBlocks * (m + 1))) :
    ∀ N : ℕ,
      (((dwz63Split (N + 1)).matchable
          (WordType.proportionalCounts dwz63Alpha (dwz63AssemblyBlocks * (N + 1)))
          (dwz63ZIndex ∘ comp₀ N)).card : ℝ) ≤
        dwz63PlainCountSu dwz63AssemblyBlocks N *
          (dwz63PlainBlockRateAlpha dwz63AssemblyBlocks /
            dwz63PlainBlockRateZ dwz63AssemblyBlocks) ^ N := by
  intro m
  have hlen : WordType.profileMass dwz63Alpha * (dwz63AssemblyBlocks * (m + 1)) =
      dwz63PlainCountDepth dwz63AssemblyBlocks m + 1 := by
    rw [profileMass_dwz63Alpha, dwz63PlainCountDepth_succ dwz63_assemblyBlocks_pos]
  have hZtype : WordType.multiplicity (dwz63ZIndex ∘ comp₀ m) =
      WordType.proportionalCounts (WordType.mappedType dwz63ZIndex dwz63Alpha)
        (dwz63AssemblyBlocks * (m + 1)) := by
    rw [WordType.multiplicity_comp_eq_mappedType, hcomp₀ m,
      WordType.mappedType_proportionalCounts]
  have hcore := dwz63_card_typedWordMapFiber_le_pushedBase dwz63ZIndex dwz63Alpha
    profileMass_dwz63Alpha_pos
    (t := dwz63AssemblyBlocks * (m + 1))
    (Nat.mul_pos dwz63_assemblyBlocks_pos (Nat.succ_pos m)) hlen
    (dwz63ZIndex ∘ comp₀ m) hZtype
  rw [mappedType_dwz63ZIndex_dwz63Alpha,
    dwz63_pushedTypeFiberEntropyBase_zIndex_pow hlen] at hcore
  refine hcore.trans_eq ?_
  simp only [dwz63PlainCountSu, dwz63_plainBlockRatio_Z,
    dwz63PlainCountDepth_succ dwz63_assemblyBlocks_pos]
  rw [dwz63_group_pow_split]
  ring

/-! ## `hbrick`, re-indexed to groups -/

/-- **`hbrick` for `dwz63Split`**, in `dwz63_cofinal_competitorBound_le_degree`'s binder shape. -/
theorem dwz63_assembly_hbrick
    (comp₀ : ∀ m : ℕ, Fin (dwz63PlainCountDepth dwz63AssemblyBlocks m + 1) → Fin 15)
    (hcomp₀ : ∀ m : ℕ, WordType.multiplicity (comp₀ m) =
      WordType.proportionalCounts dwz63Alpha (dwz63AssemblyBlocks * (m + 1))) :
    ∀ N : ℕ,
      (((dwz63Split (N + 1)).compatibleSet (comp₀ N)).card : ℝ) ≤
        dwz63AssemblySlack N * dwz63AssemblyRateCompat ^ N *
          (((dwz63Split (N + 1)).typicalSet (dwz63ZIndex ∘ comp₀ N)).card : ℝ) := by
  intro m
  have hmem : comp₀ m ∈ (dwz63Split (m + 1)).matchable
      (WordType.proportionalCounts dwz63Alpha (200000000 * (m + 1)))
      (dwz63ZIndex ∘ comp₀ m) := by
    rw [SplitRequirements.mem_matchable]
    refine ⟨?_, rfl⟩
    rw [hcomp₀ m, dwz63AssemblyBlocks_eq]
  have hb := dwz63_compatibleFractionUpper_dwz63Split (m + 1)
    (dwz63PlainCountDepth dwz63AssemblyBlocks m + 1) (dwz63ZIndex ∘ comp₀ m) (comp₀ m) hmem
  have hsplit : (Real.exp dwz63LogCompat) ^ (dwz63PlainCountDepth dwz63AssemblyBlocks m + 1) =
      dwz63AssemblyRateCompat ^ m * dwz63AssemblyRateCompat := by
    rw [dwz63PlainCountDepth_succ dwz63_assemblyBlocks_pos]
    exact dwz63_group_pow_split _ _ _
  have hslackEq : dwz63CompatSlack (Fin 3) (Fin 5)
      (dwz63PlainCountDepth dwz63AssemblyBlocks m + 1) = dwz63AssemblySlack m := by
    rw [dwz63AssemblySlack, dwz63_assemblyDepth_succ]
  rw [hslackEq, hsplit] at hb
  refine hb.trans ?_
  refine mul_le_mul_of_nonneg_right ?_ (Nat.cast_nonneg _)
  have hs : 0 ≤ dwz63AssemblySlack m * dwz63AssemblyRateCompat ^ m := by
    exact mul_nonneg (dwz63_subexponential_assemblySlack.nonneg m)
      (pow_nonneg dwz63AssemblyRateCompat_pos.le m)
  calc dwz63AssemblySlack m * (dwz63AssemblyRateCompat ^ m * dwz63AssemblyRateCompat)
      = (dwz63AssemblySlack m * dwz63AssemblyRateCompat ^ m) * dwz63AssemblyRateCompat := by ring
    _ ≤ (dwz63AssemblySlack m * dwz63AssemblyRateCompat ^ m) * 1 :=
        mul_le_mul_of_nonneg_left dwz63AssemblyRateCompat_le_one hs
    _ = dwz63AssemblySlack m * dwz63AssemblyRateCompat ^ m := mul_one _

/-! ## The cofinal `hVdeg` -/

/-- **`hVdeg`, cofinally, at the section 6.3 instance.**

Past an explicit cutoff the competitor bound `V` of
`Examples/DuanWuZhouLevelTwoCompetitorBound.lean` is below the sharp degree
`dwz63PlainSharpDegree`, which is exactly the hypothesis
`Examples/DuanWuZhouLevelTwoJointHashBranch.lean`'s `dwz63_jointHashBranch` carries. -/
theorem dwz63_cofinal_plainCompetitorBound_le_sharpDegree (K : Type u) [CommRing K]
    (comp₀ : ∀ m : ℕ, Fin (dwz63PlainCountDepth dwz63AssemblyBlocks m + 1) → Fin 15)
    (hcomp₀ : ∀ m : ℕ, WordType.multiplicity (comp₀ m) =
      WordType.proportionalCounts dwz63Alpha (dwz63AssemblyBlocks * (m + 1)))
    (xword : ∀ m : ℕ, PositiveWord (Fin 5) (dwz63PlainCountDepth dwz63AssemblyBlocks m))
    (hxword : ∀ m : ℕ, xword m ∈ dwz63PlainLegTargets .X
      (dwz63PlainCountDepth dwz63AssemblyBlocks m) (dwz63AssemblyBlocks * (m + 1)))
    (hT : ∀ m : ℕ, 0 < ((dwz63Split (m + 1)).typicalSet (dwz63ZIndex ∘ comp₀ m)).card) :
    ∃ cutoff : ℕ, ∀ m : ℕ, cutoff ≤ m →
      dwz63CompetitorBound (dwz63Split (m + 1))
          (WordType.proportionalCounts dwz63Alpha (dwz63AssemblyBlocks * (m + 1)))
          (dwz63ZIndex ∘ comp₀ m) (comp₀ m) ≤
        dwz63PlainSharpDegree K (dwz63PlainCountDepth dwz63AssemblyBlocks m)
          (dwz63AssemblyBlocks * (m + 1)) := by
  have hdeg : ∀ m : ℕ,
      (PartitionHashEncoding.sourceWordLegFiber (dwz63PlainCountDepth dwz63AssemblyBlocks m)
        (dwz63PlainMarginalWords K (dwz63PlainCountDepth dwz63AssemblyBlocks m)
          (dwz63AssemblyBlocks * (m + 1))) .X (xword m)).card ≤
        dwz63PlainSharpDegree K (dwz63PlainCountDepth dwz63AssemblyBlocks m)
          (dwz63AssemblyBlocks * (m + 1)) := by
    intro m
    have h := card_sourceWordLegFiber_le_sharpDegree K .X
      (dwz63PlainCountDepth_succ dwz63_assemblyBlocks_pos m) (hxword m)
    exact h
  obtain ⟨cutoff, hcut⟩ := dwz63_cofinal_competitorBound_le_degree
    dwz63_subexponential_assemblySlack
    ((dwz63_subexponential_plainCountSu dwz63AssemblyBlocks dwz63_assemblyBlocks_pos).mul
      (dwz63_subexponential_plainCountSl dwz63AssemblyBlocks dwz63_assemblyBlocks_pos))
    dwz63_assemblyRatio_nonneg dwz63_assemblyRatio_lt_one
    (dwz63_assembly_hbrick comp₀ hcomp₀)
    (dwz63_hcount_of_rate
      (dwz63_plainCountSu_nonneg dwz63AssemblyBlocks dwz63_assemblyBlocks_pos)
      (dwz63_plainCountSl_nonneg dwz63AssemblyBlocks dwz63_assemblyBlocks_pos)
      dwz63AssemblyRateCompat_pos.le
      (dwz63PlainBlockRateX_pos dwz63AssemblyBlocks)
      (dwz63PlainBlockRateZ_pos dwz63AssemblyBlocks) one_pos hdeg
      (dwz63_assembly_hupper comp₀ hcomp₀)
      (dwz63_hlower K dwz63AssemblyBlocks dwz63_assemblyBlocks_pos xword hxword one_pos le_rfl))
  refine ⟨cutoff, fun m hm ↦ ?_⟩
  exact (dwz63_competitorBound_le_iff _ _ _ _ _ (hT m)).mpr (hcut m hm)

end AlgebraicComplexity.Examples
