/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoJointHashBranch
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoTypicalSetNonempty

set_option autoImplicit false

/-!
# The second modulus branch, at the plain field

Layer 4 (`AlgebraicComplexity/Examples/`).  `[duan2023faster]` sets

`M₀ = 8 · max(N_triple/N_X, N_α · p_comp / N_Z)`  (`global_value.tex:137`, in the
asymmetric-hashing paragraph `:130-140`)

and `claim:hole_frac_low` (`global_value.tex:247-265`) consumes the **second** branch: the
probability that a useful small block is a hole is `N_α p_comp/(N_Z M) ≤ 1/8`.  The plain chain's
only modulus condition is `8 · dwz63PlainSharpDegree ≤ |R|`
(`Examples/DuanWuZhouLevelTwoPlainIntegration.lean:62`), which is the **first** branch alone, so it
was read as leaving `Dwz63AggregateHoleFraction` without a proof route.

That reading is too pessimistic.  `dwz63JointHashDegree K n t Vb = max (dwz63PlainSharpDegree K n t)
(11 · Vb)` (`Examples/DuanWuZhouLevelTwoJointHashBranch.lean:206`) inflates the field only when
`11 · Vb` exceeds the plain degree, and *branch one binds*: `dwz63_branchOne_lt_branchTwo`
(`Examples/DuanWuZhouLevelTwoGlobalArithmetic.lean:855`) is a **strict** rational inequality
(`2.97181937368751 < 2.97181970400509`), the rate form of DWZ's `max` selecting its first argument.
The gap is geometric --- ratio `0.99999989 < 1`, per-symbol margin `1.1215 · 10⁻⁷` --- so
`dwz63_cofinal_competitorBound_le_degree`
(`Examples/DuanWuZhouLevelTwoCompetitorRateBrick.lean:141`), which absorbs *any* subexponential
slack, gives `11 · V ≤ d` past a (larger) cutoff exactly as it gives `V ≤ d`.

The arithmetic then closes at the plain field with the constant `11` exactly:

`256 · V ≤ 264 · V = 24 · (11 · V) ≤ 24 · d = 3 · (8 · d) ≤ 3 · |R|`,

using `dwz63SharpHashModulus_requirement`.  That is `hmodulus` of
`dwz63_exists_seed_aggregateHoleFraction` (`Examples/DuanWuZhouLevelTwoSeedSelection.lean:374`) and
of the hole lane's `dwz63_exists_seed_stage_marked`, at the **plain** degree.  No endpoint variant
needs to move to the joint field.

## The constants, against the paper

The Lean aggregate residual is `16 · Σ|holes| ≤ #retained · |avail|`
(`Examples/DuanWuZhouLevelTwoAggregateHoleBudget.lean:302`), an average hole fraction of `1/16`,
where `claim:hole_frac_low` states `1/8`.  These are not the same statement:

* the paper's `1/8` is **rule (i) only** --- the probability that `Z_K̂` is compatible with a
  *different* remaining triple (`global_value.tex:247-265`).  Rule (ii), the non-useful blocks, is
  disposed of by Additional Zeroing-Out Step 2 (`global_value.tex:74-90`), not as a hole allowance;
* the Lean budgets both rules into one aggregate: `dwz63_holeMass_averaging_arith`
  (`Examples/DuanWuZhouLevelTwoSeedSelection.lean:93`) yields `1/32` for the rule-(i) mass at the
  modulus condition `256 · V ≤ 3|R|`, and `huseless` allows `1/32` for rule (ii); `1/32 + 1/32 =
  1/16`.

So at the Lean's modulus the paper's argument gives `1/32` per rule --- four times better than the
published `1/8` --- and the `1/16` is the sum of two halves, not a weakened `1/8`.  The remark at
`Examples/DuanWuZhouLevelTwoAggregateHoleBudget.lean:33-36` ("`M₀ = 16 · max(...)` in place
of the paper's `8 · max(...)`") understates this and is corrected at the next integration
window.

Primary source: Ran Duan, Hongxun Wu and Renfei Zhou, *Faster Matrix Multiplication via Asymmetric
Hashing*, arXiv:2210.10173, §6.2 (`global_value.tex:124-331`), in particular the
asymmetric-hashing modulus `:130-140` (the definition of `M₀` at `:137`), `claim:hole_frac_low`
`:247-265`, and Additional Zeroing-Out Step 2 `:74-90`.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor

universe u

/-! ## The modulus condition at the plain field -/

/-- **`hmodulus` at the plain field.**

`256 · Vb ≤ 3 · |R|` from `11 · Vb ≤ d` alone:
`264 · Vb = 24 · (11 · Vb) ≤ 24 · d = 3 · (8 · d)`,
and `8 · d ≤ dwz63SharpHashModulus d` is the field's defining requirement.  This is the binder
`dwz63_exists_seed_aggregateHoleFraction` (`…SeedSelection.lean:374`) carries, at the degree every
endpoint variant already runs at. -/
theorem dwz63_plainHashModulus_seedSelection (K : Type u) [CommRing K] (n t Vb : ℕ)
    (h11 : 11 * Vb ≤ dwz63PlainSharpDegree K n t) :
    256 * Vb ≤ 3 * Fintype.card (dwz63SharpHashField (dwz63PlainSharpDegree K n t)) := by
  rw [card_dwz63SharpHashField]
  have hreq := dwz63SharpHashModulus_requirement (dwz63PlainSharpDegree K n t)
  omega

/-- **The joint degree collapses.**  Once branch one binds finitely, the inflated field of
`Examples/DuanWuZhouLevelTwoJointHashBranch.lean` *is* the plain field. -/
theorem dwz63JointHashDegree_eq_plainSharpDegree (K : Type u) [CommRing K] (n t Vb : ℕ)
    (h11 : 11 * Vb ≤ dwz63PlainSharpDegree K n t) :
    dwz63JointHashDegree K n t Vb = dwz63PlainSharpDegree K n t := by
  unfold dwz63JointHashDegree
  omega

/-! ## The cofinal `11 · V ≤ d` -/

/-- **Branch one binds with room for the constant `11`, cofinally.**

`dwz63_cofinal_competitorBound_le_plainSharpDegree` (`…TypicalSetNonempty.lean:72`) at
`degree := d / 11`.  The asymptotic step is unchanged --- `dwz63_cofinal_competitorBound_le_degree`
absorbs any subexponential slack against `ratio ^ N` with `ratio < 1` --- so multiplying the
right-hand slack by the constant `21` (which covers `d ≤ 21 · (d / 11)` for `d ≥ 11`) only
moves the cutoff.  This is the finite form of DWZ's `max` selecting its first branch
(`global_value.tex:137`) with the margin `dwz63_branchOne_lt_branchTwo` provides.

`hdeg11` is a growth fact about the sharp degree, not about the rate comparison: it says the
hashing degree is *eventually* at least `11`.  It is carried, not proved here, in the cofinal
shape that `dwz63_cofinal_eleven_le_plainSharpDegree`
(`…SharpDegreeElevenLower.lean:60`) supplies.

Because `dwz63_cofinal_competitorBound_le_degree` needs its counting hypothesis at *every* index,
the degree fed to it is `G`: `d / 11` where `hdeg11` has already bitten, and the trivial fibre
count below that cutoff.  The `else` branch makes the counting step vacuous there and costs
nothing, since the conclusion is itself cofinal --- the returned cutoff is the `max` of the two. -/
theorem dwz63_cofinal_eleven_mul_competitorBound_le_plainSharpDegree (K : Type u) [CommRing K]
    (comp₀ : ∀ m : ℕ, Fin (dwz63PlainCountDepth dwz63AssemblyBlocks m + 1) → Fin 15)
    (hcomp₀ : ∀ m : ℕ, WordType.multiplicity (comp₀ m) =
      WordType.proportionalCounts dwz63Alpha (dwz63AssemblyBlocks * (m + 1)))
    (xword : ∀ m : ℕ, PositiveWord (Fin 5) (dwz63PlainCountDepth dwz63AssemblyBlocks m))
    (hxword : ∀ m : ℕ, xword m ∈ dwz63PlainLegTargets .X
      (dwz63PlainCountDepth dwz63AssemblyBlocks m) (dwz63AssemblyBlocks * (m + 1)))
    (hdeg11 : ∃ cutoff : ℕ, ∀ m : ℕ, cutoff ≤ m → 11 ≤ dwz63PlainSharpDegree K
      (dwz63PlainCountDepth dwz63AssemblyBlocks m) (dwz63AssemblyBlocks * (m + 1))) :
    ∃ cutoff : ℕ, ∀ m : ℕ, cutoff ≤ m →
      11 * dwz63CompetitorBound (dwz63Split (m + 1))
          (WordType.proportionalCounts dwz63Alpha (dwz63AssemblyBlocks * (m + 1)))
          (dwz63ZIndex ∘ comp₀ m) (comp₀ m) ≤
        dwz63PlainSharpDegree K (dwz63PlainCountDepth dwz63AssemblyBlocks m)
          (dwz63AssemblyBlocks * (m + 1)) := by
  classical
  obtain ⟨c11, hc11⟩ := hdeg11
  have hfib : ∀ m : ℕ,
      (PartitionHashEncoding.sourceWordLegFiber (dwz63PlainCountDepth dwz63AssemblyBlocks m)
        (dwz63PlainMarginalWords K (dwz63PlainCountDepth dwz63AssemblyBlocks m)
          (dwz63AssemblyBlocks * (m + 1))) .X (xword m)).card ≤
        dwz63PlainSharpDegree K (dwz63PlainCountDepth dwz63AssemblyBlocks m)
          (dwz63AssemblyBlocks * (m + 1)) := fun m ↦
    card_sourceWordLegFiber_le_sharpDegree K .X
      (dwz63PlainCountDepth_succ dwz63_assemblyBlocks_pos m) (hxword m)
  obtain ⟨G, hG⟩ : ∃ G : ℕ → ℕ, ∀ N : ℕ,
      G N = if 11 ≤ dwz63PlainSharpDegree K (dwz63PlainCountDepth dwz63AssemblyBlocks N)
            (dwz63AssemblyBlocks * (N + 1)) then
          dwz63PlainSharpDegree K (dwz63PlainCountDepth dwz63AssemblyBlocks N)
            (dwz63AssemblyBlocks * (N + 1)) / 11
        else (PartitionHashEncoding.sourceWordLegFiber
          (dwz63PlainCountDepth dwz63AssemblyBlocks N)
          (dwz63PlainMarginalWords K (dwz63PlainCountDepth dwz63AssemblyBlocks N)
            (dwz63AssemblyBlocks * (N + 1))) .X (xword N)).card := ⟨_, fun _ ↦ rfl⟩
  have hcountOld := dwz63_hcount_of_rate
    (dwz63_plainCountSu_nonneg dwz63AssemblyBlocks dwz63_assemblyBlocks_pos)
    (dwz63_plainCountSl_nonneg dwz63AssemblyBlocks dwz63_assemblyBlocks_pos)
    dwz63AssemblyRateCompat_pos.le
    (dwz63PlainBlockRateX_pos dwz63AssemblyBlocks)
    (dwz63PlainBlockRateZ_pos dwz63AssemblyBlocks) one_pos (fun _ ↦ le_rfl)
    (dwz63_assembly_hupper comp₀ hcomp₀)
    (dwz63_hlower K dwz63AssemblyBlocks dwz63_assemblyBlocks_pos xword hxword one_pos le_rfl)
  have hcount : ∀ N : ℕ,
      (((dwz63Split (N + 1)).matchable
          (WordType.proportionalCounts dwz63Alpha (dwz63AssemblyBlocks * (N + 1)))
          (dwz63ZIndex ∘ comp₀ N)).card : ℝ) * dwz63AssemblyRateCompat ^ N ≤
        (21 * (dwz63PlainCountSu dwz63AssemblyBlocks N *
            dwz63PlainCountSl dwz63AssemblyBlocks N)) *
          (dwz63AssemblyRateCompat * dwz63PlainBlockRateX dwz63AssemblyBlocks /
            (dwz63PlainBlockRateZ dwz63AssemblyBlocks * 1)) ^ N * ((G N : ℕ) : ℝ) := by
    intro N
    have hnat : (PartitionHashEncoding.sourceWordLegFiber
        (dwz63PlainCountDepth dwz63AssemblyBlocks N)
        (dwz63PlainMarginalWords K (dwz63PlainCountDepth dwz63AssemblyBlocks N)
          (dwz63AssemblyBlocks * (N + 1))) .X (xword N)).card ≤ 21 * G N := by
      have h1 := hfib N
      have h2 := hG N
      by_cases h : 11 ≤ dwz63PlainSharpDegree K (dwz63PlainCountDepth dwz63AssemblyBlocks N)
          (dwz63AssemblyBlocks * (N + 1))
      · rw [if_pos h] at h2
        omega
      · rw [if_neg h] at h2
        omega
    have hcast : ((PartitionHashEncoding.sourceWordLegFiber
        (dwz63PlainCountDepth dwz63AssemblyBlocks N)
        (dwz63PlainMarginalWords K (dwz63PlainCountDepth dwz63AssemblyBlocks N)
          (dwz63AssemblyBlocks * (N + 1))) .X (xword N)).card : ℝ) ≤
        21 * ((G N : ℕ) : ℝ) := by exact_mod_cast hnat
    have hnn : (0 : ℝ) ≤ (dwz63PlainCountSu dwz63AssemblyBlocks N *
        dwz63PlainCountSl dwz63AssemblyBlocks N) *
        (dwz63AssemblyRateCompat * dwz63PlainBlockRateX dwz63AssemblyBlocks /
          (dwz63PlainBlockRateZ dwz63AssemblyBlocks * 1)) ^ N := by
      refine mul_nonneg (mul_nonneg
        (dwz63_plainCountSu_nonneg dwz63AssemblyBlocks dwz63_assemblyBlocks_pos N)
        (dwz63_plainCountSl_nonneg dwz63AssemblyBlocks dwz63_assemblyBlocks_pos N)) ?_
      exact pow_nonneg dwz63_assemblyRatio_nonneg N
    calc (((dwz63Split (N + 1)).matchable
            (WordType.proportionalCounts dwz63Alpha (dwz63AssemblyBlocks * (N + 1)))
            (dwz63ZIndex ∘ comp₀ N)).card : ℝ) * dwz63AssemblyRateCompat ^ N
        ≤ (dwz63PlainCountSu dwz63AssemblyBlocks N *
            dwz63PlainCountSl dwz63AssemblyBlocks N) *
            (dwz63AssemblyRateCompat * dwz63PlainBlockRateX dwz63AssemblyBlocks /
              (dwz63PlainBlockRateZ dwz63AssemblyBlocks * 1)) ^ N *
            (((PartitionHashEncoding.sourceWordLegFiber
              (dwz63PlainCountDepth dwz63AssemblyBlocks N)
              (dwz63PlainMarginalWords K (dwz63PlainCountDepth dwz63AssemblyBlocks N)
                (dwz63AssemblyBlocks * (N + 1))) .X (xword N)).card : ℝ)) := hcountOld N
      _ ≤ (dwz63PlainCountSu dwz63AssemblyBlocks N *
            dwz63PlainCountSl dwz63AssemblyBlocks N) *
            (dwz63AssemblyRateCompat * dwz63PlainBlockRateX dwz63AssemblyBlocks /
              (dwz63PlainBlockRateZ dwz63AssemblyBlocks * 1)) ^ N *
            (21 * ((G N : ℕ) : ℝ)) :=
          mul_le_mul_of_nonneg_left hcast hnn
      _ = _ := by ring
  obtain ⟨cutoff, hcut⟩ := dwz63_cofinal_competitorBound_le_degree
    dwz63_subexponential_assemblySlack
    (((dwz63_subexponential_plainCountSu dwz63AssemblyBlocks dwz63_assemblyBlocks_pos).mul
      (dwz63_subexponential_plainCountSl dwz63AssemblyBlocks
        dwz63_assemblyBlocks_pos)).const_mul (by norm_num))
    dwz63_assemblyRatio_nonneg dwz63_assemblyRatio_lt_one
    (dwz63_assembly_hbrick comp₀ hcomp₀) hcount
  refine ⟨max cutoff c11, fun m hm ↦ ?_⟩
  have hm1 : cutoff ≤ m := le_trans (le_max_left _ _) hm
  have h11 := hc11 m (le_trans (le_max_right _ _) hm)
  have hT : 0 < ((dwz63Split (m + 1)).typicalSet (dwz63ZIndex ∘ comp₀ m)).card := by
    refine dwz63_card_split_typicalSet_pos (m + 1) (comp₀ m) ?_
    rw [hcomp₀ m, dwz63AssemblyBlocks_eq]
  have hV := (dwz63_competitorBound_le_iff _ _ _ _ _ hT).mpr (hcut m hm1)
  have hGm := hG m
  rw [if_pos h11] at hGm
  have hdiv := Nat.mul_div_le (dwz63PlainSharpDegree K
    (dwz63PlainCountDepth dwz63AssemblyBlocks m) (dwz63AssemblyBlocks * (m + 1))) 11
  omega

end AlgebraicComplexity.Examples
