/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoUniformCompetitorCoarse
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoPlainModulusBranch
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoSharpDegreeElevenLower
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoBranchGrowth
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoReferenceWord
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoHoleIntegrationSeedArith

set_option autoImplicit false

/-!
# The two remaining seed-selection inputs: the seed count and the degree comparison

Layer 4 (`AlgebraicComplexity/Examples/`).  `[duan2023faster]`, section 6.1 `sec:global-algo`,
paragraph "Asymmetric Hashing" (`papers/sources/2210.10173/global_value.tex:130-140`).  Two
hypotheses of the section 6.3 seed selection are still carried as binders by every client:

* `hlarge`, "there are enough seeds to batch" --- the integer form of the paper's
  `E[N_retain] ≥ N_α/M · 2^{-o(n)}` (`:137-139`), which is what makes the retained family big
  enough that the Hole-Lemma batching of `:100-102` has room;
* `11 · V ≤ d`, the finite form of `M_0`'s `max` selecting its first branch (`:137`), at the
  competitor bound `V` of `lemma:pcomp_g`.

This module discharges the first outright and puts the second in the shape a per-period client
can use.

## `hlarge` is `hbranch` divided by the loss

`dwz63JointSeedCount marked buckets q = 3 (marked · buckets) / (8 q²)`
(`Examples/DuanWuZhouLevelTwoHoleIntegrationSeedArith.lean:114`), so `hlarge` is the integer
statement `2 · goodBatchSize · 8 q² ≤ 3 · marked · buckets`.  The two real inequalities the
tree already has multiply into exactly that:
`dwz63_eventually_hlarge_le_branch_pow` (`…BranchGrowth.lean:86`) gives
`2 (5N+1) · 2 L ≤ branch^N`, and the Behrend selection
`exists_behrend_dwz63_plainHashBranch_marked` (`…MarkedHashBranch.lean:212`) gives
`branch^N · 4 q² ≤ L · 3 · marked · buckets`.  Multiplying the first by `4 q² ≥ 0` and
chaining cancels the strictly positive loss `L`, and `Nat.le_div_iff_mul_le` turns the product
into the quotient.  No new asymptotics: this is the paper's own "exponential beats the hash
loss" step (`:139`, the `2^{-o(n)}`) at the finite constants.

## The degree comparison, with the component word inside

`dwz63_cofinal_eleven_mul_competitorBound_le_plainSharpDegree`
(`Examples/DuanWuZhouLevelTwoPlainModulusBranch.lean:121`) bounds the competitor bound at *one*
chosen reference sequence `comp₀`.  A per-period client does not get to choose that sequence: it
is handed a reference word and must estimate at *its* component word.  The two agree, and that is
not an accident of the Lean --- it is `[duan2023faster]`'s own

> due to symmetry, `p_comp` is independent of which block `Z_K̂` we choose (`:179`),

formalized as `dwz63_competitorBound_eq_of_mem_matchable`
(`Examples/DuanWuZhouLevelTwoUniformCompetitorCoarse.lean`).  So the reference sequence can be
supplied here once and for all, from `dwz63_exists_referenceWord`, and the conclusion universally
quantified over every component word of the prescribed type.  The remaining binders of the modulus
branch are discharged too: the leg-target witness from `dwz63PlainLegCount_pos`, and the cofinal
`hdeg11` from `dwz63_cofinal_eleven_le_plainSharpDegree`.

Primary source `[duan2023faster]`: Ran Duan, Hongxun Wu and Renfei Zhou, *Faster Matrix
Multiplication via Asymmetric Hashing*, arXiv:2210.10173, section 6.1 `sec:global-algo`,
`papers/sources/2210.10173/global_value.tex:130-140`, and §6.2 `:179`, at the section 6.3
instance `:332-378`.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor CompatibleSplit

universe u

noncomputable section

/-! ## The leg-target witness -/

/-- **The kept leg words are nonempty at the forced length.**

Proof sketch: `card_dwz63PlainLegTargets` identifies the count with `dwz63PlainLegCount`, which is
positive by `dwz63PlainLegCount_pos`. -/
theorem dwz63_plainLegTargets_nonempty (c : Leg) {n t : ℕ} (hn : n + 1 = 100000000 * t) :
    (dwz63PlainLegTargets c n t).Nonempty := by
  rw [← Finset.card_pos, card_dwz63PlainLegTargets]
  exact dwz63PlainLegCount_pos c hn

/-! ## `hlarge` -/

/-- **`hlarge` from the branch inequality** (`global_value.tex:137-139`).

Proof sketch: multiply the growth inequality by `4 q² ≥ 0`, chain with the Behrend branch
inequality, cancel the positive loss, cast to `ℕ`, and apply `Nat.le_div_iff_mul_le`. -/
theorem dwz63_hlarge_of_hbranch (K : Type u) [CommRing K] {n q marked buckets : ℕ} (hq : 0 < q)
    (hgrowth : 2 * (5 * ((n + 1 : ℕ) : ℝ) + 1) *
        (2 * dwz63PlainMarkedLossHashJoint K (n + 1)) ≤ dwz63HashingBranch ^ (n + 1))
    (hbranch : dwz63HashingBranch ^ (n + 1) * (4 * ((q : ℝ) * (q : ℝ))) ≤
      dwz63PlainMarkedLossHashJoint K (n + 1) * (3 * (marked : ℝ) * (buckets : ℝ))) :
    2 * dwz63GoodBatchSize n ≤ dwz63JointSeedCount marked buckets q := by
  have hL : 0 < dwz63PlainMarkedLossHashJoint K (n + 1) :=
    dwz63PlainMarkedLossHashJoint_pos K (n + 1)
  have hgbs : ((dwz63GoodBatchSize n : ℕ) : ℝ) = 5 * ((n + 1 : ℕ) : ℝ) + 1 := by
    simp only [dwz63GoodBatchSize]
    push_cast
    ring
  have hEq : dwz63PlainMarkedLossHashJoint K (n + 1) *
        (16 * (5 * ((n + 1 : ℕ) : ℝ) + 1) * ((q : ℝ) * (q : ℝ))) =
      (2 * (5 * ((n + 1 : ℕ) : ℝ) + 1) * (2 * dwz63PlainMarkedLossHashJoint K (n + 1))) *
        (4 * ((q : ℝ) * (q : ℝ))) := by ring
  have hstep : dwz63PlainMarkedLossHashJoint K (n + 1) *
        (16 * ((dwz63GoodBatchSize n : ℕ) : ℝ) * ((q : ℝ) * (q : ℝ))) ≤
      dwz63PlainMarkedLossHashJoint K (n + 1) * (3 * (marked : ℝ) * (buckets : ℝ)) := by
    rw [hgbs, hEq]
    exact le_trans (mul_le_mul_of_nonneg_right hgrowth (by positivity)) hbranch
  have hreal : 16 * ((dwz63GoodBatchSize n : ℕ) : ℝ) * ((q : ℝ) * (q : ℝ)) ≤
      3 * (marked : ℝ) * (buckets : ℝ) := le_of_mul_le_mul_left hstep hL
  have hnat : 2 * dwz63GoodBatchSize n * (8 * (q * q)) ≤ 3 * (marked * buckets) := by
    have hcast : ((2 * dwz63GoodBatchSize n * (8 * (q * q)) : ℕ) : ℝ) ≤
        ((3 * (marked * buckets) : ℕ) : ℝ) := by
      push_cast
      nlinarith [hreal]
    exact_mod_cast hcast
  have hpos : 0 < 8 * (q * q) := Nat.mul_pos (by norm_num) (Nat.mul_pos hq hq)
  unfold dwz63JointSeedCount
  exact (Nat.le_div_iff_mul_le hpos).mpr hnat

/-! ## The degree comparison at every component word of the prescribed type -/

/-- **`11 · V ≤ d` cofinally, at every component word of the type**
(`global_value.tex:137`, with `:179`).

The modulus branch bounds the competitor bound at one reference sequence; the paper's own
independence of `p_comp` from the chosen block moves it to every component word of the same
type.  The reference sequence, the leg-target witness and the cofinal `hdeg11` are all supplied
here, so nothing is carried.

Proof sketch: `dwz63_exists_referenceWord` at each depth gives `comp₀`;
`dwz63_plainLegTargets_nonempty` gives `xword`; `dwz63_cofinal_eleven_le_plainSharpDegree` at
`len t := 10⁸ t - 1` gives the cofinal `hdeg11` (the depth is that `len` at
`t = blocks · (m+1)` definitionally); then
`dwz63_cofinal_eleven_mul_competitorBound_le_plainSharpDegree` applies, and
`dwz63_competitorBound_eq_of_mem_matchable` transfers its conclusion to the given `comp`. -/
theorem dwz63_cofinal_eleven_mul_competitorBound_uniform (K : Type u) [CommRing K] :
    ∃ cutoff : ℕ, ∀ m : ℕ, cutoff ≤ m →
      ∀ comp : Fin (dwz63PlainCountDepth dwz63AssemblyBlocks m + 1) → Fin 15,
        WordType.multiplicity comp =
          WordType.proportionalCounts dwz63Alpha (dwz63AssemblyBlocks * (m + 1)) →
        11 * dwz63CompetitorBound (dwz63Split (m + 1))
            (WordType.proportionalCounts dwz63Alpha (dwz63AssemblyBlocks * (m + 1)))
            (dwz63ZIndex ∘ comp) comp ≤
          dwz63PlainSharpDegree K (dwz63PlainCountDepth dwz63AssemblyBlocks m)
            (dwz63AssemblyBlocks * (m + 1)) := by
  classical
  have hprop : ∀ (m : ℕ) (u : Fin 15),
      WordType.proportionalCounts dwz63Alpha (dwz63AssemblyBlocks * (m + 1)) u
        = 200000000 * (dwz63Alpha u * (m + 1)) := by
    intro m u
    show dwz63Alpha u * (dwz63AssemblyBlocks * (m + 1)) = _
    rw [dwz63AssemblyBlocks_eq]
    ring
  choose wRef hwRef using fun m : ℕ ↦ dwz63_exists_referenceWord K
    (dwz63PlainCountDepth dwz63AssemblyBlocks m) (m + 1) (dwz63_assemblyDepth_succ m)
  have hcomp₀ : ∀ m : ℕ,
      WordType.multiplicity (dwz63Seg K (dwz63PlainCountDepth dwz63AssemblyBlocks m) (wRef m)) =
        WordType.proportionalCounts dwz63Alpha (dwz63AssemblyBlocks * (m + 1)) :=
    fun m ↦ funext fun u ↦ (hwRef m u).trans (hprop m u).symm
  have hdepth : ∀ m : ℕ, dwz63PlainCountDepth dwz63AssemblyBlocks m + 1 =
      100000000 * (dwz63AssemblyBlocks * (m + 1)) :=
    fun m ↦ dwz63PlainCountDepth_succ dwz63_assemblyBlocks_pos m
  choose xword hxword using fun m : ℕ ↦
    dwz63_plainLegTargets_nonempty Leg.X (hdepth m)
  have hneX : ∀ t : ℕ, 0 < t →
      (dwz63PlainLegTargets Leg.X (100000000 * t - 1) t).Nonempty := by
    intro t ht
    refine dwz63_plainLegTargets_nonempty Leg.X ?_
    have h : 0 < 100000000 * t := Nat.mul_pos (by norm_num) ht
    omega
  choose xw hxw using hneX
  have hdeg11 : ∃ cutoff : ℕ, ∀ m : ℕ, cutoff ≤ m → 11 ≤ dwz63PlainSharpDegree K
      (dwz63PlainCountDepth dwz63AssemblyBlocks m) (dwz63AssemblyBlocks * (m + 1)) := by
    obtain ⟨c, hc⟩ := dwz63_cofinal_eleven_le_plainSharpDegree K (fun t ↦ 100000000 * t - 1)
      (fun t ht ↦ by
        have h : 0 < 100000000 * t := Nat.mul_pos (by norm_num) ht
        omega) xw hxw
    refine ⟨c, fun m hm ↦ ?_⟩
    have hle : c ≤ dwz63AssemblyBlocks * (m + 1) := by
      have h1 : m + 1 ≤ dwz63AssemblyBlocks * (m + 1) :=
        Nat.le_mul_of_pos_left _ dwz63_assemblyBlocks_pos
      omega
    exact hc _ hle
  obtain ⟨cut, hcut⟩ := dwz63_cofinal_eleven_mul_competitorBound_le_plainSharpDegree K
    (fun m ↦ dwz63Seg K (dwz63PlainCountDepth dwz63AssemblyBlocks m) (wRef m)) hcomp₀
    xword hxword hdeg11
  refine ⟨cut, fun m hm comp hcomp ↦ ?_⟩
  have heq := dwz63_competitorBound_eq_of_mem_matchable (dwz63Split (m + 1))
    (WordType.proportionalCounts dwz63Alpha (dwz63AssemblyBlocks * (m + 1)))
    ((dwz63Split (m + 1)).mem_matchable.mpr ⟨hcomp, rfl⟩)
    ((dwz63Split (m + 1)).mem_matchable.mpr ⟨hcomp₀ m, rfl⟩)
  have hgoal : dwz63CompetitorBound (dwz63Split (m + 1))
        (WordType.proportionalCounts dwz63Alpha (dwz63AssemblyBlocks * (m + 1)))
        (dwz63ZIndex ∘ comp) comp =
      dwz63CompetitorBound (dwz63Split (m + 1))
        (WordType.proportionalCounts dwz63Alpha (dwz63AssemblyBlocks * (m + 1)))
        (dwz63ZIndex ∘ dwz63Seg K (dwz63PlainCountDepth dwz63AssemblyBlocks m) (wRef m))
        (dwz63Seg K (dwz63PlainCountDepth dwz63AssemblyBlocks m) (wRef m)) := heq
  rw [hgoal]
  exact hcut m hm

end

end AlgebraicComplexity.Examples
