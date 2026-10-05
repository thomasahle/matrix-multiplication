/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoSeedLargeBatch
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoStepOneCutCountInputs
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoSplitAlphabetBridge
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoMarkedHashBranch
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoMarkedWitness

set_option autoImplicit false

/-!
# The per-period seeded stage of the section 6.3 endpoint

Layer 4 (`AlgebraicComplexity/Examples/`).  `[duan2023faster]`, section 6.1 `sec:global-algo`
(`papers/sources/2210.10173/global_value.tex:98-121`, with `hole_lemma.tex:159-168`) at the
section 6.3 instance (`global_value.tex:332-378`): at every admissible period `s` beyond a
cutoff, one seed carries the six-orientation stage over `𝒯^{(1)}`, the sixth power of the copy
count, and the batching-loss bound.

This is the `hseededPeriod` binder of
`omega_lt_2374631_of_seededPeriod_goodBatchLoss`
(`Examples/DuanWuZhouLevelTwoAssemblyOrbitClosure.lean:126`), stated at that binder's exact
shape --- the statement below is the binder's own bytes.

## What each input is, and where it comes from

* `B` and `ThreeAPFree B` and the branch inequality: the Behrend selection
  `exists_behrend_dwz63_plainHashBranch_marked` (`…MarkedHashBranch.lean:212`), i.e. the
  progression-free bucket family of `hole_lemma.tex`.
* `hquarter`, `hzIndex`: `dwz63_cut_hquarter` and `dwz63_cut_hzIndex`
  (`…StepOneCutCountInputs.lean`), the first branch of `M_0` (`:137`) and
  `def:global-compatible`'s standing `Z_K̂ ∈ Z_K` (`:45`).
* `hcompetitors` and `hmodulus` at ONE AND THE SAME `V`.  `V` is the left-record competitor
  bound `dwz63CompetitorBound (dwz63Split s) α (zIndex ∘ comp) comp` at the period's own
  component word `comp = dwz63Seg K n wRef` --- the quantity `lemma:pcomp_g` computes.
  `dwz63_uniform_hV_coarse` bounds every competitor family by it uniformly in the large
  Z-block and the small block, `dwz63_hV_pair_of_hV` carries that to the pair alphabet the hole
  side reads, and `dwz63_plainHashModulus_seedSelection` turns `11 · V ≤ d` into
  `256 · V ≤ 3 |R|`.  The two hypotheses therefore hold at literally the same `V`, which is
  what makes the modulus paragraph `:130-140` one statement rather than two.
* `hlarge`: `dwz63_hlarge_of_hbranch` (`…SeedLargeBatch.lean`), the paper's `:137-139`.
* `useless := 0`: rule (ii) removes nothing in the localized picture (Additional Zeroing-Out
  Step 2, `:74-90`), so its allowance is zero.

## The cutoff

Both growth facts are cofinal --- the degree comparison `11 · V ≤ d` and the seed count --- so
the statement is "for every admissible period beyond `N₀`", with `N₀` the maximum of the two
cutoffs.  `[duan2023faster]`'s §6 is itself stated for sufficiently large `n`.

Primary source `[duan2023faster]`: Ran Duan, Hongxun Wu and Renfei Zhou, *Faster Matrix
Multiplication via Asymmetric Hashing*, arXiv:2210.10173, section 6.1 `sec:global-algo`,
`papers/sources/2210.10173/global_value.tex:98-121, 130-140`, with `hole_lemma.tex:159-168`,
at the section 6.3 instance `global_value.tex:332-378`.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor ProgressionHash CompatibleSplit

universe u

noncomputable section

/-! ## One period -/

/-- **The seeded stage at one admissible period.**

Proof sketch: the Behrend family supplies `B`, `ThreeAPFree B` and `hbranch` at
`lossHash := dwz63PlainMarkedLossHashJoint K (n+1)`; `dwz63_hlarge_of_hbranch` turns that plus
the growth hypothesis into `hlarge`; the competitor count and the modulus condition are both
taken at `V := dwz63CompetitorBound (dwz63Split s) α (zIndex ∘ dwz63Seg K n wRef)
(dwz63Seg K n wRef)`, through `dwz63_uniform_hV_coarse`, `dwz63_hV_pair_of_hV`,
`dwz63_hcompetitorsTyped` and `dwz63_plainHashModulus_seedSelection`; and
`dwz63_exists_seed_cutStage_marked` then returns the seed. -/
theorem dwz63_seededPeriod_step (K : Type u) [CommRing K] (n s : ℕ) (hs : 0 < s)
    (wRef : PositiveWord ((cwSquarePartitionedTensor K dwz63Q).support) n)
    (hn : n + 1 = 20000000000000000 * s)
    (hmu : ∀ t : Fin 15, WordType.multiplicity (dwz63Seg K n wRef) t
      = 200000000 * (dwz63Alpha t * s))
    (hwRef : wRef ∈ dwz63MarkedWords n (WordType.proportionalCounts dwz63Alpha (200000000 * s)))
    (h11 : 11 * dwz63CompetitorBound (dwz63Split s)
        (WordType.proportionalCounts dwz63Alpha (200000000 * s))
        (dwz63ZIndex ∘ dwz63Seg K n wRef) (dwz63Seg K n wRef) ≤
      dwz63PlainSharpDegree K n (200000000 * s))
    (hgrowth : 2 * (5 * ((n + 1 : ℕ) : ℝ) + 1) *
        (2 * dwz63PlainMarkedLossHashJoint K (n + 1)) ≤ dwz63HashingBranch ^ (n + 1)) :
    ∃ (B : Finset (dwz63SharpHashField (dwz63PlainSharpDegree K n (200000000 * s))))
      (seed : ProgressionHash.Seed
        (dwz63SharpHashField (dwz63PlainSharpDegree K n (200000000 * s)))
        (Fin (n + 1)))
      (batches : ℕ),
      ThreeAPFree (B : Set (dwz63SharpHashField
        (dwz63PlainSharpDegree K n (200000000 * s)))) ∧
      Restricts
        (Tensor.power (symSix K (cwSquarePartitionedTensor K dwz63Q).realize) (n + 1))
        (Tensor.indexedDirectSum
          (fun _ : dwz63SymSixIndex (Fin batches) ↦
            symSix K (dwz63ReferenceLeaf K n (dwz63JoinedAlphaTilde s) wRef).realize)) ∧
      dwz63TrueCopyRate ^ (6 * (n + 1)) ≤
        (4 * dwz63PlainMarkedLossHashJoint K (n + 1)) ^ 6 *
          ((Fintype.card (dwz63PlainJointRetainedSupport K
            (dwz63_cwSquareFieldValue_sharpHashField_injective
              (dwz63PlainSharpDegree K n (200000000 * s)))
            n (200000000 * s)
            (dwz63MarkedWords n
              (WordType.proportionalCounts dwz63Alpha (200000000 * s))) B seed) : ℝ) ^ 6) ∧
      ((dwz63PlainJointRetainedSupport K
          (dwz63_cwSquareFieldValue_sharpHashField_injective
            (dwz63PlainSharpDegree K n (200000000 * s)))
          n (200000000 * s)
          (dwz63MarkedWords n
            (WordType.proportionalCounts dwz63Alpha (200000000 * s))) B seed).card : ℝ) ≤
        ((4 * dwz63GoodBatchSize n : ℕ) : ℝ) * (Fintype.card (Fin batches) : ℝ) := by
  classical
  have ht : 0 < 200000000 * s := Nat.mul_pos (by norm_num) hs
  have hn' : n + 1 = 100000000 * (200000000 * s) := by rw [hn]; ring
  obtain ⟨B, hB, hbr⟩ := exists_behrend_dwz63_plainHashBranch_marked K ht hn'
  have hq : 0 < Fintype.card
      (dwz63SharpHashField (dwz63PlainSharpDegree K n (200000000 * s))) :=
    Fintype.card_pos_iff.mpr ⟨0⟩
  have hmarked := dwz63_marked_subset_marginal K n (200000000 * s)
  have hcompRef := dwz63_multiplicity_dwz63Seg_of_mem_markedWords K
    (WordType.proportionalCounts dwz63Alpha (200000000 * s)) wRef hwRef
  have hVpair := dwz63_hV_pair_of_hV s
    (WordType.proportionalCounts dwz63Alpha (200000000 * s))
    (dwz63CompetitorBound (dwz63Split s)
      (WordType.proportionalCounts dwz63Alpha (200000000 * s))
      (dwz63ZIndex ∘ dwz63Seg K n wRef) (dwz63Seg K n wRef))
    (dwz63_uniform_hV_coarse s (WordType.proportionalCounts dwz63Alpha (200000000 * s))
      (dwz63Seg K n wRef) hcompRef)
  obtain ⟨seed, batches, hrest, hcopy, hcard⟩ := dwz63_exists_seed_cutStage_marked K
    (dwz63_cwSquareFieldValue_sharpHashField_injective
      (dwz63PlainSharpDegree K n (200000000 * s)))
    n (200000000 * s) s B hB wRef hwRef hmu
    (dwz63CompetitorBound (dwz63Split s)
      (WordType.proportionalCounts dwz63Alpha (200000000 * s))
      (dwz63ZIndex ∘ dwz63Seg K n wRef) (dwz63Seg K n wRef))
    (dwz63_cut_hquarter K hn' hmarked)
    (dwz63_cut_hzIndex K s (dwz63_cwSquareFieldValue_sharpHashField_injective
      (dwz63PlainSharpDegree K n (200000000 * s))) wRef hmarked)
    (dwz63_hcompetitorsTyped (dwz63SplitPair s)
      (dwz63CutComponent K n (dwz63_cwSquareFieldValue_sharpHashField_injective
        (dwz63PlainSharpDegree K n (200000000 * s))))
      (dwz63CanonicalRead K n (dwz63_cwSquareFieldValue_sharpHashField_injective
        (dwz63PlainSharpDegree K n (200000000 * s))) wRef (dwz63JoinedAlphaTilde s))
      (WordType.proportionalCounts dwz63Alpha (200000000 * s)) _ _ _
      (dwz63_cut_componentInjOn K (dwz63_cwSquareFieldValue_sharpHashField_injective
        (dwz63PlainSharpDegree K n (200000000 * s))))
      (fun a _ha w ↦ hVpair _ _))
    (dwz63_plainHashModulus_seedSelection K n (200000000 * s) _ h11)
    (fun _ ↦ 0) (fun _ ↦ Nat.zero_le _)
    (dwz63_hlarge_of_hbranch K hq hgrowth hbr)
    (dwz63PlainMarkedLossHashJoint_nonneg K (n + 1)) hbr
  exact ⟨B, seed, batches, hB, hrest, hcopy, hcard⟩

/-! ## Every period beyond a cutoff -/

/-- **`hseededPeriod`** (`global_value.tex:98-121, 130-140`, at `:332-378`).

The binder of `omega_lt_2374631_of_seededPeriod_goodBatchLoss`, discharged.

Proof sketch: `N₀` is the maximum of the degree-comparison cutoff (shifted by one, so that
`s - 1` is past it) and the seed-count cutoff.  At a period `s` beyond it, `n` is forced to be
`dwz63PlainCountDepth dwz63AssemblyBlocks (s - 1)` by `dwz63_assemblyDepth_succ`, so
`dwz63_cofinal_eleven_mul_competitorBound_uniform` applies at the period's own component word
`dwz63Seg K n wRef` --- whose type is the prescribed one by
`dwz63_multiplicity_dwz63Seg_of_mem_markedWords` --- and `dwz63_seededPeriod_step` closes. -/
theorem dwz63_exists_seededPeriod (K : Type u) [CommRing K] :
    ∃ N₀ : ℕ, ∀ s : ℕ,
      40000000000000 ∣ s → 312500000000000000000 ∣ s → N₀ ≤ s →
      ∀ (n : ℕ) (wRef : PositiveWord ((cwSquarePartitionedTensor K dwz63Q).support) n),
        n + 1 = 20000000000000000 * s →
        (∀ t : Fin 15, WordType.multiplicity (dwz63Seg K n wRef) t
          = 200000000 * (dwz63Alpha t * s)) →
        wRef ∈ dwz63MarkedWords n (WordType.proportionalCounts dwz63Alpha (200000000 * s)) →
        ∃ (B : Finset (dwz63SharpHashField (dwz63PlainSharpDegree K n (200000000 * s))))
          (seed : ProgressionHash.Seed
            (dwz63SharpHashField (dwz63PlainSharpDegree K n (200000000 * s)))
            (Fin (n + 1)))
          (batches : ℕ),
          ThreeAPFree (B : Set (dwz63SharpHashField
            (dwz63PlainSharpDegree K n (200000000 * s)))) ∧
          Restricts
            (Tensor.power (symSix K (cwSquarePartitionedTensor K dwz63Q).realize) (n + 1))
            (Tensor.indexedDirectSum
              (fun _ : dwz63SymSixIndex (Fin batches) ↦
                symSix K (dwz63ReferenceLeaf K n (dwz63JoinedAlphaTilde s) wRef).realize)) ∧
          dwz63TrueCopyRate ^ (6 * (n + 1)) ≤
            (4 * dwz63PlainMarkedLossHashJoint K (n + 1)) ^ 6 *
              ((Fintype.card (dwz63PlainJointRetainedSupport K
                (dwz63_cwSquareFieldValue_sharpHashField_injective
                  (dwz63PlainSharpDegree K n (200000000 * s)))
                n (200000000 * s)
                (dwz63MarkedWords n
                  (WordType.proportionalCounts dwz63Alpha (200000000 * s))) B seed) : ℝ) ^ 6) ∧
          ((dwz63PlainJointRetainedSupport K
              (dwz63_cwSquareFieldValue_sharpHashField_injective
                (dwz63PlainSharpDegree K n (200000000 * s)))
              n (200000000 * s)
              (dwz63MarkedWords n
                (WordType.proportionalCounts dwz63Alpha (200000000 * s))) B seed).card : ℝ) ≤
            ((4 * dwz63GoodBatchSize n : ℕ) : ℝ) * (Fintype.card (Fin batches) : ℝ) := by
  classical
  obtain ⟨cut, hcut⟩ := dwz63_cofinal_eleven_mul_competitorBound_uniform K
  obtain ⟨Ng, hNg⟩ := dwz63_eventually_hlarge_le_branch_pow K
  refine ⟨max (cut + 1) Ng, fun s _h40 _h312 hs n wRef hn hmu hwRef ↦ ?_⟩
  have hscut : cut + 1 ≤ s := le_trans (le_max_left _ _) hs
  have hsNg : Ng ≤ s := le_trans (le_max_right _ _) hs
  have hspos : 0 < s := by omega
  have hgrowth : 2 * (5 * ((n + 1 : ℕ) : ℝ) + 1) *
      (2 * dwz63PlainMarkedLossHashJoint K (n + 1)) ≤ dwz63HashingBranch ^ (n + 1) :=
    hNg (n + 1) (by omega)
  refine dwz63_seededPeriod_step K n s hspos wRef hn hmu hwRef ?_ hgrowth
  have hm : s - 1 + 1 = s := by omega
  have hAB : dwz63AssemblyBlocks * (s - 1 + 1) = 200000000 * s := by
    rw [dwz63AssemblyBlocks_eq, hm]
  have hdepth : dwz63PlainCountDepth dwz63AssemblyBlocks (s - 1) + 1
      = 20000000000000000 * (s - 1 + 1) := dwz63_assemblyDepth_succ (s - 1)
  have hnd : n = dwz63PlainCountDepth dwz63AssemblyBlocks (s - 1) := by omega
  subst hnd
  have hcomp : WordType.multiplicity (dwz63Seg K _ wRef)
      = WordType.proportionalCounts dwz63Alpha (dwz63AssemblyBlocks * (s - 1 + 1)) := by
    rw [hAB]
    exact dwz63_multiplicity_dwz63Seg_of_mem_markedWords K
      (WordType.proportionalCounts dwz63Alpha (200000000 * s)) wRef hwRef
  have hstep := hcut (s - 1) (by omega) (dwz63Seg K _ wRef) hcomp
  rw [hAB, hm] at hstep
  exact hstep

end

end AlgebraicComplexity.Examples
