/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoIsolatedBypass
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoPlainIntegration
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoPlainMarkedBranch
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoPlainStage
import AlgebraicComplexity.MatrixMultiplication.SymSixUniformLeaf

set_option autoImplicit false

/-!
# `omega < 2.374631` at the plain fifteen-block partition

Layer 4 (`AlgebraicComplexity/Examples/`).  The level-two endpoint assembled on
`[DuanWuZhou2022]`'s own route: the hash acts on the **plain** power of the coarse
Coppersmith--Winograd square, `sym₆` lives only in the value functional, and the sixth power of the
copy count appears once, at the end, because the retained leaf is uniform.

The target is `omega_lt_2374631_of_dwz63IsolatedSum`
(`Examples/DuanWuZhouLevelTwoIsolatedBypass.lean`), the specialisation for uniform constituents
whose copy count is a `Fintype.card` --- field-decoupled, so no hash field appears in its
statement.  It is instantiated at

* `index j = len j + 1`, the word length;
* `Iso j = (retained³)²`, the sixfold product `restricts_power_symSix_of_plainStage`
  (`MatrixMultiplication/SymSixUniformLeaf.lean`) produces from a plain-power stage onto one
  uniform leaf;
* `retained j _ = sym₆(leaf j)`, so the per-constituent weight is a single hypothesis about the
  leaf and `HasTauWeight.indexedDirectSum_of_forall` adds the `#Iso` copies;
* `loss = lossHash ^ 6`, subexponential by `subexponential_pow_six`.

The count side is `dwz63_exists_seed_plainCopyCount_at_sharpDegree`
(`Examples/DuanWuZhouLevelTwoPlainIntegration.lean`), the join of the sharp-degree seed with the
copy count, and `Fintype.card Iso = (#retained) ^ 6` matches its exponent exactly.

## Why the hash field varies with `j`, and why `B` and the seed are quantified

The Bertrand modulus is `≍ 8 · (N_α' / N_X)`, which grows with the word length, so the hashing
field cannot be fixed: `R : ℕ → Type v`, one field per scale.  And the seed is chosen *inside*
`dwz63_exists_seed_plainCopyCount_at_sharpDegree`, so a hypothesis that mentions the retained
family must hold for **every** progression-free `B` and every seed --- the pattern of
`Examples/DuanWuZhouLevelTwoIntegrationMarkedFamily.lean`'s `hbudgetY`/`hbudgetZ`.  `hstage` is
therefore quantified over `(B, seed)` with `ThreeAPFree ↑B`.

The word length is carried by two free sequences `len` and `scale` with
`len j + 1 = 10⁸ · scale j` and `len` cofinal, rather than by a subtraction: a truncated `- 1` in a
dependent position is an elaboration hazard over these partitioned families.

## The remaining hypotheses

`omega_lt_2374631_of_plainOpenEstimates` leaves four:

1. `hstage` --- one restriction of the plain power onto a uniform-leaf direct sum over the retained
   family.  This is the conclusion of `dwz63_plainStage_of_uniformLeaf`
   (`Examples/DuanWuZhouLevelTwoPlainStage.lean`), i.e. legwise injectivity of the retained family
   together with the hole-route leaf repair, packaged as one premise: the open §0 adjudication.
2. `hleafWeight` / `hleafValue` --- the values lane: `sym₆` of the leaf carries a `tau`-weight at
   least `exp(dwz63LogVal) ^ (6 (n+1))`.
3. `hmodulus` --- the client's field is large enough for the hash, `8 d ≤ #R`.
4. `hbranch` --- `[DuanWuZhou2022]` §6.3 step (4).

`hbranch` is **discharged** by `Examples/DuanWuZhouLevelTwoPlainMarkedBranch.lean`, at the Bertrand
field `dwz63SharpHashField` and the Behrend set of `exists_threeAPFree_zmod_half_behrend`.  At that
field `hmodulus` is `dwz63SharpHashModulus_requirement`, so
`omega_lt_2374631_of_plainStageAndLeaf` --- the specialisation to the Bertrand field --- carries
only the stage and the leaf value.  (Note that `hbranch` cannot be discharged for an *arbitrary*
field satisfying only `8 d ≤ #R`: its left-hand side is quadratic in `#R` while its right-hand side
is linear, so an upper bound on the modulus is genuinely needed, and Bertrand's postulate is where
it comes from.)

Primary source: Ran Duan, Hongxun Wu and Renfei Zhou, *Faster Matrix Multiplication via Asymmetric
Hashing*, arXiv:2210.10173, section 6.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor

universe u v y

/-! ## The sixfold index -/

/-- **The sixfold index of the `sym₆` distribution.**  `Isomorphic.symSix_indexedDirectSum_uniform`
turns `ι` copies of one leaf into `ι⁶` copies of its symmetrization, in this association. -/
abbrev dwz63SymSixIndex (ι : Type) : Type := ((ι × ι) × ι) × ((ι × ι) × ι)

theorem dwz63_card_symSixIndex (ι : Type) [Fintype ι] :
    Fintype.card (dwz63SymSixIndex ι) = Fintype.card ι ^ 6 := by
  simp only [dwz63SymSixIndex, Fintype.card_prod]
  ring

/-! ## The integration -/

set_option maxRecDepth 8000 in
set_option maxHeartbeats 1000000 in
/-- **`omega < 2.374631` at the plain fifteen-block partition, from four open estimates.**

Every green piece of the plain route is consumed here: the sharp-degree seed and the copy count
(`dwz63_exists_seed_plainCopyCount_at_sharpDegree`), the `sym₆` distribution
(`restricts_power_symSix_of_plainStage`), and the isolated-sum endpoint
(`omega_lt_2374631_of_dwz63IsolatedSum`).  What is left is listed in the module docstring. -/
theorem omega_lt_2374631_of_plainOpenEstimates
    {K : Type u} [Field K]
    {R : ℕ → Type v} [∀ j, Field (R j)] [∀ j, Fintype (R j)] [∀ j, NeZero (2 : R j)]
    (hinj : ∀ j : ℕ, Function.Injective (cwSquareFieldValue (R := R j)))
    (len scale : ℕ → ℕ)
    (hlen : ∀ j : ℕ, len j + 1 = 100000000 * scale j)
    (hcofinal : ∀ cutoff : ℕ, ∃ j : ℕ, cutoff ≤ len j + 1)
    {W : ℕ → Leg → Type y} [∀ j c, AddCommMonoid (W j c)] [∀ j c, Module K (W j c)]
    (leaf : ∀ j : ℕ, Tensor3 K (W j))
    (weight lossHash : ℕ → ℝ)
    (hlossSub : Growth.Subexponential lossHash)
    (hlossNonneg : ∀ N : ℕ, 0 ≤ lossHash N)
    (hstage : ∀ (j : ℕ) (B : Finset (R j))
        (seed : ProgressionHash.Seed (R j) (Fin (len j + 1))),
        ThreeAPFree (B : Set (R j)) →
        Restricts (Tensor.power (cwSquarePartitionedTensor K dwz63Q).realize (len j + 1))
          (Tensor.indexedDirectSum
            (V := fun _ : (dwz63PlainJointRetainedSupport K (hinj j) (len j) (scale j)
                (dwz63PlainMarginalWords K (len j) (scale j)) B seed) ↦ W j)
            fun _ ↦ leaf j))
    (hleafWeight : ∀ j : ℕ, HasTauWeight K (symSix K (leaf j)) dwz63Tau (weight j))
    (hleafValue : ∀ j : ℕ, Real.exp dwz63LogVal ^ (6 * (len j + 1)) ≤ weight j)
    (hmodulus : ∀ j : ℕ, 8 * dwz63PlainSharpDegree K (len j) (scale j) ≤ Fintype.card (R j))
    (hbranch : ∀ j : ℕ, ∃ B : Finset (R j), ThreeAPFree (B : Set (R j)) ∧
        dwz63HashingBranch ^ (len j + 1) *
            (4 * ((Fintype.card (R j) : ℝ) * (Fintype.card (R j) : ℝ))) ≤
          lossHash (len j + 1) *
            (3 * ((dwz63PlainMarginalWords K (len j) (scale j)).card : ℝ) * (B.card : ℝ))) :
    omega K < (2374631 / 1000000 : ℝ) := by
  classical
  choose B hBfree hBbranch using hbranch
  choose seed hseed using fun j : ℕ ↦
    dwz63_exists_seed_plainCopyCount_at_sharpDegree K (hinj j) (hlen j)
      (dwz63PlainMarginalWords K (len j) (scale j)) (Finset.Subset.refl _)
      (B j) (hBfree j) (hmodulus j) (hlossNonneg (len j + 1)) (hBbranch j)
  have hsum : ∀ j : ℕ,
      Restricts (Tensor.power (symSix K (dwz63Source K)) (len j + 1))
        (Tensor.indexedDirectSum
          (fun _ : dwz63SymSixIndex
              (dwz63PlainJointRetainedSupport K (hinj j) (len j) (scale j)
                (dwz63PlainMarginalWords K (len j) (scale j)) (B j) (seed j)) ↦
            symSix K (leaf j))) := fun j ↦
    restricts_power_symSix_of_plainStage (len j) (hstage j (B j) (seed j) (hBfree j))
  have hcount : ∀ j : ℕ, dwz63TrueCopyRate ^ (6 * (len j + 1)) ≤
      lossHash (len j + 1) ^ 6 *
        ((Fintype.card (dwz63SymSixIndex
          (dwz63PlainJointRetainedSupport K (hinj j) (len j) (scale j)
            (dwz63PlainMarginalWords K (len j) (scale j)) (B j) (seed j))) : ℝ)) := by
    intro j
    rw [dwz63_card_symSixIndex]
    push_cast
    exact hseed j
  have hcards : ∀ j : ℕ, 0 < Fintype.card (dwz63SymSixIndex
      (dwz63PlainJointRetainedSupport K (hinj j) (len j) (scale j)
        (dwz63PlainMarginalWords K (len j) (scale j)) (B j) (seed j))) := by
    intro j
    rcases Nat.eq_zero_or_pos (Fintype.card (dwz63SymSixIndex
      (dwz63PlainJointRetainedSupport K (hinj j) (len j) (scale j)
        (dwz63PlainMarginalWords K (len j) (scale j)) (B j) (seed j)))) with h0 | hpos
    · exfalso
      have h1 := hcount j
      rw [h0] at h1
      simp only [Nat.cast_zero, mul_zero] at h1
      exact absurd h1 (not_le.mpr (pow_pos dwz63TrueCopyRate_pos _))
    · exact hpos
  -- ELABORATION RISK: `Iso` is supplied explicitly.  Left as a metavariable it would have to be
  -- solved by matching a six-orientation block family against a metavariable-headed family, which
  -- does not terminate over these partitioned sources.
  exact omega_lt_2374631_of_dwz63IsolatedSum
    (Iso := fun j ↦ dwz63SymSixIndex
      (dwz63PlainJointRetainedSupport K (hinj j) (len j) (scale j)
        (dwz63PlainMarginalWords K (len j) (scale j)) (B j) (seed j)))
    (fun j ↦ len j + 1) (fun j _ ↦ symSix K (leaf j)) weight (fun N ↦ lossHash N ^ 6)
    (subexponential_pow_six hlossSub)
    (fun cutoff ↦ (hcofinal cutoff).imp fun _ hj ↦ ⟨hj, Nat.succ_pos _⟩)
    hsum (fun j _ ↦ hleafWeight j)
    (fun j ↦ lt_of_lt_of_le (pow_pos (Real.exp_pos _) _) (hleafValue j))
    hcards hcount hleafValue

/-! ## The length bookkeeping is satisfiable -/

/-- **The two length side conditions are not vacuous.**  `len j = 10⁸ j + (10⁸ - 1)` and
`scale j = j + 1` satisfy both.  Stated with a sum rather than a truncated difference, and kept
outside every dependent type: the endpoint takes `len` and `scale` as opaque sequences precisely so
that no `- 1` ever reaches a `PositiveWord` index. -/
theorem dwz63_exists_plainIntegrationLengths :
    ∃ len scale : ℕ → ℕ,
      (∀ j : ℕ, len j + 1 = 100000000 * scale j) ∧
        (∀ cutoff : ℕ, ∃ j : ℕ, cutoff ≤ len j + 1) := by
  refine ⟨fun j ↦ 100000000 * j + 99999999, fun j ↦ j + 1, fun j ↦ ?_, fun cutoff ↦ ⟨cutoff, ?_⟩⟩
  · show 100000000 * j + 99999999 + 1 = 100000000 * (j + 1)
    ring
  · show cutoff ≤ 100000000 * cutoff + 99999999 + 1
    omega

/-! ## The Bertrand field: `hbranch` and `hmodulus` discharged -/

/-- **The five coarse degree labels stay distinct in the Bertrand field.**  Its characteristic is
at least `15625`, far above the plain partition's floor of `5`. -/
theorem dwz63_cwSquareFieldValue_sharpHashField_injective (degree : ℕ) :
    Function.Injective (cwSquareFieldValue (R := dwz63SharpHashField degree)) := by
  have hM : 5 ≤ dwz63SharpHashModulus degree :=
    le_trans (by norm_num) (dwz63SharpHashModulus_char_floor degree)
  intro i j hij
  apply Fin.ext
  exact CharP.natCast_injOn_Iio (R := dwz63SharpHashField degree)
    (dwz63SharpHashModulus degree) (i.isLt.trans_le hM) (j.isLt.trans_le hM) hij

set_option maxRecDepth 8000 in
set_option maxHeartbeats 1000000 in
/-- **`omega < 2.374631` at the plain partition, with the count side complete.**

The specialisation of `omega_lt_2374631_of_plainOpenEstimates` to the Bertrand field
`dwz63SharpHashField` at the plain sharp degree.  There `hmodulus` is
`dwz63SharpHashModulus_requirement` and `hbranch` is
`exists_behrend_dwz63_plainHashBranch`, so the only inputs left are the uniform-leaf stage and the
leaf's value. -/
theorem omega_lt_2374631_of_plainStageAndLeaf
    {K : Type u} [Field K]
    (len scale : ℕ → ℕ)
    (hlen : ∀ j : ℕ, len j + 1 = 100000000 * scale j)
    (hcofinal : ∀ cutoff : ℕ, ∃ j : ℕ, cutoff ≤ len j + 1)
    {W : ℕ → Leg → Type y} [∀ j c, AddCommMonoid (W j c)] [∀ j c, Module K (W j c)]
    (leaf : ∀ j : ℕ, Tensor3 K (W j))
    (weight : ℕ → ℝ)
    (hstage : ∀ (j : ℕ)
        (B : Finset (dwz63SharpHashField (dwz63PlainSharpDegree K (len j) (scale j))))
        (seed : ProgressionHash.Seed
          (dwz63SharpHashField (dwz63PlainSharpDegree K (len j) (scale j)))
          (Fin (len j + 1))),
        ThreeAPFree (B : Set (dwz63SharpHashField
          (dwz63PlainSharpDegree K (len j) (scale j)))) →
        Restricts (Tensor.power (cwSquarePartitionedTensor K dwz63Q).realize (len j + 1))
          (Tensor.indexedDirectSum
            (V := fun _ : (dwz63PlainJointRetainedSupport K
                (dwz63_cwSquareFieldValue_sharpHashField_injective
                  (dwz63PlainSharpDegree K (len j) (scale j)))
                (len j) (scale j)
                (dwz63PlainMarginalWords K (len j) (scale j)) B seed) ↦ W j)
            fun _ ↦ leaf j))
    (hleafWeight : ∀ j : ℕ, HasTauWeight K (symSix K (leaf j)) dwz63Tau (weight j))
    (hleafValue : ∀ j : ℕ, Real.exp dwz63LogVal ^ (6 * (len j + 1)) ≤ weight j) :
    omega K < (2374631 / 1000000 : ℝ) := by
  classical
  refine omega_lt_2374631_of_plainOpenEstimates
    (R := fun j ↦ dwz63SharpHashField (dwz63PlainSharpDegree K (len j) (scale j)))
    (fun j ↦ dwz63_cwSquareFieldValue_sharpHashField_injective
      (dwz63PlainSharpDegree K (len j) (scale j)))
    len scale hlen hcofinal leaf weight (dwz63PlainMarkedLossHash K)
    (subexponential_dwz63PlainMarkedLossHash K) (dwz63PlainMarkedLossHash_nonneg K)
    hstage hleafWeight hleafValue ?_ ?_
  · intro j
    rw [card_dwz63SharpHashField]
    exact dwz63SharpHashModulus_requirement _
  · intro j
    obtain ⟨Bset, hfree, hbr⟩ := exists_behrend_dwz63_plainHashBranch K (hlen j)
    exact ⟨Bset, hfree, hbr⟩

/-! ## The endpoint against an already-symmetrized stage -/

set_option maxRecDepth 8000 in
set_option maxHeartbeats 1000000 in
/-- **`omega < 2.374631` from a `sym₆` stage over a batch index.**

`Examples/DuanWuZhouLevelTwoLocalizedStage.lean`'s localized stage already applies
`restricts_power_symSix_of_plainStage` itself and lands on the batch index `β`, not on the retained
family, so it cannot feed `omega_lt_2374631_of_plainOpenEstimates` (which starts at the plain
power).  This is the endpoint it *can* feed: the `sym₆` stage, the leaf's value, and one copy count
against `#β`.

The count is stated against `#β` rather than `#retained` because the batched Hole Lemma repairs one
leaf per batch, so the batching loss --- `#retained ≤ O(n) · #β`, the `1/(8(nℓ+2))` of
`hole_lemma.tex:277` --- has to be paid before this point and belongs to whoever chooses `batch`. -/
theorem omega_lt_2374631_of_plainSymSixStage
    {K : Type u} [Field K]
    (len : ℕ → ℕ)
    (hcofinal : ∀ cutoff : ℕ, ∃ j : ℕ, cutoff ≤ len j + 1)
    {β : ℕ → Type} [∀ j, Fintype (β j)] [∀ j, DecidableEq (β j)]
    {W : ℕ → Leg → Type y} [∀ j c, AddCommMonoid (W j c)] [∀ j c, Module K (W j c)]
    (leaf : ∀ j : ℕ, Tensor3 K (W j))
    (weight loss : ℕ → ℝ)
    (hloss : Growth.Subexponential loss)
    (hstage : ∀ j : ℕ,
      Restricts (Tensor.power (symSix K (cwSquarePartitionedTensor K dwz63Q).realize) (len j + 1))
        (Tensor.indexedDirectSum
          (fun _ : dwz63SymSixIndex (β j) ↦ symSix K (leaf j))))
    (hleafWeight : ∀ j : ℕ, HasTauWeight K (symSix K (leaf j)) dwz63Tau (weight j))
    (hleafValue : ∀ j : ℕ, Real.exp dwz63LogVal ^ (6 * (len j + 1)) ≤ weight j)
    (hcount : ∀ j : ℕ, dwz63TrueCopyRate ^ (6 * (len j + 1)) ≤
      loss (len j + 1) * ((Fintype.card (β j) : ℝ) ^ 6)) :
    omega K < (2374631 / 1000000 : ℝ) := by
  classical
  have hcount' : ∀ j : ℕ, dwz63TrueCopyRate ^ (6 * (len j + 1)) ≤
      loss (len j + 1) * ((Fintype.card (dwz63SymSixIndex (β j)) : ℝ)) := by
    intro j
    rw [dwz63_card_symSixIndex]
    push_cast
    exact hcount j
  have hcards : ∀ j : ℕ, 0 < Fintype.card (dwz63SymSixIndex (β j)) := by
    intro j
    rcases Nat.eq_zero_or_pos (Fintype.card (dwz63SymSixIndex (β j))) with h0 | hpos
    · exfalso
      have h1 := hcount' j
      rw [h0] at h1
      simp only [Nat.cast_zero, mul_zero] at h1
      exact absurd h1 (not_le.mpr (pow_pos dwz63TrueCopyRate_pos _))
    · exact hpos
  exact omega_lt_2374631_of_dwz63IsolatedSum
    (Iso := fun j ↦ dwz63SymSixIndex (β j))
    (fun j ↦ len j + 1) (fun j _ ↦ symSix K (leaf j)) weight loss hloss
    (fun cutoff ↦ (hcofinal cutoff).imp fun _ hj ↦ ⟨hj, Nat.succ_pos _⟩)
    hstage (fun j _ ↦ hleafWeight j)
    (fun j ↦ lt_of_lt_of_le (pow_pos (Real.exp_pos _) _) (hleafValue j))
    hcards hcount' hleafValue

/-! ## The two §0 obligations, named -/

set_option maxRecDepth 8000 in
set_option maxHeartbeats 1000000 in
/-- **`omega < 2.374631` at the plain partition, with the stage premise unpacked.**

The same endpoint as `omega_lt_2374631_of_plainStageAndLeaf` with `hstage` replaced by the two
premises `dwz63_plainStage_of_uniformLeaf` actually consumes, so that neither is hidden inside a
composite hypothesis:

* `hlegwise` --- legwise injectivity of the retained family.  The hash supplies the `X` half
  (`dwz63_x_injOn_plainJointRetained`) and the engine's `Y` certificate; the `Z` half is the open
  §0 adjudication, because `[DuanWuZhou2022]`'s retained triples deliberately share large
  `Z`-blocks.  It is **not** discharged anywhere in the committed tree: the only
  `IsLegwiseInjective` certificate for a hashed power
  (`MatrixMultiplication/PartitionedPowerHashing.lean`, `legwiseIsolatedPowerAddresses`) is for the
  all-three-leg isolation, while the plain route hashes the `X`/`Y`-only
  `markedXYIsolatedPowerAddresses`.
* `hleaf` --- the hole-repair obligation: every retained constituent restricts onto the common
  uniform leaf.

Both are quantified over `(B, seed)` because the seed is chosen inside the count-side join. -/
theorem omega_lt_2374631_of_plainLegwiseAndLeaf
    {K : Type u} [Field K]
    (len scale : ℕ → ℕ)
    (hlen : ∀ j : ℕ, len j + 1 = 100000000 * scale j)
    (hcofinal : ∀ cutoff : ℕ, ∃ j : ℕ, cutoff ≤ len j + 1)
    -- ELABORATION RISK: `dwz63_plainStage_of_uniformLeaf` binds its leaf spaces at
    -- `Type (max u v)` with `v` the hash field's universe; the Bertrand field is `Type 0`, so the
    -- leaf universe here is pinned to `u`, unlike in the two theorems above.
    {W : ℕ → Leg → Type u} [∀ j c, AddCommMonoid (W j c)] [∀ j c, Module K (W j c)]
    (leaf : ∀ j : ℕ, Tensor3 K (W j))
    (weight : ℕ → ℝ)
    (hlegwise : ∀ (j : ℕ)
        (B : Finset (dwz63SharpHashField (dwz63PlainSharpDegree K (len j) (scale j))))
        (seed : ProgressionHash.Seed
          (dwz63SharpHashField (dwz63PlainSharpDegree K (len j) (scale j)))
          (Fin (len j + 1))),
        ThreeAPFree (B : Set (dwz63SharpHashField
          (dwz63PlainSharpDegree K (len j) (scale j)))) →
        IsLegwiseInjective (dwz63PlainJointRetainedSupport K
          (dwz63_cwSquareFieldValue_sharpHashField_injective
            (dwz63PlainSharpDegree K (len j) (scale j)))
          (len j) (scale j) (dwz63PlainMarginalWords K (len j) (scale j)) B seed))
    (hleaf : ∀ (j : ℕ)
        (B : Finset (dwz63SharpHashField (dwz63PlainSharpDegree K (len j) (scale j))))
        (seed : ProgressionHash.Seed
          (dwz63SharpHashField (dwz63PlainSharpDegree K (len j) (scale j)))
          (Fin (len j + 1))),
        ThreeAPFree (B : Set (dwz63SharpHashField
          (dwz63PlainSharpDegree K (len j) (scale j)))) →
        ∀ a : (dwz63PlainJointRetainedSupport K
          (dwz63_cwSquareFieldValue_sharpHashField_injective
            (dwz63PlainSharpDegree K (len j) (scale j)))
          (len j) (scale j) (dwz63PlainMarginalWords K (len j) (scale j)) B seed),
          Restricts ((dwz63PlainMarginalTypicalPower K (len j) (scale j)).constituent a.1)
            (leaf j))
    (hleafWeight : ∀ j : ℕ, HasTauWeight K (symSix K (leaf j)) dwz63Tau (weight j))
    (hleafValue : ∀ j : ℕ, Real.exp dwz63LogVal ^ (6 * (len j + 1)) ≤ weight j) :
    omega K < (2374631 / 1000000 : ℝ) :=
  omega_lt_2374631_of_plainStageAndLeaf len scale hlen hcofinal leaf weight
    (fun j B seed hB ↦ dwz63_plainStage_of_uniformLeaf K
      (dwz63_cwSquareFieldValue_sharpHashField_injective
        (dwz63PlainSharpDegree K (len j) (scale j)))
      (len j) (scale j) (dwz63PlainMarginalWords K (len j) (scale j))
      (Finset.Subset.refl _) B hB seed (hlegwise j B seed hB) (leaf j) (hleaf j B seed hB))
    hleafWeight hleafValue

end AlgebraicComplexity.Examples
