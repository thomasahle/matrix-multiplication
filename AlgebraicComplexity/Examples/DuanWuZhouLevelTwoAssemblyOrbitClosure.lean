/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoAssemblyRowSix
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoOrbitBetaCanonical
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoGoodBatchSizeGrowth

set_option autoImplicit false

/-!
# Closing the orbit premise of the section 6.3 endpoint

`omega_lt_2374631_of_orbitRowsSevenTen_and_seededPeriod`
(`Examples/DuanWuZhouLevelTwoAssemblyRowSix.lean`) already folds row `6` of the orbit table in
from `dwz63_orbitRowSix_R3`, and carries the other two symmetry-broken components as the binder
`∀ j o, o ≠ 0 → …`.  `dwz63_orbitRowsSevenTen_R3`
(`Examples/DuanWuZhouLevelTwoOrbitBetaCanonical.lean`) discharges exactly that binder, at
`ε = dwz63LeafMargin`, with a cutoff phrased on the period `312500000000000000000 ∣ s`.

This module performs the composition.  The cutoff fold is the same one row `6` uses: from
`max (max N (312500000000000000000 * N₇)) 312500000000000000000 ≤ s j` and the period
divisibility, `Nat.le_div_iff_mul_le` supplies `N₇ ≤ s j / 312500000000000000000` and
`Nat.one_le_div_iff` its positivity, which is what `dwz63_orbitRowsSevenTen_R3` asks for.
Nothing analytic happens here ---
the three orbit rows are the three components of `dwz63OrbitRow = ![6, 7, 10]` on which the
symmetrisation of section 6.3 is broken, and all three are now theorems.

What remains is the single binder `hseededPeriod`: the per-period seed selection, which the
hole-side lane supplies.  `omega_lt_2374631_of_seededPeriod_goodBatchLoss` fixes the batching loss
to `dwz63_subexponential_four_mul_goodBatchSize_pred`, the affine batch count of `cor:hole_lemma`
(`hole_lemma.tex:159-168`), so that the hole lane's statement plugs in with no further glue.

`[duan2023faster]`, `global_value.tex:124-378`.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor

universe u

section

variable (K : Type u) [Field K]

/-- **`omega < 2.374631` from the per-period seed alone.**

`omega_lt_2374631_of_orbitRowsSevenTen_and_seededPeriod` with its `o ≠ 0` premise discharged by
`dwz63_orbitRowsSevenTen_R3`.  The returned `N` folds that theorem's cutoff `N₇` into row 6's
pattern: `max (max N (312500000000000000000 * N₇)) 312500000000000000000`, so that
`N ≤ s j` together with `312500000000000000000 ∣ s j` supplies both the divided cutoff
and its positivity. -/
theorem omega_lt_2374631_of_seededPeriod
    (batchLoss : ℕ → ℝ) (hbatchLoss : Growth.Subexponential batchLoss)
    (hseededPeriod : ∃ N₀ : ℕ, ∀ s : ℕ,
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
            batchLoss (n + 1) * (Fintype.card (Fin batches) : ℝ))
    :
    ∃ N : ℕ, ∀ (len s : ℕ → ℕ),
      (∀ j : ℕ, len j + 1 = 20000000000000000 * s j) →
      (∀ cutoff : ℕ, ∃ j : ℕ, cutoff ≤ len j + 1) →
      (∀ j : ℕ, N ≤ s j) →
      (∀ j : ℕ, 40000000000000 ∣ s j ∧ 312500000000000000000 ∣ s j) →
      omega K < (2374631 / 1000000 : ℝ) := by
  obtain ⟨N₆, h₆⟩ :=
    omega_lt_2374631_of_orbitRowsSevenTen_and_seededPeriod K batchLoss hbatchLoss hseededPeriod
  obtain ⟨N₇, h₇⟩ := dwz63_orbitRowsSevenTen_R3 K (by norm_num) (by norm_num [dwz63Q])
  refine ⟨max (max N₆ (312500000000000000000 * N₇)) 312500000000000000000,
    fun len s hlen hcofinal hs hlat ↦ ?_⟩
  have hs₆ : ∀ j : ℕ, N₆ ≤ s j := fun j ↦
    le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (hs j)
  obtain ⟨wRef, hmu, hmark, hrest⟩ := h₆ len s hlen hcofinal hs₆ hlat
  clear hmu hmark
  refine hrest (fun j o ho m hm ↦ ?_)
  have hbig : 312500000000000000000 * N₇ ≤ s j :=
    le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (hs j)
  have hfloor : 312500000000000000000 ≤ s j := le_trans (le_max_right _ _) (hs j)
  have hdiv : N₇ ≤ s j / 312500000000000000000 :=
    (Nat.le_div_iff_mul_le (by norm_num)).2 (by omega)
  have hposdiv : 0 < s j / 312500000000000000000 :=
    (Nat.one_le_div_iff (by norm_num)).2 hfloor
  exact h₇ (s j) (hlat j).2
    (le_trans hdiv (Nat.le_mul_of_pos_left _ (by norm_num)))
    (Nat.mul_pos (by norm_num) hposdiv) o ho m hm

/-- **The same, with the batching loss fixed to the good-batch count.**

`batchLoss := fun m ↦ 4 * dwz63GoodBatchSize (m - 1)`, discharged by
`dwz63_subexponential_four_mul_goodBatchSize_pred`.  At the stage length `n + 1` this reads
`4 * dwz63GoodBatchSize n`, which is the shape the hole-side lane states `hseededPeriod` in, so
this is the form to instantiate. -/
theorem omega_lt_2374631_of_seededPeriod_goodBatchLoss
    (hseededPeriod : ∃ N₀ : ℕ, ∀ s : ℕ,
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
            ((4 * dwz63GoodBatchSize n : ℕ) : ℝ) * (Fintype.card (Fin batches) : ℝ))
    :
    ∃ N : ℕ, ∀ (len s : ℕ → ℕ),
      (∀ j : ℕ, len j + 1 = 20000000000000000 * s j) →
      (∀ cutoff : ℕ, ∃ j : ℕ, cutoff ≤ len j + 1) →
      (∀ j : ℕ, N ≤ s j) →
      (∀ j : ℕ, 40000000000000 ∣ s j ∧ 312500000000000000000 ∣ s j) →
      omega K < (2374631 / 1000000 : ℝ) := by
  exact omega_lt_2374631_of_seededPeriod K
    (fun m ↦ ((4 * dwz63GoodBatchSize (m - 1) : ℕ) : ℝ))
    dwz63_subexponential_four_mul_goodBatchSize_pred hseededPeriod

end

end AlgebraicComplexity.Examples
