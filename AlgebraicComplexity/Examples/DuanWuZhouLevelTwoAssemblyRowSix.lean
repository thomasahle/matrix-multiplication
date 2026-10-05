/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoAssemblyMarkedSeededLoss
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoOrbitRowSixCanonical

set_option autoImplicit false

/-!
# The section 6.3 endpoint with orbit row 6 discharged, at a per-period seed

Layer 4 (`AlgebraicComplexity/Examples/`).  `[duan2023faster]`'s §6.2 assembly
(`papers/sources/2210.10173/global_value.tex:270-305`) at §6.3's level-two parameters
(`:332-378`).  This module discharges the orbit premise at `o = 0` --- the component `(1,1,2)`,
the first of the three whose Z-marginal split distribution the paper breaks the symmetry of
(`:334`, the `b` of `table:result-2nd`) --- from `dwz63_orbitRowSix_R3`.

## Why the seed hypothesis is per-period

`omega_lt_2374631_of_referenceLeafWeight_marked_seeded_loss` binds `hseeded` *inside* its own
`∃ N`, i.e. at a cutoff already chosen.  The hole side cannot meet that: its seed selection is
itself cofinal, so it can only offer a statement of the form "there is an `N₀` such that every
admissible period beyond it carries a good seed".  `hseededPeriod` below is exactly that shape ---
the same shape image 152 uses for the orbit rows --- quantified *outside* the `∃ N`, with `N₀`
folded into `N` by `max`, as row 6's cutoff already is.

`scale` is no longer a binder: it is `fun j ↦ 200000000 * s j`, so the period equations hold by
`rfl` and by one `ring`, and the per-period hypothesis and the telescope speak the same spelling of
`dwz63PlainSharpDegree K (len j) (200000000 * s j)` with no dependent rewrite between them.

What remains: orbit rows 7 and 10 (`o ≠ 0`, the 112 successor lane) and `hseededPeriod` (the hole
lane).
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor

universe u

noncomputable section

/-- **`omega < 2.374631` from orbit rows 7 and 10 and a per-period seed.**

Proof sketch: `dwz63_orbitRowSix_R3` and the seeded telescope each return a cutoff, and
`hseededPeriod` a third; `N` is their `max` together with `40000000000000`, so that `N ≤ s j`
supplies all three at once (`Nat.le_div_iff_mul_le` and `Nat.one_le_div_iff` for row 6's
`N₆ ≤ 20088623 · (s j / 4 · 10 ^ 13)` and its positivity).  The orbit premise is
then assembled by `by_cases o = 0`: row 6 from image 152, the other two from the carried
binder. -/
theorem omega_lt_2374631_of_orbitRowsSevenTen_and_seededPeriod (K : Type u) [Field K]
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
      ∃ wRef : ∀ j : ℕ, PositiveWord ((cwSquarePartitionedTensor K dwz63Q).support) (len j),
        (∀ (j : ℕ) (t : Fin 15),
          WordType.multiplicity (dwz63Seg K (len j) (wRef j)) t
            = 200000000 * (dwz63Alpha t * s j)) ∧
        (∀ j : ℕ, wRef j ∈
          dwz63MarkedWords (len j)
            (WordType.proportionalCounts dwz63Alpha (200000000 * s j))) ∧
        (-- rows 7 and 10 (`o ≠ 0`): the 112 successor lane's increment 6.
         (∀ (j : ℕ) (o : Fin 3), o ≠ 0 → ∀ m : ℕ,
            m + 1 = 200000000 * (dwz63Alpha (dwz63OrbitRow o) * s j) →
            HasTauWeight K (symThree K (dwz63OrbitRegion K dwz63Q o (dwz63OrbitRow o) m
              (dwz63Alpha (dwz63OrbitRow o) * s j)).realize) dwz63Tau
              (Real.exp ((200000000 : ℝ) * ((dwz63Alpha (dwz63OrbitRow o) * s j : ℕ) : ℝ)
                * (dwz63OrbitLogVal o - dwz63LeafMargin)) ^ 3)) →
           omega K < (2374631 / 1000000 : ℝ)) := by
  obtain ⟨N135, h135⟩ := omega_lt_2374631_of_referenceLeafWeight_marked_seeded_loss K
  obtain ⟨N6, h6⟩ := dwz63_orbitRowSix_R3 K (by norm_num) (by norm_num [dwz63Q])
  obtain ⟨N0, h0⟩ := hseededPeriod
  refine ⟨max (max (max N135 N0) (40000000000000 * N6)) 40000000000000,
    fun len s hlen hcofinal hs hlat ↦ ?_⟩
  have hs135 : ∀ j : ℕ, N135 ≤ s j := fun j ↦
    le_trans (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_left _ _)) (hs j)
  have hs0 : ∀ j : ℕ, N0 ≤ s j := fun j ↦
    le_trans (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_left _ _)) (hs j)
  have hlen' : ∀ j : ℕ, len j + 1 = 100000000 * (200000000 * s j) := by
    intro j; rw [hlen j]; ring
  obtain ⟨wRef, hmu, hmark, hrest⟩ :=
    h135 len (fun j ↦ 200000000 * s j) s (fun _ ↦ rfl) hlen' hcofinal hs135 hlat
  refine ⟨wRef, hmu, hmark, fun hrows ↦ ?_⟩
  refine hrest ?_ batchLoss hbatchLoss
    (fun j ↦ h0 (s j) (hlat j).1 (hlat j).2 (hs0 j) (len j) (wRef j) (hlen j) (hmu j) (hmark j))
  intro j o m hm
  by_cases ho : o = 0
  · subst ho
    have hbig : 40000000000000 * N6 ≤ s j :=
      le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (hs j)
    have hfloor : 40000000000000 ≤ s j := le_trans (le_max_right _ _) (hs j)
    have hdiv : N6 ≤ s j / 40000000000000 :=
      (Nat.le_div_iff_mul_le (by norm_num)).2 (by omega)
    have hposdiv : 0 < s j / 40000000000000 :=
      (Nat.one_le_div_iff (by norm_num)).2 hfloor
    exact h6 (s j) (hlat j).1
      (le_trans hdiv (Nat.le_mul_of_pos_left _ (by norm_num)))
      (Nat.mul_pos (by norm_num) hposdiv) m hm
  · exact hrows j o ho m hm

end

end AlgebraicComplexity.Examples
