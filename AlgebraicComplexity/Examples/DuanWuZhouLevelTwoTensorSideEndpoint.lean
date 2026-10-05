/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoCofinalIndex
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoJointHashing

/-!
# The level-two endpoint with the tensor side discharged

Layer 4 (`AlgebraicComplexity/Examples/`).  This module closes the tensor-side lane by composing

* `dwz63_restricts_power_symSix_to_isolatedDirectSum` (joint-hashing lane) --- one restriction of
  `sym_6(T)^{tensor (n+1)}` onto the indexed direct sum of the doubly compatibility-isolated
  retained constituents, with no holes and no batching; and

* `dwzLevelTwoCountingStage_of_weightedRestriction` together with
  `HasTauWeight.indexedDirectSum_of_forall` (this lane) --- weights add over that direct sum, so
  the retained copy count is `Fintype.card` of the isolated support itself.

The result is `omega < 2.374631` from two lane deliverables only: a per-constituent `tau`-weight
(values lane) and a copy-count estimate (counting lane).  No `Q`, no `m`, no `alpha` split, no
`AvailableWord`, no hole family, no batch surjection, no Hole-Lemma budget, and none of the
backwards `hleaf` of the committed section 6 assembly.

## An elaboration hazard, and how it is avoided

Wiring the hashing lane's conclusion straight into
`dwzLevelTwoCountingStage_of_isolatedSum` makes Lean solve for the *block-space family* of a
six-orientation positive power by higher-order unification, and those spaces unfold to a six-fold
`ProductBlockSpace` beneath a `PositivePowerBlockSpace`.  That `whnf` does not terminate within a
million heartbeats.  Going through the decoupled
`dwzLevelTwoCountingStage_of_weightedRestriction`, whose restriction target is opaque and whose
weight is supplied separately, removes the problem entirely: the direct sum is elaborated once, in
term position, and never has to be matched against a metavariable-headed family.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor

universe u v

/-! ## The cofinal index in successor form -/

/-- The cofinal index is a successor, which is the form the hashing lane's word length takes. -/
theorem succ_pred_dwz63CofinalIndex {Mass : ℕ} (hMass : 0 < Mass) (j : ℕ) :
    dwz63CofinalIndex Mass j - 1 + 1 = dwz63CofinalIndex Mass j :=
  Nat.succ_pred_eq_of_pos (dwz63CofinalIndex_pos hMass j)

/-- Cofinality of the index, stated for the hashing lane's `n + 1` word lengths. -/
theorem dwz63CofinalIndex_pred_cofinal {Mass : ℕ} (hMass : 0 < Mass) :
    ∀ cutoff : ℕ, ∃ j : ℕ, cutoff ≤ dwz63CofinalIndex Mass j - 1 + 1 := by
  intro cutoff
  obtain ⟨j, hj, _⟩ := dwz63CofinalIndex_cofinal hMass cutoff
  exact ⟨j, by rw [succ_pred_dwz63CofinalIndex hMass j]; exact hj⟩

/-! ## The endpoint -/

/-- **`omega < 2.374631` with the tensor side discharged.**

Everything tensor-semantic is constructed: the six-orientation partition of the level-two source,
the joint hash, the two compatibility zero-outs, and the additivity of `tau`-weights over the
resulting direct sum.  The surviving hypotheses are exactly the other two lanes' deliverables ---
`hconstituent` (every retained constituent is worth at least `w j`) and `hcount` (the isolated
support is large) --- together with the choice of word lengths.

`compat` is any legwise source compatibility model, and `hcompat` is discharged for all of them by
`Tensor/PartitionedSymmetrizedCompatibility.lean`, so it is never a real obligation. -/
theorem omega_lt_2374631_of_dwz63JointHash
    {R : Type v} [Field R] {p : ℕ} [CharP R p] [NeZero (2 : R)]
    {K : Type u} [Field K] (hp : 15625 ≤ p)
    (len : ℕ → ℕ)
    (markedWords : ∀ j : ℕ,
      Finset (PositiveWord ((dwz63SymSixPartition K).support) (len j)))
    (B : Finset R) (hB : ThreeAPFree (B : Set R))
    (seed : ∀ j : ℕ, ProgressionHash.Seed R (Fin (len j + 1)))
    (compat : ∀ _leg : Leg, Fin 5 → CWSquareAddress → Prop)
    (hcompat : ∀ leg : Leg,
      IsCompatibilitySound (cwSquarePartitionedTensor K dwz63Q).support leg (compat leg))
    (w loss : ℕ → ℝ) (hloss : Growth.Subexponential loss)
    (hcofinal : ∀ cutoff : ℕ, ∃ j : ℕ, cutoff ≤ len j + 1)
    (hconstituent : ∀ (j : ℕ)
        (a : dwz63JointIsolatedSupport K hp (len j) (markedWords j) B (seed j) compat),
      HasTauWeight K
        ((dwz63JointRetained K hp (len j) (markedWords j) B (seed j)).constituent a.1)
        dwz63Tau (w j))
    (hwpos : ∀ j : ℕ, 0 < w j)
    (hcards : ∀ j : ℕ, 0 < Fintype.card
      (dwz63JointIsolatedSupport K hp (len j) (markedWords j) B (seed j) compat))
    (hcount : ∀ j : ℕ, dwz63TrueCopyRate ^ (6 * (len j + 1)) ≤ loss (len j + 1) *
      (Fintype.card
        (dwz63JointIsolatedSupport K hp (len j) (markedWords j) B (seed j) compat) : ℝ))
    (hvalue : ∀ j : ℕ, Real.exp dwz63LogVal ^ (6 * (len j + 1)) ≤ w j) :
    omega K < (2374631 / 1000000 : ℝ) := by
  classical
  have hpos : ∀ j : ℕ, (0 : ℝ) <
      (Fintype.card
        (dwz63JointIsolatedSupport K hp (len j) (markedWords j) B (seed j) compat) : ℝ) := by
    intro j
    exact_mod_cast hcards j
  refine omega_lt_2374631_of_weightedRestriction (fun j ↦ len j + 1)
    (fun j ↦ Tensor.indexedDirectSum
      (fun a : dwz63JointIsolatedSupport K hp (len j) (markedWords j) B (seed j) compat ↦
        (dwz63JointRetained K hp (len j) (markedWords j) B (seed j)).constituent a.1))
    (fun j ↦ (Fintype.card
      (dwz63JointIsolatedSupport K hp (len j) (markedWords j) B (seed j) compat) : ℝ) * w j)
    loss hloss (fun cutoff ↦ (hcofinal cutoff).imp fun _ hj ↦ ⟨hj, Nat.succ_pos _⟩)
    (fun j ↦ dwz63_restricts_power_symSix_to_isolatedDirectSum K hp (len j) (markedWords j)
      B hB (seed j) compat hcompat)
    (fun j ↦ HasTauWeight.indexedDirectSum_of_forall (hconstituent j))
    (fun j ↦ mul_pos (hpos j) (hwpos j))
    (fun j ↦ dwz63_globalRate_le_of_count_value (hcount j) (hvalue j))

end AlgebraicComplexity.Examples
