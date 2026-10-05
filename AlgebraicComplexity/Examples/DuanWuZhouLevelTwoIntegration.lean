/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoCofinalIndex
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoCopyCount
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoHashRetention
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoOrientationTypical

/-!
# Integration: `omega < 2.374631` from the still-open estimates only

Layer 4 (`AlgebraicComplexity/Examples/`).  Everything the four lanes have landed is instantiated
here, so that what remains is visible as a short, named list of hypotheses.

## What is consumed, and therefore no longer a hypothesis

* the six-orientation partition of the level-two source and its stage bridge
  (`Tensor/PartitionedSymmetrization.lean`);
* the joint hash and the two compatibility zero-outs
  (`dwz63_restricts_power_symSix_to_isolatedDirectSum`), with `hsoundY` / `hsoundZ` discharged for
  every legwise model by `Tensor/PartitionedSymmetrizedCompatibility.lean`;
* additivity of `tau`-weights over the isolated direct sum
  (`HasTauWeight.indexedDirectSum_of_forall`), so the copy count is `Fintype.card` of the isolated
  support and no hole repair occurs anywhere;
* the compatibility cleanup loss `2` (`card_dwz63JointRetainedSupport_le_two_mul_card_jointIsolated`);
* the copy-count assembly `dwz63_copyCount_fintype_of_estimates`, and with it
  `hcards` --- positivity of the copy count is *free* from the count itself
  (`fintype_card_dwz63JointIsolatedSupport_pos`);
* the marked family: `dwz63TypicalWords`, whose length identity
  (`dwz63OrientationTypical_length`) matches the cofinal index exactly;
* the cofinal index, its `10 ^ 8` divisibility, and the subexponentiality of the assembled loss.

`hvalue` is discharged by *choosing* the leaf weight to be the endpoint's own target
`exp dwz63LogVal ^ (6 (n + 1))`; it then holds by reflexivity, which is why it does not appear
below.

## The remaining hypotheses

1. `compat`, `hcompat` and the two incidence budgets with `2 (budgetY + budgetZ) <= |retained|`;
2. the hashing seed data `B`, `seed`, `hB` together with `hseed` and `hmarked` --- the count
   lane's residual estimate;
3. `hconstituent` --- the values lane's per-constituent weight on typical words.

Nothing else.  When those three land, `omega_lt_2374631_of_dwz63LevelTwo` is one `exact` away.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor

universe u

noncomputable section

/-! ## The index family -/

/-- The hashing lane's word length at index `j`: the cofinal index, less one. -/
def dwz63IntegrationLength (Mass j : ℕ) : ℕ := dwz63CofinalIndex Mass j - 1

/-- The stage length is the cofinal index, so both divisibility constraints hold at it. -/
theorem dwz63IntegrationLength_succ {Mass : ℕ} (hMass : 0 < Mass) (j : ℕ) :
    dwz63IntegrationLength Mass j + 1 = dwz63CofinalIndex Mass j :=
  Nat.succ_pred_eq_of_pos (dwz63CofinalIndex_pos hMass j)

/-- In the scale form the orientation-typical family uses. -/
theorem dwz63IntegrationLength_succ_scale {Mass : ℕ} (hMass : 0 < Mass) (j : ℕ) :
    dwz63IntegrationLength Mass j + 1 = 100000000 * (Mass * (j + 1)) := by
  rw [dwz63IntegrationLength_succ hMass]
  unfold dwz63CofinalIndex
  ring

/-- The stage lengths are unbounded. -/
theorem dwz63IntegrationLength_cofinal {Mass : ℕ} (hMass : 0 < Mass) :
    ∀ cutoff : ℕ, ∃ j : ℕ, cutoff ≤ dwz63IntegrationLength Mass j + 1 := by
  intro cutoff
  obtain ⟨j, hj, _⟩ := dwz63CofinalIndex_cofinal hMass cutoff
  exact ⟨j, by rw [dwz63IntegrationLength_succ hMass j]; exact hj⟩

/-- The marked family at index `j`: the `dwz63Alpha`-typical words at the matching scale. -/
def dwz63IntegrationMarked (K : Type u) [CommRing K] (Mass j : ℕ) :
    Finset (PositiveWord ((dwz63SymSixPartition K).support) (dwz63IntegrationLength Mass j)) :=
  dwz63TypicalWords K (dwz63IntegrationLength Mass j) (Mass * (j + 1))

/-! ## The integration -/

/-- **`omega < 2.374631` from the still-open estimates only.**

Every green input is instantiated; the hypotheses below are exactly the three residual
obligations.  In particular `hcards` and `hvalue` do not appear: the first is free from the copy
count, and the second holds by reflexivity at the chosen leaf weight. -/
theorem omega_lt_2374631_of_openEstimates
    {K : Type u} [Field K] {Mass : ℕ} (hMass : 0 < Mass)
    (compat : ∀ _leg : Leg, Fin 5 → CWSquareAddress → Prop)
    (hcompat : ∀ leg : Leg,
      IsCompatibilitySound (cwSquarePartitionedTensor K dwz63Q).support leg (compat leg))
    (B : ∀ j : ℕ, Finset (dwz63HashField (dwz63IntegrationLength Mass j)))
    (seed : ∀ j : ℕ, ProgressionHash.Seed (dwz63HashField (dwz63IntegrationLength Mass j))
      (Fin (dwz63IntegrationLength Mass j + 1)))
    (hB : ∀ j : ℕ, ThreeAPFree ((B j : Set (dwz63HashField (dwz63IntegrationLength Mass j)))))
    (budgetY budgetZ : ℕ → ℕ)
    (hbudgetY : ∀ j : ℕ, compatibilityCompetitorIncidence
      (dwz63JointRetainedSupport K (dwz63HashModulus_char_floor (dwz63IntegrationLength Mass j))
        (dwz63IntegrationLength Mass j) (dwz63IntegrationMarked K Mass j) (B j) (seed j)) .Y
      (symSixPowerCompatible (A := fun _ : Leg ↦ Fin 5) compat .Y
        (dwz63IntegrationLength Mass j)) ≤ budgetY j)
    (hbudgetZ : ∀ j : ℕ, compatibilityCompetitorIncidence
      (dwz63JointRetainedSupport K (dwz63HashModulus_char_floor (dwz63IntegrationLength Mass j))
        (dwz63IntegrationLength Mass j) (dwz63IntegrationMarked K Mass j) (B j) (seed j)) .Z
      (symSixPowerCompatible (A := fun _ : Leg ↦ Fin 5) compat .Z
        (dwz63IntegrationLength Mass j)) ≤ budgetZ j)
    (hhalf : ∀ j : ℕ, 2 * (budgetY j + budgetZ j) ≤
      (dwz63JointRetainedSupport K (dwz63HashModulus_char_floor (dwz63IntegrationLength Mass j))
        (dwz63IntegrationLength Mass j) (dwz63IntegrationMarked K Mass j) (B j) (seed j)).card)
    (lossHash : ℕ → ℝ) (hlossHashSub : Growth.Subexponential lossHash)
    (hlossHash : ∀ N : ℕ, 0 ≤ lossHash N)
    (hseed : ∀ j : ℕ,
      3 * (dwz63IntegrationMarked K Mass j).card * (B j).card ≤
        4 * (Fintype.card (dwz63HashField (dwz63IntegrationLength Mass j)) *
          Fintype.card (dwz63HashField (dwz63IntegrationLength Mass j))) *
          (dwz63JointRetainedSupport K
            (dwz63HashModulus_char_floor (dwz63IntegrationLength Mass j))
            (dwz63IntegrationLength Mass j) (dwz63IntegrationMarked K Mass j)
            (B j) (seed j)).card)
    (hmarked : ∀ j : ℕ,
      dwz63HashingBranch ^ (6 * (dwz63IntegrationLength Mass j + 1)) *
          (4 * ((Fintype.card (dwz63HashField (dwz63IntegrationLength Mass j)) : ℝ) *
            (Fintype.card (dwz63HashField (dwz63IntegrationLength Mass j)) : ℝ))) ≤
        lossHash (dwz63IntegrationLength Mass j + 1) *
          (3 * ((dwz63IntegrationMarked K Mass j).card : ℝ) * ((B j).card : ℝ)))
    (hconstituent : ∀ (j : ℕ)
        (a : dwz63JointIsolatedSupport K
          (dwz63HashModulus_char_floor (dwz63IntegrationLength Mass j))
          (dwz63IntegrationLength Mass j) (dwz63IntegrationMarked K Mass j)
          (B j) (seed j) compat),
      HasTauWeight K
        ((dwz63JointRetained K (dwz63HashModulus_char_floor (dwz63IntegrationLength Mass j))
          (dwz63IntegrationLength Mass j) (dwz63IntegrationMarked K Mass j)
          (B j) (seed j)).constituent a.1) dwz63Tau
        (Real.exp dwz63LogVal ^ (6 * (dwz63IntegrationLength Mass j + 1)))) :
    omega K < (2374631 / 1000000 : ℝ) := by
  classical
  set len : ℕ → ℕ := fun j ↦ dwz63IntegrationLength Mass j with hlen
  -- the compatibility cleanup loss is `2`, from the committed incidence bound
  have hclean : ∀ j : ℕ,
      ((dwz63JointRetainedSupport K (dwz63HashModulus_char_floor (len j)) (len j)
        (dwz63IntegrationMarked K Mass j) (B j) (seed j)).card : ℝ) ≤
        2 * ((dwz63JointIsolatedSupport K (dwz63HashModulus_char_floor (len j)) (len j)
          (dwz63IntegrationMarked K Mass j) (B j) (seed j) compat).card : ℝ) := by
    intro j
    have hnat := card_dwz63JointRetainedSupport_le_two_mul_card_jointIsolated K
      (dwz63HashModulus_char_floor (len j)) (len j) (dwz63IntegrationMarked K Mass j)
      (B j) (seed j) compat (budgetY j) (budgetZ j) (hbudgetY j) (hbudgetZ j) (hhalf j)
    exact_mod_cast hnat
  -- the copy count, and with it positivity of the copy count
  have hcount : ∀ j : ℕ, dwz63TrueCopyRate ^ (6 * (len j + 1)) ≤
      dwz63CopyCountLoss 2 lossHash (len j + 1) *
        (Fintype.card (dwz63JointIsolatedSupport K (dwz63HashModulus_char_floor (len j)) (len j)
          (dwz63IntegrationMarked K Mass j) (B j) (seed j) compat) : ℝ) := by
    intro j
    exact dwz63_copyCount_fintype_of_estimates K (dwz63HashModulus_char_floor (len j)) (len j)
      (dwz63IntegrationMarked K Mass j) (B j) (seed j) compat 2 lossHash (hlossHash _)
      (hseed j) (hmarked j) (hclean j)
  have hcards : ∀ j : ℕ, 0 < Fintype.card
      (dwz63JointIsolatedSupport K (dwz63HashModulus_char_floor (len j)) (len j)
        (dwz63IntegrationMarked K Mass j) (B j) (seed j) compat) := fun j ↦
    fintype_card_dwz63JointIsolatedSupport_pos K (dwz63HashModulus_char_floor (len j)) (len j)
      (dwz63IntegrationMarked K Mass j) (B j) (seed j) compat (hcount j)
  have hcardsReal : ∀ j : ℕ, (0 : ℝ) < (Fintype.card
      (dwz63JointIsolatedSupport K (dwz63HashModulus_char_floor (len j)) (len j)
        (dwz63IntegrationMarked K Mass j) (B j) (seed j) compat) : ℝ) := by
    intro j
    exact_mod_cast hcards j
  refine omega_lt_2374631_of_weightedRestriction (fun j ↦ len j + 1)
    (fun j ↦ Tensor.indexedDirectSum
      (fun a : dwz63JointIsolatedSupport K (dwz63HashModulus_char_floor (len j)) (len j)
        (dwz63IntegrationMarked K Mass j) (B j) (seed j) compat ↦
        (dwz63JointRetained K (dwz63HashModulus_char_floor (len j)) (len j)
          (dwz63IntegrationMarked K Mass j) (B j) (seed j)).constituent a.1))
    (fun j ↦ (Fintype.card
      (dwz63JointIsolatedSupport K (dwz63HashModulus_char_floor (len j)) (len j)
        (dwz63IntegrationMarked K Mass j) (B j) (seed j) compat) : ℝ) *
      Real.exp dwz63LogVal ^ (6 * (len j + 1)))
    (dwz63CopyCountLoss 2 lossHash)
    (subexponential_dwz63CopyCountLoss (by norm_num) hlossHashSub)
    (fun cutoff ↦ (dwz63IntegrationLength_cofinal hMass cutoff).imp
      fun _ hj ↦ ⟨hj, Nat.succ_pos _⟩)
    (fun j ↦ dwz63_restricts_power_symSix_to_isolatedDirectSum K
      (dwz63HashModulus_char_floor (len j)) (len j) (dwz63IntegrationMarked K Mass j)
      (B j) (hB j) (seed j) compat hcompat)
    (fun j ↦ HasTauWeight.indexedDirectSum_of_forall (hconstituent j))
    (fun j ↦ mul_pos (hcardsReal j) (pow_pos (Real.exp_pos _) _))
    (fun j ↦ dwz63_globalRate_le_of_count_value (hcount j) (le_refl _))

end

end AlgebraicComplexity.Examples
