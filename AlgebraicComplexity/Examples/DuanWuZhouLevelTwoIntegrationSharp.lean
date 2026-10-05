/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoCopyCountRetention
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoIntegration
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoSharpDegree

/-!
# Integration at the sharp degree: the hashing seed is no longer a hypothesis

Layer 4 (`AlgebraicComplexity/Examples/`).  `Examples/DuanWuZhouLevelTwoIntegration.lean` had to
carry the hashing seed data `B`, `seed`, `hB` as hypotheses, because the crude-degree retention
lemma's output shape did not compose with the copy-count assembly.
`Examples/DuanWuZhouLevelTwoCopyCountRetention.lean` closes that seam, and
`dwz63_retained_card_lower_sharp` supplies the seed *existentially* at any certified leg-fiber
degree.  So here the seed is chosen internally and disappears from the interface.

## What replaces it

`hsharp` --- the certified degree bound, which is the method-of-types statement the counting lane
owns --- and `hrate`, the marked-count estimate in the form the retention loss demands:

`dwz63HashingBranch ^ (6 (n + 1)) * dwz63SharpRetentionLoss (degree j) <= lossHash * |marked|`.

Dividing by the (positive) retention loss and composing with
`|marked| <= dwz63SharpRetentionLoss (degree j) * |retained|` gives exactly the `hretention`
hypothesis of `dwz63_copyCount_fintype_of_retention`.  The intended instantiation is
`degree j = dwz63SharpDegree (jointCount j) (xCount j)`, at which `hrate` is the exponential
content of `Dwz63SharpRateStatement`; `degree` is left a parameter so that any certified degree
may be used.

## One honest cost of consuming the existential

The seed is produced inside the proof, so a hypothesis that mentions the retained support cannot
name it.  The three such hypotheses --- the two incidence budgets, the half-budget condition and
the per-constituent weight --- are therefore quantified over every `B` and `seed` with `B`
progression-free.  That is a genuine strengthening relative to
`Examples/DuanWuZhouLevelTwoIntegration.lean`, where the seed was an explicit parameter.  It is
harmless in substance for `hconstituent`, since `withSupport` does not change constituents and the
weight of a constituent depends on the seed only through which addresses are supported; for the
budgets it asks the compatibility model to bound the incidence uniformly in the seed, which is how
an ambient competitor count is naturally stated.  A client that would rather fix the seed should
use the unsharp integration instead.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor

universe u

noncomputable section

/-- **`omega < 2.374631` at the sharp degree, from the still-open estimates only.**

Hypotheses: the compatibility group (`compat`, `hcompat`, the two budgets and the half condition),
the certified degree `hsharp`, the marked-count rate `hrate`, and the values lane's
`hconstituent`.  The hashing seed, the copy count, `hcards`, `hvalue`, cofinality, divisibility and
the whole leaf/hole apparatus are discharged. -/
theorem omega_lt_2374631_of_openEstimatesSharp
    {K : Type u} [Field K] {Mass : ℕ} (hMass : 0 < Mass) (degree : ℕ → ℕ)
    (compat : ∀ _leg : Leg, Fin 5 → CWSquareAddress → Prop)
    (hcompat : ∀ leg : Leg,
      IsCompatibilitySound (cwSquarePartitionedTensor K dwz63Q).support leg (compat leg))
    (budgetY budgetZ : ℕ → ℕ)
    (hbudgetY : ∀ (j : ℕ) (B : Finset (dwz63SharpHashField (degree j)))
        (seed : ProgressionHash.Seed (dwz63SharpHashField (degree j))
          (Fin (dwz63IntegrationLength Mass j + 1))),
        ThreeAPFree (B : Set (dwz63SharpHashField (degree j))) →
        compatibilityCompetitorIncidence
          (dwz63JointRetainedSupport K (dwz63SharpHashModulus_char_floor (degree j))
            (dwz63IntegrationLength Mass j) (dwz63IntegrationMarked K Mass j) B seed) .Y
          (symSixPowerCompatible (A := fun _ : Leg ↦ Fin 5) compat .Y
            (dwz63IntegrationLength Mass j)) ≤ budgetY j)
    (hbudgetZ : ∀ (j : ℕ) (B : Finset (dwz63SharpHashField (degree j)))
        (seed : ProgressionHash.Seed (dwz63SharpHashField (degree j))
          (Fin (dwz63IntegrationLength Mass j + 1))),
        ThreeAPFree (B : Set (dwz63SharpHashField (degree j))) →
        compatibilityCompetitorIncidence
          (dwz63JointRetainedSupport K (dwz63SharpHashModulus_char_floor (degree j))
            (dwz63IntegrationLength Mass j) (dwz63IntegrationMarked K Mass j) B seed) .Z
          (symSixPowerCompatible (A := fun _ : Leg ↦ Fin 5) compat .Z
            (dwz63IntegrationLength Mass j)) ≤ budgetZ j)
    (hhalf : ∀ (j : ℕ) (B : Finset (dwz63SharpHashField (degree j)))
        (seed : ProgressionHash.Seed (dwz63SharpHashField (degree j))
          (Fin (dwz63IntegrationLength Mass j + 1))),
        ThreeAPFree (B : Set (dwz63SharpHashField (degree j))) →
        2 * (budgetY j + budgetZ j) ≤
          (dwz63JointRetainedSupport K (dwz63SharpHashModulus_char_floor (degree j))
            (dwz63IntegrationLength Mass j) (dwz63IntegrationMarked K Mass j) B seed).card)
    (lossHash : ℕ → ℝ) (hlossHashSub : Growth.Subexponential lossHash)
    (hlossHash : ∀ N : ℕ, 0 ≤ lossHash N)
    (hsharp : ∀ (j : ℕ) (c : Leg),
      ∀ triple ∈ (dwz63SymSixHashEncoding K (dwz63SharpHashField (degree j))
        (dwz63SharpHashModulus_char_floor (degree j))).legalTargets
          (dwz63IntegrationLength Mass j) (dwz63IntegrationMarked K Mass j),
        (ProgressionHash.LegalTriple.legFiber
          ((dwz63SymSixHashEncoding K (dwz63SharpHashField (degree j))
            (dwz63SharpHashModulus_char_floor (degree j))).legalTargets
              (dwz63IntegrationLength Mass j) Finset.univ)
          triple c).card ≤ degree j)
    (hrate : ∀ j : ℕ,
      dwz63HashingBranch ^ (6 * (dwz63IntegrationLength Mass j + 1)) *
          dwz63SharpRetentionLoss (degree j) ≤
        lossHash (dwz63IntegrationLength Mass j + 1) *
          ((dwz63IntegrationMarked K Mass j).card : ℝ))
    (hconstituent : ∀ (j : ℕ) (B : Finset (dwz63SharpHashField (degree j)))
        (seed : ProgressionHash.Seed (dwz63SharpHashField (degree j))
          (Fin (dwz63IntegrationLength Mass j + 1))),
        ThreeAPFree (B : Set (dwz63SharpHashField (degree j))) →
        ∀ a : dwz63JointIsolatedSupport K
          (dwz63SharpHashModulus_char_floor (degree j)) (dwz63IntegrationLength Mass j)
          (dwz63IntegrationMarked K Mass j) B seed compat,
        HasTauWeight K
          ((dwz63JointRetained K (dwz63SharpHashModulus_char_floor (degree j))
            (dwz63IntegrationLength Mass j) (dwz63IntegrationMarked K Mass j)
            B seed).constituent a.1) dwz63Tau
          (Real.exp dwz63LogVal ^ (6 * (dwz63IntegrationLength Mass j + 1)))) :
    omega K < (2374631 / 1000000 : ℝ) := by
  classical
  choose B seed hB hret using fun j : ℕ ↦
    dwz63_retained_card_lower_sharp K (dwz63IntegrationLength Mass j) (degree j)
      (dwz63IntegrationMarked K Mass j) (hsharp j)
  set len : ℕ → ℕ := fun j ↦ dwz63IntegrationLength Mass j with hlen
  have hlossPos : ∀ d : ℕ, (0 : ℝ) < dwz63SharpRetentionLoss d := by
    intro d
    unfold dwz63SharpRetentionLoss
    exact mul_pos (dwz63SharpModulusLoss_pos d) (dwz63SharpBehrendLoss_pos d)
  -- the retention bound in the shape the copy-count assembly consumes
  have hretention : ∀ j : ℕ, dwz63HashingBranch ^ (6 * (len j + 1)) ≤
      lossHash (len j + 1) *
        ((dwz63JointRetainedSupport K (dwz63SharpHashModulus_char_floor (degree j)) (len j)
          (dwz63IntegrationMarked K Mass j) (B j) (seed j)).card : ℝ) := by
    intro j
    refine le_of_mul_le_mul_right ?_ (hlossPos (degree j))
    calc dwz63HashingBranch ^ (6 * (len j + 1)) * dwz63SharpRetentionLoss (degree j)
        ≤ lossHash (len j + 1) * ((dwz63IntegrationMarked K Mass j).card : ℝ) := hrate j
      _ ≤ lossHash (len j + 1) * (dwz63SharpRetentionLoss (degree j) *
            ((dwz63JointRetainedSupport K (dwz63SharpHashModulus_char_floor (degree j)) (len j)
              (dwz63IntegrationMarked K Mass j) (B j) (seed j)).card : ℝ)) :=
          mul_le_mul_of_nonneg_left (hret j) (hlossHash _)
      _ = lossHash (len j + 1) *
            ((dwz63JointRetainedSupport K (dwz63SharpHashModulus_char_floor (degree j)) (len j)
              (dwz63IntegrationMarked K Mass j) (B j) (seed j)).card : ℝ) *
            dwz63SharpRetentionLoss (degree j) := by ring
  -- the compatibility cleanup loss is `2`
  have hclean : ∀ j : ℕ,
      ((dwz63JointRetainedSupport K (dwz63SharpHashModulus_char_floor (degree j)) (len j)
        (dwz63IntegrationMarked K Mass j) (B j) (seed j)).card : ℝ) ≤
        2 * ((dwz63JointIsolatedSupport K (dwz63SharpHashModulus_char_floor (degree j)) (len j)
          (dwz63IntegrationMarked K Mass j) (B j) (seed j) compat).card : ℝ) := by
    intro j
    have hnat := card_dwz63JointRetainedSupport_le_two_mul_card_jointIsolated K
      (dwz63SharpHashModulus_char_floor (degree j)) (len j) (dwz63IntegrationMarked K Mass j)
      (B j) (seed j) compat (budgetY j) (budgetZ j)
      (hbudgetY j (B j) (seed j) (hB j)) (hbudgetZ j (B j) (seed j) (hB j))
      (hhalf j (B j) (seed j) (hB j))
    exact_mod_cast hnat
  have hcount : ∀ j : ℕ, dwz63TrueCopyRate ^ (6 * (len j + 1)) ≤
      dwz63CopyCountLoss 2 lossHash (len j + 1) *
        (Fintype.card (dwz63JointIsolatedSupport K
          (dwz63SharpHashModulus_char_floor (degree j)) (len j)
          (dwz63IntegrationMarked K Mass j) (B j) (seed j) compat) : ℝ) := fun j ↦
    dwz63_copyCount_fintype_of_retention K (dwz63SharpHashModulus_char_floor (degree j)) (len j)
      (dwz63IntegrationMarked K Mass j) (B j) (seed j) compat 2 lossHash (hlossHash _)
      (hretention j) (hclean j)
  have hcardsReal : ∀ j : ℕ, (0 : ℝ) < (Fintype.card
      (dwz63JointIsolatedSupport K (dwz63SharpHashModulus_char_floor (degree j)) (len j)
        (dwz63IntegrationMarked K Mass j) (B j) (seed j) compat) : ℝ) := by
    intro j
    have := fintype_card_dwz63JointIsolatedSupport_pos K
      (dwz63SharpHashModulus_char_floor (degree j)) (len j)
      (dwz63IntegrationMarked K Mass j) (B j) (seed j) compat (hcount j)
    exact_mod_cast this
  refine omega_lt_2374631_of_weightedRestriction (fun j ↦ len j + 1)
    (fun j ↦ Tensor.indexedDirectSum
      (fun a : dwz63JointIsolatedSupport K (dwz63SharpHashModulus_char_floor (degree j)) (len j)
        (dwz63IntegrationMarked K Mass j) (B j) (seed j) compat ↦
        (dwz63JointRetained K (dwz63SharpHashModulus_char_floor (degree j)) (len j)
          (dwz63IntegrationMarked K Mass j) (B j) (seed j)).constituent a.1))
    (fun j ↦ (Fintype.card
      (dwz63JointIsolatedSupport K (dwz63SharpHashModulus_char_floor (degree j)) (len j)
        (dwz63IntegrationMarked K Mass j) (B j) (seed j) compat) : ℝ) *
      Real.exp dwz63LogVal ^ (6 * (len j + 1)))
    (dwz63CopyCountLoss 2 lossHash)
    (subexponential_dwz63CopyCountLoss (by norm_num) hlossHashSub)
    (fun cutoff ↦ (dwz63IntegrationLength_cofinal hMass cutoff).imp
      fun _ hj ↦ ⟨hj, Nat.succ_pos _⟩)
    (fun j ↦ dwz63_restricts_power_symSix_to_isolatedDirectSum K
      (dwz63SharpHashModulus_char_floor (degree j)) (len j) (dwz63IntegrationMarked K Mass j)
      (B j) (hB j) (seed j) compat hcompat)
    (fun j ↦ HasTauWeight.indexedDirectSum_of_forall (hconstituent j (B j) (seed j) (hB j)))
    (fun j ↦ mul_pos (hcardsReal j) (pow_pos (Real.exp_pos _) _))
    (fun j ↦ dwz63_globalRate_le_of_count_value (hcount j) (le_refl _))

end

end AlgebraicComplexity.Examples
