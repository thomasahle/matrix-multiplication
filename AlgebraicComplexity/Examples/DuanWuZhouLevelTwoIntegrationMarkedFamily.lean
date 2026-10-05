/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoIntegrationSharp

/-!
# Integration at the sharp degree, for an arbitrary marked family

Layer 4 (`AlgebraicComplexity/Examples/`).  `Examples/DuanWuZhouLevelTwoIntegrationSharp.lean`
hard-wires the marked family to `dwz63TypicalWords`, the *source*-coordinate typical words.  The
typicality convention is changing to *target* coordinates, and the assembly's orbit bookkeeping
changes with it.  Neither change touches the wiring: inspecting the proof, the marked family is
passed opaquely to `dwz63_retained_card_lower_sharp`,
`card_dwz63JointRetainedSupport_le_two_mul_card_jointIsolated`,
`dwz63_copyCount_fintype_of_retention` and
`dwz63_restricts_power_symSix_to_isolatedDirectSum`, none of which knows anything about it.
**Typicality enters only through `hsharp`, `hrate` and `hconstituent`, all three of which are
hypotheses stated against whatever family is supplied.**

So this module takes the family as a parameter.  The source-coordinate instance is
`omega_lt_2374631_of_openEstimatesSharp`; the target-coordinate instance will be the same theorem
applied to `dwz63TargetTypicalWords`, a one-line corollary once
`Examples/DuanWuZhouLevelTwoTargetTypical.lean` lands.  No further convention change can reach
this file.

## What the flip does and does not touch here

* The word length is unchanged: both conventions use the `10 ^ 8 * t` form, which is exactly
  `dwz63IntegrationLength_succ_scale`, so the cofinal index and its divisibility survive verbatim.
* `Mass` is a parameter, so requiring it to be a multiple of the `(1,2,1)` orbit mass alone --- the
  `(1,1,2)` mass being no longer needed under one certificate class --- is a client's choice and
  costs no change here.
* The per-cell counts of `Examples/DuanWuZhouLevelTwoCofinalIndex.lean` and
  `Examples/DuanWuZhouLevelTwoOrbitCounting.lean` are source-coordinate quantities and are
  orbit-symmetrised under the flip.  Nothing in this module or in
  `Examples/DuanWuZhouLevelTwoIntegrationSharp.lean` depends on them: neither imports
  `DuanWuZhouLevelTwoOrbitCounting`, and `dwz63BTripleCount` / `dwz63BetaTripleCount` are used
  nowhere in the wiring.  They remain frozen and correct as source-coordinate statements.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor

universe u

noncomputable section

/-- **`omega < 2.374631` at the sharp degree, for an arbitrary marked family.**

Hypotheses: the compatibility group (`compat`, `hcompat`, the two budgets and the half condition),
the certified degree `hsharp`, the marked-count rate `hrate`, and the values lane's
`hconstituent`.  The hashing seed, the copy count, `hcards`, `hvalue`, cofinality, divisibility and
the whole leaf/hole apparatus are discharged. -/
theorem omega_lt_2374631_of_openEstimatesMarked
    {K : Type u} [Field K] {Mass : ℕ} (hMass : 0 < Mass) (degree : ℕ → ℕ)
    (marked : ∀ j : ℕ,
      Finset (PositiveWord ((dwz63SymSixPartition K).support) (dwz63IntegrationLength Mass j)))
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
            (dwz63IntegrationLength Mass j) (marked j) B seed) .Y
          (symSixPowerCompatible (A := fun _ : Leg ↦ Fin 5) compat .Y
            (dwz63IntegrationLength Mass j)) ≤ budgetY j)
    (hbudgetZ : ∀ (j : ℕ) (B : Finset (dwz63SharpHashField (degree j)))
        (seed : ProgressionHash.Seed (dwz63SharpHashField (degree j))
          (Fin (dwz63IntegrationLength Mass j + 1))),
        ThreeAPFree (B : Set (dwz63SharpHashField (degree j))) →
        compatibilityCompetitorIncidence
          (dwz63JointRetainedSupport K (dwz63SharpHashModulus_char_floor (degree j))
            (dwz63IntegrationLength Mass j) (marked j) B seed) .Z
          (symSixPowerCompatible (A := fun _ : Leg ↦ Fin 5) compat .Z
            (dwz63IntegrationLength Mass j)) ≤ budgetZ j)
    (hhalf : ∀ (j : ℕ) (B : Finset (dwz63SharpHashField (degree j)))
        (seed : ProgressionHash.Seed (dwz63SharpHashField (degree j))
          (Fin (dwz63IntegrationLength Mass j + 1))),
        ThreeAPFree (B : Set (dwz63SharpHashField (degree j))) →
        2 * (budgetY j + budgetZ j) ≤
          (dwz63JointRetainedSupport K (dwz63SharpHashModulus_char_floor (degree j))
            (dwz63IntegrationLength Mass j) (marked j) B seed).card)
    (lossHash : ℕ → ℝ) (hlossHashSub : Growth.Subexponential lossHash)
    (hlossHash : ∀ N : ℕ, 0 ≤ lossHash N)
    (hsharp : ∀ (j : ℕ) (c : Leg),
      ∀ triple ∈ (dwz63SymSixHashEncoding K (dwz63SharpHashField (degree j))
        (dwz63SharpHashModulus_char_floor (degree j))).legalTargets
          (dwz63IntegrationLength Mass j) (marked j),
        (ProgressionHash.LegalTriple.legFiber
          ((dwz63SymSixHashEncoding K (dwz63SharpHashField (degree j))
            (dwz63SharpHashModulus_char_floor (degree j))).legalTargets
              (dwz63IntegrationLength Mass j) Finset.univ)
          triple c).card ≤ degree j)
    (hrate : ∀ j : ℕ,
      dwz63HashingBranch ^ (6 * (dwz63IntegrationLength Mass j + 1)) *
          dwz63SharpRetentionLoss (degree j) ≤
        lossHash (dwz63IntegrationLength Mass j + 1) *
          ((marked j).card : ℝ))
    (hconstituent : ∀ (j : ℕ) (B : Finset (dwz63SharpHashField (degree j)))
        (seed : ProgressionHash.Seed (dwz63SharpHashField (degree j))
          (Fin (dwz63IntegrationLength Mass j + 1))),
        ThreeAPFree (B : Set (dwz63SharpHashField (degree j))) →
        ∀ a : dwz63JointIsolatedSupport K
          (dwz63SharpHashModulus_char_floor (degree j)) (dwz63IntegrationLength Mass j)
          (marked j) B seed compat,
        HasTauWeight K
          ((dwz63JointRetained K (dwz63SharpHashModulus_char_floor (degree j))
            (dwz63IntegrationLength Mass j) (marked j)
            B seed).constituent a.1) dwz63Tau
          (Real.exp dwz63LogVal ^ (6 * (dwz63IntegrationLength Mass j + 1)))) :
    omega K < (2374631 / 1000000 : ℝ) := by
  classical
  choose B seed hB hret using fun j : ℕ ↦
    dwz63_retained_card_lower_sharp K (dwz63IntegrationLength Mass j) (degree j)
      (marked j) (hsharp j)
  have hlossPos : ∀ d : ℕ, (0 : ℝ) < dwz63SharpRetentionLoss d := by
    intro d
    unfold dwz63SharpRetentionLoss
    exact mul_pos (dwz63SharpModulusLoss_pos d) (dwz63SharpBehrendLoss_pos d)
  -- the retention bound in the shape the copy-count assembly consumes
  have hretention : ∀ j : ℕ, dwz63HashingBranch ^ (6 * (dwz63IntegrationLength Mass j + 1)) ≤
      lossHash (dwz63IntegrationLength Mass j + 1) *
        ((dwz63JointRetainedSupport K (dwz63SharpHashModulus_char_floor (degree j)) (dwz63IntegrationLength Mass j)
          (marked j) (B j) (seed j)).card : ℝ) := by
    intro j
    refine le_of_mul_le_mul_right ?_ (hlossPos (degree j))
    calc dwz63HashingBranch ^ (6 * (dwz63IntegrationLength Mass j + 1)) * dwz63SharpRetentionLoss (degree j)
        ≤ lossHash (dwz63IntegrationLength Mass j + 1) * ((marked j).card : ℝ) := hrate j
      _ ≤ lossHash (dwz63IntegrationLength Mass j + 1) * (dwz63SharpRetentionLoss (degree j) *
            ((dwz63JointRetainedSupport K (dwz63SharpHashModulus_char_floor (degree j)) (dwz63IntegrationLength Mass j)
              (marked j) (B j) (seed j)).card : ℝ)) :=
          mul_le_mul_of_nonneg_left (hret j) (hlossHash _)
      _ = lossHash (dwz63IntegrationLength Mass j + 1) *
            ((dwz63JointRetainedSupport K (dwz63SharpHashModulus_char_floor (degree j)) (dwz63IntegrationLength Mass j)
              (marked j) (B j) (seed j)).card : ℝ) *
            dwz63SharpRetentionLoss (degree j) := by ring
  -- the compatibility cleanup loss is `2`
  have hclean : ∀ j : ℕ,
      ((dwz63JointRetainedSupport K (dwz63SharpHashModulus_char_floor (degree j)) (dwz63IntegrationLength Mass j)
        (marked j) (B j) (seed j)).card : ℝ) ≤
        2 * ((dwz63JointIsolatedSupport K (dwz63SharpHashModulus_char_floor (degree j)) (dwz63IntegrationLength Mass j)
          (marked j) (B j) (seed j) compat).card : ℝ) := by
    intro j
    have hnat := card_dwz63JointRetainedSupport_le_two_mul_card_jointIsolated K
      (dwz63SharpHashModulus_char_floor (degree j)) (dwz63IntegrationLength Mass j) (marked j)
      (B j) (seed j) compat (budgetY j) (budgetZ j)
      (hbudgetY j (B j) (seed j) (hB j)) (hbudgetZ j (B j) (seed j) (hB j))
      (hhalf j (B j) (seed j) (hB j))
    exact_mod_cast hnat
  have hcount : ∀ j : ℕ, dwz63TrueCopyRate ^ (6 * (dwz63IntegrationLength Mass j + 1)) ≤
      dwz63CopyCountLoss 2 lossHash (dwz63IntegrationLength Mass j + 1) *
        (Fintype.card (dwz63JointIsolatedSupport K
          (dwz63SharpHashModulus_char_floor (degree j)) (dwz63IntegrationLength Mass j)
          (marked j) (B j) (seed j) compat) : ℝ) := fun j ↦
    dwz63_copyCount_fintype_of_retention K (dwz63SharpHashModulus_char_floor (degree j)) (dwz63IntegrationLength Mass j)
      (marked j) (B j) (seed j) compat 2 lossHash (hlossHash _)
      (hretention j) (hclean j)
  have hcardsReal : ∀ j : ℕ, (0 : ℝ) < (Fintype.card
      (dwz63JointIsolatedSupport K (dwz63SharpHashModulus_char_floor (degree j)) (dwz63IntegrationLength Mass j)
        (marked j) (B j) (seed j) compat) : ℝ) := by
    intro j
    have := fintype_card_dwz63JointIsolatedSupport_pos K
      (dwz63SharpHashModulus_char_floor (degree j)) (dwz63IntegrationLength Mass j)
      (marked j) (B j) (seed j) compat (hcount j)
    exact_mod_cast this
  refine omega_lt_2374631_of_weightedRestriction (fun j ↦ dwz63IntegrationLength Mass j + 1)
    (fun j ↦ Tensor.indexedDirectSum
      (fun a : dwz63JointIsolatedSupport K (dwz63SharpHashModulus_char_floor (degree j)) (dwz63IntegrationLength Mass j)
        (marked j) (B j) (seed j) compat ↦
        (dwz63JointRetained K (dwz63SharpHashModulus_char_floor (degree j)) (dwz63IntegrationLength Mass j)
          (marked j) (B j) (seed j)).constituent a.1))
    (fun j ↦ (Fintype.card
      (dwz63JointIsolatedSupport K (dwz63SharpHashModulus_char_floor (degree j)) (dwz63IntegrationLength Mass j)
        (marked j) (B j) (seed j) compat) : ℝ) *
      Real.exp dwz63LogVal ^ (6 * (dwz63IntegrationLength Mass j + 1)))
    (dwz63CopyCountLoss 2 lossHash)
    (subexponential_dwz63CopyCountLoss (by norm_num) hlossHashSub)
    (fun cutoff ↦ (dwz63IntegrationLength_cofinal hMass cutoff).imp
      fun _ hj ↦ ⟨hj, Nat.succ_pos _⟩)
    (fun j ↦ dwz63_restricts_power_symSix_to_isolatedDirectSum K
      (dwz63SharpHashModulus_char_floor (degree j)) (dwz63IntegrationLength Mass j) (marked j)
      (B j) (hB j) (seed j) compat hcompat)
    (fun j ↦ HasTauWeight.indexedDirectSum_of_forall (hconstituent j (B j) (seed j) (hB j)))
    (fun j ↦ mul_pos (hcardsReal j) (pow_pos (Real.exp_pos _) _))
    (fun j ↦ dwz63_globalRate_le_of_count_value (hcount j) (le_refl _))

end

end AlgebraicComplexity.Examples
