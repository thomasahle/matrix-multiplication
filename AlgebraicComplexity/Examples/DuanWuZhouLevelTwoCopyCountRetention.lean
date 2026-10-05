/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoCopyCount

/-!
# The copy count from a retention bound

Layer 4 (`AlgebraicComplexity/Examples/`).  `Examples/DuanWuZhouLevelTwoCopyCount.lean` assembles
the copy count from `hseed` (a `Nat` inequality on the good-seed count) and `hmarked` (the marked
rate), deriving the intermediate

`dwz63HashingBranch ^ (6 (n + 1)) <= lossHash (n + 1) * |retained|`

internally via `dwz63_hashingBranch_pow_le_card_jointRetained`.  The hash-retention lemmas of the
joint-hashing lane instead *produce* a retention bound directly, with the Behrend and modulus
factors already absorbed, so the two factorizations do not compose.

This module restates the copy-count assembly with that intermediate promoted to a hypothesis.
Nothing is proved that `Examples/DuanWuZhouLevelTwoCopyCount.lean` does not already prove: the
calculation below is its final `calc` block verbatim, with the `have hretained := ...` line
replaced by the parameter `hretention`.  The `Fintype R` instance disappears with it, since it was
used only inside the promoted step.

Once the count lane exposes this variant itself, this module should be deleted and its clients
repointed.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor

universe u v

variable {R : Type v} [Field R] {p : ℕ} [CharP R p]

/-- **The copy count from a retention bound.**

`hretention` is the conclusion of `dwz63_hashingBranch_pow_le_card_jointRetained`, taken as a
hypothesis so that a hash-retention lemma which already absorbed the Behrend and modulus factors
can supply it directly. -/
theorem dwz63_copyCount_of_retention
    (K : Type u) [CommRing K] (hp : 15625 ≤ p) (n : ℕ)
    (markedWords : Finset (PositiveWord ((dwz63SymSixPartition K).support) n))
    (B : Finset R) (seed : ProgressionHash.Seed R (Fin (n + 1)))
    (compat : ∀ _leg : Leg, Fin 5 → CWSquareAddress → Prop)
    (lossCompat : ℝ) (lossHash : ℕ → ℝ) (hlossHash : 0 ≤ lossHash (n + 1))
    (hretention : dwz63HashingBranch ^ (6 * (n + 1)) ≤
      lossHash (n + 1) *
        ((dwz63JointRetainedSupport K hp n markedWords B seed).card : ℝ))
    (hclean : ((dwz63JointRetainedSupport K hp n markedWords B seed).card : ℝ) ≤
      lossCompat * ((dwz63JointIsolatedSupport K hp n markedWords B seed compat).card : ℝ)) :
    dwz63TrueCopyRate ^ (6 * (n + 1)) ≤
      dwz63CopyCountLoss lossCompat lossHash (n + 1) *
        ((dwz63JointIsolatedSupport K hp n markedWords B seed compat).card : ℝ) := by
  calc dwz63TrueCopyRate ^ (6 * (n + 1))
      ≤ dwz63HashingBranch ^ (6 * (n + 1)) := dwz63TrueCopyRate_pow_le_hashingBranch_pow _
    _ ≤ lossHash (n + 1) *
          ((dwz63JointRetainedSupport K hp n markedWords B seed).card : ℝ) := hretention
    _ ≤ lossHash (n + 1) *
          (lossCompat *
            ((dwz63JointIsolatedSupport K hp n markedWords B seed compat).card : ℝ)) :=
        mul_le_mul_of_nonneg_left hclean hlossHash
    _ = dwz63CopyCountLoss lossCompat lossHash (n + 1) *
          ((dwz63JointIsolatedSupport K hp n markedWords B seed compat).card : ℝ) := by
        unfold dwz63CopyCountLoss
        ring

/-- The `Fintype.card` form, which is what the stage family consumes. -/
theorem dwz63_copyCount_fintype_of_retention
    (K : Type u) [CommRing K] (hp : 15625 ≤ p) (n : ℕ)
    (markedWords : Finset (PositiveWord ((dwz63SymSixPartition K).support) n))
    (B : Finset R) (seed : ProgressionHash.Seed R (Fin (n + 1)))
    (compat : ∀ _leg : Leg, Fin 5 → CWSquareAddress → Prop)
    (lossCompat : ℝ) (lossHash : ℕ → ℝ) (hlossHash : 0 ≤ lossHash (n + 1))
    (hretention : dwz63HashingBranch ^ (6 * (n + 1)) ≤
      lossHash (n + 1) *
        ((dwz63JointRetainedSupport K hp n markedWords B seed).card : ℝ))
    (hclean : ((dwz63JointRetainedSupport K hp n markedWords B seed).card : ℝ) ≤
      lossCompat * ((dwz63JointIsolatedSupport K hp n markedWords B seed compat).card : ℝ)) :
    dwz63TrueCopyRate ^ (6 * (n + 1)) ≤
      dwz63CopyCountLoss lossCompat lossHash (n + 1) *
        (Fintype.card (dwz63JointIsolatedSupport K hp n markedWords B seed compat) : ℝ) := by
  have h := dwz63_copyCount_of_retention K hp n markedWords B seed compat lossCompat lossHash
    hlossHash hretention hclean
  rwa [Fintype.card_coe]

end AlgebraicComplexity.Examples
