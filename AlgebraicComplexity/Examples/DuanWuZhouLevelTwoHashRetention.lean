/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Analysis.BehrendRate
import AlgebraicComplexity.Combinatorics.PrimeFieldSizing
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoJointHashing

/-!
# Hash retention for the level-two joint hash

Layer 4 (`AlgebraicComplexity/Examples/`).  `Examples/DuanWuZhouLevelTwoJointHashing.lean` produces
the seeded retained family `dwz63JointRetainedSupport` and, in
`exists_seed_dwz63JointRetained`, the good-seed count

`3 · |markedWords| · |B| ≤ 4 · |R|² · |retained|`

with `|R|`, `B` and the fiber degree `d` still free.  This module *fixes* them and turns that
count into an explicit retention bound

`|markedWords| ≤ dwz63RetentionLoss n · |retained|`.

## The three parameters, fixed

* **The degree.**  `[DuanWuZhou2022]`'s modulus condition is `8d ≤ |R|` for `d` a common bound on
  the ambient `X`- and `Y`-leg fibers of a marked target.  A leg fiber is a `Finset.filter` of the
  ambient legal targets, so the crude bound `d = |ambient|` is available with no counting at all:
  `dwz63AmbientDegree n = (15 ^ 6) ^ (n + 1) = 11390625 ^ (n + 1)`, the number of block-word
  addresses of the six-orientation positive power.  **This is deliberately not the sharp bound.**
  Section 6.3's own `d` is `N_triple / N_X`, exponentially smaller, and the whole rate gain lives
  in that ratio; supplying it is the count lane's `ConditionalCompetitorEncoding` work.  Since a
  *larger* `d` is always admissible (`quarter_of_eight_mul_legFiber_le` is monotone in `d`), this
  module is correct as stated and can be re-run at the sharp `d` by changing one definition.

* **The field.**  `dwz63HashModulus n = PrimeFieldSizing.modulus 15625 (8 · dwz63AmbientDegree n)`
  --- Bertrand's postulate applied to the maximum of the characteristic floor `15625` demanded by
  the joint six-orientation encoding (`dwz63SymSixNatEncoding_alphabet`) and the modulus
  requirement `8d`.  Bertrand gives a prime in `[m, 2m]`, so
  `dwz63HashModulus_le` is the explicit upper bound that later cancels one power of the modulus.

* **The progression-free set.**  `exists_threeAPFree_zmod_half`, whose cardinality is exactly
  `rothNumberNat (M / 2)` --- Mathlib's extremal Roth set, cast into `ZMod M`.  Its size is
  Behrend's `M^{1 - o(1)}`; `Growth.le_mul_exp_of_mul_rothNumberNat_le` performs the cancellation.

## The loss, and which half of it is exponential

`dwz63RetentionLoss n = 4 · (2 · (15625 + 8 · 11390625 ^ (n+1) + 1)) · exp (4 √(log (M/2)))`.

It is **not** subexponential, and it must not be: it *is* the hashing modulus, and dividing the
marked count by the modulus is exactly what `AsymmetricGlobal.GlobalRateData.copyRate` does
(`PREP.md` §4.3, steps (1)–(4)).  The factorization `dwz63RetentionLoss = dwz63ModulusLoss ·
dwz63BehrendLoss` separates the two: `dwz63ModulusLoss` carries the rate and is what the count
lane cancels against `N_α`, while `dwz63BehrendLoss n = exp (4 √(log (M/2)))` is the genuinely
subexponential Behrend price, the same factor every other endpoint in this tree absorbs through
`Analysis/Subexponential.lean`.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor
open scoped BigOperators

universe u

/-! ## The ambient degree -/

/-- **The crude ambient leg-fiber degree**: the number of block-word addresses of the
six-orientation positive power at word length `n + 1`. -/
def dwz63AmbientDegree (n : ℕ) : ℕ := 11390625 ^ (n + 1)

theorem dwz63AmbientDegree_pos (n : ℕ) : 0 < dwz63AmbientDegree n := by
  unfold dwz63AmbientDegree
  positivity

/-! ## The field -/

/-- **The hashing modulus**: Bertrand's prime above both the joint encoding's characteristic floor
`15625` and `[DuanWuZhou2022]`'s modulus requirement `8d`. -/
noncomputable def dwz63HashModulus (n : ℕ) : ℕ :=
  PrimeFieldSizing.modulus 15625 (8 * dwz63AmbientDegree n)

instance dwz63HashModulus_fact_prime (n : ℕ) : Fact (Nat.Prime (dwz63HashModulus n)) :=
  ⟨PrimeFieldSizing.modulus_prime _ _⟩

/-- The characteristic floor the joint six-orientation encoding needs. -/
theorem dwz63HashModulus_char_floor (n : ℕ) : 15625 ≤ dwz63HashModulus n :=
  le_of_lt (PrimeFieldSizing.characteristicFloor_lt_modulus _ _)

/-- `[DuanWuZhou2022]`'s modulus condition `8d ≤ |R|`. -/
theorem dwz63HashModulus_requirement (n : ℕ) :
    8 * dwz63AmbientDegree n ≤ dwz63HashModulus n :=
  le_of_lt (PrimeFieldSizing.requirement_lt_modulus _ _)

/-- Bertrand's upper bound, the explicit factor one power of the modulus cancels against. -/
theorem dwz63HashModulus_le (n : ℕ) :
    dwz63HashModulus n ≤ 2 * (15625 + 8 * dwz63AmbientDegree n + 1) :=
  PrimeFieldSizing.modulus_le_two_mul_add _ _

instance dwz63HashModulus_neZero (n : ℕ) : NeZero (dwz63HashModulus n) :=
  ⟨(dwz63HashModulus_fact_prime n).out.ne_zero⟩

/-- **The hashing field.** -/
abbrev dwz63HashField (n : ℕ) : Type := ZMod (dwz63HashModulus n)

instance dwz63HashField_neZero_two (n : ℕ) : NeZero (2 : dwz63HashField n) :=
  neZero_two_zmod_of_three_le (by have := dwz63HashModulus_char_floor n; omega)

@[simp] theorem card_dwz63HashField (n : ℕ) :
    Fintype.card (dwz63HashField n) = dwz63HashModulus n :=
  ZMod.card _

/-! ## The ambient legal-target count and the degree bound -/

/-- The six-orientation positive power has `11390625 ^ (n+1)` block-word addresses. -/
theorem card_positiveWord_dwz63SymSix (K : Type u) [CommRing K] (n : ℕ) :
    Fintype.card (PositiveWord ((dwz63SymSixPartition K).support) n) = dwz63AmbientDegree n := by
  classical
  rw [Fintype.card_congr (positiveWordEquiv ((dwz63SymSixPartition K).support) n),
    Fintype.card_fun, Fintype.card_fin, Fintype.card_coe,
    card_dwz63SymSixPartition_support]
  rfl

/-- The ambient legal-target family is the whole address set. -/
theorem card_legalTargets_univ_dwz63 (K : Type u) [CommRing K] (n : ℕ) :
    ((dwz63SymSixHashEncoding K (dwz63HashField n)
      (dwz63HashModulus_char_floor n)).legalTargets n Finset.univ).card
      = dwz63AmbientDegree n := by
  rw [PartitionHashEncoding.card_legalTargets, Finset.card_univ,
    card_positiveWord_dwz63SymSix]

/-- **The degree bound.**  Every ambient leg fiber is a sub-family of the ambient targets. -/
theorem card_legFiber_le_dwz63AmbientDegree (K : Type u) [CommRing K] (n : ℕ) (c : Leg)
    (triple : ProgressionHash.LegalTriple (dwz63HashField n) (Fin (n + 1))
      (dwz63SymSixHashEncoding K (dwz63HashField n)
        (dwz63HashModulus_char_floor n)).target) :
    (ProgressionHash.LegalTriple.legFiber
      ((dwz63SymSixHashEncoding K (dwz63HashField n)
        (dwz63HashModulus_char_floor n)).legalTargets n Finset.univ) triple c).card
      ≤ dwz63AmbientDegree n := by
  classical
  have hsub : ProgressionHash.LegalTriple.legFiber
      ((dwz63SymSixHashEncoding K (dwz63HashField n)
        (dwz63HashModulus_char_floor n)).legalTargets n Finset.univ) triple c ⊆
      (dwz63SymSixHashEncoding K (dwz63HashField n)
        (dwz63HashModulus_char_floor n)).legalTargets n Finset.univ := by
    intro other hother
    exact ((ProgressionHash.LegalTriple.mem_legFiber _ triple other c).mp hother).1
  exact (Finset.card_le_card hsub).trans_eq (card_legalTargets_univ_dwz63 K n)

/-! ## The retention loss -/

/-- The exponentially large factor: the hashing modulus itself, which is what
`AsymmetricGlobal.GlobalRateData.copyRate` divides by. -/
noncomputable def dwz63ModulusLoss (n : ℕ) : ℝ :=
  4 * (2 * (15625 + 8 * (dwz63AmbientDegree n : ℝ) + 1))

/-- The subexponential factor: Behrend's price for the progression-free set. -/
noncomputable def dwz63BehrendLoss (n : ℕ) : ℝ :=
  Real.exp (4 * Real.sqrt (Real.log ((dwz63HashModulus n / 2 : ℕ) : ℝ)))

/-- **The retention loss.** -/
noncomputable def dwz63RetentionLoss (n : ℕ) : ℝ :=
  dwz63ModulusLoss n * dwz63BehrendLoss n

theorem dwz63RetentionLoss_eq (n : ℕ) :
    dwz63RetentionLoss n = dwz63ModulusLoss n * dwz63BehrendLoss n := rfl

theorem dwz63ModulusLoss_pos (n : ℕ) : 0 < dwz63ModulusLoss n := by
  unfold dwz63ModulusLoss
  have : (0 : ℝ) ≤ (dwz63AmbientDegree n : ℝ) := Nat.cast_nonneg _
  nlinarith

theorem dwz63BehrendLoss_pos (n : ℕ) : 0 < dwz63BehrendLoss n := Real.exp_pos _

/-! ## The retention theorem -/

/-- **Hash retention for the level-two joint hash.**

At the fixed parameters above --- the Bertrand prime `dwz63HashModulus n`, the extremal Roth set
of `ZMod` that modulus, and the crude ambient degree --- one affine seed retains a family whose
cardinality is at least the marked count divided by the explicit loss.

The only hypothesis is on the client's marked family, and there is none: the statement holds for
every `markedWords`, vacuously when it is empty.  The count lane supplies `|markedWords| = N_α`
and divides by `dwz63ModulusLoss`, which is `[DuanWuZhou2022]`'s `4M` up to the Bertrand factor
two; `dwz63BehrendLoss` is absorbed by `Analysis/Subexponential.lean`. -/
theorem dwz63_retained_card_lower (K : Type u) [CommRing K] (n : ℕ)
    (markedWords : Finset (PositiveWord ((dwz63SymSixPartition K).support) n)) :
    ∃ (B : Finset (dwz63HashField n))
      (seed : ProgressionHash.Seed (dwz63HashField n) (Fin (n + 1))),
      ThreeAPFree (B : Set (dwz63HashField n)) ∧
        (markedWords.card : ℝ) ≤ dwz63RetentionLoss n *
          ((dwz63JointRetainedSupport K (dwz63HashModulus_char_floor n) n
            markedWords B seed).card : ℝ) := by
  classical
  obtain ⟨B, hcardB, hfreeB⟩ := exists_threeAPFree_zmod_half (dwz63HashModulus n)
  have hmod : 8 * dwz63AmbientDegree n ≤ Fintype.card (dwz63HashField n) := by
    rw [card_dwz63HashField]
    exact dwz63HashModulus_requirement n
  obtain ⟨seed, hcount⟩ := exists_seed_dwz63JointRetained K (dwz63HashModulus_char_floor n) n
    markedWords B hfreeB (dwz63AmbientDegree n)
    (fun triple _ ↦ card_legFiber_le_dwz63AmbientDegree K n .X triple)
    (fun triple _ ↦ card_legFiber_le_dwz63AmbientDegree K n .Y triple) hmod
  refine ⟨B, seed, hfreeB, ?_⟩
  set retained := (dwz63JointRetainedSupport K (dwz63HashModulus_char_floor n) n
    markedWords B seed).card with hretained
  rw [card_dwz63HashField] at hcount
  -- Real-valued form of the good-seed count, in Behrend-cancellation shape.
  have hreal : (3 * (markedWords.card : ℝ)) * (rothNumberNat (dwz63HashModulus n / 2) : ℝ) ≤
      (4 * (retained : ℝ)) * ((dwz63HashModulus n : ℝ) * (dwz63HashModulus n : ℝ)) := by
    have hnat : 3 * markedWords.card * B.card ≤
        4 * (dwz63HashModulus n * dwz63HashModulus n) * retained := hcount
    have hcast : ((3 * markedWords.card * B.card : ℕ) : ℝ) ≤
        ((4 * (dwz63HashModulus n * dwz63HashModulus n) * retained : ℕ) : ℝ) := by
      exact_mod_cast hnat
    rw [hcardB] at hcast
    push_cast at hcast
    linarith
  have hM : 2 ≤ dwz63HashModulus n := by
    have := dwz63HashModulus_char_floor n; omega
  have hMU : (dwz63HashModulus n : ℝ) ≤ 2 * (15625 + 8 * (dwz63AmbientDegree n : ℝ) + 1) := by
    have := dwz63HashModulus_le n
    have hcast : ((dwz63HashModulus n : ℕ) : ℝ) ≤
        ((2 * (15625 + 8 * dwz63AmbientDegree n + 1) : ℕ) : ℝ) := by exact_mod_cast this
    push_cast at hcast
    linarith
  have hkey := Growth.le_mul_exp_of_mul_rothNumberNat_le (M := dwz63HashModulus n)
    (a := 3 * (markedWords.card : ℝ)) (b := 4 * (retained : ℝ))
    (U := 2 * (15625 + 8 * (dwz63AmbientDegree n : ℝ) + 1))
    (t := 4 * Real.sqrt (Real.log ((dwz63HashModulus n / 2 : ℕ) : ℝ)))
    hM (by positivity) (by positivity) hMU le_rfl hreal
  have hexp : (0 : ℝ) < dwz63BehrendLoss n := dwz63BehrendLoss_pos n
  unfold dwz63RetentionLoss dwz63ModulusLoss dwz63BehrendLoss
  unfold dwz63BehrendLoss at hexp
  nlinarith [hkey, hexp, Nat.cast_nonneg (α := ℝ) retained]

end AlgebraicComplexity.Examples
