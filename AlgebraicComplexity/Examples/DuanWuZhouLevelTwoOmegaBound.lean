/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoAssemblyOrbitClosure
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoSeededPeriod

set_option autoImplicit false

/-!
# The section 6.3 bound

`omega_lt_2374631_of_seededPeriod_goodBatchLoss`
(`Examples/DuanWuZhouLevelTwoAssemblyOrbitClosure.lean`) returns a cutoff `N` and then asks for a
family of stage lengths satisfying four side conditions: the period equation
`len j + 1 = 20000000000000000 * s j`, cofinality of the lengths, `N ≤ s j`, and the two period
divisibilities `40000000000000 ∣ s j` and `312500000000000000000 ∣ s j`.

This module supplies that family explicitly.  The two periods are coprime to nothing in
particular --- they simply have to hold at once, so the family runs along their product
`dwz63PeriodScale = 40000000000000 * 312500000000000000000`, shifted past the cutoff:

  `dwz63PeriodSeq N j = dwz63PeriodScale * (N + j + 1)`,
  `dwz63PeriodLen N j = 20000000000000000 * dwz63PeriodSeq N j - 1`.

All four side conditions are then theorems, not a probe: the period equation is the truncated
subtraction undone by `dwz63_periodSeq_pos`, cofinality holds at `j := cutoff` because the scale
is at least `1`, `N ≤ dwz63PeriodSeq N j` for the same reason, and both divisibilities are read
off the factorisation of `dwz63PeriodScale`.

DWZ state the bound as `omega < 2.374631` at `papers/sources/2210.10173/global_value.tex:352`;
the level-two example that produces it is section 6.3, `global_value.tex:332-378`.

Scope, stated plainly: this is DWZ's **second-power** bound, the one obtained from the
*squared* Coppersmith--Winograd tensor in section 6.3.  It is **not** the paper's headline
figure, which comes from the higher-power analysis of the same method, and nothing in this
development claims that stronger bound.

`[duan2023faster]`, `global_value.tex:352`.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor

universe u

/-- The product of the two periods the seeded endpoint requires. -/
def dwz63PeriodScale : ℕ := 12500000000000000000000000000000000

/-- The scale is exactly the product of the two periods the endpoint requires. -/
theorem dwz63PeriodScale_eq :
    dwz63PeriodScale = 40000000000000 * 312500000000000000000 := by
  norm_num [dwz63PeriodScale]

/-- The period family: a multiple of both periods, shifted past the endpoint's cutoff `N`. -/
def dwz63PeriodSeq (N j : ℕ) : ℕ := dwz63PeriodScale * (N + j + 1)

/-- The stage length attached to `dwz63PeriodSeq`. -/
def dwz63PeriodLen (N j : ℕ) : ℕ := 20000000000000000 * dwz63PeriodSeq N j - 1

/-- The family is positive, which is what undoes the truncated subtraction in
`dwz63PeriodLen`. -/
theorem dwz63_periodSeq_pos (N j : ℕ) : 0 < dwz63PeriodSeq N j :=
  Nat.mul_pos (by norm_num [dwz63PeriodScale]) (by omega)

/-- The period equation: truncated subtraction is undone because the family is positive. -/
theorem dwz63_periodLen_succ (N j : ℕ) :
    dwz63PeriodLen N j + 1 = 20000000000000000 * dwz63PeriodSeq N j := by
  have h := dwz63_periodSeq_pos N j
  unfold dwz63PeriodLen
  omega

/-- The family clears the endpoint's cutoff `N`, because the scale is at least `1` and the
family is shifted by `N + j + 1`. -/
theorem dwz63_le_periodSeq (N j : ℕ) : N ≤ dwz63PeriodSeq N j := by
  refine le_trans (by omega : N ≤ N + j + 1) ?_
  exact Nat.le_mul_of_pos_left _ (by norm_num [dwz63PeriodScale])

/-- Cofinality, witnessed at `j := cutoff`. -/
theorem dwz63_periodSeq_cofinal (N cutoff : ℕ) :
    cutoff ≤ dwz63PeriodLen N cutoff + 1 := by
  rw [dwz63_periodLen_succ]
  refine le_trans (le_trans (by omega : cutoff ≤ N + cutoff + 1) ?_)
    (Nat.le_mul_of_pos_left _ (by norm_num))
  exact Nat.le_mul_of_pos_left _ (by norm_num [dwz63PeriodScale])

/-- Both period divisibilities, read off the factorisation of `dwz63PeriodScale`. -/
theorem dwz63_periodSeq_dvd (N j : ℕ) :
    40000000000000 ∣ dwz63PeriodSeq N j ∧ 312500000000000000000 ∣ dwz63PeriodSeq N j := by
  constructor
  · exact ⟨312500000000000000000 * (N + j + 1), by
      unfold dwz63PeriodSeq dwz63PeriodScale; ring⟩
  · exact ⟨40000000000000 * (N + j + 1), by
      unfold dwz63PeriodSeq dwz63PeriodScale; ring⟩

section

variable (K : Type u) [Field K]

/-- **The section 6.3 bound, modulo the per-period seed.**

`omega_lt_2374631_of_seededPeriod_goodBatchLoss` at the explicit period family
`dwz63PeriodSeq` / `dwz63PeriodLen`, whose four side conditions are the theorems above. -/
theorem omega_lt_2374631_of_seededPeriod_applied
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
    omega K < (2374631 / 1000000 : ℝ) := by
  obtain ⟨N, hN⟩ := omega_lt_2374631_of_seededPeriod_goodBatchLoss K hseededPeriod
  exact hN (dwz63PeriodLen N) (dwz63PeriodSeq N) (dwz63_periodLen_succ N)
    (fun cutoff ↦ ⟨cutoff, dwz63_periodSeq_cofinal N cutoff⟩)
    (dwz63_le_periodSeq N) (dwz63_periodSeq_dvd N)

end

/-- **`omega < 2.374631`.**

The section 6.3 bound with every hypothesis discharged: `omega_lt_2374631_of_seededPeriod_applied`
at the explicit period family, with the per-period seed supplied by `dwz63_exists_seededPeriod`.
That supplier asks only for `[CommRing K]`, which the `[Field K]` here provides.

This is the **second-power** bound of section 6.3 (`global_value.tex:352`), from the squared
Coppersmith--Winograd tensor --- not the paper's headline figure. -/
theorem omega_lt_2374631 (K : Type u) [Field K] : omega K < (2374631 / 1000000 : ℝ) :=
  omega_lt_2374631_of_seededPeriod_applied K (dwz63_exists_seededPeriod K)

end AlgebraicComplexity.Examples
