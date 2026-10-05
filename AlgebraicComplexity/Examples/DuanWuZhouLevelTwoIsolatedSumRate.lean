/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoGlobalStageRate
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoPlainOpenIntegration

set_option autoImplicit false

/-!
# The isolated-sum and plain `sym₆` stages at an arbitrary leaf-value base

Layer 4 (`AlgebraicComplexity/Examples/`).  `omega_lt_2374631_of_dwz63IsolatedSum`
(`Examples/DuanWuZhouLevelTwoIsolatedBypass.lean`) and `omega_lt_2374631_of_plainSymSixStage`
(`Examples/DuanWuZhouLevelTwoPlainOpenIntegration.lean`) both ask their client for a leaf value at
the base `exp dwz63LogVal`.  A value route with a positive per-letter deficit cannot supply that
(`dwz63_regionProduct_lt_required`, image 109), so this module threads the base as a parameter `v`
and the global rate as `dwz63TrueCopyRate * v`.

The proofs are the committed ones verbatim: `Real.exp dwz63LogVal` is replaced by `v` and
`(pow_pos (Real.exp_pos _) _).le` by `pow_nonneg hv _`.  Both committed statements are recovered as
the instances at `v := Real.exp dwz63LogVal`, where `dwz63TrueCopyRate * v` is
`dwz63TrueGlobalRate` by definition and `hgap` is `dwz63_globalRate_lt_trueGlobalRate`; the
accepted modules are not re-issued.

Primary source: Ran Duan, Hongxun Wu and Renfei Zhou, *Faster Matrix Multiplication via Asymmetric
Hashing*, arXiv:2210.10173, section 6.3.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor

universe u v w y

/-! ## The isolated-sum residual at a shifted base -/

/-- **The count-side residual from isolated whole constituents, at leaf-value base `v`.** -/
theorem dwzLevelTwoCountingStage_of_isolatedSumAt
    {K : Type u} [Field K]
    {Iso : ℕ → Type w} [∀ i, Fintype (Iso i)] [∀ i, DecidableEq (Iso i)]
    {U : ∀ i, Iso i → Leg → Type v}
    [∀ i a c, AddCommMonoid (U i a c)] [∀ i a c, Module K (U i a c)]
    (base : ℝ) (hbase : 0 ≤ base)
    (index : ℕ → ℕ) (retained : ∀ i, ∀ a : Iso i, Tensor3 K (U i a))
    (w loss : ℕ → ℝ)
    (hloss : Growth.Subexponential loss)
    (hcofinal : ∀ cutoff : ℕ, ∃ i : ℕ, cutoff ≤ index i ∧ 0 < index i)
    (hsum : ∀ i : ℕ, Restricts (Tensor.power (symSix K (dwz63Source K)) (index i))
      (Tensor.indexedDirectSum fun a : Iso i ↦ retained i a))
    (hconstituent : ∀ (i : ℕ) (a : Iso i), HasTauWeight K (retained i a) dwz63Tau (w i))
    (hwpos : ∀ i : ℕ, 0 < w i)
    (hcards : ∀ i : ℕ, 0 < Fintype.card (Iso i))
    (hcount : ∀ i : ℕ,
      dwz63TrueCopyRate ^ (6 * index i) ≤ loss (index i) * (Fintype.card (Iso i) : ℝ))
    (hvalue : ∀ i : ℕ, base ^ (6 * index i) ≤ w i) :
    DwzLevelTwoCountingStageAt (dwz63TrueCopyRate * base) (dwz63Source K) := by
  refine ⟨loss, hloss, fun cutoff ↦ ?_⟩
  obtain ⟨i, hi, hpos⟩ := hcofinal cutoff
  have hcardPos : (0 : ℝ) < (Fintype.card (Iso i) : ℝ) := by exact_mod_cast hcards i
  refine ⟨index i, hi, hpos, (Fintype.card (Iso i) : ℝ) * w i,
    mul_pos hcardPos (hwpos i), ?_, ?_⟩
  · exact HasTauWeight.of_restricts (hsum i)
      (HasTauWeight.indexedDirectSum_of_forall (hconstituent i))
  · have hexpand : (dwz63TrueCopyRate * base) ^ (6 * index i) =
        dwz63TrueCopyRate ^ (6 * index i) * base ^ (6 * index i) := by
      rw [mul_pow]
    rw [hexpand]
    calc dwz63TrueCopyRate ^ (6 * index i) * base ^ (6 * index i)
        ≤ loss (index i) * (Fintype.card (Iso i) : ℝ) * w i :=
          mul_le_mul (hcount i) (hvalue i) (pow_nonneg hbase _)
            ((pow_pos dwz63TrueCopyRate_pos _).le.trans (hcount i))
      _ = loss (index i) * ((Fintype.card (Iso i) : ℝ) * w i) := by ring

/-- **`omega < 2.374631` from isolated whole constituents at leaf-value base `base`.** -/
theorem omega_lt_2374631_of_dwz63IsolatedSumAt
    {K : Type u} [Field K]
    {Iso : ℕ → Type w} [∀ i, Fintype (Iso i)] [∀ i, DecidableEq (Iso i)]
    {U : ∀ i, Iso i → Leg → Type v}
    [∀ i a c, AddCommMonoid (U i a c)] [∀ i a c, Module K (U i a c)]
    (base : ℝ) (hbase : 0 ≤ base)
    (hgap : (dwz63RateData 1 one_pos).globalRate < dwz63TrueCopyRate * base)
    (index : ℕ → ℕ) (retained : ∀ i, ∀ a : Iso i, Tensor3 K (U i a))
    (w loss : ℕ → ℝ)
    (hloss : Growth.Subexponential loss)
    (hcofinal : ∀ cutoff : ℕ, ∃ i : ℕ, cutoff ≤ index i ∧ 0 < index i)
    (hsum : ∀ i : ℕ, Restricts (Tensor.power (symSix K (dwz63Source K)) (index i))
      (Tensor.indexedDirectSum fun a : Iso i ↦ retained i a))
    (hconstituent : ∀ (i : ℕ) (a : Iso i), HasTauWeight K (retained i a) dwz63Tau (w i))
    (hwpos : ∀ i : ℕ, 0 < w i)
    (hcards : ∀ i : ℕ, 0 < Fintype.card (Iso i))
    (hcount : ∀ i : ℕ,
      dwz63TrueCopyRate ^ (6 * index i) ≤ loss (index i) * (Fintype.card (Iso i) : ℝ))
    (hvalue : ∀ i : ℕ, base ^ (6 * index i) ≤ w i) :
    omega K < (2374631 / 1000000 : ℝ) :=
  omega_lt_2374631_of_dwz63CountingStageAt hgap
    (dwzLevelTwoCountingStage_of_isolatedSumAt base hbase index retained w loss hloss hcofinal
      hsum hconstituent hwpos hcards hcount hvalue)

/-! ## The plain `sym₆` stage at a shifted base -/

/-- **`omega < 2.374631` from a plain `sym₆` stage whose leaf value is at base `base`.**  The
committed `omega_lt_2374631_of_plainSymSixStage` with `Real.exp dwz63LogVal` replaced by `base`. -/
theorem omega_lt_2374631_of_plainSymSixStageAt
    {K : Type u} [Field K]
    (base : ℝ) (hbase : 0 ≤ base)
    (hgap : (dwz63RateData 1 one_pos).globalRate < dwz63TrueCopyRate * base)
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
    (hleafValue : ∀ j : ℕ, base ^ (6 * (len j + 1)) ≤ weight j)
    (hweightPos : ∀ j : ℕ, 0 < weight j)
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
  exact omega_lt_2374631_of_dwz63IsolatedSumAt base hbase hgap
    (Iso := fun j ↦ dwz63SymSixIndex (β j))
    (fun j ↦ len j + 1) (fun j _ ↦ symSix K (leaf j)) weight loss hloss
    (fun cutoff ↦ (hcofinal cutoff).imp fun _ hj ↦ ⟨hj, Nat.succ_pos _⟩)
    hstage (fun j _ ↦ hleafWeight j) hweightPos hcards hcount' hleafValue

/-! ## The committed statements, recovered -/

/-- The gap hypothesis at the true rate, in the shape the parameterised theorems ask for. -/
theorem dwz63_globalRate_lt_copyRate_mul_expLogVal :
    (dwz63RateData 1 one_pos).globalRate < dwz63TrueCopyRate * Real.exp dwz63LogVal :=
  dwz63_globalRate_lt_trueGlobalRate 1 one_pos

end AlgebraicComplexity.Examples
