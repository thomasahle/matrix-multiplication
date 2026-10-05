/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoCounting
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoIsolatedBypass
import AlgebraicComplexity.MatrixMultiplication.SymSixPowerWeight

/-!
# The cofinal index of the level-two stage family, and its divisibility

Layer 4 (`AlgebraicComplexity/Examples/`).  Two independent divisibility constraints pin the word
lengths at which a level-two stage can exist, and neither is optional.

* **The distribution.** A stage of length `n` is a word of `n` six-orientation letters.  A
  *diagonal* letter is the full `S_3` orbit of one coarse address, so it contributes six oriented
  coarse letters at the *same* cell: if `m i` positions carry cell `i` then the oriented
  multiplicity of `i` is `6 * m i` and the total is `6 n`.  Typicality asks
  `m i = dwz63Alpha i * (n / 10 ^ 8)`, so what is required is `10 ^ 8 | n` --- strictly stronger
  than `10 ^ 8 | 6 n`, which is what a careless count gives.
* **The orbit certificates.** A values lane supplies a component weight on a *power*
  `Tensor.power (sym_3 X) (Mass * k)`, so the letters carrying that component must be groupable
  into blocks of `Mass` --- the orbit's group mass, `8 * 10 ^ 21` for the `(1,1,2)` orbit.  Hence
  `Mass | 6 n` as well.

`dwz63CofinalIndex Mass j = 10 ^ 8 * Mass * (j + 1)` satisfies both, and the lemmas below state
each divisibility explicitly rather than leaving it implicit in a choice of index.  Because
`DwzLevelTwoCountingStage` asks only for arbitrarily large lengths, restricting to this arithmetic
progression costs nothing: `dwz63CofinalIndex_cofinal` supplies the cofinality hypothesis of
`dwzLevelTwoCountingStage_of_isolatedSum` directly.

For several orbits with different masses, instantiate `Mass` at any common multiple of them; the
statements are uniform in `Mass`.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor
open scoped BigOperators

universe u v w

/-- **The level-two cofinal index** at orbit group mass `Mass`:
`n = 10 ^ 8 * Mass * (j + 1)`. -/
def dwz63CofinalIndex (Mass j : ℕ) : ℕ := 100000000 * Mass * (j + 1)

/-- The index is positive whenever the orbit mass is. -/
theorem dwz63CofinalIndex_pos {Mass : ℕ} (hMass : 0 < Mass) (j : ℕ) :
    0 < dwz63CofinalIndex Mass j := by
  unfold dwz63CofinalIndex
  positivity

/-- **The index is cofinal.**  This is exactly the hypothesis
`dwzLevelTwoCountingStage_of_isolatedSum` needs, so restricting the stage family to this
progression is free. -/
theorem dwz63CofinalIndex_cofinal {Mass : ℕ} (hMass : 0 < Mass) :
    ∀ cutoff : ℕ, ∃ j : ℕ, cutoff ≤ dwz63CofinalIndex Mass j ∧ 0 < dwz63CofinalIndex Mass j := by
  intro cutoff
  refine ⟨cutoff, ?_, dwz63CofinalIndex_pos hMass cutoff⟩
  unfold dwz63CofinalIndex
  calc cutoff ≤ cutoff + 1 := Nat.le_succ cutoff
    _ ≤ 100000000 * Mass * (cutoff + 1) :=
        Nat.le_mul_of_pos_left _ (by positivity)

/-- **The oriented coarse letter count at the cofinal index**, displayed as the `dwz63Alpha` mass
times the scale: `6 n = 10 ^ 8 * (3 * Mass * (j + 1))`.  So the realized `dwz63Alpha` scale is
`3 * Mass * (j + 1)`. -/
theorem six_mul_dwz63CofinalIndex (Mass j : ℕ) :
    6 * dwz63CofinalIndex Mass j = 100000000 * (6 * Mass * (j + 1)) := by
  unfold dwz63CofinalIndex
  ring

/-- **The distribution constraint.**  `10 ^ 8`, the mass of `dwz63Alpha`, divides the oriented
coarse letter count, so a `dwz63Alpha`-typical word of that length exists arithmetically. -/
theorem dwz63Alpha_mass_dvd_six_mul_cofinalIndex (Mass j : ℕ) :
    (100000000 : ℕ) ∣ 6 * dwz63CofinalIndex Mass j :=
  ⟨6 * Mass * (j + 1), six_mul_dwz63CofinalIndex Mass j⟩

/-- **The position constraint, which is the binding one.**  `10 ^ 8` divides the *stage length*
itself, so the per-position multiplicities `dwz63Alpha i * (n / 10 ^ 8)` are integers. -/
theorem dwz63Alpha_mass_dvd_cofinalIndex (Mass j : ℕ) :
    (100000000 : ℕ) ∣ dwz63CofinalIndex Mass j :=
  ⟨Mass * (j + 1), by unfold dwz63CofinalIndex; ring⟩

/-! ## Position and oriented multiplicities -/

/-- **The position multiplicities of a diagonal `dwz63Alpha`-typical word at the cofinal index**:
cell `i` occupies `dwz63Alpha i * (Mass * (j + 1))` of the `n` positions, and they exhaust `n`. -/
theorem sum_dwz63Alpha_mul_scale (Mass j : ℕ) :
    ∑ i, dwz63Alpha i * (Mass * (j + 1)) = dwz63CofinalIndex Mass j := by
  rw [← Finset.sum_mul]
  have hmass : ∑ i, dwz63Alpha i = 100000000 := by
    simpa [WordType.profileMass] using profileMass_dwz63Alpha
  rw [hmass]
  unfold dwz63CofinalIndex
  ring

/-- **The factor the values lane asked about.**  A diagonal six-orientation letter is the full
`S_3` orbit of one coarse address, so each of the `dwz63Alpha i * (Mass * (j + 1))` positions at
cell `i` contributes **six** oriented coarse letters at that same cell.  The oriented multiplicity
is therefore `dwz63Alpha i` at scale `6 * Mass * (j + 1)`, and summing over `i` returns `6 n`. -/
theorem six_mul_position_multiplicity (Mass j : ℕ) (i : Fin 15) :
    6 * (dwz63Alpha i * (Mass * (j + 1))) = dwz63Alpha i * (6 * Mass * (j + 1)) := by
  ring

/-- The oriented multiplicities exhaust the `6 n` oriented coarse letters. -/
theorem sum_oriented_multiplicity (Mass j : ℕ) :
    ∑ i, dwz63Alpha i * (6 * Mass * (j + 1)) = 6 * dwz63CofinalIndex Mass j := by
  rw [← Finset.sum_mul]
  have hmass : ∑ i, dwz63Alpha i = 100000000 := by
    simpa [WordType.profileMass] using profileMass_dwz63Alpha
  rw [hmass, six_mul_dwz63CofinalIndex]

/-- **The value identity at the cofinal index.**  Given the values lane's one-period *equality*
`exp dwz63LogVal ^ (10 ^ 8) = base`, the endpoint's target `exp dwz63LogVal ^ (6 n)` is exactly the
one-period base raised to the oriented scale `6 * Mass * (j + 1)` --- no inequality, no slack, and
no leftover factor. -/
theorem exp_dwz63LogVal_pow_six_mul_cofinalIndex {base : ℝ}
    (hbase : Real.exp dwz63LogVal ^ (100000000 : ℕ) = base) (Mass j : ℕ) :
    Real.exp dwz63LogVal ^ (6 * dwz63CofinalIndex Mass j) = base ^ (6 * Mass * (j + 1)) := by
  rw [← hbase, ← pow_mul, six_mul_dwz63CofinalIndex]

/-- **The orbit constraint.**  The orbit group mass divides the oriented coarse letter count, so
the letters carrying one component group into blocks of `Mass` with no remainder --- which is what
lets a values lane's `Tensor.power (sym_3 X) (Mass * k)` certificate be used as a group weight. -/
theorem orbitMass_dvd_six_mul_cofinalIndex (Mass j : ℕ) :
    Mass ∣ 6 * dwz63CofinalIndex Mass j :=
  ⟨600000000 * (j + 1), by unfold dwz63CofinalIndex; ring⟩

/-- The number of orbit groups available at the cofinal index: `6 n / Mass`. -/
theorem six_mul_dwz63CofinalIndex_div_mass (Mass j : ℕ) :
    6 * dwz63CofinalIndex Mass j = Mass * (600000000 * (j + 1)) := by
  unfold dwz63CofinalIndex
  ring

/-- The orbit constraint at the level of *positions*: the stage length itself is a multiple of the
orbit group mass, so the positions carrying one component group into blocks of `Mass`. -/
theorem orbitMass_dvd_cofinalIndex (Mass j : ℕ) : Mass ∣ dwz63CofinalIndex Mass j :=
  ⟨100000000 * (j + 1), by unfold dwz63CofinalIndex; ring⟩

/-- **`omega < 2.374631` along the cofinal index.**  The specialization of
`omega_lt_2374631_of_dwz63IsolatedSum` at `dwz63CofinalIndex`, so that a client never has to
supply the cofinality hypothesis --- only the isolation restriction, the per-constituent weight
and the copy count, all at lengths where both divisibility constraints hold. -/
theorem omega_lt_2374631_of_dwz63IsolatedSum_cofinalIndex
    {K : Type u} [Field K] {Mass : ℕ} (hMass : 0 < Mass)
    {Iso : ℕ → Type w} [∀ j, Fintype (Iso j)] [∀ j, DecidableEq (Iso j)]
    {U : ∀ j, Iso j → Leg → Type v}
    [∀ j a c, AddCommMonoid (U j a c)] [∀ j a c, Module K (U j a c)]
    (retained : ∀ j, ∀ a : Iso j, Tensor3 K (U j a))
    (w loss : ℕ → ℝ)
    (hloss : Growth.Subexponential loss)
    (hsum : ∀ j : ℕ,
      Restricts (Tensor.power (symSix K (dwz63Source K)) (dwz63CofinalIndex Mass j))
        (Tensor.indexedDirectSum fun a : Iso j ↦ retained j a))
    (hconstituent : ∀ (j : ℕ) (a : Iso j), HasTauWeight K (retained j a) dwz63Tau (w j))
    (hwpos : ∀ j : ℕ, 0 < w j)
    (hcards : ∀ j : ℕ, 0 < Fintype.card (Iso j))
    (hcount : ∀ j : ℕ, dwz63TrueCopyRate ^ (6 * dwz63CofinalIndex Mass j) ≤
      loss (dwz63CofinalIndex Mass j) * (Fintype.card (Iso j) : ℝ))
    (hvalue : ∀ j : ℕ,
      Real.exp dwz63LogVal ^ (6 * dwz63CofinalIndex Mass j) ≤ w j) :
    omega K < (2374631 / 1000000 : ℝ) :=
  omega_lt_2374631_of_dwz63IsolatedSum (dwz63CofinalIndex Mass) retained w loss hloss
    (dwz63CofinalIndex_cofinal hMass) hsum hconstituent hwpos hcards hcount hvalue

end AlgebraicComplexity.Examples
