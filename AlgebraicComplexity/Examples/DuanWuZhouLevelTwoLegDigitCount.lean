/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoSixOrientationDigits
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoLegMarginal
import AlgebraicComplexity.Combinatorics.MappedTypeIdentities

/-!
# `N_X` for the six-orientation power: the leg-label digit count

Layer 4 (`AlgebraicComplexity/Examples/`).  `[DuanWuZhou2022]` §6.3's hashing branch needs the
number `N_X` of `X`-label words of the six-orientation power that carry the typical marginal.  An
`X`-label of `dwz63SymSixPartition K` is a six-tuple of base-five digits, one per orientation
(`dwz63SymSixDigit`), so an `X`-label *word* of length `n + 1` is exactly six independent words
over `Fin 5`.  This module turns that observation into the count.

## Which marginal each digit carries

In **target** coordinates --- each orientation's component read where it sits, with no transport
back into the source partition's address space --- the `X` leg of every one of the six copies
carries the source `X` marginal, so all six digit sub-words carry the same five-letter table
`dwz63AlphaX`.  (In *source* coordinates the six would instead be `α_X, α_Z, α_Y, α_Y, α_X, α_Z`,
by `dwz63SymSixXLegSource_values`; that is a different, strictly smaller, count.  The convention is
fixed by the typicality predicate the count lane commits, and this module follows the target one.)
`dwz63AlphaMarginal` bundles the three source marginals by leg so that the `Y` and `Z` legs are
available on the same footing; `mappedType_legRead_dwz63AlphaAddress` is the bridge from the
address-space profile `dwz63AlphaAddress` to them.

## Principal results

* `card_dwz63LegTypedWords : #(dwz63LegTypedWords n b) = #(typeClass (n+1) b) ^ 6` --- the count
  factorizes, exactly, into six multinomial type classes.  Nothing about the coarse support is
  used: the six digits of a leg label are unconstrained.
* `dwz63XTypicalCount`, `dwz63XTypicalCount_pos` and
  `dwz63_exists_cutoff_pow_le_dwz63XTypicalCount` / `dwz63_xRate_pow_le_dwz63XTypicalCount` ---
  the count itself, its positivity at the forced word length `n + 1 = 10 ^ 8 t`, and its
  exponential rate, the second in the declared-rational form
  `Examples/DuanWuZhouLevelTwoGlobalStage.lean` states estimate (b) in.

Primary source: Ran Duan, Hongxun Wu and Renfei Zhou, *Faster Matrix Multiplication via Asymmetric
Hashing*, arXiv:2210.10173, section 6.3.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor

open scoped BigOperators

universe u

/-! ## The address-space profile is supported on the fifteen coarse cells -/

theorem mem_cwSquareSupport_of_proportionalCounts_ne_zero {t : ℕ} {s : CWSquareAddress}
    (hs : WordType.proportionalCounts dwz63AlphaAddress t s ≠ 0) : s ∈ cwSquareSupport :=
  mem_cwSquareSupport_of_dwz63AlphaAddress_ne_zero fun h0 ↦ hs (by
    show dwz63AlphaAddress s * t = 0
    rw [h0, Nat.zero_mul])

/-! ## Leg-label words with six prescribed digit types -/

/-- **The leg-label words all six of whose digit sub-words carry a prescribed five-letter type.**
A leg label is a six-tuple of base-five digits, so such a word is six independent `Fin 5` words. -/
noncomputable def dwz63LegTypedWords (n : ℕ) (b : Fin 5 → ℕ) :
    Finset (Fin (n + 1) → DwzSymSixBlock .X) := by
  classical
  exact Finset.univ.filter fun word ↦
    ∀ o : Fin 6, WordType.multiplicity (fun j ↦ dwz63SymSixDigit o (word j)) = b

@[simp] theorem mem_dwz63LegTypedWords {n : ℕ} {b : Fin 5 → ℕ}
    {word : Fin (n + 1) → DwzSymSixBlock .X} :
    word ∈ dwz63LegTypedWords n b ↔
      ∀ o : Fin 6, WordType.multiplicity (fun j ↦ dwz63SymSixDigit o (word j)) = b := by
  classical
  simp [dwz63LegTypedWords]

-- ELABORATION RISK: `Finset.card_bij'` takes its two maps first and then
-- `hi`, `hj`, `left_inv`, `right_inv`.  Fallback if that order differs: use `Finset.card_nbij'`
-- with the same four side conditions in `Set.MapsTo` / `Set.LeftInvOn` form.
/-- **The leg-label digit count factorizes into six multinomial type classes.**

The six digits of a leg label are unconstrained coordinates, so transposing "position, then
orientation" into "orientation, then position" is a bijection onto the sixfold product of type
classes.  This is the exact form of `[DuanWuZhou2022]` §6.3's `N_X` for the six-orientation
power. -/
theorem card_dwz63LegTypedWords (n : ℕ) (b : Fin 5 → ℕ) :
    (dwz63LegTypedWords n b).card = (WordType.typeClass (n + 1) b).card ^ 6 := by
  classical
  have hpi : (Fintype.piFinset fun _ : Fin 6 ↦ WordType.typeClass (n + 1) b).card
      = (WordType.typeClass (n + 1) b).card ^ 6 := by
    rw [Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [← hpi]
  refine Finset.card_bij'
    (fun word _ ↦ fun o j ↦ dwz63SymSixDigit o (word j))
    (fun g _ ↦ fun j ↦ dwz63SymSixOfDigits fun o ↦ g o j)
    ?_ ?_ ?_ ?_
  · intro word hword
    exact Fintype.mem_piFinset.mpr fun o ↦
      WordType.mem_typeClass.mpr (mem_dwz63LegTypedWords.mp hword o)
  · intro g hg
    refine mem_dwz63LegTypedWords.mpr fun o ↦ ?_
    have hfun : (fun j ↦ dwz63SymSixDigit o (dwz63SymSixOfDigits fun o' ↦ g o' j)) = g o :=
      funext fun j ↦ dwz63SymSixDigit_ofDigits _ o
    rw [hfun]
    exact WordType.mem_typeClass.mp (Fintype.mem_piFinset.mp hg o)
  · intro word _
    funext j
    exact dwz63SymSixDigitEquiv.symm_apply_apply (word j)
  · intro g _
    funext o j
    exact dwz63SymSixDigit_ofDigits _ o

/-! ## `N_X` at scale `t` -/

/-- **`[DuanWuZhou2022]`'s `N_X` for the six-orientation power at scale `t`.**

The `X`-label words whose six per-orientation digit sub-words all carry the repeated `X` marginal.
In target coordinates every one of the six copies places the source `X` marginal at the target `X`
leg, so one five-letter table serves all six digits. -/
noncomputable def dwz63XTypicalCount (n t : ℕ) : ℕ :=
  (dwz63LegTypedWords n (WordType.proportionalCounts dwz63AlphaX t)).card

/-- `N_X` is the sixth power of one multinomial type class. -/
theorem dwz63XTypicalCount_eq (n t : ℕ) :
    dwz63XTypicalCount n t =
      (WordType.typeClass (n + 1) (WordType.proportionalCounts dwz63AlphaX t)).card ^ 6 :=
  card_dwz63LegTypedWords n _

/-- At the forced word length the repeated `X` marginal is a legal type. -/
theorem proportionalCounts_dwz63AlphaX_mem_types {n t : ℕ} (hn : n + 1 = 100000000 * t) :
    WordType.proportionalCounts dwz63AlphaX t ∈ WordType.types (Fin 5) (n + 1) := by
  rw [WordType.mem_types, hn]
  show ∑ i, dwz63AlphaX i * t = 100000000 * t
  rw [← Finset.sum_mul,
    show (∑ i, dwz63AlphaX i) = WordType.profileMass dwz63AlphaX from rfl,
    profileMass_dwz63AlphaX]

/-- **`N_X` is positive**, so `dwz63SharpDegree_spec` applies to it. -/
theorem dwz63XTypicalCount_pos {n t : ℕ} (hn : n + 1 = 100000000 * t) :
    0 < dwz63XTypicalCount n t := by
  rw [dwz63XTypicalCount_eq]
  refine pow_pos ?_ 6
  rw [Finset.card_pos]
  exact WordType.typeClass_nonempty _ (proportionalCounts_dwz63AlphaX_mem_types hn)

/-- **The exponential rate of `N_X`**, loss-free after a cutoff: every base strictly below the `X`
marginal's own entropy rate is attained by `N_X` itself, at the sixth power that the six
orientations contribute. -/
theorem dwz63_exists_cutoff_pow_le_dwz63XTypicalCount {lowerBase : ℝ} (hlower : 0 < lowerBase)
    (hlt : lowerBase < (2 : ℝ) ^ ((WordType.profileMass dwz63AlphaX : ℝ) *
      WordType.profileEntropyBits dwz63AlphaX)) :
    ∃ cutoff : ℕ, ∀ t : ℕ, cutoff ≤ t → ∀ n : ℕ, n + 1 = 100000000 * t →
      lowerBase ^ (6 * t) ≤ ((dwz63XTypicalCount n t : ℕ) : ℝ) := by
  have hmass : 0 < WordType.profileMass dwz63AlphaX := by
    rw [profileMass_dwz63AlphaX]; norm_num
  obtain ⟨cutoff, hcut⟩ :=
    WordType.exists_cutoff_forall_pow_le_card_proportionalTypeClass dwz63AlphaX hmass hlower hlt
  refine ⟨cutoff, fun t ht n hn ↦ ?_⟩
  have hclass := hcut t ht
  rw [profileMass_dwz63AlphaX, ← hn] at hclass
  rw [dwz63XTypicalCount_eq, Nat.cast_pow, mul_comm 6 t, pow_mul]
  exact pow_le_pow_left₀ (pow_pos hlower t).le hclass 6

/-- **`N_X` at the declared rational rate.**  This is estimate (b) of `PREP.md` §4.3, raised to the
six orientations: `dwz63XRate ^ (6 (n+1)) ≤ N_X`, with no loss factor left. -/
theorem dwz63_xRate_pow_le_dwz63XTypicalCount :
    ∃ cutoff : ℕ, ∀ t : ℕ, cutoff ≤ t → ∀ n : ℕ, n + 1 = 100000000 * t →
      dwz63XRate ^ (6 * (n + 1)) ≤ ((dwz63XTypicalCount n t : ℕ) : ℝ) := by
  obtain ⟨cutoff, hcut⟩ := dwz63_xRate_pow_le_card_typeClass
  refine ⟨cutoff, fun t ht n hn ↦ ?_⟩
  have hclass := hcut t ht
  rw [profileMass_dwz63AlphaX, ← hn] at hclass
  rw [dwz63XTypicalCount_eq, Nat.cast_pow, mul_comm 6 (n + 1), pow_mul]
  exact pow_le_pow_left₀ (pow_pos dwz63XRate_pos _).le hclass 6

end AlgebraicComplexity.Examples
