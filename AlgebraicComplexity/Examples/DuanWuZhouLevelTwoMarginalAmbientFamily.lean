/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoSixOrientationDigits
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoCounting
import AlgebraicComplexity.Tensor.PartitionedGroupingBoxes

/-!
# The marginal-typical ambient family of `[DuanWuZhou2022]` section 6.3

Layer 4 (`AlgebraicComplexity/Examples/`).  The joint hash of
`Examples/DuanWuZhouLevelTwoJointHashing.lean` runs at ambient `Finset.univ`, and over that
ambient the leg fiber of a marked triple is `∏_o (5 - d_o)` --- fixing an `X` digit leaves
`5 - d` completions of the coarse cell.  Per oriented letter that is
`Σ_x α_X(x)·ln(5-x) = 1.2785728` nats against the sharp `H(α) - H(α_X) = 0.9240977`, so the
retained rate falls to `H(α) - 1.2785728 = 0.7346993` where `H(α_X) = 1.0891744` is required: the
count does not close at the full ambient.

This module supplies the ambient at which it does.

## Why a marginal cut, and not a joint one

`Tensor/PartitionedExtraction.lean`'s `IsProjectionClosed ambient selected active` (`:36`) is
literally the crossing-block condition: `∀ u ∈ ambient, (∀ c ∈ active, ∃ s ∈ selected, u c = s c)
→ u ∈ selected`.  `PartitionedTensor.select_support_isProjectionClosed_univ`
(`Tensor/PartitionedGroupingBoxes.lean:60`) proves it for *every* legwise `keep : ∀ c, A c → Prop`,
so a **marginal**-type cut --- each leg's condition depending only on that leg's word --- is a
free, sound restriction.

A **joint**-type cut is not, and the counterexample is one line: take the `X` word of one
`α`-typical address, the `Y` word of a second and the `Z` word of a third.  The resulting `u` has
all three correct marginals, so `u ∈ ambient`; each of its three labels is a label of a selected
address; yet its joint type need not be `α`, so `u ∉ selected`.  `IsProjectionClosed` fails
exactly there.  Hence the hashing ambient may be `dwz63MarginalWords` but may **not** be
`dwz63TargetTypicalWords`.

## What the ambient costs

Over the marginal-typical family the fiber of a fixed `α_X`-typical `X` word is `N_triple / N_X`,
and `N_triple = poly · exp(n·H(α'))` for `α'` the **maximum-entropy** member of `D_α` (the
distributions sharing all three marginals of `α`).  The committed
`dwz63_gibbsDeficit_le_log_hashLossMultiplier`
(`Examples/DuanWuZhouLevelTwoGlobalArithmetic.lean:837`) bounds `H(α') - H(α)` by `log K`, so

`marginal ambient fiber ≤ H(α) - H(α_X) + log K = 0.9240977008253182` nats per oriented letter,

and the retained rate is at least `H(α_X) - log K = 1.0891743499949558`, which is the *same
expression* as `log (exp dwz63EntropyX / dwz63HashLossMultiplier)`, i.e. `log` of branch one of
`dwz63TrueCopyRate`.  The count closes with no residual slack: the `K` in that branch is exactly
the price of the ambient being the max-entropy distribution rather than `α` itself.

Primary source: Ran Duan, Hongxun Wu and Renfei Zhou, *Faster Matrix Multiplication via Asymmetric
Hashing*, arXiv:2210.10173, section 6.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor
open scoped BigOperators

universe u v

/-! ## The three leg marginals of `dwz63Alpha` -/

/-- **The `dwz63Alpha` marginal at one leg.**  `dwz63Alpha` is symmetric in its first two
arguments, so `X` and `Y` share the profile `dwz63AlphaX`. -/
def dwz63LegMarginal : Leg → Fin 5 → ℕ
  | .X => dwz63AlphaX
  | .Y => dwz63AlphaX
  | .Z => dwz63AlphaZ

/-- **Reading one leg of a coarse address pushes `dwz63AlphaAddress` to that leg's marginal.**
This is what turns target-coordinate typicality into a per-leg marginal-type statement. -/
theorem mappedType_legProjection_dwz63AlphaAddress (c : Leg) :
    WordType.mappedType (fun addr : CWSquareAddress ↦ addr c) dwz63AlphaAddress =
      dwz63LegMarginal c := by
  unfold dwz63AlphaAddress
  rw [WordType.mappedType_comp]
  cases c
  · exact (congrArg (fun f ↦ WordType.mappedType f dwz63Alpha)
      (funext fun _ ↦ rfl : (fun addr : CWSquareAddress ↦ addr .X) ∘ dwz63CellAddress =
        dwz63XIndex)).trans mappedType_dwz63XIndex_dwz63Alpha
  · exact (congrArg (fun f ↦ WordType.mappedType f dwz63Alpha)
      (funext fun _ ↦ rfl : (fun addr : CWSquareAddress ↦ addr .Y) ∘ dwz63CellAddress =
        dwz63YIndex)).trans mappedType_dwz63YIndex_dwz63Alpha
  · exact (congrArg (fun f ↦ WordType.mappedType f dwz63Alpha)
      (funext fun _ ↦ rfl : (fun addr : CWSquareAddress ↦ addr .Z) ∘ dwz63CellAddress =
        dwz63ZIndex)).trans mappedType_dwz63ZIndex_dwz63Alpha

/-! ## Marginal typicality of a block word -/

/-- **Marginal typicality.**  Each leg's word carries, in each of the six orientations, the
`dwz63Alpha` marginal type at that leg.  Every condition depends on one leg only, which is what
makes the cut a legwise `select` and hence projection-closed. -/
def Dwz63MarginalTypical (K : Type u) [CommRing K] (n t : ℕ)
    (q : PositiveWord ((dwz63SymSixPartition K).support) n) : Prop :=
  ∀ (c : Leg) (o : Fin 6),
    WordType.multiplicity
        (fun j ↦ dwz63SymSixDigit o ((positiveWordEquiv _ n q j).val c)) =
      WordType.proportionalCounts (dwz63LegMarginal c) t

/-- **The marginal-typical word family**, the ambient the hash may legitimately run at. -/
noncomputable def dwz63MarginalWords (K : Type u) [CommRing K] (n t : ℕ) :
    Finset (PositiveWord ((dwz63SymSixPartition K).support) n) := by
  classical
  exact Finset.univ.filter (Dwz63MarginalTypical K n t)

theorem mem_dwz63MarginalWords {K : Type u} [CommRing K] {n t : ℕ}
    {q : PositiveWord ((dwz63SymSixPartition K).support) n} :
    q ∈ dwz63MarginalWords K n t ↔ Dwz63MarginalTypical K n t q := by
  classical
  simp [dwz63MarginalWords]

/-! ## Piece (3): target typicality implies marginal typicality -/

/-- **Target-coordinate typicality implies marginal typicality.**

The `c`-digit word of orientation `o` is the `c` projection of that orientation's target sub-word
(`dwz63TargetLetter_apply`), so its type is the pushforward of
`WordType.proportionalCounts dwz63AlphaAddress t` along reading leg `c` --- which is
`dwz63LegMarginal c` repeated `t` times. -/
theorem dwz63MarginalTypical_of_targetTypical {K : Type u} [CommRing K] {n t : ℕ}
    {q : PositiveWord ((dwz63SymSixPartition K).support) n}
    (h : Dwz63TargetTypical K n t q) : Dwz63MarginalTypical K n t q := by
  intro c o
  have hword : (fun j ↦ dwz63SymSixDigit o ((positiveWordEquiv _ n q j).val c)) =
      (fun addr : CWSquareAddress ↦ addr c) ∘ dwz63TargetWord K n o q := by
    funext j
    exact (dwz63TargetLetter_apply o _ c).symm
  rw [hword, WordType.multiplicity_comp_eq_mappedType, h o, mappedType_proportionalCounts,
    mappedType_legProjection_dwz63AlphaAddress]

/-- **`hmarked`.**  The marked family sits inside the ambient the hash runs at. -/
theorem dwz63TargetTypicalWords_subset_dwz63MarginalWords (K : Type u) [CommRing K] (n t : ℕ) :
    dwz63TargetTypicalWords K n t ⊆ dwz63MarginalWords K n t := by
  intro q hq
  exact mem_dwz63MarginalWords.mpr
    (dwz63MarginalTypical_of_targetTypical (mem_dwz63TargetTypicalWords.mp hq))

/-! ## Piece (1): the marginal cut as a legwise `select`, and its restriction -/

/-- **The legwise keep predicate.**  One condition per leg, depending on that leg's word alone. -/
def dwz63MarginalKeep (n t : ℕ) : ∀ c : Leg, PositiveWord (DwzSymSixBlock c) n → Prop :=
  fun c word ↦ ∀ o : Fin 6,
    WordType.multiplicity (fun j ↦ dwz63SymSixDigit o (positiveWordEquiv _ n word j)) =
      WordType.proportionalCounts (dwz63LegMarginal c) t

/-- **The marginal-typical subpartition of the six-orientation positive power.** -/
noncomputable def dwz63MarginalTypicalPower (K : Type u) [CommRing K] (n t : ℕ) := by
  classical
  exact ((dwz63SymSixPartition K).positivePower n).select (dwz63MarginalKeep n t)

/-- **The marginal cut is a restriction, with no hypothesis.**

`PartitionedTensor.select_support_isProjectionClosed_univ` supplies projection-closure on all
three legs for any legwise `keep`, and `Restricts.partitionedProjectionClosed` turns that into the
tensor restriction.  This is the step a joint-type cut cannot take. -/
theorem dwz63_restricts_positivePower_marginalTypical (K : Type u) [CommRing K] (n t : ℕ) :
    Restricts ((dwz63SymSixPartition K).positivePower n).realize
      (dwz63MarginalTypicalPower K n t).realize := by
  classical
  exact Tensor.Restricts.partitionedProjectionClosed
    ((dwz63SymSixPartition K).positivePower n)
    (dwz63MarginalTypicalPower K n t).support Finset.univ
    (PartitionedTensor.select_support_isProjectionClosed_univ
      ((dwz63SymSixPartition K).positivePower n) (dwz63MarginalKeep n t))

/-! ## Piece (2): the retained family at the marginal ambient -/

section Retained

variable {R : Type v} [Field R] {p : ℕ} [CharP R p]

/-- **The family the joint hash retains at the marginal-typical ambient.**

Identical to `dwz63JointRetainedSupport` except that the ambient is `dwz63MarginalWords` rather
than `Finset.univ`.  No engine change is needed: every marked two-leg hashing theorem is already
parametric in `(ambientWords, markedWords)` with `hwords : markedWords ⊆ ambientWords`. -/
noncomputable def dwz63JointRetainedSupportMarginal (K : Type u) [CommRing K] (hp : 15625 ≤ p)
    (n t : ℕ) (markedWords : Finset (PositiveWord ((dwz63SymSixPartition K).support) n))
    (B : Finset R) (seed : ProgressionHash.Seed R (Fin (n + 1))) :
    Finset (BlockAddress fun c ↦ PositiveWord (DwzSymSixBlock c) n) :=
  (dwz63SymSixHashEncoding K R hp).markedXYIsolatedPowerAddresses n
    (dwz63MarginalWords K n t) markedWords B seed

/-- **`hX` at the marginal ambient.** -/
theorem dwz63_x_injOn_jointRetainedMarginal [NeZero (2 : R)]
    (K : Type u) [CommRing K] (hp : 15625 ≤ p) (n t : ℕ)
    (markedWords : Finset (PositiveWord ((dwz63SymSixPartition K).support) n))
    (hmarked : markedWords ⊆ dwz63MarginalWords K n t)
    (B : Finset R) (hB : ThreeAPFree (B : Set R))
    (seed : ProgressionHash.Seed R (Fin (n + 1))) :
    Set.InjOn (fun address : BlockAddress (fun c ↦ PositiveWord (DwzSymSixBlock c) n) ↦
        address .X)
      (dwz63JointRetainedSupportMarginal K hp n t markedWords B seed : Set _) :=
  (dwz63SymSixHashEncoding K R hp).x_injectiveOn_markedXYIsolatedPowerAddresses n
    (dwz63MarginalWords K n t) markedWords hmarked B hB seed

/-- **The good seed at the marginal-typical ambient.**

The `[DuanWuZhou2022]` retention bound with the leg fibers measured against the marginal-typical
family.  This is the shape the typical-count lane's fiber bound plugs into: its `d` is
`N_triple / N_X`, whose logarithm is `H(α') - H(α_X) ≤ H(α) - H(α_X) + log K`. -/
theorem exists_seed_dwz63JointRetainedMarginal [Fintype R] [NeZero (2 : R)]
    (K : Type u) [CommRing K] (hp : 15625 ≤ p) (n t : ℕ)
    (markedWords : Finset (PositiveWord ((dwz63SymSixPartition K).support) n))
    (hmarked : markedWords ⊆ dwz63MarginalWords K n t)
    (B : Finset R) (hB : ThreeAPFree (B : Set R)) (d : ℕ)
    (hXfiber : ∀ triple ∈ (dwz63SymSixHashEncoding K R hp).legalTargets n markedWords,
      (ProgressionHash.LegalTriple.legFiber
        ((dwz63SymSixHashEncoding K R hp).legalTargets n (dwz63MarginalWords K n t))
        triple .X).card ≤ d)
    (hYfiber : ∀ triple ∈ (dwz63SymSixHashEncoding K R hp).legalTargets n markedWords,
      (ProgressionHash.LegalTriple.legFiber
        ((dwz63SymSixHashEncoding K R hp).legalTargets n (dwz63MarginalWords K n t))
        triple .Y).card ≤ d)
    (hmodulus : 8 * d ≤ Fintype.card R) :
    ∃ seed : ProgressionHash.Seed R (Fin (n + 1)),
      3 * markedWords.card * B.card ≤
        4 * (Fintype.card R * Fintype.card R) *
          (dwz63JointRetainedSupportMarginal K hp n t markedWords B seed).card := by
  obtain ⟨seed, hcount, _hsubset, _hinjX, _hinjY⟩ :=
    (dwz63SymSixHashEncoding K R hp).exists_seed_many_markedXYIsolatedPowerAddresses_of_modulus
      n (dwz63MarginalWords K n t) markedWords hmarked B hB d hXfiber hYfiber hmodulus
  exact ⟨seed, hcount⟩

end Retained

end AlgebraicComplexity.Examples
