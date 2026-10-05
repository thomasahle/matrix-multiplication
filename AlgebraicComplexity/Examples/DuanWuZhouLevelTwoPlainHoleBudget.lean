/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoHoleSupplier

set_option autoImplicit false

/-!
# `hbudget` at the plain partition, and the exact input it still needs

Layer 4 (`AlgebraicComplexity/Examples/`).  `Examples/DuanWuZhouLevelTwoLocalizedStage.lean`'s
stage carries the Hole-Lemma budget

`|avail| * ∏_{a ∈ batch⁻¹ b} |holes a| < |avail| ^ |batch⁻¹ b|`

as a hypothesis.  `Examples/DuanWuZhouLevelTwoHoleSupplier.lean`'s
`dwz63_segmentedHoleBudget_batched` already produces exactly that shape from the `1/8` hole bound
`8 |holes a| ≤ |avail|` (`[DuanWuZhou2022]`'s `claim:hole_frac_low`), so the whole of `hbudget`
reduces to that one cardinality bound at `holes := dwz63HoleSet`.  `dwz63_hbudget_of_holeBound`
below is that reduction, stated in the stage's binder verbatim.

## Splitting the hole set along its two rules

`dwz63HoleSet` is the union of Step 2's two rules, and they are separated here:

* `dwz63SharedZWords a` --- the small blocks compatible with **some other** retained triple.  The
  union bound over the other triples is done (`card_dwz63SharedZWords_le_sum`,
  `card_dwz63SharedZWords_le_mul`), which reduces it to one number: `shareBound`, a bound on
  `|{w : compatibleWith w b}|` for a single retained `b`.
* `dwz63UselessZWords a` --- the small blocks not useful for `a` (`def:useful_g`).  This is a
  statement about the fine profiles alone; no hashing quantity enters it.

`eight_mul_card_dwz63HoleSet_le` then assembles the `1/8` bound from a `1/16` bound on each half.

## What the hash does **not** supply, stated exactly

`Dwz63HoleFractionInputs` names the residual.  It is **not** dischargeable from the hashing lemmas,
and the reason is structural rather than a missing lemma:

* `Combinatorics/MarkedTwoLegHashingExtraction.lean`'s `quarter_of_eight_mul_legFiber_le` and
  `card_markedXYIsolatedTargets_le_card_marked` constrain the `X`- and `Y`-leg fibres and cap the
  retained count by `N_α`.  Neither says anything about how many *fine* `Z`-words a retained triple
  is compatible with, which is the `shareBound` above.
* The committed route to `claim:hole_frac_low` is `Analysis/CompatibilityRate.lean`'s
  `holeFraction_le : 8 V ≤ M → V / M ≤ 1/8`, where `V` is the competitor count
  `matchableCompatible` and `M` is the **modulus**.  That is a *probability over hash seeds*, not a
  cardinality of hole words: the conversion is the union bound over competitors using the per-pair
  `1/M` conditional collision mass, and `CompatibilityRate.lean`'s own "Non-goals" paragraph
  records that this step "is assembly work belonging to the global value theorem (stage M-DWZ6) and
  is not done here".
* Even granted that union bound, it yields an *expected* hole count over seeds.  A per-copy
  deterministic bound holding for **every** retained `a` at the **chosen** seed needs one further
  step --- either a second retention pass discarding the copies whose hole fraction is too large,
  or a seed selection controlling all `a` simultaneously.  `[DuanWuZhou2022]` take the former.

So `hbudget` is reported open here rather than assumed, with the residual isolated to two
inequalities that no lemma in the tree currently proves.

Primary source: Ran Duan, Hongxun Wu and Renfei Zhou, *Faster Matrix Multiplication via Asymmetric
Hashing*, arXiv:2210.10173, section 6 and `hole_lemma.tex`.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor
open scoped BigOperators

universe u v w

section HoleBudget

variable {I : Type u} [Fintype I] [DecidableEq I] {n m : ℕ}
variable {τ : Type v} [Fintype τ] [DecidableEq τ]

/-! ## The two rules of Step 2, separated -/

/-- **Rule (i)**: the small blocks compatible with some *other* retained triple. -/
noncomputable def dwz63SharedZWords (seg : Fin (n + 1) → Fin m) (α : Fin m → I → ℕ)
    (retained : Finset τ)
    (compatibleWith : SegmentedAvailableWord seg α → τ → Prop) (a : τ) :
    Finset (SegmentedAvailableWord seg α) := by
  classical
  exact Finset.univ.filter fun w ↦ ∃ b ∈ retained, b ≠ a ∧ compatibleWith w b

/-- **Rule (ii)**: the small blocks not useful for `a` (`def:useful_g`). -/
noncomputable def dwz63UselessZWords (seg : Fin (n + 1) → Fin m) (α : Fin m → I → ℕ)
    (usefulFor : SegmentedAvailableWord seg α → τ → Prop) (a : τ) :
    Finset (SegmentedAvailableWord seg α) := by
  classical
  exact Finset.univ.filter fun w ↦ ¬ usefulFor w a

/-- The small blocks compatible with one fixed retained triple. -/
noncomputable def dwz63CompatibleZWords (seg : Fin (n + 1) → Fin m) (α : Fin m → I → ℕ)
    (compatibleWith : SegmentedAvailableWord seg α → τ → Prop) (b : τ) :
    Finset (SegmentedAvailableWord seg α) := by
  classical
  exact Finset.univ.filter fun w ↦ compatibleWith w b

/-- **The hole set is covered by its two rules.** -/
theorem card_dwz63HoleSet_le (seg : Fin (n + 1) → Fin m) (α : Fin m → I → ℕ)
    (retained : Finset τ)
    (compatibleWith usefulFor : SegmentedAvailableWord seg α → τ → Prop) (a : τ) :
    (dwz63HoleSet seg α retained compatibleWith usefulFor a).card ≤
      (dwz63SharedZWords seg α retained compatibleWith a).card +
        (dwz63UselessZWords seg α usefulFor a).card := by
  classical
  refine le_trans (Finset.card_le_card ?_)
    (Finset.card_union_le (dwz63SharedZWords seg α retained compatibleWith a)
      (dwz63UselessZWords seg α usefulFor a))
  intro w hw
  rw [mem_dwz63HoleSet] at hw
  rcases hw with h | h
  · refine Finset.mem_union_left _ ?_
    simp only [dwz63SharedZWords, Finset.mem_filter, Finset.mem_univ, true_and]
    exact h
  · refine Finset.mem_union_right _ ?_
    simp only [dwz63UselessZWords, Finset.mem_filter, Finset.mem_univ, true_and]
    exact h

/-! ## The union bound over the other retained triples -/

omit [Fintype τ] in
/-- **Rule (i) is a union over the other retained triples.** -/
theorem card_dwz63SharedZWords_le_sum (seg : Fin (n + 1) → Fin m) (α : Fin m → I → ℕ)
    (retained : Finset τ)
    (compatibleWith : SegmentedAvailableWord seg α → τ → Prop) (a : τ) :
    (dwz63SharedZWords seg α retained compatibleWith a).card ≤
      ∑ b ∈ retained.erase a, (dwz63CompatibleZWords seg α compatibleWith b).card := by
  classical
  calc (dwz63SharedZWords seg α retained compatibleWith a).card
      ≤ ((retained.erase a).biUnion
          (dwz63CompatibleZWords seg α compatibleWith)).card := by
        refine Finset.card_le_card ?_
        intro w hw
        simp only [dwz63SharedZWords, Finset.mem_filter, Finset.mem_univ, true_and] at hw
        obtain ⟨b, hb, hne, hcomp⟩ := hw
        refine Finset.mem_biUnion.mpr ⟨b, Finset.mem_erase.mpr ⟨hne, hb⟩, ?_⟩
        simp only [dwz63CompatibleZWords, Finset.mem_filter, Finset.mem_univ, true_and]
        exact hcomp
    _ ≤ ∑ b ∈ retained.erase a, (dwz63CompatibleZWords seg α compatibleWith b).card :=
        Finset.card_biUnion_le

omit [Fintype τ] in
/-- **Rule (i) against one uniform per-triple bound.** -/
theorem card_dwz63SharedZWords_le_mul (seg : Fin (n + 1) → Fin m) (α : Fin m → I → ℕ)
    (retained : Finset τ)
    (compatibleWith : SegmentedAvailableWord seg α → τ → Prop) (a : τ) (shareBound : ℕ)
    (hcompat : ∀ b ∈ retained,
      (dwz63CompatibleZWords seg α compatibleWith b).card ≤ shareBound) :
    (dwz63SharedZWords seg α retained compatibleWith a).card ≤ retained.card * shareBound := by
  classical
  calc (dwz63SharedZWords seg α retained compatibleWith a).card
      ≤ ∑ b ∈ retained.erase a, (dwz63CompatibleZWords seg α compatibleWith b).card :=
        card_dwz63SharedZWords_le_sum seg α retained compatibleWith a
    _ ≤ ∑ _b ∈ retained.erase a, shareBound :=
        Finset.sum_le_sum fun b hb ↦ hcompat b (Finset.mem_of_mem_erase hb)
    _ = (retained.erase a).card * shareBound := by
        rw [Finset.sum_const, smul_eq_mul]
    _ ≤ retained.card * shareBound :=
        Nat.mul_le_mul_right _ (Finset.card_le_card (Finset.erase_subset _ _))

/-! ## The `1/8` bound from a `1/16` bound on each rule -/

/-- **`claim:hole_frac_low`'s conclusion, assembled from its two halves.** -/
theorem eight_mul_card_dwz63HoleSet_le (seg : Fin (n + 1) → Fin m) (α : Fin m → I → ℕ)
    (retained : Finset τ)
    (compatibleWith usefulFor : SegmentedAvailableWord seg α → τ → Prop) (a : τ)
    (shareBound : ℕ)
    (hcompat : ∀ b ∈ retained,
      (dwz63CompatibleZWords seg α compatibleWith b).card ≤ shareBound)
    (hshared : 16 * (retained.card * shareBound) ≤
      Fintype.card (SegmentedAvailableWord seg α))
    (huseless : 16 * (dwz63UselessZWords seg α usefulFor a).card ≤
      Fintype.card (SegmentedAvailableWord seg α)) :
    8 * (dwz63HoleSet seg α retained compatibleWith usefulFor a).card ≤
      Fintype.card (SegmentedAvailableWord seg α) := by
  have hsplit := card_dwz63HoleSet_le seg α retained compatibleWith usefulFor a
  have hshare := card_dwz63SharedZWords_le_mul seg α retained compatibleWith a shareBound hcompat
  omega

/-! ## The residual, named -/

/-- **The two inequalities the hashing layer does not supply.**

Stated, not proved --- the same convention as `Dwz63SharpRateStatement`
(`Examples/DuanWuZhouLevelTwoSharpDegree.lean`).  `shareBound` bounds the number of available small
blocks compatible with **one** retained triple; the first inequality is the union bound over all
retained triples, the second is `def:useful_g`'s density.  See the module docstring for why neither
follows from `quarter_of_eight_mul_legFiber_le`, `card_markedXYIsolatedTargets_le_card_marked` or
`Analysis/CompatibilityRate.holeFraction_le`. -/
def Dwz63HoleFractionInputs (seg : Fin (n + 1) → Fin m) (α : Fin m → I → ℕ)
    (retained : Finset τ)
    (compatibleWith usefulFor : SegmentedAvailableWord seg α → τ → Prop)
    (shareBound : ℕ) : Prop :=
  (∀ b ∈ retained, (dwz63CompatibleZWords seg α compatibleWith b).card ≤ shareBound) ∧
    16 * (retained.card * shareBound) ≤ Fintype.card (SegmentedAvailableWord seg α) ∧
      ∀ a : τ, 16 * (dwz63UselessZWords seg α usefulFor a).card ≤
        Fintype.card (SegmentedAvailableWord seg α)

theorem eight_mul_card_dwz63HoleSet_le_of_inputs {seg : Fin (n + 1) → Fin m} {α : Fin m → I → ℕ}
    {retained : Finset τ}
    {compatibleWith usefulFor : SegmentedAvailableWord seg α → τ → Prop} {shareBound : ℕ}
    (hinputs : Dwz63HoleFractionInputs seg α retained compatibleWith usefulFor shareBound)
    (a : τ) :
    8 * (dwz63HoleSet seg α retained compatibleWith usefulFor a).card ≤
      Fintype.card (SegmentedAvailableWord seg α) :=
  eight_mul_card_dwz63HoleSet_le seg α retained compatibleWith usefulFor a shareBound
    hinputs.1 hinputs.2.1 (hinputs.2.2 a)

/-! ## `hbudget`, in the stage's binder -/

omit [Fintype τ] in
/-- **`hbudget` from the `1/8` hole bound**, in the shape
`dwz63_localizedStage_of_segmentedRepair` and `dwz63_localizedSymSixStage_of_segmentedRepair`
carry it, at `holes a = dwz63HoleSet … a.1`.

This is the whole of `hbudget`: `dwz63_segmentedHoleBudget_batched` supplies the union bound over
`∏_t Avail_t`, and the only remaining content is the `1/8` bound `hholes`. -/
theorem dwz63_hbudget_of_holeBound (seg : Fin (n + 1) → Fin m) (α : Fin m → I → ℕ)
    (retained : Finset τ)
    (compatibleWith usefulFor : SegmentedAvailableWord seg α → τ → Prop) (L : ℕ)
    (hpos : 0 < Fintype.card (SegmentedAvailableWord seg α))
    (hbound : Fintype.card (SegmentedAvailableWord seg α) ≤ 2 ^ L)
    (hholes : ∀ a : τ, 8 * (dwz63HoleSet seg α retained compatibleWith usefulFor a).card ≤
      Fintype.card (SegmentedAvailableWord seg α))
    {β : Type v} [Fintype β] [DecidableEq β] (batch : retained → β)
    (hcopies : ∀ b : β, 8 * (L + 1) ≤ 7 * Fintype.card {a : retained // batch a = b}) :
    ∀ b : β,
      Fintype.card (SegmentedAvailableWord seg α) *
          ∏ a : {a : retained // batch a = b},
            (dwz63HoleSet seg α retained compatibleWith usefulFor a.1.1).card <
        Fintype.card (SegmentedAvailableWord seg α) ^
          Fintype.card {a : retained // batch a = b} :=
  dwz63_segmentedHoleBudget_batched seg α L hpos hbound batch
    (fun a : retained ↦ dwz63HoleSet seg α retained compatibleWith usefulFor a.1)
    (fun a ↦ hholes a.1) hcopies

/-- **`hbudget` from the named residual.**  The composition of the two reductions above: once
`Dwz63HoleFractionInputs` is established, the stage's `hbudget` is discharged. -/
theorem dwz63_hbudget_of_holeFractionInputs (seg : Fin (n + 1) → Fin m) (α : Fin m → I → ℕ)
    (retained : Finset τ)
    (compatibleWith usefulFor : SegmentedAvailableWord seg α → τ → Prop)
    {shareBound : ℕ}
    (hinputs : Dwz63HoleFractionInputs seg α retained compatibleWith usefulFor shareBound)
    (L : ℕ)
    (hpos : 0 < Fintype.card (SegmentedAvailableWord seg α))
    (hbound : Fintype.card (SegmentedAvailableWord seg α) ≤ 2 ^ L)
    {β : Type v} [Fintype β] [DecidableEq β] (batch : retained → β)
    (hcopies : ∀ b : β, 8 * (L + 1) ≤ 7 * Fintype.card {a : retained // batch a = b}) :
    ∀ b : β,
      Fintype.card (SegmentedAvailableWord seg α) *
          ∏ a : {a : retained // batch a = b},
            (dwz63HoleSet seg α retained compatibleWith usefulFor a.1.1).card <
        Fintype.card (SegmentedAvailableWord seg α) ^
          Fintype.card {a : retained // batch a = b} :=
  dwz63_hbudget_of_holeBound seg α retained compatibleWith usefulFor L hpos hbound
    (eight_mul_card_dwz63HoleSet_le_of_inputs hinputs) batch hcopies

end HoleBudget

end AlgebraicComplexity.Examples
