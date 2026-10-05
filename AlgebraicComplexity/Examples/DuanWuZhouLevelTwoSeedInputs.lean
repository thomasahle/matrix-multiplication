/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoSeedSelection
import AlgebraicComplexity.Analysis.CompatibilityRate
import AlgebraicComplexity.Combinatorics.WordTypeMultiplicityFilter

set_option autoImplicit false

/-!
# The three inputs of the joint seed selection

Layer 4 (`AlgebraicComplexity/Examples/`).  `Examples/DuanWuZhouLevelTwoSeedSelection.lean`'s
`dwz63_exists_seed_aggregateHoleFraction` takes three inputs that are *not* hashing facts:
`hcompetitors` with its bound `V`, `hzIndex`, and the rule-(ii) allowance `huseless`.  This module
supplies all three from the committed compatibility-cell machinery.

## The relation

`dwz63SplitCompat` pins the owner-relative `compat` of the seed selection to the committed cells:

`compat a w c  :=  zIndex ∘ component c = zIndex ∘ component a ∧
                   IsUseful (component a) (read a w) ∧ IsCompatible (component c) (read a w)`

with `component` the level-two component word of a legal triple and `read a` the reading of a
reference available word *in the copy `a`'s own coordinates*.  Three remarks.

* The first conjunct is `[DuanWuZhou2022]`'s own quantifier, not an extra assumption:
  `claim:hole_frac_low` (`global_value.tex:254`) ranges over `I' ≠ I` **matchable to `K`**, and
  Additional Zeroing-Out Step 2 (`global_value.tex:74-89`) zeroes `Z_K̂ ∈ Z_K` when it is
  compatible with another triple *through the same `Z_K`*.  The committed competitor family
  `SplitRequirements.matchable αType K` has that pinning built into it.
* It is **not** derivable from typicality.  `dwz63SplitCompat_isTypical` shows that both
  `zIndex ∘ component a` and `zIndex ∘ component c` make `read a w` typical, i.e. the two large
  `Z`-blocks have the same *type*; equal types are not equal words, so the block-level equality
  has to be part of the relation.  That lemma is also exactly the `hw` premise of the modulus
  arithmetic below, so nothing is lost.
* `IsUseful` is stated for the owner, `IsCompatible` for the competitor — that is
  `def:useful_g` for the copy one is counting inside and `def:global-compatible` for the
  competitor, precisely as `claim:hole_frac_low` reads them.

## (a) `hcompetitors` and `V`

`card_dwz63FineCompetitors_le_card_matchableCompatible` maps the seed layer's competitor Finset
into `SplitRequirements.matchableCompatible αType (zIndex ∘ component a) (read a w)` by
`component`, injectively.  So `V` may be taken to be the competitor count that
`Analysis/CompatibilityRate.card_matchableCompatible_eq_mul_compatibleFraction` evaluates exactly
as `(N_α / N_Z) · p_comp`.

## The modulus, and the number the hash lane needs

`dwz63_modulus_of_compatibleSet` is `Analysis/CompatibilityRate.eight_mul_card_matchableCompatible_le`
with the constant the joint selection needs.  It gives `256 · V ≤ 3 · M` from

`256 · (N_α/N_Z) · |compatible blocks| ≤ 3 · M · |T_K|`,

i.e. from `M ≥ (256/3) · N_α · p_comp / N_Z`.  `[DuanWuZhou2022]`'s second branch of `M₀` is
`8 · N_α · p_comp / N_Z`, so **the sharp modulus must be a factor `256/24 = 32/3 ≈ 10.67` larger
than the paper's**; equivalently `M ≥ 85.34 · N_α p_comp / N_Z`.  If image 54's
`dwz63SharpHashModulus` pinned the constant at `8`, it has to be raised to `86` (any integer
`≥ 256/3`) on that branch.  The cost is a constant factor `32/3` in `E[N_ret] = N_α/M`, which the
endpoint's subexponential `loss` absorbs, but the constant itself changes.

## (b) `hzIndex`

`dwz63_hzIndex` reads the first conjunct through the encoding: the hash's `Z`-word is determined
by the component word's `Z`-part.  That is the only encoding fact used, and it is carried as the
named hypothesis `hzHash`.

## (c) `huseless` is zero

`isUseful_of_segmentedAvailableWord` identifies `SegmentedAvailableWord seg α` with the useful
set: membership is `∀ t, segmentMultiplicity seg word t = α t`, and `IsUseful seg word` is
`multiplicity (jointWord seg word) = usefulType`, and these are the same family of position
counts (`WordType.multiplicity_eq_card_filter` supplies the instance-tolerant bridge).  Hence
`dwz63UselessZWords_eq_empty` and `card_dwz63UselessZWords_eq_zero`: in the localized picture
rule (ii) removes nothing, so the allowance may be taken to be `0`.

Primary source: Ran Duan, Hongxun Wu and Renfei Zhou, *Faster Matrix Multiplication via Asymmetric
Hashing*, arXiv:2210.10173, §6.2 (`global_value.tex`), `lemma:pcomp_g`, `claim:hole_frac_low`.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor ProgressionHash CompatibleSplit
open scoped BigOperators

universe u v w x

/-! ## The modulus arithmetic with the joint selection's constant -/

section Modulus

variable {C : Type u} [Fintype C] [DecidableEq C]
variable {L : Type v} [Fintype L] [DecidableEq L]
variable {Z : Type w} [Fintype Z] [DecidableEq Z]
variable {N : ℕ}

/-- **The modulus condition of the joint seed selection.**

`Analysis/CompatibilityRate.eight_mul_card_matchableCompatible_le` with `8` replaced by the
constant `256/3` that `dwz63_exists_seed_retained_and_holeMass` consumes.  See the module
docstring for the resulting requirement on the sharp modulus. -/
theorem dwz63_modulus_of_compatibleSet (S : SplitRequirements C L Z)
    {αType : C → ℕ} {K : Fin N → Z} {M : ℕ}
    {comp₀ : Fin N → C} (hcomp₀ : comp₀ ∈ S.matchable αType K)
    {w : Fin N → L} (hw : w ∈ S.typicalSet K) (htyp : 0 < (S.typicalSet K).card)
    (hmod : 256 * ((S.matchable αType K).card * (S.compatibleSet comp₀).card) ≤
      3 * M * (S.typicalSet K).card) :
    256 * (S.matchableCompatible αType K w).card ≤ 3 * M := by
  have hpair := SplitRequirements.card_matchableCompatible_mul_card_typicalSet
    (S := S) hcomp₀ hw
  have hstep : 256 * (S.matchableCompatible αType K w).card * (S.typicalSet K).card ≤
      (3 * M) * (S.typicalSet K).card := by
    calc 256 * (S.matchableCompatible αType K w).card * (S.typicalSet K).card
        = 256 * ((S.matchableCompatible αType K w).card * (S.typicalSet K).card) := by ring
      _ = 256 * ((S.matchable αType K).card * (S.compatibleSet comp₀).card) := by rw [hpair]
      _ ≤ 3 * M * (S.typicalSet K).card := hmod
  exact Nat.le_of_mul_le_mul_right hstep htyp

end Modulus

/-! ## The owner-relative relation, pinned to the committed cells -/

section Relation

variable {R : Type x} [Field R] [Fintype R] {N : ℕ} {targetVal : R}
variable {C : Type u} [Fintype C] [DecidableEq C]
variable {L : Type v} [Fintype L] [DecidableEq L]
variable {Z : Type w} [Fintype Z] [DecidableEq Z]
variable {A : Type v}

/-- **Additional Zeroing-Out Step 2's rule (i), pinned to the committed compatibility cells.** -/
def dwz63SplitCompat (S : SplitRequirements C L Z)
    (component : LegalTriple R (Fin N) targetVal → (Fin N → C))
    (read : LegalTriple R (Fin N) targetVal → A → (Fin N → L))
    (a : LegalTriple R (Fin N) targetVal) (w : A)
    (c : LegalTriple R (Fin N) targetVal) : Prop :=
  S.zIndex ∘ component c = S.zIndex ∘ component a ∧
    S.IsUseful (component a) (read a w) ∧ S.IsCompatible (component c) (read a w)

omit [Fintype R] in
/-- **The read block is typical for the owner's large `Z`-block.**

`def:useful_g` refines `def:global-compatible` refines typicalness — the committed chain
`mem_compatibleSet_of_mem_usefulSet` then `mem_typicalSet_of_mem_compatibleSet`.  This is the `hw`
premise of `dwz63_modulus_of_compatibleSet`, and it is what shows that pinning the large `Z`-block
in `dwz63SplitCompat` is consistent rather than restrictive. -/
theorem dwz63SplitCompat_isTypical (S : SplitRequirements C L Z)
    {component : LegalTriple R (Fin N) targetVal → (Fin N → C)}
    {read : LegalTriple R (Fin N) targetVal → A → (Fin N → L)}
    {a : LegalTriple R (Fin N) targetVal} {w : A}
    (huseful : S.IsUseful (component a) (read a w)) :
    read a w ∈ S.typicalSet (S.zIndex ∘ component a) :=
  S.mem_typicalSet_of_mem_compatibleSet
    (S.mem_compatibleSet_of_mem_usefulSet (S.mem_usefulSet.mpr huseful))

omit [Fintype R] [DecidableEq C] [DecidableEq L] [Fintype Z] [DecidableEq Z] in
/-- **(a) The competitor bridge.**

The seed layer's competitor Finset injects, by `component`, into the committed competitor family
`SplitRequirements.matchableCompatible`. -/
theorem card_dwz63FineCompetitors_le_card_matchableCompatible (S : SplitRequirements C L Z)
    (component : LegalTriple R (Fin N) targetVal → (Fin N → C))
    (read : LegalTriple R (Fin N) targetVal → A → (Fin N → L))
    {αType : C → ℕ} (ambient : Finset (LegalTriple R (Fin N) targetVal))
    (hambient : ∀ c ∈ ambient, WordType.multiplicity (component c) = αType)
    (hinj : ∀ x ∈ ambient, ∀ y ∈ ambient, component x = component y → x = y)
    (a : LegalTriple R (Fin N) targetVal) (w : A) :
    (dwz63FineCompetitors ambient (dwz63SplitCompat S component read) a w).card ≤
      (S.matchableCompatible αType (S.zIndex ∘ component a) (read a w)).card := by
  classical
  refine Finset.card_le_card_of_injOn component ?_ ?_
  · intro c hc
    rw [Finset.mem_coe, mem_dwz63FineCompetitors] at hc
    obtain ⟨⟨_hne, hcmem⟩, hzc, _huse, hcompat⟩ := hc
    rw [Finset.mem_coe, SplitRequirements.mem_matchableCompatible]
    exact ⟨S.mem_matchable.mpr ⟨hambient c hcmem, hzc⟩, hcompat⟩
  · intro x hx y hy hxy
    rw [Finset.mem_coe, mem_dwz63FineCompetitors] at hx hy
    exact hinj x hx.1.2 y hy.1.2 hxy

omit [Fintype R] [DecidableEq C] [DecidableEq L] [Fintype Z] [DecidableEq Z] in
/-- **(a) `hcompetitors`, in the binder `dwz63_exists_seed_aggregateHoleFraction` carries it.** -/
theorem dwz63_hcompetitors (S : SplitRequirements C L Z)
    (component : LegalTriple R (Fin N) targetVal → (Fin N → C))
    (read : LegalTriple R (Fin N) targetVal → A → (Fin N → L))
    {αType : C → ℕ} (ambient marked : Finset (LegalTriple R (Fin N) targetVal)) (V : ℕ)
    (hambient : ∀ c ∈ ambient, WordType.multiplicity (component c) = αType)
    (hinj : ∀ x ∈ ambient, ∀ y ∈ ambient, component x = component y → x = y)
    (hV : ∀ a ∈ marked, ∀ w : A,
      (S.matchableCompatible αType (S.zIndex ∘ component a) (read a w)).card ≤ V) :
    ∀ a ∈ marked, ∀ w : A,
      (dwz63FineCompetitors ambient (dwz63SplitCompat S component read) a w).card ≤ V :=
  fun a ha w ↦ le_trans
    (card_dwz63FineCompetitors_le_card_matchableCompatible S component read ambient
      hambient hinj a w) (hV a ha w)

omit [Fintype R] [DecidableEq C] [DecidableEq L] [Fintype Z] [DecidableEq Z] in
/-- **(b) `hzIndex`**, `lemma:triple_implies_compatible` read through the encoding.

`hzHash` is the only encoding fact used: the hash's `Z`-word is determined by the component word's
`Z`-part. -/
theorem dwz63_hzIndex (S : SplitRequirements C L Z)
    (component : LegalTriple R (Fin N) targetVal → (Fin N → C))
    (read : LegalTriple R (Fin N) targetVal → A → (Fin N → L))
    (ambient marked : Finset (LegalTriple R (Fin N) targetVal))
    (hzHash : ∀ x y : LegalTriple R (Fin N) targetVal,
      S.zIndex ∘ component x = S.zIndex ∘ component y → x.zIndex = y.zIndex) :
    ∀ a ∈ marked, ∀ w : A,
      ∀ c ∈ dwz63FineCompetitors ambient (dwz63SplitCompat S component read) a w,
        c.zIndex = a.zIndex := by
  intro a _ha w c hc
  rw [mem_dwz63FineCompetitors] at hc
  exact hzHash c a hc.2.1

end Relation

/-! ## (c) Rule (ii) is vacuous in the localized picture -/

section Useless

variable {I : Type u} [Fintype I] [DecidableEq I] {n m : ℕ}
variable {Z : Type w} [Fintype Z] [DecidableEq Z]

omit [Fintype I] [Fintype Z] [DecidableEq Z] in
/-- **The localized available words are exactly the useful ones.**

Membership in `SegmentedAvailableWord seg α` is `∀ t, segmentMultiplicity seg word t = α t`, and
`def:useful_g` is `multiplicity (jointWord seg word) = usefulType`; both are the same family of
position counts. -/
theorem isUseful_of_segmentedAvailableWord (S : SplitRequirements (Fin m) I Z)
    (seg : Fin (n + 1) → Fin m) (α : Fin m → I → ℕ) (hS : S.splitCount = α)
    (w : SegmentedAvailableWord seg α) :
    S.IsUseful seg (positiveWordEquiv I n w.1) := by
  classical
  have hw := w.2
  funext p
  obtain ⟨t, a⟩ := p
  have hcount := congrFun (hw t) a
  rw [SplitRequirements.usefulType, hS]
  rw [WordType.multiplicity_eq_card_filter]
  rw [← hcount, segmentMultiplicity]
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, WordType.jointWord,
    Prod.mk.injEq]

/-- **Rule (ii) removes nothing.** -/
theorem dwz63UselessZWords_eq_empty {τ : Type v} [Fintype τ] [DecidableEq τ]
    (seg : Fin (n + 1) → Fin m) (α : Fin m → I → ℕ)
    (usefulFor : SegmentedAvailableWord seg α → τ → Prop)
    (a : τ) (huseful : ∀ w : SegmentedAvailableWord seg α, usefulFor w a) :
    dwz63UselessZWords seg α usefulFor a = ∅ := by
  classical
  refine Finset.eq_empty_of_forall_notMem ?_
  intro w hw
  simp only [dwz63UselessZWords, Finset.mem_filter, Finset.mem_univ, true_and] at hw
  exact hw (huseful w)

/-- **The rule-(ii) allowance is `0`.** -/
theorem card_dwz63UselessZWords_eq_zero {τ : Type v} [Fintype τ] [DecidableEq τ]
    (seg : Fin (n + 1) → Fin m) (α : Fin m → I → ℕ)
    (usefulFor : SegmentedAvailableWord seg α → τ → Prop)
    (a : τ) (huseful : ∀ w : SegmentedAvailableWord seg α, usefulFor w a) :
    (dwz63UselessZWords seg α usefulFor a).card = 0 := by
  rw [dwz63UselessZWords_eq_empty seg α usefulFor a huseful, Finset.card_empty]

end Useless

end AlgebraicComplexity.Examples
