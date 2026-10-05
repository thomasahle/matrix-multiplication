/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoSeedInputs

set_option autoImplicit false

/-!
# `V`, by the exact integer identity

Layer 4 (`AlgebraicComplexity/Examples/`).  The last input of
`Examples/DuanWuZhouLevelTwoSeedInputs.lean`'s bridge is the numeric bound `V` on the competitor
count.  It is obtained here from the **exact** integer pair identity, with no probability and no
asymptotics.

## The identity, and the cast

`Combinatorics/CompatibleSplitCount.lean`'s
`SplitRequirements.card_matchableCompatible_mul_card_typicalSet` is the division-free statement

`|matchableCompatible α K K̂| · |T_K| = |matchable α K| · |compatibleSet comp₀|`,

an equality in `ℕ`.  `card_matchableCompatible_le_of_mul` cancels `|T_K| > 0` against any integer
`V` dominating the right-hand side, so

`V ≥ (N_α/N_Z) · p_comp` in the division-free form `N_α/N_Z · |compatible| ≤ V · |T_K|`

is exactly what a client has to certify.  `Analysis/CompatibilityRate.lean`'s
`card_matchableCompatible_eq_mul_compatibleFraction` is the same fact in `ℚ`,
`|matchableCompatible| = |matchable| · compatibleFraction`; it is *stated* there as a rational
identity and is quoted here only to name the quantity — nothing below uses it, so no rational
division or probability enters the seed selection.

## The recorded non-goal

What remains unavailable is the asymptotic form, verbatim from `Analysis/CompatibilityRate.lean`'s
"Non-goals" paragraph:

> The asymptotic statement `p_comp = ᾱ_p^{n + o(n)}` is likewise not proved here: the
> zero-tolerant method-of-types estimates that it needs (a compatibility profile has structurally
> zero rows at every interior component) are not available in the layer this module may import.

Nothing in this module or in the seed selection needs it; it is needed only to *evaluate* `V`
against the rate `ᾱ_p`, which is what
`Examples/DuanWuZhouLevelTwoJointHashBranch.lean` reports as the reason the two branches of `M₀`
cannot be merged.

## The typed relation

`Examples/DuanWuZhouLevelTwoEncodingComponent.lean` records that the joint-typicality hypothesis
`hambient` of `card_dwz63FineCompetitors_le_card_matchableCompatible` is false on the *ambient*
(marginally typical) family.  `dwz63SplitCompatTyped` carries the joint type as a fourth conjunct
of the relation instead, and `card_dwz63FineCompetitorsTyped_le_card_matchableCompatible` re-proves
the bridge with `hambient` deleted.  A hole needs a *remaining* competitor and remaining triples
are marked, so nothing is lost.

Primary source: Ran Duan, Hongxun Wu and Renfei Zhou, *Faster Matrix Multiplication via Asymmetric
Hashing*, arXiv:2210.10173, §6.2 (`global_value.tex`), `lemma:pcomp_g`, `claim:hole_frac_low`.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor ProgressionHash CompatibleSplit
open scoped BigOperators

universe u v w x

section Count

variable {C : Type u} [Fintype C] [DecidableEq C]
variable {L : Type v} [Fintype L] [DecidableEq L]
variable {Z : Type w} [Fintype Z] [DecidableEq Z]
variable {N : ℕ}

/-- **`V` from the exact integer pair identity.** -/
theorem card_matchableCompatible_le_of_mul (S : SplitRequirements C L Z)
    {αType : C → ℕ} {K : Fin N → Z} {comp₀ : Fin N → C} (hcomp₀ : comp₀ ∈ S.matchable αType K)
    {w : Fin N → L} (hw : w ∈ S.typicalSet K) (htyp : 0 < (S.typicalSet K).card) {V : ℕ}
    (hV : (S.matchable αType K).card * (S.compatibleSet comp₀).card ≤ V * (S.typicalSet K).card) :
    (S.matchableCompatible αType K w).card ≤ V := by
  have hpair := SplitRequirements.card_matchableCompatible_mul_card_typicalSet (S := S) hcomp₀ hw
  have hstep : (S.matchableCompatible αType K w).card * (S.typicalSet K).card ≤
      V * (S.typicalSet K).card := by
    rw [hpair]
    exact hV
  exact Nat.le_of_mul_le_mul_right hstep htyp

end Count

/-! ## The typed competitor relation -/

section Typed

variable {R : Type x} [Field R] {N : ℕ} {targetVal : R}
variable {C : Type u} [Fintype C] [DecidableEq C]
variable {L : Type v} [Fintype L] [DecidableEq L]
variable {Z : Type w} [Fintype Z] [DecidableEq Z]
variable {A : Type v}

/-- **Step 2's rule (i), with the competitor's joint type carried in the relation.** -/
def dwz63SplitCompatTyped (S : SplitRequirements C L Z)
    (component : LegalTriple R (Fin N) targetVal → (Fin N → C))
    (read : LegalTriple R (Fin N) targetVal → A → (Fin N → L)) (αType : C → ℕ)
    (a : LegalTriple R (Fin N) targetVal) (w : A)
    (c : LegalTriple R (Fin N) targetVal) : Prop :=
  WordType.multiplicity (component c) = αType ∧ dwz63SplitCompat S component read a w c

omit [DecidableEq C] [DecidableEq L] [Fintype Z] [DecidableEq Z] in
/-- **The competitor bridge, with `hambient` deleted.** -/
theorem card_dwz63FineCompetitorsTyped_le_card_matchableCompatible (S : SplitRequirements C L Z)
    (component : LegalTriple R (Fin N) targetVal → (Fin N → C))
    (read : LegalTriple R (Fin N) targetVal → A → (Fin N → L)) (αType : C → ℕ)
    (ambient : Finset (LegalTriple R (Fin N) targetVal))
    (hinj : ∀ x ∈ ambient, ∀ y ∈ ambient, component x = component y → x = y)
    (a : LegalTriple R (Fin N) targetVal) (w : A) :
    (dwz63FineCompetitors ambient (dwz63SplitCompatTyped S component read αType) a w).card ≤
      (S.matchableCompatible αType (S.zIndex ∘ component a) (read a w)).card := by
  classical
  refine Finset.card_le_card_of_injOn component ?_ ?_
  · intro c hc
    rw [Finset.mem_coe, mem_dwz63FineCompetitors] at hc
    obtain ⟨⟨_hne, _hcmem⟩, htype, hzc, _huse, hcompat⟩ := hc
    rw [Finset.mem_coe, SplitRequirements.mem_matchableCompatible]
    exact ⟨S.mem_matchable.mpr ⟨htype, hzc⟩, hcompat⟩
  · intro x hx y hy hxy
    rw [Finset.mem_coe, mem_dwz63FineCompetitors] at hx hy
    exact hinj x hx.1.2 y hy.1.2 hxy

omit [DecidableEq C] [DecidableEq L] [Fintype Z] [DecidableEq Z] in
/-- **`hcompetitors` at the typed relation.** -/
theorem dwz63_hcompetitorsTyped (S : SplitRequirements C L Z)
    (component : LegalTriple R (Fin N) targetVal → (Fin N → C))
    (read : LegalTriple R (Fin N) targetVal → A → (Fin N → L)) (αType : C → ℕ)
    (ambient marked : Finset (LegalTriple R (Fin N) targetVal)) (V : ℕ)
    (hinj : ∀ x ∈ ambient, ∀ y ∈ ambient, component x = component y → x = y)
    (hV : ∀ a ∈ marked, ∀ w : A,
      (S.matchableCompatible αType (S.zIndex ∘ component a) (read a w)).card ≤ V) :
    ∀ a ∈ marked, ∀ w : A,
      (dwz63FineCompetitors ambient (dwz63SplitCompatTyped S component read αType) a w).card ≤
        V :=
  fun a ha w ↦ le_trans
    (card_dwz63FineCompetitorsTyped_le_card_matchableCompatible S component read αType ambient
      hinj a w) (hV a ha w)

omit [DecidableEq C] [DecidableEq L] [Fintype Z] [DecidableEq Z] in
/-- **`hzIndex` at the typed relation.**  The encoding fact is asked only where it is used:
competitors run in `ambient`, owners in `marked`. -/
theorem dwz63_hzIndexTyped (S : SplitRequirements C L Z)
    (component : LegalTriple R (Fin N) targetVal → (Fin N → C))
    (read : LegalTriple R (Fin N) targetVal → A → (Fin N → L)) (αType : C → ℕ)
    (ambient marked : Finset (LegalTriple R (Fin N) targetVal))
    (hzHash : ∀ x ∈ ambient, ∀ y ∈ marked,
      S.zIndex ∘ component x = S.zIndex ∘ component y → x.zIndex = y.zIndex) :
    ∀ a ∈ marked, ∀ w : A,
      ∀ c ∈ dwz63FineCompetitors ambient (dwz63SplitCompatTyped S component read αType) a w,
        c.zIndex = a.zIndex := by
  intro a ha w c hc
  rw [mem_dwz63FineCompetitors] at hc
  exact hzHash c hc.1.2 a ha hc.2.2.1

/-- **`hV` from the exact integer identity**, with the typicality premise supplied by
`dwz63SplitCompat_isTypical`. -/
theorem dwz63_hV_of_mul (S : SplitRequirements C L Z)
    (component : LegalTriple R (Fin N) targetVal → (Fin N → C))
    (read : LegalTriple R (Fin N) targetVal → A → (Fin N → L)) (αType : C → ℕ)
    (marked : Finset (LegalTriple R (Fin N) targetVal)) (V : ℕ)
    (huseful : ∀ a ∈ marked, ∀ w : A, S.IsUseful (component a) (read a w))
    (hcompType : ∀ a ∈ marked, WordType.multiplicity (component a) = αType)
    (hprod : ∀ a ∈ marked,
      (S.matchable αType (S.zIndex ∘ component a)).card *
          (S.compatibleSet (component a)).card ≤
        V * (S.typicalSet (S.zIndex ∘ component a)).card) :
    ∀ a ∈ marked, ∀ w : A,
      (S.matchableCompatible αType (S.zIndex ∘ component a) (read a w)).card ≤ V := by
  intro a ha w
  have hw : read a w ∈ S.typicalSet (S.zIndex ∘ component a) :=
    dwz63SplitCompat_isTypical (A := A) S (component := component) (read := read)
      (huseful a ha w)
  have htyp : 0 < (S.typicalSet (S.zIndex ∘ component a)).card :=
    Finset.card_pos.mpr ⟨read a w, hw⟩
  exact card_matchableCompatible_le_of_mul S
    (S.mem_matchable.mpr ⟨hcompType a ha, rfl⟩) hw htyp (hprod a ha)

end Typed

end AlgebraicComplexity.Examples
