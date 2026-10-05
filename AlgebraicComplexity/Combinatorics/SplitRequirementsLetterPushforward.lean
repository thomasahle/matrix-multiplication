/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Combinatorics.CompatibleSplitCount

set_option autoImplicit false

/-!
# Coarsening the split alphabet of a `SplitRequirements`

Layer 3 (`AlgebraicComplexity/Combinatorics/`).  `Combinatorics/CompatibleSplitCount.lean`
develops `[duan2023faster]`'s combination loss over a record `SplitRequirements C L Z`, where `L`
is the alphabet a position's component splits into.  Two clients of the same paper can disagree
about `L`: one may record only the *left half* of a split, another the whole *pair*.  This module
is the comparison between two such records that agree on the component and `Z` alphabets.

## There is no cardinality bridge

`SplitRequirements.matchable αType K` is `WordType.typedWordMapFiber S.zIndex αType K`, and
`matchableCompatible αType K w` is that Finset filtered by `IsCompatible · w`.  Neither mentions
`L` in its *element* type — `L` enters only through the small-block word `w`, a parameter.  So for
two records over the same `C` and `Z` the two competitor families are Finsets of one and the same
type `Finset (Fin n → C)`, and the comparison below is a **subset**, not a transported
cardinality: no injection, no bijection, and no injectivity hypothesis on the letter map.

## The one hypothesis

Everything follows from the letterwise pushforward of the split table,

`hsplit : ∀ c l, mappedType f (fun l' ↦ S'.splitCount c l') l = S.splitCount c l`,

i.e. the coarse table is the fine table summed over the fibres of `f : L' → L`.  Both halves of
`IsCompatible` are *exact profile equalities* — `BoundaryMatched` on the component rows and
`IsTypical` on the pushed `Z` rows — and an exact equality summed over a fibre partition stays an
exact equality.  The direction is therefore the free one, fine ⟹ coarse; the converse would need
`f` injective on each row's support and is not proved, because no client needs it.

## Reusable infrastructure, not a published theorem

Every declaration here is **project infrastructure**, reusable at any `SplitRequirements` record:
`mappedType_prodMap_snd_apply`, `usefulType_letterPushforward`, `typicalType_letterPushforward`,
`isCompatible_of_letterPushforward`, `matchableCompatible_subset_of_letterPushforward` and
`card_matchableCompatible_le_of_letterPushforward` are statements about pushing a split table along
an arbitrary letter map.  None of them is a theorem of the paper.  What they serve is the
comparison of the two readings of `split` that `[duan2023faster]` uses --- the left-digit
distribution of `papers/sources/2210.10173/global_value.tex:35`, the compatibility and usefulness
definitions at `:44-50`, and the compatibility probability `p_comp` computed at `:145-190` --- so
that a client stating those over the pair alphabet and a client stating them over the left-digit
alphabet can be compared.

Primary source `[duan2023faster]`: Ran Duan, Hongxun Wu and Renfei Zhou, *Faster Matrix
Multiplication via Asymmetric Hashing*, arXiv:2210.10173, section 6.1 `sec:global-algo`,
`papers/sources/2210.10173/global_value.tex:35, 44-50, 145-190`.
-/

namespace AlgebraicComplexity

open AlgebraicComplexity.WordType

open scoped BigOperators

universe u v v' w

namespace WordType

/-- A pushforward along `Prod.map id f` is, at a fixed **first** coordinate, the pushforward of
that column along `f`.  The mirror of `CompatibleSplit.mappedType_prodMap_id_apply`. -/
theorem mappedType_prodMap_snd_apply {C : Type u} [Fintype C] [DecidableEq C]
    {L' : Type v'} {L : Type v} [Fintype L'] [DecidableEq L]
    (f : L' → L) (θ : C × L' → ℕ) (c : C) (l : L) :
    mappedType (Prod.map (id : C → C) f) θ (c, l) = mappedType f (fun l' ↦ θ (c, l')) l := by
  classical
  rw [mappedType_eq_sum_ite, mappedType_eq_sum_ite, Fintype.sum_prod_type]
  rw [Finset.sum_eq_single c]
  · refine Finset.sum_congr rfl fun l' _ ↦ ?_
    simp [Prod.map, Prod.ext_iff]
  · intro c' _ hc'
    refine Finset.sum_eq_zero fun l' _ ↦ ?_
    simp [Prod.map, Prod.ext_iff, hc']
  · simp

end WordType

namespace CompatibleSplit.SplitRequirements

variable {C : Type u} {L : Type v} {L' : Type v'} {Z : Type w}
variable [Fintype C] [DecidableEq C] [Fintype L] [DecidableEq L]
variable [Fintype L'] [DecidableEq L'] [Fintype Z] [DecidableEq Z]

/-! ## The two joint profiles push forward -/

omit [Fintype L] [DecidableEq L'] [Fintype Z] [DecidableEq Z] in
/-- The usefulness profile of the coarse record is the fine one pushed along `f`. -/
theorem usefulType_letterPushforward (S' : SplitRequirements C L' Z)
    (S : SplitRequirements C L Z) (f : L' → L)
    (hsplit : ∀ c l, mappedType f (fun l' ↦ S'.splitCount c l') l = S.splitCount c l) :
    mappedType (Prod.map (id : C → C) f) S'.usefulType = S.usefulType := by
  funext p
  obtain ⟨c, l⟩ := p
  rw [WordType.mappedType_prodMap_snd_apply]
  exact hsplit c l

omit [DecidableEq C] in
/-- The typicalness profile of the coarse record is the fine one pushed along `f`.  The two
pushforwards commute, so this is `usefulType_letterPushforward` summed over the `zIndex` fibres. -/
theorem typicalType_letterPushforward (S' : SplitRequirements C L' Z)
    (S : SplitRequirements C L Z) (f : L' → L) (hz : S'.zIndex = S.zIndex)
    (hsplit : ∀ c l, mappedType f (fun l' ↦ S'.splitCount c l') l = S.splitCount c l) :
    mappedType (Prod.map (id : Z → Z) f) S'.typicalType = S.typicalType := by
  classical
  funext p
  obtain ⟨z, l⟩ := p
  rw [WordType.mappedType_prodMap_snd_apply]
  show (∑ l' ∈ letterFiber f l, S'.typicalType (z, l')) = S.typicalType (z, l)
  have hfine : ∀ l' : L', S'.typicalType (z, l') =
      ∑ c ∈ letterFiber S'.zIndex z, S'.usefulType (c, l') := by
    intro l'
    exact mappedType_prodMap_id_apply _ _ _ _
  have hcoarse : S.typicalType (z, l) =
      ∑ c ∈ letterFiber S.zIndex z, S.usefulType (c, l) :=
    mappedType_prodMap_id_apply _ _ _ _
  rw [hcoarse, ← hz]
  simp only [hfine]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ ↦ ?_
  exact hsplit c l

/-! ## Compatibility, and the competitor family -/

/-- **Compatibility pushes forward.**  A small block compatible for the fine record is compatible,
after forgetting along `f`, for the coarse one. -/
theorem isCompatible_of_letterPushforward (S' : SplitRequirements C L' Z)
    (S : SplitRequirements C L Z) (f : L' → L)
    (hz : S'.zIndex = S.zIndex) (hb : S'.boundary = S.boundary)
    (hsplit : ∀ c l, mappedType f (fun l' ↦ S'.splitCount c l') l = S.splitCount c l)
    {n : ℕ} {comp : Fin n → C} {w : Fin n → L'} (h : S'.IsCompatible comp w) :
    S.IsCompatible comp (f ∘ w) := by
  classical
  obtain ⟨hbm, htyp⟩ := h
  refine ⟨?_, ?_⟩
  · intro c hc l
    have hjoint : WordType.jointWord comp (f ∘ w) =
        (Prod.map (id : C → C) f) ∘ WordType.jointWord comp w := rfl
    rw [hjoint, WordType.multiplicity_comp_eq_mappedType,
      WordType.mappedType_prodMap_snd_apply]
    rw [← hsplit c l]
    refine congrArg (fun g : L' → ℕ ↦ mappedType f g l) ?_
    funext l'
    exact hbm c (by rw [hb]; exact hc) l'
  · show WordType.multiplicity (WordType.jointWord (S.zIndex ∘ comp) (f ∘ w)) = S.typicalType
    have hjoint : WordType.jointWord (S.zIndex ∘ comp) (f ∘ w) =
        (Prod.map (id : Z → Z) f) ∘ WordType.jointWord (S'.zIndex ∘ comp) w := by
      rw [hz]
      rfl
    rw [hjoint, WordType.multiplicity_comp_eq_mappedType, htyp]
    exact typicalType_letterPushforward S' S f hz hsplit

/-- **The competitor families are nested, in one and the same type.** -/
theorem matchableCompatible_subset_of_letterPushforward (S' : SplitRequirements C L' Z)
    (S : SplitRequirements C L Z) (f : L' → L)
    (hz : S'.zIndex = S.zIndex) (hb : S'.boundary = S.boundary)
    (hsplit : ∀ c l, mappedType f (fun l' ↦ S'.splitCount c l') l = S.splitCount c l)
    (αType : C → ℕ) {n : ℕ} (K : Fin n → Z) (w : Fin n → L') :
    S'.matchableCompatible αType K w ⊆ S.matchableCompatible αType K (f ∘ w) := by
  intro comp hcomp
  rw [mem_matchableCompatible] at hcomp
  obtain ⟨hm, hc⟩ := hcomp
  rw [mem_matchableCompatible]
  refine ⟨?_, isCompatible_of_letterPushforward S' S f hz hb hsplit hc⟩
  rw [mem_matchable] at hm
  rw [mem_matchable]
  exact ⟨hm.1, by rw [← hz]; exact hm.2⟩

/-- **The competitor count only shrinks under coarsening**, which is what a client bounding the
fine count by a coarse certificate needs. -/
theorem card_matchableCompatible_le_of_letterPushforward (S' : SplitRequirements C L' Z)
    (S : SplitRequirements C L Z) (f : L' → L)
    (hz : S'.zIndex = S.zIndex) (hb : S'.boundary = S.boundary)
    (hsplit : ∀ c l, mappedType f (fun l' ↦ S'.splitCount c l') l = S.splitCount c l)
    (αType : C → ℕ) {n : ℕ} (K : Fin n → Z) (w : Fin n → L') :
    (S'.matchableCompatible αType K w).card ≤
      (S.matchableCompatible αType K (f ∘ w)).card :=
  Finset.card_le_card
    (matchableCompatible_subset_of_letterPushforward S' S f hz hb hsplit αType K w)

end CompatibleSplit.SplitRequirements

end AlgebraicComplexity
