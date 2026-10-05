/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoCompetitorBound
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoCountingSplit

set_option autoImplicit false

/-!
# `p_comp` does not depend on the block it is measured at

Layer 4 (`AlgebraicComplexity/Examples/`).  `[duan2023faster]` introduces `p_comp` at
`papers/sources/2210.10173/global_value.tex:135` as "the probability of a small block `Z_K̂`
being compatible with a random triple `(X_I, Y_J, Z_K)`", and builds the hashing modulus
`M₀ = 8 · max(N_triple/N_X, N_α · p_comp/N_Z)` from it at `:137`.  The definition at `:176-180`
closes with the paper's own uniformity claim,

> Similar to \cref{sec:2nd}, due to symmetry, `p_comp` is independent of which block `Z_K̂` we
> choose. (`:179`)

and the proof of `lemma:pcomp_g` (`:182-196`) opens by using it:

> Since `p_comp` is identical for all `Z_K̂ ∈ T`, it will also be the same for a uniformly
> randomly chosen `Z_K̂ ∈ T`. (`:198`)

This module transcribes those two sentences on the **left-digit** split record
`dwz63Split` --- the record whose letter is the left half `K̂_{2t-1}` of a split, which is what
`split(K̂, S)` means at `:35`.  What comes out is the uniform competitor bound a client needs
in order to instantiate one and the same `V` in the modulus condition `M₀` and in the
competitor-count hypothesis of the seed selection.

## The content, and why it is exactly the paper's symmetry step

`dwz63CompetitorBound S α K comp₀ = ⌈|matchable α K| · |compatibleSet comp₀| / |T_K|⌉`
(`Examples/DuanWuZhouLevelTwoCompetitorBound.lean:82`) is the integer form of the paper's
`N_α/N_Z · p_comp`.  Each of its three factors is a *type* invariant:

* `|matchable α K|` is a typed coordinatewise fibre over `K`, so
  `card_typedWordMapFiber_eq_of_multiplicity_eq` makes it a function of `multiplicity K` alone;
* `|T_K|` is a conditional type class over `K`, and
  `card_conditionalTypeClass_eq_typedWordMapFiber` turns it into the same kind of fibre;
* `|compatibleSet comp₀|` is a function of `multiplicity comp₀` alone, by the committed
  `card_compatibleSet_eq_of_multiplicity_eq` --- itself annotated as "the first of the two 'due
  to symmetry' steps of `lemma:pcomp_g`".

For any `K` with a matchable triple at all, `multiplicity K = mappedType zIndex α` is
forced, so all three factors --- and hence the whole quotient --- agree with their values at any
chosen reference pair.  That is the paper's `:179`/`:198` sentence, with "due to symmetry"
replaced by the finite reindexing the committed lemmas perform.

## Uniformity over the small block is free

`matchableCompatible α K w` is `matchable α K` filtered by `IsCompatible · w`, and
`IsCompatible comp w` contains `IsTypical (zIndex ∘ comp) w`
(`Combinatorics/CompatibleSplitCountDefs.lean:122`).  A member therefore *forces*
`w ∈ T_K`; when `w` is not typical the family is empty and the bound is free.  So no
typicalness hypothesis on `w` is needed, and the count is bounded uniformly over **all**
`(K, w)`, not only over the retained ones --- which is what
`dwz63_hV_pair_of_hV` (`Examples/DuanWuZhouLevelTwoSplitAlphabetBridge.lean:192`) has to be fed
in order to carry the coarse bound to the pair alphabet the hole side reads.

Primary source `[duan2023faster]`: Ran Duan, Hongxun Wu and Renfei Zhou, *Faster Matrix
Multiplication via Asymmetric Hashing*, arXiv:2210.10173, §6.2 `sec:global-value`,
`papers/sources/2210.10173/global_value.tex:35, 135, 137, 176-198` (`lemma:pcomp_g`).
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor CompatibleSplit

universe u v w

section Invariance

variable {C : Type u} [Fintype C] [DecidableEq C]
variable {L : Type v} [Fintype L] [DecidableEq L]
variable {Z : Type w} [Fintype Z] [DecidableEq Z]
variable {N : ℕ}

omit [DecidableEq C] [Fintype L] [DecidableEq L] [DecidableEq Z] in
/-- **`N_α/N_Z` depends on the large Z-block only through its type** (`global_value.tex:179`).

Proof sketch: `matchable` is by definition the typed coordinatewise fibre of `zIndex` over `K`,
and `card_typedWordMapFiber_eq_of_multiplicity_eq` reindexes positions by a permutation carrying
one target word to the other. -/
theorem dwz63_card_matchable_eq_of_multiplicity_eq (S : SplitRequirements C L Z)
    (αType : C → ℕ) {K K' : Fin N → Z}
    (h : WordType.multiplicity K = WordType.multiplicity K') :
    (S.matchable αType K).card = (S.matchable αType K').card :=
  WordType.card_typedWordMapFiber_eq_of_multiplicity_eq S.zIndex αType K K' h

omit [DecidableEq C] [DecidableEq L] [DecidableEq Z] in
/-- **`|T_K|` depends on the large Z-block only through its type** (`global_value.tex:198`).

Proof sketch: `card_conditionalTypeClass_eq_typedWordMapFiber` presents `T_K` as the typed
fibre of `Prod.fst` over `K` at the joint profile `γ`, and those have equal size over words of
equal type. -/
theorem dwz63_card_typicalSet_eq_of_multiplicity_eq (S : SplitRequirements C L Z)
    {K K' : Fin N → Z} (h : WordType.multiplicity K = WordType.multiplicity K') :
    (S.typicalSet K).card = (S.typicalSet K').card := by
  have hfib : ∀ J : Fin N → Z, (S.typicalSet J).card =
      (WordType.typedWordMapFiber Prod.fst S.typicalType J).card := fun J ↦
    WordType.card_conditionalTypeClass_eq_typedWordMapFiber J S.typicalType
  rw [hfib, hfib]
  exact WordType.card_typedWordMapFiber_eq_of_multiplicity_eq Prod.fst S.typicalType K K' h

omit [DecidableEq C] [DecidableEq L] [DecidableEq Z] in
/-- **The competitor bound is the same at every matchable pair** (`global_value.tex:179, 198`).

This is the paper's "due to symmetry, `p_comp` is independent of which block `Z_K̂` we choose",
in the integer form the seed selection consumes: membership in `matchable` pins
`multiplicity comp = α` and `zIndex ∘ comp = K`, so `multiplicity K = mappedType zIndex α` is
the same for both pairs and all three factors of the quotient agree. -/
theorem dwz63_competitorBound_eq_of_mem_matchable (S : SplitRequirements C L Z) (αType : C → ℕ)
    {K K' : Fin N → Z} {comp comp' : Fin N → C}
    (h : comp ∈ S.matchable αType K) (h' : comp' ∈ S.matchable αType K') :
    dwz63CompetitorBound S αType K comp = dwz63CompetitorBound S αType K' comp' := by
  obtain ⟨htype, hK⟩ := S.mem_matchable.mp h
  obtain ⟨htype', hK'⟩ := S.mem_matchable.mp h'
  have hmul : WordType.multiplicity K = WordType.multiplicity K' := by
    rw [← hK, ← hK', WordType.multiplicity_comp_eq_mappedType,
      WordType.multiplicity_comp_eq_mappedType, htype, htype']
  have hcompat : (S.compatibleSet comp).card = (S.compatibleSet comp').card :=
    S.card_compatibleSet_eq_of_multiplicity_eq (by rw [htype, htype'])
  unfold dwz63CompetitorBound
  rw [dwz63_card_matchable_eq_of_multiplicity_eq S αType hmul, hcompat,
    dwz63_card_typicalSet_eq_of_multiplicity_eq S hmul]

/-- **The uniform competitor bound at a single reference pair.**

`hV` for *every* large Z-block and *every* small block, at the value the bound takes at one
chosen matchable pair.  A non-typical small block contributes nothing: a member of
`matchableCompatible α K w` carries `IsCompatible comp w`, whose second conjunct is
`IsTypical (zIndex ∘ comp) w = IsTypical K w`.

Proof sketch: if the family is empty the bound is vacuous; otherwise a member supplies both a
matchable triple through `K` and the typicalness of `w`, so
`card_matchableCompatible_le_of_mul` applies at the local bound, which
`dwz63_competitorBound_eq_of_mem_matchable` identifies with the reference one. -/
theorem dwz63_uniform_hV_of_mem_matchable (S : SplitRequirements C L Z) (αType : C → ℕ)
    {K₀ : Fin N → Z} {comp₀ : Fin N → C} (h₀ : comp₀ ∈ S.matchable αType K₀) :
    ∀ (K : Fin N → Z) (w : Fin N → L),
      (S.matchableCompatible αType K w).card ≤ dwz63CompetitorBound S αType K₀ comp₀ := by
  intro K w
  rcases Finset.eq_empty_or_nonempty (S.matchableCompatible αType K w) with
    hempty | ⟨comp, hcomp⟩
  · rw [hempty]
    exact Nat.zero_le _
  · rw [S.mem_matchableCompatible] at hcomp
    obtain ⟨hmem, hcompat⟩ := hcomp
    have hK : S.zIndex ∘ comp = K := (S.mem_matchable.mp hmem).2
    have hw : w ∈ S.typicalSet K := by
      rw [S.mem_typicalSet, ← hK]
      exact hcompat.2
    have htyp : 0 < (S.typicalSet K).card := Finset.card_pos.mpr ⟨w, hw⟩
    refine card_matchableCompatible_le_of_mul S hmem hw htyp ?_
    rw [← dwz63_competitorBound_eq_of_mem_matchable S αType hmem h₀]
    exact dwz63_competitorBound_spec S αType K comp htyp

end Invariance

/-! ## At the section 6.3 left-digit record -/

/-- **The uniform left-record competitor bound** (`global_value.tex:35, 179, 198`).

`dwz63Split s` is the record whose letter is the left digit `K̂_{2t-1}` of a split (`:35`), which
is the alphabet `p_comp` is computed on in `lemma:pcomp_g`.  Any component word of the prescribed
type serves as the reference pair, so the single value
`dwz63CompetitorBound (dwz63Split s) α (dwz63ZIndex ∘ comp₀) comp₀` --- the one the cofinal
degree comparison of `Examples/DuanWuZhouLevelTwoCofinalCompetitorDegree.lean:348` and the modulus
branch of `Examples/DuanWuZhouLevelTwoPlainModulusBranch.lean:112` already bound --- bounds the
competitor family at every `(K, w)`.  Feeding it to `dwz63_hV_pair_of_hV` transports it to the
pair alphabet at the same value. -/
theorem dwz63_uniform_hV_coarse (s : ℕ) (αType : Fin 15 → ℕ) {N : ℕ}
    (comp₀ : Fin N → Fin 15) (hcomp₀ : WordType.multiplicity comp₀ = αType) :
    ∀ (K : Fin N → Fin 5) (w : Fin N → Fin 3),
      ((dwz63Split s).matchableCompatible αType K w).card ≤
        dwz63CompetitorBound (dwz63Split s) αType (dwz63ZIndex ∘ comp₀) comp₀ :=
  dwz63_uniform_hV_of_mem_matchable (dwz63Split s) αType
    ((dwz63Split s).mem_matchable.mpr ⟨hcomp₀, rfl⟩)

end AlgebraicComplexity.Examples
