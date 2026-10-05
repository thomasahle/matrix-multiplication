/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Combinatorics.CompatibleSplitCountDefs

/-!
# Compatible split counting: the finite core of the Duan--Wu--Zhou combination loss

Layer 2 (`AlgebraicComplexity/Combinatorics/`).  This module formalizes the counting layer of

> R. Duan, H. Wu and R. Zhou, *Faster Matrix Multiplication via Asymmetric Hashing*,
> arXiv:2210.10173v5, **§6.2 (`global_value.tex`)**: `def:global-compatible`, `def:useful_g`,
> the typicalness distribution and its `Claim`, `lemma:pcomp_g`, and the competitor count inside
> `claim:hole_frac_low` (`[DuanWuZhou2022]`).

## The situation being modelled

Fix a level-`ℓ` triple `(X_I, Y_J, Z_K)` of large blocks of `(CW_q^{⊗2^{ℓ-1}})^{⊗n}`.  Each
position `t ∈ [n]` carries a *component* `(I_t, J_t, K_t) = (i,j,k)`; this module abstracts the
component set to a finite alphabet `C` and records only the two features DWZ's compatibility
definition actually reads:

* `zIndex : C → Z`, the Z-index `k` of a component (`Z` abstracts `{0, …, 2^ℓ}`);
* `boundary : C → Bool`, DWZ's degeneracy test `i = 0 ∨ j = 0`.

A small Z-block `Z_K̂ ∈ Z_K` splits, at each position `t`, that position's Z-index as
`k = k_l + k_r`; since `k_r` is determined by `k` and `k_l`, a small block is a word
`w : Fin n → L` over the finite alphabet `L` of left halves.  A component word
`comp : Fin n → C` is the position-by-position record of the large triple, so `zIndex ∘ comp` is
the large Z-block `K` itself.

The prescribed split distributions `α̃_{i,j,k}` enter as an integral profile
`splitCount : C → L → ℕ`, where `splitCount c l` is `n · α(c) · α̃_c(l)`: the number of positions
of component `c` at which the split must take the left half `l`.

## Principal results

* `SplitRequirements.isCompatible_iff_mem_compatibleSet` — **the requirement-partition identity**,
  the paper's one asserted combinatorial sentence.  DWZ's compatibility, defined as the
  conjunction of the per-Z-index *average* condition (b) and the *boundary-component* condition
  (a), is equivalent to a single conditional word-type membership over the requirement alphabet
  `C ⊕ Z`, whose fibers are the position sets `{S_{i,j,k} : i = 0 ∨ j = 0}` together with the
  pooled sets `S_{+,+,k}`.  Because the requirement of a position is a *function of its
  component*, the paper's "every index position `t ∈ [n]` belongs to the set `S` of exactly one
  requirement" is not an extra hypothesis: it is the statement that these sets are the fibers of
  `requirement ∘ comp`.
* `SplitRequirements.multinomial_zType_mul_card_typicalSet` — the exact division-free form of
  `|T_K| = C(n, [nγ]) / C(n, [nα_Z])`.  The typicalness distribution `γ` is `typicalType`, the
  pushforward of the split profile along `zIndex`.
* `SplitRequirements.multinomial_reqType_mul_card_compatibleSet` — the same for the numerator of
  `lemma:pcomp_g`: the number of compatible small blocks.
* `SplitRequirements.card_matchableCompatible_mul_card_typicalSet` — **the pair count** that
  `claim:hole_frac_low` needs: for *every* typical small block, the number of large triples
  through `Z_K` compatible with it, times `|T_K|`, equals the number of large triples through
  `Z_K` times the compatible-block count.  This is the exact division-free form of DWZ's
  `N_α · p_comp / N_Z`, the analogue of `hashing.tex` l.53's `N_α · N_triple / N_X`.

Both "due to symmetry" steps of `lemma:pcomp_g` are discharged, and neither needs the paper's
orbit count:

* the compatible-block count is the same for every large triple through `Z_K`, because
  `card_conditionalTypeClass_eq_typedWordMapFiber` makes it depend on the component word only
  through its multiplicity type (`card_compatibleSet_eq_of_multiplicity_eq`);
* the compatible-triple count is the same for every *typical* small block, by transporting along
  `WordType.positionPermOfSameMultiplicity` applied to the joint word `(K, w)`; the resulting
  permutation fixes `K` and carries one typical block to the other
  (`card_matchableCompatible_eq_of_mem_typicalSet`).

## Layout

The definitions this module reasons about — `SplitRequirements` and its `requirement`/`reqIndex`
alphabet, the three profiles `usefulType`/`typicalType`/`compatibleType`, the predicates
`IsTypical`/`BoundaryMatched`/`IsCompatible`/`IsUseful`, the finsets
`typicalSet`/`compatibleSet`/`usefulSet`, the hypothesis `RefinesType` and the competitor families
`matchable`/`matchableCompatible` — live one module below, in
`Combinatorics/CompatibleSplitCountDefs.lean`, which this file imports and re-exports.  Clients
that only need to state DWZ compatibility should import that leaf instead; clients that need the
counts import this file exactly as before.  No public name and no import path changed when the two
were separated.

## Naming

DWZ's *combination loss* is `1 / p_comp`, the reciprocal of the ratio computed here.  It is
**not** the repository's existing `combinationLoss` (`Probability/TwoLetter.lean`,
`MatrixMultiplication/RationalTypedLeaf.lean`), which is the entropy deficit against the
maximum-entropy point of a marginal fiber — that is DWZ's *hash loss*.  Nothing in this module
uses the name `combinationLoss`; the exponential rate is `compatibilityRate` in
`MatrixMultiplication/CompatibilityRate.lean`.

## Non-goals

No asymptotics and no entropy: this module is exact finite counting only.  The rate `ᾱ_p`, its
closed form and the hole-fraction bound live in `MatrixMultiplication/CompatibilityRate.lean`.
No tensor appears; the bridge to the compatibility *zeroing-out* of a partitioned tensor is
`MatrixMultiplication/MoreAsymmetryCompatibility*.lean`, consumed but not modified by the DWZ
campaign.
-/

namespace AlgebraicComplexity.CompatibleSplit

open AlgebraicComplexity.WordType
open scoped BigOperators

universe u v w

variable {C : Type u} {L : Type v} {Z : Type w}

namespace SplitRequirements

variable [Fintype C] [DecidableEq C] [Fintype L] [DecidableEq L] [Fintype Z] [DecidableEq Z]
variable (S : SplitRequirements C L Z)

omit [Fintype C] [DecidableEq C] [Fintype L] [DecidableEq L] [Fintype Z] [DecidableEq Z] in
/-- A component sits in the boundary cell of `c` exactly when it is `c` and `c` is a boundary
component. -/
theorem requirement_eq_inl_iff (c c' : C) :
    S.requirement c' = Sum.inl c ↔ (S.boundary c' = true ∧ c' = c) := by
  unfold requirement
  by_cases hc' : S.boundary c' <;> simp [hc']

omit [Fintype L] [DecidableEq L] [Fintype Z] [DecidableEq Z] in
omit [DecidableEq C] in
/-- The `requirement`-fiber of a boundary cell is the singleton of that component, and the fiber
of a non-boundary cell is empty.  This is why condition (a) of `def:global-compatible` reads off
exactly the `Sum.inl` rows of the requirement profile. -/
theorem letterFiber_requirement_inl (c : C) :
    letterFiber S.requirement (Sum.inl c) = if S.boundary c then {c} else ∅ := by
  classical
  ext c'
  rw [mem_letterFiber, S.requirement_eq_inl_iff c c']
  by_cases hc : S.boundary c = true
  · rw [if_pos hc, Finset.mem_singleton]
    exact ⟨fun h ↦ h.2, fun h ↦ ⟨h ▸ hc, h⟩⟩
  · rw [if_neg hc]
    constructor
    · rintro ⟨hb, rfl⟩
      exact absurd hb hc
    · intro h
      simp at h

/-! ### Evaluating pushforwards along a first-coordinate map -/

/-- A pushforward along `Prod.map f id` is, at a fixed second coordinate, the pushforward of that
row along `f`.  Unfolded, both sides sum the joint profile over the `f`-fiber. -/
theorem mappedType_prodMap_id_apply {A B : Type*} [Fintype A] [DecidableEq B]
    (f : A → B) (θ : A × L → ℕ) (b : B) (l : L) :
    mappedType (Prod.map f (id : L → L)) θ (b, l) = mappedType f (fun a ↦ θ (a, l)) b := by
  classical
  rw [mappedType_eq_sum_ite, mappedType_eq_sum_ite, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  rw [Finset.sum_eq_single l]
  · simp [Prod.map, Prod.ext_iff]
  · intro l' _ hl'
    simp [Prod.map, Prod.ext_iff, hl']
  · simp

omit [Fintype Z] in
/-- The boundary rows of a requirement pushforward are the corresponding component rows, and
vanish off the boundary components. -/
theorem mappedType_requirement_inl (θ : C × L → ℕ) (c : C) (l : L) :
    mappedType (Prod.map S.requirement (id : L → L)) θ (Sum.inl c, l) =
      if S.boundary c then θ (c, l) else 0 := by
  classical
  rw [mappedType_prodMap_id_apply]
  show (∑ c' ∈ letterFiber S.requirement (Sum.inl c), θ (c', l)) = _
  rw [S.letterFiber_requirement_inl c]
  by_cases hc : S.boundary c = true
  · rw [if_pos hc, if_pos hc, Finset.sum_singleton]
  · rw [if_neg hc, if_neg hc, Finset.sum_empty]

omit [DecidableEq C] in
/-- The pushforward of a requirement-indexed profile along `reqIndex` splits into the boundary
rows over the given Z-index plus the single pooled row of that Z-index.  This is the finite form
of "the requirements of type (a) and (c) over a fixed `k` exhaust `S_{*,*,k}`". -/
theorem mappedType_reqIndex_apply (σ : (C ⊕ Z) × L → ℕ) (z : Z) (l : L) :
    mappedType (Prod.map S.reqIndex (id : L → L)) σ (z, l) =
      mappedType S.zIndex (fun c ↦ σ (Sum.inl c, l)) z + σ (Sum.inr z, l) := by
  classical
  rw [mappedType_prodMap_id_apply, mappedType_eq_sum_ite, mappedType_eq_sum_ite,
    Fintype.sum_sum_type]
  have h1 : ∀ c : C, (if S.reqIndex (Sum.inl c) = z then σ (Sum.inl c, l) else 0) =
      (if S.zIndex c = z then σ (Sum.inl c, l) else 0) := fun _ ↦ rfl
  have h2 : (∑ z' : Z, if S.reqIndex (Sum.inr z') = z then σ (Sum.inr z', l) else 0) =
      σ (Sum.inr z, l) := by
    refine (Finset.sum_eq_single z (fun z' _ hz' ↦ ?_)
      (fun h ↦ absurd (Finset.mem_univ z) h)).trans ?_
    · simp [reqIndex, hz']
    · simp [reqIndex]
  simp only [h1, h2]

omit [Fintype Z] in
/-- The boundary rows of the compatibility profile are the prescribed split counts of the
boundary components, and vanish elsewhere. -/
theorem compatibleType_inl (c : C) (l : L) :
    S.compatibleType (Sum.inl c, l) = if S.boundary c then S.splitCount c l else 0 :=
  S.mappedType_requirement_inl S.usefulType c l

omit [Fintype Z] in
/-- The pooled rows of the compatibility profile, in the computable "sum over components" form:
`α(+,+,k) · α̃^{avg}_{+,+,k}` in integral form. -/
theorem compatibleType_inr (z : Z) (l : L) :
    S.compatibleType (Sum.inr z, l) =
      ∑ c, if S.requirement c = Sum.inr z then S.splitCount c l else 0 := by
  classical
  rw [compatibleType, mappedType_prodMap_id_apply, mappedType_eq_sum_ite]
  rfl

omit [DecidableEq C] [Fintype Z] in
/-- The rows of the typicalness profile, in the computable "sum over components" form:
`α_Z(k) · α̃^{avg}_{*,*,k}` in integral form. -/
theorem typicalType_apply (z : Z) (l : L) :
    S.typicalType (z, l) = ∑ c, if S.zIndex c = z then S.splitCount c l else 0 := by
  classical
  rw [typicalType, mappedType_prodMap_id_apply, mappedType_eq_sum_ite]
  rfl

/-! ### The requirement-partition identity -/

omit [DecidableEq C] in
/-- **Requirement partition, arithmetic core.**  Two requirement-indexed profiles that agree on
all boundary rows agree everywhere as soon as their `reqIndex`-pushforwards agree.

This is DWZ's "we subtract (a) from (b)".  Its content is that over a fixed Z-index the boundary
rows and the single pooled row exhaust the fiber, so cancelling the (equal) boundary rows from
the two (equal) pushforward sums leaves exactly the pooled rows. -/
theorem eq_of_mappedType_reqIndex_eq {σ π : (C ⊕ Z) × L → ℕ}
    (hboundary : ∀ c l, σ (Sum.inl c, l) = π (Sum.inl c, l))
    (hpush : mappedType (Prod.map S.reqIndex (id : L → L)) σ =
      mappedType (Prod.map S.reqIndex (id : L → L)) π) :
    σ = π := by
  funext p
  obtain ⟨r, l⟩ := p
  cases r with
  | inl c => exact hboundary c l
  | inr z =>
      have h := congrFun hpush (z, l)
      rw [S.mappedType_reqIndex_apply σ z l, S.mappedType_reqIndex_apply π z l] at h
      have hrow : mappedType S.zIndex (fun c ↦ σ (Sum.inl c, l)) z =
          mappedType S.zIndex (fun c ↦ π (Sum.inl c, l)) z := by
        congr 1
        funext c
        exact hboundary c l
      omega

/-! ### Typical, compatible and useful small blocks: characterizations -/

variable {n : ℕ}

omit [Fintype L] [DecidableEq L] in
/-- Pairing a composed coarse word with a refinement is the coordinatewise pushforward of the
pairing. -/
theorem jointWord_comp {A B : Type*} (f : A → B) (word : Fin n → A) (w : Fin n → L) :
    jointWord (f ∘ word) w = (Prod.map f (id : L → L)) ∘ jointWord word w := rfl

/-- **The requirement-partition identity.**  A small block is compatible with a large triple in
DWZ's sense — condition (2) on every boundary component together with condition (1), the average
split condition on every `S_{*,*,k}` — exactly when its joint word with the *requirement* word
has the compatibility profile.

Proof sketch: write `θ` for the joint type of `(comp, w)` over `C × L`.  Condition (2) says the
boundary rows of `mappedType (Prod.map requirement id) θ` agree with those of `compatibleType`
(`mappedType_requirement_inl`), and condition (1) says their `reqIndex`-pushforwards agree, since
`reqIndex ∘ requirement = zIndex` and `mappedType_comp` turns the two-step pushforward into the
one-step pushforward along `zIndex`.  Together these give equality of the two profiles by
`eq_of_mappedType_reqIndex_eq`, whose content is precisely DWZ's "subtract (a) from (b)"; the
converse re-reads the two halves off that equality.  The requirement position sets are the fibers
of `requirement ∘ comp`, so the paper's assertion that every position lies in exactly one
requirement is discharged by construction rather than assumed. -/
theorem isCompatible_iff_mem_compatibleSet (comp : Fin n → C) (w : Fin n → L) :
    S.IsCompatible comp w ↔ w ∈ S.compatibleSet comp := by
  classical
  set θ := multiplicity (jointWord comp w) with hθ
  have hreq : multiplicity (jointWord (S.requirement ∘ comp) w) =
      mappedType (Prod.map S.requirement (id : L → L)) θ := by
    rw [jointWord_comp, multiplicity_comp_eq_mappedType]
  have hz : multiplicity (jointWord (S.zIndex ∘ comp) w) =
      mappedType (Prod.map S.zIndex (id : L → L)) θ := by
    rw [jointWord_comp, multiplicity_comp_eq_mappedType]
  have hcompose : (Prod.map S.reqIndex (id : L → L)) ∘ (Prod.map S.requirement (id : L → L)) =
      Prod.map S.zIndex (id : L → L) := by
    funext p
    simp [Prod.map, S.reqIndex_requirement]
  have hpushθ : mappedType (Prod.map S.reqIndex (id : L → L))
      (mappedType (Prod.map S.requirement (id : L → L)) θ) =
      mappedType (Prod.map S.zIndex (id : L → L)) θ := by
    rw [mappedType_comp, hcompose]
  have hpushU : mappedType (Prod.map S.reqIndex (id : L → L)) S.compatibleType = S.typicalType := by
    rw [compatibleType, mappedType_comp, hcompose, typicalType]
  constructor
  · rintro ⟨hb, ht⟩
    rw [mem_compatibleSet, hreq]
    refine S.eq_of_mappedType_reqIndex_eq (fun c l ↦ ?_) ?_
    · rw [S.mappedType_requirement_inl θ c l, S.compatibleType_inl c l]
      by_cases hc : S.boundary c = true
      · rw [if_pos hc, if_pos hc]
        exact hb c hc l
      · rw [if_neg hc, if_neg hc]
    · rw [hpushθ, hpushU]
      rw [IsTypical, hz] at ht
      exact ht
  · intro hmem
    rw [mem_compatibleSet, hreq] at hmem
    constructor
    · intro c hc l
      have h := congrFun hmem (Sum.inl c, l)
      rw [S.mappedType_requirement_inl θ c l, S.compatibleType_inl c l] at h
      rw [if_pos hc, if_pos hc] at h
      exact h
    · rw [IsTypical, hz, ← hpushθ, hmem, hpushU]

/-- Compatible small blocks are typical: this is condition (1) of `def:global-compatible`. -/
theorem mem_typicalSet_of_mem_compatibleSet {comp : Fin n → C} {w : Fin n → L}
    (h : w ∈ S.compatibleSet comp) : w ∈ S.typicalSet (S.zIndex ∘ comp) :=
  S.mem_typicalSet.2 ((S.isCompatible_iff_mem_compatibleSet comp w).2 h).2

omit [DecidableEq C] [DecidableEq L] [DecidableEq Z] in
/-- Useful small blocks are compatible.  DWZ's usefulness constrains the split on **all**
components, compatibility only on the boundary ones and on the pooled averages. -/
theorem mem_compatibleSet_of_mem_usefulSet {comp : Fin n → C} {w : Fin n → L}
    (h : w ∈ S.usefulSet comp) : w ∈ S.compatibleSet comp := by
  rw [S.mem_usefulSet, IsUseful] at h
  rw [mem_compatibleSet, jointWord_comp, multiplicity_comp_eq_mappedType, h]
  rfl

/-! ### Exact counts -/

variable {S}

omit [DecidableEq C] [DecidableEq L] [Fintype Z] [DecidableEq Z] in
/-- The first marginal of the usefulness profile is the component type. -/
theorem mappedType_fst_usefulType {αType : C → ℕ} (h : S.RefinesType αType) :
    mappedType Prod.fst S.usefulType = αType := by
  funext c
  rw [mappedType_fst_apply]
  exact h c

omit [DecidableEq C] [DecidableEq L] [Fintype Z] [DecidableEq Z] in
/-- The total mass of the usefulness profile is the word length. -/
theorem sum_usefulType {αType : C → ℕ} (h : S.RefinesType αType) :
    ∑ p, S.usefulType p = ∑ c, αType c := by
  classical
  rw [Fintype.sum_prod_type]
  exact Finset.sum_congr rfl fun c _ ↦ h c

omit [DecidableEq C] in
/-- The first marginal of the typicalness profile is the Z-marginal of the component type. -/
theorem mappedType_fst_typicalType {αType : C → ℕ} (h : S.RefinesType αType) :
    mappedType Prod.fst S.typicalType = mappedType S.zIndex αType := by
  classical
  funext z
  rw [mappedType_fst_apply]
  have : ∀ l, S.typicalType (z, l) = ∑ c ∈ letterFiber S.zIndex z, S.usefulType (c, l) :=
    fun l ↦ mappedType_prodMap_id_apply _ _ _ _
  simp only [this]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ ↦ ?_
  exact h c

/-- The first marginal of the compatibility profile is the requirement marginal of the component
type. -/
theorem mappedType_fst_compatibleType {αType : C → ℕ} (h : S.RefinesType αType) :
    mappedType Prod.fst S.compatibleType = mappedType S.requirement αType := by
  classical
  funext r
  rw [mappedType_fst_apply]
  have : ∀ l, S.compatibleType (r, l) = ∑ c ∈ letterFiber S.requirement r, S.usefulType (c, l) :=
    fun l ↦ mappedType_prodMap_id_apply _ _ _ _
  simp only [this]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ ↦ ?_
  exact h c

omit [DecidableEq C] in
/-- **The typical-block count**, `|T_K| = C(n, [nγ]) / C(n, [nα_Z])` in exact division-free form:
the number of Z-blocks of the given marginal type, times the number of typical small blocks inside
one of them, is the number of words of the typicalness type `γ`.

Proof sketch: `typicalSet K` is literally the conditional type class of the refinement `w` over
the coarse word `K` with joint type `γ`, so this is
`WordType.multinomial_source_mul_card_conditionalTypeClass`; the two side conditions are that `γ`
has total mass `n` and that its first marginal is the multiplicity type of `K`, both immediate
from `RefinesType`. -/
theorem multinomial_zType_mul_card_typicalSet {αType : C → ℕ} (h : S.RefinesType αType)
    (comp : Fin n → C) (hcomp : multiplicity comp = αType) :
    Nat.multinomial Finset.univ (mappedType S.zIndex αType) *
        (S.typicalSet (S.zIndex ∘ comp)).card =
      Nat.multinomial Finset.univ S.typicalType := by
  classical
  have hmul : multiplicity (S.zIndex ∘ comp) = mappedType S.zIndex αType := by
    rw [multiplicity_comp_eq_mappedType, hcomp]
  have hlen : ∑ c, αType c = n := by
    rw [← hcomp]; exact sum_multiplicity comp
  have hjoint : S.typicalType ∈ types (Z × L) n := by
    rw [mem_types, typicalType, sum_mappedType, sum_usefulType h, hlen]
  have hmap : mappedType Prod.fst S.typicalType = multiplicity (S.zIndex ∘ comp) := by
    rw [mappedType_fst_typicalType h, hmul]
  have := multinomial_source_mul_card_conditionalTypeClass (S.zIndex ∘ comp) S.typicalType
    hjoint hmap
  rwa [hmul] at this

/-- **The compatible-block count**, the numerator of `lemma:pcomp_g` in exact division-free form:
the number of requirement words of the given type, times the number of compatible small blocks,
is the number of words of the compatibility type. -/
theorem multinomial_reqType_mul_card_compatibleSet {αType : C → ℕ} (h : S.RefinesType αType)
    (comp : Fin n → C) (hcomp : multiplicity comp = αType) :
    Nat.multinomial Finset.univ (mappedType S.requirement αType) *
        (S.compatibleSet comp).card =
      Nat.multinomial Finset.univ S.compatibleType := by
  classical
  have hmul : multiplicity (S.requirement ∘ comp) = mappedType S.requirement αType := by
    rw [multiplicity_comp_eq_mappedType, hcomp]
  have hlen : ∑ c, αType c = n := by
    rw [← hcomp]; exact sum_multiplicity comp
  have hjoint : S.compatibleType ∈ types ((C ⊕ Z) × L) n := by
    rw [mem_types, compatibleType, sum_mappedType, sum_usefulType h, hlen]
  have hmap : mappedType Prod.fst S.compatibleType = multiplicity (S.requirement ∘ comp) := by
    rw [mappedType_fst_compatibleType h, hmul]
  have := multinomial_source_mul_card_conditionalTypeClass (S.requirement ∘ comp) S.compatibleType
    hjoint hmap
  rwa [hmul] at this

omit [DecidableEq C] in
/-- Typical small blocks exist.  Anti-vacuity for the denominator of `lemma:pcomp_g`. -/
theorem typicalSet_nonempty {αType : C → ℕ} (h : S.RefinesType αType)
    (comp : Fin n → C) (hcomp : multiplicity comp = αType) :
    (S.typicalSet (S.zIndex ∘ comp)).Nonempty := by
  classical
  have hmul : multiplicity (S.zIndex ∘ comp) = mappedType S.zIndex αType := by
    rw [multiplicity_comp_eq_mappedType, hcomp]
  have hlen : ∑ c, αType c = n := by
    rw [← hcomp]; exact sum_multiplicity comp
  refine conditionalTypeClass_nonempty (S.zIndex ∘ comp) S.typicalType ?_ ?_
  · rw [mem_types, typicalType, sum_mappedType, sum_usefulType h, hlen]
  · rw [mappedType_fst_typicalType h, hmul]

/-- Compatible small blocks exist.  Anti-vacuity for the numerator of `lemma:pcomp_g`: the
combination loss is a genuine ratio of nonzero counts, not a division by zero. -/
theorem compatibleSet_nonempty {αType : C → ℕ} (h : S.RefinesType αType)
    (comp : Fin n → C) (hcomp : multiplicity comp = αType) :
    (S.compatibleSet comp).Nonempty := by
  classical
  have hmul : multiplicity (S.requirement ∘ comp) = mappedType S.requirement αType := by
    rw [multiplicity_comp_eq_mappedType, hcomp]
  have hlen : ∑ c, αType c = n := by
    rw [← hcomp]; exact sum_multiplicity comp
  refine conditionalTypeClass_nonempty (S.requirement ∘ comp) S.compatibleType ?_ ?_
  · rw [mem_types, compatibleType, sum_mappedType, sum_usefulType h, hlen]
  · rw [mappedType_fst_compatibleType h, hmul]

omit [DecidableEq C] [DecidableEq L] [DecidableEq Z] in
/-- The compatible-block count depends on the large triple only through its component type.  This
is the first of the two "due to symmetry" steps of `lemma:pcomp_g`, and it needs no group action:
a conditional type class is a typed coordinatewise fiber, and those have equal size over coarse
words of equal type. -/
theorem card_compatibleSet_eq_of_multiplicity_eq {comp comp' : Fin n → C}
    (h : multiplicity comp = multiplicity comp') :
    (S.compatibleSet comp).card = (S.compatibleSet comp').card := by
  classical
  rw [compatibleSet, compatibleSet, card_conditionalTypeClass_eq_typedWordMapFiber,
    card_conditionalTypeClass_eq_typedWordMapFiber]
  refine card_typedWordMapFiber_eq_of_multiplicity_eq Prod.fst S.compatibleType _ _ ?_
  rw [multiplicity_comp_eq_mappedType, multiplicity_comp_eq_mappedType, h]

/-! ### The product closed form -/

omit [DecidableEq C] [Fintype L] [DecidableEq L] [Fintype Z] [DecidableEq Z] in
/-- **Multinomial chain identity.**  A multinomial coefficient of a joint profile factors as the
multinomial of its first marginal times the product of the multinomials of its rows.  This is the
exact finite form of the entropy chain rule, and it is what turns DWZ's "taking product over all
requirements" into a theorem.

Proof sketch: `Nat.multinomial_spec` turns each of the three multinomials into a factorial
identity; expanding the marginal factorials by the row identities and regrouping the double
product over `A × B` cancels the common factor `∏_{a,b} θ(a,b)!`, which is positive. -/
theorem multinomial_eq_mul_prod_rows {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A]
    (θ : A × B → ℕ) :
    Nat.multinomial Finset.univ θ =
      Nat.multinomial Finset.univ (mappedType Prod.fst θ) *
        ∏ a, Nat.multinomial Finset.univ (fun b ↦ θ (a, b)) := by
  exact WordType.multinomial_eq_multinomial_mappedType_fst_mul_prod θ

/-- **DWZ's product closed form for the compatible-block count** (`lemma:pcomp_g`, numerator):
the number of small blocks compatible with a large triple is the product, over the boundary
requirements `S_{i,j,k}` (`i = 0` or `j = 0`) and the pooled requirements `S_{+,+,k}`, of the
multinomial coefficient of that requirement's prescribed split. -/
theorem card_compatibleSet_eq_prod {αType : C → ℕ} (h : S.RefinesType αType)
    (comp : Fin n → C) (hcomp : multiplicity comp = αType) :
    (S.compatibleSet comp).card =
      ∏ r : C ⊕ Z, Nat.multinomial Finset.univ fun l ↦ S.compatibleType (r, l) := by
  classical
  have h1 := multinomial_reqType_mul_card_compatibleSet h comp hcomp
  have h2 := multinomial_eq_mul_prod_rows S.compatibleType
  rw [mappedType_fst_compatibleType h] at h2
  rw [h2] at h1
  exact Nat.eq_of_mul_eq_mul_left (Nat.multinomial_pos _ _) h1

omit [DecidableEq C] in
/-- **DWZ's product closed form for the typical-block count** (`lemma:pcomp_g`, denominator):
`|T_K|` is the product over Z-indices `k` of the multinomial coefficient of the average split
`α̃^{avg}_{*,*,k}` on `S_{*,*,k}`. -/
theorem card_typicalSet_eq_prod {αType : C → ℕ} (h : S.RefinesType αType)
    (comp : Fin n → C) (hcomp : multiplicity comp = αType) :
    (S.typicalSet (S.zIndex ∘ comp)).card =
      ∏ z : Z, Nat.multinomial Finset.univ fun l ↦ S.typicalType (z, l) := by
  classical
  have h1 := multinomial_zType_mul_card_typicalSet h comp hcomp
  have h2 := multinomial_eq_mul_prod_rows S.typicalType
  rw [mappedType_fst_typicalType h] at h2
  rw [h2] at h1
  exact Nat.eq_of_mul_eq_mul_left (Nat.multinomial_pos _ _) h1

omit [DecidableEq C] [DecidableEq L] [Fintype Z] [DecidableEq Z] in
/-- The useful-block count, in the same product form: `|Z^M|` of `overview.tex` is the product over
**all** components of the multinomial coefficient of that component's prescribed split. -/
theorem card_usefulSet_eq_prod {αType : C → ℕ} (h : S.RefinesType αType)
    (comp : Fin n → C) (hcomp : multiplicity comp = αType) :
    (S.usefulSet comp).card = ∏ c : C, Nat.multinomial Finset.univ (S.splitCount c) := by
  classical
  have hlen : ∑ c, αType c = n := by
    rw [← hcomp]; exact sum_multiplicity comp
  have hjoint : S.usefulType ∈ types (C × L) n := by
    rw [mem_types, sum_usefulType h, hlen]
  have hmap : mappedType Prod.fst S.usefulType = multiplicity comp := by
    rw [mappedType_fst_usefulType h, hcomp]
  have h1 := multinomial_source_mul_card_conditionalTypeClass comp S.usefulType hjoint hmap
  have h2 := multinomial_eq_mul_prod_rows S.usefulType
  rw [mappedType_fst_usefulType h] at h2
  rw [h2, hcomp] at h1
  exact Nat.eq_of_mul_eq_mul_left (Nat.multinomial_pos _ _) h1

omit [DecidableEq C] [DecidableEq L] [DecidableEq Z] in
/-- **The combination loss is a gain in block count.**  Every useful small block is compatible, so
DWZ's `|Z'| ≥ |Z^M|`: the compatible family is at least as large as the family the prior analyses
kept.  `overview.tex` asserts the ratio is `2^{Θ(n)}` under the hypothesis that the pooled split
distributions genuinely differ; only the inequality is unconditional. -/
theorem card_usefulSet_le_card_compatibleSet (comp : Fin n → C) :
    (S.usefulSet comp).card ≤ (S.compatibleSet comp).card :=
  Finset.card_le_card fun _ hw ↦ S.mem_compatibleSet_of_mem_usefulSet hw

/-! ### The pair count for the hole bound -/

variable (S)

variable {S}

/-- For a large triple through `Z_K`, the small blocks of `T_K` compatible with it are exactly its
compatible blocks: compatibility already implies typicalness. -/
theorem filter_typicalSet_isCompatible {αType : C → ℕ} {K : Fin n → Z} {comp : Fin n → C}
    (hcomp : comp ∈ S.matchable αType K) :
    ((S.typicalSet K).filter fun w ↦ S.IsCompatible comp w) = S.compatibleSet comp := by
  obtain ⟨-, hK⟩ := S.mem_matchable.1 hcomp
  ext w
  rw [Finset.mem_filter, S.mem_typicalSet]
  constructor
  · rintro ⟨-, hcompat⟩
    exact (S.isCompatible_iff_mem_compatibleSet comp w).1 hcompat
  · intro hmem
    have hcompat := (S.isCompatible_iff_mem_compatibleSet comp w).2 hmem
    refine ⟨?_, hcompat⟩
    have h2 := hcompat.2
    rwa [hK] at h2

/-- The compatible-triple count is the same for every typical small block.  This is the second
"due to symmetry" step of `lemma:pcomp_g`.

Proof sketch: two typical blocks `w, w'` have the same joint type with `K`, so
`WordType.positionPermOfSameMultiplicity` supplies a permutation `σ` of the positions with
`jointWord K w ∘ σ = jointWord K w'`; reading the two coordinates, `σ` fixes `K` and carries `w`
to `w'`.  Precomposition with `σ` is then a bijection between the two competitor families: it
preserves the component multiplicity type and the Z-word by `WordType.multiplicity_reindex`, and
it preserves compatibility because `jointWord (requirement ∘ comp ∘ σ) w'` is
`jointWord (requirement ∘ comp) w ∘ σ`. -/
theorem card_matchableCompatible_eq_of_mem_typicalSet {αType : C → ℕ} {K : Fin n → Z}
    {w w' : Fin n → L} (hw : w ∈ S.typicalSet K) (hw' : w' ∈ S.typicalSet K) :
    (S.matchableCompatible αType K w).card = (S.matchableCompatible αType K w').card := by
  have htype : multiplicity (jointWord K w') = multiplicity (jointWord K w) := by
    rw [S.mem_typicalSet] at hw hw'
    rw [hw, hw']
  set σ := positionPermOfSameMultiplicity (jointWord K w') (jointWord K w) htype with hσdef
  have hmap : jointWord K w ∘ σ = jointWord K w' :=
    positionPermOfSameMultiplicity_map _ _ htype
  have hK : ∀ i, K (σ i) = K i := fun i ↦ congrArg Prod.fst (congrFun hmap i)
  have hww : ∀ i, w (σ i) = w' i := fun i ↦ congrArg Prod.snd (congrFun hmap i)
  have hKcomp : K ∘ σ = K := funext hK
  have hwcomp : w ∘ σ = w' := funext hww
  have hKsymm : K ∘ σ.symm = K := by
    conv_lhs => rw [← hKcomp]
    funext i
    simp
  have hwsymm : w' ∘ σ.symm = w := by
    conv_lhs => rw [← hwcomp]
    funext i
    simp
  refine Finset.card_nbij' (fun comp ↦ comp ∘ σ) (fun comp ↦ comp ∘ σ.symm) ?_ ?_ ?_ ?_
  · intro comp hcomp
    simp only [Finset.mem_coe, S.mem_matchableCompatible, S.mem_matchable] at hcomp ⊢
    obtain ⟨⟨hmult, hz⟩, hcompat⟩ := hcomp
    have hmultσ : multiplicity (comp ∘ σ) = multiplicity comp := by
      simpa using multiplicity_reindex (α := C) σ.symm comp
    refine ⟨⟨by rw [hmultσ, hmult], ?_⟩, ?_⟩
    · show (S.zIndex ∘ comp) ∘ σ = K
      rw [hz, hKcomp]
    · rw [S.isCompatible_iff_mem_compatibleSet, S.mem_compatibleSet] at hcompat
      rw [S.isCompatible_iff_mem_compatibleSet, S.mem_compatibleSet]
      have hjw : jointWord (S.requirement ∘ (comp ∘ σ)) w' =
          jointWord (S.requirement ∘ comp) w ∘ σ := by
        funext i
        show (S.requirement (comp (σ i)), w' i) = (S.requirement (comp (σ i)), w (σ i))
        rw [hww]
      rw [hjw]
      have hre := multiplicity_reindex (α := (C ⊕ Z) × L) σ.symm
        (jointWord (S.requirement ∘ comp) w)
      simp only [Equiv.symm_symm] at hre
      rw [hre]
      exact hcompat
  · intro comp hcomp
    simp only [Finset.mem_coe, S.mem_matchableCompatible, S.mem_matchable] at hcomp ⊢
    obtain ⟨⟨hmult, hz⟩, hcompat⟩ := hcomp
    have hmultσ : multiplicity (comp ∘ σ.symm) = multiplicity comp := by
      simpa using multiplicity_reindex (α := C) σ comp
    refine ⟨⟨by rw [hmultσ, hmult], ?_⟩, ?_⟩
    · show (S.zIndex ∘ comp) ∘ σ.symm = K
      rw [hz, hKsymm]
    · rw [S.isCompatible_iff_mem_compatibleSet, S.mem_compatibleSet] at hcompat
      rw [S.isCompatible_iff_mem_compatibleSet, S.mem_compatibleSet]
      have hjw : jointWord (S.requirement ∘ (comp ∘ σ.symm)) w =
          jointWord (S.requirement ∘ comp) w' ∘ σ.symm := by
        funext i
        show (S.requirement (comp (σ.symm i)), w i) =
          (S.requirement (comp (σ.symm i)), w' (σ.symm i))
        have hi := congrFun hwsymm i
        simp only [Function.comp_apply] at hi
        rw [hi]
      rw [hjw]
      have hre := multiplicity_reindex (α := (C ⊕ Z) × L) σ
        (jointWord (S.requirement ∘ comp) w')
      rw [hre]
      exact hcompat
  · intro comp _
    funext i
    simp
  · intro comp _
    funext i
    simp

/-- **The pair count of `claim:hole_frac_low`.**  For every typical small block `Z_K̂ ∈ T_K`, the
number of large triples through `Z_K` compatible with it, multiplied by `|T_K|`, equals the number
of large triples through `Z_K` multiplied by the number of small blocks compatible with any one of
them.  Dividing, this is DWZ's

`#{I' matchable to K : Z_K̂ compatible with X_{I'}} = (N_α / N_Z) · p_comp`,

the competitor count that the second branch `8 · N_α · p_comp / N_Z` of the modulus `M_0` is
chosen to dominate.

Proof sketch: both sides count the set of compatible pairs `(X_{I'}, Z_K̂')` with `I'` matchable
to `K` and `K̂' ∈ T_K`.  Summing first over `I'` uses `filter_typicalSet_isCompatible` (compatible
implies typical) and `card_compatibleSet_eq_of_multiplicity_eq`; summing first over `K̂'` uses
`card_matchableCompatible_eq_of_mem_typicalSet`.  The exchange of the two summations is
`Finset.sum_comm` on indicator sums. -/
theorem card_matchableCompatible_mul_card_typicalSet {αType : C → ℕ} {K : Fin n → Z}
    {comp₀ : Fin n → C} (hcomp₀ : comp₀ ∈ S.matchable αType K)
    {w : Fin n → L} (hw : w ∈ S.typicalSet K) :
    (S.matchableCompatible αType K w).card * (S.typicalSet K).card =
      (S.matchable αType K).card * (S.compatibleSet comp₀).card := by
  have hpair : ∑ comp ∈ S.matchable αType K,
        (((S.typicalSet K).filter fun w' ↦ S.IsCompatible comp w').card) =
      ∑ w' ∈ S.typicalSet K,
        (((S.matchable αType K).filter fun comp ↦ S.IsCompatible comp w').card) := by
    simp only [Finset.card_filter]
    exact Finset.sum_comm
  have hleft : ∀ comp ∈ S.matchable αType K,
      (((S.typicalSet K).filter fun w' ↦ S.IsCompatible comp w').card) =
        (S.compatibleSet comp₀).card := by
    intro comp hcomp
    rw [filter_typicalSet_isCompatible hcomp]
    exact card_compatibleSet_eq_of_multiplicity_eq
      (by rw [(S.mem_matchable.1 hcomp).1, (S.mem_matchable.1 hcomp₀).1])
  have hright : ∀ w' ∈ S.typicalSet K,
      (((S.matchable αType K).filter fun comp ↦ S.IsCompatible comp w').card) =
        (S.matchableCompatible αType K w).card := by
    intro w' hw'
    show (S.matchableCompatible αType K w').card = _
    exact card_matchableCompatible_eq_of_mem_typicalSet hw' hw
  rw [Finset.sum_congr rfl hleft, Finset.sum_const, smul_eq_mul] at hpair
  rw [Finset.sum_congr rfl hright, Finset.sum_const, smul_eq_mul] at hpair
  rw [hpair]
  ring

end SplitRequirements

/-! ### A tiny inhabited instance

The smallest configuration in which the combination loss is a genuine gain: two *interior*
components sharing one Z-index — so the requirement partition pools them into a single cell — two
split labels, and one position of each component.  The useful family has one member (the split
prescribed component by component); the compatible family has two, the extra one being the block
that exchanges the two prescribed left halves between the two positions.  This is DWZ's
`|Z'| > |Z^M|` in its smallest instance, and it is the standing anti-vacuity regression for the
counting theorems above. -/

/-- Two interior components with a common Z-index and two split labels. -/
def tiny : SplitRequirements (Fin 2) (Fin 2) (Fin 1) where
  zIndex _ := 0
  boundary _ := false
  splitCount c l := if c = l then 1 else 0

/-- One position of each component. -/
def tinyComp : Fin 2 → Fin 2 := id

@[simp] theorem tiny_multiplicity : WordType.multiplicity tinyComp = fun _ ↦ 1 := by
  funext c
  rw [WordType.multiplicity_eq_card_fiber]
  exact Fintype.card_eq_one_iff.mpr ⟨⟨c, rfl⟩, fun y ↦ Subtype.ext y.2⟩

theorem tiny_refines : tiny.RefinesType (fun _ ↦ 1) := by
  intro c
  simp [tiny]

/-- Both components are pooled into the single interior requirement of the unique Z-index. -/
theorem tiny_requirement (c : Fin 2) : tiny.requirement c = Sum.inr 0 := by
  simp [SplitRequirements.requirement, tiny]

/-- The compatibility profile: the boundary rows vanish and the single pooled row is the uniform
profile, so the pooled cell may split its two positions in either order. -/
theorem tiny_compatibleType :
    tiny.compatibleType = fun p ↦ Sum.elim (fun _ ↦ 0) (fun _ ↦ 1) p.1 := by
  funext p
  obtain ⟨r, l⟩ := p
  cases r with
  | inl c =>
      rw [SplitRequirements.compatibleType_inl]
      simp [tiny]
  | inr z =>
      rw [SplitRequirements.compatibleType_inr]
      simp only [tiny_requirement, Subsingleton.elim z 0]
      simp [tiny]

/-- The useful family has exactly one member. -/
theorem tiny_card_usefulSet : (tiny.usefulSet tinyComp).card = 1 := by
  rw [SplitRequirements.card_usefulSet_eq_prod tiny_refines tinyComp tiny_multiplicity]
  decide

/-- The compatible family has exactly two members. -/
theorem tiny_card_compatibleSet : (tiny.compatibleSet tinyComp).card = 2 := by
  rw [SplitRequirements.card_compatibleSet_eq_prod tiny_refines tinyComp tiny_multiplicity,
    tiny_compatibleType]
  decide

/-- **The combination loss is strictly a loss in the prior analyses.**  In the tiny instance the
compatible family is strictly larger than the useful family, so DWZ's `|Z'| / |Z^M| > 1` is not
vacuous. -/
theorem tiny_card_usefulSet_lt_card_compatibleSet :
    (tiny.usefulSet tinyComp).card < (tiny.compatibleSet tinyComp).card := by
  rw [tiny_card_usefulSet, tiny_card_compatibleSet]
  norm_num

end AlgebraicComplexity.CompatibleSplit
