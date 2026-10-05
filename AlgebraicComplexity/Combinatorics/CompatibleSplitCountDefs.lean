/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Combinatorics.ConditionalWordTypeCore

/-!
# Compatible split counting: definitions

Layer 2 (`AlgebraicComplexity/Combinatorics/`).  The definition half of
`Combinatorics/CompatibleSplitCount.lean`, split off so that clients which only need to *state*
DWZ compatibility — such as `MatrixMultiplication/AsymmetricGlobalValue.lean` — do not import the
exact multinomial counting proofs above them.  The entropy identities in
`Analysis/CompatibilityRateCore.lean` intentionally use the full finite counting cluster for its
pushforward lemmas, while still avoiding proportional-multinomial asymptotics.  The mathematical
narrative, the paper references and every counting theorem live in `CompatibleSplitCount.lean`,
which imports this file and re-exports it; no public name and no import path changed when the two
were separated.

This file carries:

* `SplitRequirements`, the three-field record `(zIndex, boundary, splitCount)` that DWZ's
  compatibility definition reads off a level-`ℓ` component alphabet;
* the requirement alphabet `C ⊕ Z` (`requirement`, `reqIndex`) and the two one-line lemmas saying
  requirements refine Z-indices;
* the three joint split profiles `usefulType`, `typicalType`, `compatibleType`;
* the predicates `IsTypical`, `BoundaryMatched`, `IsCompatible`, `IsUseful`, the finsets
  `typicalSet`, `compatibleSet`, `usefulSet` and their `@[simp]` membership lemmas;
* the standing consistency hypothesis `RefinesType`;
* the competitor families `matchable`, `matchableCompatible` and their membership lemmas.
-/

namespace AlgebraicComplexity.CompatibleSplit

open AlgebraicComplexity.WordType
open scoped BigOperators

universe u v w

variable {C : Type u} {L : Type v} {Z : Type w}

/-- The data DWZ's compatibility definition reads off a level-`ℓ` component alphabet.

`zIndex c` is the Z-index `k` of the component `c = (i,j,k)`; `boundary c` is the degeneracy test
`i = 0 ∨ j = 0`, exactly the case in which a zero index forces a bijection between the X- (resp.
Y-) split and the Z-split; and `splitCount c l` is the integral profile `n · α(c) · α̃_c(l)`
prescribing how many positions of component `c` split with left half `l`. -/
structure SplitRequirements (C : Type u) (L : Type v) (Z : Type w) where
  /-- The Z-index of a component. -/
  zIndex : C → Z
  /-- DWZ's degeneracy test `i = 0 ∨ j = 0` on components. -/
  boundary : C → Bool
  /-- The prescribed integral split profile of each component. -/
  splitCount : C → L → ℕ

namespace SplitRequirements

variable [Fintype C] [DecidableEq C] [Fintype L] [DecidableEq L] [Fintype Z] [DecidableEq Z]
variable (S : SplitRequirements C L Z)

/-! ### The requirement alphabet -/

/-- The requirement a position's component belongs to: its own cell when the component is a
boundary component (`i = 0` or `j = 0`), and otherwise the cell pooled over all interior
components sharing its Z-index.  These are DWZ's requirement families (a) and (c). -/
def requirement (c : C) : C ⊕ Z :=
  if S.boundary c then Sum.inl c else Sum.inr (S.zIndex c)

/-- The Z-index of a requirement.  Both requirement families refine the Z-index. -/
def reqIndex : C ⊕ Z → Z :=
  Sum.elim S.zIndex id

omit [Fintype C] [DecidableEq C] [Fintype L] [DecidableEq L] [Fintype Z] [DecidableEq Z] in
/-- Requirements refine Z-indices: `reqIndex (requirement c) = zIndex c`. -/
@[simp] theorem reqIndex_requirement (c : C) : S.reqIndex (S.requirement c) = S.zIndex c := by
  unfold requirement reqIndex
  split <;> rfl

omit [Fintype C] [DecidableEq C] [Fintype L] [DecidableEq L] [Fintype Z] [DecidableEq Z] in
/-- Requirements refine Z-indices, in composed form. -/
theorem reqIndex_comp_requirement : S.reqIndex ∘ S.requirement = S.zIndex :=
  funext S.reqIndex_requirement

/-! ### The three joint split profiles -/

/-- The *usefulness* profile: the prescribed split count of every component separately.  This is
DWZ's `def:useful_g` requirement `Split(K̂, S_{i,j,k}) = α̃_{i,j,k}` for **all** components. -/
def usefulType : C × L → ℕ := fun p ↦ S.splitCount p.1 p.2

/-- The *typicalness* profile `γ` of `global_value.tex`'s typicalness definition: the split
profile pushed forward along the Z-index, i.e. the integral form of
`γ(k_l, k_r) = ∑_{k = k_l + k_r} α(i,j,k) · α̃_{i,j,k}(k_l)`. -/
noncomputable def typicalType : Z × L → ℕ :=
  mappedType (Prod.map S.zIndex (id : L → L)) S.usefulType

/-- The *compatibility* profile: the split profile pushed forward along the requirement map.  Its
`Sum.inl c` rows are the boundary requirements (a) and its `Sum.inr k` rows the pooled
requirements (c) of `lemma:pcomp_g`, whose weights are DWZ's `α(+,+,k) · α̃^{avg}_{+,+,k}`. -/
noncomputable def compatibleType : (C ⊕ Z) × L → ℕ :=
  mappedType (Prod.map S.requirement (id : L → L)) S.usefulType

/-! ### Typical, compatible and useful small blocks -/

variable {n : ℕ}

/-- DWZ typicalness (`global_value.tex`, the typicalness definition): the joint word of the large
Z-block with the small block has the prescribed profile `γ`.  Equivalently, by the paper's own
`Claim`, `Split(K̂, S_{*,*,k}) = α̃^{avg}_{*,*,k}` for every `k`; here the two are the *same*
statement, since a profile equation over `Z × L` is exactly a family of per-`k` split equations. -/
def IsTypical (K : Fin n → Z) (w : Fin n → L) : Prop :=
  multiplicity (jointWord K w) = S.typicalType

/-- Condition (2) of `def:global-compatible`: the split matches the prescribed distribution on
every boundary component (`i = 0` or `j = 0`) separately. -/
def BoundaryMatched (comp : Fin n → C) (w : Fin n → L) : Prop :=
  ∀ c, S.boundary c → ∀ l, multiplicity (jointWord comp w) (c, l) = S.splitCount c l

/-- DWZ `def:global-compatible`: the small block is typical for the large Z-block and matches the
prescribed split on every boundary component of the large triple. -/
def IsCompatible (comp : Fin n → C) (w : Fin n → L) : Prop :=
  S.BoundaryMatched comp w ∧ S.IsTypical (S.zIndex ∘ comp) w

/-- DWZ `def:useful_g`: the split matches the prescribed distribution on **every** component,
including the interior ones.  Usefulness is strictly stronger than compatibility. -/
def IsUseful (comp : Fin n → C) (w : Fin n → L) : Prop :=
  multiplicity (jointWord comp w) = S.usefulType

/-- The typical small blocks inside a fixed large Z-block: DWZ's `T_K`. -/
noncomputable def typicalSet (K : Fin n → Z) : Finset (Fin n → L) :=
  conditionalTypeClass K S.typicalType

/-- The small blocks compatible with a fixed large triple. -/
noncomputable def compatibleSet (comp : Fin n → C) : Finset (Fin n → L) :=
  conditionalTypeClass (S.requirement ∘ comp) S.compatibleType

/-- The small blocks useful for a fixed large triple. -/
noncomputable def usefulSet (comp : Fin n → C) : Finset (Fin n → L) :=
  conditionalTypeClass comp S.usefulType

omit [DecidableEq C] [DecidableEq L] [DecidableEq Z] in
@[simp] theorem mem_typicalSet {K : Fin n → Z} {w : Fin n → L} :
    w ∈ S.typicalSet K ↔ S.IsTypical K w := mem_conditionalTypeClass

omit [DecidableEq C] [DecidableEq L] [Fintype Z] [DecidableEq Z] in
@[simp] theorem mem_usefulSet {comp : Fin n → C} {w : Fin n → L} :
    w ∈ S.usefulSet comp ↔ S.IsUseful comp w := mem_conditionalTypeClass

omit [DecidableEq C] [DecidableEq L] [DecidableEq Z] in
@[simp] theorem mem_compatibleSet {comp : Fin n → C} {w : Fin n → L} :
    w ∈ S.compatibleSet comp ↔
      multiplicity (jointWord (S.requirement ∘ comp) w) = S.compatibleType :=
  mem_conditionalTypeClass

/-! ### The standing consistency hypothesis -/

/-- The split profile is the refinement of a component multiplicity type: `∑_l α̃_c(l) = α(c)` in
integral form.  This is the standing consistency hypothesis of `lemma:pcomp_g`. -/
def RefinesType (αType : C → ℕ) : Prop :=
  ∀ c, ∑ l, S.splitCount c l = αType c

/-! ### The competitor families -/

/-- Compatibility is decidable; the witness is classical because `WordType.multiplicity` is.
Declaring it as an instance keeps every `Finset.filter` by compatibility — in the definitions
below and in their proofs — over one and the same decidability witness. -/
noncomputable instance instDecidableIsCompatible {n : ℕ} (comp : Fin n → C) (w : Fin n → L) :
    Decidable (S.IsCompatible comp w) :=
  Classical.dec _

/-- The large triples through a fixed large Z-block that are consistent with the joint
distribution: DWZ's `N_α / N_Z` many blocks `X_I` matchable to `Z_K`. -/
noncomputable def matchable (αType : C → ℕ) (K : Fin n → Z) : Finset (Fin n → C) :=
  typedWordMapFiber S.zIndex αType K

omit [DecidableEq C] [Fintype L] [DecidableEq L] [Fintype Z] [DecidableEq Z] in
@[simp] theorem mem_matchable {αType : C → ℕ} {K : Fin n → Z} {comp : Fin n → C} :
    comp ∈ S.matchable αType K ↔ multiplicity comp = αType ∧ S.zIndex ∘ comp = K :=
  mem_typedWordMapFiber

/-- The large triples through `Z_K` compatible with a fixed small block: the competitor family of
`claim:hole_frac_low`. -/
noncomputable def matchableCompatible (αType : C → ℕ) (K : Fin n → Z) (w : Fin n → L) :
    Finset (Fin n → C) :=
  (S.matchable αType K).filter fun comp ↦ S.IsCompatible comp w

omit [DecidableEq C] [DecidableEq L] [Fintype Z] [DecidableEq Z] in
@[simp] theorem mem_matchableCompatible {αType : C → ℕ} {K : Fin n → Z} {w : Fin n → L}
    {comp : Fin n → C} :
    comp ∈ S.matchableCompatible αType K w ↔
      comp ∈ S.matchable αType K ∧ S.IsCompatible comp w :=
  Finset.mem_filter

end SplitRequirements

end AlgebraicComplexity.CompatibleSplit
