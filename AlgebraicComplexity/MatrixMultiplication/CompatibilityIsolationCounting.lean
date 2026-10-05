import AlgebraicComplexity.Combinatorics.ConditionalWordTypeCore
import AlgebraicComplexity.Tensor.CompatibilityZeroing
import Mathlib.Combinatorics.Enumerative.DoubleCounting

/-!
# Exact counting for compatibility isolation

Compatibility zeroing retains an address precisely when its pivot label has no distinct
compatible competitor in the ambient support.  This file turns that semantic definition into a
division-free finite cardinality estimate.  The loss is the exact number of directed competitor
incidences, first on `Y` and then on the surviving `Y` support for `Z`.

The final section provides a method-of-types adapter.  An injective encoding of every competitor
fiber into a conditional word-type class gives the corresponding exact multinomial bound.  Thus
the tensor semantics and the certificate-specific entropy estimate meet at a small, explicit
interface; no damaged-box or hole-repair hypothesis appears here.
-/

namespace AlgebraicComplexity.Tensor

open scoped BigOperators

universe u v w

variable {A : Leg → Type u} [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]

/-- Distinct ambient addresses compatible with the pivot label used by `address`.

Its cardinality is the exact directed competitor count for this address. -/
noncomputable def compatibilityCompetitors
    (ambient : Finset (BlockAddress A)) (pivot : Leg)
    (compatible : A pivot → BlockAddress A → Prop)
    (address : BlockAddress A) : Finset (BlockAddress A) := by
  classical
  exact (ambient.erase address).filter (compatible (address pivot))

@[simp] theorem mem_compatibilityCompetitors
    (ambient : Finset (BlockAddress A)) (pivot : Leg)
    (compatible : A pivot → BlockAddress A → Prop)
    (address other : BlockAddress A) :
    other ∈ compatibilityCompetitors ambient pivot compatible address ↔
      other ∈ ambient ∧ other ≠ address ∧ compatible (address pivot) other := by
  classical
  simp [compatibilityCompetitors, and_assoc, and_left_comm]

/-- An ambient address fails unique compatibility only if it has a listed distinct competitor. -/
theorem compatibilityCompetitors_nonempty_of_not_isolated
    (ambient : Finset (BlockAddress A)) (pivot : Leg)
    (compatible : A pivot → BlockAddress A → Prop)
    {address : BlockAddress A} (haddress : address ∈ ambient)
    (hnot : address ∉ compatibilityIsolatedSupport ambient pivot compatible) :
    (compatibilityCompetitors ambient pivot compatible address).Nonempty := by
  classical
  have hnotUnique : ¬ IsUniquelyCompatible ambient pivot compatible address := by
    intro hunique
    exact hnot ((mem_compatibilityIsolatedSupport
      ambient pivot compatible address).2 hunique)
  have hnotAll : ¬ ∀ other ∈ ambient,
      compatible (address pivot) other → other = address := by
    intro hall
    exact hnotUnique ⟨haddress, hall⟩
  push Not at hnotAll
  obtain ⟨other, hother, hcompatible, hne⟩ := hnotAll
  exact ⟨other, (mem_compatibilityCompetitors
    ambient pivot compatible address other).2 ⟨hother, hne, hcompatible⟩⟩

/-- One compatibility cleanup loses at most the total number of directed competitor incidences.

This union bound is exact and division-free.  It does not need compatibility soundness: soundness
is used by the tensor zeroing theorem, whereas this result only counts the support selected by
the definition. -/
theorem card_le_card_compatibilityIsolatedSupport_add_sum_competitors
    (ambient : Finset (BlockAddress A)) (pivot : Leg)
    (compatible : A pivot → BlockAddress A → Prop) :
    ambient.card ≤
      (compatibilityIsolatedSupport ambient pivot compatible).card +
        ∑ address ∈ ambient,
          (compatibilityCompetitors ambient pivot compatible address).card := by
  classical
  let isolated := compatibilityIsolatedSupport ambient pivot compatible
  let bad := ambient \ isolated
  have hbad : bad.card ≤
      ∑ address ∈ ambient,
        (compatibilityCompetitors ambient pivot compatible address).card := by
    calc
      bad.card = ∑ _address ∈ bad, 1 := by simp
      _ ≤ ∑ address ∈ bad,
          (compatibilityCompetitors ambient pivot compatible address).card := by
        apply Finset.sum_le_sum
        intro address haddress
        have hmem := Finset.mem_sdiff.mp haddress
        exact (compatibilityCompetitors_nonempty_of_not_isolated
          ambient pivot compatible hmem.1 hmem.2).card_pos
      _ ≤ ∑ address ∈ ambient,
          (compatibilityCompetitors ambient pivot compatible address).card := by
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.sdiff_subset)
          (fun _ _ _ ↦ Nat.zero_le _)
  have hpartition : bad.card + isolated.card = ambient.card := by
    exact Finset.card_sdiff_add_card_eq_card
      (compatibilityIsolatedSupport_subset ambient pivot compatible)
  dsimp only [bad, isolated] at hbad hpartition ⊢
  omega

/-- Exact total competitor incidence used by certificate-facing counting statements. -/
noncomputable def compatibilityCompetitorIncidence
    (ambient : Finset (BlockAddress A)) (pivot : Leg)
    (compatible : A pivot → BlockAddress A → Prop) : ℕ :=
  ∑ address ∈ ambient,
    (compatibilityCompetitors ambient pivot compatible address).card

/-! ## The transposed label/address incidence

The paper counts the same compatibility relation in the opposite orientation: for a fixed
coarse address it counts all fine labels compatible with that address.  The following small API
keeps the finite label family explicit (for example, it may be the family of typical labels) and
records the exact double-counting identity between the two orientations. -/

/-- Labels in `labels` compatible with one fixed ambient address. -/
noncomputable def compatibleLabels
    {pivot : Leg} (labels : Finset (A pivot))
    (compatible : A pivot → BlockAddress A → Prop)
    (address : BlockAddress A) : Finset (A pivot) := by
  classical
  exact labels.filter fun label ↦ compatible label address

@[simp] theorem mem_compatibleLabels
    {pivot : Leg} (labels : Finset (A pivot))
    (compatible : A pivot → BlockAddress A → Prop)
    (address : BlockAddress A) (label : A pivot) :
    label ∈ compatibleLabels labels compatible address ↔
      label ∈ labels ∧ compatible label address := by
  classical
  simp [compatibleLabels]

/-- Ambient addresses compatible with one fixed label. -/
noncomputable def compatibleAddresses
    (ambient : Finset (BlockAddress A)) {pivot : Leg}
    (compatible : A pivot → BlockAddress A → Prop)
    (label : A pivot) : Finset (BlockAddress A) := by
  classical
  exact ambient.filter (compatible label)

@[simp] theorem mem_compatibleAddresses
    (ambient : Finset (BlockAddress A)) {pivot : Leg}
    (compatible : A pivot → BlockAddress A → Prop)
    (label : A pivot) (address : BlockAddress A) :
    address ∈ compatibleAddresses ambient compatible label ↔
      address ∈ ambient ∧ compatible label address := by
  classical
  simp [compatibleAddresses]

/-- Exact double count of compatible label/address pairs.  This is the finite identity behind
the paper's `Q`: it can be evaluated either by fixing the label or by fixing the coarse address. -/
theorem sum_card_compatibleAddresses_eq_sum_card_compatibleLabels
    (ambient : Finset (BlockAddress A)) {pivot : Leg}
    (labels : Finset (A pivot))
    (compatible : A pivot → BlockAddress A → Prop) :
    (∑ label ∈ labels, (compatibleAddresses ambient compatible label).card) =
      ∑ address ∈ ambient, (compatibleLabels labels compatible address).card := by
  classical
  let relation : A pivot → BlockAddress A → Prop := compatible
  simpa only [compatibleAddresses, compatibleLabels, relation,
    Finset.bipartiteAbove, Finset.bipartiteBelow] using
    (Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
      (s := labels) (t := ambient) relation)

/-- Two-stage `Y`/`Z` compatibility isolation loses at most the sum of its two exact incidence
counts.  The `Z` incidence is deliberately measured only after `Y` isolation, matching the
actual cleanup algorithm. -/
theorem card_le_card_YZCompatibilityIsolatedSupport_add_incidences
    (ambient : Finset (BlockAddress A))
    (compatibleY : A .Y → BlockAddress A → Prop)
    (compatibleZ : A .Z → BlockAddress A → Prop) :
    let ySupport := compatibilityIsolatedSupport ambient .Y compatibleY
    let zSupport := compatibilityIsolatedSupport ySupport .Z compatibleZ
    ambient.card ≤ zSupport.card +
      compatibilityCompetitorIncidence ambient .Y compatibleY +
      compatibilityCompetitorIncidence ySupport .Z compatibleZ := by
  classical
  dsimp only
  have hy := card_le_card_compatibilityIsolatedSupport_add_sum_competitors
    ambient .Y compatibleY
  have hz := card_le_card_compatibilityIsolatedSupport_add_sum_competitors
    (compatibilityIsolatedSupport ambient .Y compatibleY) .Z compatibleZ
  change ambient.card ≤
      (compatibilityIsolatedSupport ambient .Y compatibleY).card +
    compatibilityCompetitorIncidence ambient .Y compatibleY at hy
  change (compatibilityIsolatedSupport ambient .Y compatibleY).card ≤
      (compatibilityIsolatedSupport
        (compatibilityIsolatedSupport ambient .Y compatibleY) .Z compatibleZ).card +
      compatibilityCompetitorIncidence
        (compatibilityIsolatedSupport ambient .Y compatibleY) .Z compatibleZ at hz
  omega

/-- Budget form of the two-stage counting theorem. -/
theorem card_le_card_YZCompatibilityIsolatedSupport_add_budgets
    (ambient : Finset (BlockAddress A))
    (compatibleY : A .Y → BlockAddress A → Prop)
    (compatibleZ : A .Z → BlockAddress A → Prop)
    (budgetY budgetZ : ℕ)
    (hbudgetY : compatibilityCompetitorIncidence ambient .Y compatibleY ≤ budgetY)
    (hbudgetZ : compatibilityCompetitorIncidence
      (compatibilityIsolatedSupport ambient .Y compatibleY) .Z compatibleZ ≤ budgetZ) :
    let ySupport := compatibilityIsolatedSupport ambient .Y compatibleY
    let zSupport := compatibilityIsolatedSupport ySupport .Z compatibleZ
    ambient.card ≤ zSupport.card + budgetY + budgetZ := by
  have hcount := card_le_card_YZCompatibilityIsolatedSupport_add_incidences
    ambient compatibleY compatibleZ
  dsimp only at hcount ⊢
  omega

/-- If the two competitor budgets consume at most half the ambient family, compatibility cleanup
retains at least half of the addresses. -/
theorem card_le_two_mul_card_YZCompatibilityIsolatedSupport
    (ambient : Finset (BlockAddress A))
    (compatibleY : A .Y → BlockAddress A → Prop)
    (compatibleZ : A .Z → BlockAddress A → Prop)
    (budgetY budgetZ : ℕ)
    (hbudgetY : compatibilityCompetitorIncidence ambient .Y compatibleY ≤ budgetY)
    (hbudgetZ : compatibilityCompetitorIncidence
      (compatibilityIsolatedSupport ambient .Y compatibleY) .Z compatibleZ ≤ budgetZ)
    (hhalf : 2 * (budgetY + budgetZ) ≤ ambient.card) :
    let ySupport := compatibilityIsolatedSupport ambient .Y compatibleY
    let zSupport := compatibilityIsolatedSupport ySupport .Z compatibleZ
    ambient.card ≤ 2 * zSupport.card := by
  have hcount := card_le_card_YZCompatibilityIsolatedSupport_add_budgets
    ambient compatibleY compatibleZ budgetY budgetZ hbudgetY hbudgetZ
  dsimp only at hcount ⊢
  omega

/-! ## Conditional method-of-types adapter -/

/-- A competitor fiber encoded injectively by a conditional word-type class.  This is the exact
finite interface expected from a quotient competitor classification. -/
structure ConditionalCompetitorEncoding
    (ambient : Finset (BlockAddress A)) (pivot : Leg)
    (compatible : A pivot → BlockAddress A → Prop)
    (address : BlockAddress A)
    (U : Type v) (Z : Type v) [Fintype U] [Fintype Z] (n : ℕ) where
  source : Fin n → U
  jointType : U × Z → ℕ
  jointType_legal : jointType ∈ WordType.types (U × Z) n
  jointType_fst : WordType.mappedType Prod.fst jointType =
    WordType.multiplicity source
  refinement :
    {other // other ∈ compatibilityCompetitors ambient pivot compatible address} →
      Fin n → Z
  refinement_mem : ∀ other,
    refinement other ∈ WordType.conditionalTypeClass source jointType
  refinement_injective : Function.Injective refinement

namespace ConditionalCompetitorEncoding

/-- The competitor count is bounded by the represented conditional type class. -/
theorem card_competitors_le_card_conditionalTypeClass
    {ambient : Finset (BlockAddress A)} {pivot : Leg}
    {compatible : A pivot → BlockAddress A → Prop}
    {address : BlockAddress A}
    {U : Type v} {Z : Type v} [Fintype U] [Fintype Z] {n : ℕ}
    (encoding : ConditionalCompetitorEncoding
      ambient pivot compatible address U Z n) :
    (compatibilityCompetitors ambient pivot compatible address).card ≤
      (WordType.conditionalTypeClass encoding.source encoding.jointType).card := by
  classical
  let f :
      {other // other ∈ compatibilityCompetitors ambient pivot compatible address} →
        {word // word ∈
          WordType.conditionalTypeClass encoding.source encoding.jointType} :=
    fun other ↦ ⟨encoding.refinement other, encoding.refinement_mem other⟩
  have hinjective : Function.Injective f := by
    intro left right h
    exact encoding.refinement_injective (congrArg Subtype.val h)
  simpa only [Fintype.card_coe] using Fintype.card_le_of_injective f hinjective

/-- Division-free exact method-of-types bound for one compatibility competitor fiber. -/
theorem multinomial_source_mul_card_competitors_le_multinomial_joint
    {ambient : Finset (BlockAddress A)} {pivot : Leg}
    {compatible : A pivot → BlockAddress A → Prop}
    {address : BlockAddress A}
    {U : Type v} {Z : Type v} [Fintype U] [Fintype Z] {n : ℕ}
    (encoding : ConditionalCompetitorEncoding
      ambient pivot compatible address U Z n) :
    Nat.multinomial Finset.univ (WordType.multiplicity encoding.source) *
        (compatibilityCompetitors ambient pivot compatible address).card ≤
      Nat.multinomial Finset.univ encoding.jointType := by
  calc
    _ ≤ Nat.multinomial Finset.univ (WordType.multiplicity encoding.source) *
        (WordType.conditionalTypeClass encoding.source encoding.jointType).card :=
      Nat.mul_le_mul_left _ encoding.card_competitors_le_card_conditionalTypeClass
    _ = _ := WordType.multinomial_source_mul_card_conditionalTypeClass
      encoding.source encoding.jointType encoding.jointType_legal encoding.jointType_fst

end ConditionalCompetitorEncoding

/-- A competitor encoding together with the distinguished word representing the address itself.
Removing that word from the target class removes the unavoidable diagonal incidence and gives
the sharp `class.card - 1` bound needed by isolation estimates. -/
structure PointedConditionalCompetitorEncoding
    (ambient : Finset (BlockAddress A)) (pivot : Leg)
    (compatible : A pivot → BlockAddress A → Prop)
    (address : BlockAddress A)
    (U : Type v) (Z : Type v) [Fintype U] [Fintype Z] (n : ℕ) where
  encoding : ConditionalCompetitorEncoding
    ambient pivot compatible address U Z n
  point : Fin n → Z
  point_mem : point ∈ WordType.conditionalTypeClass
    encoding.source encoding.jointType
  refinement_ne_point : ∀ other, encoding.refinement other ≠ point

namespace PointedConditionalCompetitorEncoding

/-- Sharp competitor bound after deleting the distinguished diagonal word. -/
theorem card_competitors_le_card_conditionalTypeClass_tsub_one
    {ambient : Finset (BlockAddress A)} {pivot : Leg}
    {compatible : A pivot → BlockAddress A → Prop}
    {address : BlockAddress A}
    {U : Type v} {Z : Type v} [Fintype U] [Fintype Z] {n : ℕ}
    (pointed : PointedConditionalCompetitorEncoding
      ambient pivot compatible address U Z n) :
    (compatibilityCompetitors ambient pivot compatible address).card ≤
      (WordType.conditionalTypeClass
        pointed.encoding.source pointed.encoding.jointType).card - 1 := by
  classical
  let target := WordType.conditionalTypeClass
    pointed.encoding.source pointed.encoding.jointType
  let f :
      {other // other ∈ compatibilityCompetitors ambient pivot compatible address} →
        {word // word ∈ target.erase pointed.point} := fun other ↦
    ⟨pointed.encoding.refinement other, by
      rw [Finset.mem_erase]
      exact ⟨pointed.refinement_ne_point other,
        pointed.encoding.refinement_mem other⟩⟩
  have hinjective : Function.Injective f := by
    intro left right h
    exact pointed.encoding.refinement_injective (congrArg Subtype.val h)
  calc
    (compatibilityCompetitors ambient pivot compatible address).card ≤
        (target.erase pointed.point).card := by
      simpa only [Fintype.card_coe] using Fintype.card_le_of_injective f hinjective
    _ = target.card - 1 := Finset.card_erase_of_mem pointed.point_mem
    _ = _ := rfl

end PointedConditionalCompetitorEncoding

/-! ## Conditional encodings in the paper's fixed-address orientation -/

/-- A family of compatible labels encoded injectively by an ordinary conditional word-type
class.  Unlike `ConditionalCompetitorEncoding`, this fixes the coarse address and varies the
label.  This is the orientation used to compute the compatibility quantity `Q` in the paper. -/
structure ConditionalCompatibleLabelEncoding
    {pivot : Leg} (labels : Finset (A pivot))
    (compatible : A pivot → BlockAddress A → Prop)
    (address : BlockAddress A)
    (U : Type v) (Z : Type w) [Fintype U] [Fintype Z] (n : ℕ) where
  source : Fin n → U
  jointType : U × Z → ℕ
  jointType_legal : jointType ∈ WordType.types (U × Z) n
  jointType_fst : WordType.mappedType Prod.fst jointType =
    WordType.multiplicity source
  refinement :
    {label // label ∈ compatibleLabels labels compatible address} → Fin n → Z
  refinement_mem : ∀ label,
    refinement label ∈ WordType.conditionalTypeClass source jointType
  refinement_injective : Function.Injective refinement

namespace ConditionalCompatibleLabelEncoding

/-- The number of compatible labels is at most its concrete conditional type class. -/
theorem card_compatibleLabels_le_card_conditionalTypeClass
    {pivot : Leg} {labels : Finset (A pivot)}
    {compatible : A pivot → BlockAddress A → Prop}
    {address : BlockAddress A}
    {U : Type v} {Z : Type w} [Fintype U] [Fintype Z] {n : ℕ}
    (encoding : ConditionalCompatibleLabelEncoding
      labels compatible address U Z n) :
    (compatibleLabels labels compatible address).card ≤
      (WordType.conditionalTypeClass encoding.source encoding.jointType).card := by
  classical
  let f :
      {label // label ∈ compatibleLabels labels compatible address} →
        {word // word ∈
          WordType.conditionalTypeClass encoding.source encoding.jointType} :=
    fun label ↦ ⟨encoding.refinement label, encoding.refinement_mem label⟩
  have hinjective : Function.Injective f := by
    intro left right h
    exact encoding.refinement_injective (congrArg Subtype.val h)
  simpa only [Fintype.card_coe] using Fintype.card_le_of_injective f hinjective

/-- Division-free method-of-types bound for the compatible-label fiber of one fixed address. -/
theorem multinomial_source_mul_card_compatibleLabels_le_multinomial_joint
    {pivot : Leg} {labels : Finset (A pivot)}
    {compatible : A pivot → BlockAddress A → Prop}
    {address : BlockAddress A}
    {U : Type v} {Z : Type w} [Fintype U] [Fintype Z] {n : ℕ}
    (encoding : ConditionalCompatibleLabelEncoding
      labels compatible address U Z n) :
    Nat.multinomial Finset.univ (WordType.multiplicity encoding.source) *
        (compatibleLabels labels compatible address).card ≤
      Nat.multinomial Finset.univ encoding.jointType := by
  calc
    _ ≤ Nat.multinomial Finset.univ (WordType.multiplicity encoding.source) *
        (WordType.conditionalTypeClass encoding.source encoding.jointType).card :=
      Nat.mul_le_mul_left _ encoding.card_compatibleLabels_le_card_conditionalTypeClass
    _ = _ := WordType.multinomial_source_mul_card_conditionalTypeClass
      encoding.source encoding.jointType encoding.jointType_legal encoding.jointType_fst

end ConditionalCompatibleLabelEncoding

end AlgebraicComplexity.Tensor
