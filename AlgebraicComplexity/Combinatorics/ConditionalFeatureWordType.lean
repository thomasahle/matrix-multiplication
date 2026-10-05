import AlgebraicComplexity.Combinatorics.ConditionalFeatureMap
import AlgebraicComplexity.Combinatorics.ConditionalWordType

/-!
# Conditional word types with a visible feature profile

In recursive laser arguments a competitor word often ranges over a fine alphabet `T`, while the
counting theorem prescribes only a coarser feature `feature : T → C`.  For a fixed source word
`source : Fin n → S`, this file partitions the words with a prescribed `(source, feature)`
profile by their full `(source, target)` joint type.

The partition is exact.  Consequently the visible-feature class is bounded by a sum of ordinary
conditional type classes.  There are at most `(n + 1)^|S × T|` summands, so forgetting the full
joint type costs only a polynomial factor for fixed alphabets.  This is the reusable finite
adapter needed by compatibility-competitor counts; it is independent of tensors and of any
particular compatibility predicate.
-/

namespace AlgebraicComplexity.WordType

universe u v w

variable {S : Type u} {T : Type v} {C : Type w}
variable [Fintype S] [Fintype T] [Fintype C]

/-- Fine target words having a prescribed joint profile of the fixed source letter and the
visible feature of the target letter. -/
noncomputable def conditionalFeatureTypeClass
    (source : Fin n → S) (feature : T → C) (profile : S × C → ℕ) :
    Finset (Fin n → T) := by
  classical
  exact Finset.univ.filter fun target ↦
    multiplicity (jointWord source (feature ∘ target)) = profile

@[simp] theorem mem_conditionalFeatureTypeClass
    {source : Fin n → S} {feature : T → C} {profile : S × C → ℕ}
    {target : Fin n → T} :
    target ∈ conditionalFeatureTypeClass source feature profile ↔
      multiplicity (jointWord source (feature ∘ target)) = profile := by
  classical
  simp [conditionalFeatureTypeClass]

/-- Full `(source, target)` empirical types that push forward to the prescribed visible-feature
profile.  Types whose source marginal differs from `multiplicity source` are harmless: their
ordinary conditional type class is empty, so no extra side condition is needed here. -/
noncomputable def feasibleConditionalFeatureTypes
    (feature : T → C) (profile : S × C → ℕ) (n : ℕ) :
    Finset (S × T → ℕ) := by
  classical
  exact (types (S × T) n).filter fun jointType ↦
    mappedType (conditionalFeatureMap feature) jointType = profile

@[simp] theorem mem_feasibleConditionalFeatureTypes
    {feature : T → C} {profile : S × C → ℕ} {n : ℕ}
    {jointType : S × T → ℕ} :
    jointType ∈ feasibleConditionalFeatureTypes feature profile n ↔
      jointType ∈ types (S × T) n ∧
        mappedType (conditionalFeatureMap feature) jointType = profile := by
  classical
  simp [feasibleConditionalFeatureTypes]

/-- A visible `(source, feature)` profile with the prescribed source marginal forces every
feasible fine joint type to have that same source marginal. -/
theorem mappedType_fst_eq_of_mem_feasibleConditionalFeatureTypes
    (feature : T → C) (profile : S × C → ℕ) (n : ℕ)
    (sourceType : S → ℕ)
    (hprofile : mappedType Prod.fst profile = sourceType)
    {jointType : S × T → ℕ}
    (hjointType : jointType ∈
      feasibleConditionalFeatureTypes feature profile n) :
    mappedType Prod.fst jointType = sourceType := by
  have hpush := (mem_feasibleConditionalFeatureTypes.mp hjointType).2
  calc
    mappedType Prod.fst jointType =
        mappedType (Prod.fst ∘ conditionalFeatureMap feature) jointType := by
      congr 2
    _ = mappedType Prod.fst
        (mappedType (conditionalFeatureMap feature) jointType) :=
      (mappedType_comp (conditionalFeatureMap feature) Prod.fst jointType).symm
    _ = mappedType Prod.fst profile := by rw [hpush]
    _ = sourceType := hprofile

/-- Union of the ordinary conditional classes over every feasible full joint type. -/
noncomputable def conditionalFeatureTypeUnion
    (source : Fin n → S) (feature : T → C) (profile : S × C → ℕ) :
    Finset (Fin n → T) := by
  classical
  exact (feasibleConditionalFeatureTypes feature profile n).biUnion
    (conditionalTypeClass source)

/-- Exact partition of a visible-feature class by the full `(source, target)` joint type. -/
theorem conditionalFeatureTypeClass_eq_biUnion_conditionalTypeClass
    (source : Fin n → S) (feature : T → C) (profile : S × C → ℕ) :
    conditionalFeatureTypeClass source feature profile =
      conditionalFeatureTypeUnion source feature profile := by
  classical
  ext target
  rw [mem_conditionalFeatureTypeClass]
  simp only [conditionalFeatureTypeUnion, Finset.mem_biUnion]
  constructor
  · intro htarget
    let jointType : S × T → ℕ := multiplicity (jointWord source target)
    have hpush :
        mappedType (conditionalFeatureMap feature) jointType = profile := by
      calc
        mappedType (conditionalFeatureMap feature) jointType =
            multiplicity
              (conditionalFeatureMap feature ∘ jointWord source target) :=
          (multiplicity_comp_eq_mappedType
            (conditionalFeatureMap feature) (jointWord source target)).symm
        _ = multiplicity (jointWord source (feature ∘ target)) := by
          rw [conditionalFeatureMap_jointWord]
        _ = profile := htarget
    refine ⟨jointType, ?_, ?_⟩
    · exact mem_feasibleConditionalFeatureTypes.mpr
        ⟨multiplicity_mem_types (jointWord source target), hpush⟩
    · exact mem_conditionalTypeClass.mpr rfl
  · rintro ⟨jointType, hjointType, htarget⟩
    have hfull := mem_conditionalTypeClass.mp htarget
    have hpush := (mem_feasibleConditionalFeatureTypes.mp hjointType).2
    calc
      multiplicity (jointWord source (feature ∘ target)) =
          multiplicity
            (conditionalFeatureMap feature ∘ jointWord source target) := by
        rw [conditionalFeatureMap_jointWord]
      _ = mappedType (conditionalFeatureMap feature)
          (multiplicity (jointWord source target)) :=
        multiplicity_comp_eq_mappedType
          (conditionalFeatureMap feature) (jointWord source target)
      _ = mappedType (conditionalFeatureMap feature) jointType := by rw [hfull]
      _ = profile := hpush

/-- The visible-feature class is bounded by the sum of its ordinary conditional type classes. -/
theorem card_conditionalFeatureTypeClass_le_sum_conditionalTypeClasses
    (source : Fin n → S) (feature : T → C) (profile : S × C → ℕ) :
    (conditionalFeatureTypeClass source feature profile).card ≤
      ∑ jointType ∈ feasibleConditionalFeatureTypes feature profile n,
        (conditionalTypeClass source jointType).card := by
  classical
  rw [conditionalFeatureTypeClass_eq_biUnion_conditionalTypeClass]
  unfold conditionalFeatureTypeUnion
  exact Finset.card_biUnion_le

/-- If every feasible full conditional type class has size at most `bound`, forgetting the full
type costs at most the number of empirical types. -/
theorem card_conditionalFeatureTypeClass_le_types_mul
    (source : Fin n → S) (feature : T → C) (profile : S × C → ℕ)
    (bound : ℕ)
    (hbound : ∀ jointType ∈ feasibleConditionalFeatureTypes feature profile n,
      (conditionalTypeClass source jointType).card ≤ bound) :
    (conditionalFeatureTypeClass source feature profile).card ≤
      (types (S × T) n).card * bound := by
  classical
  calc
    (conditionalFeatureTypeClass source feature profile).card ≤
        ∑ jointType ∈ feasibleConditionalFeatureTypes feature profile n,
          (conditionalTypeClass source jointType).card :=
      card_conditionalFeatureTypeClass_le_sum_conditionalTypeClasses
        source feature profile
    _ ≤ ∑ _jointType ∈ feasibleConditionalFeatureTypes feature profile n,
          bound := by
      apply Finset.sum_le_sum
      intro jointType hjointType
      exact hbound jointType hjointType
    _ = (feasibleConditionalFeatureTypes feature profile n).card * bound := by simp
    _ ≤ (types (S × T) n).card * bound := by
      exact Nat.mul_le_mul_right bound
        (Finset.card_le_card (Finset.filter_subset _ _))

/-- Fully explicit polynomial-overhead form of the preceding estimate. -/
theorem card_conditionalFeatureTypeClass_le_succ_pow_mul
    (source : Fin n → S) (feature : T → C) (profile : S × C → ℕ)
    (bound : ℕ)
    (hbound : ∀ jointType ∈ feasibleConditionalFeatureTypes feature profile n,
      (conditionalTypeClass source jointType).card ≤ bound) :
    (conditionalFeatureTypeClass source feature profile).card ≤
      (n + 1) ^ Fintype.card (S × T) * bound := by
  exact (card_conditionalFeatureTypeClass_le_types_mul
      source feature profile bound hbound).trans
    (Nat.mul_le_mul_right bound (card_types_le (S × T) n))

/-- Real-valued polynomial loss for forgetting a full `(source, target)` empirical type while
retaining only its visible feature profile. -/
noncomputable def conditionalFeatureTypeSelectionLoss
    (S : Type u) (T : Type v) [Fintype S] [Fintype T] (n : ℕ) : ℝ :=
  (((n + 1 : ℕ) : ℝ)) ^ Fintype.card (S × T)

/-- For fixed source and target alphabets, visible-feature type selection has subexponential
loss. -/
theorem conditionalFeatureTypeSelectionLoss_subexponential
    (S : Type u) (T : Type v) [Fintype S] [Fintype T] :
    Growth.Subexponential (conditionalFeatureTypeSelectionLoss S T) := by
  exact Growth.Subexponential.natCast_succ_pow (Fintype.card (S × T))

end AlgebraicComplexity.WordType
