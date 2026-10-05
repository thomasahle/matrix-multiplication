/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Combinatorics.ConditionalFeatureMap
import AlgebraicComplexity.Combinatorics.ProportionalTypeClassCore

/-!
# Finite type lifting through an alphabet quotient

This is the analysis-free core of pushed-profile counting.  It proves the exact marginal and
fine-lift statements; entropy bounds remain in `PushedProfileTypeCounting`.
-/

namespace AlgebraicComplexity.WordType

universe u v w

variable {Cell : Type u} {Feature : Type v} {Raw : Type w}
variable [Fintype Cell] [Fintype Feature] [Fintype Raw]

/-- Pushing only the symbol coordinate preserves the cell marginal. -/
theorem mappedType_fst_pushedConditionalProfile
    (feature : Raw → Feature) (rawProfile : Cell × Raw → ℕ) :
    mappedType Prod.fst
        (mappedType (conditionalFeatureMap feature) rawProfile) =
      mappedType Prod.fst rawProfile := by
  calc
    mappedType Prod.fst
        (mappedType (conditionalFeatureMap feature) rawProfile) =
      mappedType (Prod.fst ∘ conditionalFeatureMap feature) rawProfile :=
        mappedType_comp (conditionalFeatureMap feature) Prod.fst rawProfile
    _ = mappedType Prod.fst rawProfile := by
      congr 2

/-- Mapping a fine target word sends its exact raw type to the pushed feature type. -/
theorem feature_comp_mem_pushedConditionalTypeClass
    (feature : Raw → Feature) (rawProfile : Cell × Raw → ℕ)
    (source : Fin n → Cell) (target : Fin n → Raw)
    (htarget : target ∈ conditionalTypeClass source rawProfile) :
    feature ∘ target ∈ conditionalTypeClass source
      (mappedType (conditionalFeatureMap feature) rawProfile) := by
  rw [mem_conditionalTypeClass] at htarget ⊢
  calc
    multiplicity (jointWord source (feature ∘ target)) =
        multiplicity
          (conditionalFeatureMap feature ∘ jointWord source target) := by
      rw [conditionalFeatureMap_jointWord]
    _ = mappedType (conditionalFeatureMap feature)
          (multiplicity (jointWord source target)) :=
      multiplicity_comp_eq_mappedType
        (conditionalFeatureMap feature) (jointWord source target)
    _ = mappedType (conditionalFeatureMap feature) rawProfile := by rw [htarget]

/-- Fine conditional words of one raw type mapping to a fixed feature target. -/
noncomputable def conditionalTypedFeatureFiber
    (source : Fin n → Cell) (feature : Raw → Feature)
    (rawProfile : Cell × Raw → ℕ) (featureTarget : Fin n → Feature) :
    Finset (Fin n → Raw) := by
  classical
  exact (conditionalTypeClass source rawProfile).filter fun rawTarget ↦
    feature ∘ rawTarget = featureTarget

omit [Fintype Feature] in
@[simp] theorem mem_conditionalTypedFeatureFiber
    {source : Fin n → Cell} {feature : Raw → Feature}
    {rawProfile : Cell × Raw → ℕ} {featureTarget : Fin n → Feature}
    {rawTarget : Fin n → Raw} :
    rawTarget ∈ conditionalTypedFeatureFiber source feature rawProfile featureTarget ↔
      rawTarget ∈ conditionalTypeClass source rawProfile ∧
        feature ∘ rawTarget = featureTarget := by
  classical
  simp [conditionalTypedFeatureFiber]

/-- A source-aware conditional fine fiber is canonically an ordinary typed-word fiber on the
joint alphabet. -/
noncomputable def conditionalTypedFeatureFiberEquivTypedWordMapFiber
    (source : Fin n → Cell) (feature : Raw → Feature)
    (rawProfile : Cell × Raw → ℕ) (featureTarget : Fin n → Feature) :
    {rawTarget // rawTarget ∈
        conditionalTypedFeatureFiber source feature rawProfile featureTarget} ≃
      {fineJoint // fineJoint ∈
        typedWordMapFiber (conditionalFeatureMap feature) rawProfile
          (jointWord source featureTarget)} where
  toFun rawTarget := ⟨jointWord source rawTarget.1, by
    rw [mem_typedWordMapFiber]
    have htarget := mem_conditionalTypedFeatureFiber.mp rawTarget.2
    refine ⟨mem_conditionalTypeClass.mp htarget.1, ?_⟩
    rw [conditionalFeatureMap_jointWord, htarget.2]⟩
  invFun fineJoint := ⟨fun i ↦ (fineJoint.1 i).2, by
    rw [mem_conditionalTypedFeatureFiber]
    have hword := mem_typedWordMapFiber.mp fineJoint.2
    have hjoint : jointWord source (fun i ↦ (fineJoint.1 i).2) = fineJoint.1 := by
      funext i
      apply Prod.ext
      · have hi := congrFun hword.2 i
        have hi' : (fineJoint.1 i).1 = source i := by
          simpa [conditionalFeatureMap, jointWord, Function.comp_apply] using
            congrArg Prod.fst hi
        exact hi'.symm
      · rfl
    constructor
    · rw [mem_conditionalTypeClass, hjoint, hword.1]
    · funext i
      have hi := congrFun hword.2 i
      exact congrArg Prod.snd hi⟩
  left_inv rawTarget := by
    apply Subtype.ext
    funext i
    rfl
  right_inv fineJoint := by
    apply Subtype.ext
    funext i
    have hword := mem_typedWordMapFiber.mp fineJoint.2
    apply Prod.ext
    · have hi := congrFun hword.2 i
      have hi' : (fineJoint.1 i).1 = source i := by
        simpa [conditionalFeatureMap, jointWord, Function.comp_apply] using
          congrArg Prod.fst hi
      exact hi'.symm
    · rfl

omit [Fintype Feature] in
/-- Cardinal form of `conditionalTypedFeatureFiberEquivTypedWordMapFiber`. -/
theorem card_conditionalTypedFeatureFiber_eq_card_typedWordMapFiber
    (source : Fin n → Cell) (feature : Raw → Feature)
    (rawProfile : Cell × Raw → ℕ) (featureTarget : Fin n → Feature) :
    (conditionalTypedFeatureFiber
        source feature rawProfile featureTarget).card =
      (typedWordMapFiber (conditionalFeatureMap feature) rawProfile
        (jointWord source featureTarget)).card := by
  classical
  rw [← Fintype.card_coe
      (conditionalTypedFeatureFiber source feature rawProfile featureTarget),
    ← Fintype.card_coe
      (typedWordMapFiber (conditionalFeatureMap feature) rawProfile
        (jointWord source featureTarget))]
  exact Fintype.card_congr
    (conditionalTypedFeatureFiberEquivTypedWordMapFiber
      source feature rawProfile featureTarget)

/-- Every exact pushed conditional word has a fine lift of the entire prescribed raw joint
type.  No injectivity of the feature map is assumed. -/
theorem exists_fineConditionalTarget_of_mem_pushedConditionalTypeClass
    (feature : Raw → Feature) (rawProfile : Cell × Raw → ℕ)
    (source : Fin n → Cell)
    (hraw : rawProfile ∈ types (Cell × Raw) n)
    (featureTarget : Fin n → Feature)
    (hfeatureTarget : featureTarget ∈ conditionalTypeClass source
      (mappedType (conditionalFeatureMap feature) rawProfile)) :
    ∃ rawTarget : Fin n → Raw,
      rawTarget ∈ conditionalTypeClass source rawProfile ∧
        feature ∘ rawTarget = featureTarget := by
  have htargetType : jointWord source featureTarget ∈
      typeClass n (mappedType (conditionalFeatureMap feature) rawProfile) := by
    rw [mem_typeClass]
    exact mem_conditionalTypeClass.mp hfeatureTarget
  have hfiberNonempty :
      (typedWordMapFiber (conditionalFeatureMap feature) rawProfile
        (jointWord source featureTarget)).Nonempty := by
    rw [← Finset.card_pos]
    have hfactor := card_targetType_mul_card_typedWordMapFiber
      (conditionalFeatureMap feature) rawProfile
        (jointWord source featureTarget) htargetType
    have hsource : 0 < (typeClass n rawProfile).card :=
      Finset.card_pos.mpr (typeClass_nonempty rawProfile hraw)
    have hproduct :
        0 < (typeClass n
            (mappedType (conditionalFeatureMap feature) rawProfile)).card *
          (typedWordMapFiber (conditionalFeatureMap feature) rawProfile
            (jointWord source featureTarget)).card := by
      rw [hfactor]
      exact hsource
    exact Nat.pos_of_mul_pos_left hproduct
  obtain ⟨fineJoint, hfineJoint⟩ := hfiberNonempty
  have hfine := mem_typedWordMapFiber.mp hfineJoint
  let rawTarget : Fin n → Raw := fun i ↦ (fineJoint i).2
  have hfirst (i : Fin n) : (fineJoint i).1 = source i := by
    have hi := congrFun hfine.2 i
    exact congrArg Prod.fst hi
  have hsecond (i : Fin n) : feature (fineJoint i).2 = featureTarget i := by
    have hi := congrFun hfine.2 i
    exact congrArg Prod.snd hi
  refine ⟨rawTarget, ?_, ?_⟩
  · rw [mem_conditionalTypeClass]
    have hjoint : jointWord source rawTarget = fineJoint := by
      funext i
      exact Prod.ext (hfirst i).symm rfl
    rw [hjoint, hfine.1]
  · funext i
    exact hsecond i

end AlgebraicComplexity.WordType
