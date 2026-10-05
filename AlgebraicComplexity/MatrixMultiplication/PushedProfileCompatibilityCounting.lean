import AlgebraicComplexity.Combinatorics.PushedProfileTypeCounting
import AlgebraicComplexity.MatrixMultiplication.CompatibilityIsolationCounting

/-!
# Pushed-profile bounds for compatibility competitor encodings

`CompatibilityIsolationCounting` deliberately ends at an exact injection of compatible labels
into a conditional word-type class.  This file supplies the analytic half of that interface when
the class is the pushforward of a finer prescribed joint profile.

The tensor-specific client remains responsible for constructing
`ConditionalCompatibleLabelEncoding`; in particular it must prove that a compatibility label is
recovered injectively as its quotient-feature word.  Once that finite fact is available, the
theorem below puts the competitor count in precisely the

`subexponential loss × fixed base ^ repetition`

form used to bound full-bucket field sizes.
-/

namespace AlgebraicComplexity.Tensor

open scoped BigOperators
open AlgebraicComplexity.WordType

universe u v w x

variable {A : Leg → Type u} [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]

namespace ConditionalCompetitorEncoding

/-- The fixed-address form used by compatibility isolation: once a concrete competitor encoding
has identified its exact joint type with a proportional pushed profile, its cardinality has the
certificate's quotient conditional-entropy bound. -/
theorem card_competitors_le_pushedConditionalTypeLoss_mul_entropyBase_pow
    {ambient : Finset (BlockAddress A)} {pivot : Leg}
    {compatible : A pivot → BlockAddress A → Prop}
    {address : BlockAddress A}
    {Cell Feature : Type v} {Raw : Type w}
    [Fintype Cell] [Fintype Raw] [Fintype Feature]
    (feature : Raw → Feature)
    (rawProfile : Cell × Raw → ℕ) (cellProfile : Cell → ℕ)
    (hmargin : mappedType Prod.fst rawProfile = cellProfile)
    (hmass : 0 < profileMass cellProfile)
    (k : ℕ) (hk : 0 < k)
    (encoding : ConditionalCompetitorEncoding ambient pivot compatible address
      Cell Feature (profileMass cellProfile * k))
    (hsource : multiplicity encoding.source =
      proportionalCounts cellProfile k)
    (hjoint : encoding.jointType =
      proportionalCounts
        (mappedType (conditionalFeatureMap feature) rawProfile) k) :
    ((compatibilityCompetitors ambient pivot compatible address).card : ℝ) ≤
      pushedConditionalTypeLoss cellProfile k *
        conditionalProfileEntropyBase cellProfile
          (mappedType (conditionalFeatureMap feature) rawProfile) ^ k := by
  have hfinite :
      ((conditionalTypeClass encoding.source
          (proportionalCounts
            (mappedType (conditionalFeatureMap feature) rawProfile) k)).card : ℝ) ≤
        pushedConditionalTypeLoss cellProfile k *
          conditionalProfileEntropyBase cellProfile
            (mappedType (conditionalFeatureMap feature) rawProfile) ^ k :=
    card_pushedConditionalTypeClass_le_loss_mul_entropyBase_pow
      feature rawProfile cellProfile hmargin hmass k hk encoding.source hsource
  have hencodingNat := encoding.card_competitors_le_card_conditionalTypeClass
  have hencodingReal :
      ((compatibilityCompetitors ambient pivot compatible address).card : ℝ) ≤
        ((conditionalTypeClass encoding.source encoding.jointType).card : ℝ) := by
    exact_mod_cast hencodingNat
  calc
    ((compatibilityCompetitors ambient pivot compatible address).card : ℝ) ≤
        ((conditionalTypeClass encoding.source encoding.jointType).card : ℝ) :=
      hencodingReal
    _ = ((conditionalTypeClass encoding.source
          (proportionalCounts
            (mappedType (conditionalFeatureMap feature) rawProfile) k)).card : ℝ) := by
      rw [hjoint]
    _ ≤ pushedConditionalTypeLoss cellProfile k *
        conditionalProfileEntropyBase cellProfile
          (mappedType (conditionalFeatureMap feature) rawProfile) ^ k := hfinite

/-- Length-transporting form used by positive-word clients, whose sample count is commonly
presented as `n + 1` together with an exact divisibility equation. -/
theorem card_competitors_le_pushedConditionalTypeLoss_mul_entropyBase_pow_of_length
    {ambient : Finset (BlockAddress A)} {pivot : Leg}
    {compatible : A pivot → BlockAddress A → Prop}
    {address : BlockAddress A}
    {Cell Feature : Type v} {Raw : Type w}
    [Fintype Cell] [Fintype Raw] [Fintype Feature]
    (feature : Raw → Feature)
    (rawProfile : Cell × Raw → ℕ) (cellProfile : Cell → ℕ)
    (hmargin : mappedType Prod.fst rawProfile = cellProfile)
    (hmass : 0 < profileMass cellProfile)
    (k : ℕ) (hk : 0 < k) {n : ℕ}
    (encoding : ConditionalCompetitorEncoding ambient pivot compatible address
      Cell Feature n)
    (hlength : n = profileMass cellProfile * k)
    (hsource : multiplicity encoding.source =
      proportionalCounts cellProfile k)
    (hjoint : encoding.jointType =
      proportionalCounts
        (mappedType (conditionalFeatureMap feature) rawProfile) k) :
    ((compatibilityCompetitors ambient pivot compatible address).card : ℝ) ≤
      pushedConditionalTypeLoss cellProfile k *
        conditionalProfileEntropyBase cellProfile
          (mappedType (conditionalFeatureMap feature) rawProfile) ^ k := by
  subst n
  exact encoding.card_competitors_le_pushedConditionalTypeLoss_mul_entropyBase_pow
    feature rawProfile cellProfile hmargin hmass k hk hsource hjoint

/-- Aggregate a uniform family of exact pushed-profile competitor encodings into the directed
incidence bound used by compatibility isolation.  The theorem deliberately indexes encodings by
the actual ambient address, so no choice of a representative address or quotient fiber is hidden
in the asymptotic interface. -/
theorem compatibilityCompetitorIncidence_le_card_mul_pushedConditionalTypeBound
    {ambient : Finset (BlockAddress A)} {pivot : Leg}
    {compatible : A pivot → BlockAddress A → Prop}
    {Cell Feature : Type v} {Raw : Type w}
    [Fintype Cell] [Fintype Raw] [Fintype Feature]
    (feature : Raw → Feature)
    (rawProfile : Cell × Raw → ℕ) (cellProfile : Cell → ℕ)
    (hmargin : mappedType Prod.fst rawProfile = cellProfile)
    (hmass : 0 < profileMass cellProfile)
    (k : ℕ) (hk : 0 < k) {n : ℕ}
    (encodings : ∀ address : {address // address ∈ ambient},
      ConditionalCompetitorEncoding ambient pivot compatible address.1
        Cell Feature n)
    (hlength : n = profileMass cellProfile * k)
    (hsource : ∀ address,
      multiplicity (encodings address).source =
        proportionalCounts cellProfile k)
    (hjoint : ∀ address,
      (encodings address).jointType =
        proportionalCounts
          (mappedType (conditionalFeatureMap feature) rawProfile) k) :
    (compatibilityCompetitorIncidence ambient pivot compatible : ℝ) ≤
      (ambient.card : ℝ) *
        (pushedConditionalTypeLoss cellProfile k *
          conditionalProfileEntropyBase cellProfile
            (mappedType (conditionalFeatureMap feature) rawProfile) ^ k) := by
  classical
  have hpoint : ∀ address ∈ ambient,
      ((compatibilityCompetitors ambient pivot compatible address).card : ℝ) ≤
        pushedConditionalTypeLoss cellProfile k *
          conditionalProfileEntropyBase cellProfile
            (mappedType (conditionalFeatureMap feature) rawProfile) ^ k := by
    intro address haddress
    exact (encodings ⟨address, haddress⟩
      ).card_competitors_le_pushedConditionalTypeLoss_mul_entropyBase_pow_of_length
        feature rawProfile cellProfile hmargin hmass k hk hlength
          (hsource ⟨address, haddress⟩) (hjoint ⟨address, haddress⟩)
  have hsum :
      ∑ address ∈ ambient,
          ((compatibilityCompetitors ambient pivot compatible address).card : ℝ) ≤
        ∑ _address ∈ ambient,
          (pushedConditionalTypeLoss cellProfile k *
            conditionalProfileEntropyBase cellProfile
              (mappedType (conditionalFeatureMap feature) rawProfile) ^ k) := by
    exact Finset.sum_le_sum fun address haddress ↦ hpoint address haddress
  simpa [compatibilityCompetitorIncidence] using hsum

end ConditionalCompetitorEncoding

namespace ConditionalCompatibleLabelEncoding

/-- A compatible-label encoding whose joint type is an exact proportional pushed profile has
the quotient conditional-entropy bound.  `pushedConditionalTypeLoss` is positive and
subexponential by the generic theorems in `PushedProfileTypeCounting`. -/
theorem card_compatibleLabels_le_pushedConditionalTypeLoss_mul_entropyBase_pow
    {pivot : Leg} {labels : Finset (A pivot)}
    {compatible : A pivot → BlockAddress A → Prop}
    {address : BlockAddress A}
    {Cell : Type v} {Raw : Type w} {Feature : Type x}
    [Fintype Cell] [Fintype Raw] [Fintype Feature]
    (feature : Raw → Feature)
    (rawProfile : Cell × Raw → ℕ) (cellProfile : Cell → ℕ)
    (hmargin : mappedType Prod.fst rawProfile = cellProfile)
    (hmass : 0 < profileMass cellProfile)
    (k : ℕ) (hk : 0 < k)
    (encoding : ConditionalCompatibleLabelEncoding labels compatible address
      Cell Feature (profileMass cellProfile * k))
    (hsource : multiplicity encoding.source =
      proportionalCounts cellProfile k)
    (hjoint : encoding.jointType =
      proportionalCounts
        (mappedType (conditionalFeatureMap feature) rawProfile) k) :
    ((compatibleLabels labels compatible address).card : ℝ) ≤
      pushedConditionalTypeLoss cellProfile k *
        conditionalProfileEntropyBase cellProfile
          (mappedType (conditionalFeatureMap feature) rawProfile) ^ k := by
  have hfinite :
      ((conditionalTypeClass encoding.source
          (proportionalCounts
            (mappedType (conditionalFeatureMap feature) rawProfile) k)).card : ℝ) ≤
        pushedConditionalTypeLoss cellProfile k *
          conditionalProfileEntropyBase cellProfile
            (mappedType (conditionalFeatureMap feature) rawProfile) ^ k :=
    card_pushedConditionalTypeClass_le_loss_mul_entropyBase_pow
      feature rawProfile cellProfile hmargin hmass k hk encoding.source hsource
  have hencodingNat := encoding.card_compatibleLabels_le_card_conditionalTypeClass
  have hencodingReal :
      ((compatibleLabels labels compatible address).card : ℝ) ≤
        ((conditionalTypeClass encoding.source encoding.jointType).card : ℝ) := by
    exact_mod_cast hencodingNat
  calc
    ((compatibleLabels labels compatible address).card : ℝ) ≤
        ((conditionalTypeClass encoding.source encoding.jointType).card : ℝ) :=
      hencodingReal
    _ = ((conditionalTypeClass encoding.source
          (proportionalCounts
            (mappedType (conditionalFeatureMap feature) rawProfile) k)).card : ℝ) := by
      rw [hjoint]
    _ ≤ pushedConditionalTypeLoss cellProfile k *
        conditionalProfileEntropyBase cellProfile
          (mappedType (conditionalFeatureMap feature) rawProfile) ^ k := hfinite

/-- Length-transporting transposed-label form. -/
theorem card_compatibleLabels_le_pushedConditionalTypeLoss_mul_entropyBase_pow_of_length
    {pivot : Leg} {labels : Finset (A pivot)}
    {compatible : A pivot → BlockAddress A → Prop}
    {address : BlockAddress A}
    {Cell : Type v} {Raw : Type w} {Feature : Type x}
    [Fintype Cell] [Fintype Raw] [Fintype Feature]
    (feature : Raw → Feature)
    (rawProfile : Cell × Raw → ℕ) (cellProfile : Cell → ℕ)
    (hmargin : mappedType Prod.fst rawProfile = cellProfile)
    (hmass : 0 < profileMass cellProfile)
    (k : ℕ) (hk : 0 < k) {n : ℕ}
    (encoding : ConditionalCompatibleLabelEncoding labels compatible address
      Cell Feature n)
    (hlength : n = profileMass cellProfile * k)
    (hsource : multiplicity encoding.source =
      proportionalCounts cellProfile k)
    (hjoint : encoding.jointType =
      proportionalCounts
        (mappedType (conditionalFeatureMap feature) rawProfile) k) :
    ((compatibleLabels labels compatible address).card : ℝ) ≤
      pushedConditionalTypeLoss cellProfile k *
        conditionalProfileEntropyBase cellProfile
          (mappedType (conditionalFeatureMap feature) rawProfile) ^ k := by
  subst n
  exact encoding.card_compatibleLabels_le_pushedConditionalTypeLoss_mul_entropyBase_pow
    feature rawProfile cellProfile hmargin hmass k hk hsource hjoint

end ConditionalCompatibleLabelEncoding

end AlgebraicComplexity.Tensor
