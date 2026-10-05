/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinogradTotalWeightFeatureGrowth
import AlgebraicComplexity.Examples.CoppersmithWinogradTotalWeightNestedComposition
import AlgebraicComplexity.MatrixMultiplication.WholeConstituentFullBucketSequence
import AlgebraicComplexity.Combinatorics.PrimeFieldSizing

set_option autoImplicit false

/-!
# Full-bucket construction of the total-weight outer sequence

The finite total-weight proof has two numerically distinct stages before the inner typed-family
extraction:

* a target family grows with base `targetBase`; and
* one full-bucket affine hash loses a field whose cardinality grows with base `fieldBase`.

This file packages the actual surviving whole-constituent families into
`CWTotalWeightLocalizedOuterSequenceData`.  The copy-growth inequality is proved here from the
finite full-bucket count; clients do not supply it again as an opaque asymptotic premise.

The remaining certificate-specific inputs are intentionally concrete: the finite survivor type,
its coarse word, the restriction to the indexed direct sum of localized whole fine families, and
the target/field cardinality inequalities.  Compatibility counting supplies the field inequality;
hashing and cleanup supply the finite count and restriction.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor

universe u v w

namespace CWTotalWeightLocalizedOuterSequenceData

/-- Build the outer total-weight sequence directly from full-bucket finite stages.

The result has copy base `outerBase`; `hbase` identifies it with the quotient of the target-family
and field bases.  Its loss is the explicit positive subexponential factor
`fullBucketSequenceLoss targetLoss fieldLoss`.

Unlike the fully generic `FullBucketWholeConstituentSequenceData`, the finite outputs here are
whole localized CW fine families, not matrix-multiplication tensors.  They can therefore be fed
without loss to `CanonicalInnerSequenceData` and retain the separate `E2` exponent. -/
noncomputable def ofFullBucketHashCount
    (K : Type u) [CommRing K] (q depth : ℕ)
    {Source : Leg → Type v}
    [∀ c, AddCommMonoid (Source c)] [∀ c, Module K (Source c)]
    (T : Tensor3 K Source)
    (stride : ℕ) (targetBase fieldBase outerBase : ℝ)
    (hstride : 0 < stride) (htargetBase : 0 < targetBase)
    (hfieldBase : 0 < fieldBase)
    (hbase : outerBase = targetBase / fieldBase)
    (targetLoss fieldLoss : ℕ → ℝ)
    (targetCount fieldCard : ℕ → ℕ)
    (n : ℕ → ℕ)
    (fineType : ℕ → Leg → PositiveWord CWBlock (2 ^ depth - 1) → ℕ)
    (I : ℕ → Type w) [fintypeI : ∀ r, Fintype (I r)]
    (coarseWord : ∀ r,
      I r → PositiveWord (CWTotalWeightCoarseSupport K q depth) (n r))
    (htargetLoss : Growth.Subexponential targetLoss)
    (hfieldLoss : Growth.Subexponential fieldLoss)
    (htargetLossPos : ∀ r, 0 < r → 0 < targetLoss r)
    (hfieldLossPos : ∀ r, 0 < r → 0 < fieldLoss r)
    (hcountPos : ∀ r, 0 < r → 0 < Fintype.card (I r))
    (hsource : ∀ r, 0 < r → Restricts
      (Tensor.power T (stride * r))
      (Tensor.indexedDirectSum (fun i : I r ↦
        (cwTotalWeightLocalizedFineTypes K q depth (n r)
          (positiveSupportWordBlockAddress
            (CWTotalWeightCoarseSupport K q depth) (n r) (coarseWord r i))
          (fineType r)).realize)))
    (htargetGrowth : ∀ r, 0 < r →
      targetBase ^ r ≤ targetLoss r * (targetCount r : ℝ))
    (hfieldGrowth : ∀ r, 0 < r →
      (fieldCard r : ℝ) ≤ fieldLoss r * fieldBase ^ r)
    (hhash : ∀ r, 0 < r →
      3 * targetCount r ≤ 8 * fieldCard r * Fintype.card (I r)) :
    CWTotalWeightLocalizedOuterSequenceData.{u, v, w}
      K q depth T stride outerBase where
  stride_pos := hstride
  outerBase_pos := by
    rw [hbase]
    exact div_pos htargetBase hfieldBase
  loss := fullBucketSequenceLoss targetLoss fieldLoss
  count := fun r ↦ Fintype.card (I r)
  n := n
  fineType := fineType
  I := I
  fintypeI := fintypeI
  coarseWord := coarseWord
  card_I := fun _r ↦ rfl
  loss_subexponential :=
    fullBucketSequenceLoss_subexponential htargetLoss hfieldLoss
  loss_pos := fullBucketSequenceLoss_pos targetLoss fieldLoss
    htargetLossPos hfieldLossPos
  count_pos := hcountPos
  source_restricts := hsource
  copy_growth := by
    intro r hr
    rw [hbase]
    exact copy_growth_of_fullBucket_hashCount
      targetBase fieldBase targetLoss fieldLoss r
      (targetCount r) (fieldCard r) (Fintype.card (I r))
      hfieldBase (le_of_lt (htargetLossPos r hr))
      (le_of_lt (hfieldLossPos r hr))
      (htargetGrowth r hr) (hfieldGrowth r hr) (hhash r hr)

/-- The exponential base of the outer hashing field must dominate three different finite
families: competitors sharing the hashed `X` block and the two directed compatibility-hole
families.  The first maximum is explicit because the `X`-fiber is not one of the evaluator-visible
`Y`/`Z` feature classes. -/
noncomputable def combinedFieldBase
    (xBase visibleBase : ℝ) : ℝ :=
  max 1 (max xBase visibleBase)

theorem one_le_combinedFieldBase (xBase visibleBase : ℝ) :
    1 ≤ combinedFieldBase xBase visibleBase :=
  le_max_left _ _

theorem combinedFieldBase_pos (xBase visibleBase : ℝ) :
    0 < combinedFieldBase xBase visibleBase :=
  zero_lt_one.trans_le (one_le_combinedFieldBase xBase visibleBase)

/-- Subexponential factor obtained by combining the `X`-fiber and compatibility-feature field
requirements. -/
noncomputable def combinedFieldLoss
    (xLoss visibleLoss : ℕ → ℝ) (r : ℕ) : ℝ :=
  xLoss r + visibleLoss r

theorem combinedFieldLoss_subexponential
    {xLoss visibleLoss : ℕ → ℝ}
    (hx : Growth.Subexponential xLoss)
    (hvisible : Growth.Subexponential visibleLoss) :
    Growth.Subexponential (combinedFieldLoss xLoss visibleLoss) := by
  exact hx.add hvisible

theorem combinedFieldLoss_pos
    (xLoss visibleLoss : ℕ → ℝ)
    (hx : ∀ r, 0 < r → 0 < xLoss r)
    (hvisible : ∀ r, 0 < r → 0 < visibleLoss r)
    (r : ℕ) (hr : 0 < r) :
    0 < combinedFieldLoss xLoss visibleLoss r := by
  exact add_pos (hx r hr) (hvisible r hr)

/-- The canonical prime chosen from the combined requirement automatically discharges the exact
affine `X` quarter budget once the source-side competitor count has been bounded by
`xRequirement`.  This is the result a concrete coarse-hashing client should pass to
`exists_seed_many_xIsolatedCoarseSupport`. -/
theorem xQuarter_le_card_combinedPrimeField
    (characteristicFloor xRequirement visibleRequirement competitors : ℕ)
    (hx : 4 * competitors ≤ xRequirement) :
    4 * competitors ≤
      Fintype.card (ZMod (PrimeFieldSizing.modulus characteristicFloor
        (max xRequirement visibleRequirement))) := by
  rw [ZMod.card]
  exact hx.trans (Nat.le_max_left _ _ |>.trans
    (Nat.le_of_lt (PrimeFieldSizing.requirement_lt_modulus characteristicFloor
      (max xRequirement visibleRequirement))))

/-- The same canonical prime strictly dominates the exact compatibility half-retention
requirement.  This theorem and `xQuarter_le_card_combinedPrimeField` ensure that the two finite
passes use one and the same field. -/
theorem visibleRequirement_lt_card_combinedPrimeField
    (characteristicFloor xRequirement visibleRequirement : ℕ) :
    visibleRequirement <
      Fintype.card (ZMod (PrimeFieldSizing.modulus characteristicFloor
        (max xRequirement visibleRequirement))) := by
  rw [ZMod.card]
  exact (Nat.le_max_right xRequirement visibleRequirement).trans_lt
    (PrimeFieldSizing.requirement_lt_modulus characteristicFloor
      (max xRequirement visibleRequirement))

/-- Two separately certified natural field requirements have the common exponential bound
obtained by taking the maximum of their exact values and the maximum of their exponential bases.

The `xRequirement` input is intended to dominate
`4 * |xCompetitorYIndices|`; `visibleRequirement` is the total-weight `Y/Z` half-retention
requirement. -/
theorem max_requirement_cast_le_combinedFieldLoss_mul_pow
    (xRequirement visibleRequirement r : ℕ)
    (xLoss visibleLoss xBase visibleBase : ℝ)
    (hxLoss : 0 ≤ xLoss) (hvisibleLoss : 0 ≤ visibleLoss)
    (hxBase : 0 ≤ xBase) (hvisibleBase : 0 ≤ visibleBase)
    (hx : (xRequirement : ℝ) ≤ xLoss * xBase ^ r)
    (hvisible : (visibleRequirement : ℝ) ≤
      visibleLoss * visibleBase ^ r) :
    ((max xRequirement visibleRequirement : ℕ) : ℝ) ≤
      (xLoss + visibleLoss) * combinedFieldBase xBase visibleBase ^ r := by
  have hxPow : xBase ^ r ≤ combinedFieldBase xBase visibleBase ^ r := by
    exact pow_le_pow_left₀ hxBase
      ((le_max_left _ _).trans (le_max_right _ _)) r
  have hvisiblePow : visibleBase ^ r ≤
      combinedFieldBase xBase visibleBase ^ r := by
    exact pow_le_pow_left₀ hvisibleBase
      ((le_max_right _ _).trans (le_max_right _ _)) r
  rw [Nat.cast_max]
  apply max_le
  · calc
      (xRequirement : ℝ) ≤ xLoss * xBase ^ r := hx
      _ ≤ xLoss * combinedFieldBase xBase visibleBase ^ r := by gcongr
      _ ≤ (xLoss + visibleLoss) *
          combinedFieldBase xBase visibleBase ^ r := by
        exact mul_le_mul_of_nonneg_right (by linarith)
          (pow_nonneg (combinedFieldBase_pos xBase visibleBase).le r)
  · calc
      (visibleRequirement : ℝ) ≤ visibleLoss * visibleBase ^ r := hvisible
      _ ≤ visibleLoss * combinedFieldBase xBase visibleBase ^ r := by gcongr
      _ ≤ (xLoss + visibleLoss) *
          combinedFieldBase xBase visibleBase ^ r := by
        exact mul_le_mul_of_nonneg_right (by linarith)
          (pow_nonneg (combinedFieldBase_pos xBase visibleBase).le r)

/-- Arithmetic packaging for a finite full-bucket extraction whose *single* prime dominates both
the initial `X`-isolation degree and the later `Y/Z` compatibility-hole requirement.

This is deliberately named `...FullBucketCount`: it does not manufacture the finite hash stage.
The `hfinite` premise must come from the concrete theorem that uses this same modulus to prove the
`X` quarter bound, compatibility half-retention, and the resulting survivor count.  Its two
arguments explicitly expose that the chosen modulus dominates both exact natural requirements;
passing an independently postulated survivor-count inequality is not the final certificate
interface.

Bertrand rounding and the combined field-growth accounting are discharged internally. -/
noncomputable def ofCombinedPrimeFullBucketCount
    (K : Type u) [CommRing K] (q depth : ℕ)
    {Source : Leg → Type v}
    [∀ c, AddCommMonoid (Source c)] [∀ c, Module K (Source c)]
    (T : Tensor3 K Source)
    (stride : ℕ) (targetBase xFieldBase outerBase : ℝ)
    (hstride : 0 < stride) (htargetBase : 0 < targetBase)
    (hxFieldBase : 0 ≤ xFieldBase)
    {Part : Type} [Fintype Part]
    (ySourceProfile zSourceProfile : CWCoarseDigit depth → ℕ)
    (yJointExponentPerRepetition zJointExponentPerRepetition : ℝ)
    (hbase : outerBase = targetBase /
      combinedFieldBase xFieldBase
        (cwTotalWeightVisibleFeatureFieldBase
          ySourceProfile zSourceProfile
          yJointExponentPerRepetition zJointExponentPerRepetition))
    (characteristicFloor : ℕ)
    (targetLoss xFieldLoss : ℕ → ℝ)
    (targetCount xRequirement visibleRequirement : ℕ → ℕ)
    (n : ℕ → ℕ)
    (fineType : ℕ → Leg → PositiveWord CWBlock (2 ^ depth - 1) → ℕ)
    (I : ℕ → Type w) [fintypeI : ∀ r, Fintype (I r)]
    (coarseWord : ∀ r,
      I r → PositiveWord (CWTotalWeightCoarseSupport K q depth) (n r))
    (htargetLoss : Growth.Subexponential targetLoss)
    (hxFieldLoss : Growth.Subexponential xFieldLoss)
    (htargetLossPos : ∀ r, 0 < r → 0 < targetLoss r)
    (hxFieldLossPos : ∀ r, 0 < r → 0 < xFieldLoss r)
    (hcountPos : ∀ r, 0 < r → 0 < Fintype.card (I r))
    (hsource : ∀ r, 0 < r → Restricts
      (Tensor.power T (stride * r))
      (Tensor.indexedDirectSum (fun i : I r ↦
        (cwTotalWeightLocalizedFineTypes K q depth (n r)
          (positiveSupportWordBlockAddress
            (CWTotalWeightCoarseSupport K q depth) (n r) (coarseWord r i))
          (fineType r)).realize)))
    (htargetGrowth : ∀ r, 0 < r →
      targetBase ^ r ≤ targetLoss r * (targetCount r : ℝ))
    (hxRequirement : ∀ r, 0 < r →
      (xRequirement r : ℝ) ≤ xFieldLoss r * xFieldBase ^ r)
    (hvisibleRequirement : ∀ r, 0 < r →
      (visibleRequirement r : ℝ) ≤
        cwTotalWeightVisibleFeatureFieldLoss
            depth Part ySourceProfile zSourceProfile r *
          cwTotalWeightVisibleFeatureFieldBase
            ySourceProfile zSourceProfile
            yJointExponentPerRepetition zJointExponentPerRepetition ^ r)
    (hfinite : ∀ r, 0 < r →
      xRequirement r < PrimeFieldSizing.modulus characteristicFloor
          (max (xRequirement r) (visibleRequirement r)) →
      visibleRequirement r < PrimeFieldSizing.modulus characteristicFloor
          (max (xRequirement r) (visibleRequirement r)) →
      3 * targetCount r ≤
        8 * PrimeFieldSizing.modulus characteristicFloor
            (max (xRequirement r) (visibleRequirement r)) *
          Fintype.card (I r)) :
    CWTotalWeightLocalizedOuterSequenceData.{u, v, w}
      K q depth T stride outerBase := by
  let visibleLoss : ℕ → ℝ :=
    cwTotalWeightVisibleFeatureFieldLoss
      depth Part ySourceProfile zSourceProfile
  let visibleBase : ℝ :=
    cwTotalWeightVisibleFeatureFieldBase
      ySourceProfile zSourceProfile
      yJointExponentPerRepetition zJointExponentPerRepetition
  let fieldBase : ℝ := combinedFieldBase xFieldBase visibleBase
  let fieldInputLoss : ℕ → ℝ := combinedFieldLoss xFieldLoss visibleLoss
  let primeLoss : ℕ → ℝ :=
    PrimeFieldSizing.loss characteristicFloor fieldInputLoss
  apply ofFullBucketHashCount K q depth T stride targetBase fieldBase outerBase
    hstride htargetBase
    (combinedFieldBase_pos xFieldBase visibleBase)
    hbase targetLoss primeLoss targetCount
    (fun r ↦ PrimeFieldSizing.modulus characteristicFloor
      (max (xRequirement r) (visibleRequirement r)))
    n fineType I coarseWord htargetLoss
  · exact PrimeFieldSizing.loss_subexponential characteristicFloor
      (combinedFieldLoss_subexponential hxFieldLoss
        (cwTotalWeightVisibleFeatureFieldLoss_subexponential
          depth Part ySourceProfile zSourceProfile))
  · exact htargetLossPos
  · intro r _hr
    dsimp only [primeLoss, PrimeFieldSizing.loss, fieldInputLoss]
    have hcombinedLoss := combinedFieldLoss_pos xFieldLoss visibleLoss
      hxFieldLossPos
      (fun s _hs ↦ cwTotalWeightVisibleFeatureFieldLoss_pos
        depth Part ySourceProfile zSourceProfile s)
      r _hr
    positivity
  · exact hcountPos
  · exact hsource
  · exact htargetGrowth
  · intro r hr
    have hrequirement :
        ((max (xRequirement r) (visibleRequirement r) : ℕ) : ℝ) ≤
          fieldInputLoss r * fieldBase ^ r := by
      exact max_requirement_cast_le_combinedFieldLoss_mul_pow
        (xRequirement r) (visibleRequirement r) r
        (xFieldLoss r) (visibleLoss r) xFieldBase visibleBase
        (le_of_lt (hxFieldLossPos r hr))
        (le_of_lt (cwTotalWeightVisibleFeatureFieldLoss_pos
          depth Part ySourceProfile zSourceProfile r))
        hxFieldBase (le_of_lt (cwTotalWeightVisibleFeatureFieldBase_pos
          ySourceProfile zSourceProfile
          yJointExponentPerRepetition zJointExponentPerRepetition))
        (hxRequirement r hr) (hvisibleRequirement r hr)
    simpa only [primeLoss, PrimeFieldSizing.loss, add_assoc] using
      PrimeFieldSizing.modulus_cast_le_loss_mul_pow
      characteristicFloor (max (xRequirement r) (visibleRequirement r)) r
      (fieldInputLoss r) fieldBase
      (one_le_combinedFieldBase xFieldBase visibleBase) hrequirement
  · intro r hr
    apply hfinite r hr
    · exact (Nat.le_max_left (xRequirement r) (visibleRequirement r)).trans_lt
        (PrimeFieldSizing.requirement_lt_modulus characteristicFloor
          (max (xRequirement r) (visibleRequirement r)))
    · exact (Nat.le_max_right (xRequirement r) (visibleRequirement r)).trans_lt
        (PrimeFieldSizing.requirement_lt_modulus characteristicFloor
          (max (xRequirement r) (visibleRequirement r)))

end CWTotalWeightLocalizedOuterSequenceData

end AlgebraicComplexity.Examples
