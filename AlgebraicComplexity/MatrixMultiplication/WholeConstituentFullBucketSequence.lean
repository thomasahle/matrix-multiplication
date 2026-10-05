import AlgebraicComplexity.MatrixMultiplication.WholeConstituentLaserVolume

/-!
# Full-bucket hashing to whole-constituent extraction sequences

When every field element is an allowed hash bucket, the finite sorted-pair count has the generic
shape

`3 * targetCount ≤ 8 * fieldCard * finalCount`.

If target counts have exponential base `targetBase` and the required field sizes have exponential
base `fieldBase`, the surviving copy base is their quotient.  This module packages that algebra,
including arbitrary positive subexponential losses, into
`WholeConstituentLaserVolumeSequenceData`.  It is independent of CW tensors and of the concrete
conditional-type bounds used to choose the field.
-/

namespace AlgebraicComplexity

open Tensor

universe u v

/-- Positive loss left after combining target-family counting, the constant `8/3` hash loss,
and the upper bound on the chosen field size. -/
noncomputable def fullBucketSequenceLoss
    (targetLoss fieldLoss : ℕ → ℝ) (r : ℕ) : ℝ :=
  (8 / 3 : ℝ) * targetLoss r * fieldLoss r

theorem fullBucketSequenceLoss_pos
    (targetLoss fieldLoss : ℕ → ℝ)
    (htarget : ∀ r, 0 < r → 0 < targetLoss r)
    (hfield : ∀ r, 0 < r → 0 < fieldLoss r)
    (r : ℕ) (hr : 0 < r) :
    0 < fullBucketSequenceLoss targetLoss fieldLoss r := by
  unfold fullBucketSequenceLoss
  exact mul_pos (mul_pos (by norm_num) (htarget r hr)) (hfield r hr)

theorem fullBucketSequenceLoss_subexponential
    {targetLoss fieldLoss : ℕ → ℝ}
    (htarget : Growth.Subexponential targetLoss)
    (hfield : Growth.Subexponential fieldLoss) :
    Growth.Subexponential (fullBucketSequenceLoss targetLoss fieldLoss) := by
  have hproduct := htarget.mul hfield
  unfold fullBucketSequenceLoss
  convert hproduct.const_mul (by norm_num : (0 : ℝ) ≤ 8 / 3) using 1
  funext n
  ring

/-- Directed one-repetition algebra for full-bucket hashing.

The exact finite hash inequality loses one factor of `fieldCard`.  An exponential upper bound
on that field cardinality therefore subtracts `log fieldBase` from the target copy exponent;
all remaining factors are placed in `fullBucketSequenceLoss`. -/
theorem copy_growth_of_fullBucket_hashCount
    (targetBase fieldBase : ℝ)
    (targetLoss fieldLoss : ℕ → ℝ)
    (r targetCount fieldCard finalCount : ℕ)
    (hfieldBase : 0 < fieldBase)
    (htargetLoss : 0 ≤ targetLoss r)
    (_hfieldLoss : 0 ≤ fieldLoss r)
    (htargetGrowth : targetBase ^ r ≤ targetLoss r * (targetCount : ℝ))
    (hfieldGrowth : (fieldCard : ℝ) ≤ fieldLoss r * fieldBase ^ r)
    (hhash : 3 * targetCount ≤ 8 * fieldCard * finalCount) :
    (targetBase / fieldBase) ^ r ≤
      fullBucketSequenceLoss targetLoss fieldLoss r * (finalCount : ℝ) := by
  have hhashReal : (3 : ℝ) * targetCount ≤
      8 * fieldCard * finalCount := by
    exact_mod_cast hhash
  have htargetCount : (targetCount : ℝ) ≤
      (8 / 3 : ℝ) * fieldCard * finalCount := by
    nlinarith
  rw [div_pow]
  apply (div_le_iff₀ (pow_pos hfieldBase r)).2
  calc
    targetBase ^ r ≤ targetLoss r * (targetCount : ℝ) := htargetGrowth
    _ ≤ targetLoss r *
        ((8 / 3 : ℝ) * fieldCard * finalCount) :=
      mul_le_mul_of_nonneg_left htargetCount htargetLoss
    _ ≤ targetLoss r *
        ((8 / 3 : ℝ) * (fieldLoss r * fieldBase ^ r) * finalCount) := by
      gcongr
    _ = fullBucketSequenceLoss targetLoss fieldLoss r *
        (finalCount : ℝ) * fieldBase ^ r := by
      unfold fullBucketSequenceLoss
      ring

section Sequence

variable (K : Type u) [CommSemiring K]
variable {Source : Leg → Type v}
variable [∀ c, AddCommMonoid (Source c)] [∀ c, Module K (Source c)]

/-- Candidate-independent data for converting full-bucket finite stages into an asymptotic
whole-constituent sequence.  `fieldCard` may grow exponentially; its base is divided out of the
target-family base, while `fieldLoss` must be subexponential. -/
structure FullBucketWholeConstituentSequenceData
    (T : Tensor3 K Source) (stride : ℕ)
    (targetBase fieldBase volumeBase : ℝ) where
  stride_pos : 0 < stride
  targetBase_pos : 0 < targetBase
  fieldBase_pos : 0 < fieldBase
  volumeBase_pos : 0 < volumeBase
  targetLoss : ℕ → ℝ
  fieldLoss : ℕ → ℝ
  targetCount : ℕ → ℕ
  fieldCard : ℕ → ℕ
  finalCount : ℕ → ℕ
  xSize : ℕ → ℕ
  ySize : ℕ → ℕ
  zSize : ℕ → ℕ
  targetLoss_subexponential : Growth.Subexponential targetLoss
  fieldLoss_subexponential : Growth.Subexponential fieldLoss
  targetLoss_pos : ∀ r, 0 < r → 0 < targetLoss r
  fieldLoss_pos : ∀ r, 0 < r → 0 < fieldLoss r
  targetCount_pos : ∀ r, 0 < r → 0 < targetCount r
  fieldCard_pos : ∀ r, 0 < r → 0 < fieldCard r
  finalCount_pos : ∀ r, 0 < r → 0 < finalCount r
  xSize_pos : ∀ r, 0 < r → 0 < xSize r
  ySize_pos : ∀ r, 0 < r → 0 < ySize r
  zSize_pos : ∀ r, 0 < r → 0 < zSize r
  stage : ∀ r, 0 < r →
    WholeConstituentLaserVolumeStage K (Tensor.power T (stride * r))
      (finalCount r) (xSize r) (ySize r) (zSize r)
  target_growth : ∀ r, 0 < r →
    targetBase ^ r ≤ targetLoss r * (targetCount r : ℝ)
  field_growth : ∀ r, 0 < r →
    (fieldCard r : ℝ) ≤ fieldLoss r * fieldBase ^ r
  fullBucket_hash_count : ∀ r, 0 < r →
    3 * targetCount r ≤ 8 * fieldCard r * finalCount r
  volume_growth : ∀ r, 0 < r →
    volumeBase ^ r ≤ (((xSize r * ySize r * zSize r : ℕ) : ℝ))

namespace FullBucketWholeConstituentSequenceData

/-- Full-bucket sequence data yields the standard whole-constituent sequence with copy base
`targetBase / fieldBase`. -/
noncomputable def toWholeConstituentLaserVolumeSequenceData
    {T : Tensor3 K Source} {stride : ℕ}
    {targetBase fieldBase volumeBase : ℝ}
    (data : FullBucketWholeConstituentSequenceData K T stride
      targetBase fieldBase volumeBase) :
    WholeConstituentLaserVolumeSequenceData K T stride
      (targetBase / fieldBase) volumeBase where
  stride_pos := data.stride_pos
  copyBase_pos := div_pos data.targetBase_pos data.fieldBase_pos
  volumeBase_pos := data.volumeBase_pos
  loss := fullBucketSequenceLoss data.targetLoss data.fieldLoss
  count := data.finalCount
  xSize := data.xSize
  ySize := data.ySize
  zSize := data.zSize
  loss_subexponential := fullBucketSequenceLoss_subexponential
    data.targetLoss_subexponential data.fieldLoss_subexponential
  loss_pos := fullBucketSequenceLoss_pos data.targetLoss data.fieldLoss
    data.targetLoss_pos data.fieldLoss_pos
  count_pos := data.finalCount_pos
  xSize_pos := data.xSize_pos
  ySize_pos := data.ySize_pos
  zSize_pos := data.zSize_pos
  stage := data.stage
  copy_growth := by
    intro r hr
    exact copy_growth_of_fullBucket_hashCount targetBase fieldBase
      data.targetLoss data.fieldLoss r (data.targetCount r) (data.fieldCard r)
      (data.finalCount r) data.fieldBase_pos
      (le_of_lt (data.targetLoss_pos r hr))
      (le_of_lt (data.fieldLoss_pos r hr))
      (data.target_growth r hr) (data.field_growth r hr)
      (data.fullBucket_hash_count r hr)
  volume_growth := data.volume_growth

/-- Direct standard laser-volume sequence adapter. -/
noncomputable def toSubexponentialLaserVolumeSequence
    {T : Tensor3 K Source} {stride : ℕ}
    {targetBase fieldBase volumeBase : ℝ}
    (data : FullBucketWholeConstituentSequenceData K T stride
      targetBase fieldBase volumeBase) :
    SubexponentialLaserVolumeSequence K T stride
      (targetBase / fieldBase) volumeBase :=
  data.toWholeConstituentLaserVolumeSequenceData.toSubexponentialLaserVolumeSequence

end FullBucketWholeConstituentSequenceData

end Sequence

end AlgebraicComplexity
