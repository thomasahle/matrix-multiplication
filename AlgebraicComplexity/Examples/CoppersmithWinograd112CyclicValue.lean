import AlgebraicComplexity.Examples.CoppersmithWinograd112Asymptotic
import AlgebraicComplexity.MatrixMultiplication.CyclicLaserVolume

/-!
# Direct-sum cyclic extraction rate of the CW `112` constituent

This module packages the finite proportional extraction from
`CoppersmithWinograd112Asymptotic` as a reusable cyclic laser sequence.  It contains no hashing,
C-tensor, or prime-field arguments: those have already been reduced to an exact degeneration,
an exponential copy base, and a proved subexponential loss.

The endpoint `cw112_hasCyclicLaserExtractionRate` is an unconditional semantic lower bound, but it
is not yet the full Coppersmith--Winograd `112` value lemma.  Flattening the shared-Z groups after
cyclic symmetrization yields the copy base `side² / Z`.  The historical proof first uses
superadditivity across the Z-indexed C-tensor family and thereby obtains `side² * Z`; that stronger
aggregation theorem remains a separate obligation.  Subsequent lemmas simplify the proved direct-
sum rate to its `μ`-entropy formula.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor

universe u

/-- The declared volume base is exactly the volume of the square extracted at repetition `k`. -/
theorem cw112CyclicVolumeBase_pow_eq_volume (q L G k : ℕ) :
    cw112CyclicVolumeBase q L G ^ k =
      (((cw112AsymptoticSquareSide q L G k *
          cw112AsymptoticSquareSide q L G k *
          cw112AsymptoticSquareSide q L G k : ℕ) : ℝ)) := by
  unfold cw112CyclicVolumeBase cw112AsymptoticSquareSide
  norm_num only [Nat.cast_mul, Nat.cast_pow]
  rw [← pow_mul, ← pow_add, ← pow_add]
  congr 1
  ring

section

variable (K : Type u) [CommRing K]

/-- Complete cyclic finite extraction sequence for a positive rational CW `112` profile. -/
noncomputable def cw112CyclicExtractionSequence
    (q L G : ℕ) (hq : 0 < q) (hL : 0 < L) (hG : 0 < G) :
    SubexponentialCyclicLaserVolumeSequence K
      (cw112PartitionedTensor K q).realize
      (cw112CyclicStride L G)
      (cw112CyclicCopyBase L G)
      (cw112CyclicVolumeBase q L G) where
  stride_pos := by simp only [cw112CyclicStride]; positivity
  copyBase_pos := (cw112CyclicBases_pos hq).1
  volumeBase_pos := (cw112CyclicBases_pos hq).2
  loss := cw112CyclicLoss L G
  count := cw112AsymptoticCopies K q L G hL
  xSize := cw112AsymptoticSquareSide q L G
  ySize := cw112AsymptoticSquareSide q L G
  zSize := cw112AsymptoticSquareSide q L G
  loss_subexponential := cw112CyclicLoss_subexponential L G
  loss_pos := fun _k hk ↦ cw112CyclicLoss_pos hL hG hk
  count_pos := fun _k hk ↦ cw112AsymptoticCopies_pos K q L G hL hk
  xSize_pos := fun _k _hk ↦ by
    unfold cw112AsymptoticSquareSide
    exact pow_pos hq _
  ySize_pos := fun _k _hk ↦ by
    unfold cw112AsymptoticSquareSide
    exact pow_pos hq _
  zSize_pos := fun _k _hk ↦ by
    unfold cw112AsymptoticSquareSide
    exact pow_pos hq _
  extract := fun _k hk ↦ cw112Asymptotic_degenerates K hL hk
  copy_growth := fun _k hk ↦
    cw112CyclicCopyBase_pow_le_loss_mul_copies K hL hG hk
  volume_growth := fun k _hk ↦ (cw112CyclicVolumeBase_pow_eq_volume q L G k).le

/-- The exceptional `112` constituent achieves the direct-sum cyclic rate supplied by its exact
method-of-types copy and volume bases.

This theorem is unconditional: its proof contains the finite leaf restriction, simultaneous
shared-Z grouping, generic C-tensor degeneration, hashing count, Behrend loss, and proportional
limit.  It deliberately claims only the rate with copy base `side² / Z`; the stronger paper value
requires superadditive aggregation of the shared-Z C-tensors before cyclic symmetrization. -/
theorem cw112_hasCyclicLaserExtractionRate
    (q L G : ℕ) (hq : 0 < q) (hL : 0 < L) (hG : 0 < G) :
    HasCyclicLaserExtractionRate K (cw112PartitionedTensor K q).realize
      ((Real.log (cw112CyclicCopyBase L G) +
          (omega K / 3) * Real.log (cw112CyclicVolumeBase q L G)) /
        (3 * cw112CyclicStride L G)) :=
  (cw112CyclicExtractionSequence K q L G hq hL hG).hasCyclicLaserExtractionRate

end

end AlgebraicComplexity.Examples
