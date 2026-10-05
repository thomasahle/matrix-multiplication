import AlgebraicComplexity.MatrixMultiplication.LaserVolume

/-!
# Whole-constituent laser-volume assembly

Some compatibility cleanups zero complete partition variables and therefore leave every retained
constituent intact.  In that situation no damaged-copy model or hole-repair budget is needed:
one finite restriction to an indexed direct sum, followed by a cardinality reindexing, is already
the exact extraction consumed by the volume form of the asymptotic sum inequality.

This file packages that shorter path.  It is independent of Coppersmith--Winograd tensors and of
any particular certificate representation.
-/

namespace AlgebraicComplexity

open Tensor

universe u v z

section FiniteStage

variable (K : Type u) [CommSemiring K]
variable {Source : Leg → Type v}
variable [∀ c, AddCommMonoid (Source c)] [∀ c, Module K (Source c)]

/-- One finite extraction whose retained constituents are already whole and have common
rectangular dimensions.  The natural output index may be structured; `card_I` is the exact
bridge to the scalar copy count used by the asymptotic interface. -/
structure WholeConstituentLaserVolumeStage
    (source : Tensor3 K Source) (copies xSize ySize zSize : ℕ) where
  I : Type z
  [fintypeI : Fintype I]
  card_I : Fintype.card I = copies
  source_restricts : Restricts source
    (matrixMultiplicationDirectSum (ι := I) K
      (fun _ ↦ xSize) (fun _ ↦ ySize) (fun _ ↦ zSize))

namespace WholeConstituentLaserVolumeStage

/-- A whole-constituent finite stage is a polynomial degeneration to exactly `copies` equal
matrix-multiplication tensors. -/
theorem polynomialDegenerates
    {source : Tensor3 K Source} {copies xSize ySize zSize : ℕ}
    (stage : WholeConstituentLaserVolumeStage K source copies xSize ySize zSize) :
    PolynomialDegenerates source
      (matrixMultiplicationDirectSum (ι := Fin copies) K
        (fun _ ↦ xSize) (fun _ ↦ ySize) (fun _ ↦ zSize)) := by
  letI := stage.fintypeI
  let leaf := matrixMultiplication (K := K) xSize ySize zSize
  let e : stage.I ≃ Fin copies := Fintype.equivFinOfCardEq stage.card_I
  have hreindex : Restricts
      (Tensor.indexedDirectSum (fun _ : stage.I ↦ leaf))
      (Tensor.indexedDirectSum (fun _ : Fin copies ↦ leaf)) :=
    Tensor.Restricts.indexedDirectSum_const_equiv (K := K) e leaf
  exact PolynomialDegenerates.of_restricts (stage.source_restricts.trans (by
    simpa only [matrixMultiplicationDirectSum, leaf] using hreindex))

end WholeConstituentLaserVolumeStage

end FiniteStage

section Sequence

variable (K : Type u) [CommSemiring K]
variable {Source : Leg → Type v}
variable [∀ c, AddCommMonoid (Source c)] [∀ c, Module K (Source c)]

/-- Candidate-independent proportional sequence for a cleanup that retains whole constituents.

All finite tensor semantics live in `stage`; all asymptotic estimates are the explicit one-sided
growth fields.  In particular, a client may combine every method-of-types and hashing overhead
inside any convenient positive subexponential `loss`. -/
structure WholeConstituentLaserVolumeSequenceData
    (T : Tensor3 K Source) (stride : ℕ) (copyBase volumeBase : ℝ) where
  stride_pos : 0 < stride
  copyBase_pos : 0 < copyBase
  volumeBase_pos : 0 < volumeBase
  loss : ℕ → ℝ
  count : ℕ → ℕ
  xSize : ℕ → ℕ
  ySize : ℕ → ℕ
  zSize : ℕ → ℕ
  loss_subexponential : Growth.Subexponential loss
  loss_pos : ∀ r, 0 < r → 0 < loss r
  count_pos : ∀ r, 0 < r → 0 < count r
  xSize_pos : ∀ r, 0 < r → 0 < xSize r
  ySize_pos : ∀ r, 0 < r → 0 < ySize r
  zSize_pos : ∀ r, 0 < r → 0 < zSize r
  stage : ∀ r, 0 < r →
    WholeConstituentLaserVolumeStage K (Tensor.power T (stride * r))
      (count r) (xSize r) (ySize r) (zSize r)
  copy_growth : ∀ r, 0 < r →
    copyBase ^ r ≤ loss r * (count r : ℝ)
  volume_growth : ∀ r, 0 < r →
    volumeBase ^ r ≤ (((xSize r * ySize r * zSize r : ℕ) : ℝ))

namespace WholeConstituentLaserVolumeSequenceData

/-- Whole-constituent stages plus directed growth estimates form the standard
`SubexponentialLaserVolumeSequence`. -/
noncomputable def toSubexponentialLaserVolumeSequence
    {T : Tensor3 K Source} {stride : ℕ} {copyBase volumeBase : ℝ}
    (data : WholeConstituentLaserVolumeSequenceData K T stride copyBase volumeBase) :
    SubexponentialLaserVolumeSequence K T stride copyBase volumeBase where
  stride_pos := data.stride_pos
  copyBase_pos := data.copyBase_pos
  volumeBase_pos := data.volumeBase_pos
  loss := data.loss
  count := data.count
  xSize := data.xSize
  ySize := data.ySize
  zSize := data.zSize
  loss_subexponential := data.loss_subexponential
  loss_pos := data.loss_pos
  count_pos := data.count_pos
  xSize_pos := data.xSize_pos
  ySize_pos := data.ySize_pos
  zSize_pos := data.zSize_pos
  extract := fun r hr ↦ (data.stage r hr).polynomialDegenerates
  copy_growth := data.copy_growth
  volume_growth := data.volume_growth

end WholeConstituentLaserVolumeSequenceData

end Sequence

end AlgebraicComplexity
