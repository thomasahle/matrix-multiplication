import AlgebraicComplexity.MatrixMultiplication.WholeConstituentLaserVolume
import AlgebraicComplexity.Tensor.IndexedDegeneration

/-!
# Nested laser-volume extraction

Compatibility hashing often supplies an *outer* direct sum of retained constituents, while a
separate typed-leaf theorem extracts an *inner* direct sum of matrix-multiplication tensors from
each retained constituent.  The two copy counts live at different levels and must be multiplied;
one matrix-multiplication leaf from each outer constituent does not justify the inner exponent.

This file records that distinction in the type of the finite witness.  A
`NestedLaserVolumeStage` contains the actual inner polynomial degeneration for every outer
constituent.  Its main theorem flattens the dependent pair of outer and inner copy indices.  The
sequence adapter then multiplies independently proved outer and inner exponential bases and
subexponential losses.

The construction is tensor- and certificate-independent.  In particular, it does not infer an
inner type-class exponent from a representative leaf.
-/

namespace AlgebraicComplexity

open Tensor

universe u v w x y

section FiniteStage

variable (K : Type u) [CommSemiring K]
variable {Source : Leg → Type v}
variable [∀ c, AddCommMonoid (Source c)] [∀ c, Module K (Source c)]

/-- A two-level finite extraction witness.

`outer_restricts` is the hashing/cleanup output.  Crucially, `inner_degenerates` is a family of
actual degenerations to `innerCopies` matrix-multiplication tensors; supplying only one typed
leaf per outer constituent is not enough to construct this structure. -/
structure NestedLaserVolumeStage
    (source : Tensor3 K Source)
    (outerCopies innerCopies xSize ySize zSize : ℕ) where
  I : Type w
  [fintypeI : Fintype I]
  card_I : Fintype.card I = outerCopies
  W : I → Leg → Type x
  [addCommMonoidW : ∀ i c, AddCommMonoid (W i c)]
  [moduleW : ∀ i c, Module K (W i c)]
  constituent : ∀ i, Tensor3 K (W i)
  outer_restricts : Restricts source (Tensor.indexedDirectSum constituent)
  inner_degenerates : ∀ i, PolynomialDegenerates (constituent i)
    (matrixMultiplicationDirectSum (ι := Fin innerCopies) K
      (fun _ ↦ xSize) (fun _ ↦ ySize) (fun _ ↦ zSize))

namespace NestedLaserVolumeStage

/-- Construct a nested stage from naturally indexed inner families.

Concrete localized type classes are usually subtypes or finite fibers, not `Fin innerCopies`.
This constructor requires their exact cardinality and reindexes each constant inner direct sum
canonically.  It still requires a degeneration of the *whole* inner family for every outer
constituent; a representative member cannot discharge `inner_degenerates`. -/
noncomputable def ofDependentInnerFamilies
    {source : Tensor3 K Source}
    {outerCopies innerCopies xSize ySize zSize : ℕ}
    {I : Type w} [Fintype I]
    {J : I → Type y} [∀ i, Fintype (J i)]
    {W : I → Leg → Type x}
    [∀ i c, AddCommMonoid (W i c)] [∀ i c, Module K (W i c)]
    {constituent : ∀ i, Tensor3 K (W i)}
    (hcardI : Fintype.card I = outerCopies)
    (houter : Restricts source (Tensor.indexedDirectSum constituent))
    (hcardJ : ∀ i, Fintype.card (J i) = innerCopies)
    (hinner : ∀ i, PolynomialDegenerates (constituent i)
      (Tensor.indexedDirectSum (fun _j : J i ↦
        matrixMultiplication (K := K) xSize ySize zSize))) :
    NestedLaserVolumeStage K source
      outerCopies innerCopies xSize ySize zSize where
  I := I
  card_I := hcardI
  W := W
  constituent := constituent
  outer_restricts := houter
  inner_degenerates := fun i ↦ by
    let Q := matrixMultiplication (K := K) xSize ySize zSize
    let e : J i ≃ Fin innerCopies := Fintype.equivFinOfCardEq (hcardJ i)
    have hreindex : Restricts
        (Tensor.indexedDirectSum (fun _j : J i ↦ Q))
        (Tensor.indexedDirectSum (fun _k : Fin innerCopies ↦ Q)) :=
      Tensor.Restricts.indexedDirectSum_const_equiv (K := K) e Q
    exact (hinner i).trans (Tensor.PolynomialDegenerates.of_restricts (by
      simpa only [matrixMultiplicationDirectSum, Q] using hreindex))

/-- Flatten the outer survivor and inner extraction indices.

The output has exactly `outerCopies * innerCopies` summands.  This is the finite semantic
identity which prevents an outer type count and an inner type count from being conflated: the
inner factor appears only because every outer constituent carries the displayed
`inner_degenerates` certificate. -/
theorem polynomialDegenerates
    {source : Tensor3 K Source}
    {outerCopies innerCopies xSize ySize zSize : ℕ}
    (stage : NestedLaserVolumeStage K source
      outerCopies innerCopies xSize ySize zSize) :
    PolynomialDegenerates source
      (matrixMultiplicationDirectSum (ι := Fin (outerCopies * innerCopies)) K
        (fun _ ↦ xSize) (fun _ ↦ ySize) (fun _ ↦ zSize)) := by
  classical
  letI := stage.fintypeI
  letI := stage.addCommMonoidW
  letI := stage.moduleW
  let Q := matrixMultiplication (K := K) xSize ySize zSize
  let FlatIndex := Σ _i : stage.I, Fin innerCopies
  have hnested : PolynomialDegenerates
      (Tensor.indexedDirectSum stage.constituent)
      (Tensor.indexedDirectSum (fun _i : stage.I ↦
        Tensor.indexedDirectSum (fun _j : Fin innerCopies ↦ Q))) := by
    simpa only [matrixMultiplicationDirectSum, Q] using
      (Tensor.PolynomialDegenerates.indexedDirectSum stage.inner_degenerates)
  have hflatten : Restricts
      (Tensor.indexedDirectSum (fun _i : stage.I ↦
        Tensor.indexedDirectSum (fun _j : Fin innerCopies ↦ Q)))
      (Tensor.indexedDirectSum (fun _ij : FlatIndex ↦ Q)) := by
    exact (Tensor.Isomorphic.indexedDirectSum_sigma
      (K := K)
      (J := fun _i : stage.I ↦ Fin innerCopies)
      (S := fun _i _j ↦ MMSpace K xSize ySize zSize)
      (T := fun _ij : FlatIndex ↦ Q)).symm.restricts
  have hcard : Fintype.card FlatIndex = outerCopies * innerCopies := by
    dsimp only [FlatIndex]
    calc
      Fintype.card (Σ _i : stage.I, Fin innerCopies) =
          Fintype.card (stage.I × Fin innerCopies) :=
        Fintype.card_congr (Equiv.sigmaEquivProd stage.I (Fin innerCopies))
      _ = outerCopies * innerCopies := by
        rw [Fintype.card_prod, Fintype.card_fin, stage.card_I]
  let e : FlatIndex ≃ Fin (outerCopies * innerCopies) :=
    Fintype.equivFinOfCardEq hcard
  have hreindex : Restricts
      (Tensor.indexedDirectSum (fun _ij : FlatIndex ↦ Q))
      (Tensor.indexedDirectSum
        (fun _k : Fin (outerCopies * innerCopies) ↦ Q)) :=
    Tensor.Restricts.indexedDirectSum_const_equiv (K := K) e Q
  exact (Tensor.PolynomialDegenerates.of_restricts stage.outer_restricts).trans
    (hnested.trans (Tensor.PolynomialDegenerates.of_restricts
      (hflatten.trans (by
        simpa only [matrixMultiplicationDirectSum, Q] using hreindex))))

end NestedLaserVolumeStage

end FiniteStage

section Sequence

variable (K : Type u) [CommSemiring K]
variable {Source : Leg → Type v}
variable [∀ c, AddCommMonoid (Source c)] [∀ c, Module K (Source c)]

/-- Candidate-independent two-level extraction data.

The outer and inner counts have separate directed growth bounds.  Thus a client must prove the
inner fine-extraction exponent as an actual family of finite degenerations; it cannot obtain that
exponent merely by identifying one representative typed leaf. -/
structure NestedLaserVolumeSequenceData
    (T : Tensor3 K Source) (stride : ℕ)
    (outerBase innerBase volumeBase : ℝ) where
  stride_pos : 0 < stride
  outerBase_pos : 0 < outerBase
  innerBase_pos : 0 < innerBase
  volumeBase_pos : 0 < volumeBase
  outerLoss : ℕ → ℝ
  innerLoss : ℕ → ℝ
  outerCount : ℕ → ℕ
  innerCount : ℕ → ℕ
  xSize : ℕ → ℕ
  ySize : ℕ → ℕ
  zSize : ℕ → ℕ
  outerLoss_subexponential : Growth.Subexponential outerLoss
  innerLoss_subexponential : Growth.Subexponential innerLoss
  outerLoss_pos : ∀ r, 0 < r → 0 < outerLoss r
  innerLoss_pos : ∀ r, 0 < r → 0 < innerLoss r
  outerCount_pos : ∀ r, 0 < r → 0 < outerCount r
  innerCount_pos : ∀ r, 0 < r → 0 < innerCount r
  xSize_pos : ∀ r, 0 < r → 0 < xSize r
  ySize_pos : ∀ r, 0 < r → 0 < ySize r
  zSize_pos : ∀ r, 0 < r → 0 < zSize r
  stage : ∀ r, 0 < r →
    NestedLaserVolumeStage.{u, max u v, w, x} K (Tensor.power T (stride * r))
      (outerCount r) (innerCount r) (xSize r) (ySize r) (zSize r)
  outer_copy_growth : ∀ r, 0 < r →
    outerBase ^ r ≤ outerLoss r * (outerCount r : ℝ)
  inner_copy_growth : ∀ r, 0 < r →
    innerBase ^ r ≤ innerLoss r * (innerCount r : ℝ)
  volume_growth : ∀ r, 0 < r →
    volumeBase ^ r ≤ (((xSize r * ySize r * zSize r : ℕ) : ℝ))

namespace NestedLaserVolumeSequenceData

/-- Multiply the independently certified outer and inner count bases and losses.

The resulting copy base is `outerBase * innerBase`; the volume base is unchanged because the
inner stage already exposes the final rectangular dimensions. -/
noncomputable def toSubexponentialLaserVolumeSequence
    {T : Tensor3 K Source} {stride : ℕ}
    {outerBase innerBase volumeBase : ℝ}
    (data : NestedLaserVolumeSequenceData K T stride
      outerBase innerBase volumeBase) :
    SubexponentialLaserVolumeSequence K T stride
      (outerBase * innerBase) volumeBase where
  stride_pos := data.stride_pos
  copyBase_pos := mul_pos data.outerBase_pos data.innerBase_pos
  volumeBase_pos := data.volumeBase_pos
  loss := fun r ↦ data.outerLoss r * data.innerLoss r
  count := fun r ↦ data.outerCount r * data.innerCount r
  xSize := data.xSize
  ySize := data.ySize
  zSize := data.zSize
  loss_subexponential :=
    data.outerLoss_subexponential.mul data.innerLoss_subexponential
  loss_pos := fun r hr ↦ mul_pos (data.outerLoss_pos r hr) (data.innerLoss_pos r hr)
  count_pos := fun r hr ↦ Nat.mul_pos
    (data.outerCount_pos r hr) (data.innerCount_pos r hr)
  xSize_pos := data.xSize_pos
  ySize_pos := data.ySize_pos
  zSize_pos := data.zSize_pos
  extract := fun r hr ↦ (data.stage r hr).polynomialDegenerates
  copy_growth := by
    intro r hr
    rw [mul_pow]
    calc
      outerBase ^ r * innerBase ^ r ≤
          (data.outerLoss r * (data.outerCount r : ℝ)) *
            (data.innerLoss r * (data.innerCount r : ℝ)) :=
        mul_le_mul (data.outer_copy_growth r hr) (data.inner_copy_growth r hr)
          (pow_nonneg data.innerBase_pos.le r)
          (mul_nonneg (data.outerLoss_pos r hr).le (Nat.cast_nonneg _))
      _ = (data.outerLoss r * data.innerLoss r) *
          ((data.outerCount r * data.innerCount r : ℕ) : ℝ) := by
        push_cast
        ring
  volume_growth := data.volume_growth

end NestedLaserVolumeSequenceData

end Sequence

end AlgebraicComplexity
