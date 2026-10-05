import AlgebraicComplexity.MatrixMultiplication.NestedLaserVolume
import AlgebraicComplexity.MatrixMultiplication.OuterConstituentStageCore

/-!
# Composition of outer constituent extraction with uniform inner extraction

Recursive laser arguments first isolate an indexed direct sum of whole outer constituents and
then run the same-size matrix-multiplication extraction inside every survivor.  This file keeps
those two certificates separate until the final composition.  In particular, an outer survivor
count and an inner type-class count are multiplied only after an actual inner degeneration has
been supplied for every outer constituent.

The outer stage carries no matrix dimensions.  The inner extraction targets the final rectangular
matrix-multiplication tensor, whose dimensions already include every leaf product.  Accordingly,
only the outer and inner copy counts, exponential bases, and subexponential losses multiply; the
sequence exposes one final rectangular-volume base and does not double-count it.
-/

namespace AlgebraicComplexity

open Tensor

universe u v w x y

section FiniteStage

variable (K : Type u) [CommSemiring K]
variable {Source : Leg → Type v}
variable [∀ c, AddCommMonoid (Source c)] [∀ c, Module K (Source c)]

namespace OuterConstituentStage

/-- Uniform-size inner extraction property over every outer constituent.

The inner copy index has already been normalized to `Fin innerCopies`.  The companion constructor
`hasUniformInnerExtraction_ofDependentFamilies` accepts the naturally dependent finite index
types produced by localized hashing. -/
def HasUniformInnerExtraction
    {source : Tensor3 K Source} {outerCopies : ℕ}
    (outer : OuterConstituentStage.{u, v, w, x} K source outerCopies)
    (innerCopies xSize ySize zSize : ℕ) : Prop := by
  letI := outer.addCommMonoidW
  letI := outer.moduleW
  exact ∀ i, PolynomialDegenerates (outer.constituent i)
    (matrixMultiplicationDirectSum (ι := Fin innerCopies) K
      (fun _ ↦ xSize) (fun _ ↦ ySize) (fun _ ↦ zSize))

/-- Naturally indexed version of `HasUniformInnerExtraction`. -/
def HasDependentInnerExtraction
    {source : Tensor3 K Source} {outerCopies : ℕ}
    (outer : OuterConstituentStage.{u, v, w, x} K source outerCopies)
    (J : outer.I → Type y) [∀ i, Fintype (J i)]
    (xSize ySize zSize : ℕ) : Prop := by
  letI := outer.addCommMonoidW
  letI := outer.moduleW
  exact ∀ i, PolynomialDegenerates (outer.constituent i)
    (Tensor.indexedDirectSum (fun _j : J i ↦
      matrixMultiplication (K := K) xSize ySize zSize))

/-- Every outer constituent is tensor-isomorphic to one reference tensor.

The reference may have a different ambient leg-space type.  This is the reusable transport
boundary used when sample-position permutations identify all survivors of one exact type. -/
def IsomorphicToReference
    {source : Tensor3 K Source} {outerCopies : ℕ}
    (outer : OuterConstituentStage.{u, v, w, x} K source outerCopies)
    {ReferenceSpace : Leg → Type y}
    [∀ c, AddCommMonoid (ReferenceSpace c)] [∀ c, Module K (ReferenceSpace c)]
    (reference : Tensor3 K ReferenceSpace) : Prop := by
  letI := outer.addCommMonoidW
  letI := outer.moduleW
  exact ∀ i, Isomorphic (outer.constituent i) reference

/-- Reindex naturally dependent inner families to one common scalar copy count.

This is useful when each outer constituent has a different subtype of selected addresses, but all
those subtypes have the same certified cardinality. -/
theorem hasUniformInnerExtraction_ofDependentFamilies
    {source : Tensor3 K Source} {outerCopies innerCopies xSize ySize zSize : ℕ}
    (outer : OuterConstituentStage.{u, v, w, x} K source outerCopies)
    {J : outer.I → Type y} [∀ i, Fintype (J i)]
    (hcard : ∀ i, Fintype.card (J i) = innerCopies)
    (hinner : HasDependentInnerExtraction K outer J xSize ySize zSize) :
    HasUniformInnerExtraction K outer innerCopies xSize ySize zSize := by
  letI := outer.addCommMonoidW
  letI := outer.moduleW
  intro i
  let Q := matrixMultiplication (K := K) xSize ySize zSize
  let e : J i ≃ Fin innerCopies := Fintype.equivFinOfCardEq (hcard i)
  have hreindex : Restricts
      (Tensor.indexedDirectSum (fun _j : J i ↦ Q))
      (Tensor.indexedDirectSum (fun _k : Fin innerCopies ↦ Q)) :=
    Tensor.Restricts.indexedDirectSum_const_equiv (K := K) e Q
  exact (hinner i).trans (Tensor.PolynomialDegenerates.of_restricts (by
    simpa only [matrixMultiplicationDirectSum, Q] using hreindex))

/-- Transport one naturally indexed inner extraction on a reference tensor to every isomorphic
outer constituent, preserving the entire inner indexed family and its exact cardinality. -/
theorem hasUniformInnerExtraction_of_isomorphicReference
    {source : Tensor3 K Source} {outerCopies innerCopies xSize ySize zSize : ℕ}
    (outer : OuterConstituentStage.{u, v, w, x} K source outerCopies)
    {ReferenceSpace : Leg → Type y}
    [∀ c, AddCommMonoid (ReferenceSpace c)] [∀ c, Module K (ReferenceSpace c)]
    (reference : Tensor3 K ReferenceSpace)
    (hisomorphic : IsomorphicToReference K outer reference)
    {J : Type*} [Fintype J]
    (hcard : Fintype.card J = innerCopies)
    (hreference : PolynomialDegenerates reference
      (Tensor.indexedDirectSum (fun _j : J ↦
        matrixMultiplication (K := K) xSize ySize zSize))) :
    HasUniformInnerExtraction K outer innerCopies xSize ySize zSize := by
  apply hasUniformInnerExtraction_ofDependentFamilies K outer
    (J := fun _i ↦ J) (fun _i ↦ hcard)
  letI := outer.addCommMonoidW
  letI := outer.moduleW
  intro i
  exact (Tensor.PolynomialDegenerates.of_restricts
    (hisomorphic i).restricts).trans hreference

/-- Compose a whole outer direct sum with a genuine inner extraction on every survivor. -/
noncomputable def nest
    {source : Tensor3 K Source} {outerCopies innerCopies xSize ySize zSize : ℕ}
    (outer : OuterConstituentStage.{u, v, w, x} K source outerCopies)
    (inner : HasUniformInnerExtraction K outer innerCopies xSize ySize zSize) :
    NestedLaserVolumeStage K source
      outerCopies innerCopies xSize ySize zSize := by
  letI := outer.addCommMonoidW
  letI := outer.moduleW
  exact
    { I := outer.I
      fintypeI := outer.fintypeI
      card_I := outer.card_I
      W := outer.W
      addCommMonoidW := outer.addCommMonoidW
      moduleW := outer.moduleW
      constituent := outer.constituent
      outer_restricts := outer.source_restricts
      inner_degenerates := inner }

/-- Direct dependent-index constructor for the composed finite stage. -/
noncomputable def nestDependentFamilies
    {source : Tensor3 K Source} {outerCopies innerCopies xSize ySize zSize : ℕ}
    (outer : OuterConstituentStage.{u, v, w, x} K source outerCopies)
    {J : outer.I → Type y} [∀ i, Fintype (J i)]
    (hcard : ∀ i, Fintype.card (J i) = innerCopies)
    (hinner : HasDependentInnerExtraction K outer J xSize ySize zSize) :
    NestedLaserVolumeStage K source
      outerCopies innerCopies xSize ySize zSize :=
  OuterConstituentStage.nest (K := K) outer
    (hasUniformInnerExtraction_ofDependentFamilies K outer hcard hinner)

/-- Flatten the genuinely nested outer/inner extraction to exactly
`outerCopies * innerCopies` equal rectangular matrix-multiplication tensors. -/
theorem polynomialDegenerates_nested
    {source : Tensor3 K Source} {outerCopies innerCopies xSize ySize zSize : ℕ}
    (outer : OuterConstituentStage.{u, v, w, x} K source outerCopies)
    (inner : HasUniformInnerExtraction K outer innerCopies xSize ySize zSize) :
    PolynomialDegenerates source
      (matrixMultiplicationDirectSum (ι := Fin (outerCopies * innerCopies)) K
        (fun _ ↦ xSize) (fun _ ↦ ySize) (fun _ ↦ zSize)) :=
  (OuterConstituentStage.nest (K := K) outer inner).polynomialDegenerates

end OuterConstituentStage

end FiniteStage

section Sequence

variable (K : Type u) [CommSemiring K]
variable {Source : Leg → Type v}
variable [∀ c, AddCommMonoid (Source c)] [∀ c, Module K (Source c)]

namespace NestedLaserVolumeSequenceData

/-- Base-two normalization of nested copy rates.

The generic nested adapter naturally returns the product of the outer and inner copy bases.
When both bases are written as powers of two with the same stride, this theorem rewrites that
product to the sum of retained exponents expected by the endpoint interface. -/
noncomputable def toSubexponentialLaserVolumeSequence_addRetained
    {T : Tensor3 K Source} {stride : ℕ}
    {outerRetained innerRetained volumeBase : ℝ}
    (data : NestedLaserVolumeSequenceData K T stride
      ((2 : ℝ) ^ ((stride : ℝ) * outerRetained))
      ((2 : ℝ) ^ ((stride : ℝ) * innerRetained)) volumeBase) :
    SubexponentialLaserVolumeSequence K T stride
      ((2 : ℝ) ^ ((stride : ℝ) * (outerRetained + innerRetained))) volumeBase := by
  have hbase :
      (2 : ℝ) ^ ((stride : ℝ) * outerRetained) *
          (2 : ℝ) ^ ((stride : ℝ) * innerRetained) =
        (2 : ℝ) ^ ((stride : ℝ) * (outerRetained + innerRetained)) := by
    rw [mul_add, Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
  rw [← hbase]
  exact data.toSubexponentialLaserVolumeSequence

end NestedLaserVolumeSequenceData

/-- An asymptotic sequence of outer whole-constituent direct sums.

This structure deliberately stops before assigning any matrix dimensions.  Its count base and
loss describe only the quotient/hash survivors.  A uniform copywise inner extraction is required
by `toNestedLaserVolumeSequenceData` before the data can enter the matrix-multiplication endpoint. -/
structure OuterConstituentSequenceData
    (T : Tensor3 K Source) (stride : ℕ) (outerBase : ℝ) where
  stride_pos : 0 < stride
  outerBase_pos : 0 < outerBase
  loss : ℕ → ℝ
  count : ℕ → ℕ
  loss_subexponential : Growth.Subexponential loss
  loss_pos : ∀ r, 0 < r → 0 < loss r
  count_pos : ∀ r, 0 < r → 0 < count r
  stage : ∀ r, 0 < r →
    OuterConstituentStage.{u, max u v, w, x} K
      (Tensor.power T (stride * r)) (count r)
  copy_growth : ∀ r, 0 < r →
    outerBase ^ r ≤ loss r * (count r : ℝ)

namespace OuterConstituentSequenceData

/-- Add a uniform inner extraction sequence to an outer whole-constituent sequence.

The output keeps the two copy growth bounds separate.  This makes the later multiplication in
`NestedLaserVolumeSequenceData.toSubexponentialLaserVolumeSequence` auditable and prevents a
representative inner leaf from being mistaken for an entire inner type class. -/
noncomputable def toNestedLaserVolumeSequenceData
    {T : Tensor3 K Source} {stride : ℕ} {outerBase innerBase volumeBase : ℝ}
    (outer : OuterConstituentSequenceData.{u, v, w, x} K T stride outerBase)
    (innerBase_pos : 0 < innerBase) (volumeBase_pos : 0 < volumeBase)
    (innerLoss : ℕ → ℝ) (innerCount xSize ySize zSize : ℕ → ℕ)
    (innerLoss_subexponential : Growth.Subexponential innerLoss)
    (innerLoss_pos : ∀ r, 0 < r → 0 < innerLoss r)
    (innerCount_pos : ∀ r, 0 < r → 0 < innerCount r)
    (xSize_pos : ∀ r, 0 < r → 0 < xSize r)
    (ySize_pos : ∀ r, 0 < r → 0 < ySize r)
    (zSize_pos : ∀ r, 0 < r → 0 < zSize r)
    (inner : ∀ r (hr : 0 < r),
      OuterConstituentStage.HasUniformInnerExtraction K (outer.stage r hr)
        (innerCount r) (xSize r) (ySize r) (zSize r))
    (inner_copy_growth : ∀ r, 0 < r →
      innerBase ^ r ≤ innerLoss r * (innerCount r : ℝ))
    (volume_growth : ∀ r, 0 < r →
      volumeBase ^ r ≤ (((xSize r * ySize r * zSize r : ℕ) : ℝ))) :
    NestedLaserVolumeSequenceData K T stride
      outerBase innerBase volumeBase where
  stride_pos := outer.stride_pos
  outerBase_pos := outer.outerBase_pos
  innerBase_pos := innerBase_pos
  volumeBase_pos := volumeBase_pos
  outerLoss := outer.loss
  innerLoss := innerLoss
  outerCount := outer.count
  innerCount := innerCount
  xSize := xSize
  ySize := ySize
  zSize := zSize
  outerLoss_subexponential := outer.loss_subexponential
  innerLoss_subexponential := innerLoss_subexponential
  outerLoss_pos := outer.loss_pos
  innerLoss_pos := innerLoss_pos
  outerCount_pos := outer.count_pos
  innerCount_pos := innerCount_pos
  xSize_pos := xSize_pos
  ySize_pos := ySize_pos
  zSize_pos := zSize_pos
  stage := fun r hr ↦ OuterConstituentStage.nest (K := K)
    (outer.stage r hr) (inner r hr)
  outer_copy_growth := outer.copy_growth
  inner_copy_growth := inner_copy_growth
  volume_growth := volume_growth

/-- Direct endpoint adapter: outer and inner copy bases multiply, while the inner extraction's
final rectangular-volume base is retained exactly once. -/
noncomputable def toSubexponentialLaserVolumeSequence
    {T : Tensor3 K Source} {stride : ℕ} {outerBase innerBase volumeBase : ℝ}
    (outer : OuterConstituentSequenceData.{u, v, w, x} K T stride outerBase)
    (innerBase_pos : 0 < innerBase) (volumeBase_pos : 0 < volumeBase)
    (innerLoss : ℕ → ℝ) (innerCount xSize ySize zSize : ℕ → ℕ)
    (innerLoss_subexponential : Growth.Subexponential innerLoss)
    (innerLoss_pos : ∀ r, 0 < r → 0 < innerLoss r)
    (innerCount_pos : ∀ r, 0 < r → 0 < innerCount r)
    (xSize_pos : ∀ r, 0 < r → 0 < xSize r)
    (ySize_pos : ∀ r, 0 < r → 0 < ySize r)
    (zSize_pos : ∀ r, 0 < r → 0 < zSize r)
    (inner : ∀ r (hr : 0 < r),
      OuterConstituentStage.HasUniformInnerExtraction K (outer.stage r hr)
        (innerCount r) (xSize r) (ySize r) (zSize r))
    (inner_copy_growth : ∀ r, 0 < r →
      innerBase ^ r ≤ innerLoss r * (innerCount r : ℝ))
    (volume_growth : ∀ r, 0 < r →
      volumeBase ^ r ≤ (((xSize r * ySize r * zSize r : ℕ) : ℝ))) :
    SubexponentialLaserVolumeSequence K T stride
      (outerBase * innerBase) volumeBase :=
  (OuterConstituentSequenceData.toNestedLaserVolumeSequenceData (K := K) outer
    innerBase_pos volumeBase_pos
    innerLoss innerCount xSize ySize zSize innerLoss_subexponential
    innerLoss_pos innerCount_pos xSize_pos ySize_pos zSize_pos inner
    inner_copy_growth volume_growth).toSubexponentialLaserVolumeSequence

/-- Base-two endpoint form of `toSubexponentialLaserVolumeSequence`.

This constructor exposes the final copy base directly as the sum of the outer quotient/hash rate
and the inner typed-leaf rate. -/
noncomputable def toSubexponentialLaserVolumeSequence_addRetained
    {T : Tensor3 K Source} {stride : ℕ}
    {outerRetained innerRetained volumeBase : ℝ}
    (outer : OuterConstituentSequenceData.{u, v, w, x} K T stride
      ((2 : ℝ) ^ ((stride : ℝ) * outerRetained)))
    (volumeBase_pos : 0 < volumeBase)
    (innerLoss : ℕ → ℝ) (innerCount xSize ySize zSize : ℕ → ℕ)
    (innerLoss_subexponential : Growth.Subexponential innerLoss)
    (innerLoss_pos : ∀ r, 0 < r → 0 < innerLoss r)
    (innerCount_pos : ∀ r, 0 < r → 0 < innerCount r)
    (xSize_pos : ∀ r, 0 < r → 0 < xSize r)
    (ySize_pos : ∀ r, 0 < r → 0 < ySize r)
    (zSize_pos : ∀ r, 0 < r → 0 < zSize r)
    (inner : ∀ r (hr : 0 < r),
      OuterConstituentStage.HasUniformInnerExtraction K (outer.stage r hr)
        (innerCount r) (xSize r) (ySize r) (zSize r))
    (inner_copy_growth : ∀ r, 0 < r →
      ((2 : ℝ) ^ ((stride : ℝ) * innerRetained)) ^ r ≤
        innerLoss r * (innerCount r : ℝ))
    (volume_growth : ∀ r, 0 < r →
      volumeBase ^ r ≤ (((xSize r * ySize r * zSize r : ℕ) : ℝ))) :
    SubexponentialLaserVolumeSequence K T stride
      ((2 : ℝ) ^ ((stride : ℝ) * (outerRetained + innerRetained))) volumeBase :=
  (OuterConstituentSequenceData.toNestedLaserVolumeSequenceData (K := K) outer
    (by positivity) volumeBase_pos innerLoss innerCount xSize ySize zSize
    innerLoss_subexponential innerLoss_pos innerCount_pos xSize_pos ySize_pos zSize_pos
    inner inner_copy_growth volume_growth).toSubexponentialLaserVolumeSequence_addRetained

end OuterConstituentSequenceData

end Sequence

end AlgebraicComplexity
