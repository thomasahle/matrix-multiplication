import AlgebraicComplexity.MatrixMultiplication.WholeConstituentLaserVolume
import AlgebraicComplexity.Tensor.IndexedProduct
import AlgebraicComplexity.Tensor.PowerCoherence

/-!
# Product assembly for whole-constituent laser-volume stages

Independent constituent extractions tensor by taking the Cartesian product of their output
indices.  When both stages retain whole, equal matrix-multiplication tensors, their external
product is again a whole-constituent stage: copy counts multiply and each of the three matrix
dimensions multiplies.

This is the finite, lossless composition rule needed to assemble recursive regional and leaf
extractions.  All hashing and type-counting losses remain confined to the input stages.
-/

namespace AlgebraicComplexity

open Tensor

universe u v w

namespace WholeConstituentLaserVolumeStage

variable (K : Type u) [CommSemiring K]
variable {V : Leg → Type v} [∀ c, AddCommMonoid (V c)] [∀ c, Module K (V c)]
variable {W : Leg → Type w} [∀ c, AddCommMonoid (W c)] [∀ c, Module K (W c)]

/-- Precompose a whole-constituent stage with an exact restriction.  This transports finite
extractions through support selection, power coherence, and recursive interface division without
changing their copy count or rectangular dimensions. -/
noncomputable def precompose
    {source : Tensor3 K V} {newSource : Tensor3 K W}
    {copies xSize ySize zSize : ℕ}
    (hsource : Restricts newSource source)
    (stage : WholeConstituentLaserVolumeStage K source copies xSize ySize zSize) :
    WholeConstituentLaserVolumeStage K newSource copies xSize ySize zSize where
  I := stage.I
  fintypeI := stage.fintypeI
  card_I := stage.card_I
  source_restricts := hsource.trans stage.source_restricts

/-- The external product of two whole-constituent stages is indexed by the Cartesian product of
their output families.  Copy counts and all three rectangular dimensions multiply exactly. -/
noncomputable def external
    {leftSource : Tensor3 K V} {leftCopies leftX leftY leftZ : ℕ}
    {rightSource : Tensor3 K W} {rightCopies rightX rightY rightZ : ℕ}
    (left : WholeConstituentLaserVolumeStage K leftSource
      leftCopies leftX leftY leftZ)
    (right : WholeConstituentLaserVolumeStage K rightSource
      rightCopies rightX rightY rightZ) :
    WholeConstituentLaserVolumeStage K (Tensor.external leftSource rightSource)
      (leftCopies * rightCopies) (leftX * rightX) (leftY * rightY) (leftZ * rightZ) := by
  letI := left.fintypeI
  letI := right.fintypeI
  let leftLeaf := matrixMultiplication (K := K) leftX leftY leftZ
  let rightLeaf := matrixMultiplication (K := K) rightX rightY rightZ
  let productLeaf := matrixMultiplication (K := K)
    (leftX * rightX) (leftY * rightY) (leftZ * rightZ)
  refine
    { I := left.I × right.I
      card_I := ?_
      source_restricts := ?_ }
  · rw [Fintype.card_prod, left.card_I, right.card_I]
  · have hproduct : Restricts
        (Tensor.external
          (Tensor.indexedDirectSum (fun _i : left.I ↦ leftLeaf))
          (Tensor.indexedDirectSum (fun _j : right.I ↦ rightLeaf)))
        (Tensor.indexedDirectSum (fun _q : left.I × right.I ↦ productLeaf)) :=
      (Tensor.Isomorphic.external_indexedDirectSum
          (fun _i : left.I ↦ leftLeaf) (fun _j : right.I ↦ rightLeaf)).restricts.trans
        (Tensor.Restricts.indexedDirectSum fun _q ↦
          (Tensor.Isomorphic.matrixMultiplication_external
            (K := K) leftX leftY leftZ rightX rightY rightZ).restricts)
    have hsource : Restricts
        (Tensor.external leftSource rightSource)
        (Tensor.external
          (Tensor.indexedDirectSum (fun _i : left.I ↦ leftLeaf))
          (Tensor.indexedDirectSum (fun _j : right.I ↦ rightLeaf))) := by
      simpa only [matrixMultiplicationDirectSum, leftLeaf, rightLeaf] using
        left.source_restricts.external right.source_restricts
    simpa only [matrixMultiplicationDirectSum, productLeaf] using hsource.trans hproduct

/-- Two stages extracted from powers of one source tensor assemble into the summed source power.
This is `external` followed by the canonical coherence isomorphism
`T^a ⊐ T^b ≅ T^(a+b)`. -/
noncomputable def powerAdd
    {T : Tensor3 K V} {leftExponent rightExponent : ℕ}
    {leftCopies leftX leftY leftZ : ℕ}
    {rightCopies rightX rightY rightZ : ℕ}
    (left : WholeConstituentLaserVolumeStage K (Tensor.power T leftExponent)
      leftCopies leftX leftY leftZ)
    (right : WholeConstituentLaserVolumeStage K (Tensor.power T rightExponent)
      rightCopies rightX rightY rightZ) :
    WholeConstituentLaserVolumeStage K (Tensor.power T (leftExponent + rightExponent))
      (leftCopies * rightCopies) (leftX * rightX) (leftY * rightY) (leftZ * rightZ) := by
  let combined := WholeConstituentLaserVolumeStage.external (K := K) left right
  exact WholeConstituentLaserVolumeStage.precompose (K := K)
    (Tensor.isomorphic_external_power T leftExponent rightExponent).symm.restricts combined

end WholeConstituentLaserVolumeStage

end AlgebraicComplexity
