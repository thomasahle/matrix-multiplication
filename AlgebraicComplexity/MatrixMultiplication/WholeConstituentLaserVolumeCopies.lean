import AlgebraicComplexity.MatrixMultiplication.WholeConstituentLaserVolume

/-!
# Whole-constituent stages from indexed copies

This file records the small semantic adapter used after a cleanup or repair theorem has produced
an indexed direct sum of identical intact tensors.  If one intact tensor restricts to a fixed
matrix-multiplication tensor, then the whole indexed family is already a
`WholeConstituentLaserVolumeStage`.

The statement is independent of Coppersmith--Winograd tensors and of any counting argument.
-/

namespace AlgebraicComplexity

open Tensor

universe u v w

namespace WholeConstituentLaserVolumeStage

variable (K : Type u) [CommSemiring K]
variable {V : Leg → Type v} [∀ c, AddCommMonoid (V c)] [∀ c, Module K (V c)]
variable {W : Leg → Type w} [∀ c, AddCommMonoid (W c)] [∀ c, Module K (W c)]

/-- Package a restriction which already ends in a direct sum of equal rectangular
matrix-multiplication tensors. -/
noncomputable def ofMatrixMultiplicationDirectSum
    {source : Tensor3 K V} {I : Type} [Fintype I]
    {copies xSize ySize zSize : ℕ}
    (hcard : Fintype.card I = copies)
    (hsource : Restricts source
      (matrixMultiplicationDirectSum (ι := I) K
        (fun _ ↦ xSize) (fun _ ↦ ySize) (fun _ ↦ zSize))) :
    WholeConstituentLaserVolumeStage K source copies xSize ySize zSize where
  I := I
  card_I := hcard
  source_restricts := hsource

/-- Package a restriction to finitely many identical intact tensors as a whole-constituent
laser-volume stage.  The only tensor-specific input is the restriction of one intact copy to the
desired rectangular matrix-multiplication tensor. -/
noncomputable def ofIndexedCopies
    {source : Tensor3 K V} {box : Tensor3 K W}
    {I : Type} [Fintype I]
    {copies xSize ySize zSize : ℕ}
    (hcard : Fintype.card I = copies)
    (hsource : Restricts source (Tensor.indexedDirectSum (fun _ : I ↦ box)))
    (hbox : Restricts box (matrixMultiplication (K := K) xSize ySize zSize)) :
    WholeConstituentLaserVolumeStage K source copies xSize ySize zSize where
  I := I
  card_I := hcard
  source_restricts := hsource.trans (by
    simpa only [matrixMultiplicationDirectSum] using
      (Tensor.Restricts.indexedDirectSum (fun _ : I ↦ hbox)))

end WholeConstituentLaserVolumeStage

end AlgebraicComplexity
