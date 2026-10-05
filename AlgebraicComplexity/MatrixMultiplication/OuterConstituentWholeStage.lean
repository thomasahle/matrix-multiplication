/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.OuterConstituentStageCore
import AlgebraicComplexity.MatrixMultiplication.WholeConstituentLaserVolume
import AlgebraicComplexity.Tensor.IndexedProduct

/-!
# Exact inner refinement of an outer constituent stage

An `OuterConstituentStage` keeps every retained outer constituent intact.  If each such
constituent restricts to the same number of equal matrix-multiplication tensors, the outer and
inner indices may be flattened to one `WholeConstituentLaserVolumeStage` whose copy count is the
product of the two counts.

This is the exact-restriction counterpart of `NestedLaserVolumeStage.polynomialDegenerates`.
It is useful when a coarse cleanup retains whole constituents and a later typed extraction inside
each constituent is itself an exact restriction.  No restriction of the assembled family is
assumed: it is derived from the outer restriction, the constituentwise inner restrictions, and
the canonical dependent-sum reindexing.
-/

namespace AlgebraicComplexity

open Tensor

universe u v w x y

namespace OuterConstituentStage

variable (K : Type u) [CommSemiring K]

/-- Exact, naturally indexed inner restrictions for every survivor of an outer constituent stage.

This proposition installs the constituent-space instances stored in `outer` before stating the
dependent restriction family.  Keeping that installation behind a named definition avoids asking
clients to repeat implementation-level instance plumbing. -/
def HasExactDependentInnerExtraction
    {Source : Leg → Type v}
    [∀ c, AddCommMonoid (Source c)] [∀ c, Module K (Source c)]
    {source : Tensor3 K Source} {outerCopies xSize ySize zSize : ℕ}
    (outer : OuterConstituentStage.{u, v, w, x} K source outerCopies)
    (J : outer.I → Type y) [∀ i, Fintype (J i)] : Prop := by
  letI := outer.addCommMonoidW
  letI := outer.moduleW
  exact ∀ i, Restricts (outer.constituent i)
    (Tensor.indexedDirectSum (fun _j : J i ↦
      matrixMultiplication (K := K) xSize ySize zSize))

/-- Refine every outer constituent by an exact, uniformly sized matrix-multiplication family and
flatten the two indices.

The natural inner index type may depend on the outer survivor.  Only its cardinality is required
to be constant.  The output contains exactly `outerCopies * innerCopies` equal rectangular
matrix-multiplication tensors. -/
noncomputable def toWholeConstituentLaserVolumeStage_of_exactInner
    {Source : Leg → Type v}
    [∀ c, AddCommMonoid (Source c)] [∀ c, Module K (Source c)]
    {source : Tensor3 K Source} {outerCopies innerCopies xSize ySize zSize : ℕ}
    (outer : OuterConstituentStage.{u, v, w, x} K source outerCopies)
    (J : outer.I → Type y) [∀ i, Fintype (J i)]
    (hcard : ∀ i, Fintype.card (J i) = innerCopies)
    (hinner : HasExactDependentInnerExtraction K outer J
      (xSize := xSize) (ySize := ySize) (zSize := zSize)) :
    WholeConstituentLaserVolumeStage K source
      (outerCopies * innerCopies) xSize ySize zSize := by
  classical
  letI := outer.fintypeI
  letI := outer.addCommMonoidW
  letI := outer.moduleW
  refine
    { I := Σ i, J i
      card_I := ?_
      source_restricts := ?_ }
  · rw [Fintype.card_sigma]
    calc
      ∑ i, Fintype.card (J i) = ∑ _i : outer.I, innerCopies := by
        apply Finset.sum_congr rfl
        intro i _
        exact hcard i
      _ = Fintype.card outer.I * innerCopies := by simp
      _ = outerCopies * innerCopies := by rw [outer.card_I]
  · have hnested : Restricts
        (Tensor.indexedDirectSum outer.constituent)
        (Tensor.indexedDirectSum fun i ↦
          Tensor.indexedDirectSum (fun _j : J i ↦
            matrixMultiplication (K := K) xSize ySize zSize)) :=
      Tensor.Restricts.indexedDirectSum hinner
    have hflatten : Restricts
        (Tensor.indexedDirectSum fun i ↦
          Tensor.indexedDirectSum (fun _j : J i ↦
            matrixMultiplication (K := K) xSize ySize zSize))
        (Tensor.indexedDirectSum fun _pair : Σ i, J i ↦
          matrixMultiplication (K := K) xSize ySize zSize) :=
      (Tensor.Isomorphic.indexedDirectSum_sigma
        (K := K) (J := J)
        (S := fun _i _j _c ↦ MMSpace K xSize ySize zSize _c)
        (T := fun _pair : Σ i, J i ↦
          matrixMultiplication (K := K) xSize ySize zSize)).symm.restricts
    exact outer.source_restricts.trans (hnested.trans (by
      simpa only [matrixMultiplicationDirectSum] using hflatten))

end OuterConstituentStage

end AlgebraicComplexity
