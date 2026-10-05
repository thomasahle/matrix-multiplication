/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinograd112CTensor
import AlgebraicComplexity.Examples.CoppersmithWinograd112SymmetricTypedLeaf
import AlgebraicComplexity.MatrixMultiplication.TypeExtraction

/-!
# Matrix restrictions of the symmetric CW `112` constituents

The symmetric `112` partition is the external product of the primitive partition with its two
cyclic leg orientations.  This file proves that every one of its 64 supported constituents
restricts to the rectangular matrix-multiplication tensor recorded by the symmetric rational
typed leaf.

The proof is structural rather than a 64-case enumeration.  Each source address uses one of the
four already checked primitive CW restrictions.  The second and third restrictions are transported
through the two leg permutations, and the three resulting matrix tensors are combined with the
generic external-product isomorphism.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor

universe u

variable (K : Type u) [CommRing K]

/-- Regard a combinatorial `112` support address as a supported address of the actual primitive
partitioned tensor. -/
def cw112AsPartitionSupport (q : ℕ) (s : cw112BlockSupport) :
    (cw112PartitionedTensor K q).support :=
  ⟨s.1, by simpa only [cw112PartitionedTensor_support] using s.2⟩

/-- The primitive typed-leaf dimensions agree pointwise with the dimensions used by the checked
constituent restrictions.

Proof sketch: inspect the four primitive support addresses.  Diagonal addresses have dimensions
`(1,q,1)` and cross addresses have dimensions `(q,1,q)`. -/
theorem cw112LeafDimension_eq_tensorConstituentDimension
    (q : ℕ) (s : cw112BlockSupport) (c : Leg) :
    cw112LeafDimension q s c =
      match c with
      | .X => cw112TensorConstituentM K q (cw112AsPartitionSupport K q s)
      | .Y => cw112TensorConstituentN K q (cw112AsPartitionSupport K q s)
      | .Z => cw112TensorConstituentP K q (cw112AsPartitionSupport K q s) := by
  rcases s with ⟨s, hs⟩
  simp only [cw112BlockSupport, Finset.mem_insert, Finset.mem_singleton] at hs
  rcases hs with rfl | rfl | rfl | rfl <;>
    cases c <;>
    simp [cw112LeafDimension, cw112AsPartitionSupport,
      cw112TensorConstituentM, cw112TensorConstituentN,
      cw112TensorConstituentP,
      cw112DiagonalFirstAddress, cw112DiagonalSecondAddress,
      cw112CrossFirstAddress, cw112CrossSecondAddress, cw112BlockAddress]

/-- Every primitive support address restricts to the matrix tensor described pointwise by
`cw112LeafDimension`. -/
theorem cw112SupportedConstituent_restricts_leafDimension
    (q : ℕ) (s : cw112BlockSupport) :
    Restricts ((cw112PartitionedTensor K q).constituent s.1)
      (matrixMultiplication (K := K)
        (cw112LeafDimension q s .X)
        (cw112LeafDimension q s .Y)
        (cw112LeafDimension q s .Z)) := by
  have h := cw112SupportedConstituent_restricts K q
    (cw112AsPartitionSupport K q s)
  exact h.trans
    (Tensor.Isomorphic.matrixMultiplication_congr (K := K)
      (cw112LeafDimension_eq_tensorConstituentDimension K q s .X).symm
      (cw112LeafDimension_eq_tensorConstituentDimension K q s .Y).symm
      (cw112LeafDimension_eq_tensorConstituentDimension K q s .Z).symm).restricts

/-- The constituent of a cyclically permuted partition restricts to the correspondingly rotated
matrix-multiplication tensor. -/
private theorem cw112CycleConstituent_restricts
    (q : ℕ) (s : cw112BlockSupport) :
    Restricts
      (((cw112PartitionedTensor K q).permute cycle).constituent
        (permuteBlockAddress cycle s.1))
      (matrixMultiplication (K := K)
        (cw112LeafDimension q s .Z)
        (cw112LeafDimension q s .X)
        (cw112LeafDimension q s .Y)) := by
  let source : cw112BlockSupport :=
    ⟨(permuteBlockAddress cycle).symm (permuteBlockAddress cycle s.1), by
      simpa using s.2⟩
  have hsource := cw112SupportedConstituent_restricts_leafDimension K q source
  have hpermuted := hsource.permute cycle
  have hcast : Restricts
      (((cw112PartitionedTensor K q).permute cycle).constituent
        (permuteBlockAddress cycle s.1))
      (Tensor.permute cycle ((cw112PartitionedTensor K q).constituent source.1)) := by
    rw [PartitionedTensor.permute_constituent]
    exact (Tensor.Isomorphic.map
      (Tensor.permute cycle ((cw112PartitionedTensor K q).constituent source.1))
      (fun c ↦ permuteBlockSpaceCast (K := K)
        (V := CW112PartitionBlockSpace K q) cycle
        (permuteBlockAddress cycle s.1) c)).symm.restricts
  have hresult := hcast.trans (hpermuted.trans
    (Tensor.Isomorphic.matrixMultiplication_cycle (K := K)
      (cw112LeafDimension q source .X)
      (cw112LeafDimension q source .Y)
      (cw112LeafDimension q source .Z)).restricts)
  have hsourceEq : source = s := by
    apply Subtype.ext
    exact (permuteBlockAddress cycle).symm_apply_apply s.1
  rw [hsourceEq] at hresult
  exact hresult

/-- The constituent of an inverse-cyclic partition restricts to the oppositely rotated matrix
tensor. -/
private theorem cw112CycleSymmConstituent_restricts
    (q : ℕ) (s : cw112BlockSupport) :
    Restricts
      (((cw112PartitionedTensor K q).permute cycle.symm).constituent
        (permuteBlockAddress cycle.symm s.1))
      (matrixMultiplication (K := K)
        (cw112LeafDimension q s .Y)
        (cw112LeafDimension q s .Z)
        (cw112LeafDimension q s .X)) := by
  let source : cw112BlockSupport :=
    ⟨(permuteBlockAddress cycle.symm).symm
        (permuteBlockAddress cycle.symm s.1), by
      simpa using s.2⟩
  have hsource := cw112SupportedConstituent_restricts_leafDimension K q source
  have hpermuted := hsource.permute cycle.symm
  have hcast : Restricts
      (((cw112PartitionedTensor K q).permute cycle.symm).constituent
        (permuteBlockAddress cycle.symm s.1))
      (Tensor.permute cycle.symm
        ((cw112PartitionedTensor K q).constituent source.1)) := by
    rw [PartitionedTensor.permute_constituent]
    exact (Tensor.Isomorphic.map
      (Tensor.permute cycle.symm
        ((cw112PartitionedTensor K q).constituent source.1))
      (fun c ↦ permuteBlockSpaceCast (K := K)
        (V := CW112PartitionBlockSpace K q) cycle.symm
        (permuteBlockAddress cycle.symm s.1) c)).symm.restricts
  have hresult := hcast.trans (hpermuted.trans
    (Tensor.Isomorphic.matrixMultiplication_cycle_symm (K := K)
      (cw112LeafDimension q source .X)
      (cw112LeafDimension q source .Y)
      (cw112LeafDimension q source .Z)).restricts)
  have hsourceEq : source = s := by
    apply Subtype.ext
    exact (permuteBlockAddress cycle.symm).symm_apply_apply s.1
  rw [hsourceEq] at hresult
  exact hresult

/-- Every supported constituent of the three-orientation `112` product restricts to the matrix
tensor recorded by the support-indexed symmetric typed leaf.

Proof sketch: decode the supported address into its three primitive sources.  Restrict the first
constituent directly and the other two after their cyclic orientations.  External-product closure
and the generic matrix-product law multiply the three dimension triples; these products are
definitionally the dimensions of `RationalTypedLeaf.cyclicProduct`, transported through the
support equivalence. -/
theorem cw112SymmetricSupportedConstituent_restricts
    (q L G : ℕ) (hq : 0 < q) (hL : 0 < L) (hG : 0 < G)
    (s : (cw112SymmetricPartitionedTensor K q).support) :
    Restricts ((cw112SymmetricPartitionedTensor K q).constituent s.1)
      (matrixMultiplication (K := K)
        ((cw112SymmetricPartitionRationalTypedLeaf K q L G hq hL hG).dimension s .X)
        ((cw112SymmetricPartitionRationalTypedLeaf K q L G hq hL hG).dimension s .Y)
        ((cw112SymmetricPartitionRationalTypedLeaf K q L G hq hL hG).dimension s .Z)) := by
  let sources := (cw112SymmetricPartitionSupportEquiv K q).symm s
  have hsources : cw112SymmetricPartitionSupportEquiv K q sources = s := by
    exact (cw112SymmetricPartitionSupportEquiv K q).apply_symm_apply s
  have hfirst := cw112SupportedConstituent_restricts_leafDimension K q sources.1.1
  have hsecond := cw112CycleConstituent_restricts K q sources.1.2
  have hthird := cw112CycleSymmConstituent_restricts K q sources.2
  have hproduct := (hfirst.external hsecond).external hthird
  have hmm :=
    (Tensor.Isomorphic.matrixMultiplication_external (K := K)
      (cw112LeafDimension q sources.1.1 .X)
      (cw112LeafDimension q sources.1.1 .Y)
      (cw112LeafDimension q sources.1.1 .Z)
      (cw112LeafDimension q sources.1.2 .Z)
      (cw112LeafDimension q sources.1.2 .X)
      (cw112LeafDimension q sources.1.2 .Y)).restricts
  have hmmThree :=
    (Tensor.Isomorphic.matrixMultiplication_external (K := K)
      (cw112LeafDimension q sources.1.1 .X * cw112LeafDimension q sources.1.2 .Z)
      (cw112LeafDimension q sources.1.1 .Y * cw112LeafDimension q sources.1.2 .X)
      (cw112LeafDimension q sources.1.1 .Z * cw112LeafDimension q sources.1.2 .Y)
      (cw112LeafDimension q sources.2 .Y)
      (cw112LeafDimension q sources.2 .Z)
      (cw112LeafDimension q sources.2 .X)).restricts
  have hmatrix := hproduct.trans ((hmm.external
    (Tensor.Restricts.refl (matrixMultiplication (K := K)
      (cw112LeafDimension q sources.2 .Y)
      (cw112LeafDimension q sources.2 .Z)
      (cw112LeafDimension q sources.2 .X)))).trans hmmThree)
  have hAtSources :
      Restricts
        ((cw112SymmetricPartitionedTensor K q).constituent
          (cw112SymmetricAddress sources))
        (matrixMultiplication (K := K)
          (cw112LeafDimension q sources.1.1 .X *
            cw112LeafDimension q sources.1.2 .Z *
            cw112LeafDimension q sources.2 .Y)
          (cw112LeafDimension q sources.1.1 .Y *
            cw112LeafDimension q sources.1.2 .X *
            cw112LeafDimension q sources.2 .Z)
          (cw112LeafDimension q sources.1.1 .Z *
            cw112LeafDimension q sources.1.2 .Y *
            cw112LeafDimension q sources.2 .X)) := by
    change Restricts
      (Tensor.external
        (Tensor.external
          ((cw112PartitionedTensor K q).constituent sources.1.1.1)
          (((cw112PartitionedTensor K q).permute cycle).constituent
            (permuteBlockAddress cycle sources.1.2.1)))
        (((cw112PartitionedTensor K q).permute cycle.symm).constituent
          (permuteBlockAddress cycle.symm sources.2.1))) _
    exact hmatrix
  have hdimension (c : Leg) :
      (cw112SymmetricPartitionRationalTypedLeaf K q L G hq hL hG).dimension
          (cw112SymmetricPartitionSupportEquiv K q sources) c =
        match c with
        | .X => cw112LeafDimension q sources.1.1 .X *
            cw112LeafDimension q sources.1.2 .Z *
            cw112LeafDimension q sources.2 .Y
        | .Y => cw112LeafDimension q sources.1.1 .Y *
            cw112LeafDimension q sources.1.2 .X *
            cw112LeafDimension q sources.2 .Z
        | .Z => cw112LeafDimension q sources.1.1 .Z *
            cw112LeafDimension q sources.1.2 .Y *
            cw112LeafDimension q sources.2 .X := by
    change (cw112SymmetricRationalTypedLeaf q L G hq hL hG).dimension
      ((cw112SymmetricPartitionSupportEquiv K q).symm
        (cw112SymmetricPartitionSupportEquiv K q sources)) c = _
    rw [(cw112SymmetricPartitionSupportEquiv K q).symm_apply_apply]
    cases c <;>
      rfl
  have hAtLeafAddress :
      Restricts
        ((cw112SymmetricPartitionedTensor K q).constituent
          (cw112SymmetricPartitionSupportEquiv K q sources).1)
        (matrixMultiplication (K := K)
          ((cw112SymmetricPartitionRationalTypedLeaf K q L G hq hL hG).dimension
            (cw112SymmetricPartitionSupportEquiv K q sources) .X)
          ((cw112SymmetricPartitionRationalTypedLeaf K q L G hq hL hG).dimension
            (cw112SymmetricPartitionSupportEquiv K q sources) .Y)
          ((cw112SymmetricPartitionRationalTypedLeaf K q L G hq hL hG).dimension
            (cw112SymmetricPartitionSupportEquiv K q sources) .Z)) := by
    rw [cw112SymmetricPartitionSupportEquiv_val]
    exact hAtSources.trans
      (Tensor.Isomorphic.matrixMultiplication_congr (K := K)
        (hdimension .X).symm (hdimension .Y).symm (hdimension .Z).symm).restricts
  rw [hsources] at hAtLeafAddress
  exact hAtLeafAddress

end AlgebraicComplexity.Examples
