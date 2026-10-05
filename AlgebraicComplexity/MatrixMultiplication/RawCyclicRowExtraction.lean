/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Combinatorics.ProportionalTypeClassCore
import AlgebraicComplexity.MatrixMultiplication.CyclicTypedLeaf
import AlgebraicComplexity.MatrixMultiplication.MarkedPartitionedPowerHashing
import AlgebraicComplexity.MatrixMultiplication.PartitionedSymmetrizationPower
import AlgebraicComplexity.MatrixMultiplication.PartitionedTypeAssembly
import AlgebraicComplexity.MatrixMultiplication.RationalTypedLeafReindex
import AlgebraicComplexity.Tensor.PartitionedProductConstituent
import AlgebraicComplexity.Tensor.PartitionedReindexConstituent

set_option autoImplicit false

/-!
# One-hash extraction of a raw cyclic row

The Total-Weight legal-hybrid Mode B uses a new finite specialization in which three cyclic
orientations of one raw row are assembled before one joint affine hash is applied.  This module
formalizes the specialization's finite semantic step while retaining an arbitrary lower-level
child interface.  The result is intended for the forthcoming legal-hybrid appendix of
`better_bound/paper.tex`; it is not a theorem stated in [alman2025more].

For a partitioned tensor `P`, the support of `P.symThreePartition` is canonically the ordered
triple of primitive support addresses.  An exact cyclic-product type on a joint word projects to
the same scaled primitive type in all three orientations.  Consequently one joint marked-hashing
extraction from the actual positive power of `P.symThreePartition` restricts to an indexed direct
sum of identical `symThree` copies of any reference child constituent of that primitive type.

The main theorem does not assume an assembled tensor restriction and does not reduce the child to
a matrix-multiplication tensor.  A concrete recursive client must still construct the raw-row
partition and, for the approximate parent selection in the paper, account for the input-profile
holes before applying this theorem.

## Provenance

- The one-joint-hash raw-cyclic specialization is new to the Total-Weight manuscript and will be
  stated in its legal-hybrid appendix.
- [alman2025more] Josh Alman, Ran Duan, Virginia Vassilevska Williams, Yinzhan Xu, Zixuan Xu,
  and Renfei Zhou, *More Asymmetry Yields Faster Matrix Multiplication*, supplies the ordinary
  partitioned-power, constituent-extraction, compatibility, and repair ingredients only:
  `papers/sources/2404.16349/overview.tex:18-40` and
  `papers/sources/2404.16349/constituent.tex:113-147,338-348,376-440,483-497`.
-/

namespace AlgebraicComplexity

open Tensor

universe u v w x

variable {K : Type u} [CommSemiring K]
variable {A : Leg → Type w} [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]
variable {V : ∀ c, A c → Type (max u v)}
variable [∀ c a, AddCommMonoid (V c a)] [∀ c a, Module K (V c a)]
variable {R : Type x} [Field R]

namespace Tensor.PartitionedTensor

omit [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)] in
/-- Reading the word-transpose equivalence positionwise returns the three source letters. -/
theorem positiveWordEquiv_symThreeWordEquiv
    (n : ℕ) (c : Leg)
    (p : ProductBlockIndex (ProductBlockIndex (fun c ↦ PositiveWord (A c) n)
      (PermutedBlockIndex cycle (fun c ↦ PositiveWord (A c) n)))
      (PermutedBlockIndex cycle.symm (fun c ↦ PositiveWord (A c) n)) c) :
    positiveWordEquiv _ n (symThreeWordEquiv (A := A) n c p) =
      fun i ↦ ((positiveWordEquiv (A c) n p.1.1 i,
          positiveWordEquiv (A (cycle.symm c)) n p.1.2 i),
        positiveWordEquiv (A (cycle.symm.symm c)) n p.2 i) := by
  show positiveWordEquiv _ n
      (positiveWordProdEquiv (A c × A (cycle.symm c)) (A (cycle.symm.symm c)) n
        (positiveWordProdEquiv (A c) (A (cycle.symm c)) n (p.1.1, p.1.2), p.2)) = _
  rw [positiveWordEquiv_positiveWordProdEquiv]
  funext i
  rw [positiveWordEquiv_positiveWordProdEquiv]

private def symThreeFirstAddress
    (s : BlockAddress (ProductBlockIndex (ProductBlockIndex A (PermutedBlockIndex cycle A))
      (PermutedBlockIndex cycle.symm A))) : BlockAddress A :=
  fun c ↦ (s c).1.1

private def symThreeSecondAddress
    (s : BlockAddress (ProductBlockIndex (ProductBlockIndex A (PermutedBlockIndex cycle A))
      (PermutedBlockIndex cycle.symm A))) : BlockAddress A :=
  (permuteBlockAddress cycle).symm (fun c ↦ (s c).1.2)

private def symThreeThirdAddress
    (s : BlockAddress (ProductBlockIndex (ProductBlockIndex A (PermutedBlockIndex cycle A))
      (PermutedBlockIndex cycle.symm A))) : BlockAddress A :=
  (permuteBlockAddress cycle.symm).symm (fun c ↦ (s c).2)

private def symThreeSupportAddress
    (P : PartitionedTensor (K := K) (A := A) V) (source : CyclicTriple P.support) :
    BlockAddress (ProductBlockIndex (ProductBlockIndex A (PermutedBlockIndex cycle A))
      (PermutedBlockIndex cycle.symm A)) :=
  blockAddressProductEquiv
    (blockAddressProductEquiv
      (source.1.1.1, permuteBlockAddress cycle source.1.2.1),
      permuteBlockAddress cycle.symm source.2.1)

@[simp] private theorem symThreeFirstAddress_supportAddress
    (P : PartitionedTensor (K := K) (A := A) V) (source : CyclicTriple P.support) :
    symThreeFirstAddress (symThreeSupportAddress P source) = source.1.1.1 := by
  rfl

@[simp] private theorem symThreeSecondAddress_supportAddress
    (P : PartitionedTensor (K := K) (A := A) V) (source : CyclicTriple P.support) :
    symThreeSecondAddress (symThreeSupportAddress P source) = source.1.2.1 := by
  unfold symThreeSecondAddress symThreeSupportAddress
  exact (permuteBlockAddress cycle).symm_apply_apply source.1.2.1

@[simp] private theorem symThreeThirdAddress_supportAddress
    (P : PartitionedTensor (K := K) (A := A) V) (source : CyclicTriple P.support) :
    symThreeThirdAddress (symThreeSupportAddress P source) = source.2.1 := by
  unfold symThreeThirdAddress symThreeSupportAddress
  exact (permuteBlockAddress cycle.symm).symm_apply_apply source.2.1

private theorem symThreeSupportAddress_mem
    (P : PartitionedTensor (K := K) (A := A) V) (source : CyclicTriple P.support) :
    symThreeSupportAddress P source ∈ P.symThreePartition.support := by
  simp only [PartitionedTensor.symThreePartition,
    PartitionedTensor.mem_external_support, PartitionedTensor.mem_permute_support]
  exact ⟨⟨source.1.1.2, by
    change (permuteBlockAddress cycle).symm
      (permuteBlockAddress cycle source.1.2.1) ∈ P.support
    rw [Equiv.symm_apply_apply]
    exact source.1.2.2⟩, by
      change (permuteBlockAddress cycle.symm).symm
        (permuteBlockAddress cycle.symm source.2.1) ∈ P.support
      rw [Equiv.symm_apply_apply]
      exact source.2.2⟩

private def symThreeSupportSources
    (P : PartitionedTensor (K := K) (A := A) V)
    (s : P.symThreePartition.support) : CyclicTriple P.support := by
  have houter := (PartitionedTensor.mem_external_support
    (P.external (P.permute cycle)) (P.permute cycle.symm) s.1).mp s.2
  have hinner := (PartitionedTensor.mem_external_support
    P (P.permute cycle) (fun c ↦ (s.1 c).1)).mp houter.1
  exact ((⟨symThreeFirstAddress s.1, hinner.1⟩,
    ⟨symThreeSecondAddress s.1,
      (PartitionedTensor.mem_permute_support P cycle (fun c ↦ (s.1 c).1.2)).mp hinner.2⟩),
    ⟨symThreeThirdAddress s.1,
      (PartitionedTensor.mem_permute_support P cycle.symm (fun c ↦ (s.1 c).2)).mp houter.2⟩)

/-- The actual three-orientation support is canonically equivalent to three ordered primitive
support addresses. -/
def symThreeSupportEquiv
    (P : PartitionedTensor (K := K) (A := A) V) :
    CyclicTriple P.support ≃ P.symThreePartition.support where
  toFun source := ⟨symThreeSupportAddress P source, symThreeSupportAddress_mem P source⟩
  invFun := symThreeSupportSources P
  left_inv source := by
    rcases source with ⟨⟨first, second⟩, third⟩
    apply Prod.ext
    · apply Prod.ext <;> apply Subtype.ext <;>
        simp [symThreeSupportSources]
    · apply Subtype.ext
      simp [symThreeSupportSources]
  right_inv s := by
    apply Subtype.ext
    funext c
    have hsecond :
        permuteBlockAddress cycle (symThreeSecondAddress s.1) =
          (fun c ↦ (s.1 c).1.2) := by
      exact (permuteBlockAddress cycle).apply_symm_apply _
    have hthird :
        permuteBlockAddress cycle.symm (symThreeThirdAddress s.1) =
          (fun c ↦ (s.1 c).2) := by
      exact (permuteBlockAddress cycle.symm).apply_symm_apply _
    change ((symThreeFirstAddress s.1 c,
      permuteBlockAddress cycle (symThreeSecondAddress s.1) c),
        permuteBlockAddress cycle.symm (symThreeThirdAddress s.1) c) = s.1 c
    rw [congrFun hsecond c, congrFun hthird c]
    rfl

/-- The block address in `symThree (P.positivePower n)` assembled from three primitive words. -/
noncomputable def symThreePositivePowerAddress
    (P : PartitionedTensor (K := K) (A := A) V) (n : ℕ)
    (q₀ q₁ q₂ : PositiveWord P.support n) :
    BlockAddress (ProductBlockIndex
      (ProductBlockIndex (fun c ↦ PositiveWord (A c) n)
        (PermutedBlockIndex cycle (fun c ↦ PositiveWord (A c) n)))
      (PermutedBlockIndex cycle.symm (fun c ↦ PositiveWord (A c) n))) :=
  blockAddressProductEquiv
    (blockAddressProductEquiv
      (positiveSupportWordBlockAddress P.support n q₀,
        permuteBlockAddress cycle
          (positiveSupportWordBlockAddress P.support n q₁)),
      permuteBlockAddress cycle.symm
        (positiveSupportWordBlockAddress P.support n q₂))

private theorem isomorphic_permutedConstituent_apply
    (P : PartitionedTensor (K := K) (A := A) V) (e : Orientation)
    (s : BlockAddress A) :
    Isomorphic (Tensor.permute e (P.constituent s))
      ((P.permute e).constituent (permuteBlockAddress e s)) := by
  have h : Isomorphic
      (Tensor.permute e
        (P.constituent ((permuteBlockAddress e).symm (permuteBlockAddress e s))))
      ((P.permute e).constituent (permuteBlockAddress e s)) :=
    Isomorphic.map _ (fun c ↦ permuteBlockSpaceCast
      (K := K) (V := V) e (permuteBlockAddress e s) c)
  rwa [Equiv.symm_apply_apply] at h

/-- A word-transposed constituent of the positive power of `symThree P` is `symThree` of one
reference constituent whenever its three primitive words have the same exact type.

Proof sketch: the power/symmetrization transpose first identifies the joint constituent with the
external product of the three oriented constituents.  Same-type position relabelings identify the
second and third constituents with cyclic images of the first. -/
theorem isomorphic_symThreePositivePower_constituent_of_same_type
    (P : PartitionedTensor (K := K) (A := A) V) (n : ℕ)
    (q₀ q₁ q₂ : PositiveWord P.support n)
    (h₁ : WordType.multiplicity (positiveWordEquiv P.support n q₁) =
      WordType.multiplicity (positiveWordEquiv P.support n q₀))
    (h₂ : WordType.multiplicity (positiveWordEquiv P.support n q₂) =
      WordType.multiplicity (positiveWordEquiv P.support n q₀)) :
    Isomorphic
      (((P.symThreePartition).positivePower n).constituent
        (blockAddressCongr (symThreeWordEquiv (A := A) n)
          (symThreePositivePowerAddress P n q₀ q₁ q₂)))
      (symThree K
        ((P.positivePower n).constituent
          (positiveSupportWordBlockAddress P.support n q₀))) := by
  let a₀ := positiveSupportWordBlockAddress P.support n q₀
  let a₁ := positiveSupportWordBlockAddress P.support n q₁
  let a₂ := positiveSupportWordBlockAddress P.support n q₂
  let sourceAddress := symThreePositivePowerAddress P n q₀ q₁ q₂
  let targetAddress := blockAddressCongr (symThreeWordEquiv (A := A) n) sourceAddress
  have htransport :=
    (reindexEquiv_symThreePartition_positivePower P n).constituent_isomorphic targetAddress
  have hinverse :
      (blockAddressCongr (symThreeWordEquiv (A := A) n)).symm targetAddress = sourceAddress :=
    (blockAddressCongr (symThreeWordEquiv (A := A) n)).symm_apply_apply sourceAddress
  rw [hinverse] at htransport
  have hsame₁ := Tensor.Isomorphic.positivePower_constituent_of_same_type P n q₁ q₀ h₁
  have hsame₂ := Tensor.Isomorphic.positivePower_constituent_of_same_type P n q₂ q₀ h₂
  have hperm₁ : Isomorphic
      (((P.positivePower n).permute cycle).constituent (permuteBlockAddress cycle a₁))
      (Tensor.permute cycle ((P.positivePower n).constituent a₀)) :=
    (isomorphic_permutedConstituent_apply (P.positivePower n) cycle a₁).symm.trans
      (hsame₁.permute_legs cycle)
  have hperm₂ : Isomorphic
      (((P.positivePower n).permute cycle.symm).constituent
        (permuteBlockAddress cycle.symm a₂))
      (Tensor.permute cycle.symm ((P.positivePower n).constituent a₀)) :=
    (isomorphic_permutedConstituent_apply (P.positivePower n) cycle.symm a₂).symm.trans
      (hsame₂.permute_legs cycle.symm)
  have hsource : Isomorphic
      (((P.positivePower n).symThreePartition).constituent sourceAddress)
      (symThree K ((P.positivePower n).constituent a₀)) := by
    change Isomorphic
      (Tensor.external
        (Tensor.external ((P.positivePower n).constituent a₀)
          (((P.positivePower n).permute cycle).constituent
            (permuteBlockAddress cycle a₁)))
        (((P.positivePower n).permute cycle.symm).constituent
          (permuteBlockAddress cycle.symm a₂)))
      (symThree K ((P.positivePower n).constituent a₀))
    exact ((Isomorphic.refl ((P.positivePower n).constituent a₀)).external hperm₁).external hperm₂
  exact htransport.symm.trans hsource

end Tensor.PartitionedTensor

namespace WordType

private theorem mappedType_equiv
    {I J : Type w} [Fintype I] (e : I ≃ J) (profile : I → ℕ) :
    mappedType e profile = fun j ↦ profile (e.symm j) := by
  classical
  funext j
  have hfiber : letterFiber (e : I → J) j = {e.symm j} := by
    ext i
    simp [mem_letterFiber, Equiv.apply_eq_iff_eq_symm_apply]
  show ∑ i ∈ letterFiber (e : I → J) j, profile i = profile (e.symm j)
  rw [hfiber, Finset.sum_singleton]

end WordType

namespace PositiveIntegralProfile

variable {I : Type w} [Fintype I]

private theorem mappedType_cyclicProduct_fst_fst (profile : PositiveIntegralProfile I) :
    WordType.mappedType (fun source : CyclicTriple I ↦ source.1.1)
        profile.cyclicProduct.count =
      fun i ↦ profile.count i * profile.mass ^ 2 := by
  classical
  funext i
  simp [WordType.mappedType_eq_sum_ite, Fintype.sum_prod_type,
    PositiveIntegralProfile.cyclicProduct,
    PositiveIntegralProfile.mass, WordType.profileMass, pow_two,
    Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro left _
  apply Finset.sum_congr rfl
  intro right _
  ring

private theorem mappedType_cyclicProduct_fst_snd (profile : PositiveIntegralProfile I) :
    WordType.mappedType (fun source : CyclicTriple I ↦ source.1.2)
        profile.cyclicProduct.count =
      fun i ↦ profile.count i * profile.mass ^ 2 := by
  classical
  funext i
  simp [WordType.mappedType_eq_sum_ite, Fintype.sum_prod_type,
    PositiveIntegralProfile.cyclicProduct,
    PositiveIntegralProfile.mass, WordType.profileMass, pow_two,
    Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro left _
  apply Finset.sum_congr rfl
  intro right _
  ring

private theorem mappedType_cyclicProduct_snd (profile : PositiveIntegralProfile I) :
    WordType.mappedType (fun source : CyclicTriple I ↦ source.2)
        profile.cyclicProduct.count =
      fun i ↦ profile.count i * profile.mass ^ 2 := by
  classical
  funext i
  simp [WordType.mappedType_eq_sum_ite, Fintype.sum_prod_type,
    PositiveIntegralProfile.cyclicProduct,
    PositiveIntegralProfile.mass, WordType.profileMass, pow_two,
    Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro left _
  apply Finset.sum_congr rfl
  intro right _
  ring

/-- Exact proportional type induced on the first factor of a cyclic product profile. -/
theorem mappedType_proportionalCounts_cyclicProduct_fst_fst
    (profile : PositiveIntegralProfile I) (k : ℕ) :
    WordType.mappedType (fun source : CyclicTriple I ↦ source.1.1)
        (WordType.proportionalCounts profile.cyclicProduct.count k) =
      WordType.proportionalCounts profile.count (profile.mass ^ 2 * k) := by
  rw [WordType.mappedType_proportionalCounts, mappedType_cyclicProduct_fst_fst]
  funext i
  simp only [WordType.proportionalCounts]
  ring

/-- Exact proportional type induced on the second factor of a cyclic product profile. -/
theorem mappedType_proportionalCounts_cyclicProduct_fst_snd
    (profile : PositiveIntegralProfile I) (k : ℕ) :
    WordType.mappedType (fun source : CyclicTriple I ↦ source.1.2)
        (WordType.proportionalCounts profile.cyclicProduct.count k) =
      WordType.proportionalCounts profile.count (profile.mass ^ 2 * k) := by
  rw [WordType.mappedType_proportionalCounts, mappedType_cyclicProduct_fst_snd]
  funext i
  simp only [WordType.proportionalCounts]
  ring

/-- Exact proportional type induced on the third factor of a cyclic product profile. -/
theorem mappedType_proportionalCounts_cyclicProduct_snd
    (profile : PositiveIntegralProfile I) (k : ℕ) :
    WordType.mappedType (fun source : CyclicTriple I ↦ source.2)
        (WordType.proportionalCounts profile.cyclicProduct.count k) =
      WordType.proportionalCounts profile.count (profile.mass ^ 2 * k) := by
  rw [WordType.mappedType_proportionalCounts, mappedType_cyclicProduct_snd]
  funext i
  simp only [WordType.proportionalCounts]
  ring

omit [Fintype I] in
private theorem mappedType_symm_reindex
    {J : Type w} [Fintype J] (profile : PositiveIntegralProfile I) (e : I ≃ J) :
    WordType.mappedType e.symm (profile.reindex e).count = profile.count := by
  rw [WordType.mappedType_equiv]
  funext i
  simp [PositiveIntegralProfile.reindex]

omit [Fintype I] in
private theorem mappedType_proportionalCounts_symm_reindex
    {J : Type w} [Fintype J] (profile : PositiveIntegralProfile I) (e : I ≃ J) (k : ℕ) :
    WordType.mappedType e.symm
        (WordType.proportionalCounts (profile.reindex e).count k) =
      WordType.proportionalCounts profile.count k := by
  rw [WordType.mappedType_proportionalCounts, mappedType_symm_reindex]

end PositiveIntegralProfile

namespace Tensor.PartitionedTensor

/-- The cyclic product profile transported onto the support of the actual symmetrized partition. -/
noncomputable def symThreeSupportProfile
    (P : PartitionedTensor (K := K) (A := A) V)
    (profile : PositiveIntegralProfile P.support) :
    PositiveIntegralProfile P.symThreePartition.support :=
  profile.cyclicProduct.reindex (symThreeSupportEquiv P)

/-- Project a positive word in the actual symmetrized support to its three primitive source words,
with every leg permutation removed. -/
noncomputable def symThreePrimitiveWords
    (P : PartitionedTensor (K := K) (A := A) V) (n : ℕ)
    (word : PositiveWord P.symThreePartition.support n) :
    CyclicTriple (PositiveWord P.support n) :=
  let tripleWord := positiveWordMap (symThreeSupportEquiv P).symm n word
  ((positiveWordMap (fun source : CyclicTriple P.support ↦ source.1.1) n tripleWord,
    positiveWordMap (fun source : CyclicTriple P.support ↦ source.1.2) n tripleWord),
    positiveWordMap (fun source : CyclicTriple P.support ↦ source.2) n tripleWord)

/-- An exact cyclic product type projects to the exact scaled primitive type in the first
orientation. -/
theorem multiplicity_symThreePrimitiveWords_fst_fst
    (P : PartitionedTensor (K := K) (A := A) V)
    (profile : PositiveIntegralProfile P.support) (n k : ℕ)
    (word : PositiveWord P.symThreePartition.support n)
    (htype : WordType.multiplicity
        (positiveWordEquiv P.symThreePartition.support n word) =
      WordType.proportionalCounts (symThreeSupportProfile P profile).count k) :
    WordType.multiplicity
        (positiveWordEquiv P.support n (symThreePrimitiveWords P n word).1.1) =
      WordType.proportionalCounts profile.count (profile.mass ^ 2 * k) := by
  let tripleWord := positiveWordMap (symThreeSupportEquiv P).symm n word
  have htriple : WordType.multiplicity
      (positiveWordEquiv (CyclicTriple P.support) n tripleWord) =
      WordType.proportionalCounts profile.cyclicProduct.count k := by
    rw [positiveWordEquiv_map, WordType.multiplicity_comp_eq_mappedType, htype]
    exact PositiveIntegralProfile.mappedType_proportionalCounts_symm_reindex
      profile.cyclicProduct (symThreeSupportEquiv P) k
  rw [show (symThreePrimitiveWords P n word).1.1 =
      positiveWordMap (fun source : CyclicTriple P.support ↦ source.1.1) n tripleWord by rfl,
    positiveWordEquiv_map, WordType.multiplicity_comp_eq_mappedType, htriple,
    PositiveIntegralProfile.mappedType_proportionalCounts_cyclicProduct_fst_fst]

/-- An exact cyclic product type projects to the exact scaled primitive type in the second
orientation. -/
theorem multiplicity_symThreePrimitiveWords_fst_snd
    (P : PartitionedTensor (K := K) (A := A) V)
    (profile : PositiveIntegralProfile P.support) (n k : ℕ)
    (word : PositiveWord P.symThreePartition.support n)
    (htype : WordType.multiplicity
        (positiveWordEquiv P.symThreePartition.support n word) =
      WordType.proportionalCounts (symThreeSupportProfile P profile).count k) :
    WordType.multiplicity
        (positiveWordEquiv P.support n (symThreePrimitiveWords P n word).1.2) =
      WordType.proportionalCounts profile.count (profile.mass ^ 2 * k) := by
  let tripleWord := positiveWordMap (symThreeSupportEquiv P).symm n word
  have htriple : WordType.multiplicity
      (positiveWordEquiv (CyclicTriple P.support) n tripleWord) =
      WordType.proportionalCounts profile.cyclicProduct.count k := by
    rw [positiveWordEquiv_map, WordType.multiplicity_comp_eq_mappedType, htype]
    exact PositiveIntegralProfile.mappedType_proportionalCounts_symm_reindex
      profile.cyclicProduct (symThreeSupportEquiv P) k
  rw [show (symThreePrimitiveWords P n word).1.2 =
      positiveWordMap (fun source : CyclicTriple P.support ↦ source.1.2) n tripleWord by rfl,
    positiveWordEquiv_map, WordType.multiplicity_comp_eq_mappedType, htriple,
    PositiveIntegralProfile.mappedType_proportionalCounts_cyclicProduct_fst_snd]

/-- An exact cyclic product type projects to the exact scaled primitive type in the third
orientation. -/
theorem multiplicity_symThreePrimitiveWords_snd
    (P : PartitionedTensor (K := K) (A := A) V)
    (profile : PositiveIntegralProfile P.support) (n k : ℕ)
    (word : PositiveWord P.symThreePartition.support n)
    (htype : WordType.multiplicity
        (positiveWordEquiv P.symThreePartition.support n word) =
      WordType.proportionalCounts (symThreeSupportProfile P profile).count k) :
    WordType.multiplicity
        (positiveWordEquiv P.support n (symThreePrimitiveWords P n word).2) =
      WordType.proportionalCounts profile.count (profile.mass ^ 2 * k) := by
  let tripleWord := positiveWordMap (symThreeSupportEquiv P).symm n word
  have htriple : WordType.multiplicity
      (positiveWordEquiv (CyclicTriple P.support) n tripleWord) =
      WordType.proportionalCounts profile.cyclicProduct.count k := by
    rw [positiveWordEquiv_map, WordType.multiplicity_comp_eq_mappedType, htype]
    exact PositiveIntegralProfile.mappedType_proportionalCounts_symm_reindex
      profile.cyclicProduct (symThreeSupportEquiv P) k
  rw [show (symThreePrimitiveWords P n word).2 =
      positiveWordMap (fun source : CyclicTriple P.support ↦ source.2) n tripleWord by rfl,
    positiveWordEquiv_map, WordType.multiplicity_comp_eq_mappedType, htriple,
    PositiveIntegralProfile.mappedType_proportionalCounts_cyclicProduct_snd]

/-- Transposing the three primitive words decoded from a joint symmetric-support word recovers
the joint word's actual positive-power block address. -/
theorem positiveSupportWordBlockAddress_eq_symThreePrimitiveWords
    (P : PartitionedTensor (K := K) (A := A) V) (n : ℕ)
    (word : PositiveWord P.symThreePartition.support n) :
    positiveSupportWordBlockAddress P.symThreePartition.support n word =
      blockAddressCongr (symThreeWordEquiv (A := A) n)
        (symThreePositivePowerAddress P n
          (symThreePrimitiveWords P n word).1.1
          (symThreePrimitiveWords P n word).1.2
          (symThreePrimitiveWords P n word).2) := by
  funext c
  apply (positiveWordEquiv _ n).injective
  funext i
  rw [positiveWordEquiv_positiveSupportWordBlockAddress,
    blockAddressCongr_apply, positiveWordEquiv_symThreeWordEquiv]
  simp only [symThreePositivePowerAddress, blockAddressProductEquiv_apply_fst,
    blockAddressProductEquiv_apply_snd, permuteBlockAddress_apply]
  have hread (q : PositiveWord P.support n) (d : Leg) :
      positiveWordEquiv (A d) n
          (positiveSupportWordBlockAddress P.support n q d) i =
        (positiveWordEquiv P.support n q i).1 d :=
    congrFun (positiveWordEquiv_positiveSupportWordBlockAddress P.support n q d) i
  rw [hread, hread, hread]
  simp only [symThreePrimitiveWords, positiveWordEquiv_map, Function.comp_apply]
  change (positiveWordEquiv P.symThreePartition.support n word i).1 c = _
  let source := (symThreeSupportEquiv P).symm
    (positiveWordEquiv P.symThreePartition.support n word i)
  have hsource : symThreeSupportEquiv P source =
      positiveWordEquiv P.symThreePartition.support n word i :=
    (symThreeSupportEquiv P).apply_symm_apply _
  have hvalue := congrArg (fun s : P.symThreePartition.support ↦ s.1 c) hsource
  change (positiveWordEquiv P.symThreePartition.support n word i).1 c =
    symThreeSupportAddress P source c
  exact hvalue.symm

/-- The symmetric constituent attached to three same-type primitive words is the symmetric
constituent attached to any fourth reference word of that type. -/
theorem isomorphic_symThreePositivePower_constituent_of_reference_type
    (P : PartitionedTensor (K := K) (A := A) V) (n : ℕ)
    (q₀ q₁ q₂ reference : PositiveWord P.support n)
    (h₀ : WordType.multiplicity (positiveWordEquiv P.support n q₀) =
      WordType.multiplicity (positiveWordEquiv P.support n reference))
    (h₁ : WordType.multiplicity (positiveWordEquiv P.support n q₁) =
      WordType.multiplicity (positiveWordEquiv P.support n reference))
    (h₂ : WordType.multiplicity (positiveWordEquiv P.support n q₂) =
      WordType.multiplicity (positiveWordEquiv P.support n reference)) :
    Isomorphic
      (((P.symThreePartition).positivePower n).constituent
        (blockAddressCongr (symThreeWordEquiv (A := A) n)
          (symThreePositivePowerAddress P n q₀ q₁ q₂)))
      (symThree K
        ((P.positivePower n).constituent
          (positiveSupportWordBlockAddress P.support n reference))) := by
  have hbase := isomorphic_symThreePositivePower_constituent_of_same_type
    P n q₀ q₁ q₂ (h₁.trans h₀.symm) (h₂.trans h₀.symm)
  have href := Tensor.Isomorphic.positivePower_constituent_of_same_type P n q₀ reference h₀
  exact hbase.trans
    ((href.external (href.permute_legs cycle)).external
      (href.permute_legs cycle.symm))

end Tensor.PartitionedTensor

namespace Tensor.Restricts

/-- One joint cyclic hash extracts a uniform direct sum of symmetric copies of an arbitrary
reference child constituent.

The marked joint words have one exact cyclic-product type.  Its three projections therefore have
the exact type of `reference`; same-type relabeling identifies every selected constituent with
the same `symThree` child.  The index of the target direct sum is exactly the selected marked
address subtype, so no copy is lost after hashing.

This is a finite semantic theorem.  It assumes a pointwise description of the raw partition's
constituents, not a restriction to the assembled target. -/
theorem rawCyclicRow_to_symThreeChildDirectSum
    {P : PartitionedTensor (K := K) (A := A) V}
    (H : PartitionHashEncoding (R := R) P.symThreePartition.support)
    (n k : ℕ)
    (profile : PositiveIntegralProfile P.support)
    (reference : PositiveWord P.support n)
    (href : WordType.multiplicity (positiveWordEquiv P.support n reference) =
      WordType.proportionalCounts profile.count (profile.mass ^ 2 * k))
    (ambientWords markedWords : Finset (PositiveWord P.symThreePartition.support n))
    (hmarked : markedWords ⊆ ambientWords)
    (hmarkedType : ∀ word ∈ markedWords,
      WordType.multiplicity
          (positiveWordEquiv P.symThreePartition.support n word) =
        WordType.proportionalCounts (P.symThreeSupportProfile profile).count k)
    (Q : PartitionedTensor (K := K)
      (A := fun c ↦ PositiveWord
        (ProductBlockIndex (ProductBlockIndex A (PermutedBlockIndex cycle A))
          (PermutedBlockIndex cycle.symm A) c) n)
      (PositivePowerBlockSpace K
        (ProductBlockSpace K (ProductBlockSpace K V (PermutedBlockSpace cycle V))
          (PermutedBlockSpace cycle.symm V)) n))
    (hsupport : Q.support = H.modeledAddresses n (H.legalTargets n ambientWords))
    (hconstituentQ : ∀ address, Q.constituent address =
      ((P.symThreePartition).positivePower n).constituent address)
    [Fintype R] [NeZero (2 : R)]
    (B : Finset R) (hB : ThreeAPFree (B : Set R))
    (seed : ProgressionHash.Seed R (Fin (n + 1))) :
    Restricts Q.realize
      (Tensor.indexedDirectSum
        (fun _selected : H.markedLegwiseIsolatedPowerAddresses
          n ambientWords markedWords B seed ↦
          symThree K ((P.positivePower n).constituent
            (positiveSupportWordBlockAddress P.support n reference)))) := by
  classical
  let selected := H.markedLegwiseIsolatedPowerAddresses
    n ambientWords markedWords B seed
  have hseparate : Restricts Q.realize
      (Tensor.indexedDirectSum
        (V := SelectedBlockFamily
          (V := PositivePowerBlockSpace K
            (ProductBlockSpace K (ProductBlockSpace K V (PermutedBlockSpace cycle V))
              (PermutedBlockSpace cycle.symm V)) n) selected)
        (fun s : selected ↦ Q.constituent s.1)) := by
    exact Restricts.modeledTargets_to_markedLegwiseIsolatedIndexedDirectSum
      H ambientWords markedWords hmarked B hB seed Q hsupport
  apply hseparate.trans
  apply Restricts.indexedDirectSum
  intro address
  obtain ⟨word, hwordMarked, hwordAddress⟩ :=
    H.exists_markedSourceWord_of_mem_markedLegwiseIsolatedPowerAddresses
      n ambientWords markedWords B seed address.2
  have hwordType := hmarkedType word hwordMarked
  have htype₀ := PartitionedTensor.multiplicity_symThreePrimitiveWords_fst_fst
    P profile n k word hwordType
  have htype₁ := PartitionedTensor.multiplicity_symThreePrimitiveWords_fst_snd
    P profile n k word hwordType
  have htype₂ := PartitionedTensor.multiplicity_symThreePrimitiveWords_snd
    P profile n k word hwordType
  change Restricts (Q.constituent address.1)
    (symThree K ((P.positivePower n).constituent
      (positiveSupportWordBlockAddress P.support n reference)))
  rw [hconstituentQ, ← hwordAddress]
  change Restricts
    (((P.symThreePartition).positivePower n).constituent
      (positiveSupportWordBlockAddress P.symThreePartition.support n word))
    (symThree K ((P.positivePower n).constituent
      (positiveSupportWordBlockAddress P.support n reference)))
  rw [PartitionedTensor.positiveSupportWordBlockAddress_eq_symThreePrimitiveWords]
  exact (PartitionedTensor.isomorphic_symThreePositivePower_constituent_of_reference_type
    P n
      (P.symThreePrimitiveWords n word).1.1
      (P.symThreePrimitiveWords n word).1.2
      (P.symThreePrimitiveWords n word).2 reference
      (htype₀.trans href.symm) (htype₁.trans href.symm)
      (htype₂.trans href.symm)).restricts

end Tensor.Restricts

end AlgebraicComplexity
