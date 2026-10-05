/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinogradZeroDimensionCore
import AlgebraicComplexity.Examples.CoppersmithWinogradZeroInterface
import AlgebraicComplexity.MatrixMultiplication.PositiveWordProduct
import AlgebraicComplexity.Tensor.PartitionedPowerSupportDecodeCore

/-!
# Exact dimensions of zero-coordinate CW interfaces

If the `Z` block of a supported CW constituent is zero, the only possible base addresses are
`(2,0,0)`, `(0,2,0)`, and `(1,1,0)`.  Their matrix dimensions are respectively
`⟨1,1,1⟩`, `⟨1,1,1⟩`, and `⟨1,q,1⟩`.  Hence a supported chunk with zero `Z` block has
dimensions `⟨1,q^k,1⟩`, where `k` is the number of middle digits in its encoded `X` split word.

At an exact recursive interface, complete-split consistency fixes the sum of those middle-digit
counts across every retained outer word.  Thus the whole selected family has one common local
`q`-power.  All statements are exact finite equalities; no entropy or asymptotic estimate occurs
here.  The downstream module `CoppersmithWinogradZeroDimensionRestriction` uses these equalities
to construct explicit one-slice maps.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor MoreAsymmetryCompatibility
open scoped BigOperators

universe u

private theorem positivePowerProfile_counts_aux {depth : ℕ}
    (index : LevelConstituentIndex depth) (multiplicity n : ℕ)
    (split : ∀ c, CompleteSplitProfile depth (index.count c) multiplicity)
    (hmultiplicity : multiplicity = n + 1) (c : Leg) :
    ((ExactInterfaceTermParameters.mk multiplicity index split).positivePowerProfile
      hmultiplicity c).counts = (split c).counts := by
  subst hmultiplicity
  rfl

private theorem positivePowerProfile_counts
    {depth n : ℕ} (term : ExactInterfaceTermParameters depth)
    (hmultiplicity : term.multiplicity = n + 1) (c : Leg) :
    (term.positivePowerProfile hmultiplicity c).counts = (term.split c).counts :=
  positivePowerProfile_counts_aux term.index term.multiplicity n term.split hmultiplicity c

/-- Every chunk letter in a selected zero-Z outer address lies in the chunk zero-Z fiber. -/
theorem cwSelectedExactInterfaceSupportedWord_letter_z_eq_zero
    (K : Type u) [CommRing K] (q : ℕ) {depth n : ℕ}
    (term : ExactInterfaceTermParameters depth)
    (hmultiplicity : term.multiplicity = n + 1)
    (hz : term.index.count .Z = 0)
    (address : (cwSelectedExactInterfaceTerm K q term hmultiplicity).support)
    (position : Fin (n + 1)) :
    (positiveWordEquiv (cwChunkPartitionedTensor K q depth).support n
      (cwSelectedExactInterfaceSupportedWord K q term hmultiplicity address) position).1 .Z =
        cwZeroChunkWord depth := by
  let outerWord := cwSelectedExactInterfaceSupportedWord K q term hmultiplicity address
  have haddress := positiveSupportWordBlockAddress_cwSelectedExactInterfaceSupportedWord
    K q term hmultiplicity address
  have hshared :=
    (cwSelectedExactInterfaceTerm_zeroZ_support_isSharedFiber
      K q term hmultiplicity hz).1 address.1 address.2
  have hzWords :
      positiveSupportWordBlockAddress (cwChunkPartitionedTensor K q depth).support n
          outerWord .Z = positiveWordConst (cwZeroChunkWord depth) n := by
    rw [haddress]
    exact hshared
  have hzFunctions := congrArg
    (positiveWordEquiv (PositiveWord CWBlock (2 ^ depth - 1)) n) hzWords
  have hzPosition := congrFun hzFunctions position
  calc
    (positiveWordEquiv (cwChunkPartitionedTensor K q depth).support n outerWord position).1 .Z =
        positiveWordEquiv (PositiveWord CWBlock (2 ^ depth - 1)) n
          (positiveSupportWordBlockAddress
            (cwChunkPartitionedTensor K q depth).support n outerWord .Z) position :=
      (congrFun (positiveWordEquiv_positiveSupportWordBlockAddress_recursive
        (cwChunkPartitionedTensor K q depth).support n outerWord .Z) position).symm
    _ = positiveWordEquiv (PositiveWord CWBlock (2 ^ depth - 1)) n
        (positiveWordConst (cwZeroChunkWord depth) n) position := hzPosition
    _ = cwZeroChunkWord depth := by simp only [positiveWordEquiv_const]

/-- The encoded X chunk sequence of the recovered supported outer word realizes the exact stored
X profile. -/
theorem cwSelectedExactInterfaceSupportedWord_x_isConsistent
    (K : Type u) [CommRing K] (q : ℕ) {depth n : ℕ}
    (term : ExactInterfaceTermParameters depth)
    (hmultiplicity : term.multiplicity = n + 1)
    (address : (cwSelectedExactInterfaceTerm K q term hmultiplicity).support) :
    (term.positivePowerProfile hmultiplicity .X).IsConsistent
      (fun position ↦ cwChunkSplitWord depth
        ((positiveWordEquiv (cwChunkPartitionedTensor K q depth).support n
          (cwSelectedExactInterfaceSupportedWord K q term hmultiplicity address)
            position).1 .X)) := by
  have hselected := address.2
  change address.1 ∈
    ((cwChunkPartitionedTensor K q depth).selectEncodedCompleteSplitProfiles
      (fun _c ↦ cwChunkSplitWord depth) term.index
      (fun c ↦ term.positivePowerProfile hmultiplicity c)).support at hselected
  have hconsistent :=
    ((cwChunkPartitionedTensor K q depth).mem_selectEncodedCompleteSplitProfiles_support
      (fun _c ↦ cwChunkSplitWord depth) term.index
      (fun c ↦ term.positivePowerProfile hmultiplicity c) address.1).mp hselected |>.2 .X
  have haddress := positiveSupportWordBlockAddress_cwSelectedExactInterfaceSupportedWord
    K q term hmultiplicity address
  have hxWords := congrArg
    (positiveWordEquiv (PositiveWord CWBlock (2 ^ depth - 1)) n)
    (congrFun haddress .X)
  unfold CompleteSplitProfile.IsConsistent at hconsistent ⊢
  have hsequence :
      (fun position ↦ cwChunkSplitWord depth
        ((positiveWordEquiv (cwChunkPartitionedTensor K q depth).support n
          (cwSelectedExactInterfaceSupportedWord K q term hmultiplicity address)
            position).1 .X)) =
        (cwChunkSplitWord depth ∘ positiveWordEquiv
          (PositiveWord CWBlock (2 ^ depth - 1)) n (address.1 .X)) := by
    funext position
    rw [Function.comp_apply]
    congr 1
    have hxPosition := congrFun hxWords position
    calc
      (positiveWordEquiv (cwChunkPartitionedTensor K q depth).support n
          (cwSelectedExactInterfaceSupportedWord K q term hmultiplicity address) position).1 .X =
          positiveWordEquiv (PositiveWord CWBlock (2 ^ depth - 1)) n
            (positiveSupportWordBlockAddress
              (cwChunkPartitionedTensor K q depth).support n
              (cwSelectedExactInterfaceSupportedWord K q term hmultiplicity address) .X)
              position :=
        (congrFun (positiveWordEquiv_positiveSupportWordBlockAddress_recursive
          (cwChunkPartitionedTensor K q depth).support n
          (cwSelectedExactInterfaceSupportedWord K q term hmultiplicity address) .X)
          position).symm
      _ = positiveWordEquiv (PositiveWord CWBlock (2 ^ depth - 1)) n
          (address.1 .X) position := hxPosition
  rw [hsequence]
  exact hconsistent

/-- Exact complete-split consistency fixes the total middle-digit count of every selected
zero-Z outer constituent. -/
theorem cwSelectedExactInterfaceSupportedWord_sum_middleCount
    (K : Type u) [CommRing K] (q : ℕ) {depth n : ℕ}
    (term : ExactInterfaceTermParameters depth)
    (hmultiplicity : term.multiplicity = n + 1)
    (address : (cwSelectedExactInterfaceTerm K q term hmultiplicity).support) :
    ∑ position, splitWordMiddleCount
        (cwChunkSplitWord depth
          ((positiveWordEquiv (cwChunkPartitionedTensor K q depth).support n
            (cwSelectedExactInterfaceSupportedWord K q term hmultiplicity address)
              position).1 .X)) =
      cwZeroInterfaceQExponent term := by
  have h := (term.positivePowerProfile hmultiplicity .X).sum_middleCount_of_isConsistent
    _ (cwSelectedExactInterfaceSupportedWord_x_isConsistent
      K q term hmultiplicity address)
  simpa only [positivePowerProfile_counts, cwZeroInterfaceQExponent] using h

/-- **Uniform zero-interface dimension law.**  Every retained constituent of an exact zero-Z
CW interface has dimensions `⟨1,q^e,1⟩`, where `e` depends only on the stored complete-split
profile and not on the selected address. -/
theorem cwSelectedExactInterfaceConstituentDimension_zeroZ
    (K : Type u) [CommRing K] (q : ℕ) {depth n : ℕ}
    (term : ExactInterfaceTermParameters depth)
    (hmultiplicity : term.multiplicity = n + 1)
    (hz : term.index.count .Z = 0)
    (address : (cwSelectedExactInterfaceTerm K q term hmultiplicity).support) :
    cwSelectedExactInterfaceConstituentDimension K q term hmultiplicity address .X = 1 ∧
      cwSelectedExactInterfaceConstituentDimension K q term hmultiplicity address .Y =
        q ^ cwZeroInterfaceQExponent term ∧
      cwSelectedExactInterfaceConstituentDimension K q term hmultiplicity address .Z = 1 := by
  let outerWord := cwSelectedExactInterfaceSupportedWord K q term hmultiplicity address
  have hchunk (position : Fin (n + 1)) := cwChunkConstituentDimension_zeroZ
    K q depth
    (positiveWordEquiv (cwChunkPartitionedTensor K q depth).support n outerWord position)
    (cwSelectedExactInterfaceSupportedWord_letter_z_eq_zero
      K q term hmultiplicity hz address position)
  refine ⟨?_, ?_, ?_⟩
  · unfold cwSelectedExactInterfaceConstituentDimension
    rw [positiveWordProduct_eq_fin_prod]
    apply Finset.prod_eq_one
    intro position _
    exact (hchunk position).1
  · unfold cwSelectedExactInterfaceConstituentDimension
    rw [positiveWordProduct_eq_fin_prod]
    calc
      (∏ position,
          cwChunkConstituentDimension K q depth
            (positiveWordEquiv (cwChunkPartitionedTensor K q depth).support n
              outerWord position) .Y) =
          ∏ position, q ^ splitWordMiddleCount
            (cwChunkSplitWord depth
              ((positiveWordEquiv (cwChunkPartitionedTensor K q depth).support n
                outerWord position).1 .X)) := by
        apply Finset.prod_congr rfl
        intro position _
        exact (hchunk position).2.1
      _ = q ^ cwZeroInterfaceQExponent term := by
        rw [Finset.prod_pow_eq_pow_sum,
          cwSelectedExactInterfaceSupportedWord_sum_middleCount
            K q term hmultiplicity address]
  · unfold cwSelectedExactInterfaceConstituentDimension
    rw [positiveWordProduct_eq_fin_prod]
    apply Finset.prod_eq_one
    intro position _
    exact (hchunk position).2.2

end AlgebraicComplexity.Examples
