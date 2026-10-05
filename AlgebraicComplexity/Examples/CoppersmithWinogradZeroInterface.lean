/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinogradZeroWord
import AlgebraicComplexity.MatrixMultiplication.ZeroCoordinateInterface

/-!
# Exact zero-coordinate Coppersmith--Winograd interfaces

An exact recursive CW interface term whose `Z` coordinate is zero has considerably more
structure than an arbitrary selected constituent.  Its selected support has one common native
`Z` block word, while either the `X` or the `Y` block word determines the whole address.  This is
the combinatorial core of the zero/easy constituent extraction: the entire selected type class is
a shared-`Z` C-tensor family, rather than a collection from which one representative must be
chosen.

The proofs use only exact profile consistency and coordinatewise legality.  In particular, they
do not assume full support of a probability law, a hashing theorem, or a tensor degeneration.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor MoreAsymmetryCompatibility

universe u

/-- Fine legality of the native depth-`depth` CW chunk support, kept local to the lightweight
zero-interface import cone. -/
private theorem cwZeroInterface_isEncodedFineLegalOnSupport
    (K : Type u) [CommRing K] (q depth : ℕ) :
    IsEncodedFineLegalOnSupport (cwChunkPartitionedTensor K q depth).support
      (fun _c ↦ cwChunkSplitWord depth) := by
  intro address haddress position
  change address ∈
    ((cwPartitionedTensor K q).positivePower (2 ^ depth - 1)).support at haddress
  obtain ⟨source, hsource⟩ :=
    (cwPartitionedTensor K q).exists_positiveSupportWord_of_mem_positivePower_support
      (2 ^ depth - 1) haddress
  rw [← hsource]
  let sample : Fin (2 ^ depth - 1 + 1) := (cwChunkPositionEquiv depth).symm position
  change
    (cwBlockDigit
          (positiveWordEquiv CWBlock (2 ^ depth - 1)
            (positiveSupportWordBlockAddress (cwPartitionedTensor K q).support
              (2 ^ depth - 1) source .X) sample) : ℕ) +
        (cwBlockDigit
          (positiveWordEquiv CWBlock (2 ^ depth - 1)
            (positiveSupportWordBlockAddress (cwPartitionedTensor K q).support
              (2 ^ depth - 1) source .Y) sample) : ℕ) +
        (cwBlockDigit
          (positiveWordEquiv CWBlock (2 ^ depth - 1)
            (positiveSupportWordBlockAddress (cwPartitionedTensor K q).support
              (2 ^ depth - 1) source .Z) sample) : ℕ) = 2
  rw [congrFun
      (positiveWordEquiv_positiveSupportWordBlockAddress
        (cwPartitionedTensor K q).support (2 ^ depth - 1) source .X) sample,
    congrFun
      (positiveWordEquiv_positiveSupportWordBlockAddress
        (cwPartitionedTensor K q).support (2 ^ depth - 1) source .Y) sample,
    congrFun
      (positiveWordEquiv_positiveSupportWordBlockAddress
        (cwPartitionedTensor K q).support (2 ^ depth - 1) source .Z) sample]
  have hsupported := (positiveWordEquiv (cwPartitionedTensor K q).support
    (2 ^ depth - 1) source sample).2
  change
    (cwBlockDigit
          ((positiveWordEquiv (cwPartitionedTensor K q).support
            (2 ^ depth - 1) source sample).1 .X) : ℕ) +
        (cwBlockDigit
          ((positiveWordEquiv (cwPartitionedTensor K q).support
            (2 ^ depth - 1) source sample).1 .Y) : ℕ) +
        (cwBlockDigit
          ((positiveWordEquiv (cwPartitionedTensor K q).support
            (2 ^ depth - 1) source sample).1 .Z) : ℕ) = 2
  change
    (positiveWordEquiv (cwPartitionedTensor K q).support
      (2 ^ depth - 1) source sample).1 ∈ cwBlockSupport at hsupported
  simpa [sum_leg] using cwBlockSupport_digit_sum
    (positiveWordEquiv (cwPartitionedTensor K q).support
      (2 ^ depth - 1) source sample).1 hsupported

/-- **Shared-leg C-tensor support law.**  On a zero-`Z` exact CW interface term, the `Z` block is
constant and either side block is injective on the entire selected support.  No representative
selection occurs. -/
theorem cwSelectedExactInterfaceTerm_zeroZ_support_isSharedFiber
    (K : Type u) [CommRing K] (q : ℕ) {depth n : ℕ}
    (term : ExactInterfaceTermParameters depth)
    (hmultiplicity : term.multiplicity = n + 1)
    (hz : term.index.count .Z = 0) :
    (∀ address ∈ (cwSelectedExactInterfaceTerm K q term hmultiplicity).support,
        address .Z = cwZeroInterfaceLegWord depth n) ∧
      Set.InjOn (fun address ↦ address .X)
        ((cwSelectedExactInterfaceTerm K q term hmultiplicity).support :
          Set (BlockAddress fun _c ↦ PositiveWord (PositiveWord CWBlock (2 ^ depth - 1)) n)) ∧
      Set.InjOn (fun address ↦ address .Y)
        ((cwSelectedExactInterfaceTerm K q term hmultiplicity).support :
          Set (BlockAddress fun _c ↦ PositiveWord (PositiveWord CWBlock (2 ^ depth - 1)) n)) := by
  simpa [cwSelectedExactInterfaceTerm, cwZeroInterfaceLegWord] using
    (selectedExactInterfaceTerm_zeroZ_support_isSharedFiber
      (P := cwChunkPartitionedTensor K q depth)
      (encode := fun _c ↦ cwChunkSplitWord depth)
      (hencode := fun _c ↦ cwChunkSplitWord_injective depth)
      (hlegalSupport := cwZeroInterface_isEncodedFineLegalOnSupport K q depth)
      (term := term) (hmultiplicity := hmultiplicity) (hz := hz)
      (zeroZ := cwZeroChunkWord depth)
      (hzeroZ := cwChunkSplitWord_zeroChunkWord depth))

end AlgebraicComplexity.Examples
