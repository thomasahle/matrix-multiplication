/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinogradZeroInterface
import AlgebraicComplexity.MatrixMultiplication.ZeroCoordinateTypeClass

/-!
# Exact type-class count for zero-coordinate CW interfaces

This file supplies the concrete per-letter completeness certificate required by the generic
zero-coordinate counting theorem.  A ternary split digit `0`, `1`, or `2` is lifted to the unique
base CW support address with `Z = 0`; lifting is then performed independently at every position
inside a recursive chunk.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor MoreAsymmetryCompatibility

universe u

/-- The native CW block whose split digit is the supplied ternary digit. -/
def cwBlockOfSplitDigit (digit : SplitDigit) : CWBlock :=
  if digit = 0 then .zero else if digit = 1 then .middle else .last

@[simp] theorem cwBlockOfSplitDigit_zero : cwBlockOfSplitDigit 0 = .zero := by
  simp [cwBlockOfSplitDigit]
@[simp] theorem cwBlockOfSplitDigit_one : cwBlockOfSplitDigit 1 = .middle := by
  simp [cwBlockOfSplitDigit]
@[simp] theorem cwBlockOfSplitDigit_two : cwBlockOfSplitDigit 2 = .last := by
  simp [cwBlockOfSplitDigit]

@[simp] theorem cwBlockDigit_cwBlockOfSplitDigit (digit : SplitDigit) :
    cwBlockDigit (cwBlockOfSplitDigit digit) = digit := by
  fin_cases digit <;> simp [cwBlockOfSplitDigit]

/-- The unique supported base CW address with prescribed `X` digit and zero `Z` digit. -/
def cwZeroBaseAddressOfSplitDigit (digit : SplitDigit) : CWBlockAddress :=
  cwBlockAddress (cwBlockOfSplitDigit digit)
    (cwBlockOfSplitDigit (Fin.rev digit)) .zero

theorem cwZeroBaseAddressOfSplitDigit_mem (digit : SplitDigit) :
    cwZeroBaseAddressOfSplitDigit digit ∈ cwBlockSupport := by
  fin_cases digit <;>
    simp [cwZeroBaseAddressOfSplitDigit, cwBlockOfSplitDigit, cwBlockSupport,
      cwBlockAddress, cw020, cw110, cw200]

/-- Supported base letter associated to one split digit on the zero-`Z` fibre. -/
def cwZeroBaseSupportOfSplitDigit (digit : SplitDigit) : cwBlockSupport :=
  ⟨cwZeroBaseAddressOfSplitDigit digit, cwZeroBaseAddressOfSplitDigit_mem digit⟩

@[simp] theorem cwZeroBaseSupportOfSplitDigit_x (digit : SplitDigit) :
    cwBlockDigit ((cwZeroBaseSupportOfSplitDigit digit).1 .X) = digit := by
  simp [cwZeroBaseSupportOfSplitDigit, cwZeroBaseAddressOfSplitDigit]

@[simp] theorem cwZeroBaseSupportOfSplitDigit_y (digit : SplitDigit) :
    cwBlockDigit ((cwZeroBaseSupportOfSplitDigit digit).1 .Y) = Fin.rev digit := by
  simp [cwZeroBaseSupportOfSplitDigit, cwZeroBaseAddressOfSplitDigit]

@[simp] theorem cwZeroBaseSupportOfSplitDigit_z (digit : SplitDigit) :
    cwBlockDigit ((cwZeroBaseSupportOfSplitDigit digit).1 .Z) = 0 := by
  rfl

/-- Lift a complete-split word positionwise to the zero-`Z` part of the base CW support. -/
noncomputable def cwZeroChunkSourceWord (depth : ℕ) (word : SplitWord depth) :
    PositiveWord cwBlockSupport (2 ^ depth - 1) :=
  (positiveWordEquiv cwBlockSupport (2 ^ depth - 1)).symm fun position ↦
    cwZeroBaseSupportOfSplitDigit (word (cwChunkPositionEquiv depth position))

/-- The resulting supported block address in the depth-`depth` CW chunk partition. -/
noncomputable def cwZeroChunkSupportOfSplitWord
    (K : Type u) [CommRing K] (q depth : ℕ) (word : SplitWord depth) :
    (cwChunkPartitionedTensor K q depth).support := by
  let source := cwZeroChunkSourceWord depth word
  refine ⟨positiveSupportWordBlockAddress cwBlockSupport (2 ^ depth - 1) source, ?_⟩
  change positiveSupportWordBlockAddress cwBlockSupport (2 ^ depth - 1) source ∈
    ((cwPartitionedTensor K q).positivePower (2 ^ depth - 1)).support
  exact (cwPartitionedTensor K q
    ).positiveSupportWordBlockAddress_mem_positivePower_support_recursive
      (2 ^ depth - 1) source

@[simp] theorem cwChunkSplitWord_zeroChunkSupport_x
    (K : Type u) [CommRing K] (q depth : ℕ) (word : SplitWord depth) :
    cwChunkSplitWord depth ((cwZeroChunkSupportOfSplitWord K q depth word).1 .X) = word := by
  funext position
  unfold cwChunkSplitWord cwZeroChunkSupportOfSplitWord
  rw [congrFun
    (positiveWordEquiv_positiveSupportWordBlockAddress_recursive
      cwBlockSupport (2 ^ depth - 1) (cwZeroChunkSourceWord depth word) .X)
    ((cwChunkPositionEquiv depth).symm position)]
  change cwBlockDigit
      ((positiveWordEquiv cwBlockSupport (2 ^ depth - 1)
        ((positiveWordEquiv cwBlockSupport (2 ^ depth - 1)).symm
          (fun sourcePosition ↦
            cwZeroBaseSupportOfSplitDigit
              (word (cwChunkPositionEquiv depth sourcePosition))))
        ((cwChunkPositionEquiv depth).symm position)).1 .X) = _
  rw [Equiv.apply_symm_apply]
  simp

@[simp] theorem cwChunkSplitWord_zeroChunkSupport_y
    (K : Type u) [CommRing K] (q depth : ℕ) (word : SplitWord depth) :
    cwChunkSplitWord depth ((cwZeroChunkSupportOfSplitWord K q depth word).1 .Y) =
      complementSplitWord word := by
  funext position
  unfold cwChunkSplitWord cwZeroChunkSupportOfSplitWord
  rw [congrFun
    (positiveWordEquiv_positiveSupportWordBlockAddress_recursive
      cwBlockSupport (2 ^ depth - 1) (cwZeroChunkSourceWord depth word) .Y)
    ((cwChunkPositionEquiv depth).symm position)]
  change cwBlockDigit
      ((positiveWordEquiv cwBlockSupport (2 ^ depth - 1)
        ((positiveWordEquiv cwBlockSupport (2 ^ depth - 1)).symm
          (fun sourcePosition ↦
            cwZeroBaseSupportOfSplitDigit
              (word (cwChunkPositionEquiv depth sourcePosition))))
        ((cwChunkPositionEquiv depth).symm position)).1 .Y) = _
  rw [Equiv.apply_symm_apply]
  simp [complementSplitWord]

@[simp] theorem cwChunkSplitWord_zeroChunkSupport_z
    (K : Type u) [CommRing K] (q depth : ℕ) (word : SplitWord depth) :
    cwChunkSplitWord depth ((cwZeroChunkSupportOfSplitWord K q depth word).1 .Z) = 0 := by
  funext position
  unfold cwChunkSplitWord cwZeroChunkSupportOfSplitWord
  rw [congrFun
    (positiveWordEquiv_positiveSupportWordBlockAddress_recursive
      cwBlockSupport (2 ^ depth - 1) (cwZeroChunkSourceWord depth word) .Z)
    ((cwChunkPositionEquiv depth).symm position)]
  change cwBlockDigit
      ((positiveWordEquiv cwBlockSupport (2 ^ depth - 1)
        ((positiveWordEquiv cwBlockSupport (2 ^ depth - 1)).symm
          (fun sourcePosition ↦
            cwZeroBaseSupportOfSplitDigit
              (word (cwChunkPositionEquiv depth sourcePosition))))
        ((cwChunkPositionEquiv depth).symm position)).1 .Z) = _
  rw [Equiv.apply_symm_apply]
  rfl

/-- Concrete complete-fibre certificate for the zero-`Z` part of a recursive CW chunk. -/
noncomputable def cwZeroCoordinateCompleteFiberData
    (K : Type u) [CommRing K] (q depth : ℕ) :
    ZeroCoordinateCompleteFiberData
      (cwChunkPartitionedTensor K q depth)
      (fun _c ↦ cwChunkSplitWord depth) where
  lift := cwZeroChunkSupportOfSplitWord K q depth
  encode_x := cwChunkSplitWord_zeroChunkSupport_x K q depth
  encode_y := cwChunkSplitWord_zeroChunkSupport_y K q depth
  encode_z := cwChunkSplitWord_zeroChunkSupport_z K q depth

/-- Every exact zero-`Z` CW interface with complementary `X/Y` profiles has exactly the
multinomial type-class number of supported addresses. -/
theorem card_cwSelectedExactInterfaceTerm_zeroZ_eq_card_typeClass
    (K : Type u) [CommRing K] (q : ℕ) {depth n : ℕ}
    (term : ExactInterfaceTermParameters depth)
    (hmultiplicity : term.multiplicity = n + 1)
    (hz : term.index.count .Z = 0)
    (hcomplement : ∀ word,
      (term.positivePowerProfile hmultiplicity .Y).counts word =
        (term.positivePowerProfile hmultiplicity .X).counts
          (complementSplitWord word)) :
    (cwSelectedExactInterfaceTerm K q term hmultiplicity).support.card =
      (term.positivePowerProfile hmultiplicity .X).typeClass.card := by
  change
    ((cwChunkPartitionedTensor K q depth).selectEncodedCompleteSplitProfiles
      (fun _c ↦ cwChunkSplitWord depth) term.index
      (fun c ↦ term.positivePowerProfile hmultiplicity c)).support.card = _
  exact card_selectEncodedCompleteSplitProfiles_zero_eq_card_typeClass
      (P := cwChunkPartitionedTensor K q depth)
      (encode := fun _c ↦ cwChunkSplitWord depth)
      (hencodeX := cwChunkSplitWord_injective depth)
      (D := cwZeroCoordinateCompleteFiberData K q depth)
      (index := term.index)
      (profile := fun c ↦ term.positivePowerProfile hmultiplicity c)
      hz hcomplement
      (by
        simpa [cwSelectedExactInterfaceTerm,
          Tensor.PartitionedTensor.selectEncodedExactInterfaceTerm] using
          (cwSelectedExactInterfaceTerm_zeroZ_support_isSharedFiber
            K q term hmultiplicity hz).2.1)

end AlgebraicComplexity.Examples
