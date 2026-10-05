/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinogradZeroOrientation
import AlgebraicComplexity.Examples.CoppersmithWinogradZeroTypeClass
import AlgebraicComplexity.MatrixMultiplication.ZeroCoordinateOrientedTypeClass

set_option autoImplicit false

/-!
# Exact CW zero-coordinate type classes in every orientation

For each zero leg and split digit, this file constructs the unique native CW support address whose
first live digit is the prescribed digit and whose second live digit is its complement.  The
construction is iterated over a recursive chunk and instantiates the generic oriented type-class
equivalence.  Thus all three zero orientations have the same exact finite count; no relabelled
support, representative choice, or cardinality hypothesis is introduced.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor MoreAsymmetryCompatibility

universe u

/-- The supported base CW address with zero at `zero`, digit `digit` at the first live leg, and
the complementary digit at the second live leg. -/
def cwZeroBaseAddressOfSplitDigitOn (zero : Leg) (digit : SplitDigit) : CWBlockAddress :=
  match zero with
  | .X => cwBlockAddress .zero (cwBlockOfSplitDigit digit)
      (cwBlockOfSplitDigit (Fin.rev digit))
  | .Y => cwBlockAddress (cwBlockOfSplitDigit (Fin.rev digit)) .zero
      (cwBlockOfSplitDigit digit)
  | .Z => cwZeroBaseAddressOfSplitDigit digit

theorem cwZeroBaseAddressOfSplitDigitOn_mem (zero : Leg) (digit : SplitDigit) :
    cwZeroBaseAddressOfSplitDigitOn zero digit ∈ cwBlockSupport := by
  cases zero <;> fin_cases digit <;>
    simp [cwZeroBaseAddressOfSplitDigitOn, cwZeroBaseAddressOfSplitDigit,
      cwBlockOfSplitDigit, cwBlockSupport, cwBlockAddress,
      cw200, cw020, cw002, cw011, cw101, cw110]

/-- Supported base letter in the oriented zero fibre. -/
def cwZeroBaseSupportOfSplitDigitOn (zero : Leg) (digit : SplitDigit) : cwBlockSupport :=
  ⟨cwZeroBaseAddressOfSplitDigitOn zero digit,
    cwZeroBaseAddressOfSplitDigitOn_mem zero digit⟩

@[simp] theorem cwZeroBaseSupportOfSplitDigitOn_first (zero : Leg) (digit : SplitDigit) :
    cwBlockDigit
      ((cwZeroBaseSupportOfSplitDigitOn zero digit).1 (firstLiveLeg zero)) = digit := by
  cases zero <;> simp [cwZeroBaseSupportOfSplitDigitOn,
    cwZeroBaseAddressOfSplitDigitOn, cwZeroBaseAddressOfSplitDigit]

@[simp] theorem cwZeroBaseSupportOfSplitDigitOn_second (zero : Leg) (digit : SplitDigit) :
    cwBlockDigit
      ((cwZeroBaseSupportOfSplitDigitOn zero digit).1 (secondLiveLeg zero)) = Fin.rev digit := by
  cases zero <;> simp [cwZeroBaseSupportOfSplitDigitOn,
    cwZeroBaseAddressOfSplitDigitOn, cwZeroBaseAddressOfSplitDigit]

@[simp] theorem cwZeroBaseSupportOfSplitDigitOn_zero (zero : Leg) (digit : SplitDigit) :
    cwBlockDigit ((cwZeroBaseSupportOfSplitDigitOn zero digit).1 zero) = 0 := by
  cases zero <;> simp [cwZeroBaseSupportOfSplitDigitOn,
    cwZeroBaseAddressOfSplitDigitOn, cwZeroBaseAddressOfSplitDigit]

/-- Lift a complete-split word positionwise through the oriented zero fibre. -/
noncomputable def cwZeroChunkSourceWordOn
    (zero : Leg) (depth : ℕ) (word : SplitWord depth) :
    PositiveWord cwBlockSupport (2 ^ depth - 1) :=
  (positiveWordEquiv cwBlockSupport (2 ^ depth - 1)).symm fun position ↦
    cwZeroBaseSupportOfSplitDigitOn zero (word (cwChunkPositionEquiv depth position))

/-- The resulting supported recursive CW chunk address. -/
noncomputable def cwZeroChunkSupportOfSplitWordOn
    (K : Type u) [CommRing K] (q : ℕ) (zero : Leg) (depth : ℕ)
    (word : SplitWord depth) : (cwChunkPartitionedTensor K q depth).support := by
  let source := cwZeroChunkSourceWordOn zero depth word
  refine ⟨positiveSupportWordBlockAddress cwBlockSupport (2 ^ depth - 1) source, ?_⟩
  change positiveSupportWordBlockAddress cwBlockSupport (2 ^ depth - 1) source ∈
    ((cwPartitionedTensor K q).positivePower (2 ^ depth - 1)).support
  exact (cwPartitionedTensor K q
    ).positiveSupportWordBlockAddress_mem_positivePower_support_recursive
      (2 ^ depth - 1) source

private theorem cwChunkSplitWord_zeroChunkSupportOfSplitWordOn_eq
    (K : Type u) [CommRing K] (q : ℕ) (zero c : Leg) (depth : ℕ)
    (target : SplitDigit → SplitDigit)
    (htarget : ∀ digit,
      cwBlockDigit ((cwZeroBaseSupportOfSplitDigitOn zero digit).1 c) = target digit)
    (word : SplitWord depth) :
    cwChunkSplitWord depth
        ((cwZeroChunkSupportOfSplitWordOn K q zero depth word).1 c) =
      target ∘ word := by
  funext position
  unfold cwChunkSplitWord cwZeroChunkSupportOfSplitWordOn
  rw [congrFun
    (positiveWordEquiv_positiveSupportWordBlockAddress_recursive
      cwBlockSupport (2 ^ depth - 1) (cwZeroChunkSourceWordOn zero depth word) c)
    ((cwChunkPositionEquiv depth).symm position)]
  change cwBlockDigit
      ((positiveWordEquiv cwBlockSupport (2 ^ depth - 1)
        ((positiveWordEquiv cwBlockSupport (2 ^ depth - 1)).symm
          (fun sourcePosition ↦ cwZeroBaseSupportOfSplitDigitOn zero
            (word (cwChunkPositionEquiv depth sourcePosition))))
        ((cwChunkPositionEquiv depth).symm position)).1 c) = _
  rw [Equiv.apply_symm_apply]
  exact htarget (word position)

@[simp] theorem cwChunkSplitWord_zeroChunkSupportOn_first
    (K : Type u) [CommRing K] (q : ℕ) (zero : Leg) (depth : ℕ)
    (word : SplitWord depth) :
    cwChunkSplitWord depth
        ((cwZeroChunkSupportOfSplitWordOn K q zero depth word).1 (firstLiveLeg zero)) = word := by
  simpa using cwChunkSplitWord_zeroChunkSupportOfSplitWordOn_eq
    K q zero (firstLiveLeg zero) depth id
    (cwZeroBaseSupportOfSplitDigitOn_first zero) word

@[simp] theorem cwChunkSplitWord_zeroChunkSupportOn_second
    (K : Type u) [CommRing K] (q : ℕ) (zero : Leg) (depth : ℕ)
    (word : SplitWord depth) :
    cwChunkSplitWord depth
        ((cwZeroChunkSupportOfSplitWordOn K q zero depth word).1 (secondLiveLeg zero)) =
      complementSplitWord word := by
  calc
    _ = Fin.rev ∘ word := cwChunkSplitWord_zeroChunkSupportOfSplitWordOn_eq
      K q zero (secondLiveLeg zero) depth Fin.rev
      (cwZeroBaseSupportOfSplitDigitOn_second zero) word
    _ = complementSplitWord word := by rfl

@[simp] theorem cwChunkSplitWord_zeroChunkSupportOn_zero
    (K : Type u) [CommRing K] (q : ℕ) (zero : Leg) (depth : ℕ)
    (word : SplitWord depth) :
    cwChunkSplitWord depth
        ((cwZeroChunkSupportOfSplitWordOn K q zero depth word).1 zero) = 0 := by
  calc
    _ = (fun _digit ↦ 0) ∘ word :=
      cwChunkSplitWord_zeroChunkSupportOfSplitWordOn_eq
        K q zero zero depth (fun _digit ↦ 0)
        (cwZeroBaseSupportOfSplitDigitOn_zero zero) word
    _ = 0 := by rfl

/-- Concrete complete-fibre data for all three zero orientations of a recursive CW chunk. -/
noncomputable def cwOrientedZeroCoordinateCompleteFiberData
    (K : Type u) [CommRing K] (q : ℕ) (zero : Leg) (depth : ℕ) :
    OrientedZeroCoordinateCompleteFiberData
      (cwChunkPartitionedTensor K q depth) (fun _c ↦ cwChunkSplitWord depth) zero where
  lift := cwZeroChunkSupportOfSplitWordOn K q zero depth
  encode_first := cwChunkSplitWord_zeroChunkSupportOn_first K q zero depth
  encode_second := cwChunkSplitWord_zeroChunkSupportOn_second K q zero depth
  encode_zero := cwChunkSplitWord_zeroChunkSupportOn_zero K q zero depth

/-- **Exact selected-support count for every zero-coordinate CW orientation.** -/
theorem card_cwSelectedExactInterfaceTerm_zero_eq_card_typeClass
    (K : Type u) [CommRing K] (q : ℕ) {depth n : ℕ}
    (term : ExactInterfaceTermParameters depth)
    (hmultiplicity : term.multiplicity = n + 1)
    (zero : Leg) (hzero : term.index.count zero = 0)
    (hcomplement : ∀ word,
      (term.positivePowerProfile hmultiplicity (secondLiveLeg zero)).counts word =
        (term.positivePowerProfile hmultiplicity (firstLiveLeg zero)).counts
          (complementSplitWord word)) :
    (cwSelectedExactInterfaceTerm K q term hmultiplicity).support.card =
      (term.positivePowerProfile hmultiplicity (firstLiveLeg zero)).typeClass.card := by
  change
    ((cwChunkPartitionedTensor K q depth).selectEncodedCompleteSplitProfiles
      (fun _c ↦ cwChunkSplitWord depth) term.index
      (fun c ↦ term.positivePowerProfile hmultiplicity c)).support.card = _
  exact card_selectEncodedCompleteSplitProfiles_orientedZero_eq_card_typeClass
    (P := cwChunkPartitionedTensor K q depth)
    (encode := fun _c ↦ cwChunkSplitWord depth)
    (zero := zero)
    (hencodeFirst := cwChunkSplitWord_injective depth)
    (D := cwOrientedZeroCoordinateCompleteFiberData K q zero depth)
    (index := term.index)
    (profile := fun c ↦ term.positivePowerProfile hmultiplicity c)
    hzero hcomplement
    (by
      simpa [cwSelectedExactInterfaceTerm,
        Tensor.PartitionedTensor.selectEncodedExactInterfaceTerm] using
        (cwSelectedExactInterfaceTerm_zero_support_isSharedFiber
          K q term hmultiplicity zero hzero).2.1)

end AlgebraicComplexity.Examples
