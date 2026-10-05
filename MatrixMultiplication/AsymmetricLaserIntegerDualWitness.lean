/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import MatrixMultiplication.AsymmetricLaserLogWitness
import MatrixMultiplication.IntegerEntropyDual
import AlgebraicComplexity.Probability.RationalCore

/-!
# Finite logarithm atoms for integer maximum-entropy duals

This is the directed maximum-entropy verification step of [duan2023faster],
`papers/sources/2210.10173/second_power.tex:536-563` and
`global_value.tex:286-309`, in the integer-factor format described in
`better_bound/blueprint/FW_shared_bridge.md:179-240`.

An upper partition logarithm and lower coordinate-factor logarithms give an upper
dual value. The reference law has arbitrary rational weights. Every structural
state enters the partition, including states with zero reference mass. Completeness
of that structural state type is a separate obligation of its native decoder.

Proof sketch: apply the existing integer-product weak-duality theorem, rewrite the
three marginal expectations as a single state sum, and bound its nonnegative
weighted summands. The finite atoms use the landed rational atanh bounds, not the
different canonical endpoints of `IntegerEntropyDual`. Subtracting a proved lower
entropy bound gives the combination-loss upper bound. No extraction, optimization
convergence, or all-scales tensor hypothesis occurs in this arithmetic adapter.
-/

set_option autoImplicit false

open scoped BigOperators

namespace AlgebraicComplexity.AsymmetricLaserData

variable {A X Y Z : Type*}

/-- Rational upper dual form, with the marginal pairings expanded over all states. -/
def integerDualUpper [Fintype A]
    (coordX : A → X) (coordY : A → Y) (coordZ : A → Z)
    (reference : RationalProbabilityData A) (partitionUpper : ℚ)
    (lowerX : X → ℚ) (lowerY : Y → ℚ) (lowerZ : Z → ℚ) : ℚ :=
  partitionUpper - ∑ a, reference.weight a *
    (lowerX (coordX a) + lowerY (coordY a) + lowerZ (coordZ a))

/-- Checked logarithm atoms bound maximum entropy at the reference marginals.
The partition identity includes every element of `A`, not only its primal support. -/
theorem integerDualUpper_bounds
    [Fintype A] [Nonempty A] [Fintype X] [Fintype Y] [Fintype Z]
    [DecidableEq X] [DecidableEq Y] [DecidableEq Z]
    (coordX : A → X) (coordY : A → Y) (coordZ : A → Z)
    (reference : RationalProbabilityData A) (href : reference.IsProbability)
    (partitionAtom : LogAtom) (atomX : X → LogAtom) (atomY : Y → LogAtom)
    (atomZ : Z → LogAtom) (hpartition : partitionAtom.Valid)
    (hX : ∀ x, (atomX x).Valid) (hY : ∀ y, (atomY y).Valid)
    (hZ : ∀ z, (atomZ z).Valid)
    (hargument : partitionAtom.argument =
      MatrixMultiplication.IntegerEntropyDual.integerPartitionNumerator
        coordX coordY coordZ (fun x => (atomX x).argument)
        (fun y => (atomY y).argument) (fun z => (atomZ z).argument)) :
    MaximumEntropyDual.maximumEntropyBits coordX coordY coordZ
        (reference.toReal href).weight ≤
      (integerDualUpper coordX coordY coordZ reference partitionAtom.upper
        (fun x => (atomX x).lower) (fun y => (atomY y).lower)
        (fun z => (atomZ z).lower) : ℝ) := by
  have hprob : MaximumEntropyDual.IsProbability (reference.toReal href).weight :=
    ⟨(reference.toReal href).nonneg, (reference.toReal href).total⟩
  apply (MatrixMultiplication.IntegerEntropyDual.maximumEntropyBits_le_integerCoordinateDual
    coordX coordY coordZ (reference.toReal href).weight
    (fun x => (atomX x).argument) (fun y => (atomY y).argument)
    (fun z => (atomZ z).argument) hprob
    (fun x => (hX x).1) (fun y => (hY y).1) (fun z => (hZ z).1)).trans
  unfold MatrixMultiplication.IntegerEntropyDual.integerCoordinateDualBits
  rw [MatrixMultiplication.IntegerEntropyDual.integerPartition_eq_cast, ← hargument]
  rw [← MaximumEntropyDual.coordinateScore_expectation]
  simp only [integerDualUpper, Rat.cast_sub, Rat.cast_sum, Rat.cast_mul, Rat.cast_add]
  apply sub_le_sub (partitionAtom.le_upper hpartition)
  apply Finset.sum_le_sum
  intro a _
  exact mul_le_mul_of_nonneg_left
    (add_le_add (add_le_add ((atomX (coordX a)).lower_le (hX _))
      ((atomY (coordY a)).lower_le (hY _))) ((atomZ (coordZ a)).lower_le (hZ _)))
    ((reference.toReal href).nonneg a)

/-- Subtracting a lower reference-entropy bound gives a conservative combination-loss bound.
The lower entropy premise is discharged by the separate finite-law entropy adapter. -/
theorem integerDualGapUpper_bounds
    [Fintype A] [Nonempty A] [Fintype X] [Fintype Y] [Fintype Z]
    [DecidableEq X] [DecidableEq Y] [DecidableEq Z]
    (coordX : A → X) (coordY : A → Y) (coordZ : A → Z)
    (reference : RationalProbabilityData A) (href : reference.IsProbability)
    (partitionAtom : LogAtom) (atomX : X → LogAtom) (atomY : Y → LogAtom)
    (atomZ : Z → LogAtom) (hpartition : partitionAtom.Valid)
    (hX : ∀ x, (atomX x).Valid) (hY : ∀ y, (atomY y).Valid)
    (hZ : ∀ z, (atomZ z).Valid)
    (hargument : partitionAtom.argument =
      MatrixMultiplication.IntegerEntropyDual.integerPartitionNumerator
        coordX coordY coordZ (fun x => (atomX x).argument)
        (fun y => (atomY y).argument) (fun z => (atomZ z).argument))
    (entropyLower : ℚ)
    (hentropy : (entropyLower : ℝ) ≤
      MaximumEntropyDual.entropyBits (reference.toReal href).weight) :
    MaximumEntropyDual.combinationLossBits coordX coordY coordZ
        (reference.toReal href).weight ≤
      ((integerDualUpper coordX coordY coordZ reference partitionAtom.upper
        (fun x => (atomX x).lower) (fun y => (atomY y).lower)
        (fun z => (atomZ z).lower) - entropyLower : ℚ) : ℝ) := by
  rw [Rat.cast_sub]
  exact sub_le_sub (integerDualUpper_bounds coordX coordY coordZ reference href
    partitionAtom atomX atomY atomZ hpartition hX hY hZ hargument) hentropy

end AlgebraicComplexity.AsymmetricLaserData
