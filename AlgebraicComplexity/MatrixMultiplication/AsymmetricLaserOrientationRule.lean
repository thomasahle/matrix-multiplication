/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.TypeExtraction
import AlgebraicComplexity.Tensor.PermutationCoherence

/-!
# Finite physical-leg decoding and matrix-multiplication retyping

This is the finite orientation step in [duan2023faster],
`papers/sources/2210.10173/component_value.tex:459-475` (the six zero-component frames)
and `prelim.tex:294-309` (ordered split children). It follows the output-to-input convention
of `AsymmetricLaserData.ChildRef.physicalLegs`: the table encodes the inverse orientation.
Only the six permutations of the three physical legs are admitted. Matrix dimensions are
derived from that orientation and the input dimensions, never supplied as output witnesses.

Retyping composes the existing cyclic and Y/Z-swap matrix isomorphisms and the tensor
permutation composition law. This shared rule has no CW-specific tensor-coordinate proof.
Its literal DWZ zero-X011 consumer is in the same image. Profile transport, canonical shared
leg-map coherence, producing-DAG checks and exponent regression are separate obligations.
-/

set_option autoImplicit false

namespace AlgebraicComplexity.AsymmetricLaserData

open Tensor

universe u v

/-- Integer codes for the physical tensor legs, in X/Y/Z order. -/
def physicalLegCode : Leg → Nat
  | .X => 0
  | .Y => 1
  | .Z => 2

/-- The input leg supplying each output leg of the tensor permutation. -/
def physicalLegTable (e : Orientation) : List Nat :=
  [physicalLegCode (e.symm .X), physicalLegCode (e.symm .Y), physicalLegCode (e.symm .Z)]

/-- Decode all six output-to-input tables; other lengths, repeated and invalid digits reject. -/
def decodePhysicalLegs : List Nat → Option Orientation
  | [0, 1, 2] => some (Equiv.refl Leg)
  | [2, 0, 1] => some cycle
  | [1, 2, 0] => some cycle.symm
  | [0, 2, 1] => some xzy
  | [2, 1, 0] => some (cycle.trans xzy)
  | [1, 0, 2] => some (cycle.symm.trans xzy)
  | _ => none

/-- Derive the matrix dimensions from the inverse physical-leg action.
The repeated-leg fallback cannot occur for an orientation admitted by the decoder. -/
def physicalLegMatrixDimensions (e : Orientation) (m n p : Nat) : Nat × Nat × Nat :=
  match e.symm .X, e.symm .Y with
  | .X, .Y => (m, n, p)
  | .Z, .X => (p, m, n)
  | .Y, .Z => (n, p, m)
  | .X, .Z => (n, m, p)
  | .Z, .Y => (m, p, n)
  | .Y, .X => (p, n, m)
  | _, _ => (m, n, p)

/-- Successful decoding binds the exact input table to the inverse native leg action. -/
theorem decodePhysicalLegs_sound (table : List Nat) (e : Orientation)
    (h : decodePhysicalLegs table = some e) : physicalLegTable e = table := by
  unfold decodePhysicalLegs at h
  split at h <;> simp only [Option.some.injEq, reduceCtorEq] at h
  all_goals subst e; rfl

/-- Each admitted table retypes the actual permuted matrix tensor to the derived dimensions. -/
theorem decodePhysicalLegs_isomorphic (K : Type u) [CommSemiring K]
    (table : List Nat) (e : Orientation) (m n p : Nat)
    (h : decodePhysicalLegs table = some e) :
    Isomorphic (Tensor.permute e (matrixMultiplication (K := K) m n p))
      (matrixMultiplication (K := K)
        (physicalLegMatrixDimensions e m n p).1
        (physicalLegMatrixDimensions e m n p).2.1
        (physicalLegMatrixDimensions e m n p).2.2) := by
  unfold decodePhysicalLegs at h
  split at h <;> simp only [Option.some.injEq, reduceCtorEq] at h
  all_goals subst e
  · exact Isomorphic.cancel_permute_refl _
  · exact Isomorphic.matrixMultiplication_cycle m n p
  · exact Isomorphic.matrixMultiplication_cycle_symm m n p
  · exact Isomorphic.matrixMultiplication_swapYZ m n p
  · rw [Tensor.permute_composite_apply]
    exact ((Isomorphic.matrixMultiplication_cycle (K := K) m n p).permute_legs xzy).trans
      (Isomorphic.matrixMultiplication_swapYZ p m n)
  · rw [Tensor.permute_composite_apply]
    exact ((Isomorphic.matrixMultiplication_cycle_symm (K := K) m n p).permute_legs xzy).trans
      (Isomorphic.matrixMultiplication_swapYZ n p m)

/-- Transport an already derived restriction through a checked physical-leg table.
The input restriction is semantic provider output, not a field of the finite payload. -/
theorem decodePhysicalLegs_restricts (K : Type u) [CommSemiring K]
    {V : Leg → Type v} [∀ i, AddCommMonoid (V i)] [∀ i, Module K (V i)]
    (table : List Nat) (e : Orientation) (m n p : Nat)
    (h : decodePhysicalLegs table = some e) (T : Tensor3 K V)
    (hT : Restricts T (matrixMultiplication (K := K) m n p)) :
    Restricts (Tensor.permute e T)
      (matrixMultiplication (K := K)
        (physicalLegMatrixDimensions e m n p).1
        (physicalLegMatrixDimensions e m n p).2.1
        (physicalLegMatrixDimensions e m n p).2.2) :=
  (hT.permute e).trans (decodePhysicalLegs_isomorphic K table e m n p h).restricts

end AlgebraicComplexity.AsymmetricLaserData
