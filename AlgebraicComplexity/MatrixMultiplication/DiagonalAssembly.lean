/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.TypeExtraction
import AlgebraicComplexity.MatrixMultiplication.AsymptoticSum
import AlgebraicComplexity.Tensor.IndexedDirectSum
import AlgebraicComplexity.Tensor.PowerFamily

/-!
# Diagonal assembly of heterogeneous extracted families

A recursive laser construction commonly extracts one direct sum for each constituent kind and
then tensors those families together.  The intended outputs use the same copy label in every
factor; all cross-labelled products must be zeroed.  This module packages that operation for an
arbitrary nonempty word of heterogeneous stages.

The first theorem is tensor-generic.  The second additionally assumes a rectangular
matrix-multiplication restriction for every stage and output label, and computes the three final
dimensions as exact products.  Thus neither theorem depends on a Coppersmith--Winograd tensor,
an entropy convention, or a numerical certificate.
-/

namespace AlgebraicComplexity

open Tensor

universe u v w x

variable (K : Type u) [CommSemiring K]
variable {Stage : Type w}
variable {Output : Type x} [Fintype Output]
variable {W : Stage → Output → Leg → Type (max u v)}
variable [∀ stage output c, AddCommMonoid (W stage output c)]
variable [∀ stage output c, Module K (W stage output c)]

/-- Package the spaces of one stage's output-indexed direct sum. -/
@[reducible] noncomputable def diagonalStageFamily
    (W : Stage → Output → Leg → Type (max u v))
    [∀ stage output c, AddCommMonoid (W stage output c)]
    [∀ stage output c, Module K (W stage output c)]
    (stage : Stage) : LegModuleFamily.{u, max v x} K :=
  indexedDirectSumFamily
    (fun output ↦ LegModuleFamily.of (K := K) (W stage output))

/-- Package one output component across all heterogeneous stages. -/
@[reducible] def diagonalComponentFamily
    (W : Stage → Output → Leg → Type (max u v))
    [∀ stage output c, AddCommMonoid (W stage output c)]
    [∀ stage output c, Module K (W stage output c)]
    (output : Output) (stage : Stage) : LegModuleFamily.{u, v} K :=
  LegModuleFamily.of (K := K) (W stage output)

namespace Tensor.Restricts

/-- A nonempty external product of output-indexed direct sums restricts to the direct sum of
componentwise products with one shared output label.

At every inductive step `external_indexedDirectSum_diagonal` kills precisely the cross-labelled
terms.  This is the finite no-mixing statement used when independently repaired constituent
families are assembled into complete recursive outputs. -/
theorem positiveWord_indexedDirectSum_diagonal
    (S : ∀ stage output, Tensor3 K (W stage output))
    (r : ℕ) (stages : PositiveWord Stage r) :
    Restricts
      (positiveWordTensor
        (diagonalStageFamily (K := K) W)
        (fun stage ↦ Tensor.indexedDirectSum (S stage)) r stages)
      (Tensor.indexedDirectSum (fun output ↦
        positiveWordTensor
          (diagonalComponentFamily (K := K) W output)
          (fun stage ↦ S stage output) r stages)) := by
  classical
  induction r with
  | zero =>
      exact Restricts.refl _
  | succ r ih =>
      change Restricts
        (Tensor.external
          (positiveWordTensor
          (diagonalStageFamily (K := K) W)
            (fun stage ↦ Tensor.indexedDirectSum (S stage)) r stages.1)
          (Tensor.indexedDirectSum (S stages.2)))
        (Tensor.indexedDirectSum (fun output ↦
          Tensor.external
            (positiveWordTensor
              (diagonalComponentFamily (K := K) W output)
              (fun stage ↦ S stage output) r stages.1)
            (S stages.2 output)))
      exact
        ((ih stages.1).external
          (Restricts.refl (Tensor.indexedDirectSum (S stages.2)))).trans
          (Restricts.external_indexedDirectSum_diagonal
            (fun output ↦
              positiveWordTensor
                (diagonalComponentFamily (K := K) W output)
                (fun stage ↦ S stage output) r stages.1)
            (S stages.2))

/-- Diagonal assembly followed by heterogeneous rectangular leaf multiplication.

Each output label may use different dimensions at each stage.  The result records their exact
products along the supplied stage word, so a certificate can prove uniformity only after this
generic semantic step. -/
theorem positiveWord_indexedDirectSum_matrixMultiplication
    (S : ∀ stage output, Tensor3 K (W stage output))
    (m n p : Stage → Output → ℕ)
    (hleaf : ∀ stage output,
      Restricts (S stage output)
        (matrixMultiplication (K := K)
          (m stage output) (n stage output) (p stage output)))
    (r : ℕ) (stages : PositiveWord Stage r) :
    Restricts
      (positiveWordTensor
        (diagonalStageFamily (K := K) W)
        (fun stage ↦ Tensor.indexedDirectSum (S stage)) r stages)
      (matrixMultiplicationDirectSum K
        (fun output ↦ positiveWordProduct (fun stage ↦ m stage output) r stages)
        (fun output ↦ positiveWordProduct (fun stage ↦ n stage output) r stages)
        (fun output ↦ positiveWordProduct (fun stage ↦ p stage output) r stages)) := by
  classical
  have hcomponent : ∀ output,
      Restricts
        (positiveWordTensor
          (diagonalComponentFamily (K := K) W output)
          (fun stage ↦ S stage output) r stages)
        (matrixMultiplication (K := K)
          (positiveWordProduct (fun stage ↦ m stage output) r stages)
          (positiveWordProduct (fun stage ↦ n stage output) r stages)
          (positiveWordProduct (fun stage ↦ p stage output) r stages)) := by
    intro output
    induction r with
    | zero =>
        exact hleaf stages output
    | succ r ih =>
        change Restricts
          (Tensor.external
            (positiveWordTensor
              (diagonalComponentFamily (K := K) W output)
              (fun stage ↦ S stage output) r stages.1)
            (S stages.2 output))
          (matrixMultiplication (K := K)
            (positiveWordProduct (fun stage ↦ m stage output) r stages.1 *
              m stages.2 output)
            (positiveWordProduct (fun stage ↦ n stage output) r stages.1 *
              n stages.2 output)
            (positiveWordProduct (fun stage ↦ p stage output) r stages.1 *
              p stages.2 output))
        exact
          ((ih stages.1).external (hleaf stages.2 output)).trans
            (Tensor.Isomorphic.matrixMultiplication_external
              (K := K)
              (positiveWordProduct (fun stage ↦ m stage output) r stages.1)
              (positiveWordProduct (fun stage ↦ n stage output) r stages.1)
              (positiveWordProduct (fun stage ↦ p stage output) r stages.1)
              (m stages.2 output) (n stages.2 output) (p stages.2 output)).restricts
  exact
    (positiveWord_indexedDirectSum_diagonal (K := K) S r stages).trans
      (Restricts.indexedDirectSum hcomponent)

/-! ## Assembly directly from powers of one common source -/

variable {V₀ : Leg → Type v}
variable [∀ c, AddCommMonoid (V₀ c)] [∀ c, Module K (V₀ c)]

/-- Stagewise restrictions of powers of one tensor assemble into a restriction of the power whose
exponent is the sum of the stage exponents.

This is the source-coherence half of recursive diagonal assembly.  The target stages may have
unrelated leg spaces; only their source tensor is shared. -/
theorem power_positiveWord_indexedDirectSum
    (T : Tensor3 K V₀) (exponent : Stage → ℕ)
    (S : ∀ stage output, Tensor3 K (W stage output))
    (hstage : ∀ stage,
      Restricts (Tensor.power T (exponent stage)) (Tensor.indexedDirectSum (S stage)))
    (r : ℕ) (stages : PositiveWord Stage r) :
    Restricts
      (Tensor.power T (positiveWordSum exponent r stages))
      (positiveWordTensor
        (diagonalStageFamily (K := K) W)
        (fun stage ↦ Tensor.indexedDirectSum (S stage)) r stages) := by
  induction r with
  | zero =>
      exact hstage stages
  | succ r ih =>
      change Restricts
        (Tensor.power T
          (positiveWordSum exponent r stages.1 + exponent stages.2))
        (Tensor.external
          (positiveWordTensor
            (diagonalStageFamily (K := K) W)
            (fun stage ↦ Tensor.indexedDirectSum (S stage)) r stages.1)
          (Tensor.indexedDirectSum (S stages.2)))
      exact
        (isomorphic_external_power T
          (positiveWordSum exponent r stages.1) (exponent stages.2)).symm.restricts.trans
          ((ih stages.1).external (hstage stages.2))

/-- Complete finite diagonal assembly from heterogeneous restrictions of powers of one source.

Every stage extracts an output-indexed family from its own source power.  Tensoring the stages,
zeroing cross-labelled products, and applying the rectangular leaf restrictions produces one
matrix-multiplication tensor per shared output label.  The source exponent and all three output
dimensions are computed exactly. -/
theorem power_positiveWord_indexedDirectSum_matrixMultiplication
    (T : Tensor3 K V₀) (exponent : Stage → ℕ)
    (S : ∀ stage output, Tensor3 K (W stage output))
    (hstage : ∀ stage,
      Restricts (Tensor.power T (exponent stage)) (Tensor.indexedDirectSum (S stage)))
    (m n p : Stage → Output → ℕ)
    (hleaf : ∀ stage output,
      Restricts (S stage output)
        (matrixMultiplication (K := K)
          (m stage output) (n stage output) (p stage output)))
    (r : ℕ) (stages : PositiveWord Stage r) :
    Restricts
      (Tensor.power T (positiveWordSum exponent r stages))
      (matrixMultiplicationDirectSum K
        (fun output ↦ positiveWordProduct (fun stage ↦ m stage output) r stages)
        (fun output ↦ positiveWordProduct (fun stage ↦ n stage output) r stages)
        (fun output ↦ positiveWordProduct (fun stage ↦ p stage output) r stages)) :=
  (power_positiveWord_indexedDirectSum (K := K) T exponent S hstage r stages).trans
    (positiveWord_indexedDirectSum_matrixMultiplication
      (K := K) S m n p hleaf r stages)

end Tensor.Restricts

namespace Tensor.PolynomialDegenerates

/-- Polynomial-degeneration form of heterogeneous diagonal matrix-multiplication assembly. -/
theorem positiveWord_indexedDirectSum_matrixMultiplication
    (S : ∀ stage output, Tensor3 K (W stage output))
    (m n p : Stage → Output → ℕ)
    (hleaf : ∀ stage output,
      Restricts (S stage output)
        (matrixMultiplication (K := K)
          (m stage output) (n stage output) (p stage output)))
    (r : ℕ) (stages : PositiveWord Stage r) :
    PolynomialDegenerates
      (positiveWordTensor
        (diagonalStageFamily (K := K) W)
        (fun stage ↦ Tensor.indexedDirectSum (S stage)) r stages)
      (matrixMultiplicationDirectSum K
        (fun output ↦ positiveWordProduct (fun stage ↦ m stage output) r stages)
        (fun output ↦ positiveWordProduct (fun stage ↦ n stage output) r stages)
        (fun output ↦ positiveWordProduct (fun stage ↦ p stage output) r stages)) :=
  PolynomialDegenerates.of_restricts
    (Restricts.positiveWord_indexedDirectSum_matrixMultiplication
      (K := K) S m n p hleaf r stages)

variable {V₀ : Leg → Type v}
variable [∀ c, AddCommMonoid (V₀ c)] [∀ c, Module K (V₀ c)]

/-- Polynomial-degeneration form of complete finite diagonal assembly from powers of one common
source tensor. -/
theorem power_positiveWord_indexedDirectSum_matrixMultiplication
    (T : Tensor3 K V₀) (exponent : Stage → ℕ)
    (S : ∀ stage output, Tensor3 K (W stage output))
    (hstage : ∀ stage,
      Restricts (Tensor.power T (exponent stage)) (Tensor.indexedDirectSum (S stage)))
    (m n p : Stage → Output → ℕ)
    (hleaf : ∀ stage output,
      Restricts (S stage output)
        (matrixMultiplication (K := K)
          (m stage output) (n stage output) (p stage output)))
    (r : ℕ) (stages : PositiveWord Stage r) :
    PolynomialDegenerates
      (Tensor.power T (positiveWordSum exponent r stages))
      (matrixMultiplicationDirectSum K
        (fun output ↦ positiveWordProduct (fun stage ↦ m stage output) r stages)
        (fun output ↦ positiveWordProduct (fun stage ↦ n stage output) r stages)
        (fun output ↦ positiveWordProduct (fun stage ↦ p stage output) r stages)) :=
  PolynomialDegenerates.of_restricts
    (Restricts.power_positiveWord_indexedDirectSum_matrixMultiplication
      (K := K) T exponent S hstage m n p hleaf r stages)

end Tensor.PolynomialDegenerates

end AlgebraicComplexity
