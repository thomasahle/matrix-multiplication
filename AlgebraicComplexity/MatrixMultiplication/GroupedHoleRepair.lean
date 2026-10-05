/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.LaserVolume
import AlgebraicComplexity.Tensor.HoleRepairTree

/-!
# From cleaned constituent fibers to repaired matrix-multiplication copies

This module is the finite semantic adapter between compatibility cleanup and the volume laser
interface.  A single embedding assigns distinct cleaned fibers to every occurrence in every
repair plan.  Each fiber need only restrict to its own damaged box.  The repair trees reconstruct
the intact boxes, after which the ordinary leaf restrictions produce a matrix-multiplication
direct sum.
-/

namespace AlgebraicComplexity

open Tensor

universe u v w x

/-- Assemble a cleaned grouped family, varying broken-box repair plans, and one common
matrix-multiplication leaf into the finite direct sum consumed by the laser interface.

The injectivity of `pick` is the no-reuse condition across both repair occurrences and output
copies.  In particular, this theorem does not replace damaged fibers by full copies of `P`.
-/
theorem PolynomialDegenerates.of_groupedRepairPlans_matrixMultiplication
    (K : Type u) [CommSemiring K]
    {A : Leg → Type u} [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]
    {V : ∀ c, A c → Type u}
    [∀ c a, AddCommMonoid (V c a)] [∀ c a, Module K (V c a)]
    {P : PartitionedTensor (K := K) (A := A) V}
    {target : ∀ c, Finset (A c)}
    {O : Type w} [Fintype O] [DecidableEq O]
    (plans : O → RepairPlan P target)
    {I : Type x} [Fintype I] [DecidableEq I]
    {U : Leg → Type v}
    [∀ c, AddCommMonoid (U c)] [∀ c, Module K (U c)]
    {T : Tensor3 K U} (groups : I → Tensor3 K U)
    (hgroups : Restricts T (Tensor.indexedDirectSum groups))
    (pick : (Σ output, (plans output).Copy) ↪ I)
    (hbroken : ∀ occurrence : Σ output, (plans output).Copy,
      Restricts (groups (pick occurrence))
        (P.box (fun c ↦ Finset.univ \
          (plans occurrence.1).holesAt occurrence.2 c)).realize)
    {m n p : ℕ}
    (hleaf : Restricts (P.box target).realize
      (matrixMultiplication (K := K) m n p)) :
    PolynomialDegenerates T
      (matrixMultiplicationDirectSum (ι := O) K
        (fun _ ↦ m) (fun _ ↦ n) (fun _ ↦ p)) := by
  have hrepair : Restricts (Tensor.indexedDirectSum groups)
      (Tensor.indexedDirectSum (fun _output : O ↦ (P.box target).realize)) :=
    RepairPlan.indexedDirectSum_repairPlans plans groups pick hbroken
  exact PolynomialDegenerates.of_restricts_indexedDirectSum_matrixMultiplication K
    (hgroups.trans hrepair) (fun _output ↦ hleaf)

end AlgebraicComplexity
