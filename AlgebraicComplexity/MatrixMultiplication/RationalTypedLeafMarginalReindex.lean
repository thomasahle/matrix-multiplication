/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.RationalTypedLeafGrowth
import AlgebraicComplexity.MatrixMultiplication.RationalTypedLeafReindex

set_option autoImplicit false

/-!
# Relabelling the source index leaves the leg marginals alone

Layer 3 (`AlgebraicComplexity/MatrixMultiplication/`).  `RationalTypedLeaf.reindex` renames the
*source* index type of a typed leaf along an equivalence, leaving its three interface coordinates
and its count table untouched up to that renaming.  A leg marginal is the pushforward of the count
table along one coordinate, so it does not move.

This is bookkeeping, not mathematics: the committed tensor-facing `112` leaf is a `reindex` of the
cyclic product onto the actual partition-support subtype, so every marginal fact proved for the
cyclic product has to travel across that renaming.

Primary source: none; this is typed-leaf infrastructure.
-/

namespace AlgebraicComplexity

open Tensor
open scoped BigOperators

universe u v

namespace RationalTypedLeaf

variable {I : Type u} [Fintype I] [Nonempty I]
variable {J : Type u} [Fintype J] [Nonempty J]
variable {A : Leg → Type v} [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]

omit [Nonempty I] [Nonempty J] [∀ c, Fintype (A c)] in
/-- **A source relabelling does not move a leg marginal.** -/
theorem marginalProfile_reindex (leaf : RationalTypedLeaf I A) (e : I ≃ J) (c : Leg) :
    (leaf.reindex e).marginalProfile c = leaf.marginalProfile c := by
  classical
  funext a
  unfold marginalProfile
  rw [WordType.mappedType_eq_sum_ite, WordType.mappedType_eq_sum_ite]
  exact (Fintype.sum_equiv e _ _ (fun i ↦ by simp [RationalTypedLeaf.reindex,
    PositiveIntegralProfile.reindex])).symm

end RationalTypedLeaf

end AlgebraicComplexity
