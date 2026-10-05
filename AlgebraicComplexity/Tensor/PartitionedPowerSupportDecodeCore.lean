/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Tensor.PartitionedPowerSupportDecodeRecursive
import AlgebraicComplexity.Tensor.PositiveWord

/-!
# Coordinate decoding of positive-power support addresses

`PartitionedPowerSupportDecodeRecursive` proves and re-exports the dependency-light recursive
decoder.  This module adds the coordinate theorem identifying its legwise transpose with the
canonical function representation on `Fin (n + 1)`.  Consumers that need only a recovered word
should import the recursive leaf and avoid this finite-tuple layer.
-/

namespace AlgebraicComplexity.Tensor

universe u v w

variable {K : Type u} [CommSemiring K]
variable {A : Leg → Type w} [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]
variable {V : ∀ c, A c → Type (max u v)}
variable [∀ c a, AddCommMonoid (V c a)] [∀ c a, Module K (V c a)]

omit [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)] in
/-- Reading one leg of the recursive transpose recovers the corresponding projection of every
source address.  This dependency-light form avoids the global word/address equivalence developed
by `PartitionedPower`. -/
theorem positiveWordEquiv_positiveSupportWordBlockAddress_recursive
    (support : Finset (BlockAddress A)) (n : ℕ)
    (word : PositiveWord support n) (c : Leg) :
    positiveWordEquiv (A c) n (positiveSupportWordBlockAddress support n word c) =
      fun i ↦ (positiveWordEquiv support n word i).1 c := by
  induction n with
  | zero =>
      funext i
      have hi : i = 0 := Fin.eq_zero i
      subst i
      rfl
  | succ n ih =>
      rcases word with ⟨initial, final⟩
      change positiveWordEquiv (A c) (n + 1)
          (positiveSupportWordBlockAddress support n initial c, final.1 c) =
        fun i ↦ (@Fin.snoc (n + 1) (fun _ ↦ support)
          (positiveWordEquiv support n initial) final i).1 c
      change (fun i ↦ @Fin.snoc (n + 1) (fun _ ↦ A c)
          (positiveWordEquiv (A c) n
            (positiveSupportWordBlockAddress support n initial c)) (final.1 c) i) = _
      funext i
      refine Fin.lastCases ?_ (fun j ↦ ?_) i
      · simp
      · simpa using congrFun (ih initial) j

end AlgebraicComplexity.Tensor
