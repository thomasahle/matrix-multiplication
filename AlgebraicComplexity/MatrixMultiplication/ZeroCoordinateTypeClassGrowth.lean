/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Combinatorics.TypeClassEntropyLowerCore
import AlgebraicComplexity.MatrixMultiplication.ZeroCoordinateTypeClass

/-!
# Entropy growth of exact zero-coordinate interfaces

The finite semantic theorem identifies a selected zero-coordinate support with one exact type
class.  This file applies the general method-of-types lower bound to that identity.  Keeping the
analytic corollary separate prevents entropy, real exponentials, and multinomial estimates from
entering the finite selector and tensor-realization import cone.
-/

namespace AlgebraicComplexity

open Tensor

universe u v w

variable {K : Type u} [CommSemiring K]
variable {A : Leg → Type w} [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]
variable {V : ∀ c, A c → Type (max u v)}
variable [∀ c a, AddCommMonoid (V c a)] [∀ c a, Module K (V c a)]
variable {depth n : ℕ}

/-- Method-of-types lower bound for an exact zero-coordinate selected support.  The loss is the
named polynomial sequence `typeClassEntropyLoss`; its subexponentiality is already proved in the
generic counting library. -/
theorem two_rpow_profileEntropyBits_le_typeClassEntropyLoss_mul_card_zeroCoordinateSupport
    (P : PartitionedTensor (K := K) (A := A) V)
    (encode : ∀ c, A c → SplitWord depth)
    (hencodeX : Function.Injective (encode .X))
    (D : ZeroCoordinateCompleteFiberData P encode)
    (index : LevelConstituentIndex depth)
    (profile : ∀ c, CompleteSplitProfile depth (index.count c) (n + 1))
    (hz : index.count .Z = 0)
    (hcomplement : ∀ word,
      (profile .Y).counts word =
        (profile .X).counts (complementSplitWord word))
    (hshared : Set.InjOn (fun address ↦ address .X)
      ((P.selectEncodedCompleteSplitProfiles encode index profile).support :
        Set (BlockAddress fun c ↦ PositiveWord (A c) n))) :
    (2 : ℝ) ^ (((n + 1 : ℕ) : ℝ) *
      WordType.profileEntropyBits (profile .X).counts) ≤
      WordType.typeClassEntropyLoss (SplitWord depth) (n + 1) *
        (((P.selectEncodedCompleteSplitProfiles encode index profile).support.card : ℕ) :
          ℝ) := by
  have hcount := card_selectEncodedCompleteSplitProfiles_zero_eq_card_typeClass
    P encode hencodeX D index profile hz hcomplement hshared
  change (P.selectEncodedCompleteSplitProfiles encode index profile).support.card =
    (WordType.typeClass (n + 1) (profile .X).counts).card at hcount
  have htype := WordType.two_rpow_profileEntropyBits_le_typeClassEntropyLoss_mul_card_typeClass
    (profile .X).counts (profile .X).isType (Nat.succ_pos n)
  rw [← hcount] at htype
  exact htype

end AlgebraicComplexity
