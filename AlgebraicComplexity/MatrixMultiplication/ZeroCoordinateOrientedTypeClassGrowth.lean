/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Combinatorics.TypeClassEntropyLowerCore
import AlgebraicComplexity.MatrixMultiplication.ZeroCoordinateOrientedTypeClass

set_option autoImplicit false

/-!
# Entropy growth of exact zero-coordinate interfaces in every orientation

This is the directed method-of-types consequence of the orientation-general selected-support
equivalence.  It retains the explicit fixed-alphabet polynomial loss and makes the live profile
part of the statement through `firstLiveLeg zero`.
-/

namespace AlgebraicComplexity

open Tensor MoreAsymmetryCompatibility

universe u v w

variable {K : Type u} [CommSemiring K]
variable {A : Leg → Type w} [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]
variable {V : ∀ c, A c → Type (max u v)}
variable [∀ c a, AddCommMonoid (V c a)] [∀ c a, Module K (V c a)]
variable {depth n : ℕ}

/-- Method-of-types lower bound for a complete zero-coordinate support in an arbitrary
orientation. -/
theorem two_rpow_profileEntropyBits_le_typeClassEntropyLoss_mul_card_orientedZeroSupport
    (P : PartitionedTensor (K := K) (A := A) V)
    (encode : ∀ c, A c → SplitWord depth) (zero : Leg)
    (hencodeFirst : Function.Injective (encode (firstLiveLeg zero)))
    (D : OrientedZeroCoordinateCompleteFiberData P encode zero)
    (index : LevelConstituentIndex depth)
    (profile : ∀ c, CompleteSplitProfile depth (index.count c) (n + 1))
    (hzero : index.count zero = 0)
    (hcomplement : ∀ word,
      (profile (secondLiveLeg zero)).counts word =
        (profile (firstLiveLeg zero)).counts (complementSplitWord word))
    (hshared : Set.InjOn (fun address ↦ address (firstLiveLeg zero))
      ((P.selectEncodedCompleteSplitProfiles encode index profile).support :
        Set (BlockAddress fun c ↦ PositiveWord (A c) n))) :
    (2 : ℝ) ^ (((n + 1 : ℕ) : ℝ) *
        WordType.profileEntropyBits (profile (firstLiveLeg zero)).counts) ≤
      WordType.typeClassEntropyLoss (SplitWord depth) (n + 1) *
        (((P.selectEncodedCompleteSplitProfiles encode index profile).support.card : ℕ) :
          ℝ) := by
  have hcount := card_selectEncodedCompleteSplitProfiles_orientedZero_eq_card_typeClass
    P encode zero hencodeFirst D index profile hzero hcomplement hshared
  change (P.selectEncodedCompleteSplitProfiles encode index profile).support.card =
    (WordType.typeClass (n + 1) (profile (firstLiveLeg zero)).counts).card at hcount
  have htype := WordType.two_rpow_profileEntropyBits_le_typeClassEntropyLoss_mul_card_typeClass
    (profile (firstLiveLeg zero)).counts (profile (firstLiveLeg zero)).isType
    (Nat.succ_pos n)
  rw [← hcount] at htype
  exact htype

end AlgebraicComplexity
