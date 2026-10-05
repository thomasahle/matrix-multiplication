/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.ZeroCoordinateOrientation
import AlgebraicComplexity.MatrixMultiplication.ZeroCoordinateTypeClass

set_option autoImplicit false

/-!
# Exact zero-coordinate type classes in every orientation

The original zero-coordinate counting theorem uses the canonical frame in which `Z` vanishes,
`X` carries a split word, and `Y` carries its digitwise complement.  This file states and proves
the finite theorem once for an arbitrary zero leg.  Its two live legs are
`firstLiveLeg zero` and `secondLiveLeg zero`, so the statement itself records the orientation.

The principal result is an actual equivalence between the complete selected support and the exact
type class on the first live leg.  The cardinality equality is a corollary.  No tensor
degeneration, representative selection, asymptotic estimate, or certificate datum is assumed.
-/

namespace AlgebraicComplexity

open Tensor MoreAsymmetryCompatibility

universe u v w

variable {K : Type u} [CommSemiring K]
variable {A : Leg → Type w} [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]
variable {V : ∀ c, A c → Type (max u v)}
variable [∀ c a, AddCommMonoid (V c a)] [∀ c a, Module K (V c a)]
variable {depth n : ℕ}

/-- Per-letter completeness of a zero-coordinate fibre in an arbitrary orientation.  Each split
word has a supported lift whose first live label encodes the word, whose second live label encodes
its complement, and whose zero label encodes zero. -/
structure OrientedZeroCoordinateCompleteFiberData
    (P : PartitionedTensor (K := K) (A := A) V)
    (encode : ∀ c, A c → SplitWord depth) (zero : Leg) where
  lift : SplitWord depth → P.support
  encode_first : ∀ word,
    encode (firstLiveLeg zero) ((lift word).1 (firstLiveLeg zero)) = word
  encode_second : ∀ word,
    encode (secondLiveLeg zero) ((lift word).1 (secondLiveLeg zero)) =
      complementSplitWord word
  encode_zero : ∀ word, encode zero ((lift word).1 zero) = 0

namespace OrientedZeroCoordinateCompleteFiberData

variable {P : PartitionedTensor (K := K) (A := A) V}
variable {encode : ∀ c, A c → SplitWord depth} {zero : Leg}

/-- Lift a finite split-word sequence letterwise to a supported source word. -/
noncomputable def sourceWord
    (D : OrientedZeroCoordinateCompleteFiberData P encode zero)
    (sequence : Fin (n + 1) → SplitWord depth) : PositiveWord P.support n :=
  (positiveWordEquiv P.support n).symm (D.lift ∘ sequence)

/-- Transpose an oriented lifted source word into its three positive-power block labels. -/
noncomputable def blockAddress
    (D : OrientedZeroCoordinateCompleteFiberData P encode zero)
    (sequence : Fin (n + 1) → SplitWord depth) :
    BlockAddress (fun c ↦ PositiveWord (A c) n) :=
  positiveSupportWordBlockAddress P.support n (D.sourceWord sequence)

private theorem encoded_blockAddress
    (D : OrientedZeroCoordinateCompleteFiberData P encode zero)
    (c : Leg) (target : SplitWord depth → SplitWord depth)
    (hencode : ∀ word, encode c ((D.lift word).1 c) = target word)
    (sequence : Fin (n + 1) → SplitWord depth) :
    encode c ∘ positiveWordEquiv (A c) n (D.blockAddress sequence c) =
      target ∘ sequence := by
  funext sample
  change encode c
    (positiveWordEquiv (A c) n
      (positiveSupportWordBlockAddress P.support n (D.sourceWord sequence) c) sample) = _
  rw [congrFun
    (positiveWordEquiv_positiveSupportWordBlockAddress_recursive
      P.support n (D.sourceWord sequence) c) sample]
  change encode c
      ((positiveWordEquiv P.support n
        ((positiveWordEquiv P.support n).symm (D.lift ∘ sequence)) sample).1 c) = _
  rw [Equiv.apply_symm_apply]
  exact hencode (sequence sample)

@[simp] theorem encoded_first_blockAddress
    (D : OrientedZeroCoordinateCompleteFiberData P encode zero)
    (sequence : Fin (n + 1) → SplitWord depth) :
    encode (firstLiveLeg zero) ∘
        positiveWordEquiv (A (firstLiveLeg zero)) n
          (D.blockAddress sequence (firstLiveLeg zero)) = sequence := by
  simpa using D.encoded_blockAddress (firstLiveLeg zero) id D.encode_first sequence

@[simp] theorem encoded_second_blockAddress
    (D : OrientedZeroCoordinateCompleteFiberData P encode zero)
    (sequence : Fin (n + 1) → SplitWord depth) :
    encode (secondLiveLeg zero) ∘
        positiveWordEquiv (A (secondLiveLeg zero)) n
          (D.blockAddress sequence (secondLiveLeg zero)) =
      complementSplitWord ∘ sequence :=
  D.encoded_blockAddress (secondLiveLeg zero) complementSplitWord D.encode_second sequence

@[simp] theorem encoded_zero_blockAddress
    (D : OrientedZeroCoordinateCompleteFiberData P encode zero)
    (sequence : Fin (n + 1) → SplitWord depth) :
    encode zero ∘ positiveWordEquiv (A zero) n (D.blockAddress sequence zero) = 0 := by
  have h := D.encoded_blockAddress zero (fun _word ↦ 0) D.encode_zero sequence
  funext sample
  simpa only [Function.comp_apply, Pi.zero_apply] using congrFun h sample

/-- Every word of the first-live-leg type lifts to the complete selected support. -/
theorem blockAddress_mem_selectedSupport
    (D : OrientedZeroCoordinateCompleteFiberData P encode zero)
    (index : LevelConstituentIndex depth)
    (profile : ∀ c, CompleteSplitProfile depth (index.count c) (n + 1))
    (hzero : index.count zero = 0)
    (hcomplement : ∀ word,
      (profile (secondLiveLeg zero)).counts word =
        (profile (firstLiveLeg zero)).counts (complementSplitWord word))
    (sequence : Fin (n + 1) → SplitWord depth)
    (hsequence : (profile (firstLiveLeg zero)).IsConsistent sequence) :
    D.blockAddress sequence ∈
      (P.selectEncodedCompleteSplitProfiles encode index profile).support := by
  rw [P.mem_selectEncodedCompleteSplitProfiles_support]
  refine ⟨P.positiveSupportWordBlockAddress_mem_positivePower_support_recursive n
    (D.sourceWord sequence), ?_⟩
  intro c
  rcases leg_eq_or_eq_firstLiveLeg_or_eq_secondLiveLeg zero c with rfl | rfl | rfl
  · rw [D.encoded_zero_blockAddress]
    exact (profile _).isConsistent_zero_of_total_eq_zero hzero
  · simpa using hsequence
  · rw [D.encoded_second_blockAddress]
    unfold CompleteSplitProfile.IsConsistent at hsequence ⊢
    funext word
    rw [multiplicity_comp_complementSplitWord, hcomplement, ← hsequence]

end OrientedZeroCoordinateCompleteFiberData

variable {P : PartitionedTensor (K := K) (A := A) V}
variable {encode : ∀ c, A c → SplitWord depth}

/-- **The complete selected support is one exact type class, in every orientation.** -/
noncomputable def selectedSupportEquivTypeClass_of_orientedZero
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
    (P.selectEncodedCompleteSplitProfiles encode index profile).support ≃
      (profile (firstLiveLeg zero)).typeClass := by
  classical
  let selected := P.selectEncodedCompleteSplitProfiles encode index profile
  have hshared' : Set.InjOn (fun address ↦ address (firstLiveLeg zero))
      (selected.support : Set (BlockAddress fun c ↦ PositiveWord (A c) n)) := by
    simpa [selected] using hshared
  let forward : selected.support → (profile (firstLiveLeg zero)).typeClass := fun address ↦
    ⟨encode (firstLiveLeg zero) ∘
        positiveWordEquiv (A (firstLiveLeg zero)) n (address.1 (firstLiveLeg zero)), by
      rw [← CompleteSplitProfile.isConsistent_iff_mem_typeClass]
      have hmem :=
        (P.mem_selectEncodedCompleteSplitProfiles_support encode index profile address.1).mp
          address.2
      exact hmem.2 (firstLiveLeg zero)⟩
  let backward : (profile (firstLiveLeg zero)).typeClass → selected.support := fun sequence ↦
    ⟨D.blockAddress sequence.1,
      D.blockAddress_mem_selectedSupport index profile hzero hcomplement sequence.1
        (((profile (firstLiveLeg zero)).isConsistent_iff_mem_typeClass sequence.1).mpr
          sequence.2)⟩
  have hleft : Function.LeftInverse backward forward := by
    intro address
    apply Subtype.ext
    apply hshared' (backward (forward address)).2 address.2
    apply (positiveWordEquiv (A (firstLiveLeg zero)) n).injective
    apply funext
    intro sample
    apply hencodeFirst
    have hfirst := D.encoded_first_blockAddress (forward address).1
    exact congrFun hfirst sample
  have hright : Function.RightInverse backward forward := by
    intro sequence
    apply Subtype.ext
    exact D.encoded_first_blockAddress sequence.1
  exact
    { toFun := forward
      invFun := backward
      left_inv := hleft
      right_inv := hright }

/-- Cardinal form of `selectedSupportEquivTypeClass_of_orientedZero`. -/
theorem card_selectEncodedCompleteSplitProfiles_orientedZero_eq_card_typeClass
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
    (P.selectEncodedCompleteSplitProfiles encode index profile).support.card =
      (profile (firstLiveLeg zero)).typeClass.card := by
  simpa only [Fintype.card_coe] using Fintype.card_congr
    (selectedSupportEquivTypeClass_of_orientedZero
      P encode zero hencodeFirst D index profile hzero hcomplement hshared)

end AlgebraicComplexity
