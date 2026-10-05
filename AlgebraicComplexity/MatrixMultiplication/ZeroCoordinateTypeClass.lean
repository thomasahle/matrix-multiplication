/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.InterfaceTensorSelectionCore
import AlgebraicComplexity.Tensor.PartitionedPowerSupportDecodeCore

/-!
# Exact type-class counting on a zero-coordinate interface

A zero-coordinate constituent of a tight partition has only two live legs.  If every split word
has a supported lift whose live labels encode that word and its digitwise complement, then an
exact complementary pair of complete-split profiles selects precisely one supported address for
every word in either type class.

The hypotheses below are deliberately local.  `ZeroCoordinateCompleteFiberData` contains one
supported source letter for each split word and three literal encoding equations.  It does not
contain a degeneration, an assembled tensor, or a cardinality assertion.  The main theorem
derives the selected-support cardinality from those per-letter equations and the generic
zero-coordinate support theorem.
-/

namespace AlgebraicComplexity

open Tensor

universe u v w

variable {K : Type u} [CommSemiring K]
variable {A : Leg → Type w} [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]
variable {V : ∀ c, A c → Type (max u v)}
variable [∀ c a, AddCommMonoid (V c a)] [∀ c a, Module K (V c a)]
variable {depth n : ℕ}

/-- Per-letter completeness of the zero-`Z` fibre.  Each split word has an explicitly supported
source address whose `X`, `Y`, and `Z` encodings are respectively the word, its complement, and
zero. -/
structure ZeroCoordinateCompleteFiberData
    (P : PartitionedTensor (K := K) (A := A) V)
    (encode : ∀ c, A c → SplitWord depth) where
  lift : SplitWord depth → P.support
  encode_x : ∀ word, encode .X ((lift word).1 .X) = word
  encode_y : ∀ word,
    encode .Y ((lift word).1 .Y) = complementSplitWord word
  encode_z : ∀ word, encode .Z ((lift word).1 .Z) = 0

namespace ZeroCoordinateCompleteFiberData

variable {P : PartitionedTensor (K := K) (A := A) V}
variable {encode : ∀ c, A c → SplitWord depth}

/-- Lift a finite split-word sequence letterwise to a supported source word. -/
noncomputable def sourceWord
    (D : ZeroCoordinateCompleteFiberData P encode)
    (sequence : Fin (n + 1) → SplitWord depth) : PositiveWord P.support n :=
  (positiveWordEquiv P.support n).symm (D.lift ∘ sequence)

/-- Transpose a lifted source word into the three block labels of the positive power. -/
noncomputable def blockAddress
    (D : ZeroCoordinateCompleteFiberData P encode)
    (sequence : Fin (n + 1) → SplitWord depth) :
    BlockAddress (fun c ↦ PositiveWord (A c) n) :=
  positiveSupportWordBlockAddress P.support n (D.sourceWord sequence)

@[simp] theorem encoded_x_blockAddress
    (D : ZeroCoordinateCompleteFiberData P encode)
    (sequence : Fin (n + 1) → SplitWord depth) :
    encode .X ∘ positiveWordEquiv (A .X) n (D.blockAddress sequence .X) = sequence := by
  funext sample
  change encode .X
    (positiveWordEquiv (A .X) n
      (positiveSupportWordBlockAddress P.support n (D.sourceWord sequence) .X) sample) = _
  rw [congrFun
    (positiveWordEquiv_positiveSupportWordBlockAddress_recursive
      P.support n (D.sourceWord sequence) .X) sample]
  change encode .X
      ((positiveWordEquiv P.support n
        ((positiveWordEquiv P.support n).symm (D.lift ∘ sequence)) sample).1 .X) = _
  rw [Equiv.apply_symm_apply]
  exact D.encode_x (sequence sample)

@[simp] theorem encoded_y_blockAddress
    (D : ZeroCoordinateCompleteFiberData P encode)
    (sequence : Fin (n + 1) → SplitWord depth) :
    encode .Y ∘ positiveWordEquiv (A .Y) n (D.blockAddress sequence .Y) =
      complementSplitWord ∘ sequence := by
  funext sample
  change encode .Y
    (positiveWordEquiv (A .Y) n
      (positiveSupportWordBlockAddress P.support n (D.sourceWord sequence) .Y) sample) = _
  rw [congrFun
    (positiveWordEquiv_positiveSupportWordBlockAddress_recursive
      P.support n (D.sourceWord sequence) .Y) sample]
  change encode .Y
      ((positiveWordEquiv P.support n
        ((positiveWordEquiv P.support n).symm (D.lift ∘ sequence)) sample).1 .Y) = _
  rw [Equiv.apply_symm_apply]
  exact D.encode_y (sequence sample)

@[simp] theorem encoded_z_blockAddress
    (D : ZeroCoordinateCompleteFiberData P encode)
    (sequence : Fin (n + 1) → SplitWord depth) :
    encode .Z ∘ positiveWordEquiv (A .Z) n (D.blockAddress sequence .Z) = 0 := by
  funext sample
  change encode .Z
    (positiveWordEquiv (A .Z) n
      (positiveSupportWordBlockAddress P.support n (D.sourceWord sequence) .Z) sample) = _
  rw [congrFun
    (positiveWordEquiv_positiveSupportWordBlockAddress_recursive
      P.support n (D.sourceWord sequence) .Z) sample]
  change encode .Z
      ((positiveWordEquiv P.support n
        ((positiveWordEquiv P.support n).symm (D.lift ∘ sequence)) sample).1 .Z) = _
  rw [Equiv.apply_symm_apply]
  exact D.encode_z (sequence sample)

end ZeroCoordinateCompleteFiberData

variable {P : PartitionedTensor (K := K) (A := A) V}
variable {encode : ∀ c, A c → SplitWord depth}

/-- Complementing every letter of a word transports its exact multiplicity through the
involution. -/
theorem multiplicity_comp_complementSplitWord
    (sequence : Fin (n + 1) → SplitWord depth) (word : SplitWord depth) :
    WordType.multiplicity (complementSplitWord ∘ sequence) word =
      WordType.multiplicity sequence (complementSplitWord word) := by
  classical
  unfold WordType.multiplicity
  congr 1
  ext sample
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Function.comp_apply]
  constructor
  · intro h
    have := congrArg complementSplitWord h
    simpa using this
  · intro h
    rw [h, complementSplitWord_complementSplitWord]

/-- A complete-split profile of total weight zero is necessarily the constant-zero type. -/
theorem CompleteSplitProfile.isConsistent_zero_of_total_eq_zero
    (profile : CompleteSplitProfile depth total samples) (htotal : total = 0) :
    profile.IsConsistent (fun _ : Fin samples ↦ (0 : SplitWord depth)) := by
  classical
  have hother : ∀ word : SplitWord depth, word ≠ 0 → profile.counts word = 0 := by
    intro word hword
    by_contra hcount
    have hweight := profile.supported word hcount
    have : word = 0 := splitWord_eq_zero_of_weight_eq_zero word
      (hweight.trans htotal)
    exact hword this
  have hzero : profile.counts 0 = samples := by
    have hsum := WordType.mem_types.mp profile.isType
    have hsumzero : (∑ word, profile.counts word) = profile.counts 0 :=
      Finset.sum_eq_single 0
      (fun word _ hword ↦ hother word hword)
      (fun hzeroMem ↦ False.elim (hzeroMem (Finset.mem_univ 0)))
    exact hsumzero.symm.trans hsum
  unfold CompleteSplitProfile.IsConsistent
  funext word
  unfold WordType.multiplicity
  by_cases hword : word = 0
  · subst word
    simpa using hzero.symm
  · have hzeroWord : (0 : SplitWord depth) ≠ word := Ne.symm hword
    simp [hzeroWord, hother word hword]

/-- The address constructed from any `X`-profile word belongs to the exact selected support.
The only profile relation used is literal complementarity of the `Y` counts. -/
theorem ZeroCoordinateCompleteFiberData.blockAddress_mem_selectedSupport
    (D : ZeroCoordinateCompleteFiberData P encode)
    (index : LevelConstituentIndex depth)
    (profile : ∀ c, CompleteSplitProfile depth (index.count c) (n + 1))
    (hz : index.count .Z = 0)
    (hcomplement : ∀ word,
      (profile .Y).counts word =
        (profile .X).counts (complementSplitWord word))
    (sequence : Fin (n + 1) → SplitWord depth)
    (hsequence : (profile .X).IsConsistent sequence) :
    D.blockAddress sequence ∈
      (P.selectEncodedCompleteSplitProfiles encode index profile).support := by
  rw [P.mem_selectEncodedCompleteSplitProfiles_support]
  refine ⟨?_, ?_⟩
  · exact P.positiveSupportWordBlockAddress_mem_positivePower_support_recursive n
      (D.sourceWord sequence)
  · intro c
    cases c with
    | X => simpa using hsequence
    | Y =>
        rw [D.encoded_y_blockAddress]
        unfold CompleteSplitProfile.IsConsistent at hsequence ⊢
        funext word
        rw [multiplicity_comp_complementSplitWord, hcomplement, ← hsequence]
    | Z =>
        rw [D.encoded_z_blockAddress]
        exact (profile .Z).isConsistent_zero_of_total_eq_zero hz

/-- **Exact zero-coordinate type-class count.**  Under a complete per-letter zero fibre and
complementary exact live profiles, the selected support is in bijection with the `X` type class.
No representative selection and no asymptotic estimate occurs in this theorem. -/
theorem card_selectEncodedCompleteSplitProfiles_zero_eq_card_typeClass
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
    (P.selectEncodedCompleteSplitProfiles encode index profile).support.card =
      (profile .X).typeClass.card := by
  classical
  let selected := P.selectEncodedCompleteSplitProfiles encode index profile
  have hshared' : Set.InjOn (fun address ↦ address .X)
      (selected.support : Set (BlockAddress fun c ↦ PositiveWord (A c) n)) := by
    simpa [selected] using hshared
  let forward : selected.support → (profile .X).typeClass := fun address ↦
    ⟨encode .X ∘ positiveWordEquiv (A .X) n (address.1 .X), by
      rw [← CompleteSplitProfile.isConsistent_iff_mem_typeClass]
      have hmem :=
        (P.mem_selectEncodedCompleteSplitProfiles_support encode index profile address.1).mp
          address.2
      exact hmem.2 .X⟩
  let backward : (profile .X).typeClass → selected.support := fun sequence ↦
    ⟨D.blockAddress sequence.1,
      ZeroCoordinateCompleteFiberData.blockAddress_mem_selectedSupport
        (P := P) (encode := encode) D index profile hz hcomplement sequence.1
        (((profile .X).isConsistent_iff_mem_typeClass sequence.1).mpr sequence.2)⟩
  have hleft : Function.LeftInverse backward forward := by
    intro address
    apply Subtype.ext
    apply hshared' (backward (forward address)).2 address.2
    apply (positiveWordEquiv (A .X) n).injective
    apply funext
    intro sample
    apply hencodeX
    have hx := D.encoded_x_blockAddress (forward address).1
    exact congrFun hx sample
  have hright : Function.RightInverse backward forward := by
    intro sequence
    apply Subtype.ext
    exact D.encoded_x_blockAddress sequence.1
  let e : selected.support ≃ (profile .X).typeClass :=
    { toFun := forward
      invFun := backward
      left_inv := hleft
      right_inv := hright }
  change selected.support.card = (profile .X).typeClass.card
  simpa only [Fintype.card_coe] using Fintype.card_congr e

end AlgebraicComplexity
