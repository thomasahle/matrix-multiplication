/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Tensor.PartitionedCoarseningPower
import AlgebraicComplexity.Tensor.PartitionedExtraction
import AlgebraicComplexity.Tensor.PartitionedPowerRelabeling

set_option autoImplicit false

/-!
# Localized fine selection inside one coarsened constituent

A quotient constituent is the sum of all fine constituents in one block-address fiber.  This
module proves that it restricts to the realization of the entire fine subfamily in that fiber
satisfying an arbitrary legwise predicate.  The indexed forms preserve a previously isolated
outer family exactly.  They are the safe interface for retaining a later, inner type-class
extraction: unlike choosing one representative, no fine summand in the selected fiber is lost.
-/

namespace AlgebraicComplexity.Tensor

universe u v w x

variable {K : Type u} [CommSemiring K]
variable {A : Leg → Type w} {B : Leg → Type x}
variable [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]
variable [∀ c, Fintype (B c)] [∀ c, DecidableEq (B c)]
variable {V : ∀ c, A c → Type (max u v)}
variable [∀ c a, AddCommMonoid (V c a)] [∀ c a, Module K (V c a)]

omit [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)] in
/-- Transposing a supported joint word into its three leg words is injective. -/
theorem positiveSupportWordBlockAddress_injective
    (support : Finset (BlockAddress A)) (n : ℕ) :
    Function.Injective (positiveSupportWordBlockAddress support n) := by
  intro left right haddress
  apply (positiveWordEquiv support n).injective
  funext i
  apply Subtype.ext
  funext c
  have hc := congrArg
    (fun address ↦ positiveWordEquiv (A c) n (address c)) haddress
  rw [positiveWordEquiv_positiveSupportWordBlockAddress,
    positiveWordEquiv_positiveSupportWordBlockAddress] at hc
  exact congrFun hc i

/-- Coordinatewise alphabet maps commute with a common permutation of word positions. -/
theorem positiveWordMap_position_apply
    {I : Type*} {J : Type*} (f : I → J) (n : ℕ)
    (sigma : Equiv.Perm (Fin (n + 1))) (word : PositiveWord I n) :
    positiveWordMap f n (positiveWordPositionEquiv I n sigma word) =
      positiveWordPositionEquiv J n sigma (positiveWordMap f n word) := by
  apply (positiveWordEquiv J n).injective
  rw [positiveWordEquiv_map, positiveWordEquiv_position_apply,
    positiveWordEquiv_position_apply, positiveWordEquiv_map]
  rfl

/-- Pulling a fine word back by a position permutation maps to a fixed coarse word exactly when
the original fine word maps to the correspondingly permuted coarse word. -/
theorem positiveWordMap_position_symm_eq_iff
    {I : Type*} {J : Type*} (f : I → J) (n : ℕ)
    (sigma : Equiv.Perm (Fin (n + 1)))
    (word : PositiveWord I n) (target : PositiveWord J n) :
    positiveWordMap f n ((positiveWordPositionEquiv I n sigma).symm word) = target ↔
      positiveWordMap f n word = positiveWordPositionEquiv J n sigma target := by
  let sourceEquiv := positiveWordPositionEquiv I n sigma
  let targetEquiv := positiveWordPositionEquiv J n sigma
  have hnaturality := positiveWordMap_position_apply f n sigma (sourceEquiv.symm word)
  change positiveWordMap f n (sourceEquiv.symm word) = target ↔
    positiveWordMap f n word = targetEquiv target
  constructor
  · intro h
    calc
      positiveWordMap f n word =
          positiveWordMap f n (sourceEquiv (sourceEquiv.symm word)) := by
            rw [sourceEquiv.apply_symm_apply]
      _ = targetEquiv (positiveWordMap f n (sourceEquiv.symm word)) := hnaturality
      _ = targetEquiv target := congrArg targetEquiv h
  · intro h
    apply targetEquiv.injective
    calc
      targetEquiv (positiveWordMap f n (sourceEquiv.symm word)) =
          positiveWordMap f n (sourceEquiv (sourceEquiv.symm word)) := hnaturality.symm
      _ = positiveWordMap f n word := by rw [sourceEquiv.apply_symm_apply]
      _ = targetEquiv target := h

/-- Function representation of the inverse position action. -/
theorem positiveWordEquiv_position_symm_apply
    {I : Type*} (n : ℕ) (sigma : Equiv.Perm (Fin (n + 1)))
    (word : PositiveWord I n) :
    positiveWordEquiv I n ((positiveWordPositionEquiv I n sigma).symm word) =
      positiveWordEquiv I n word ∘ sigma.symm := by
  let e := positiveWordPositionEquiv I n sigma
  have h := congrArg (positiveWordEquiv I n) (e.apply_symm_apply word)
  rw [positiveWordEquiv_position_apply] at h
  funext i
  have hi := congrFun h (sigma.symm i)
  simpa [e, Function.comp_apply] using hi

/-- Exact word multiplicity types are invariant under inverse position relabeling. -/
theorem positiveTypeClass_position_symm_iff
    {I : Type*} [Fintype I] (n : ℕ) (a : I → ℕ)
    (sigma : Equiv.Perm (Fin (n + 1))) (word : PositiveWord I n) :
    (positiveWordPositionEquiv I n sigma).symm word ∈ positiveTypeClass I n a ↔
      word ∈ positiveTypeClass I n a := by
  rw [mem_positiveTypeClass, mem_positiveTypeClass,
    positiveWordEquiv_position_symm_apply,
    WordType.multiplicity_reindex]

/-- Apply one common position permutation to all three words of a block address. -/
def positionRelabelBlockAddress
    (A : Leg → Type*) (n : ℕ) (sigma : Equiv.Perm (Fin (n + 1))) :
    BlockAddress (fun c ↦ PositiveWord (A c) n) →
      BlockAddress (fun c ↦ PositiveWord (A c) n) :=
  fun address c ↦ positiveWordPositionEquiv (A c) n sigma (address c)

/-- Transposing a supported joint word into its three leg words commutes with a common
permutation of sample positions. -/
theorem positionRelabelBlockAddress_positiveSupportWordBlockAddress
    (support : Finset (BlockAddress A)) (n : ℕ)
    (sigma : Equiv.Perm (Fin (n + 1)))
    (word : PositiveWord support n) :
    positionRelabelBlockAddress A n sigma
        (positiveSupportWordBlockAddress support n word) =
      positiveSupportWordBlockAddress support n
        (positiveWordPositionEquiv support n sigma word) := by
  funext c
  apply (positiveWordEquiv (A c) n).injective
  change positiveWordEquiv (A c) n
      (positiveWordPositionEquiv (A c) n sigma
        (positiveSupportWordBlockAddress support n word c)) = _
  rw [positiveWordEquiv_position_apply,
    positiveWordEquiv_positiveSupportWordBlockAddress,
    positiveWordEquiv_positiveSupportWordBlockAddress,
    positiveWordEquiv_position_apply]
  rfl

/-- Send a supported fine address to its supported quotient address.  This core-level spelling
keeps localized fiber selection independent of the rational typed-leaf layer. -/
def PartitionedTensor.coarseningSupportMap
    (P : PartitionedTensor (K := K) (A := A) V)
    (f : ∀ c, A c → B c) : P.support → (P.coarsen f).support :=
  fun source ↦ ⟨coarsenBlockAddress f source.1,
    Finset.mem_image.mpr ⟨source.1, source.2, rfl⟩⟩

@[simp] theorem PartitionedTensor.coe_coarseningSupportMap
    (P : PartitionedTensor (K := K) (A := A) V)
    (f : ∀ c, A c → B c) (source : P.support) :
    (P.coarseningSupportMap f source).1 = coarsenBlockAddress f source.1 :=
  rfl

/-- Mapping a joint supported word to the quotient commutes with transposing it into three leg
words. -/
theorem PartitionedTensor.positiveSupportWordBlockAddress_coarseningSupportMap
    (P : PartitionedTensor (K := K) (A := A) V)
    (f : ∀ c, A c → B c) (n : ℕ) (word : PositiveWord P.support n) :
    positiveSupportWordBlockAddress (P.coarsen f).support n
        (positiveWordMap (P.coarseningSupportMap f) n word) =
      fun c ↦ positiveWordMap (f c) n
        (positiveSupportWordBlockAddress P.support n word c) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rcases word with ⟨word, last⟩
      funext c
      change
        (positiveSupportWordBlockAddress (P.coarsen f).support n
            (positiveWordMap (P.coarseningSupportMap f) n word) c,
          f c (last.1 c)) =
        (positiveWordMap (f c) n
            (positiveSupportWordBlockAddress P.support n word c),
          f c (last.1 c))
      rw [congrFun (ih word) c]

/-- Fine support addresses lying over one fixed coarse address. -/
def PartitionedTensor.coarseningFiberSupport
    (P : PartitionedTensor (K := K) (A := A) V)
    (f : ∀ c, A c → B c) (target : BlockAddress B) :
    Finset (BlockAddress A) :=
  P.support.filter fun source ↦ coarsenBlockAddress f source = target

@[simp] theorem PartitionedTensor.mem_coarseningFiberSupport
    (P : PartitionedTensor (K := K) (A := A) V)
    (f : ∀ c, A c → B c) (target : BlockAddress B)
    (source : BlockAddress A) :
    source ∈ P.coarseningFiberSupport f target ↔
      source ∈ P.support ∧ coarsenBlockAddress f source = target := by
  simp [PartitionedTensor.coarseningFiberSupport]

/-- The partition on the full fine alphabet localized to one coarse-address fiber. -/
def PartitionedTensor.coarseningFiber
    (P : PartitionedTensor (K := K) (A := A) V)
    (f : ∀ c, A c → B c) (target : BlockAddress B) :
    PartitionedTensor (K := K) (A := A) V :=
  P.withSupport (P.coarseningFiberSupport f target)

@[simp] theorem PartitionedTensor.coarseningFiber_support
    (P : PartitionedTensor (K := K) (A := A) V)
    (f : ∀ c, A c → B c) (target : BlockAddress B) :
    (P.coarseningFiber f target).support = P.coarseningFiberSupport f target :=
  rfl

@[simp] theorem PartitionedTensor.coarseningFiber_constituent
    (P : PartitionedTensor (K := K) (A := A) V)
    (f : ∀ c, A c → B c) (target : BlockAddress B)
    (source : BlockAddress A) :
    (P.coarseningFiber f target).constituent source = P.constituent source :=
  rfl

/-- Fine labels retained on one leg by a localized coarse-fiber selection. -/
noncomputable def coarseningFiberSelectParts
    (f : ∀ c, A c → B c) (target : BlockAddress B)
    (keep : ∀ c, A c → Prop) [∀ c a, Decidable (keep c a)]
    (c : Leg) : Finset (A c) := by
  classical
  exact Finset.univ.filter fun a ↦ f c a = target c ∧ keep c a

@[simp] theorem mem_coarseningFiberSelectParts
    (f : ∀ c, A c → B c) (target : BlockAddress B)
    (keep : ∀ c, A c → Prop) [∀ c a, Decidable (keep c a)]
    (c : Leg) (a : A c) :
    a ∈ coarseningFiberSelectParts f target keep c ↔
      f c a = target c ∧ keep c a := by
  classical
  simp [coarseningFiberSelectParts]

/-- A localized fiber followed by a legwise fine selection is exactly one Cartesian box in the
original fine partition. -/
theorem PartitionedTensor.coarseningFiber_select_eq_box
    (P : PartitionedTensor (K := K) (A := A) V)
    (f : ∀ c, A c → B c) (target : BlockAddress B)
    (keep : ∀ c, A c → Prop) [∀ c a, Decidable (keep c a)] :
    (P.coarseningFiber f target).select keep =
      P.box (coarseningFiberSelectParts f target keep) := by
  classical
  apply PartitionedTensor.ext
  · ext address
    simp only [PartitionedTensor.mem_select_support,
      PartitionedTensor.coarseningFiber_support,
      PartitionedTensor.mem_coarseningFiberSupport,
      PartitionedTensor.mem_box_support,
      mem_coarseningFiberSelectParts]
    constructor
    · rintro ⟨⟨hsource, hmap⟩, hkeep⟩
      exact ⟨hsource, fun c ↦ ⟨congrFun hmap c, hkeep c⟩⟩
    · rintro ⟨hsource, hparts⟩
      exact ⟨⟨hsource, funext fun c ↦ (hparts c).1⟩,
        fun c ↦ (hparts c).2⟩
  · rfl

/-- Position relabeling transports localized box parts, provided the fine keep predicate is
invariant under that same relabeling. -/
theorem relabelParts_coarseningFiberSelectParts_positiveWordMap
    (f : ∀ c, A c → B c) (n : ℕ)
    (target : BlockAddress (fun c ↦ PositiveWord (B c) n))
    (keep : ∀ c, PositiveWord (A c) n → Prop)
    [∀ c word, Decidable (keep c word)]
    (sigma : Equiv.Perm (Fin (n + 1)))
    (hkeep : ∀ c word,
      keep c ((positiveWordPositionEquiv (A c) n sigma).symm word) ↔ keep c word) :
    relabelParts
        (fun c ↦ positiveWordPositionEquiv (A c) n sigma)
        (coarseningFiberSelectParts
          (fun c ↦ positiveWordMap (f c) n) target keep) =
      coarseningFiberSelectParts (fun c ↦ positiveWordMap (f c) n)
        (positionRelabelBlockAddress B n sigma target) keep := by
  classical
  funext c
  ext word
  rw [mem_relabelParts, mem_coarseningFiberSelectParts,
    mem_coarseningFiberSelectParts]
  exact and_congr
    (positiveWordMap_position_symm_eq_iff (f c) n sigma word (target c))
    (hkeep c word)

namespace Isomorphic

/-- A common position permutation transports the whole localized selected tensor over one
coarse address to the corresponding tensor over the permuted coarse address. -/
theorem positivePower_localizedCoarseningFiberSelect_position
    (P : PartitionedTensor (K := K) (A := A) V)
    (f : ∀ c, A c → B c) (n : ℕ)
    (target : BlockAddress (fun c ↦ PositiveWord (B c) n))
    (keep : ∀ c, PositiveWord (A c) n → Prop)
    [∀ c word, Decidable (keep c word)]
    (sigma : Equiv.Perm (Fin (n + 1)))
    (hkeep : ∀ c word,
      keep c ((positiveWordPositionEquiv (A c) n sigma).symm word) ↔ keep c word) :
    Isomorphic
      ((((P.positivePower n).coarseningFiber
          (fun c ↦ positiveWordMap (f c) n) target).select keep).realize)
      ((((P.positivePower n).coarseningFiber
          (fun c ↦ positiveWordMap (f c) n)
          (positionRelabelBlockAddress B n sigma target)).select keep).realize) := by
  let R := P.positivePower n
  let r := PartitionedTensor.StructureRelabeling.positivePowerPositionRelabeling
    P n sigma
  let parts := coarseningFiberSelectParts
    (fun c ↦ positiveWordMap (f c) n) target keep
  have hparts : relabelParts r.partEquiv parts =
      coarseningFiberSelectParts (fun c ↦ positiveWordMap (f c) n)
        (positionRelabelBlockAddress B n sigma target) keep := by
    rw [show r.partEquiv =
        fun c ↦ positiveWordPositionEquiv (A c) n sigma by
      funext c
      exact PartitionedTensor.StructureRelabeling.positivePowerPositionRelabeling_partEquiv
        P n sigma c]
    exact relabelParts_coarseningFiberSelectParts_positiveWordMap
      f n target keep sigma hkeep
  have h := r.box_isomorphic parts
  rw [hparts] at h
  simpa only [R, parts,
    PartitionedTensor.coarseningFiber_select_eq_box] using h

/-- Exact fine marginal types satisfy the invariance premise automatically. -/
theorem positivePower_localizedCoarseningFiberTypes_position
    (P : PartitionedTensor (K := K) (A := A) V)
    (f : ∀ c, A c → B c) (n : ℕ)
    (target : BlockAddress (fun c ↦ PositiveWord (B c) n))
    (fineType : ∀ c, A c → ℕ)
    (sigma : Equiv.Perm (Fin (n + 1))) :
    Isomorphic
      ((((P.positivePower n).coarseningFiber
          (fun c ↦ positiveWordMap (f c) n) target).select
        (fun c word ↦ word ∈ positiveTypeClass (A c) n (fineType c))).realize)
      ((((P.positivePower n).coarseningFiber
          (fun c ↦ positiveWordMap (f c) n)
          (positionRelabelBlockAddress B n sigma target)).select
        (fun c word ↦ word ∈ positiveTypeClass (A c) n (fineType c))).realize) :=
  positivePower_localizedCoarseningFiberSelect_position
    P f n target
      (fun c word ↦ word ∈ positiveTypeClass (A c) n (fineType c))
      sigma (fun c word ↦ positiveTypeClass_position_symm_iff
        n (fineType c) sigma word)

end Isomorphic

/-- Fine joint words of one exact profile mapping to a fixed coarse joint word. -/
noncomputable def PartitionedTensor.typedCoarseningFiberWords
    (P : PartitionedTensor (K := K) (A := A) V)
    (f : ∀ c, A c → B c) (n : ℕ) (profile : P.support → ℕ)
    (coarseWord : PositiveWord (P.coarsen f).support n) :=
  WordType.typedWordMapFiber (P.coarseningSupportMap f) profile
    (positiveWordEquiv (P.coarsen f).support n coarseWord)

/-- Interpret a function-valued member of an exact typed coarsening fiber as the corresponding
positive word over the fine support alphabet. -/
noncomputable def PartitionedTensor.typedCoarseningFiberPositiveWord
    (P : PartitionedTensor (K := K) (A := A) V)
    (f : ∀ c, A c → B c) (n : ℕ) (profile : P.support → ℕ)
    (coarseWord : PositiveWord (P.coarsen f).support n)
    (word : P.typedCoarseningFiberWords f n profile coarseWord) :
    PositiveWord P.support n :=
  (positiveWordEquiv P.support n).symm word.1

/-- Exact typed lifts as a finite family of positive fine-support words. -/
noncomputable def PartitionedTensor.typedCoarseningFiberPositiveWords
    (P : PartitionedTensor (K := K) (A := A) V)
    (f : ∀ c, A c → B c) (n : ℕ) (profile : P.support → ℕ)
    (coarseWord : PositiveWord (P.coarsen f).support n) :
    Finset (PositiveWord P.support n) :=
  Finset.univ.image (P.typedCoarseningFiberPositiveWord f n profile coarseWord)

/-- The function-to-positive-word conversion on a typed fiber is injective. -/
theorem PartitionedTensor.typedCoarseningFiberPositiveWord_injective
    (P : PartitionedTensor (K := K) (A := A) V)
    (f : ∀ c, A c → B c) (n : ℕ) (profile : P.support → ℕ)
    (coarseWord : PositiveWord (P.coarsen f).support n) :
    Function.Injective
      (P.typedCoarseningFiberPositiveWord f n profile coarseWord) := by
  intro left right h
  apply Subtype.ext
  exact (positiveWordEquiv P.support n).symm.injective h

/-- Converting an exact typed fiber to positive words preserves its cardinality. -/
theorem PartitionedTensor.card_typedCoarseningFiberPositiveWords
    (P : PartitionedTensor (K := K) (A := A) V)
    (f : ∀ c, A c → B c) (n : ℕ) (profile : P.support → ℕ)
    (coarseWord : PositiveWord (P.coarsen f).support n) :
    (P.typedCoarseningFiberPositiveWords f n profile coarseWord).card =
      (P.typedCoarseningFiberWords f n profile coarseWord).card := by
  rw [PartitionedTensor.typedCoarseningFiberPositiveWords,
    Finset.card_image_of_injective _
      (P.typedCoarseningFiberPositiveWord_injective f n profile coarseWord),
    Finset.card_univ, Fintype.card_coe]

/-- A positive fine word is in the converted typed fiber exactly when it has the prescribed
fine joint type and maps to the fixed coarse word. -/
theorem PartitionedTensor.mem_typedCoarseningFiberPositiveWords_iff
    (P : PartitionedTensor (K := K) (A := A) V)
    (f : ∀ c, A c → B c) (n : ℕ) (profile : P.support → ℕ)
    (coarseWord : PositiveWord (P.coarsen f).support n)
    (fineWord : PositiveWord P.support n) :
    fineWord ∈ P.typedCoarseningFiberPositiveWords f n profile coarseWord ↔
      WordType.multiplicity (positiveWordEquiv P.support n fineWord) = profile ∧
      positiveWordMap (P.coarseningSupportMap f) n fineWord = coarseWord := by
  classical
  rw [PartitionedTensor.typedCoarseningFiberPositiveWords, Finset.mem_image]
  constructor
  · rintro ⟨word, _hword, rfl⟩
    have htyped := WordType.mem_typedWordMapFiber.mp word.2
    constructor
    · simpa [PartitionedTensor.typedCoarseningFiberPositiveWord] using htyped.1
    · apply (positiveWordEquiv (P.coarsen f).support n).injective
      rw [positiveWordEquiv_map]
      simpa [PartitionedTensor.typedCoarseningFiberPositiveWord] using htyped.2
  · rintro ⟨htype, hmap⟩
    let functionWord := positiveWordEquiv P.support n fineWord
    have hfunctionMap : P.coarseningSupportMap f ∘ functionWord =
        positiveWordEquiv (P.coarsen f).support n coarseWord := by
      have h := congrArg (positiveWordEquiv (P.coarsen f).support n) hmap
      rw [positiveWordEquiv_map] at h
      exact h
    let typedWord : P.typedCoarseningFiberWords f n profile coarseWord :=
      ⟨functionWord, WordType.mem_typedWordMapFiber.mpr ⟨htype, hfunctionMap⟩⟩
    refine ⟨typedWord, Finset.mem_univ _, ?_⟩
    exact (positiveWordEquiv P.support n).symm_apply_apply fineWord

/-- Supported fine words whose transposed address belongs to a prescribed subfamily of the
positive-power support. -/
noncomputable def PartitionedTensor.positiveWordsOverSupport
    (P : PartitionedTensor (K := K) (A := A) V) (n : ℕ)
    (selected : Finset (BlockAddress (fun c ↦ PositiveWord (A c) n))) :
    Finset (PositiveWord P.support n) :=
  Finset.univ.filter fun word ↦
    positiveSupportWordBlockAddress P.support n word ∈ selected

@[simp] theorem PartitionedTensor.mem_positiveWordsOverSupport
    (P : PartitionedTensor (K := K) (A := A) V) (n : ℕ)
    (selected : Finset (BlockAddress (fun c ↦ PositiveWord (A c) n)))
    (word : PositiveWord P.support n) :
    word ∈ P.positiveWordsOverSupport n selected ↔
      positiveSupportWordBlockAddress P.support n word ∈ selected := by
  classical
  simp [PartitionedTensor.positiveWordsOverSupport]

/-- If a block-address family lies in the positive-power support, transposing all supported
words over that family recovers it exactly. -/
theorem PartitionedTensor.image_positiveWordsOverSupport_eq
    (P : PartitionedTensor (K := K) (A := A) V) (n : ℕ)
    (selected : Finset (BlockAddress (fun c ↦ PositiveWord (A c) n)))
    (hselected : selected ⊆ (P.positivePower n).support) :
    (P.positiveWordsOverSupport n selected).image
        (positiveSupportWordBlockAddress P.support n) = selected := by
  classical
  ext address
  rw [Finset.mem_image]
  constructor
  · rintro ⟨word, hword, rfl⟩
    exact (P.mem_positiveWordsOverSupport n selected word).mp hword
  · intro haddress
    obtain ⟨word, hword⟩ :=
      P.exists_positiveSupportWord_of_mem_positivePower_support n
        (hselected haddress)
    refine ⟨word, ?_, hword⟩
    exact (P.mem_positiveWordsOverSupport n selected word).mpr
      (hword.symm ▸ haddress)

/-- Transpose one typed fine lift into its fine positive-power block address. -/
noncomputable def PartitionedTensor.typedCoarseningFiberAddress
    (P : PartitionedTensor (K := K) (A := A) V)
    (f : ∀ c, A c → B c) (n : ℕ) (profile : P.support → ℕ)
    (coarseWord : PositiveWord (P.coarsen f).support n)
    (word : P.typedCoarseningFiberWords f n profile coarseWord) :
    BlockAddress (fun c ↦ PositiveWord (A c) n) :=
  positiveSupportWordBlockAddress P.support n
    ((positiveWordEquiv P.support n).symm word.1)

/-- Distinct typed fine lifts give distinct fine block addresses. -/
theorem PartitionedTensor.typedCoarseningFiberAddress_injective
    (P : PartitionedTensor (K := K) (A := A) V)
    (f : ∀ c, A c → B c) (n : ℕ) (profile : P.support → ℕ)
    (coarseWord : PositiveWord (P.coarsen f).support n) :
    Function.Injective (P.typedCoarseningFiberAddress f n profile coarseWord) := by
  intro left right h
  apply Subtype.ext
  apply (positiveWordEquiv P.support n).symm.injective
  exact positiveSupportWordBlockAddress_injective P.support n h

/-- Fine positive-power addresses represented by the exact typed quotient fiber. -/
noncomputable def PartitionedTensor.typedCoarseningFiberAddresses
    (P : PartitionedTensor (K := K) (A := A) V)
    (f : ∀ c, A c → B c) (n : ℕ) (profile : P.support → ℕ)
    (coarseWord : PositiveWord (P.coarsen f).support n) :
    Finset (BlockAddress (fun c ↦ PositiveWord (A c) n)) :=
  Finset.univ.image (P.typedCoarseningFiberAddress f n profile coarseWord)

/-- The address realization of a typed quotient fiber preserves its exact cardinality. -/
theorem PartitionedTensor.card_typedCoarseningFiberAddresses
    (P : PartitionedTensor (K := K) (A := A) V)
    (f : ∀ c, A c → B c) (n : ℕ) (profile : P.support → ℕ)
    (coarseWord : PositiveWord (P.coarsen f).support n) :
    (P.typedCoarseningFiberAddresses f n profile coarseWord).card =
      (P.typedCoarseningFiberWords f n profile coarseWord).card := by
  rw [PartitionedTensor.typedCoarseningFiberAddresses,
    Finset.card_image_of_injective _
      (P.typedCoarseningFiberAddress_injective f n profile coarseWord),
    Finset.card_univ, Fintype.card_coe]

/-- Every exact typed lift belongs to the localized fine selection with the profile's three
coordinate marginals.  This connects the quantitative `typedWordMapFiber` count exactly to the
semantic output of `coarsen_constituent_to_fineFiberSelect`. -/
theorem PartitionedTensor.typedCoarseningFiberAddresses_subset_localizedMarginalTypes
    (P : PartitionedTensor (K := K) (A := A) V)
    (f : ∀ c, A c → B c) (n : ℕ) (profile : P.support → ℕ)
    (coarseWord : PositiveWord (P.coarsen f).support n) :
    P.typedCoarseningFiberAddresses f n profile coarseWord ⊆
      (((P.positivePower n).coarseningFiber
          (fun c ↦ positiveWordMap (f c) n)
          (positiveSupportWordBlockAddress (P.coarsen f).support n coarseWord)).select
        (fun c word ↦ word ∈ positiveTypeClass (A c) n
          (WordType.mappedType (fun s : P.support ↦ s.1 c) profile))).support := by
  classical
  intro address haddress
  obtain ⟨word, _hwordUniv, rfl⟩ := Finset.mem_image.mp haddress
  let fineWord : PositiveWord P.support n :=
    (positiveWordEquiv P.support n).symm word.1
  have htyped := WordType.mem_typedWordMapFiber.mp word.2
  have hfineType : WordType.multiplicity
      (positiveWordEquiv P.support n fineWord) = profile := by
    simpa [fineWord] using htyped.1
  have hmapWord : positiveWordMap (P.coarseningSupportMap f) n fineWord = coarseWord := by
    apply (positiveWordEquiv (P.coarsen f).support n).injective
    rw [positiveWordEquiv_map]
    simpa [fineWord] using htyped.2
  rw [PartitionedTensor.mem_select_support,
    PartitionedTensor.coarseningFiber_support,
    PartitionedTensor.mem_coarseningFiberSupport]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [P.positivePower_support_eq_image_positiveSupportWordBlockAddress n]
    exact Finset.mem_image.mpr ⟨fineWord, Finset.mem_univ _, rfl⟩
  · change
      (fun c ↦ positiveWordMap (f c) n
        (positiveSupportWordBlockAddress P.support n fineWord c)) = _
    rw [← P.positiveSupportWordBlockAddress_coarseningSupportMap f n fineWord,
      hmapWord]
  · intro c
    rw [mem_positiveTypeClass,
      show P.typedCoarseningFiberAddress f n profile coarseWord word =
          positiveSupportWordBlockAddress P.support n fineWord from rfl]
    rw [positiveWordEquiv_positiveSupportWordBlockAddress]
    change WordType.multiplicity
      ((fun s : P.support ↦ s.1 c) ∘ positiveWordEquiv P.support n fineWord) = _
    rw [WordType.multiplicity_comp_eq_mappedType, hfineType]

theorem PartitionedTensor.coarsen_coarseningFiber_support
    (P : PartitionedTensor (K := K) (A := A) V)
    (f : ∀ c, A c → B c) (target : BlockAddress B)
    (htarget : target ∈ (P.coarsen f).support) :
    ((P.coarseningFiber f target).coarsen f).support = {target} := by
  classical
  ext other
  simp only [PartitionedTensor.coarsen_support, Finset.mem_image,
    PartitionedTensor.coarseningFiber_support,
    PartitionedTensor.mem_coarseningFiberSupport, Finset.mem_singleton]
  constructor
  · rintro ⟨source, ⟨_hsource, hmap⟩, rfl⟩
    exact hmap
  · rintro rfl
    rw [PartitionedTensor.coarsen_support] at htarget
    obtain ⟨source, hsource, hmap⟩ := Finset.mem_image.mp htarget
    exact ⟨source, ⟨hsource, hmap⟩, hmap⟩

theorem PartitionedTensor.coarsen_coarseningFiber_constituent
    (P : PartitionedTensor (K := K) (A := A) V)
    (f : ∀ c, A c → B c) (target : BlockAddress B) :
    ((P.coarseningFiber f target).coarsen f).constituent target =
      (P.coarsen f).constituent target := by
  classical
  simp only [PartitionedTensor.coarsen_constituent]
  rw [coarsenedConstituent_eq_sum_filter,
    coarsenedConstituent_eq_sum_filter]
  simp only [PartitionedTensor.coarseningFiber_support,
    PartitionedTensor.coarseningFiber_constituent,
    PartitionedTensor.coarseningFiberSupport, Finset.filter_filter]
  apply Finset.sum_congr
  · ext source
    simp
  · intro source hsource
    have hmap : coarsenBlockAddress f source = target :=
      (Finset.mem_filter.mp hsource).2
    rw [coarsenedTerm_eq_map_of_eq _ _ _ _ hmap,
      coarsenedTerm_eq_map_of_eq _ _ _ _ hmap]
    rfl

namespace Restricts

/-- The two block presentations of a power/coarsening have exactly the same quotient support. -/
theorem positivePower_coarsen_support_eq
    (P : PartitionedTensor (K := K) (A := A) V)
    (f : ∀ c, A c → B c) (n : ℕ) :
    (P.coarsenedPositivePower f n).support =
      ((P.positivePower n).coarsen
        (fun c ↦ positiveWordMap (f c) n)).support := by
  have h := congrArg PartitionedTensor.support
    (P.positivePower_coarsen_reindex f n)
  change
    (P.coarsenedPositivePower f n).support.map
        (blockAddressCongr (fun _ ↦ Equiv.refl _)).toEmbedding = _ at h
  have hsupport :
      (P.coarsenedPositivePower f n).support.map
          (blockAddressCongr (fun _ ↦ Equiv.refl _)).toEmbedding =
        (P.coarsenedPositivePower f n).support := by
    ext target
    simp [blockAddressCongr]
  rw [hsupport] at h
  exact h

/-- Blockwise form of power/coarsening distributivity. -/
theorem positivePower_coarsen_constituent
    (P : PartitionedTensor (K := K) (A := A) V)
    (f : ∀ c, A c → B c) (n : ℕ)
    (target : BlockAddress (fun c ↦ PositiveWord (B c) n)) :
    Restricts
      ((P.coarsenedPositivePower f n).constituent target)
      (((P.positivePower n).coarsen
        (fun c ↦ positiveWordMap (f c) n)).constituent target) := by
  let blockEquiv := positivePowerCoarseningBlockEquiv
    (K := K) (V := V) f n
  refine ⟨fun c ↦ (blockEquiv c (target c)).toLinearMap, ?_⟩
  have h := congrArg (fun Q ↦ Q.constituent target)
    (P.positivePower_coarsen_reindex f n)
  change
    map (fun c ↦ (blockEquiv c (target c)).toLinearMap)
        ((P.coarsenedPositivePower f n).constituent target) = _ at h
  exact h

/-- A single whole coarse constituent restricts to the realization of every fine constituent
in its fiber.  No representative is chosen and no fiber cardinality is discarded. -/
theorem coarsen_constituent_to_fineFiber
    (P : PartitionedTensor (K := K) (A := A) V)
    (f : ∀ c, A c → B c) (target : BlockAddress B)
    (htarget : target ∈ (P.coarsen f).support) :
    Restricts ((P.coarsen f).constituent target)
      (P.coarseningFiber f target).realize := by
  classical
  let R := P.coarseningFiber f target
  have hsupport : (R.coarsen f).support = {target} :=
    P.coarsen_coarseningFiber_support f target htarget
  have hconstituent : (R.coarsen f).constituent target =
      (P.coarsen f).constituent target :=
    P.coarsen_coarseningFiber_constituent f target
  have hsingle : Restricts ((P.coarsen f).constituent target)
      (R.coarsen f).realize := by
    refine ⟨blockInclude (K := K)
      (V := CoarsenedBlockSpace (V := V) f) target, ?_⟩
    unfold PartitionedTensor.realize realizePartition
    rw [hsupport]
    simp only [Finset.sum_singleton]
    rw [hconstituent]
  exact hsingle.trans (Isomorphic.partitionedCoarsen R f).symm.restricts

/-- A fixed coarse constituent restricts to the entire fine subfamily in its fiber satisfying
an arbitrary legwise fine-label predicate.  This is the localized selected-tensor interface:
it preserves all inner type-class summands available in that coarse fiber. -/
theorem coarsen_constituent_to_fineFiberSelect
    (P : PartitionedTensor (K := K) (A := A) V)
    (f : ∀ c, A c → B c) (target : BlockAddress B)
    (htarget : target ∈ (P.coarsen f).support)
    (keep : ∀ c, A c → Prop) [∀ c a, Decidable (keep c a)] :
    Restricts ((P.coarsen f).constituent target)
      ((P.coarseningFiber f target).select keep).realize :=
  (coarsen_constituent_to_fineFiber P f target htarget).trans
    (partitionedSelect (P.coarseningFiber f target) keep)

/-- Indexed outer-copy form of the localized selected-tensor bridge.  The outer coarse index is
preserved exactly, while every output retains its whole localized fine type-selected tensor. -/
theorem indexedDirectSum_coarsen_constituent_to_fineFiberSelect
    {I : Type*} [Fintype I]
    (P : PartitionedTensor (K := K) (A := A) V)
    (f : ∀ c, A c → B c) (target : I → BlockAddress B)
    (htarget : ∀ i, target i ∈ (P.coarsen f).support)
    (keep : ∀ c, A c → Prop) [∀ c a, Decidable (keep c a)] :
    Restricts
      (Tensor.indexedDirectSum (fun i ↦ (P.coarsen f).constituent (target i)))
      (Tensor.indexedDirectSum (fun i ↦
        ((P.coarseningFiber f (target i)).select keep).realize)) := by
  apply indexedDirectSum
  intro i
  exact coarsen_constituent_to_fineFiberSelect P f (target i) (htarget i) keep

/-- Quotient-first power form of the localized selected-tensor bridge.  This is the semantic
interface used after hashing has isolated constituents of `(P.coarsen f).positivePower n`. -/
theorem coarsenedPositivePower_constituent_to_fineFiberSelect
    (P : PartitionedTensor (K := K) (A := A) V)
    (f : ∀ c, A c → B c) (n : ℕ)
    (target : BlockAddress (fun c ↦ PositiveWord (B c) n))
    (htarget : target ∈ (P.coarsenedPositivePower f n).support)
    (keep : ∀ c, PositiveWord (A c) n → Prop)
    [∀ c word, Decidable (keep c word)] :
    Restricts
      ((P.coarsenedPositivePower f n).constituent target)
      ((((P.positivePower n).coarseningFiber
        (fun c ↦ positiveWordMap (f c) n) target).select keep).realize) := by
  apply (positivePower_coarsen_constituent P f n target).trans
  apply coarsen_constituent_to_fineFiberSelect
  rw [← positivePower_coarsen_support_eq P f n]
  exact htarget

/-- Indexed quotient-first form.  Every isolated coarse output retains all fine selected
constituents in its own quotient fiber; the outer index is unchanged. -/
theorem indexedDirectSum_coarsenedPositivePower_constituent_to_fineFiberSelect
    {I : Type*} [Fintype I]
    (P : PartitionedTensor (K := K) (A := A) V)
    (f : ∀ c, A c → B c) (n : ℕ)
    (target : I → BlockAddress (fun c ↦ PositiveWord (B c) n))
    (htarget : ∀ i, target i ∈ (P.coarsenedPositivePower f n).support)
    (keep : ∀ c, PositiveWord (A c) n → Prop)
    [∀ c word, Decidable (keep c word)] :
    Restricts
      (Tensor.indexedDirectSum (fun i ↦
        (P.coarsenedPositivePower f n).constituent (target i)))
      (Tensor.indexedDirectSum (fun i ↦
        (((P.positivePower n).coarseningFiber
          (fun c ↦ positiveWordMap (f c) n) (target i)).select keep).realize)) := by
  apply indexedDirectSum
  intro i
  exact coarsenedPositivePower_constituent_to_fineFiberSelect
    P f n (target i) (htarget i) keep

end Restricts

end AlgebraicComplexity.Tensor
