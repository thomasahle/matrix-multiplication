/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Combinatorics.TwoLegHashingExtraction
import AlgebraicComplexity.Combinatorics.WordType
import AlgebraicComplexity.Tensor.PartitionedPower
import AlgebraicComplexity.Tensor.PartitionedDirectSum

/-!
# Hash models for powers of partitioned tensors

This module bridges word-indexed partitioned tensor powers to the finite legal triples consumed
by the affine-hashing extraction theorem.  A client supplies an injective field encoding of each
leg's block labels and proves that every base support address has one fixed coordinate sum.
Supported address words then become legal hashing triples automatically, while equality of hash
indices is proved equivalent to equality of the original block words.

The construction is paper-independent.  The easy and full Coppersmith--Winograd supports are
clients of this interface; neither tensor core nor the generic hashing combinatorics imports a
named tensor.

`blockAddressWordEquiv` is the legwise dictionary between the recursive `PositiveWord`
representation of block addresses used here and the function representation `Fin (n + 1) → A c`
used by `Tensor/CoordinateBlockWord.lean`; `PartitionHashEncoding.mem_support_blockAddressWordEquiv`
transports support membership across it.
-/

namespace AlgebraicComplexity

open Tensor

universe u v w x

/-- The legwise bijection between the recursive word representation of block addresses used by the
hashing interface below and the function representation `Fin (n + 1) → A c` used by
`Tensor/CoordinateBlockWord.lean`. -/
def blockAddressWordEquiv (A : Leg → Type w) (n : ℕ) :
    BlockAddress (fun c ↦ PositiveWord (A c) n) ≃ BlockAddress (fun c ↦ Fin (n + 1) → A c) :=
  Equiv.piCongrRight fun c ↦ positiveWordEquiv (A c) n

@[simp] theorem blockAddressWordEquiv_apply (A : Leg → Type w) (n : ℕ)
    (s : BlockAddress fun c ↦ PositiveWord (A c) n) (c : Leg) :
    blockAddressWordEquiv A n s c = positiveWordEquiv (A c) n (s c) := rfl

variable {R : Type u} [Field R]
variable {A : Leg → Type w} [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]

/-- Field labels making a finite partition support compatible with progression hashing. -/
structure PartitionHashEncoding (support : Finset (BlockAddress A)) where
  encode : ∀ c, A c → R
  target : R
  support_nonempty : support.Nonempty
  encode_injective : ∀ c, Function.Injective (encode c)
  legal : ∀ s ∈ support,
    encode .X (s .X) + encode .Y (s .Y) + encode .Z (s .Z) = target

namespace PartitionHashEncoding

variable {support : Finset (BlockAddress A)}

/-- Transpose a word of supported full addresses into the three original block-label words. -/
def supportWordAddress (n : ℕ) (q : PositiveWord support n) :
    BlockAddress (fun c ↦ PositiveWord (A c) n) :=
  positiveSupportWordBlockAddress support n q

omit [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)] in
/-- Reading a leg of `supportWordAddress` agrees coordinatewise with reading the corresponding
leg of each supported address in the source word. -/
theorem positiveWordEquiv_supportWordAddress
    (n : ℕ) (q : PositiveWord support n) (c : Leg) :
    positiveWordEquiv (A c) n (supportWordAddress n q c) =
      fun i ↦ (positiveWordEquiv support n q i).1 c := by
  unfold supportWordAddress
  exact positiveWordEquiv_positiveSupportWordBlockAddress support n q c

omit [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)] in
/-- Position by position, the transposed block address of a word of supported addresses is itself a
supported address. -/
theorem mem_support_blockAddressWordEquiv (n : ℕ) (q : PositiveWord support n)
    (i : Fin (n + 1)) :
    (fun c ↦ blockAddressWordEquiv A n (supportWordAddress n q) c i) ∈ support := by
  have h : (fun c ↦ blockAddressWordEquiv A n (supportWordAddress n q) c i)
      = ((positiveWordEquiv support n q i : support) : BlockAddress A) := by
    funext c
    exact congrFun (positiveWordEquiv_supportWordAddress n q c) i
  rw [h]
  exact (positiveWordEquiv support n q i).2

omit [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)] in
/-- Different supported-address words give different transposed block addresses. -/
theorem supportWordAddress_injective (n : ℕ) :
    Function.Injective (supportWordAddress (A := A) (support := support) n) := by
  intro left right h
  apply (positiveWordEquiv support n).injective
  funext i
  apply Subtype.ext
  funext c
  have hleg := congrFun h c
  have hword := congrArg (positiveWordEquiv (A c) n) hleg
  simpa [positiveWordEquiv_supportWordAddress] using congrFun hword i

/-- A supported address word, encoded coordinatewise as a legal affine-hashing triple. -/
def legalTriple (H : PartitionHashEncoding (R := R) support) (n : ℕ)
    (q : PositiveWord support n) :
    ProgressionHash.LegalTriple R (Fin (n + 1)) H.target where
  xIndex i := H.encode .X ((positiveWordEquiv support n q i).1 .X)
  yIndex i := H.encode .Y ((positiveWordEquiv support n q i).1 .Y)
  zIndex i := H.encode .Z ((positiveWordEquiv support n q i).1 .Z)
  legal i := H.legal _ (positiveWordEquiv support n q i).2

omit [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)] in
/-- The encoded hashing word on each leg is precisely the field encoding of the corresponding
transposed partition block word. -/
theorem legalTriple_legIndex_eq
    (H : PartitionHashEncoding (R := R) support) (n : ℕ)
    (q : PositiveWord support n) (c : Leg) :
    (H.legalTriple n q).legIndex c =
      H.encode c ∘ positiveWordEquiv (A c) n (supportWordAddress n q c) := by
  funext i
  have haddress := congrFun (positiveWordEquiv_supportWordAddress
    (A := A) (support := support) n q c) i
  cases c <;> simp only [ProgressionHash.LegalTriple.legIndex_X,
    ProgressionHash.LegalTriple.legIndex_Y,
    ProgressionHash.LegalTriple.legIndex_Z, legalTriple, Function.comp_apply] <;>
    rw [haddress]

omit [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)] in
/-- Equality of encoded hashing indices is equivalent to equality of the original block word on
that leg. -/
theorem legalTriple_legIndex_eq_iff
    (H : PartitionHashEncoding (R := R) support) (n : ℕ)
    (left right : PositiveWord support n) (c : Leg) :
    (H.legalTriple n left).legIndex c = (H.legalTriple n right).legIndex c ↔
      supportWordAddress n left c = supportWordAddress n right c := by
  rw [H.legalTriple_legIndex_eq n left c, H.legalTriple_legIndex_eq n right c]
  constructor
  · intro h
    apply (positiveWordEquiv (A c) n).injective
    funext i
    apply H.encode_injective c
    exact congrFun h i
  · intro h
    rw [h]

omit [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)] in
/-- The bundled legal-triple representation loses no source words. -/
theorem legalTriple_injective
    (H : PartitionHashEncoding (R := R) support) (n : ℕ) :
    Function.Injective (H.legalTriple n) := by
  intro left right h
  apply supportWordAddress_injective n
  funext c
  apply (H.legalTriple_legIndex_eq_iff n left right c).mp
  exact congrArg (fun triple ↦ triple.legIndex c) h

/-- Legal hashing targets associated to a finite family of supported-address words. -/
noncomputable def legalTargets
    (H : PartitionHashEncoding (R := R) support) (n : ℕ)
    (words : Finset (PositiveWord support n)) :
    Finset (ProgressionHash.LegalTriple R (Fin (n + 1)) H.target) := by
  classical
  exact words.image (H.legalTriple n)

omit [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)] in
/-- Passing from supported words to legal hashing targets preserves cardinality. -/
@[simp] theorem card_legalTargets
    (H : PartitionHashEncoding (R := R) support) (n : ℕ)
    (words : Finset (PositiveWord support n)) :
    (H.legalTargets n words).card = words.card := by
  classical
  unfold legalTargets
  exact Finset.card_image_of_injOn (H.legalTriple_injective n).injOn

/-- Recover the source supported-address word of an encoded legal triple.  Statements using this
function carry a membership hypothesis in `legalTargets`; outside the image its value is an
irrelevant classical default. -/
noncomputable def sourceWordOfLegalTriple
    (H : PartitionHashEncoding (R := R) support) (n : ℕ)
    (triple : ProgressionHash.LegalTriple R (Fin (n + 1)) H.target) :
    PositiveWord support n := by
  letI : Nonempty support := H.support_nonempty.to_subtype
  exact Function.invFun (H.legalTriple n) triple

omit [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)] in
@[simp] theorem sourceWordOfLegalTriple_legalTriple
    (H : PartitionHashEncoding (R := R) support) (n : ℕ)
    (q : PositiveWord support n) :
    H.sourceWordOfLegalTriple n (H.legalTriple n q) = q := by
  letI : Nonempty support := H.support_nonempty.to_subtype
  exact Function.leftInverse_invFun (H.legalTriple_injective n) q

/-- Original partition block address represented by a bundled legal triple. -/
noncomputable def modeledAddress
    (H : PartitionHashEncoding (R := R) support) (n : ℕ)
    (triple : ProgressionHash.LegalTriple R (Fin (n + 1)) H.target) :
    BlockAddress (fun c ↦ PositiveWord (A c) n) :=
  supportWordAddress n (H.sourceWordOfLegalTriple n triple)

omit [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)] in
@[simp] theorem modeledAddress_legalTriple
    (H : PartitionHashEncoding (R := R) support) (n : ℕ)
    (q : PositiveWord support n) :
    H.modeledAddress n (H.legalTriple n q) = supportWordAddress n q := by
  simp [modeledAddress]

omit [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)] in
/-- Every triple in `legalTargets` is recovered by encoding its chosen source word. -/
theorem legalTriple_sourceWordOfLegalTriple_eq_of_mem
    (H : PartitionHashEncoding (R := R) support) (n : ℕ)
    (words : Finset (PositiveWord support n))
    {triple : ProgressionHash.LegalTriple R (Fin (n + 1)) H.target}
    (htriple : triple ∈ H.legalTargets n words) :
    H.legalTriple n (H.sourceWordOfLegalTriple n triple) = triple := by
  classical
  rw [legalTargets, Finset.mem_image] at htriple
  obtain ⟨q, _hq, rfl⟩ := htriple
  rw [sourceWordOfLegalTriple_legalTriple]

omit [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)] in
/-- The recovered source word of a represented legal target belongs to the source family used to
construct that target. -/
theorem sourceWordOfLegalTriple_mem_of_mem
    (H : PartitionHashEncoding (R := R) support) (n : ℕ)
    (words : Finset (PositiveWord support n))
    {triple : ProgressionHash.LegalTriple R (Fin (n + 1)) H.target}
    (htriple : triple ∈ H.legalTargets n words) :
    H.sourceWordOfLegalTriple n triple ∈ words := by
  classical
  rw [legalTargets, Finset.mem_image] at htriple
  obtain ⟨q, hq, rfl⟩ := htriple
  simpa using hq

omit [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)] in
/-- On represented targets, equality of modeled block words is equivalent to equality of the
corresponding hashing indices. -/
theorem modeledAddress_leg_eq_iff
    (H : PartitionHashEncoding (R := R) support) (n : ℕ)
    (words : Finset (PositiveWord support n))
    {left right : ProgressionHash.LegalTriple R (Fin (n + 1)) H.target}
    (hleft : left ∈ H.legalTargets n words) (hright : right ∈ H.legalTargets n words)
    (c : Leg) :
    H.modeledAddress n left c = H.modeledAddress n right c ↔
      left.legIndex c = right.legIndex c := by
  let leftWord := H.sourceWordOfLegalTriple n left
  let rightWord := H.sourceWordOfLegalTriple n right
  have hleftRecover : H.legalTriple n leftWord = left :=
    H.legalTriple_sourceWordOfLegalTriple_eq_of_mem n words hleft
  have hrightRecover : H.legalTriple n rightWord = right :=
    H.legalTriple_sourceWordOfLegalTriple_eq_of_mem n words hright
  change supportWordAddress n leftWord c = supportWordAddress n rightWord c ↔ _
  rw [← hleftRecover, ← hrightRecover]
  exact (H.legalTriple_legIndex_eq_iff n leftWord rightWord c).symm

omit [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)] in
/-- Source support words in a finite family having one prescribed transposed block word on a
chosen leg.  This is the exact source-side counterpart of `ProgressionHash.LegalTriple.legFiber`.
-/
noncomputable def sourceWordLegFiber
    (n : ℕ) (words : Finset (PositiveWord support n)) (c : Leg)
    (target : PositiveWord (A c) n) : Finset (PositiveWord support n) := by
  classical
  exact words.filter fun word ↦ supportWordAddress n word c = target

/-- Reindex the `n + 1` positions of a recursive positive word. -/
noncomputable def positiveWordReindex {I : Type*} (n : ℕ)
    (e : Equiv.Perm (Fin (n + 1))) (word : PositiveWord I n) : PositiveWord I n :=
  (positiveWordEquiv I n).symm ((positiveWordEquiv I n word) ∘ e.symm)

/-- Function representation of a reindexed positive word. -/
@[simp] theorem positiveWordEquiv_positiveWordReindex {I : Type*} (n : ℕ)
    (e : Equiv.Perm (Fin (n + 1))) (word : PositiveWord I n) :
    positiveWordEquiv I n (positiveWordReindex n e word) =
      positiveWordEquiv I n word ∘ e.symm := by
  simp [positiveWordReindex]

/-- Reindexing by inverse position permutations cancels. -/
@[simp] theorem positiveWordReindex_symm_apply {I : Type*} (n : ℕ)
    (e : Equiv.Perm (Fin (n + 1))) (word : PositiveWord I n) :
    positiveWordReindex n e.symm (positiveWordReindex n e word) = word := by
  apply (positiveWordEquiv I n).injective
  simp [Function.comp_def]

omit [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)] in
/-- Transposing a support word to one tensor leg commutes with reindexing word positions. -/
theorem positiveWordEquiv_supportWordAddress_reindex
    (n : ℕ) (e : Equiv.Perm (Fin (n + 1)))
    (word : PositiveWord support n) (c : Leg) :
    positiveWordEquiv (A c) n
        (supportWordAddress n (positiveWordReindex n e word) c) =
      positiveWordEquiv (A c) n (supportWordAddress n word c) ∘ e.symm := by
  rw [positiveWordEquiv_supportWordAddress,
    positiveWordEquiv_supportWordAddress]
  simp only [positiveWordEquiv_positiveWordReindex, Function.comp_apply]
  rfl

/-- In a source-word family invariant under position permutations, fibers over leg words of the
same multiplicity type have equal size.

Proof sketch: choose a position permutation carrying the first target word to the second and
apply it to the complete support-address word.  Stability keeps the source word in the family;
the inverse position permutation supplies the inverse fiber map. -/
theorem card_sourceWordLegFiber_eq_of_multiplicity_eq
    (n : ℕ) (words : Finset (PositiveWord support n)) (c : Leg)
    (hstable : ∀ (e : Equiv.Perm (Fin (n + 1))) word,
      word ∈ words ↔ positiveWordReindex n e word ∈ words)
    (left right : PositiveWord (A c) n)
    (hmultiplicity :
      WordType.multiplicity (positiveWordEquiv (A c) n left) =
        WordType.multiplicity (positiveWordEquiv (A c) n right)) :
    (sourceWordLegFiber n words c left).card =
      (sourceWordLegFiber n words c right).card := by
  classical
  let e := WordType.positionPermOfSameMultiplicity
    (positiveWordEquiv (A c) n left) (positiveWordEquiv (A c) n right)
    hmultiplicity
  have he : positiveWordEquiv (A c) n right ∘ e =
      positiveWordEquiv (A c) n left :=
    WordType.positionPermOfSameMultiplicity_map _ _ hmultiplicity
  have he' : positiveWordEquiv (A c) n left ∘ e.symm =
      positiveWordEquiv (A c) n right := by
    funext i
    have hi := congrFun he (e.symm i)
    simpa [Function.comp_apply] using hi.symm
  apply Finset.card_bij (fun word _ ↦ positiveWordReindex n e word)
  · intro word hword
    rw [sourceWordLegFiber, Finset.mem_filter] at hword ⊢
    refine ⟨(hstable e word).mp hword.1, ?_⟩
    apply (positiveWordEquiv (A c) n).injective
    rw [positiveWordEquiv_supportWordAddress_reindex, hword.2, he']
  · intro leftWord _ rightWord _ heq
    apply (positiveWordEquiv support n).injective
    have hfunctions := congrArg (positiveWordEquiv support n) heq
    simp only [positiveWordEquiv_positiveWordReindex] at hfunctions
    funext i
    have hi := congrFun hfunctions (e i)
    simpa [Function.comp_apply] using hi
  · intro word hword
    refine ⟨positiveWordReindex n e.symm word, ?_, ?_⟩
    · rw [sourceWordLegFiber, Finset.mem_filter] at hword ⊢
      refine ⟨(hstable e.symm word).mp hword.1, ?_⟩
      apply (positiveWordEquiv (A c) n).injective
      rw [positiveWordEquiv_supportWordAddress_reindex, hword.2]
      exact he
    · simpa using positiveWordReindex_symm_apply n e.symm word

omit [∀ c, Fintype (A c)] in
/-- Encoding support words as legal triples preserves the exact size of every leg fiber.

Proof sketch: recover the unique source word of each encoded target.  Membership and equality on
the selected leg are preserved by `modeledAddress_leg_eq_iff`; encoding a word in the source
fiber gives the inverse map. -/
theorem card_legFiber_legalTargets_eq_card_sourceWordLegFiber
    (H : PartitionHashEncoding (R := R) support) (n : ℕ)
    (words : Finset (PositiveWord support n))
    {triple : ProgressionHash.LegalTriple R (Fin (n + 1)) H.target}
    (htriple : triple ∈ H.legalTargets n words) (c : Leg) :
    (ProgressionHash.LegalTriple.legFiber (H.legalTargets n words) triple c).card =
      (sourceWordLegFiber n words c (H.modeledAddress n triple c)).card := by
  classical
  apply Finset.card_bij (fun other _ ↦ H.sourceWordOfLegalTriple n other)
  · intro other hother
    rw [sourceWordLegFiber, Finset.mem_filter]
    have hfiber := (ProgressionHash.LegalTriple.mem_legFiber
      (H.legalTargets n words) triple other c).mp hother
    refine ⟨H.sourceWordOfLegalTriple_mem_of_mem n words hfiber.1, ?_⟩
    exact (H.modeledAddress_leg_eq_iff n words hfiber.1 htriple c).mpr hfiber.2
  · intro left hleft right hright heq
    have hleftTarget := (ProgressionHash.LegalTriple.mem_legFiber
      (H.legalTargets n words) triple left c).mp hleft |>.1
    have hrightTarget := (ProgressionHash.LegalTriple.mem_legFiber
      (H.legalTargets n words) triple right c).mp hright |>.1
    calc
      left = H.legalTriple n (H.sourceWordOfLegalTriple n left) :=
        (H.legalTriple_sourceWordOfLegalTriple_eq_of_mem n words hleftTarget).symm
      _ = H.legalTriple n (H.sourceWordOfLegalTriple n right) := congrArg _ heq
      _ = right := H.legalTriple_sourceWordOfLegalTriple_eq_of_mem n words hrightTarget
  · intro word hword
    rw [sourceWordLegFiber, Finset.mem_filter] at hword
    refine ⟨H.legalTriple n word, ?_, ?_⟩
    · rw [ProgressionHash.LegalTriple.mem_legFiber]
      refine ⟨?_, ?_⟩
      · unfold legalTargets
        exact Finset.mem_image.mpr ⟨word, hword.1, rfl⟩
      · apply (H.modeledAddress_leg_eq_iff n words
          (by
            unfold legalTargets
            exact Finset.mem_image.mpr ⟨word, hword.1, rfl⟩)
          htriple c).mp
        simpa using hword.2
    · exact H.sourceWordOfLegalTriple_legalTriple n word

omit [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)] in
/-- Shared counting core of the two leg-fiber bounds below.  Recovering the chosen source word
of a represented hashing target is injective on every leg fiber, so as soon as all recovered
source words of a leg fiber land in some finite family of support words, the fiber is at most as
large as that family. -/
private theorem card_legFiber_legalTargets_le_of_sourceWord_mem
    (H : PartitionHashEncoding (R := R) support) (n : ℕ)
    (words : Finset (PositiveWord support n))
    {triple : ProgressionHash.LegalTriple R (Fin (n + 1)) H.target} (c : Leg)
    {targets : Finset (Fin (n + 1) → support)}
    (hmem : ∀ other ∈
        ProgressionHash.LegalTriple.legFiber (H.legalTargets n words) triple c,
      positiveWordEquiv support n (H.sourceWordOfLegalTriple n other) ∈ targets) :
    (ProgressionHash.LegalTriple.legFiber (H.legalTargets n words) triple c).card ≤
      targets.card := by
  classical
  apply Finset.card_le_card_of_injOn
    (fun other ↦ positiveWordEquiv support n (H.sourceWordOfLegalTriple n other)) hmem
  intro left hleft right hright hsource
  have hleftTarget := (ProgressionHash.LegalTriple.mem_legFiber
    (H.legalTargets n words) triple left c).mp hleft |>.1
  have hrightTarget := (ProgressionHash.LegalTriple.mem_legFiber
    (H.legalTargets n words) triple right c).mp hright |>.1
  have hword : H.sourceWordOfLegalTriple n left =
      H.sourceWordOfLegalTriple n right :=
    (positiveWordEquiv support n).injective hsource
  calc
    left = H.legalTriple n (H.sourceWordOfLegalTriple n left) :=
      (H.legalTriple_sourceWordOfLegalTriple_eq_of_mem n words hleftTarget).symm
    _ = H.legalTriple n (H.sourceWordOfLegalTriple n right) := congrArg _ hword
    _ = right := H.legalTriple_sourceWordOfLegalTriple_eq_of_mem n words hrightTarget

omit [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)] in
/-- Shared word-identification core of the two leg-fiber bounds below.  On the fiber leg `c`,
the recovered source word of any competitor in the leg fiber of `triple` projects coordinatewise
to exactly the modeled block word of `triple` on that leg. -/
private theorem sourceWord_leg_eq_modeledAddress_of_mem_legFiber
    (H : PartitionHashEncoding (R := R) support) (n : ℕ)
    (words : Finset (PositiveWord support n))
    {triple : ProgressionHash.LegalTriple R (Fin (n + 1)) H.target}
    (htriple : triple ∈ H.legalTargets n words) (c : Leg)
    {other : ProgressionHash.LegalTriple R (Fin (n + 1)) H.target}
    (hother : other ∈
      ProgressionHash.LegalTriple.legFiber (H.legalTargets n words) triple c) :
    ((fun s : support ↦ s.1 c) ∘
        positiveWordEquiv support n (H.sourceWordOfLegalTriple n other)) =
      positiveWordEquiv (A c) n (H.modeledAddress n triple c) := by
  have hfiber := (ProgressionHash.LegalTriple.mem_legFiber
    (H.legalTargets n words) triple other c).mp hother
  have haddress : H.modeledAddress n other c = H.modeledAddress n triple c :=
    (H.modeledAddress_leg_eq_iff n words hfiber.1 htriple c).mpr hfiber.2
  calc
    ((fun s : support ↦ s.1 c) ∘
        positiveWordEquiv support n (H.sourceWordOfLegalTriple n other)) =
        positiveWordEquiv (A c) n (H.modeledAddress n other c) := by
      unfold modeledAddress
      funext i
      exact congrFun (positiveWordEquiv_supportWordAddress
        (A := A) (support := support) n
        (H.sourceWordOfLegalTriple n other) c).symm i
    _ = positiveWordEquiv (A c) n (H.modeledAddress n triple c) :=
      congrArg (positiveWordEquiv (A c) n) haddress

omit [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)] in
/-- A leg fiber of represented hashing targets injects into the ambient coordinatewise word
fiber of source support addresses.  Clients can therefore bound hashing competitors using only
the much smaller one-coordinate fibers of their finite support. -/
theorem card_legFiber_legalTargets_le_card_wordMapFiber
    (H : PartitionHashEncoding (R := R) support) (n : ℕ)
    (words : Finset (PositiveWord support n))
    {triple : ProgressionHash.LegalTriple R (Fin (n + 1)) H.target}
    (htriple : triple ∈ H.legalTargets n words) (c : Leg) :
    (ProgressionHash.LegalTriple.legFiber (H.legalTargets n words) triple c).card ≤
      (WordType.wordMapFiber (fun s : support ↦ s.1 c)
        (positiveWordEquiv (A c) n (H.modeledAddress n triple c))).card := by
  apply H.card_legFiber_legalTargets_le_of_sourceWord_mem n words c
  intro other hother
  rw [WordType.mem_wordMapFiber]
  exact H.sourceWord_leg_eq_modeledAddress_of_mem_legFiber n words htriple c hother

omit [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)] in
/-- If every selected supported-address word has one fixed joint multiplicity type, a leg fiber
of hashing targets injects into the corresponding *typed* coordinatewise word fiber.  This is
strictly sharper than `card_legFiber_legalTargets_le_card_wordMapFiber`: it retains the global
type selection used by tight-support laser arguments. -/
theorem card_legFiber_legalTargets_le_card_typedWordMapFiber
    (H : PartitionHashEncoding (R := R) support) (n : ℕ)
    (words : Finset (PositiveWord support n)) (a : support → ℕ)
    (hwords : ∀ q ∈ words,
      WordType.multiplicity (positiveWordEquiv support n q) = a)
    {triple : ProgressionHash.LegalTriple R (Fin (n + 1)) H.target}
    (htriple : triple ∈ H.legalTargets n words) (c : Leg) :
    (ProgressionHash.LegalTriple.legFiber (H.legalTargets n words) triple c).card ≤
      (WordType.typedWordMapFiber (fun s : support ↦ s.1 c) a
        (positiveWordEquiv (A c) n (H.modeledAddress n triple c))).card := by
  apply H.card_legFiber_legalTargets_le_of_sourceWord_mem n words c
  intro other hother
  have hfiber := (ProgressionHash.LegalTriple.mem_legFiber
    (H.legalTargets n words) triple other c).mp hother
  rw [WordType.mem_typedWordMapFiber]
  refine ⟨hwords _ (H.sourceWordOfLegalTriple_mem_of_mem n words hfiber.1), ?_⟩
  exact H.sourceWord_leg_eq_modeledAddress_of_mem_legFiber n words htriple c hother

omit [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)] in
/-- The modeled-address map is injective on every legal target family. -/
theorem modeledAddress_injOn_legalTargets
    (H : PartitionHashEncoding (R := R) support) (n : ℕ)
    (words : Finset (PositiveWord support n)) :
    Set.InjOn (H.modeledAddress n) (H.legalTargets n words : Set _) := by
  intro left hleft right hright haddress
  apply ProgressionHash.LegalTriple.ext
  · exact (H.modeledAddress_leg_eq_iff n words hleft hright .X).mp
      (congrFun haddress .X)
  · exact (H.modeledAddress_leg_eq_iff n words hleft hright .Y).mp
      (congrFun haddress .Y)
  · exact (H.modeledAddress_leg_eq_iff n words hleft hright .Z).mp
      (congrFun haddress .Z)

/-- Original block addresses represented by a finite legal-triple family. -/
noncomputable def modeledAddresses
    (H : PartitionHashEncoding (R := R) support) (n : ℕ)
    (triples : Finset (ProgressionHash.LegalTriple R (Fin (n + 1)) H.target)) :
    Finset (BlockAddress (fun c ↦ PositiveWord (A c) n)) := by
  classical
  exact triples.image (H.modeledAddress n)

omit [∀ c, Fintype (A c)] in
/-- Modeling the legal targets generated by source words simply returns the corresponding
transposed partition block addresses. -/
theorem modeledAddresses_legalTargets_eq_image
    (H : PartitionHashEncoding (R := R) support) (n : ℕ)
    (words : Finset (PositiveWord support n)) :
    H.modeledAddresses n (H.legalTargets n words) =
      words.image (supportWordAddress n) := by
  classical
  unfold modeledAddresses legalTargets
  rw [Finset.image_image]
  apply Finset.image_congr
  intro q _hq
  exact H.modeledAddress_legalTriple n q

omit [∀ c, Fintype (A c)] in
/-- Membership in a modeled legal-target family can be unpacked back to a supported source word
in the original family. -/
theorem exists_sourceWord_of_mem_modeledAddresses_legalTargets
    (H : PartitionHashEncoding (R := R) support) (n : ℕ)
    (words : Finset (PositiveWord support n))
    {address : BlockAddress (fun c ↦ PositiveWord (A c) n)}
    (haddress : address ∈ H.modeledAddresses n (H.legalTargets n words)) :
    ∃ q ∈ words, supportWordAddress n q = address := by
  rw [H.modeledAddresses_legalTargets_eq_image n words] at haddress
  exact Finset.mem_image.mp haddress

/-- The complete positive partition support is exactly the modeled family obtained from all
supported source words. -/
theorem positivePower_support_eq_modeledLegalTargets
    {K : Type v} [CommSemiring K]
    {V : ∀ c, A c → Type (max v x)}
    [∀ c a, AddCommMonoid (V c a)] [∀ c a, Module K (V c a)]
    (P : PartitionedTensor (K := K) (A := A) V)
    (H : PartitionHashEncoding (R := R) P.support) (n : ℕ) :
    (P.positivePower n).support =
      H.modeledAddresses n (H.legalTargets n Finset.univ) := by
  classical
  rw [PartitionedTensor.positivePower_support_eq_map_positiveSupportWords,
    Finset.map_eq_image, positiveSupportWords_eq_image_univ_subtype,
    Finset.image_image, H.modeledAddresses_legalTargets_eq_image]
  apply Finset.image_congr
  intro q _hq
  exact (positiveSupportWordBlockAddress_eq_equiv_map P.support n q).symm

omit [∀ c, Fintype (A c)] in
/-- A leg-local predicate whose conjunction characterizes a source-word family filters the
complete modeled support to exactly that modeled subfamily.  This is the generic type-selection
bridge used before hashing. -/
theorem filter_modeledLegalTargets_eq_of_mem_iff
    (H : PartitionHashEncoding (R := R) support) (n : ℕ)
    (words : Finset (PositiveWord support n))
    (keep : ∀ c, PositiveWord (A c) n → Prop)
    [∀ c word, Decidable (keep c word)]
    (hkeep : ∀ q : PositiveWord support n,
      q ∈ words ↔ ∀ c, keep c (supportWordAddress n q c)) :
    (H.modeledAddresses n (H.legalTargets n Finset.univ)).filter
        (fun s ↦ ∀ c, keep c (s c)) =
      H.modeledAddresses n (H.legalTargets n words) := by
  classical
  rw [H.modeledAddresses_legalTargets_eq_image,
    H.modeledAddresses_legalTargets_eq_image]
  ext address
  constructor
  · intro haddress
    obtain ⟨hall, hselected⟩ := Finset.mem_filter.mp haddress
    obtain ⟨q, _hq, rfl⟩ := Finset.mem_image.mp hall
    exact Finset.mem_image.mpr ⟨q, (hkeep q).mpr hselected, rfl⟩
  · intro haddress
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp haddress
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_image.mpr ⟨q, Finset.mem_univ q, rfl⟩, (hkeep q).mp hq⟩

omit [∀ c, Fintype (A c)] in
/-- Modeled addresses preserve the cardinality of any subfamily of `legalTargets`. -/
theorem card_modeledAddresses_of_subset
    (H : PartitionHashEncoding (R := R) support) (n : ℕ)
    (words : Finset (PositiveWord support n))
    (triples : Finset (ProgressionHash.LegalTriple R (Fin (n + 1)) H.target))
    (htriples : triples ⊆ H.legalTargets n words) :
    (H.modeledAddresses n triples).card = triples.card := by
  classical
  unfold modeledAddresses
  exact Finset.card_image_of_injOn
    ((H.modeledAddress_injOn_legalTargets n words).mono htriples)

/-- Hash-filtered addresses in the original partition-word representation. -/
noncomputable def filteredPowerAddresses
    (H : PartitionHashEncoding (R := R) support) (n : ℕ)
    (words : Finset (PositiveWord support n)) (B : Finset R)
    (seed : ProgressionHash.Seed R (Fin (n + 1))) :
    Finset (BlockAddress (fun c ↦ PositiveWord (A c) n)) :=
  H.modeledAddresses n
    (ProgressionHash.LegalTriple.filteredTargets (H.legalTargets n words) B seed)

/-- Legwise-isolated addresses in the original partition-word representation. -/
noncomputable def legwiseIsolatedPowerAddresses
    (H : PartitionHashEncoding (R := R) support) (n : ℕ)
    (words : Finset (PositiveWord support n)) (B : Finset R)
    (seed : ProgressionHash.Seed R (Fin (n + 1))) :
    Finset (BlockAddress (fun c ↦ PositiveWord (A c) n)) :=
  H.modeledAddresses n
    (ProgressionHash.LegalTriple.legwiseIsolatedTargets
      (H.legalTargets n words) B seed)

/-- X/Y-isolated addresses in the original partition-word representation.  Unlike legwise
isolation, this family intentionally permits repeated Z words. -/
noncomputable def xyIsolatedPowerAddresses
    (H : PartitionHashEncoding (R := R) support) (n : ℕ)
    (words : Finset (PositiveWord support n)) (B : Finset R)
    (seed : ProgressionHash.Seed R (Fin (n + 1))) :
    Finset (BlockAddress (fun c ↦ PositiveWord (A c) n)) :=
  H.modeledAddresses n
    (ProgressionHash.LegalTriple.xyIsolatedTargets
      (H.legalTargets n words) B seed)

/-- Independent block predicate implementing the three hash-membership zero-outs on the original
partition-word labels. -/
noncomputable def hashKeepBlock
    (H : PartitionHashEncoding (R := R) support) (n : ℕ)
    (B : Finset R) (seed : ProgressionHash.Seed R (Fin (n + 1))) :
    ∀ c, PositiveWord (A c) n → Prop
  | .X => fun word ↦
      seed.xHash (H.encode .X ∘ positiveWordEquiv (A .X) n word) ∈ B
  | .Y => fun word ↦
      seed.yHash (H.encode .Y ∘ positiveWordEquiv (A .Y) n word) ∈ B
  | .Z => fun word ↦
      seed.zHash H.target (H.encode .Z ∘ positiveWordEquiv (A .Z) n word) ∈ B

omit [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)] in
/-- On a supported source word, independent hash block selection is exactly the bundled legal
triple's survival predicate. -/
theorem hashKeepBlock_supportWordAddress_iff
    (H : PartitionHashEncoding (R := R) support) (n : ℕ)
    (B : Finset R) (seed : ProgressionHash.Seed R (Fin (n + 1)))
    (q : PositiveWord support n) :
    (∀ c, H.hashKeepBlock n B seed c (supportWordAddress n q c)) ↔
      ProgressionHash.LegalTriple.SurvivesHashFilter (B : Set R) seed
        (H.legalTriple n q) := by
  unfold ProgressionHash.LegalTriple.SurvivesHashFilter
  constructor
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · have hx := h .X
      change seed.xHash
        (H.encode .X ∘ positiveWordEquiv (A .X) n (supportWordAddress n q .X)) ∈ B at hx
      change seed.xHash ((H.legalTriple n q).legIndex .X) ∈ B
      rwa [H.legalTriple_legIndex_eq n q .X]
    · have hy := h .Y
      change seed.yHash
        (H.encode .Y ∘ positiveWordEquiv (A .Y) n (supportWordAddress n q .Y)) ∈ B at hy
      change seed.yHash ((H.legalTriple n q).legIndex .Y) ∈ B
      rwa [H.legalTriple_legIndex_eq n q .Y]
    · have hz := h .Z
      change seed.zHash H.target
        (H.encode .Z ∘ positiveWordEquiv (A .Z) n (supportWordAddress n q .Z)) ∈ B at hz
      change seed.zHash H.target ((H.legalTriple n q).legIndex .Z) ∈ B
      rwa [H.legalTriple_legIndex_eq n q .Z]
  · rintro ⟨hx, hy, hz⟩ c
    cases c with
    | X =>
        change seed.xHash
          (H.encode .X ∘ positiveWordEquiv (A .X) n (supportWordAddress n q .X)) ∈ B
        change seed.xHash ((H.legalTriple n q).legIndex .X) ∈ B at hx
        rwa [H.legalTriple_legIndex_eq n q .X] at hx
    | Y =>
        change seed.yHash
          (H.encode .Y ∘ positiveWordEquiv (A .Y) n (supportWordAddress n q .Y)) ∈ B
        change seed.yHash ((H.legalTriple n q).legIndex .Y) ∈ B at hy
        rwa [H.legalTriple_legIndex_eq n q .Y] at hy
    | Z =>
        change seed.zHash H.target
          (H.encode .Z ∘ positiveWordEquiv (A .Z) n (supportWordAddress n q .Z)) ∈ B
        change seed.zHash H.target ((H.legalTriple n q).legIndex .Z) ∈ B at hz
        rwa [H.legalTriple_legIndex_eq n q .Z] at hz

omit [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)] in
/-- The hash block predicate on a represented address agrees with survival of that represented
legal target. -/
theorem hashKeepBlock_modeledAddress_iff_of_mem
    (H : PartitionHashEncoding (R := R) support) (n : ℕ)
    (words : Finset (PositiveWord support n)) (B : Finset R)
    (seed : ProgressionHash.Seed R (Fin (n + 1)))
    {triple : ProgressionHash.LegalTriple R (Fin (n + 1)) H.target}
    (htriple : triple ∈ H.legalTargets n words) :
    (∀ c, H.hashKeepBlock n B seed c (H.modeledAddress n triple c)) ↔
      ProgressionHash.LegalTriple.SurvivesHashFilter (B : Set R) seed triple := by
  let q := H.sourceWordOfLegalTriple n triple
  have hrecover : H.legalTriple n q = triple :=
    H.legalTriple_sourceWordOfLegalTriple_eq_of_mem n words htriple
  have h := H.hashKeepBlock_supportWordAddress_iff n B seed q
  simpa [modeledAddress, q, hrecover] using h

/-- The explicit finite-set filter by the three independent hash block predicates. -/
noncomputable def hashFilteredModeledAddresses
    (H : PartitionHashEncoding (R := R) support) (n : ℕ)
    (words : Finset (PositiveWord support n)) (B : Finset R)
    (seed : ProgressionHash.Seed R (Fin (n + 1))) :
    Finset (BlockAddress (fun c ↦ PositiveWord (A c) n)) := by
  classical
  exact (H.modeledAddresses n (H.legalTargets n words)).filter
    (fun s ↦ ∀ c, H.hashKeepBlock n B seed c (s c))

omit [∀ c, Fintype (A c)] in
/-- Filtering all modeled target addresses by the independent hash predicates produces exactly
the modeled hash-filtered target family. -/
theorem filter_modeledAddresses_hashKeepBlock_eq
    (H : PartitionHashEncoding (R := R) support) (n : ℕ)
    (words : Finset (PositiveWord support n)) (B : Finset R)
    (seed : ProgressionHash.Seed R (Fin (n + 1))) :
    H.hashFilteredModeledAddresses n words B seed =
      H.filteredPowerAddresses n words B seed := by
  classical
  unfold hashFilteredModeledAddresses
  ext address
  constructor
  · intro haddress
    obtain ⟨hmodeled, hkeep⟩ := Finset.mem_filter.mp haddress
    unfold modeledAddresses at hmodeled
    obtain ⟨triple, htriple, rfl⟩ := Finset.mem_image.mp hmodeled
    unfold filteredPowerAddresses modeledAddresses
    apply Finset.mem_image.mpr
    refine ⟨triple, Finset.mem_filter.mpr ⟨htriple, ?_⟩, rfl⟩
    exact (H.hashKeepBlock_modeledAddress_iff_of_mem n words B seed htriple).mp hkeep
  · intro haddress
    unfold filteredPowerAddresses modeledAddresses at haddress
    obtain ⟨triple, htripleFiltered, rfl⟩ := Finset.mem_image.mp haddress
    have htriple : triple ∈ H.legalTargets n words :=
      ProgressionHash.LegalTriple.filteredTargets_subset
        (H.legalTargets n words) B seed htripleFiltered
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_image.mpr ⟨triple, htriple, rfl⟩, ?_⟩
    exact (H.hashKeepBlock_modeledAddress_iff_of_mem n words B seed htriple).mpr
      (Finset.mem_filter.mp htripleFiltered).2

omit [∀ c, Fintype (A c)] in
/-- Hash-filtered modeled addresses remain in the original modeled target family. -/
theorem filteredPowerAddresses_subset_modeledAddresses
    (H : PartitionHashEncoding (R := R) support) (n : ℕ)
    (words : Finset (PositiveWord support n)) (B : Finset R)
    (seed : ProgressionHash.Seed R (Fin (n + 1))) :
    H.filteredPowerAddresses n words B seed ⊆
      H.modeledAddresses n (H.legalTargets n words) := by
  classical
  exact Finset.image_mono _
    (ProgressionHash.LegalTriple.filteredTargets_subset
      (H.legalTargets n words) B seed)

omit [∀ c, Fintype (A c)] in
/-- Modeled isolated addresses and isolated legal triples have the same cardinality. -/
theorem card_legwiseIsolatedPowerAddresses [NeZero (2 : R)]
    (H : PartitionHashEncoding (R := R) support) (n : ℕ)
    (words : Finset (PositiveWord support n)) (B : Finset R)
    (seed : ProgressionHash.Seed R (Fin (n + 1))) :
    (H.legwiseIsolatedPowerAddresses n words B seed).card =
      (ProgressionHash.LegalTriple.legwiseIsolatedTargets
        (H.legalTargets n words) B seed).card := by
  classical
  apply H.card_modeledAddresses_of_subset n words
  exact (ProgressionHash.LegalTriple.legwiseIsolatedTargets_subset_filteredTargets
    (H.legalTargets n words) B seed).trans (Finset.filter_subset _ _)

omit [∀ c, Fintype (A c)] in
/-- Modeled XY-isolated addresses and XY-isolated legal triples have the same cardinality. -/
theorem card_xyIsolatedPowerAddresses [NeZero (2 : R)]
    (H : PartitionHashEncoding (R := R) support) (n : ℕ)
    (words : Finset (PositiveWord support n)) (B : Finset R)
    (seed : ProgressionHash.Seed R (Fin (n + 1))) :
    (H.xyIsolatedPowerAddresses n words B seed).card =
      (ProgressionHash.LegalTriple.xyIsolatedTargets
        (H.legalTargets n words) B seed).card := by
  classical
  apply H.card_modeledAddresses_of_subset n words
  exact (ProgressionHash.LegalTriple.xyIsolatedTargets_subset_filteredTargets
    (H.legalTargets n words) B seed).trans (Finset.filter_subset _ _)

omit [∀ c, Fintype (A c)] in
/-- Modeled legwise-isolated addresses are contained in the modeled hash-filtered family. -/
theorem legwiseIsolatedPowerAddresses_subset_filteredPowerAddresses [NeZero (2 : R)]
    (H : PartitionHashEncoding (R := R) support) (n : ℕ)
    (words : Finset (PositiveWord support n)) (B : Finset R)
    (seed : ProgressionHash.Seed R (Fin (n + 1))) :
    H.legwiseIsolatedPowerAddresses n words B seed ⊆
      H.filteredPowerAddresses n words B seed := by
  classical
  exact Finset.image_mono _
    (ProgressionHash.LegalTriple.legwiseIsolatedTargets_subset_filteredTargets
      (H.legalTargets n words) B seed)

omit [∀ c, Fintype (A c)] in
/-- Modeled XY-isolated addresses are contained in the modeled hash-filtered family. -/
theorem xyIsolatedPowerAddresses_subset_filteredPowerAddresses [NeZero (2 : R)]
    (H : PartitionHashEncoding (R := R) support) (n : ℕ)
    (words : Finset (PositiveWord support n)) (B : Finset R)
    (seed : ProgressionHash.Seed R (Fin (n + 1))) :
    H.xyIsolatedPowerAddresses n words B seed ⊆
      H.filteredPowerAddresses n words B seed := by
  classical
  exact Finset.image_mono _
    (ProgressionHash.LegalTriple.xyIsolatedTargets_subset_filteredTargets
      (H.legalTargets n words) B seed)

omit [∀ c, Fintype (A c)] in
/-- Modeled XY-isolated addresses are injective on X. -/
theorem x_injectiveOn_xyIsolatedPowerAddresses [NeZero (2 : R)]
    (H : PartitionHashEncoding (R := R) support) (n : ℕ)
    (words : Finset (PositiveWord support n)) (B : Finset R)
    (hB : ThreeAPFree (B : Set R))
    (seed : ProgressionHash.Seed R (Fin (n + 1))) :
    Set.InjOn (fun s : BlockAddress (fun c ↦ PositiveWord (A c) n) ↦ s .X)
      (H.xyIsolatedPowerAddresses n words B seed : Set _) := by
  classical
  intro left hleft right hright hx
  unfold xyIsolatedPowerAddresses modeledAddresses at hleft hright
  obtain ⟨leftTriple, hleftTriple, rfl⟩ := Finset.mem_image.mp hleft
  obtain ⟨rightTriple, hrightTriple, rfl⟩ := Finset.mem_image.mp hright
  have hleftTarget : leftTriple ∈ H.legalTargets n words :=
    ProgressionHash.LegalTriple.filteredTargets_subset
      (H.legalTargets n words) B seed
      (ProgressionHash.LegalTriple.xyIsolatedTargets_subset_filteredTargets
        (H.legalTargets n words) B seed hleftTriple)
  have hrightTarget : rightTriple ∈ H.legalTargets n words :=
    ProgressionHash.LegalTriple.filteredTargets_subset
      (H.legalTargets n words) B seed
      (ProgressionHash.LegalTriple.xyIsolatedTargets_subset_filteredTargets
        (H.legalTargets n words) B seed hrightTriple)
  have hindex : leftTriple.xIndex = rightTriple.xIndex := by
    simpa using (H.modeledAddress_leg_eq_iff n words hleftTarget hrightTarget .X).mp hx
  have heq := ProgressionHash.LegalTriple.xIndex_injectiveOn_xyIsolatedTargets
    (H.legalTargets n words) B hB seed hleftTriple hrightTriple hindex
  subst rightTriple
  rfl

omit [∀ c, Fintype (A c)] in
/-- Modeled XY-isolated addresses are injective on Y. -/
theorem y_injectiveOn_xyIsolatedPowerAddresses [NeZero (2 : R)]
    (H : PartitionHashEncoding (R := R) support) (n : ℕ)
    (words : Finset (PositiveWord support n)) (B : Finset R)
    (hB : ThreeAPFree (B : Set R))
    (seed : ProgressionHash.Seed R (Fin (n + 1))) :
    Set.InjOn (fun s : BlockAddress (fun c ↦ PositiveWord (A c) n) ↦ s .Y)
      (H.xyIsolatedPowerAddresses n words B seed : Set _) := by
  classical
  intro left hleft right hright hy
  unfold xyIsolatedPowerAddresses modeledAddresses at hleft hright
  obtain ⟨leftTriple, hleftTriple, rfl⟩ := Finset.mem_image.mp hleft
  obtain ⟨rightTriple, hrightTriple, rfl⟩ := Finset.mem_image.mp hright
  have hleftTarget : leftTriple ∈ H.legalTargets n words :=
    ProgressionHash.LegalTriple.filteredTargets_subset
      (H.legalTargets n words) B seed
      (ProgressionHash.LegalTriple.xyIsolatedTargets_subset_filteredTargets
        (H.legalTargets n words) B seed hleftTriple)
  have hrightTarget : rightTriple ∈ H.legalTargets n words :=
    ProgressionHash.LegalTriple.filteredTargets_subset
      (H.legalTargets n words) B seed
      (ProgressionHash.LegalTriple.xyIsolatedTargets_subset_filteredTargets
        (H.legalTargets n words) B seed hrightTriple)
  have hindex : leftTriple.yIndex = rightTriple.yIndex := by
    simpa using (H.modeledAddress_leg_eq_iff n words hleftTarget hrightTarget .Y).mp hy
  have heq := ProgressionHash.LegalTriple.yIndex_injectiveOn_xyIsolatedTargets
    (H.legalTargets n words) B hB seed hleftTriple hrightTriple hindex
  subst rightTriple
  rfl

omit [∀ c, Fintype (A c)] in
/-- The modeled isolated address family is legwise injective. -/
theorem legwiseIsolatedPowerAddresses_isLegwiseInjective [NeZero (2 : R)]
    (H : PartitionHashEncoding (R := R) support) (n : ℕ)
    (words : Finset (PositiveWord support n)) (B : Finset R)
    (hB : ThreeAPFree (B : Set R))
    (seed : ProgressionHash.Seed R (Fin (n + 1))) :
    IsLegwiseInjective (H.legwiseIsolatedPowerAddresses n words B seed) := by
  classical
  intro c left hleft right hright hleg
  unfold legwiseIsolatedPowerAddresses modeledAddresses at hleft hright
  obtain ⟨leftTriple, hleftTriple, rfl⟩ := Finset.mem_image.mp hleft
  obtain ⟨rightTriple, hrightTriple, rfl⟩ := Finset.mem_image.mp hright
  have hleftTarget : leftTriple ∈ H.legalTargets n words :=
    (ProgressionHash.LegalTriple.legwiseIsolatedTargets_subset_filteredTargets
      (H.legalTargets n words) B seed hleftTriple) |> fun hfiltered ↦
        ProgressionHash.LegalTriple.filteredTargets_subset
          (H.legalTargets n words) B seed hfiltered
  have hrightTarget : rightTriple ∈ H.legalTargets n words :=
    (ProgressionHash.LegalTriple.legwiseIsolatedTargets_subset_filteredTargets
      (H.legalTargets n words) B seed hrightTriple) |> fun hfiltered ↦
        ProgressionHash.LegalTriple.filteredTargets_subset
          (H.legalTargets n words) B seed hfiltered
  have hindex : leftTriple.legIndex c = rightTriple.legIndex c :=
    (H.modeledAddress_leg_eq_iff n words hleftTarget hrightTarget c).mp hleg
  have heq : leftTriple = rightTriple :=
    ProgressionHash.LegalTriple.legIndex_injectiveOn_legwiseIsolatedTargets
      (H.legalTargets n words) B hB seed c hleftTriple hrightTriple hindex
  subst rightTriple
  rfl

omit [∀ c, Fintype (A c)] in
/-- Every selected modeled address is the unique filtered address in its fiber on each leg. -/
theorem legwiseIsolatedPowerAddresses_hasUniqueLegFibers [NeZero (2 : R)]
    (H : PartitionHashEncoding (R := R) support) (n : ℕ)
    (words : Finset (PositiveWord support n)) (B : Finset R)
    (hB : ThreeAPFree (B : Set R))
    (seed : ProgressionHash.Seed R (Fin (n + 1))) (c : Leg) :
    HasUniqueLegFibers (H.filteredPowerAddresses n words B seed)
      (H.legwiseIsolatedPowerAddresses n words B seed) c := by
  classical
  refine ⟨H.legwiseIsolatedPowerAddresses_subset_filteredPowerAddresses n words B seed, ?_⟩
  intro selected hselected surviving hsurviving hleg
  unfold legwiseIsolatedPowerAddresses modeledAddresses at hselected
  unfold filteredPowerAddresses modeledAddresses at hsurviving
  obtain ⟨selectedTriple, hselectedTriple, rfl⟩ := Finset.mem_image.mp hselected
  obtain ⟨survivingTriple, hsurvivingTriple, rfl⟩ := Finset.mem_image.mp hsurviving
  have hselectedTarget : selectedTriple ∈ H.legalTargets n words :=
    ProgressionHash.LegalTriple.filteredTargets_subset
      (H.legalTargets n words) B seed
      (ProgressionHash.LegalTriple.legwiseIsolatedTargets_subset_filteredTargets
        (H.legalTargets n words) B seed hselectedTriple)
  have hsurvivingTarget : survivingTriple ∈ H.legalTargets n words :=
    ProgressionHash.LegalTriple.filteredTargets_subset
      (H.legalTargets n words) B seed hsurvivingTriple
  have hindex : survivingTriple.legIndex c = selectedTriple.legIndex c :=
    (H.modeledAddress_leg_eq_iff n words hsurvivingTarget hselectedTarget c).mp hleg
  have heq : survivingTriple = selectedTriple :=
    ProgressionHash.LegalTriple.eq_of_mem_legwiseIsolatedTargets_of_mem_filteredTargets
      (H.legalTargets n words) B hB seed hselectedTriple hsurvivingTriple c hindex
  subst survivingTriple
  rfl

omit [∀ c, Fintype (A c)] in
/-- Every modeled XY-isolated address is the unique filtered address in its X fiber.  This exact
zeroing certificate retains repeated Z fibers for the C-tensor step. -/
theorem xyIsolatedPowerAddresses_hasUniqueXFibers [NeZero (2 : R)]
    (H : PartitionHashEncoding (R := R) support) (n : ℕ)
    (words : Finset (PositiveWord support n)) (B : Finset R)
    (hB : ThreeAPFree (B : Set R))
    (seed : ProgressionHash.Seed R (Fin (n + 1))) :
    HasUniqueLegFibers (H.filteredPowerAddresses n words B seed)
      (H.xyIsolatedPowerAddresses n words B seed) .X := by
  classical
  refine ⟨H.xyIsolatedPowerAddresses_subset_filteredPowerAddresses n words B seed, ?_⟩
  intro selected hselected surviving hsurviving hx
  unfold xyIsolatedPowerAddresses modeledAddresses at hselected
  unfold filteredPowerAddresses modeledAddresses at hsurviving
  obtain ⟨selectedTriple, hselectedTriple, rfl⟩ := Finset.mem_image.mp hselected
  obtain ⟨survivingTriple, hsurvivingTriple, rfl⟩ := Finset.mem_image.mp hsurviving
  have hselectedTarget : selectedTriple ∈ H.legalTargets n words :=
    ProgressionHash.LegalTriple.filteredTargets_subset
      (H.legalTargets n words) B seed
      (ProgressionHash.LegalTriple.xyIsolatedTargets_subset_filteredTargets
        (H.legalTargets n words) B seed hselectedTriple)
  have hsurvivingTarget : survivingTriple ∈ H.legalTargets n words :=
    ProgressionHash.LegalTriple.filteredTargets_subset
      (H.legalTargets n words) B seed hsurvivingTriple
  have hindex : selectedTriple.xIndex = survivingTriple.xIndex :=
    (H.modeledAddress_leg_eq_iff n words hselectedTarget hsurvivingTarget .X).mp hx.symm
  have heq : survivingTriple = selectedTriple :=
    ProgressionHash.LegalTriple.eq_of_mem_xyIsolatedTargets_of_mem_filteredTargets
      (H.legalTargets n words) B hB seed hselectedTriple hsurvivingTriple
      (Or.inl hindex)
  subst survivingTriple
  rfl

section TensorExtraction

variable {K : Type v} [CommSemiring K]
variable {n : ℕ}
variable {V : ∀ c, PositiveWord (A c) n → Type x}
variable [∀ c a, AddCommMonoid (V c a)] [∀ c a, Module K (V c a)]

/-- Independent hash block zeroing restricts a partition whose support is the modeled target
family to precisely its modeled hash-filtered subfamily. -/
theorem _root_.AlgebraicComplexity.Tensor.Restricts.modeledTargets_to_hashFilteredPower
    (H : PartitionHashEncoding (R := R) support)
    (words : Finset (PositiveWord support n)) (B : Finset R)
    (seed : ProgressionHash.Seed R (Fin (n + 1)))
    (P : PartitionedTensor (K := K) (A := fun c ↦ PositiveWord (A c) n) V)
    (hsupport : P.support = H.modeledAddresses n (H.legalTargets n words)) :
    Restricts P.realize
      (P.withSupport (H.filteredPowerAddresses n words B seed)).realize := by
  classical
  let keep := H.hashKeepBlock n B seed
  have hselect := Tensor.Restricts.partitionedSelect P keep
  apply hselect.trans (Tensor.Restricts.of_eq ?_)
  have hselectedSupport : (P.select keep).support =
      H.filteredPowerAddresses n words B seed := by
    change P.support.filter (fun s ↦ ∀ c, H.hashKeepBlock n B seed c (s c)) = _
    rw [hsupport]
    change H.hashFilteredModeledAddresses n words B seed = _
    exact H.filter_modeledAddresses_hashKeepBlock_eq n words B seed
  unfold PartitionedTensor.realize
  change realizePartition (P.select keep).support P.constituent =
    realizePartition (H.filteredPowerAddresses n words B seed) P.constituent
  rw [hselectedSupport]

/-- One progression-hash pass followed by legwise isolation restricts a modeled filtered
partitioned tensor to the genuine indexed direct sum of all surviving constituents. -/
theorem _root_.AlgebraicComplexity.Tensor.Restricts.hashFilteredPower_to_legwiseIsolatedIndexedDirectSum
    [NeZero (2 : R)]
    (H : PartitionHashEncoding (R := R) support)
    (words : Finset (PositiveWord support n)) (B : Finset R)
    (hB : ThreeAPFree (B : Set R))
    (seed : ProgressionHash.Seed R (Fin (n + 1)))
    (P : PartitionedTensor (K := K) (A := fun c ↦ PositiveWord (A c) n) V)
    (hsupport : P.support = H.filteredPowerAddresses n words B seed) :
    Restricts P.realize
      (indexedDirectSum
        (V := SelectedBlockFamily (V := V)
          (H.legwiseIsolatedPowerAddresses n words B seed))
        (fun s : H.legwiseIsolatedPowerAddresses n words B seed ↦
          P.constituent s.1)) := by
  exact (Tensor.Restricts.partitionedUniqueXFibers P
      (H.legwiseIsolatedPowerAddresses n words B seed) (by
        rw [hsupport]
        exact H.legwiseIsolatedPowerAddresses_hasUniqueLegFibers
          n words B hB seed .X)).trans
    (Tensor.Restricts.partitionedLegwiseInjective_to_indexedDirectSum
      (P.withSupport (H.legwiseIsolatedPowerAddresses n words B seed))
      (H.legwiseIsolatedPowerAddresses_isLegwiseInjective n words B hB seed))

/-- A hash-filtered modeled power restricts exactly to its XY-isolated subpartition, preserving
all repeated Z blocks for subsequent C-tensor grouping. -/
theorem _root_.AlgebraicComplexity.Tensor.Restricts.hashFilteredPower_to_xyIsolated
    [NeZero (2 : R)]
    (H : PartitionHashEncoding (R := R) support)
    (words : Finset (PositiveWord support n)) (B : Finset R)
    (hB : ThreeAPFree (B : Set R))
    (seed : ProgressionHash.Seed R (Fin (n + 1)))
    (P : PartitionedTensor (K := K) (A := fun c ↦ PositiveWord (A c) n) V)
    (hsupport : P.support = H.filteredPowerAddresses n words B seed) :
    Restricts P.realize
      (P.withSupport (H.xyIsolatedPowerAddresses n words B seed)).realize := by
  apply Tensor.Restricts.partitionedUniqueXFibers P
    (H.xyIsolatedPowerAddresses n words B seed)
  rw [hsupport]
  exact H.xyIsolatedPowerAddresses_hasUniqueXFibers n words B hB seed

/-- Complete modeled-target C-tensor hashing extraction: independent hash zeroing followed by
XY isolation retains the shared-Z subpartition. -/
theorem _root_.AlgebraicComplexity.Tensor.Restricts.modeledTargets_to_xyIsolated
    [NeZero (2 : R)]
    (H : PartitionHashEncoding (R := R) support)
    (words : Finset (PositiveWord support n)) (B : Finset R)
    (hB : ThreeAPFree (B : Set R))
    (seed : ProgressionHash.Seed R (Fin (n + 1)))
    (P : PartitionedTensor (K := K) (A := fun c ↦ PositiveWord (A c) n) V)
    (hsupport : P.support = H.modeledAddresses n (H.legalTargets n words)) :
    Restricts P.realize
      (P.withSupport (H.xyIsolatedPowerAddresses n words B seed)).realize := by
  exact (Tensor.Restricts.modeledTargets_to_hashFilteredPower
      H words B seed P hsupport).trans
    (by
      simpa only [PartitionedTensor.withSupport] using
        Tensor.Restricts.hashFilteredPower_to_xyIsolated
          H words B hB seed
          (P.withSupport (H.filteredPowerAddresses n words B seed)) rfl)

/-- Complete modeled-target hashing extraction: independent hash zeroing and one-pass legwise
isolation produce the indexed direct sum of the surviving constituents. -/
theorem _root_.AlgebraicComplexity.Tensor.Restricts.modeledTargets_to_legwiseIsolatedIndexedDirectSum
    [NeZero (2 : R)]
    (H : PartitionHashEncoding (R := R) support)
    (words : Finset (PositiveWord support n)) (B : Finset R)
    (hB : ThreeAPFree (B : Set R))
    (seed : ProgressionHash.Seed R (Fin (n + 1)))
    (P : PartitionedTensor (K := K) (A := fun c ↦ PositiveWord (A c) n) V)
    (hsupport : P.support = H.modeledAddresses n (H.legalTargets n words)) :
    Restricts P.realize
      (indexedDirectSum
        (V := SelectedBlockFamily (V := V)
          (H.legwiseIsolatedPowerAddresses n words B seed))
        (fun s : H.legwiseIsolatedPowerAddresses n words B seed ↦
          P.constituent s.1)) := by
  exact (Tensor.Restricts.modeledTargets_to_hashFilteredPower
      H words B seed P hsupport).trans
    (by
      simpa only [PartitionedTensor.withSupport] using
        Tensor.Restricts.hashFilteredPower_to_legwiseIsolatedIndexedDirectSum
          H words B hB seed
          (P.withSupport (H.filteredPowerAddresses n words B seed)) rfl)

end TensorExtraction

end PartitionHashEncoding

end AlgebraicComplexity
