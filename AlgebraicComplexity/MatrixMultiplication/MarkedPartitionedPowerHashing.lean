import AlgebraicComplexity.Combinatorics.MarkedLegwiseHashingExtraction
import AlgebraicComplexity.MatrixMultiplication.PartitionedPowerHashing

/-!
# Marked affine hashing for partitioned tensor powers

This module transports marked-target hashing from encoded legal triples back to block-word
addresses of a partitioned tensor power.  It is the reusable semantic bridge required when a
chosen joint type is not determined by its three marginals.  The ambient word family is the one
obtainable by legwise variable zeroing; the marked subfamily is the joint type whose constituent
value is counted.

The main tensor theorem first applies the ordinary hash filter to the ambient partition and then
zeros it to an indexed direct sum of marked targets.  Soundness follows because marked targets
were isolated against every ambient competitor, not merely against one another.
-/

namespace AlgebraicComplexity

open Tensor

universe u v w x

variable {R : Type u} [Field R]
variable {A : Leg → Type w} [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]

namespace PartitionHashEncoding

variable {support : Finset (BlockAddress A)}

omit [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)] in
/-- Encoding source words as legal triples is monotone in the source-word family. -/
theorem legalTargets_mono
    (H : PartitionHashEncoding (R := R) support) (n : ℕ)
    {marked ambient : Finset (PositiveWord support n)}
    (hwords : marked ⊆ ambient) :
    H.legalTargets n marked ⊆ H.legalTargets n ambient := by
  classical
  unfold legalTargets
  exact Finset.image_mono _ hwords

/-- Modeled block addresses of marked targets isolated against the ambient target family. -/
noncomputable def markedLegwiseIsolatedPowerAddresses
    (H : PartitionHashEncoding (R := R) support) (n : ℕ)
    (ambientWords markedWords : Finset (PositiveWord support n))
    (B : Finset R) (seed : ProgressionHash.Seed R (Fin (n + 1))) :
    Finset (BlockAddress (fun c ↦ PositiveWord (A c) n)) :=
  H.modeledAddresses n
    (ProgressionHash.LegalTriple.markedLegwiseIsolatedTargets
      (H.legalTargets n ambientWords) (H.legalTargets n markedWords) B seed)

omit [∀ c, Fintype (A c)] in
/-- Modeling marked isolated targets preserves their cardinality. -/
theorem card_markedLegwiseIsolatedPowerAddresses
    (H : PartitionHashEncoding (R := R) support) (n : ℕ)
    (ambientWords markedWords : Finset (PositiveWord support n))
    (hwords : markedWords ⊆ ambientWords) (B : Finset R)
    (seed : ProgressionHash.Seed R (Fin (n + 1))) :
    (H.markedLegwiseIsolatedPowerAddresses n ambientWords markedWords B seed).card =
      (ProgressionHash.LegalTriple.markedLegwiseIsolatedTargets
        (H.legalTargets n ambientWords) (H.legalTargets n markedWords) B seed).card := by
  apply H.card_modeledAddresses_of_subset n ambientWords
  exact (ProgressionHash.LegalTriple.markedLegwiseIsolatedTargets_subset_marked
      (H.legalTargets n ambientWords) (H.legalTargets n markedWords) B seed).trans
    (H.legalTargets_mono n hwords)

omit [∀ c, Fintype (A c)] in
/-- Every modeled address retained by marked isolation comes from a word in the marked source
family.

The conclusion retains the exact transposed block address, rather than merely its three marginal
types.  Tensor clients can therefore rewrite the selected constituent to the constituent indexed
by the recovered supported word.

Proof sketch: unpack the selected modeled address to a marked isolated legal triple.  Marked
isolation is a subset of the marked legal-target family, so inverse decoding recovers a marked
source word.  The definition of `modeledAddress` supplies the asserted address equality. -/
theorem exists_markedSourceWord_of_mem_markedLegwiseIsolatedPowerAddresses
    (H : PartitionHashEncoding (R := R) support) (n : ℕ)
    (ambientWords markedWords : Finset (PositiveWord support n))
    (B : Finset R) (seed : ProgressionHash.Seed R (Fin (n + 1)))
    {address : BlockAddress (fun c ↦ PositiveWord (A c) n)}
    (haddress : address ∈
      H.markedLegwiseIsolatedPowerAddresses n ambientWords markedWords B seed) :
    ∃ word ∈ markedWords, supportWordAddress n word = address := by
  classical
  unfold markedLegwiseIsolatedPowerAddresses modeledAddresses at haddress
  obtain ⟨triple, htriple, rfl⟩ := Finset.mem_image.mp haddress
  have hmarked : triple ∈ H.legalTargets n markedWords :=
    ProgressionHash.LegalTriple.markedLegwiseIsolatedTargets_subset_marked
      (H.legalTargets n ambientWords) (H.legalTargets n markedWords) B seed htriple
  refine ⟨H.sourceWordOfLegalTriple n triple,
    H.sourceWordOfLegalTriple_mem_of_mem n markedWords hmarked, ?_⟩
  rfl

omit [∀ c, Fintype (A c)] in
/-- Marked isolated modeled addresses lie in the ambient hash-filtered partition. -/
theorem markedLegwiseIsolatedPowerAddresses_subset_filteredPowerAddresses
    [NeZero (2 : R)]
    (H : PartitionHashEncoding (R := R) support) (n : ℕ)
    (ambientWords markedWords : Finset (PositiveWord support n))
    (hwords : markedWords ⊆ ambientWords) (B : Finset R)
    (seed : ProgressionHash.Seed R (Fin (n + 1))) :
    H.markedLegwiseIsolatedPowerAddresses n ambientWords markedWords B seed ⊆
      H.filteredPowerAddresses n ambientWords B seed := by
  classical
  unfold markedLegwiseIsolatedPowerAddresses filteredPowerAddresses modeledAddresses
  exact Finset.image_mono _
    (ProgressionHash.LegalTriple.markedLegwiseIsolatedTargets_subset_filteredTargets
      (H.legalTargets n ambientWords) (H.legalTargets n markedWords)
      (H.legalTargets_mono n hwords) B seed)

omit [∀ c, Fintype (A c)] in
/-- The marked modeled address family is injective on every tensor leg. -/
theorem markedLegwiseIsolatedPowerAddresses_isLegwiseInjective
    [NeZero (2 : R)]
    (H : PartitionHashEncoding (R := R) support) (n : ℕ)
    (ambientWords markedWords : Finset (PositiveWord support n))
    (hwords : markedWords ⊆ ambientWords) (B : Finset R)
    (hB : ThreeAPFree (B : Set R))
    (seed : ProgressionHash.Seed R (Fin (n + 1))) :
    IsLegwiseInjective
      (H.markedLegwiseIsolatedPowerAddresses n ambientWords markedWords B seed) := by
  classical
  intro c left hleft right hright hleg
  unfold markedLegwiseIsolatedPowerAddresses modeledAddresses at hleft hright
  obtain ⟨leftTriple, hleftTriple, rfl⟩ := Finset.mem_image.mp hleft
  obtain ⟨rightTriple, hrightTriple, rfl⟩ := Finset.mem_image.mp hright
  have htargets := H.legalTargets_mono n hwords
  have hleftTarget : leftTriple ∈ H.legalTargets n ambientWords :=
    htargets (ProgressionHash.LegalTriple.markedLegwiseIsolatedTargets_subset_marked
      _ _ B seed hleftTriple)
  have hrightTarget : rightTriple ∈ H.legalTargets n ambientWords :=
    htargets (ProgressionHash.LegalTriple.markedLegwiseIsolatedTargets_subset_marked
      _ _ B seed hrightTriple)
  have hindex : leftTriple.legIndex c = rightTriple.legIndex c :=
    (H.modeledAddress_leg_eq_iff n ambientWords hleftTarget hrightTarget c).mp hleg
  have heq : leftTriple = rightTriple :=
    ProgressionHash.LegalTriple.legIndex_injectiveOn_markedLegwiseIsolatedTargets
      (H.legalTargets n ambientWords) (H.legalTargets n markedWords)
      htargets B hB seed c hleftTriple hrightTriple hindex
  subst rightTriple
  rfl

omit [∀ c, Fintype (A c)] in
/-- Every marked selected address is the unique ambient hash survivor in each of its leg fibers. -/
theorem markedLegwiseIsolatedPowerAddresses_hasUniqueLegFibers
    [NeZero (2 : R)]
    (H : PartitionHashEncoding (R := R) support) (n : ℕ)
    (ambientWords markedWords : Finset (PositiveWord support n))
    (hwords : markedWords ⊆ ambientWords) (B : Finset R)
    (hB : ThreeAPFree (B : Set R))
    (seed : ProgressionHash.Seed R (Fin (n + 1))) (c : Leg) :
    HasUniqueLegFibers (H.filteredPowerAddresses n ambientWords B seed)
      (H.markedLegwiseIsolatedPowerAddresses n ambientWords markedWords B seed) c := by
  classical
  refine ⟨H.markedLegwiseIsolatedPowerAddresses_subset_filteredPowerAddresses
    n ambientWords markedWords hwords B seed, ?_⟩
  intro selected hselected surviving hsurviving hleg
  unfold markedLegwiseIsolatedPowerAddresses modeledAddresses at hselected
  unfold filteredPowerAddresses modeledAddresses at hsurviving
  obtain ⟨selectedTriple, hselectedTriple, rfl⟩ := Finset.mem_image.mp hselected
  obtain ⟨survivingTriple, hsurvivingTriple, rfl⟩ := Finset.mem_image.mp hsurviving
  have htargets := H.legalTargets_mono n hwords
  have hselectedTarget : selectedTriple ∈ H.legalTargets n ambientWords :=
    htargets (ProgressionHash.LegalTriple.markedLegwiseIsolatedTargets_subset_marked
      _ _ B seed hselectedTriple)
  have hsurvivingTarget : survivingTriple ∈ H.legalTargets n ambientWords :=
    ProgressionHash.LegalTriple.filteredTargets_subset
      (H.legalTargets n ambientWords) B seed hsurvivingTriple
  have hindex : survivingTriple.legIndex c = selectedTriple.legIndex c :=
    (H.modeledAddress_leg_eq_iff n ambientWords
      hsurvivingTarget hselectedTarget c).mp hleg
  have heq : survivingTriple = selectedTriple :=
    ProgressionHash.LegalTriple.eq_of_mem_markedLegwiseIsolatedTargets_of_mem_filteredTargets
      (H.legalTargets n ambientWords) (H.legalTargets n markedWords) htargets
      B hB seed hselectedTriple hsurvivingTriple c hindex
  subst survivingTriple
  rfl

omit [∀ c, Fintype (A c)] in
/-- The marked good-seed theorem in the original partition-word representation. -/
theorem exists_seed_many_markedLegwiseIsolatedPowerAddresses
    [Fintype R] [NeZero (2 : R)]
    (H : PartitionHashEncoding (R := R) support) (n : ℕ)
    (ambientWords markedWords : Finset (PositiveWord support n))
    (hwords : markedWords ⊆ ambientWords) (B : Finset R)
    (hB : ThreeAPFree (B : Set R))
    (hquarter : ∀ triple ∈ H.legalTargets n markedWords,
      4 * (ProgressionHash.LegalTriple.legwiseCompetitorYIndices
        (H.legalTargets n ambientWords) triple).card ≤ Fintype.card R) :
    ∃ seed : ProgressionHash.Seed R (Fin (n + 1)),
      3 * markedWords.card * B.card ≤
          4 * (Fintype.card R * Fintype.card R) *
            (H.markedLegwiseIsolatedPowerAddresses
              n ambientWords markedWords B seed).card ∧
        H.markedLegwiseIsolatedPowerAddresses n ambientWords markedWords B seed ⊆
          H.filteredPowerAddresses n ambientWords B seed ∧
        IsLegwiseInjective
          (H.markedLegwiseIsolatedPowerAddresses n ambientWords markedWords B seed) := by
  have htargets := H.legalTargets_mono n hwords
  obtain ⟨seed, hcount, hsubset, hinj⟩ :=
    ProgressionHash.LegalTriple.exists_seed_many_markedLegwiseIsolatedTargets
      (H.legalTargets n ambientWords) (H.legalTargets n markedWords)
      htargets B hB hquarter
  refine ⟨seed, ?_, ?_, ?_⟩
  · rw [H.card_markedLegwiseIsolatedPowerAddresses
      n ambientWords markedWords hwords B seed]
    simpa using hcount
  · exact H.markedLegwiseIsolatedPowerAddresses_subset_filteredPowerAddresses
      n ambientWords markedWords hwords B seed
  · exact H.markedLegwiseIsolatedPowerAddresses_isLegwiseInjective
      n ambientWords markedWords hwords B hB seed

section TensorExtraction

variable {K : Type v} [CommSemiring K]
variable {n : ℕ}
variable {V : ∀ c, PositiveWord (A c) n → Type x}
variable [∀ c a, AddCommMonoid (V c a)] [∀ c a, Module K (V c a)]

/-- An ambient hash-filtered power restricts to the indexed direct sum of the marked targets that
were isolated against all ambient competitors. -/
theorem _root_.AlgebraicComplexity.Tensor.Restricts.hashFilteredPower_to_markedLegwiseIsolatedIndexedDirectSum
    [NeZero (2 : R)]
    (H : PartitionHashEncoding (R := R) support)
    (ambientWords markedWords : Finset (PositiveWord support n))
    (hwords : markedWords ⊆ ambientWords) (B : Finset R)
    (hB : ThreeAPFree (B : Set R))
    (seed : ProgressionHash.Seed R (Fin (n + 1)))
    (P : PartitionedTensor (K := K) (A := fun c ↦ PositiveWord (A c) n) V)
    (hsupport : P.support = H.filteredPowerAddresses n ambientWords B seed) :
    Restricts P.realize
      (indexedDirectSum
        (V := SelectedBlockFamily (V := V)
          (H.markedLegwiseIsolatedPowerAddresses
            n ambientWords markedWords B seed))
        (fun s : H.markedLegwiseIsolatedPowerAddresses
            n ambientWords markedWords B seed ↦ P.constituent s.1)) := by
  exact (Tensor.Restricts.partitionedUniqueXFibers P
      (H.markedLegwiseIsolatedPowerAddresses n ambientWords markedWords B seed)
      (by
        rw [hsupport]
        exact H.markedLegwiseIsolatedPowerAddresses_hasUniqueLegFibers
          n ambientWords markedWords hwords B hB seed .X)).trans
    (Tensor.Restricts.partitionedLegwiseInjective_to_indexedDirectSum
      (P.withSupport (H.markedLegwiseIsolatedPowerAddresses
        n ambientWords markedWords B seed))
      (H.markedLegwiseIsolatedPowerAddresses_isLegwiseInjective
        n ambientWords markedWords hwords B hB seed))

/-- Complete marked modeled-target extraction: ambient hash zeroing followed by marked isolation
produces a genuine indexed direct sum of the selected joint-type constituents. -/
theorem _root_.AlgebraicComplexity.Tensor.Restricts.modeledTargets_to_markedLegwiseIsolatedIndexedDirectSum
    [NeZero (2 : R)]
    (H : PartitionHashEncoding (R := R) support)
    (ambientWords markedWords : Finset (PositiveWord support n))
    (hwords : markedWords ⊆ ambientWords) (B : Finset R)
    (hB : ThreeAPFree (B : Set R))
    (seed : ProgressionHash.Seed R (Fin (n + 1)))
    (P : PartitionedTensor (K := K) (A := fun c ↦ PositiveWord (A c) n) V)
    (hsupport : P.support = H.modeledAddresses n (H.legalTargets n ambientWords)) :
    Restricts P.realize
      (indexedDirectSum
        (V := SelectedBlockFamily (V := V)
          (H.markedLegwiseIsolatedPowerAddresses
            n ambientWords markedWords B seed))
        (fun s : H.markedLegwiseIsolatedPowerAddresses
            n ambientWords markedWords B seed ↦ P.constituent s.1)) := by
  exact (Tensor.Restricts.modeledTargets_to_hashFilteredPower
      H ambientWords B seed P hsupport).trans
    (by
      simpa only [PartitionedTensor.withSupport] using
        Tensor.Restricts.hashFilteredPower_to_markedLegwiseIsolatedIndexedDirectSum
          H ambientWords markedWords hwords B hB seed
          (P.withSupport (H.filteredPowerAddresses n ambientWords B seed)) rfl)

end TensorExtraction

end PartitionHashEncoding

end AlgebraicComplexity
