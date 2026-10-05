/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Combinatorics.MarkedTwoLegHashingExtraction
import AlgebraicComplexity.MatrixMultiplication.MarkedPartitionedPowerHashing

/-!
# Marked asymmetric (two-leg) affine hashing for partitioned tensor powers

`Combinatorics/MarkedTwoLegHashingExtraction.lean` selects, for one affine seed, a large family of
*marked* legal triples that are isolated on the `X` and `Y` legs against the whole *ambient*
family, with **no constraint at all on the `Z` leg**.  `MatrixMultiplication/PartitionedPowerHashing.lean`
transports the unmarked families back to block-word addresses of a partitioned tensor power.  This
module supplies the missing combination: the marked two-leg family in the block-word
representation.

The two neighbouring endpoints do not cover it.

* `MatrixMultiplication/MarkedPartitionedPowerHashing.lean` is the marked **three-leg** transport.
  Its conclusion is an indexed direct sum, which is exactly what an asymmetric-hashing client must
  not take: isolating `Z` destroys the repeated `Z` blocks that the later compatibility/C-tensor
  step consumes.
* `PartitionHashEncoding.xyIsolatedPowerAddresses` keeps the repeated `Z` blocks but is unmarked,
  so its count is the ambient count `N_triple` rather than the marked count `N_alpha`.

Everything here is therefore stated for `markedXYIsolatedTargets`: the count is against
`markedWords.card`, while the degree hypothesis and every uniqueness statement refer to the ambient
family.  The three-leg module is imported only for its general monotonicity lemma
`PartitionHashEncoding.legalTargets_mono`; none of its isolation or direct-sum endpoints is used.

## What is proved

* `markedXYIsolatedPowerAddresses` and its exact cardinality
  (`card_markedXYIsolatedPowerAddresses`), which is the marked target count, not the ambient one;
* every retained modeled address comes from a genuinely marked source word, with its transposed
  block address preserved
  (`exists_markedSourceWord_of_mem_markedXYIsolatedPowerAddresses`);
* containment in the ambient hash-filtered family, and `X`- and `Y`-leg injectivity of the modeled
  family --- the latter is `M-DWZ6`'s `hX`, derived rather than assumed;
* the semantic step: an ambient modeled power **restricts** to its marked XY-isolated
  subpartition, keeping repeated `Z` labels
  (`Tensor.Restricts.modeledTargets_to_markedXYIsolated`);
* the packaged good-seed statement `exists_seed_many_markedXYIsolatedPowerAddresses`, and its
  modulus form, which is what a laser client instantiates.

## Position in the library

Layer 3.  It introduces no new isolation combinatorics and no new tensor primitive: the isolation
core is `Combinatorics/MarkedTwoLegHashingExtraction.lean`'s and the zeroing primitive is
`Tensor.Restricts.partitionedUniqueXFibers`.

Primary source: Ran Duan, Hongxun Wu and Renfei Zhou, *Faster Matrix Multiplication via Asymmetric
Hashing*, arXiv:2210.10173.
-/

namespace AlgebraicComplexity

open Tensor

universe u v w x

variable {R : Type u} [Field R]
variable {A : Leg → Type w} [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]

namespace PartitionHashEncoding

variable {support : Finset (BlockAddress A)}

/-- Modeled block addresses of marked targets isolated on the `X` and `Y` legs against the ambient
target family.  The `Z` leg is deliberately unconstrained, so several retained addresses may share
one `Z` block word. -/
noncomputable def markedXYIsolatedPowerAddresses
    (H : PartitionHashEncoding (R := R) support) (n : ℕ)
    (ambientWords markedWords : Finset (PositiveWord support n))
    (B : Finset R) (seed : ProgressionHash.Seed R (Fin (n + 1))) :
    Finset (BlockAddress (fun c ↦ PositiveWord (A c) n)) :=
  H.modeledAddresses n
    (ProgressionHash.LegalTriple.markedXYIsolatedTargets
      (H.legalTargets n ambientWords) (H.legalTargets n markedWords) B seed)

omit [∀ c, Fintype (A c)] in
/-- Modeling marked XY-isolated targets preserves their cardinality, which is bounded by the
*marked* count. -/
theorem card_markedXYIsolatedPowerAddresses
    (H : PartitionHashEncoding (R := R) support) (n : ℕ)
    (ambientWords markedWords : Finset (PositiveWord support n))
    (hwords : markedWords ⊆ ambientWords) (B : Finset R)
    (seed : ProgressionHash.Seed R (Fin (n + 1))) :
    (H.markedXYIsolatedPowerAddresses n ambientWords markedWords B seed).card =
      (ProgressionHash.LegalTriple.markedXYIsolatedTargets
        (H.legalTargets n ambientWords) (H.legalTargets n markedWords) B seed).card := by
  apply H.card_modeledAddresses_of_subset n ambientWords
  exact (ProgressionHash.LegalTriple.markedXYIsolatedTargets_subset_marked
      (H.legalTargets n ambientWords) (H.legalTargets n markedWords) B seed).trans
    (H.legalTargets_mono n hwords)

omit [∀ c, Fintype (A c)] in
/-- **The hash loss stays visible.**  The retained modeled family is never larger than the marked
source family `N_alpha`. -/
theorem card_markedXYIsolatedPowerAddresses_le_card_markedWords
    (H : PartitionHashEncoding (R := R) support) (n : ℕ)
    (ambientWords markedWords : Finset (PositiveWord support n))
    (hwords : markedWords ⊆ ambientWords) (B : Finset R)
    (seed : ProgressionHash.Seed R (Fin (n + 1))) :
    (H.markedXYIsolatedPowerAddresses n ambientWords markedWords B seed).card ≤
      markedWords.card := by
  rw [H.card_markedXYIsolatedPowerAddresses n ambientWords markedWords hwords B seed,
    ← H.card_legalTargets n markedWords]
  exact ProgressionHash.LegalTriple.card_markedXYIsolatedTargets_le_card_marked
    (H.legalTargets n ambientWords) (H.legalTargets n markedWords) B seed

omit [∀ c, Fintype (A c)] in
/-- Every retained modeled address comes from a word of the marked source family, and its exact
transposed block address --- not merely its three marginal types --- is preserved.  Tensor clients
therefore rewrite the retained constituent to the constituent indexed by the recovered word. -/
theorem exists_markedSourceWord_of_mem_markedXYIsolatedPowerAddresses
    (H : PartitionHashEncoding (R := R) support) (n : ℕ)
    (ambientWords markedWords : Finset (PositiveWord support n))
    (B : Finset R) (seed : ProgressionHash.Seed R (Fin (n + 1)))
    {address : BlockAddress (fun c ↦ PositiveWord (A c) n)}
    (haddress : address ∈
      H.markedXYIsolatedPowerAddresses n ambientWords markedWords B seed) :
    ∃ word ∈ markedWords, supportWordAddress n word = address := by
  classical
  unfold markedXYIsolatedPowerAddresses modeledAddresses at haddress
  obtain ⟨triple, htriple, rfl⟩ := Finset.mem_image.mp haddress
  have hmarked : triple ∈ H.legalTargets n markedWords :=
    ProgressionHash.LegalTriple.markedXYIsolatedTargets_subset_marked
      (H.legalTargets n ambientWords) (H.legalTargets n markedWords) B seed htriple
  refine ⟨H.sourceWordOfLegalTriple n triple,
    H.sourceWordOfLegalTriple_mem_of_mem n markedWords hmarked, ?_⟩
  rfl

omit [∀ c, Fintype (A c)] in
/-- Retained marked modeled addresses lie in the ambient hash-filtered partition. -/
theorem markedXYIsolatedPowerAddresses_subset_filteredPowerAddresses
    [NeZero (2 : R)]
    (H : PartitionHashEncoding (R := R) support) (n : ℕ)
    (ambientWords markedWords : Finset (PositiveWord support n))
    (hwords : markedWords ⊆ ambientWords) (B : Finset R)
    (seed : ProgressionHash.Seed R (Fin (n + 1))) :
    H.markedXYIsolatedPowerAddresses n ambientWords markedWords B seed ⊆
      H.filteredPowerAddresses n ambientWords B seed := by
  classical
  unfold markedXYIsolatedPowerAddresses filteredPowerAddresses modeledAddresses
  exact Finset.image_mono _
    (ProgressionHash.LegalTriple.markedXYIsolatedTargets_subset_filteredTargets
      (H.legalTargets n ambientWords) (H.legalTargets n markedWords)
      (H.legalTargets_mono n hwords) B seed)

omit [∀ c, Fintype (A c)] in
/-- **`M-DWZ6`'s `hX`, derived.**  The retained marked modeled family has pairwise distinct `X`
block words. -/
theorem x_injectiveOn_markedXYIsolatedPowerAddresses
    [NeZero (2 : R)]
    (H : PartitionHashEncoding (R := R) support) (n : ℕ)
    (ambientWords markedWords : Finset (PositiveWord support n))
    (hwords : markedWords ⊆ ambientWords) (B : Finset R)
    (hB : ThreeAPFree (B : Set R))
    (seed : ProgressionHash.Seed R (Fin (n + 1))) :
    Set.InjOn (fun s : BlockAddress (fun c ↦ PositiveWord (A c) n) ↦ s .X)
      (H.markedXYIsolatedPowerAddresses n ambientWords markedWords B seed : Set _) := by
  classical
  intro left hleft right hright hx
  unfold markedXYIsolatedPowerAddresses modeledAddresses at hleft hright
  obtain ⟨leftTriple, hleftTriple, rfl⟩ := Finset.mem_image.mp hleft
  obtain ⟨rightTriple, hrightTriple, rfl⟩ := Finset.mem_image.mp hright
  have htargets := H.legalTargets_mono n hwords
  have hleftTarget : leftTriple ∈ H.legalTargets n ambientWords :=
    ProgressionHash.LegalTriple.filteredTargets_subset
      (H.legalTargets n ambientWords) B seed
      (ProgressionHash.LegalTriple.markedXYIsolatedTargets_subset_filteredTargets
        (H.legalTargets n ambientWords) (H.legalTargets n markedWords) htargets B seed
        hleftTriple)
  have hrightTarget : rightTriple ∈ H.legalTargets n ambientWords :=
    ProgressionHash.LegalTriple.filteredTargets_subset
      (H.legalTargets n ambientWords) B seed
      (ProgressionHash.LegalTriple.markedXYIsolatedTargets_subset_filteredTargets
        (H.legalTargets n ambientWords) (H.legalTargets n markedWords) htargets B seed
        hrightTriple)
  have hindex : leftTriple.xIndex = rightTriple.xIndex := by
    simpa using (H.modeledAddress_leg_eq_iff n ambientWords hleftTarget hrightTarget .X).mp hx
  have heq := ProgressionHash.LegalTriple.xIndex_injectiveOn_markedXYIsolatedTargets
    (H.legalTargets n ambientWords) (H.legalTargets n markedWords) htargets B hB seed
    hleftTriple hrightTriple hindex
  subst rightTriple
  rfl

omit [∀ c, Fintype (A c)] in
/-- The retained marked modeled family has pairwise distinct `Y` block words.  `M-DWZ6` consumes
only `X`-injectivity, but `Y`-injectivity is what validates the first compatibility zero-out. -/
theorem y_injectiveOn_markedXYIsolatedPowerAddresses
    [NeZero (2 : R)]
    (H : PartitionHashEncoding (R := R) support) (n : ℕ)
    (ambientWords markedWords : Finset (PositiveWord support n))
    (hwords : markedWords ⊆ ambientWords) (B : Finset R)
    (hB : ThreeAPFree (B : Set R))
    (seed : ProgressionHash.Seed R (Fin (n + 1))) :
    Set.InjOn (fun s : BlockAddress (fun c ↦ PositiveWord (A c) n) ↦ s .Y)
      (H.markedXYIsolatedPowerAddresses n ambientWords markedWords B seed : Set _) := by
  classical
  intro left hleft right hright hy
  unfold markedXYIsolatedPowerAddresses modeledAddresses at hleft hright
  obtain ⟨leftTriple, hleftTriple, rfl⟩ := Finset.mem_image.mp hleft
  obtain ⟨rightTriple, hrightTriple, rfl⟩ := Finset.mem_image.mp hright
  have htargets := H.legalTargets_mono n hwords
  have hleftTarget : leftTriple ∈ H.legalTargets n ambientWords :=
    ProgressionHash.LegalTriple.filteredTargets_subset
      (H.legalTargets n ambientWords) B seed
      (ProgressionHash.LegalTriple.markedXYIsolatedTargets_subset_filteredTargets
        (H.legalTargets n ambientWords) (H.legalTargets n markedWords) htargets B seed
        hleftTriple)
  have hrightTarget : rightTriple ∈ H.legalTargets n ambientWords :=
    ProgressionHash.LegalTriple.filteredTargets_subset
      (H.legalTargets n ambientWords) B seed
      (ProgressionHash.LegalTriple.markedXYIsolatedTargets_subset_filteredTargets
        (H.legalTargets n ambientWords) (H.legalTargets n markedWords) htargets B seed
        hrightTriple)
  have hindex : leftTriple.yIndex = rightTriple.yIndex := by
    simpa using (H.modeledAddress_leg_eq_iff n ambientWords hleftTarget hrightTarget .Y).mp hy
  have heq := ProgressionHash.LegalTriple.yIndex_injectiveOn_markedXYIsolatedTargets
    (H.legalTargets n ambientWords) (H.legalTargets n markedWords) htargets B hB seed
    hleftTriple hrightTriple hindex
  subst rightTriple
  rfl

omit [∀ c, Fintype (A c)] in
/-- Every retained marked modeled address is the unique **ambient** hash survivor in its `X`
fiber.  This is the exact zeroing certificate: keeping a selected `X` block cannot accidentally
keep an unmarked ambient constituent, while repeated `Z` fibers are untouched. -/
theorem markedXYIsolatedPowerAddresses_hasUniqueXFibers
    [NeZero (2 : R)]
    (H : PartitionHashEncoding (R := R) support) (n : ℕ)
    (ambientWords markedWords : Finset (PositiveWord support n))
    (hwords : markedWords ⊆ ambientWords) (B : Finset R)
    (hB : ThreeAPFree (B : Set R))
    (seed : ProgressionHash.Seed R (Fin (n + 1))) :
    HasUniqueLegFibers (H.filteredPowerAddresses n ambientWords B seed)
      (H.markedXYIsolatedPowerAddresses n ambientWords markedWords B seed) .X := by
  classical
  refine ⟨H.markedXYIsolatedPowerAddresses_subset_filteredPowerAddresses
    n ambientWords markedWords hwords B seed, ?_⟩
  intro selected hselected surviving hsurviving hx
  unfold markedXYIsolatedPowerAddresses modeledAddresses at hselected
  unfold filteredPowerAddresses modeledAddresses at hsurviving
  obtain ⟨selectedTriple, hselectedTriple, rfl⟩ := Finset.mem_image.mp hselected
  obtain ⟨survivingTriple, hsurvivingTriple, rfl⟩ := Finset.mem_image.mp hsurviving
  have htargets := H.legalTargets_mono n hwords
  have hselectedTarget : selectedTriple ∈ H.legalTargets n ambientWords :=
    ProgressionHash.LegalTriple.filteredTargets_subset
      (H.legalTargets n ambientWords) B seed
      (ProgressionHash.LegalTriple.markedXYIsolatedTargets_subset_filteredTargets
        (H.legalTargets n ambientWords) (H.legalTargets n markedWords) htargets B seed
        hselectedTriple)
  have hsurvivingTarget : survivingTriple ∈ H.legalTargets n ambientWords :=
    ProgressionHash.LegalTriple.filteredTargets_subset
      (H.legalTargets n ambientWords) B seed hsurvivingTriple
  have hindex : survivingTriple.xIndex = selectedTriple.xIndex := by
    simpa using
      (H.modeledAddress_leg_eq_iff n ambientWords hsurvivingTarget hselectedTarget .X).mp hx
  have heq : survivingTriple = selectedTriple :=
    ProgressionHash.LegalTriple.eq_of_mem_markedXYIsolatedTargets_of_mem_filteredTargets
      (H.legalTargets n ambientWords) (H.legalTargets n markedWords) htargets B hB seed
      hselectedTriple hsurvivingTriple (Or.inl hindex.symm)
  subst survivingTriple
  rfl

omit [∀ c, Fintype (A c)] in
/-- **The marked asymmetric good-seed theorem in the block-word representation.**  One affine seed
retains a large marked modeled family which survives the ambient hash filter, has pairwise
distinct `X` and `Y` block words, and carries no `Z` constraint whatsoever.

The count is against the marked source family, while the degree hypothesis and both injectivity
conclusions refer to the ambient family; that asymmetry is `[DuanWuZhou2022]`'s hash loss. -/
theorem exists_seed_many_markedXYIsolatedPowerAddresses
    [Fintype R] [NeZero (2 : R)]
    (H : PartitionHashEncoding (R := R) support) (n : ℕ)
    (ambientWords markedWords : Finset (PositiveWord support n))
    (hwords : markedWords ⊆ ambientWords) (B : Finset R)
    (hB : ThreeAPFree (B : Set R))
    (hquarter : ∀ triple ∈ H.legalTargets n markedWords,
      4 * (ProgressionHash.LegalTriple.xyCompetitorYIndices
        (H.legalTargets n ambientWords) triple).card ≤ Fintype.card R) :
    ∃ seed : ProgressionHash.Seed R (Fin (n + 1)),
      3 * markedWords.card * B.card ≤
          4 * (Fintype.card R * Fintype.card R) *
            (H.markedXYIsolatedPowerAddresses
              n ambientWords markedWords B seed).card ∧
        H.markedXYIsolatedPowerAddresses n ambientWords markedWords B seed ⊆
          H.filteredPowerAddresses n ambientWords B seed ∧
        Set.InjOn (fun s : BlockAddress (fun c ↦ PositiveWord (A c) n) ↦ s .X)
          (H.markedXYIsolatedPowerAddresses n ambientWords markedWords B seed : Set _) ∧
        Set.InjOn (fun s : BlockAddress (fun c ↦ PositiveWord (A c) n) ↦ s .Y)
          (H.markedXYIsolatedPowerAddresses n ambientWords markedWords B seed : Set _) := by
  have htargets := H.legalTargets_mono n hwords
  obtain ⟨seed, hcount, _hsubset, _hinjX, _hinjY⟩ :=
    ProgressionHash.LegalTriple.exists_seed_many_markedXYIsolatedTargets
      (H.legalTargets n ambientWords) (H.legalTargets n markedWords)
      htargets B hB hquarter
  refine ⟨seed, ?_, ?_, ?_, ?_⟩
  · rw [H.card_markedXYIsolatedPowerAddresses n ambientWords markedWords hwords B seed]
    simpa [H.card_legalTargets n markedWords] using hcount
  · exact H.markedXYIsolatedPowerAddresses_subset_filteredPowerAddresses
      n ambientWords markedWords hwords B seed
  · exact H.x_injectiveOn_markedXYIsolatedPowerAddresses
      n ambientWords markedWords hwords B hB seed
  · exact H.y_injectiveOn_markedXYIsolatedPowerAddresses
      n ambientWords markedWords hwords B hB seed

omit [∀ c, Fintype (A c)] in
/-- The form a laser client instantiates: it mentions only the common ambient leg-fiber degree `d`
of every marked target and `[DuanWuZhou2022]`'s modulus condition `8 * d ≤ |R|`. -/
theorem exists_seed_many_markedXYIsolatedPowerAddresses_of_modulus
    [Fintype R] [NeZero (2 : R)]
    (H : PartitionHashEncoding (R := R) support) (n : ℕ)
    (ambientWords markedWords : Finset (PositiveWord support n))
    (hwords : markedWords ⊆ ambientWords) (B : Finset R)
    (hB : ThreeAPFree (B : Set R)) (d : ℕ)
    (hX : ∀ triple ∈ H.legalTargets n markedWords,
      (ProgressionHash.LegalTriple.legFiber (H.legalTargets n ambientWords) triple .X).card ≤ d)
    (hY : ∀ triple ∈ H.legalTargets n markedWords,
      (ProgressionHash.LegalTriple.legFiber (H.legalTargets n ambientWords) triple .Y).card ≤ d)
    (hmodulus : 8 * d ≤ Fintype.card R) :
    ∃ seed : ProgressionHash.Seed R (Fin (n + 1)),
      3 * markedWords.card * B.card ≤
          4 * (Fintype.card R * Fintype.card R) *
            (H.markedXYIsolatedPowerAddresses
              n ambientWords markedWords B seed).card ∧
        H.markedXYIsolatedPowerAddresses n ambientWords markedWords B seed ⊆
          H.filteredPowerAddresses n ambientWords B seed ∧
        Set.InjOn (fun s : BlockAddress (fun c ↦ PositiveWord (A c) n) ↦ s .X)
          (H.markedXYIsolatedPowerAddresses n ambientWords markedWords B seed : Set _) ∧
        Set.InjOn (fun s : BlockAddress (fun c ↦ PositiveWord (A c) n) ↦ s .Y)
          (H.markedXYIsolatedPowerAddresses n ambientWords markedWords B seed : Set _) :=
  H.exists_seed_many_markedXYIsolatedPowerAddresses n ambientWords markedWords hwords B hB
    (ProgressionHash.LegalTriple.quarter_of_eight_mul_legFiber_le
      (H.legalTargets n ambientWords) (H.legalTargets n markedWords) d hX hY hmodulus)

section TensorExtraction

variable {K : Type v} [CommSemiring K]
variable {n : ℕ}
variable {V : ∀ c, PositiveWord (A c) n → Type x}
variable [∀ c a, AddCommMonoid (V c a)] [∀ c a, Module K (V c a)]

/-- An ambient hash-filtered power restricts exactly to its marked XY-isolated subpartition.  The
result is a subpartition, **not** an indexed direct sum: repeated `Z` block words are preserved for
the subsequent compatibility and C-tensor steps. -/
theorem _root_.AlgebraicComplexity.Tensor.Restricts.hashFilteredPower_to_markedXYIsolated
    [NeZero (2 : R)]
    (H : PartitionHashEncoding (R := R) support)
    (ambientWords markedWords : Finset (PositiveWord support n))
    (hwords : markedWords ⊆ ambientWords) (B : Finset R)
    (hB : ThreeAPFree (B : Set R))
    (seed : ProgressionHash.Seed R (Fin (n + 1)))
    (P : PartitionedTensor (K := K) (A := fun c ↦ PositiveWord (A c) n) V)
    (hsupport : P.support = H.filteredPowerAddresses n ambientWords B seed) :
    Restricts P.realize
      (P.withSupport
        (H.markedXYIsolatedPowerAddresses n ambientWords markedWords B seed)).realize := by
  apply Tensor.Restricts.partitionedUniqueXFibers P
    (H.markedXYIsolatedPowerAddresses n ambientWords markedWords B seed)
  rw [hsupport]
  exact H.markedXYIsolatedPowerAddresses_hasUniqueXFibers
    n ambientWords markedWords hwords B hB seed

/-- **Complete marked asymmetric extraction in the block-word representation.**  Independent hash
block zeroing on the ambient modeled power, followed by marked XY isolation, restricts to the
retained marked subpartition with all repeated `Z` blocks intact. -/
theorem _root_.AlgebraicComplexity.Tensor.Restricts.modeledTargets_to_markedXYIsolated
    [NeZero (2 : R)]
    (H : PartitionHashEncoding (R := R) support)
    (ambientWords markedWords : Finset (PositiveWord support n))
    (hwords : markedWords ⊆ ambientWords) (B : Finset R)
    (hB : ThreeAPFree (B : Set R))
    (seed : ProgressionHash.Seed R (Fin (n + 1)))
    (P : PartitionedTensor (K := K) (A := fun c ↦ PositiveWord (A c) n) V)
    (hsupport : P.support = H.modeledAddresses n (H.legalTargets n ambientWords)) :
    Restricts P.realize
      (P.withSupport
        (H.markedXYIsolatedPowerAddresses n ambientWords markedWords B seed)).realize := by
  exact (Tensor.Restricts.modeledTargets_to_hashFilteredPower
      H ambientWords B seed P hsupport).trans
    (by
      simpa only [PartitionedTensor.withSupport] using
        Tensor.Restricts.hashFilteredPower_to_markedXYIsolated
          H ambientWords markedWords hwords B hB seed
          (P.withSupport (H.filteredPowerAddresses n ambientWords B seed)) rfl)

end TensorExtraction

/-! ### Regression against the unmarked two-leg transport -/

omit [∀ c, Fintype (A c)] in
/-- At `markedWords = ambientWords` the marked construction **is** the unmarked one,
definitionally.  This records that the unmarked XY-isolated modeled family is the marked family
with a trivial marking, so the two must never drift apart. -/
theorem markedXYIsolatedPowerAddresses_self
    (H : PartitionHashEncoding (R := R) support) (n : ℕ)
    (words : Finset (PositiveWord support n)) (B : Finset R)
    (seed : ProgressionHash.Seed R (Fin (n + 1))) :
    H.markedXYIsolatedPowerAddresses n words words B seed =
      H.xyIsolatedPowerAddresses n words B seed := rfl

end PartitionHashEncoding

end AlgebraicComplexity
