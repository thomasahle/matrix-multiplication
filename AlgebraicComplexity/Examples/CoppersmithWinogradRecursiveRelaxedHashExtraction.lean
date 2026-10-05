/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinogradRecursiveRelaxedCoarseFamily

/-!
# Marked X-only hashing on the relaxed recursive CW family

The recursive constituent argument averages its affine hash over the abstract marginal-word
family, not over the quotient blocks which happen to occur in one chosen parent empirical type.
This module performs that finite extraction on the relaxed family constructed in
`CoppersmithWinogradRecursiveRelaxedCoarseFamily`.

The output is a set of intended quotient addresses.  Some of these addresses can have empty fine
preimage in the approximately selected parent tensor; those are the input-profile holes handled
later by concentration and repair.  Thus no existence of a fine lift is assumed here.

The principal theorem, `exists_seed_many_relaxedRecursiveMarkedXIsolatedCoarseSupport`, has the
paper's exact finite count: the numerator is `N_alpha`, all X-competitors come from `N_triple`,
and the surviving intended addresses have pairwise distinct physical `sigma X` words.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor MoreAsymmetryCompatibility

universe v

namespace CWCoarseFieldEncoding

variable {R : Type v} [Field R]

/-- Abstract marginal words whose legal triples survive marked X-only isolation. -/
noncomputable def relaxedRecursiveMarkedXIsolatedSources
    (encoding : CWCoarseFieldEncoding R depth)
    {n : ℕ}
    (term : ExactInterfaceTermParameters (depth + 1))
    (sigma : Orientation)
    (alpha : ExactRecursiveSplitType
      (cwRecursiveLogicalParent term sigma) (coarseTotal depth) (n + 1))
    (B : Finset R)
    (seed : ProgressionHash.Seed R (Fin ((n + 1) + (n + 1)))) := by
  classical
  exact Finset.univ.filter fun source : {word // word ∈ alpha.marginalWords} ↦
    encoding.relaxedRecursiveOrientedLegalTriple term sigma source.1 ∈
      ProgressionHash.LegalTriple.markedXIsolatedTargets
        (encoding.relaxedRecursiveAmbientTargets term sigma alpha)
        (encoding.relaxedRecursiveMarkedTargets term sigma alpha) B seed

/-- Intended quotient addresses retained by marked X-only isolation of the relaxed family. -/
noncomputable def relaxedRecursiveMarkedXIsolatedCoarseSupport
    (encoding : CWCoarseFieldEncoding R depth)
    {n : ℕ}
    (term : ExactInterfaceTermParameters (depth + 1))
    (sigma : Orientation)
    (alpha : ExactRecursiveSplitType
      (cwRecursiveLogicalParent term sigma) (coarseTotal depth) (n + 1))
    (B : Finset R)
    (seed : ProgressionHash.Seed R (Fin ((n + 1) + (n + 1)))) :
    Finset (CWRecursiveCoarseAddress depth n) := by
  classical
  exact (encoding.relaxedRecursiveMarkedXIsolatedSources
    term sigma alpha B seed).image fun source ↦
      cwRecursiveCoarseAddressOfLeftShapeWord term sigma source.1

@[simp] theorem mem_relaxedRecursiveMarkedXIsolatedCoarseSupport_iff
    (encoding : CWCoarseFieldEncoding R depth)
    {n : ℕ}
    (term : ExactInterfaceTermParameters (depth + 1))
    (sigma : Orientation)
    (alpha : ExactRecursiveSplitType
      (cwRecursiveLogicalParent term sigma) (coarseTotal depth) (n + 1))
    (B : Finset R)
    (seed : ProgressionHash.Seed R (Fin ((n + 1) + (n + 1))))
    (source : {word // word ∈ alpha.marginalWords}) :
    cwRecursiveCoarseAddressOfLeftShapeWord term sigma source.1 ∈
        encoding.relaxedRecursiveMarkedXIsolatedCoarseSupport
          term sigma alpha B seed ↔
      encoding.relaxedRecursiveOrientedLegalTriple term sigma source.1 ∈
        ProgressionHash.LegalTriple.markedXIsolatedTargets
          (encoding.relaxedRecursiveAmbientTargets term sigma alpha)
          (encoding.relaxedRecursiveMarkedTargets term sigma alpha) B seed := by
  classical
  constructor
  · intro hsource
    rw [relaxedRecursiveMarkedXIsolatedCoarseSupport, Finset.mem_image] at hsource
    obtain ⟨other, hother, hvalue⟩ := hsource
    have hword : other.1 = source.1 :=
      cwRecursiveCoarseAddressOfLeftShapeWord_injective term sigma hvalue
    have hsourceEq : other = source := Subtype.ext hword
    subst other
    exact (Finset.mem_filter.mp hother).2
  · intro hsource
    unfold relaxedRecursiveMarkedXIsolatedCoarseSupport
      relaxedRecursiveMarkedXIsolatedSources
    exact Finset.mem_image.mpr
      ⟨source, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hsource⟩, rfl⟩

/-- Every intended isolated address is a marked joint-type address. -/
theorem relaxedRecursiveMarkedXIsolatedCoarseSupport_subset_marked
    (encoding : CWCoarseFieldEncoding R depth)
    {n : ℕ}
    (term : ExactInterfaceTermParameters (depth + 1))
    (sigma : Orientation)
    (alpha : ExactRecursiveSplitType
      (cwRecursiveLogicalParent term sigma) (coarseTotal depth) (n + 1))
    (B : Finset R)
    (seed : ProgressionHash.Seed R (Fin ((n + 1) + (n + 1)))) :
    encoding.relaxedRecursiveMarkedXIsolatedCoarseSupport
        term sigma alpha B seed ⊆
      cwRecursiveRelaxedMarkedCoarseSupport term sigma alpha := by
  classical
  intro address haddress
  rw [relaxedRecursiveMarkedXIsolatedCoarseSupport, Finset.mem_image] at haddress
  obtain ⟨source, hsource, rfl⟩ := haddress
  have hisolated := (Finset.mem_filter.mp hsource).2
  have hmarked :=
    ProgressionHash.LegalTriple.markedXIsolatedTargets_subset_marked
      (encoding.relaxedRecursiveAmbientTargets term sigma alpha)
      (encoding.relaxedRecursiveMarkedTargets term sigma alpha) B seed hisolated
  rw [relaxedRecursiveMarkedTargets, Finset.mem_image] at hmarked
  obtain ⟨word, hword, heq⟩ := hmarked
  have hwordSource : word = source.1 :=
    encoding.relaxedRecursiveOrientedLegalTriple_injective term sigma heq
  unfold cwRecursiveRelaxedMarkedCoarseSupport
  exact Finset.mem_image.mpr ⟨word, hword, congrArg _ hwordSource⟩

/-- Every intended isolated address belongs to the relaxed ambient family. -/
theorem relaxedRecursiveMarkedXIsolatedCoarseSupport_subset_ambient
    (encoding : CWCoarseFieldEncoding R depth)
    {n : ℕ}
    (term : ExactInterfaceTermParameters (depth + 1))
    (sigma : Orientation)
    (alpha : ExactRecursiveSplitType
      (cwRecursiveLogicalParent term sigma) (coarseTotal depth) (n + 1))
    (B : Finset R)
    (seed : ProgressionHash.Seed R (Fin ((n + 1) + (n + 1)))) :
    encoding.relaxedRecursiveMarkedXIsolatedCoarseSupport
        term sigma alpha B seed ⊆
      cwRecursiveRelaxedAmbientCoarseSupport term sigma alpha :=
  (encoding.relaxedRecursiveMarkedXIsolatedCoarseSupport_subset_marked
    term sigma alpha B seed).trans
      (cwRecursiveRelaxedMarkedCoarseSupport_subset_ambient term sigma alpha)

/-- Source-side and legal-triple-side relaxed isolated families have identical cardinality. -/
theorem card_relaxedRecursiveMarkedXIsolatedCoarseSupport
    (encoding : CWCoarseFieldEncoding R depth)
    {n : ℕ}
    (term : ExactInterfaceTermParameters (depth + 1))
    (sigma : Orientation)
    (alpha : ExactRecursiveSplitType
      (cwRecursiveLogicalParent term sigma) (coarseTotal depth) (n + 1))
    (B : Finset R)
    (seed : ProgressionHash.Seed R (Fin ((n + 1) + (n + 1)))) :
    (encoding.relaxedRecursiveMarkedXIsolatedCoarseSupport
        term sigma alpha B seed).card =
      (ProgressionHash.LegalTriple.markedXIsolatedTargets
        (encoding.relaxedRecursiveAmbientTargets term sigma alpha)
        (encoding.relaxedRecursiveMarkedTargets term sigma alpha) B seed).card := by
  classical
  let sources := encoding.relaxedRecursiveMarkedXIsolatedSources
    term sigma alpha B seed
  let ambient := encoding.relaxedRecursiveAmbientTargets term sigma alpha
  let marked := encoding.relaxedRecursiveMarkedTargets term sigma alpha
  let isolated := ProgressionHash.LegalTriple.markedXIsolatedTargets
    ambient marked B seed
  have hmarked : marked ⊆ ambient :=
    encoding.relaxedRecursiveMarkedTargets_subset_ambientTargets term sigma alpha
  have himage : isolated = sources.image
      (fun source ↦ encoding.relaxedRecursiveOrientedLegalTriple
        term sigma source.1) := by
    ext triple
    constructor
    · intro htriple
      have htarget : triple ∈ ambient :=
        hmarked <| ProgressionHash.LegalTriple.markedXIsolatedTargets_subset_marked
          ambient marked B seed htriple
      unfold ambient relaxedRecursiveAmbientTargets at htarget
      obtain ⟨word, hword, rfl⟩ := Finset.mem_image.mp htarget
      let source : {word // word ∈ alpha.marginalWords} := ⟨word, hword⟩
      exact Finset.mem_image.mpr
        ⟨source, Finset.mem_filter.mpr ⟨Finset.mem_univ _, htriple⟩, rfl⟩
    · intro htriple
      obtain ⟨source, hsource, rfl⟩ := Finset.mem_image.mp htriple
      exact (Finset.mem_filter.mp hsource).2
  change
    (sources.image (fun source ↦
      cwRecursiveCoarseAddressOfLeftShapeWord term sigma source.1)).card =
      isolated.card
  have hsourceInjective : Set.InjOn
      (fun source : {word // word ∈ alpha.marginalWords} ↦
        cwRecursiveCoarseAddressOfLeftShapeWord term sigma source.1) sources :=
    ((cwRecursiveCoarseAddressOfLeftShapeWord_injective term sigma).comp
      Subtype.val_injective).injOn
  have hsourceCard :
      (sources.image (fun source ↦
        cwRecursiveCoarseAddressOfLeftShapeWord term sigma source.1)).card =
        sources.card :=
    Finset.card_image_of_injOn hsourceInjective
  have htripleInjective : Set.InjOn
      (fun source : {word // word ∈ alpha.marginalWords} ↦
        encoding.relaxedRecursiveOrientedLegalTriple term sigma source.1) sources :=
    ((encoding.relaxedRecursiveOrientedLegalTriple_injective term sigma).comp
      Subtype.val_injective).injOn
  have htripleCard :
      (sources.image (fun source ↦
        encoding.relaxedRecursiveOrientedLegalTriple term sigma source.1)).card =
        sources.card :=
    Finset.card_image_of_injOn htripleInjective
  rw [hsourceCard]
  calc
    sources.card =
        (sources.image (fun source ↦
          encoding.relaxedRecursiveOrientedLegalTriple term sigma source.1)).card := htripleCard.symm
    _ = isolated.card := congrArg Finset.card himage.symm

/-- Relaxed marked X-only isolation makes the physical `sigma X` quotient label injective. -/
theorem relaxedRecursiveX_injectiveOn_markedXIsolatedCoarseSupport
    (encoding : CWCoarseFieldEncoding R depth)
    {n : ℕ}
    (term : ExactInterfaceTermParameters (depth + 1))
    (sigma : Orientation)
    (alpha : ExactRecursiveSplitType
      (cwRecursiveLogicalParent term sigma) (coarseTotal depth) (n + 1))
    (B : Finset R)
    (seed : ProgressionHash.Seed R (Fin ((n + 1) + (n + 1)))) :
    Set.InjOn
      (fun address : CWRecursiveCoarseAddress depth n ↦ address (sigma .X))
      (encoding.relaxedRecursiveMarkedXIsolatedCoarseSupport
        term sigma alpha B seed : Set _) := by
  classical
  let ambient := encoding.relaxedRecursiveAmbientTargets term sigma alpha
  let marked := encoding.relaxedRecursiveMarkedTargets term sigma alpha
  let isolated := ProgressionHash.LegalTriple.markedXIsolatedTargets
    ambient marked B seed
  have hmarked : marked ⊆ ambient :=
    encoding.relaxedRecursiveMarkedTargets_subset_ambientTargets term sigma alpha
  intro left hleft right hright hx
  change left ∈ encoding.relaxedRecursiveMarkedXIsolatedCoarseSupport
    term sigma alpha B seed at hleft
  change right ∈ encoding.relaxedRecursiveMarkedXIsolatedCoarseSupport
    term sigma alpha B seed at hright
  rw [relaxedRecursiveMarkedXIsolatedCoarseSupport, Finset.mem_image] at hleft hright
  obtain ⟨leftSource, hleftSource, rfl⟩ := hleft
  obtain ⟨rightSource, hrightSource, rfl⟩ := hright
  have hleftIsolated :
      encoding.relaxedRecursiveOrientedLegalTriple
        term sigma leftSource.1 ∈ isolated :=
    (Finset.mem_filter.mp hleftSource).2
  have hrightIsolated :
      encoding.relaxedRecursiveOrientedLegalTriple
        term sigma rightSource.1 ∈ isolated :=
    (Finset.mem_filter.mp hrightSource).2
  have hindex :
      (encoding.relaxedRecursiveOrientedLegalTriple
        term sigma leftSource.1).xIndex =
      (encoding.relaxedRecursiveOrientedLegalTriple
        term sigma rightSource.1).xIndex := by
    funext occurrence
    exact congrArg encoding.encode (congrFun hx occurrence)
  have htarget :=
    ProgressionHash.LegalTriple.xIndex_injectiveOn_markedXIsolatedTargets
      ambient marked hmarked B seed hleftIsolated hrightIsolated hindex
  exact congrArg (cwRecursiveCoarseAddressOfLeftShapeWord term sigma) <|
    encoding.relaxedRecursiveOrientedLegalTriple_injective term sigma htarget

/-- Orientation-parametric finite marked X-only extraction on the paper's relaxed family. -/
theorem exists_seed_many_relaxedRecursiveMarkedXIsolatedCoarseSupport
    (encoding : CWCoarseFieldEncoding R depth)
    [Fintype R] [NeZero (2 : R)]
    {n : ℕ}
    (term : ExactInterfaceTermParameters (depth + 1))
    (sigma : Orientation)
    (alpha : ExactRecursiveSplitType
      (cwRecursiveLogicalParent term sigma) (coarseTotal depth) (n + 1))
    (B : Finset R)
    (hquarter : ∀ triple ∈ encoding.relaxedRecursiveMarkedTargets
        term sigma alpha,
      4 * (ProgressionHash.LegalTriple.xCompetitorYIndices
        (encoding.relaxedRecursiveAmbientTargets term sigma alpha) triple).card ≤
          Fintype.card R) :
    ∃ seed : ProgressionHash.Seed R (Fin ((n + 1) + (n + 1))),
      3 * Nat.multinomial Finset.univ alpha.count * B.card ≤
        4 * (Fintype.card R * Fintype.card R) *
          (encoding.relaxedRecursiveMarkedXIsolatedCoarseSupport
            term sigma alpha B seed).card ∧
      encoding.relaxedRecursiveMarkedXIsolatedCoarseSupport
          term sigma alpha B seed ⊆
        cwRecursiveRelaxedMarkedCoarseSupport term sigma alpha ∧
      Set.InjOn
        (fun address : CWRecursiveCoarseAddress depth n ↦ address (sigma .X))
        (encoding.relaxedRecursiveMarkedXIsolatedCoarseSupport
          term sigma alpha B seed : Set _) := by
  let ambient := encoding.relaxedRecursiveAmbientTargets term sigma alpha
  let marked := encoding.relaxedRecursiveMarkedTargets term sigma alpha
  have hmarked : marked ⊆ ambient :=
    encoding.relaxedRecursiveMarkedTargets_subset_ambientTargets term sigma alpha
  obtain ⟨seed, hcount, _hfiltered, _hinjective⟩ :=
    ProgressionHash.LegalTriple.exists_seed_many_markedXIsolatedTargets
      ambient marked hmarked B hquarter
  refine ⟨seed, ?_,
    encoding.relaxedRecursiveMarkedXIsolatedCoarseSupport_subset_marked
      term sigma alpha B seed,
    encoding.relaxedRecursiveX_injectiveOn_markedXIsolatedCoarseSupport
      term sigma alpha B seed⟩
  rw [encoding.card_relaxedRecursiveMarkedXIsolatedCoarseSupport
      term sigma alpha B seed,
    ← encoding.card_relaxedRecursiveMarkedTargets term sigma alpha]
  exact hcount

end CWCoarseFieldEncoding

end AlgebraicComplexity.Examples
