/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinogradRecursiveCleanup

/-!
# Tensor-level marked X-only hashing for recursive CW constituents

The recursive constituent theorem first selects the three ordered-child marginal types, applies a
common-bucket affine hash to the complete labelled-child weight words, and isolates only the X
word of a marked joint-type target against all ambient marginal-type competitors.  Compatibility
and usefulness zero-outs subsequently make Y and Z readable.

`CoppersmithWinogradRecursiveHashing` constructs the ambient and marked finite legal-triple
families, while `MarkedXHashingExtraction` proves the exact finite count.  This module supplies the
semantic bridge back to the tensor:

* selected legal triples are identified with actual recursive quotient addresses;
* their exact cardinality and physical-`sigma X` injectivity are transported without choosing
  representatives;
* the common-bucket filter is realized by three independent block zero-outs on the fine tensor;
* ambient X-fiber uniqueness then zeroes the filtered tensor to the **entire** fine preimage of
  every selected marked quotient address; and
* this restriction composes with the grouped recursive compatibility cleanup.

No assembled restriction, target box, survivor count, repair plan, or asymptotic estimate is a
hypothesis.  The remaining quantitative obligation after this file is the ambient X-fiber degree
bound, followed by the compatibility competitor count, sparse repair, and intact-family theorem.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor MoreAsymmetryCompatibility

universe u v

namespace CWCoarseFieldEncoding

variable {R : Type v} [Field R]

/-! ## Selected quotient addresses and the exact finite count -/

/-- Ambient quotient sources whose legal triples belong to the marked X-only isolated family. -/
noncomputable def recursiveMarkedXIsolatedSources
    (encoding : CWCoarseFieldEncoding R depth)
    (K : Type u) [CommRing K] (q : ℕ) {n : ℕ}
    (term : ExactInterfaceTermParameters (depth + 1))
    (hmultiplicity : term.multiplicity = n + 1)
    (sigma : Orientation)
    (alpha : ExactRecursiveSplitType
      (cwRecursiveLogicalParent term sigma) (coarseTotal depth) (n + 1))
    (B : Finset R)
    (seed : ProgressionHash.Seed R (Fin ((n + 1) + (n + 1)))) := by
  classical
  exact Finset.univ.filter fun source : {address : CWRecursiveCoarseAddress depth n //
      address ∈ (cwRecursiveCoarsenedAlphaMarginalTerm
        K q term hmultiplicity sigma alpha).support} ↦
    encoding.recursiveOrientedLegalTriple
        K q term hmultiplicity sigma alpha source ∈
      ProgressionHash.LegalTriple.markedXIsolatedTargets
        (encoding.recursiveAmbientTargets K q term hmultiplicity sigma alpha)
        (encoding.recursiveMarkedTargets K q term hmultiplicity sigma alpha) B seed

/-- Actual recursive quotient addresses retained by marked X-only isolation. -/
noncomputable def recursiveMarkedXIsolatedCoarseSupport
    (encoding : CWCoarseFieldEncoding R depth)
    (K : Type u) [CommRing K] (q : ℕ) {n : ℕ}
    (term : ExactInterfaceTermParameters (depth + 1))
    (hmultiplicity : term.multiplicity = n + 1)
    (sigma : Orientation)
    (alpha : ExactRecursiveSplitType
      (cwRecursiveLogicalParent term sigma) (coarseTotal depth) (n + 1))
    (B : Finset R)
    (seed : ProgressionHash.Seed R (Fin ((n + 1) + (n + 1)))) :
    Finset (CWRecursiveCoarseAddress depth n) := by
  classical
  exact (encoding.recursiveMarkedXIsolatedSources
    K q term hmultiplicity sigma alpha B seed).image Subtype.val

@[simp] theorem mem_recursiveMarkedXIsolatedCoarseSupport_iff
    (encoding : CWCoarseFieldEncoding R depth)
    (K : Type u) [CommRing K] (q : ℕ) {n : ℕ}
    (term : ExactInterfaceTermParameters (depth + 1))
    (hmultiplicity : term.multiplicity = n + 1)
    (sigma : Orientation)
    (alpha : ExactRecursiveSplitType
      (cwRecursiveLogicalParent term sigma) (coarseTotal depth) (n + 1))
    (B : Finset R)
    (seed : ProgressionHash.Seed R (Fin ((n + 1) + (n + 1))))
    (source : {address : CWRecursiveCoarseAddress depth n //
      address ∈ (cwRecursiveCoarsenedAlphaMarginalTerm
        K q term hmultiplicity sigma alpha).support}) :
    source.1 ∈ encoding.recursiveMarkedXIsolatedCoarseSupport
        K q term hmultiplicity sigma alpha B seed ↔
      encoding.recursiveOrientedLegalTriple
          K q term hmultiplicity sigma alpha source ∈
        ProgressionHash.LegalTriple.markedXIsolatedTargets
          (encoding.recursiveAmbientTargets K q term hmultiplicity sigma alpha)
          (encoding.recursiveMarkedTargets K q term hmultiplicity sigma alpha) B seed := by
  classical
  constructor
  · intro hsource
    rw [recursiveMarkedXIsolatedCoarseSupport, Finset.mem_image] at hsource
    obtain ⟨other, hother, hval⟩ := hsource
    have heq : other = source := Subtype.ext hval
    subst other
    exact (Finset.mem_filter.mp hother).2
  · intro hsource
    unfold recursiveMarkedXIsolatedCoarseSupport recursiveMarkedXIsolatedSources
    exact Finset.mem_image.mpr
      ⟨source, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hsource⟩, rfl⟩

/-- Every isolated recursive quotient address belongs to the marginal-selected coarse support. -/
theorem recursiveMarkedXIsolatedCoarseSupport_subset
    (encoding : CWCoarseFieldEncoding R depth)
    (K : Type u) [CommRing K] (q : ℕ) {n : ℕ}
    (term : ExactInterfaceTermParameters (depth + 1))
    (hmultiplicity : term.multiplicity = n + 1)
    (sigma : Orientation)
    (alpha : ExactRecursiveSplitType
      (cwRecursiveLogicalParent term sigma) (coarseTotal depth) (n + 1))
    (B : Finset R)
    (seed : ProgressionHash.Seed R (Fin ((n + 1) + (n + 1)))) :
    encoding.recursiveMarkedXIsolatedCoarseSupport
        K q term hmultiplicity sigma alpha B seed ⊆
      (cwRecursiveCoarsenedAlphaMarginalTerm
        K q term hmultiplicity sigma alpha).support := by
  classical
  intro address haddress
  rw [recursiveMarkedXIsolatedCoarseSupport, Finset.mem_image] at haddress
  obtain ⟨source, _hsource, rfl⟩ := haddress
  exact source.2

/-- Source-side and legal-triple-side marked isolated families have exactly the same cardinality. -/
theorem card_recursiveMarkedXIsolatedCoarseSupport
    (encoding : CWCoarseFieldEncoding R depth) [NeZero (2 : R)]
    (K : Type u) [CommRing K] (q : ℕ) {n : ℕ}
    (term : ExactInterfaceTermParameters (depth + 1))
    (hmultiplicity : term.multiplicity = n + 1)
    (sigma : Orientation)
    (alpha : ExactRecursiveSplitType
      (cwRecursiveLogicalParent term sigma) (coarseTotal depth) (n + 1))
    (B : Finset R)
    (seed : ProgressionHash.Seed R (Fin ((n + 1) + (n + 1)))) :
    (encoding.recursiveMarkedXIsolatedCoarseSupport
        K q term hmultiplicity sigma alpha B seed).card =
      (ProgressionHash.LegalTriple.markedXIsolatedTargets
        (encoding.recursiveAmbientTargets K q term hmultiplicity sigma alpha)
        (encoding.recursiveMarkedTargets K q term hmultiplicity sigma alpha) B seed).card := by
  classical
  let sources := encoding.recursiveMarkedXIsolatedSources
    K q term hmultiplicity sigma alpha B seed
  let ambient := encoding.recursiveAmbientTargets
    K q term hmultiplicity sigma alpha
  let marked := encoding.recursiveMarkedTargets
    K q term hmultiplicity sigma alpha
  let isolated := ProgressionHash.LegalTriple.markedXIsolatedTargets
    ambient marked B seed
  have hmarked : marked ⊆ ambient :=
    encoding.recursiveMarkedTargets_subset_ambientTargets
      K q term hmultiplicity sigma alpha
  have himage : isolated = sources.image
      (encoding.recursiveOrientedLegalTriple
        K q term hmultiplicity sigma alpha) := by
    ext triple
    constructor
    · intro htriple
      have htarget : triple ∈ ambient := by
        exact ProgressionHash.LegalTriple.filteredTargets_subset ambient B seed
          (ProgressionHash.LegalTriple.markedXIsolatedTargets_subset_filteredTargets
            ambient marked hmarked B seed htriple)
      unfold ambient recursiveAmbientTargets at htarget
      obtain ⟨source, _hsource, rfl⟩ := Finset.mem_image.mp htarget
      apply Finset.mem_image.mpr
      exact ⟨source, Finset.mem_filter.mpr ⟨Finset.mem_univ _, htriple⟩, rfl⟩
    · intro htriple
      obtain ⟨source, hsource, rfl⟩ := Finset.mem_image.mp htriple
      exact (Finset.mem_filter.mp hsource).2
  unfold recursiveMarkedXIsolatedCoarseSupport
  rw [Finset.card_image_of_injOn Subtype.val_injective.injOn]
  calc
    sources.card =
        (sources.image (encoding.recursiveOrientedLegalTriple
          K q term hmultiplicity sigma alpha)).card :=
      (Finset.card_image_of_injOn
        (encoding.recursiveOrientedLegalTriple_injective
          K q term hmultiplicity sigma alpha).injOn).symm
    _ = isolated.card := congrArg Finset.card himage.symm

/-- Marked X-only isolation makes physical `sigma X` recursive quotient labels injective. -/
theorem recursiveX_injectiveOn_recursiveMarkedXIsolatedCoarseSupport
    (encoding : CWCoarseFieldEncoding R depth)
    (K : Type u) [CommRing K] (q : ℕ) {n : ℕ}
    (term : ExactInterfaceTermParameters (depth + 1))
    (hmultiplicity : term.multiplicity = n + 1)
    (sigma : Orientation)
    (alpha : ExactRecursiveSplitType
      (cwRecursiveLogicalParent term sigma) (coarseTotal depth) (n + 1))
    (B : Finset R)
    (seed : ProgressionHash.Seed R (Fin ((n + 1) + (n + 1)))) :
    Set.InjOn
      (fun address : CWRecursiveCoarseAddress depth n ↦ address (sigma .X))
      (encoding.recursiveMarkedXIsolatedCoarseSupport
        K q term hmultiplicity sigma alpha B seed : Set _) := by
  classical
  let ambient := encoding.recursiveAmbientTargets
    K q term hmultiplicity sigma alpha
  let marked := encoding.recursiveMarkedTargets
    K q term hmultiplicity sigma alpha
  let isolated := ProgressionHash.LegalTriple.markedXIsolatedTargets
    ambient marked B seed
  have hmarked : marked ⊆ ambient :=
    encoding.recursiveMarkedTargets_subset_ambientTargets
      K q term hmultiplicity sigma alpha
  intro left hleft right hright hx
  change left ∈ encoding.recursiveMarkedXIsolatedCoarseSupport
    K q term hmultiplicity sigma alpha B seed at hleft
  change right ∈ encoding.recursiveMarkedXIsolatedCoarseSupport
    K q term hmultiplicity sigma alpha B seed at hright
  rw [recursiveMarkedXIsolatedCoarseSupport, Finset.mem_image] at hleft hright
  obtain ⟨leftSource, hleftSource, rfl⟩ := hleft
  obtain ⟨rightSource, hrightSource, rfl⟩ := hright
  have hleftIsolated :
      encoding.recursiveOrientedLegalTriple
        K q term hmultiplicity sigma alpha leftSource ∈ isolated :=
    (Finset.mem_filter.mp hleftSource).2
  have hrightIsolated :
      encoding.recursiveOrientedLegalTriple
        K q term hmultiplicity sigma alpha rightSource ∈ isolated :=
    (Finset.mem_filter.mp hrightSource).2
  have hindex :
      (encoding.recursiveOrientedLegalTriple
        K q term hmultiplicity sigma alpha leftSource).xIndex =
      (encoding.recursiveOrientedLegalTriple
        K q term hmultiplicity sigma alpha rightSource).xIndex := by
    funext occurrence
    exact congrArg encoding.encode (congrFun hx occurrence)
  have htargetInj :=
    ProgressionHash.LegalTriple.xIndex_injectiveOn_markedXIsolatedTargets
      ambient marked hmarked B seed
  have htriple := htargetInj hleftIsolated hrightIsolated hindex
  exact congrArg Subtype.val
    (encoding.recursiveOrientedLegalTriple_injective
      K q term hmultiplicity sigma alpha htriple)

/-- Orientation-parametric finite marked X-only extraction with its exact division-free count. -/
theorem exists_seed_many_recursiveMarkedXIsolatedCoarseSupport
    (encoding : CWCoarseFieldEncoding R depth)
    [Fintype R] [NeZero (2 : R)]
    (K : Type u) [CommRing K] (q : ℕ) {n : ℕ}
    (term : ExactInterfaceTermParameters (depth + 1))
    (hmultiplicity : term.multiplicity = n + 1)
    (sigma : Orientation)
    (alpha : ExactRecursiveSplitType
      (cwRecursiveLogicalParent term sigma) (coarseTotal depth) (n + 1))
    (B : Finset R)
    (hquarter : ∀ triple ∈ encoding.recursiveMarkedTargets
        K q term hmultiplicity sigma alpha,
      4 * (ProgressionHash.LegalTriple.xCompetitorYIndices
        (encoding.recursiveAmbientTargets K q term hmultiplicity sigma alpha)
        triple).card ≤ Fintype.card R) :
    ∃ seed : ProgressionHash.Seed R (Fin ((n + 1) + (n + 1))),
      3 * (encoding.recursiveMarkedTargets
          K q term hmultiplicity sigma alpha).card * B.card ≤
        4 * (Fintype.card R * Fintype.card R) *
          (encoding.recursiveMarkedXIsolatedCoarseSupport
            K q term hmultiplicity sigma alpha B seed).card ∧
      encoding.recursiveMarkedXIsolatedCoarseSupport
          K q term hmultiplicity sigma alpha B seed ⊆
        (cwRecursiveCoarsenedAlphaMarginalTerm
          K q term hmultiplicity sigma alpha).support ∧
      Set.InjOn
        (fun address : CWRecursiveCoarseAddress depth n ↦ address (sigma .X))
        (encoding.recursiveMarkedXIsolatedCoarseSupport
          K q term hmultiplicity sigma alpha B seed : Set _) := by
  let ambient := encoding.recursiveAmbientTargets
    K q term hmultiplicity sigma alpha
  let marked := encoding.recursiveMarkedTargets
    K q term hmultiplicity sigma alpha
  have hmarked : marked ⊆ ambient :=
    encoding.recursiveMarkedTargets_subset_ambientTargets
      K q term hmultiplicity sigma alpha
  obtain ⟨seed, hcount, _hfiltered, _hinjective⟩ :=
    ProgressionHash.LegalTriple.exists_seed_many_markedXIsolatedTargets
      ambient marked hmarked B hquarter
  refine ⟨seed, ?_,
    encoding.recursiveMarkedXIsolatedCoarseSupport_subset
      K q term hmultiplicity sigma alpha B seed,
    encoding.recursiveX_injectiveOn_recursiveMarkedXIsolatedCoarseSupport
      K q term hmultiplicity sigma alpha B seed⟩
  change 3 * marked.card * B.card ≤
    4 * (Fintype.card R * Fintype.card R) *
      (encoding.recursiveMarkedXIsolatedCoarseSupport
        K q term hmultiplicity sigma alpha B seed).card
  rw [encoding.card_recursiveMarkedXIsolatedCoarseSupport
    K q term hmultiplicity sigma alpha B seed]
  exact hcount

end CWCoarseFieldEncoding

/-! ## Fine hash filtering and whole-fiber X isolation -/

/-- The supported recursive quotient address containing one supported fine marginal-selected
parent address. -/
def cwRecursiveCoarseSourceOfFine
    (K : Type u) [CommRing K] (q : ℕ) {depth n : ℕ}
    (term : ExactInterfaceTermParameters (depth + 1))
    (hmultiplicity : term.multiplicity = n + 1)
    (sigma : Orientation)
    (alpha : ExactRecursiveSplitType
      (cwRecursiveLogicalParent term sigma) (coarseTotal depth) (n + 1))
    (source : {address : BlockAddress (fun _c ↦
      PositiveWord (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n) //
      address ∈ (cwRecursiveAlphaMarginalSelectedTerm
        K q term hmultiplicity sigma alpha).support}) :
    {address : CWRecursiveCoarseAddress depth n //
      address ∈ (cwRecursiveCoarsenedAlphaMarginalTerm
        K q term hmultiplicity sigma alpha).support} := by
  refine ⟨cwRecursiveChildGroup depth n source.1, ?_⟩
  change cwRecursiveChildGroup depth n source.1 ∈
    ((cwRecursiveAlphaMarginalSelectedTerm
      K q term hmultiplicity sigma alpha).coarsen
        (cwRecursiveChildCoarsening depth n)).support
  rw [PartitionedTensor.coarsen_support]
  exact Finset.mem_image.mpr ⟨source.1, source.2, rfl⟩

@[simp] theorem cwRecursiveCoarseSourceOfFine_val
    (K : Type u) [CommRing K] (q : ℕ) {depth n : ℕ}
    (term : ExactInterfaceTermParameters (depth + 1))
    (hmultiplicity : term.multiplicity = n + 1)
    (sigma : Orientation)
    (alpha : ExactRecursiveSplitType
      (cwRecursiveLogicalParent term sigma) (coarseTotal depth) (n + 1))
    (source : {address : BlockAddress (fun _c ↦
      PositiveWord (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n) //
      address ∈ (cwRecursiveAlphaMarginalSelectedTerm
        K q term hmultiplicity sigma alpha).support}) :
    (cwRecursiveCoarseSourceOfFine
      K q term hmultiplicity sigma alpha source).1 =
      cwRecursiveChildGroup depth n source.1 :=
  rfl

/-- Independent physical block predicate implementing the recursive common-bucket hash filter. -/
noncomputable def cwRecursiveOrientedHashKeepFineBlock
    {R : Type v} [Field R] (encoding : CWCoarseFieldEncoding R depth)
    (n : ℕ) (sigma : Orientation) (B : Finset R)
    (seed : ProgressionHash.Seed R (Fin ((n + 1) + (n + 1)))) :
    (c : Leg) →
      PositiveWord (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n → Prop :=
  fun c label ↦
    let word := cwRecursiveLabelledChildWord depth n label
    match sigma.symm c with
    | .X => seed.xHash (encoding.encode ∘ word) ∈ B
    | .Y => seed.yHash (encoding.encode ∘ word) ∈ B
    | .Z => seed.zHash encoding.target (encoding.encode ∘ word) ∈ B

@[simp] theorem cwRecursiveOrientedHashKeepFineBlock_sigma_X
    {R : Type v} [Field R] (encoding : CWCoarseFieldEncoding R depth)
    (n : ℕ) (sigma : Orientation) (B : Finset R)
    (seed : ProgressionHash.Seed R (Fin ((n + 1) + (n + 1)))) (label) :
    cwRecursiveOrientedHashKeepFineBlock encoding n sigma B seed (sigma .X) label ↔
      seed.xHash
        (encoding.encode ∘ cwRecursiveLabelledChildWord depth n label) ∈ B := by
  simp [cwRecursiveOrientedHashKeepFineBlock]

@[simp] theorem cwRecursiveOrientedHashKeepFineBlock_sigma_Y
    {R : Type v} [Field R] (encoding : CWCoarseFieldEncoding R depth)
    (n : ℕ) (sigma : Orientation) (B : Finset R)
    (seed : ProgressionHash.Seed R (Fin ((n + 1) + (n + 1)))) (label) :
    cwRecursiveOrientedHashKeepFineBlock encoding n sigma B seed (sigma .Y) label ↔
      seed.yHash
        (encoding.encode ∘ cwRecursiveLabelledChildWord depth n label) ∈ B := by
  simp [cwRecursiveOrientedHashKeepFineBlock]

@[simp] theorem cwRecursiveOrientedHashKeepFineBlock_sigma_Z
    {R : Type v} [Field R] (encoding : CWCoarseFieldEncoding R depth)
    (n : ℕ) (sigma : Orientation) (B : Finset R)
    (seed : ProgressionHash.Seed R (Fin ((n + 1) + (n + 1)))) (label) :
    cwRecursiveOrientedHashKeepFineBlock encoding n sigma B seed (sigma .Z) label ↔
      seed.zHash encoding.target
        (encoding.encode ∘ cwRecursiveLabelledChildWord depth n label) ∈ B := by
  simp [cwRecursiveOrientedHashKeepFineBlock]

/-- Fine marginal-selected support after the three independent hash-membership zero-outs. -/
noncomputable def cwRecursiveOrientedHashFilteredFineSupport
    {R : Type v} [Field R] (encoding : CWCoarseFieldEncoding R depth)
    (K : Type u) [CommRing K] (q : ℕ) {n : ℕ}
    (term : ExactInterfaceTermParameters (depth + 1))
    (hmultiplicity : term.multiplicity = n + 1)
    (sigma : Orientation)
    (alpha : ExactRecursiveSplitType
      (cwRecursiveLogicalParent term sigma) (coarseTotal depth) (n + 1))
    (B : Finset R)
    (seed : ProgressionHash.Seed R (Fin ((n + 1) + (n + 1)))) := by
  classical
  exact (cwRecursiveAlphaMarginalSelectedTerm
    K q term hmultiplicity sigma alpha).support.filter fun address ↦
      ∀ c, cwRecursiveOrientedHashKeepFineBlock
        encoding n sigma B seed c (address c)

@[simp] theorem mem_cwRecursiveOrientedHashFilteredFineSupport
    {R : Type v} [Field R] (encoding : CWCoarseFieldEncoding R depth)
    (K : Type u) [CommRing K] (q : ℕ) {n : ℕ}
    (term : ExactInterfaceTermParameters (depth + 1))
    (hmultiplicity : term.multiplicity = n + 1)
    (sigma : Orientation)
    (alpha : ExactRecursiveSplitType
      (cwRecursiveLogicalParent term sigma) (coarseTotal depth) (n + 1))
    (B : Finset R)
    (seed : ProgressionHash.Seed R (Fin ((n + 1) + (n + 1)))) (address) :
    address ∈ cwRecursiveOrientedHashFilteredFineSupport
        encoding K q term hmultiplicity sigma alpha B seed ↔
      address ∈ (cwRecursiveAlphaMarginalSelectedTerm
          K q term hmultiplicity sigma alpha).support ∧
        ∀ c, cwRecursiveOrientedHashKeepFineBlock
          encoding n sigma B seed c (address c) := by
  classical
  simp [cwRecursiveOrientedHashFilteredFineSupport]

/-- The three independent fine block predicates are exactly survival of the associated recursive
ambient legal triple. -/
theorem cwRecursiveOrientedHashKeepFineBlock_all_iff_survives
    {R : Type v} [Field R] (encoding : CWCoarseFieldEncoding R depth)
    (K : Type u) [CommRing K] (q : ℕ) {n : ℕ}
    (term : ExactInterfaceTermParameters (depth + 1))
    (hmultiplicity : term.multiplicity = n + 1)
    (sigma : Orientation)
    (alpha : ExactRecursiveSplitType
      (cwRecursiveLogicalParent term sigma) (coarseTotal depth) (n + 1))
    (B : Finset R)
    (seed : ProgressionHash.Seed R (Fin ((n + 1) + (n + 1))))
    (source : {address : BlockAddress (fun _c ↦
      PositiveWord (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n) //
      address ∈ (cwRecursiveAlphaMarginalSelectedTerm
        K q term hmultiplicity sigma alpha).support}) :
    (∀ c, cwRecursiveOrientedHashKeepFineBlock
        encoding n sigma B seed c (source.1 c)) ↔
      ProgressionHash.LegalTriple.SurvivesHashFilter (B : Set R) seed
        (encoding.recursiveOrientedLegalTriple K q term hmultiplicity sigma alpha
          (cwRecursiveCoarseSourceOfFine
            K q term hmultiplicity sigma alpha source)) := by
  let coarseSource := cwRecursiveCoarseSourceOfFine
    K q term hmultiplicity sigma alpha source
  have hleg (logical : Leg) :
      (match logical with
        | .X => (encoding.recursiveOrientedLegalTriple
            K q term hmultiplicity sigma alpha coarseSource).xIndex
        | .Y => (encoding.recursiveOrientedLegalTriple
            K q term hmultiplicity sigma alpha coarseSource).yIndex
        | .Z => (encoding.recursiveOrientedLegalTriple
            K q term hmultiplicity sigma alpha coarseSource).zIndex) =
        encoding.encode ∘ cwRecursiveLabelledChildWord
          depth n (source.1 (sigma logical)) := by
    cases logical <;> rfl
  have hlegX :
      (encoding.recursiveOrientedLegalTriple
          K q term hmultiplicity sigma alpha coarseSource).xIndex =
        encoding.encode ∘ cwRecursiveLabelledChildWord
          depth n (source.1 (sigma .X)) := by
    simpa using hleg .X
  have hlegY :
      (encoding.recursiveOrientedLegalTriple
          K q term hmultiplicity sigma alpha coarseSource).yIndex =
        encoding.encode ∘ cwRecursiveLabelledChildWord
          depth n (source.1 (sigma .Y)) := by
    simpa using hleg .Y
  have hlegZ :
      (encoding.recursiveOrientedLegalTriple
          K q term hmultiplicity sigma alpha coarseSource).zIndex =
        encoding.encode ∘ cwRecursiveLabelledChildWord
          depth n (source.1 (sigma .Z)) := by
    simpa using hleg .Z
  constructor
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · have hk := (cwRecursiveOrientedHashKeepFineBlock_sigma_X
          encoding n sigma B seed (source.1 (sigma .X))).mp (h (sigma .X))
      change seed.xHash
        ((encoding.recursiveOrientedLegalTriple
          K q term hmultiplicity sigma alpha coarseSource).xIndex) ∈ (B : Set R)
      rw [hlegX]
      simpa using hk
    · have hk := (cwRecursiveOrientedHashKeepFineBlock_sigma_Y
          encoding n sigma B seed (source.1 (sigma .Y))).mp (h (sigma .Y))
      change seed.yHash
        ((encoding.recursiveOrientedLegalTriple
          K q term hmultiplicity sigma alpha coarseSource).yIndex) ∈ (B : Set R)
      rw [hlegY]
      simpa using hk
    · have hk := (cwRecursiveOrientedHashKeepFineBlock_sigma_Z
          encoding n sigma B seed (source.1 (sigma .Z))).mp (h (sigma .Z))
      change seed.zHash encoding.target
        ((encoding.recursiveOrientedLegalTriple
          K q term hmultiplicity sigma alpha coarseSource).zIndex) ∈ (B : Set R)
      rw [hlegZ]
      simpa using hk
  · rintro ⟨hx, hy, hz⟩ c
    rw [← sigma.apply_symm_apply c]
    generalize hlogical : sigma.symm c = logical
    cases logical with
    | X =>
        apply (cwRecursiveOrientedHashKeepFineBlock_sigma_X
          encoding n sigma B seed (source.1 (sigma .X))).mpr
        have hx' : seed.xHash
            ((encoding.recursiveOrientedLegalTriple
              K q term hmultiplicity sigma alpha coarseSource).xIndex) ∈
              (B : Set R) := hx
        rw [hlegX] at hx'
        simpa using hx'
    | Y =>
        apply (cwRecursiveOrientedHashKeepFineBlock_sigma_Y
          encoding n sigma B seed (source.1 (sigma .Y))).mpr
        have hy' : seed.yHash
            ((encoding.recursiveOrientedLegalTriple
              K q term hmultiplicity sigma alpha coarseSource).yIndex) ∈
              (B : Set R) := hy
        rw [hlegY] at hy'
        simpa using hy'
    | Z =>
        apply (cwRecursiveOrientedHashKeepFineBlock_sigma_Z
          encoding n sigma B seed (source.1 (sigma .Z))).mpr
        have hz' : seed.zHash encoding.target
            ((encoding.recursiveOrientedLegalTriple
              K q term hmultiplicity sigma alpha coarseSource).zIndex) ∈
              (B : Set R) := hz
        rw [hlegZ] at hz'
        simpa using hz'

/-- The recursive common-bucket filter is a genuine variable restriction on the fine tensor. -/
theorem cwRecursiveAlphaMarginalSelectedTerm_restricts_orientedHashFilteredFine
    {R : Type v} [Field R] (encoding : CWCoarseFieldEncoding R depth)
    (K : Type u) [CommRing K] (q : ℕ) {n : ℕ}
    (term : ExactInterfaceTermParameters (depth + 1))
    (hmultiplicity : term.multiplicity = n + 1)
    (sigma : Orientation)
    (alpha : ExactRecursiveSplitType
      (cwRecursiveLogicalParent term sigma) (coarseTotal depth) (n + 1))
    (B : Finset R)
    (seed : ProgressionHash.Seed R (Fin ((n + 1) + (n + 1)))) :
    let selected := cwRecursiveAlphaMarginalSelectedTerm
      K q term hmultiplicity sigma alpha
    let filtered := selected.withSupport
      (cwRecursiveOrientedHashFilteredFineSupport
        encoding K q term hmultiplicity sigma alpha B seed)
    Restricts selected.realize filtered.realize := by
  classical
  let selected := cwRecursiveAlphaMarginalSelectedTerm
    K q term hmultiplicity sigma alpha
  let keep := cwRecursiveOrientedHashKeepFineBlock encoding n sigma B seed
  let filteredSupport := cwRecursiveOrientedHashFilteredFineSupport
    encoding K q term hmultiplicity sigma alpha B seed
  let filtered := selected.withSupport filteredSupport
  have hselect := Tensor.Restricts.partitionedSelect selected keep
  apply hselect.trans (Restricts.of_eq ?_)
  apply PartitionedTensor.realize_eq_of_support_eq
  · rfl
  · intro address _haddress
    rfl

/-- The fine preimage of a recursive quotient-address set is saturated by complete quotient
groups inside any smaller ambient support. -/
theorem cwRecursiveFineSupportOverCoarseSupport_isGroupSaturatedIn
    {depth n : ℕ}
    (fine ambient : Finset (BlockAddress (fun _c ↦
      PositiveWord (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n)))
    (coarse : Finset (CWRecursiveCoarseAddress depth n))
    (hambient : ambient ⊆ fine) :
    IsGroupSaturatedIn ambient
      (cwRecursiveFineSupportOverCoarseSupport fine coarse)
      (cwRecursiveChildGroup depth n) := by
  intro selected hselected other hother hgroup
  have hselectedData :=
    (mem_cwRecursiveFineSupportOverCoarseSupport fine coarse selected).mp hselected
  apply (mem_cwRecursiveFineSupportOverCoarseSupport fine coarse other).mpr
  exact ⟨hambient hother, hgroup.symm ▸ hselectedData.2⟩

/-- The retained marked fine preimage has its quotient group readable from physical `sigma X`
inside the entire ambient hash-filtered fine support. -/
theorem cwRecursiveMarkedXIsolatedFine_hasGroupUniqueLegFibers
    {R : Type v} [Field R] [Fintype R] [NeZero (2 : R)]
    (encoding : CWCoarseFieldEncoding R depth)
    (K : Type u) [CommRing K] (q : ℕ) {n : ℕ}
    (term : ExactInterfaceTermParameters (depth + 1))
    (hmultiplicity : term.multiplicity = n + 1)
    (sigma : Orientation)
    (alpha : ExactRecursiveSplitType
      (cwRecursiveLogicalParent term sigma) (coarseTotal depth) (n + 1))
    (B : Finset R) (hB : ThreeAPFree (B : Set R))
    (seed : ProgressionHash.Seed R (Fin ((n + 1) + (n + 1)))) :
    let selected := cwRecursiveAlphaMarginalSelectedTerm
      K q term hmultiplicity sigma alpha
    let filteredSupport := cwRecursiveOrientedHashFilteredFineSupport
      encoding K q term hmultiplicity sigma alpha B seed
    let coarseKept := encoding.recursiveMarkedXIsolatedCoarseSupport
      K q term hmultiplicity sigma alpha B seed
    let isolatedSupport := cwRecursiveFineSupportOverCoarseSupport
      selected.support coarseKept
    HasGroupUniqueLegFibers filteredSupport isolatedSupport
      (cwRecursiveChildGroup depth n) (sigma .X) := by
  classical
  let selected := cwRecursiveAlphaMarginalSelectedTerm
    K q term hmultiplicity sigma alpha
  let filteredSupport := cwRecursiveOrientedHashFilteredFineSupport
    encoding K q term hmultiplicity sigma alpha B seed
  let coarseKept := encoding.recursiveMarkedXIsolatedCoarseSupport
    K q term hmultiplicity sigma alpha B seed
  let isolatedSupport := cwRecursiveFineSupportOverCoarseSupport
    selected.support coarseKept
  let ambient := encoding.recursiveAmbientTargets
    K q term hmultiplicity sigma alpha
  let marked := encoding.recursiveMarkedTargets
    K q term hmultiplicity sigma alpha
  let isolated := ProgressionHash.LegalTriple.markedXIsolatedTargets
    ambient marked B seed
  have hmarked : marked ⊆ ambient :=
    encoding.recursiveMarkedTargets_subset_ambientTargets
      K q term hmultiplicity sigma alpha
  refine ⟨?_, ?_⟩
  · intro address haddress
    have hisolated := (mem_cwRecursiveFineSupportOverCoarseSupport
      selected.support coarseKept address).mp haddress
    let source : {address // address ∈ selected.support} :=
      ⟨address, hisolated.1⟩
    let coarseSource := cwRecursiveCoarseSourceOfFine
      K q term hmultiplicity sigma alpha source
    have hcoarseIsolated : coarseSource.1 ∈ coarseKept := by
      simpa [coarseSource, source] using hisolated.2
    have htripleIsolated :
        encoding.recursiveOrientedLegalTriple
          K q term hmultiplicity sigma alpha coarseSource ∈ isolated :=
      (encoding.mem_recursiveMarkedXIsolatedCoarseSupport_iff
        K q term hmultiplicity sigma alpha B seed coarseSource).mp hcoarseIsolated
    have htripleFiltered :=
      ProgressionHash.LegalTriple.markedXIsolatedTargets_subset_filteredTargets
        ambient marked hmarked B seed htripleIsolated
    have hsurvives : ProgressionHash.LegalTriple.SurvivesHashFilter (B : Set R) seed
        (encoding.recursiveOrientedLegalTriple
          K q term hmultiplicity sigma alpha coarseSource) :=
      (Finset.mem_filter.mp htripleFiltered).2
    apply (mem_cwRecursiveOrientedHashFilteredFineSupport
      encoding K q term hmultiplicity sigma alpha B seed address).mpr
    refine ⟨hisolated.1, ?_⟩
    simpa [source, coarseSource] using
      (cwRecursiveOrientedHashKeepFineBlock_all_iff_survives
        encoding K q term hmultiplicity sigma alpha B seed source).mpr hsurvives
  · intro kept hkept other hother hlabel
    have hkeptData := (mem_cwRecursiveFineSupportOverCoarseSupport
      selected.support coarseKept kept).mp hkept
    have hotherData := (mem_cwRecursiveOrientedHashFilteredFineSupport
      encoding K q term hmultiplicity sigma alpha B seed other).mp hother
    let keptSource : {address // address ∈ selected.support} :=
      ⟨kept, hkeptData.1⟩
    let otherSource : {address // address ∈ selected.support} :=
      ⟨other, hotherData.1⟩
    let keptCoarse := cwRecursiveCoarseSourceOfFine
      K q term hmultiplicity sigma alpha keptSource
    let otherCoarse := cwRecursiveCoarseSourceOfFine
      K q term hmultiplicity sigma alpha otherSource
    have hkeptIsolated :
        encoding.recursiveOrientedLegalTriple
          K q term hmultiplicity sigma alpha keptCoarse ∈ isolated := by
      apply (encoding.mem_recursiveMarkedXIsolatedCoarseSupport_iff
        K q term hmultiplicity sigma alpha B seed keptCoarse).mp
      simpa [coarseKept, keptCoarse, keptSource] using hkeptData.2
    have hotherTarget :
        encoding.recursiveOrientedLegalTriple
          K q term hmultiplicity sigma alpha otherCoarse ∈ ambient := by
      unfold ambient CWCoarseFieldEncoding.recursiveAmbientTargets
      exact Finset.mem_image.mpr ⟨otherCoarse, Finset.mem_univ _, rfl⟩
    have hotherSurvives :
        ProgressionHash.LegalTriple.SurvivesHashFilter (B : Set R) seed
          (encoding.recursiveOrientedLegalTriple
            K q term hmultiplicity sigma alpha otherCoarse) :=
      (cwRecursiveOrientedHashKeepFineBlock_all_iff_survives
        encoding K q term hmultiplicity sigma alpha B seed otherSource).mp hotherData.2
    have hotherFiltered :
        encoding.recursiveOrientedLegalTriple
          K q term hmultiplicity sigma alpha otherCoarse ∈
        ProgressionHash.LegalTriple.filteredTargets ambient B seed :=
      Finset.mem_filter.mpr ⟨hotherTarget, hotherSurvives⟩
    have hxIndex :
        (encoding.recursiveOrientedLegalTriple
          K q term hmultiplicity sigma alpha otherCoarse).xIndex =
        (encoding.recursiveOrientedLegalTriple
          K q term hmultiplicity sigma alpha keptCoarse).xIndex := by
      funext occurrence
      exact congrArg encoding.encode <|
        congrFun (congrArg (cwRecursiveLabelledChildWord depth n) hlabel) occurrence
    have htriple :
        encoding.recursiveOrientedLegalTriple
            K q term hmultiplicity sigma alpha otherCoarse =
          encoding.recursiveOrientedLegalTriple
            K q term hmultiplicity sigma alpha keptCoarse :=
      ProgressionHash.LegalTriple.eq_of_mem_markedXIsolatedTargets_of_mem_filteredTargets
        ambient marked hmarked B hB seed hkeptIsolated hotherFiltered hxIndex
    have hsource : otherCoarse = keptCoarse :=
      encoding.recursiveOrientedLegalTriple_injective
        K q term hmultiplicity sigma alpha htriple
    exact congrArg Subtype.val hsource

/-- Complete tensor-level marked X-only hash extraction: the marginal-selected fine term
restricts to the entire fine preimage of every isolated marked quotient address. -/
theorem cwRecursiveAlphaMarginalSelectedTerm_restricts_markedXIsolatedFine
    {R : Type v} [Field R] [Fintype R] [NeZero (2 : R)]
    (encoding : CWCoarseFieldEncoding R depth)
    (K : Type u) [CommRing K] (q : ℕ) {n : ℕ}
    (term : ExactInterfaceTermParameters (depth + 1))
    (hmultiplicity : term.multiplicity = n + 1)
    (sigma : Orientation)
    (alpha : ExactRecursiveSplitType
      (cwRecursiveLogicalParent term sigma) (coarseTotal depth) (n + 1))
    (B : Finset R) (hB : ThreeAPFree (B : Set R))
    (seed : ProgressionHash.Seed R (Fin ((n + 1) + (n + 1)))) :
    let selected := cwRecursiveAlphaMarginalSelectedTerm
      K q term hmultiplicity sigma alpha
    let coarseKept := encoding.recursiveMarkedXIsolatedCoarseSupport
      K q term hmultiplicity sigma alpha B seed
    let isolatedSupport := cwRecursiveFineSupportOverCoarseSupport
      selected.support coarseKept
    Restricts selected.realize (selected.withSupport isolatedSupport).realize := by
  classical
  let selected := cwRecursiveAlphaMarginalSelectedTerm
    K q term hmultiplicity sigma alpha
  let filteredSupport := cwRecursiveOrientedHashFilteredFineSupport
    encoding K q term hmultiplicity sigma alpha B seed
  let filtered := selected.withSupport filteredSupport
  let coarseKept := encoding.recursiveMarkedXIsolatedCoarseSupport
    K q term hmultiplicity sigma alpha B seed
  let isolatedSupport := cwRecursiveFineSupportOverCoarseSupport
    selected.support coarseKept
  have hfirst : Restricts selected.realize filtered.realize := by
    simpa [selected, filtered, filteredSupport] using
      cwRecursiveAlphaMarginalSelectedTerm_restricts_orientedHashFilteredFine
        encoding K q term hmultiplicity sigma alpha B seed
  have hunique : HasGroupUniqueLegFibers filteredSupport isolatedSupport
      (cwRecursiveChildGroup depth n) (sigma .X) := by
    simpa [selected, filteredSupport, coarseKept, isolatedSupport] using
      cwRecursiveMarkedXIsolatedFine_hasGroupUniqueLegFibers
        encoding K q term hmultiplicity sigma alpha B hB seed
  have hambient : filteredSupport ⊆ selected.support := by
    intro address haddress
    exact (mem_cwRecursiveOrientedHashFilteredFineSupport
      encoding K q term hmultiplicity sigma alpha B seed address).mp haddress |>.1
  have hsaturated : IsGroupSaturatedIn filteredSupport isolatedSupport
      (cwRecursiveChildGroup depth n) :=
    cwRecursiveFineSupportOverCoarseSupport_isGroupSaturatedIn
      selected.support filteredSupport coarseKept hambient
  have hsecond : Restricts filtered.realize
      (filtered.withSupport isolatedSupport).realize := by
    exact Tensor.Restricts.partitionedGroupSaturated filtered isolatedSupport
      (cwRecursiveChildGroup depth n) (sigma .X)
      (by simpa [filtered] using hunique) hsaturated
  exact hfirst.trans (hsecond.trans (Restricts.of_eq (by rfl)))

/-! ## Composition with grouped recursive compatibility cleanup -/

/-- One marked X-only affine hash pass followed by the complete grouped recursive compatibility
and usefulness cleanup.

The theorem begins with the selected parent constituent, constructs every restriction internally,
and ends at an indexed direct sum of whole surviving fine quotient fibers.  Its only hashing datum
is a concrete seed; no assembled restriction is accepted as a premise. -/
theorem cwRecursiveSelectedTerm_orientedMarkedXHashAndGroupedCleanup
    {R : Type v} [Field R] [Fintype R] [NeZero (2 : R)]
    (encoding : CWCoarseFieldEncoding R depth)
    (K : Type u) [CommRing K] (q : ℕ)
    {Part : Type v} [DecidableEq Part] {n : ℕ}
    (partAt : Fin (n + 1) → Part)
    (term : ExactInterfaceTermParameters (depth + 1))
    (hmultiplicity : term.multiplicity = n + 1)
    (sigma : Orientation)
    (alpha : ExactRecursiveSplitType
      (cwRecursiveLogicalParent term sigma) (coarseTotal depth) (n + 1))
    (targets : CompatibilityTargets Part depth)
    (pooled : PooledAllTargets targets)
    (B : Finset R) (hB : ThreeAPFree (B : Set R))
    (seed : ProgressionHash.Seed R (Fin ((n + 1) + (n + 1)))) :
    let parentSelected := cwSelectedExactInterfaceTerm K q term hmultiplicity
    let alphaSelected := cwRecursiveAlphaMarginalSelectedTerm
      K q term hmultiplicity sigma alpha
    let coarseKept := encoding.recursiveMarkedXIsolatedCoarseSupport
      K q term hmultiplicity sigma alpha B seed
    let fineAmbient := cwRecursiveFineSupportOverCoarseSupport
      alphaSelected.support coarseKept
    let hashed := alphaSelected.withSupport fineAmbient
    let model := cwRecursiveChildCompatibilityModel depth n partAt
    let xSupport := groupStableSupport hashed.support (fun address ↦
      model.MatchesExact (logicalAddress sigma address) .X targets.xExact)
    let xUseful := hashed.withSupport xSupport
    let yFirst := cwRecursivePooledYFirstZeroOut xUseful sigma partAt pooled.yAll
    let compatibleY := OrientedCompatibleY
      (A := fun _c ↦
        PositiveWord (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n)
      sigma model targets
    let ySupport := groupCompatibilityIsolatedSupport
      yFirst.support (cwRecursiveChildGroup depth n) (sigma .Y) compatibleY
    let yIsolated := yFirst.withSupport ySupport
    let yUsefulSupport := groupStableSupport yIsolated.support (fun address ↦
      model.MatchesExact (logicalAddress sigma address) .Y targets.yExact)
    let yUseful := yIsolated.withSupport yUsefulSupport
    let zFirst := cwRecursivePooledZFirstZeroOut yUseful sigma partAt pooled.zAll
    let compatibleZ := OrientedCompatibleZ
      (A := fun _c ↦
        PositiveWord (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n)
      sigma model targets
    let zSupport := groupCompatibilityIsolatedSupport
      zFirst.support (cwRecursiveChildGroup depth n) (sigma .Z) compatibleZ
    let zIsolated := zFirst.withSupport zSupport
    let zUsefulSupport := groupStableSupport zIsolated.support (fun address ↦
      model.MatchesExact (logicalAddress sigma address) .Z targets.zExact)
    let zUseful := zIsolated.withSupport zUsefulSupport
    ∃ G : zUseful.LegGrouping (CWRecursiveCoarseAddress depth n),
      (∀ address, G.group address = cwRecursiveChildGroup depth n address) ∧
        IsProjectionClosed hashed.support zUsefulSupport Finset.univ ∧
          Restricts parentSelected.realize
            (Tensor.indexedDirectSum (fun coarse ↦ (G.fiber coarse).realize)) := by
  classical
  let parentSelected := cwSelectedExactInterfaceTerm K q term hmultiplicity
  let alphaSelected := cwRecursiveAlphaMarginalSelectedTerm
    K q term hmultiplicity sigma alpha
  let coarseKept := encoding.recursiveMarkedXIsolatedCoarseSupport
    K q term hmultiplicity sigma alpha B seed
  let fineAmbient := cwRecursiveFineSupportOverCoarseSupport
    alphaSelected.support coarseKept
  let hashed := alphaSelected.withSupport fineAmbient
  have hMarginal : Restricts parentSelected.realize alphaSelected.realize := by
    simpa [parentSelected, alphaSelected] using
      cwSelectedExactInterfaceTerm_restricts_recursiveAlphaMarginals
        K q term hmultiplicity sigma alpha
  have hHash : Restricts alphaSelected.realize hashed.realize := by
    simpa [alphaSelected, coarseKept, fineAmbient, hashed] using
      cwRecursiveAlphaMarginalSelectedTerm_restricts_markedXIsolatedFine
        encoding K q term hmultiplicity sigma alpha B hB seed
  have hcoarseX : Set.InjOn
      (fun address : CWRecursiveCoarseAddress depth n ↦ address (sigma .X))
      (coarseKept : Set _) := by
    simpa [coarseKept] using
      encoding.recursiveX_injectiveOn_recursiveMarkedXIsolatedCoarseSupport
        K q term hmultiplicity sigma alpha B seed
  obtain ⟨G, hgroup, hclosed, hcleanup⟩ :=
    cwRecursiveSelectedTerm_orientedGroupedCleanup_withCoarseGroup
      K q partAt term hmultiplicity sigma alpha targets pooled coarseKept hcoarseX
  refine ⟨G, hgroup, hclosed, ?_⟩
  exact hMarginal.trans (hHash.trans hcleanup)

/-- Complete finite existence theorem for one recursive constituent node.

The degree hypothesis ranges only over marked joint-type targets, but each competitor list is
computed in the ambient marginal-type family.  The conclusion combines the exact marked survivor
count with a constructed tensor restriction through X hashing and Y/Z compatibility cleanup. -/
theorem exists_seed_many_recursiveMarkedXHashAndGroupedCleanup
    {R : Type v} [Field R] [Fintype R] [NeZero (2 : R)]
    (encoding : CWCoarseFieldEncoding R depth)
    (K : Type u) [CommRing K] (q : ℕ)
    {Part : Type v} [DecidableEq Part] {n : ℕ}
    (partAt : Fin (n + 1) → Part)
    (term : ExactInterfaceTermParameters (depth + 1))
    (hmultiplicity : term.multiplicity = n + 1)
    (sigma : Orientation)
    (alpha : ExactRecursiveSplitType
      (cwRecursiveLogicalParent term sigma) (coarseTotal depth) (n + 1))
    (targets : CompatibilityTargets Part depth)
    (pooled : PooledAllTargets targets)
    (B : Finset R) (hB : ThreeAPFree (B : Set R))
    (hquarter : ∀ triple ∈ encoding.recursiveMarkedTargets
        K q term hmultiplicity sigma alpha,
      4 * (ProgressionHash.LegalTriple.xCompetitorYIndices
        (encoding.recursiveAmbientTargets K q term hmultiplicity sigma alpha)
        triple).card ≤ Fintype.card R) :
    ∃ seed : ProgressionHash.Seed R (Fin ((n + 1) + (n + 1))),
      3 * (encoding.recursiveMarkedTargets
          K q term hmultiplicity sigma alpha).card * B.card ≤
        4 * (Fintype.card R * Fintype.card R) *
          (encoding.recursiveMarkedXIsolatedCoarseSupport
            K q term hmultiplicity sigma alpha B seed).card ∧
      let parentSelected := cwSelectedExactInterfaceTerm K q term hmultiplicity
      let alphaSelected := cwRecursiveAlphaMarginalSelectedTerm
        K q term hmultiplicity sigma alpha
      let coarseKept := encoding.recursiveMarkedXIsolatedCoarseSupport
        K q term hmultiplicity sigma alpha B seed
      let fineAmbient := cwRecursiveFineSupportOverCoarseSupport
        alphaSelected.support coarseKept
      let hashed := alphaSelected.withSupport fineAmbient
      let model := cwRecursiveChildCompatibilityModel depth n partAt
      let xSupport := groupStableSupport hashed.support (fun address ↦
        model.MatchesExact (logicalAddress sigma address) .X targets.xExact)
      let xUseful := hashed.withSupport xSupport
      let yFirst := cwRecursivePooledYFirstZeroOut xUseful sigma partAt pooled.yAll
      let compatibleY := OrientedCompatibleY
        (A := fun _c ↦
          PositiveWord (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n)
        sigma model targets
      let ySupport := groupCompatibilityIsolatedSupport
        yFirst.support (cwRecursiveChildGroup depth n) (sigma .Y) compatibleY
      let yIsolated := yFirst.withSupport ySupport
      let yUsefulSupport := groupStableSupport yIsolated.support (fun address ↦
        model.MatchesExact (logicalAddress sigma address) .Y targets.yExact)
      let yUseful := yIsolated.withSupport yUsefulSupport
      let zFirst := cwRecursivePooledZFirstZeroOut yUseful sigma partAt pooled.zAll
      let compatibleZ := OrientedCompatibleZ
        (A := fun _c ↦
          PositiveWord (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n)
        sigma model targets
      let zSupport := groupCompatibilityIsolatedSupport
        zFirst.support (cwRecursiveChildGroup depth n) (sigma .Z) compatibleZ
      let zIsolated := zFirst.withSupport zSupport
      let zUsefulSupport := groupStableSupport zIsolated.support (fun address ↦
        model.MatchesExact (logicalAddress sigma address) .Z targets.zExact)
      let zUseful := zIsolated.withSupport zUsefulSupport
      ∃ G : zUseful.LegGrouping (CWRecursiveCoarseAddress depth n),
        (∀ address, G.group address = cwRecursiveChildGroup depth n address) ∧
          IsProjectionClosed hashed.support zUsefulSupport Finset.univ ∧
            Restricts parentSelected.realize
              (Tensor.indexedDirectSum (fun coarse ↦ (G.fiber coarse).realize)) := by
  obtain ⟨seed, hcount, _hsubset, _hinjective⟩ :=
    encoding.exists_seed_many_recursiveMarkedXIsolatedCoarseSupport
      K q term hmultiplicity sigma alpha B hquarter
  refine ⟨seed, hcount, ?_⟩
  exact cwRecursiveSelectedTerm_orientedMarkedXHashAndGroupedCleanup
    encoding K q partAt term hmultiplicity sigma alpha targets pooled B hB seed

end AlgebraicComplexity.Examples
