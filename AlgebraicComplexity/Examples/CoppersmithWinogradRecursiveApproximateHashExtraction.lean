/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinogradRecursiveRelaxedHashExtraction
import AlgebraicComplexity.Examples.CoppersmithWinogradRecursiveHashExtraction
import AlgebraicComplexity.Combinatorics.LegwiseHashingExtraction

/-!
# Tensor-level relaxed hashing of an approximate recursive CW input

This module joins the two finite objects which the recursive constituent proof intentionally
keeps distinct:

* hashing and survivor counting take place in the full abstract marginal-word family; and
* tensor zero-outs act on the fine preimages present in the approximately selected parent.

An isolated abstract target need not have a fine preimage.  The restriction therefore retains the
whole fine preimage of every isolated target that is present, while leaving absent targets visible
as input-profile holes for the later repair theorem.  No lower bound on the number of present
targets is assumed here.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor MoreAsymmetryCompatibility

universe u v

/-- The actual supported quotient address containing one approximate-input fine address. -/
def cwRecursiveApproximateCoarseSourceOfFine
    (K : Type u) [CommRing K] (q : ℕ) {depth n : ℕ}
    (term : ExactInterfaceTermParameters (depth + 1))
    (hmultiplicity : term.multiplicity = n + 1)
    (epsilon : ℝ) (sigma : Orientation)
    (alpha : ExactRecursiveSplitType
      (cwRecursiveLogicalParent term sigma) (coarseTotal depth) (n + 1))
    (source : {address : BlockAddress (fun _c ↦
      PositiveWord (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n) //
      address ∈ (cwRecursiveApproximateAlphaMarginalSelectedTerm
        K q term hmultiplicity epsilon sigma alpha).support}) :
    {address : CWRecursiveCoarseAddress depth n //
      address ∈ (cwRecursiveApproximateCoarsenedAlphaMarginalTerm
        K q term hmultiplicity epsilon sigma alpha).support} := by
  refine ⟨cwRecursiveChildGroup depth n source.1, ?_⟩
  change cwRecursiveChildGroup depth n source.1 ∈
    ((cwRecursiveApproximateAlphaMarginalSelectedTerm
      K q term hmultiplicity epsilon sigma alpha).coarsen
        (cwRecursiveChildCoarsening depth n)).support
  rw [PartitionedTensor.coarsen_support]
  exact Finset.mem_image.mpr ⟨source.1, source.2, rfl⟩

@[simp] theorem cwRecursiveApproximateCoarseSourceOfFine_val
    (K : Type u) [CommRing K] (q : ℕ) {depth n : ℕ}
    (term : ExactInterfaceTermParameters (depth + 1))
    (hmultiplicity : term.multiplicity = n + 1)
    (epsilon : ℝ) (sigma : Orientation)
    (alpha : ExactRecursiveSplitType
      (cwRecursiveLogicalParent term sigma) (coarseTotal depth) (n + 1))
    (source : {address : BlockAddress (fun _c ↦
      PositiveWord (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n) //
      address ∈ (cwRecursiveApproximateAlphaMarginalSelectedTerm
        K q term hmultiplicity epsilon sigma alpha).support}) :
    (cwRecursiveApproximateCoarseSourceOfFine
      K q term hmultiplicity epsilon sigma alpha source).1 =
      cwRecursiveChildGroup depth n source.1 :=
  rfl

/-- The abstract marginal word represented by one actual approximate-input fine address. -/
def cwRecursiveApproximateRelaxedSourceOfFine
    (K : Type u) [CommRing K] (q : ℕ) {depth n : ℕ}
    (term : ExactInterfaceTermParameters (depth + 1))
    (hmultiplicity : term.multiplicity = n + 1)
    (epsilon : ℝ) (sigma : Orientation)
    (alpha : ExactRecursiveSplitType
      (cwRecursiveLogicalParent term sigma) (coarseTotal depth) (n + 1))
    (source : {address : BlockAddress (fun _c ↦
      PositiveWord (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n) //
      address ∈ (cwRecursiveApproximateAlphaMarginalSelectedTerm
        K q term hmultiplicity epsilon sigma alpha).support}) :
    {word // word ∈ alpha.marginalWords} := by
  let coarse := cwRecursiveApproximateCoarseSourceOfFine
    K q term hmultiplicity epsilon sigma alpha source
  exact ⟨cwRecursiveApproximateLogicalLeftShapeWordOfCoarse
      K q term hmultiplicity epsilon sigma alpha coarse.1 coarse.2,
    cwRecursiveApproximateLogicalLeftShapeWordOfCoarse_mem_marginalWords
      K q term hmultiplicity epsilon sigma alpha coarse.1 coarse.2⟩

/-- Rebuilding the relaxed quotient address of an actual fine source gives its genuine child
group. -/
theorem cwRecursiveCoarseAddress_approximateRelaxedSourceOfFine
    (K : Type u) [CommRing K] (q : ℕ) {depth n : ℕ}
    (term : ExactInterfaceTermParameters (depth + 1))
    (hmultiplicity : term.multiplicity = n + 1)
    (epsilon : ℝ) (sigma : Orientation)
    (alpha : ExactRecursiveSplitType
      (cwRecursiveLogicalParent term sigma) (coarseTotal depth) (n + 1))
    (source : {address : BlockAddress (fun _c ↦
      PositiveWord (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n) //
      address ∈ (cwRecursiveApproximateAlphaMarginalSelectedTerm
        K q term hmultiplicity epsilon sigma alpha).support}) :
    cwRecursiveCoarseAddressOfLeftShapeWord term sigma
        (cwRecursiveApproximateRelaxedSourceOfFine
          K q term hmultiplicity epsilon sigma alpha source).1 =
      cwRecursiveChildGroup depth n source.1 := by
  let coarse := cwRecursiveApproximateCoarseSourceOfFine
    K q term hmultiplicity epsilon sigma alpha source
  exact cwRecursiveCoarseAddressOfLeftShapeWord_approximateShape_eq
    K q term hmultiplicity epsilon sigma alpha coarse.1 coarse.2

/-- The relaxed legal triple attached to an actual fine source hashes precisely its labelled
child word on each logical leg. -/
theorem CWCoarseFieldEncoding.relaxedRecursiveLegalTriple_approximateFine_legIndex
    {R : Type v} [Field R] (encoding : CWCoarseFieldEncoding R depth)
    (K : Type u) [CommRing K] (q : ℕ) {n : ℕ}
    (term : ExactInterfaceTermParameters (depth + 1))
    (hmultiplicity : term.multiplicity = n + 1)
    (epsilon : ℝ) (sigma : Orientation)
    (alpha : ExactRecursiveSplitType
      (cwRecursiveLogicalParent term sigma) (coarseTotal depth) (n + 1))
    (source : {address : BlockAddress (fun _c ↦
      PositiveWord (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n) //
      address ∈ (cwRecursiveApproximateAlphaMarginalSelectedTerm
        K q term hmultiplicity epsilon sigma alpha).support})
    (logicalLeg : Leg) :
    (encoding.relaxedRecursiveOrientedLegalTriple term sigma
      (cwRecursiveApproximateRelaxedSourceOfFine
        K q term hmultiplicity epsilon sigma alpha source).1).legIndex logicalLeg =
      encoding.encode ∘ cwRecursiveLabelledChildWord
        depth n (source.1 (sigma logicalLeg)) := by
  have haddress := cwRecursiveCoarseAddress_approximateRelaxedSourceOfFine
    K q term hmultiplicity epsilon sigma alpha source
  cases logicalLeg <;>
    funext occurrence <;>
    change encoding.encode
        ((cwRecursiveCoarseAddressOfLeftShapeWord term sigma
          (cwRecursiveApproximateRelaxedSourceOfFine
            K q term hmultiplicity epsilon sigma alpha source).1)
            (sigma _) occurrence) =
      encoding.encode (cwRecursiveLabelledChildWord
        depth n (source.1 (sigma _)) occurrence) <;>
    rw [haddress] <;> rfl

/-! ## Fine common-bucket filtering -/

/-- Approximate marginal-selected support after the three independent hash-membership
zero-outs. -/
noncomputable def cwRecursiveApproximateOrientedHashFilteredFineSupport
    {R : Type v} [Field R] (encoding : CWCoarseFieldEncoding R depth)
    (K : Type u) [CommRing K] (q : ℕ) {n : ℕ}
    (term : ExactInterfaceTermParameters (depth + 1))
    (hmultiplicity : term.multiplicity = n + 1)
    (epsilon : ℝ) (sigma : Orientation)
    (alpha : ExactRecursiveSplitType
      (cwRecursiveLogicalParent term sigma) (coarseTotal depth) (n + 1))
    (B : Finset R)
    (seed : ProgressionHash.Seed R (Fin ((n + 1) + (n + 1)))) := by
  classical
  exact (cwRecursiveApproximateAlphaMarginalSelectedTerm
    K q term hmultiplicity epsilon sigma alpha).support.filter fun address ↦
      ∀ c, cwRecursiveOrientedHashKeepFineBlock
        encoding n sigma B seed c (address c)

@[simp] theorem mem_cwRecursiveApproximateOrientedHashFilteredFineSupport
    {R : Type v} [Field R] (encoding : CWCoarseFieldEncoding R depth)
    (K : Type u) [CommRing K] (q : ℕ) {n : ℕ}
    (term : ExactInterfaceTermParameters (depth + 1))
    (hmultiplicity : term.multiplicity = n + 1)
    (epsilon : ℝ) (sigma : Orientation)
    (alpha : ExactRecursiveSplitType
      (cwRecursiveLogicalParent term sigma) (coarseTotal depth) (n + 1))
    (B : Finset R)
    (seed : ProgressionHash.Seed R (Fin ((n + 1) + (n + 1)))) (address) :
    address ∈ cwRecursiveApproximateOrientedHashFilteredFineSupport
        encoding K q term hmultiplicity epsilon sigma alpha B seed ↔
      address ∈ (cwRecursiveApproximateAlphaMarginalSelectedTerm
          K q term hmultiplicity epsilon sigma alpha).support ∧
        ∀ c, cwRecursiveOrientedHashKeepFineBlock
          encoding n sigma B seed c (address c) := by
  classical
  simp [cwRecursiveApproximateOrientedHashFilteredFineSupport]

/-- Fine blockwise hash survival equals survival of the corresponding relaxed legal target. -/
theorem cwRecursiveApproximateHashKeep_all_iff_relaxedSurvives
    {R : Type v} [Field R] (encoding : CWCoarseFieldEncoding R depth)
    (K : Type u) [CommRing K] (q : ℕ) {n : ℕ}
    (term : ExactInterfaceTermParameters (depth + 1))
    (hmultiplicity : term.multiplicity = n + 1)
    (epsilon : ℝ) (sigma : Orientation)
    (alpha : ExactRecursiveSplitType
      (cwRecursiveLogicalParent term sigma) (coarseTotal depth) (n + 1))
    (B : Finset R)
    (seed : ProgressionHash.Seed R (Fin ((n + 1) + (n + 1))))
    (source : {address : BlockAddress (fun _c ↦
      PositiveWord (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n) //
      address ∈ (cwRecursiveApproximateAlphaMarginalSelectedTerm
        K q term hmultiplicity epsilon sigma alpha).support}) :
    (∀ c, cwRecursiveOrientedHashKeepFineBlock
        encoding n sigma B seed c (source.1 c)) ↔
      ProgressionHash.LegalTriple.SurvivesHashFilter (B : Set R) seed
        (encoding.relaxedRecursiveOrientedLegalTriple term sigma
          (cwRecursiveApproximateRelaxedSourceOfFine
            K q term hmultiplicity epsilon sigma alpha source).1) := by
  have hleg := encoding.relaxedRecursiveLegalTriple_approximateFine_legIndex
    K q term hmultiplicity epsilon sigma alpha source
  constructor
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · have hk := (cwRecursiveOrientedHashKeepFineBlock_sigma_X
          encoding n sigma B seed (source.1 (sigma .X))).mp (h (sigma .X))
      change seed.xHash
        ((encoding.relaxedRecursiveOrientedLegalTriple term sigma
          (cwRecursiveApproximateRelaxedSourceOfFine
            K q term hmultiplicity epsilon sigma alpha source).1).legIndex .X) ∈
          (B : Set R)
      rw [hleg .X]
      simpa using hk
    · have hk := (cwRecursiveOrientedHashKeepFineBlock_sigma_Y
          encoding n sigma B seed (source.1 (sigma .Y))).mp (h (sigma .Y))
      change seed.yHash
        ((encoding.relaxedRecursiveOrientedLegalTriple term sigma
          (cwRecursiveApproximateRelaxedSourceOfFine
            K q term hmultiplicity epsilon sigma alpha source).1).legIndex .Y) ∈
          (B : Set R)
      rw [hleg .Y]
      simpa using hk
    · have hk := (cwRecursiveOrientedHashKeepFineBlock_sigma_Z
          encoding n sigma B seed (source.1 (sigma .Z))).mp (h (sigma .Z))
      change seed.zHash encoding.target
        ((encoding.relaxedRecursiveOrientedLegalTriple term sigma
          (cwRecursiveApproximateRelaxedSourceOfFine
            K q term hmultiplicity epsilon sigma alpha source).1).legIndex .Z) ∈
          (B : Set R)
      rw [hleg .Z]
      simpa using hk
  · rintro ⟨hx, hy, hz⟩ c
    rw [← sigma.apply_symm_apply c]
    generalize hlogical : sigma.symm c = logical
    cases logical with
    | X =>
        apply (cwRecursiveOrientedHashKeepFineBlock_sigma_X
          encoding n sigma B seed (source.1 (sigma .X))).mpr
        rw [← hleg .X]
        exact hx
    | Y =>
        apply (cwRecursiveOrientedHashKeepFineBlock_sigma_Y
          encoding n sigma B seed (source.1 (sigma .Y))).mpr
        rw [← hleg .Y]
        exact hy
    | Z =>
        apply (cwRecursiveOrientedHashKeepFineBlock_sigma_Z
          encoding n sigma B seed (source.1 (sigma .Z))).mpr
        rw [← hleg .Z]
        exact hz

/-- The relaxed common-bucket filter is a genuine variable restriction of the approximate fine
input. -/
theorem cwRecursiveApproximateAlphaMarginalSelectedTerm_restricts_hashFilteredFine
    {R : Type v} [Field R] (encoding : CWCoarseFieldEncoding R depth)
    (K : Type u) [CommRing K] (q : ℕ) {n : ℕ}
    (term : ExactInterfaceTermParameters (depth + 1))
    (hmultiplicity : term.multiplicity = n + 1)
    (epsilon : ℝ) (sigma : Orientation)
    (alpha : ExactRecursiveSplitType
      (cwRecursiveLogicalParent term sigma) (coarseTotal depth) (n + 1))
    (B : Finset R)
    (seed : ProgressionHash.Seed R (Fin ((n + 1) + (n + 1)))) :
    let selected := cwRecursiveApproximateAlphaMarginalSelectedTerm
      K q term hmultiplicity epsilon sigma alpha
    let filtered := selected.withSupport
      (cwRecursiveApproximateOrientedHashFilteredFineSupport
        encoding K q term hmultiplicity epsilon sigma alpha B seed)
    Restricts selected.realize filtered.realize := by
  classical
  let selected := cwRecursiveApproximateAlphaMarginalSelectedTerm
    K q term hmultiplicity epsilon sigma alpha
  let keep := cwRecursiveOrientedHashKeepFineBlock encoding n sigma B seed
  let filteredSupport := cwRecursiveApproximateOrientedHashFilteredFineSupport
    encoding K q term hmultiplicity epsilon sigma alpha B seed
  let filtered := selected.withSupport filteredSupport
  have hselect := Tensor.Restricts.partitionedSelect selected keep
  apply hselect.trans (Restricts.of_eq ?_)
  apply PartitionedTensor.realize_eq_of_support_eq
  · rfl
  · intro address _haddress
    rfl

/-! ## Whole fine preimages of isolated intended targets -/

/-- The present fine preimages of relaxed isolated targets have their quotient group readable
from physical `sigma X` throughout the approximate hash-filtered ambient support. -/
theorem cwRecursiveApproximateRelaxedIsolatedFine_hasGroupUniqueLegFibers
    {R : Type v} [Field R] [Fintype R] [NeZero (2 : R)]
    (encoding : CWCoarseFieldEncoding R depth)
    (K : Type u) [CommRing K] (q : ℕ) {n : ℕ}
    (term : ExactInterfaceTermParameters (depth + 1))
    (hmultiplicity : term.multiplicity = n + 1)
    (epsilon : ℝ) (sigma : Orientation)
    (alpha : ExactRecursiveSplitType
      (cwRecursiveLogicalParent term sigma) (coarseTotal depth) (n + 1))
    (B : Finset R) (hB : ThreeAPFree (B : Set R))
    (seed : ProgressionHash.Seed R (Fin ((n + 1) + (n + 1)))) :
    let selected := cwRecursiveApproximateAlphaMarginalSelectedTerm
      K q term hmultiplicity epsilon sigma alpha
    let filteredSupport := cwRecursiveApproximateOrientedHashFilteredFineSupport
      encoding K q term hmultiplicity epsilon sigma alpha B seed
    let coarseKept := encoding.relaxedRecursiveMarkedXIsolatedCoarseSupport
      term sigma alpha B seed
    let isolatedSupport := cwRecursiveFineSupportOverCoarseSupport
      selected.support coarseKept
    HasGroupUniqueLegFibers filteredSupport isolatedSupport
      (cwRecursiveChildGroup depth n) (sigma .X) := by
  classical
  let selected := cwRecursiveApproximateAlphaMarginalSelectedTerm
    K q term hmultiplicity epsilon sigma alpha
  let filteredSupport := cwRecursiveApproximateOrientedHashFilteredFineSupport
    encoding K q term hmultiplicity epsilon sigma alpha B seed
  let coarseKept := encoding.relaxedRecursiveMarkedXIsolatedCoarseSupport
    term sigma alpha B seed
  let isolatedSupport := cwRecursiveFineSupportOverCoarseSupport
    selected.support coarseKept
  let ambient := encoding.relaxedRecursiveAmbientTargets term sigma alpha
  let marked := encoding.relaxedRecursiveMarkedTargets term sigma alpha
  let isolated := ProgressionHash.LegalTriple.markedXIsolatedTargets
    ambient marked B seed
  have hmarked : marked ⊆ ambient :=
    encoding.relaxedRecursiveMarkedTargets_subset_ambientTargets term sigma alpha
  refine ⟨?_, ?_⟩
  · intro address haddress
    have hisolated := (mem_cwRecursiveFineSupportOverCoarseSupport
      selected.support coarseKept address).mp haddress
    let source : {address // address ∈ selected.support} := ⟨address, hisolated.1⟩
    let relaxedSource := cwRecursiveApproximateRelaxedSourceOfFine
      K q term hmultiplicity epsilon sigma alpha source
    have htripleIsolated :
        encoding.relaxedRecursiveOrientedLegalTriple
          term sigma relaxedSource.1 ∈ isolated := by
      apply (encoding.mem_relaxedRecursiveMarkedXIsolatedCoarseSupport_iff
        term sigma alpha B seed relaxedSource).mp
      simpa [relaxedSource, source,
        cwRecursiveCoarseAddress_approximateRelaxedSourceOfFine] using hisolated.2
    have htripleFiltered :=
      ProgressionHash.LegalTriple.markedXIsolatedTargets_subset_filteredTargets
        ambient marked hmarked B seed htripleIsolated
    have hsurvives : ProgressionHash.LegalTriple.SurvivesHashFilter (B : Set R) seed
        (encoding.relaxedRecursiveOrientedLegalTriple
          term sigma relaxedSource.1) :=
      (Finset.mem_filter.mp htripleFiltered).2
    apply (mem_cwRecursiveApproximateOrientedHashFilteredFineSupport
      encoding K q term hmultiplicity epsilon sigma alpha B seed address).mpr
    refine ⟨hisolated.1, ?_⟩
    simpa [source, relaxedSource] using
      (cwRecursiveApproximateHashKeep_all_iff_relaxedSurvives
        encoding K q term hmultiplicity epsilon sigma alpha B seed source).mpr hsurvives
  · intro kept hkept other hother hlabel
    have hkeptData := (mem_cwRecursiveFineSupportOverCoarseSupport
      selected.support coarseKept kept).mp hkept
    have hotherData := (mem_cwRecursiveApproximateOrientedHashFilteredFineSupport
      encoding K q term hmultiplicity epsilon sigma alpha B seed other).mp hother
    let keptSource : {address // address ∈ selected.support} :=
      ⟨kept, hkeptData.1⟩
    let otherSource : {address // address ∈ selected.support} :=
      ⟨other, hotherData.1⟩
    let keptRelaxed := cwRecursiveApproximateRelaxedSourceOfFine
      K q term hmultiplicity epsilon sigma alpha keptSource
    let otherRelaxed := cwRecursiveApproximateRelaxedSourceOfFine
      K q term hmultiplicity epsilon sigma alpha otherSource
    have hkeptIsolated :
        encoding.relaxedRecursiveOrientedLegalTriple
          term sigma keptRelaxed.1 ∈ isolated := by
      apply (encoding.mem_relaxedRecursiveMarkedXIsolatedCoarseSupport_iff
        term sigma alpha B seed keptRelaxed).mp
      simpa [keptRelaxed, keptSource,
        cwRecursiveCoarseAddress_approximateRelaxedSourceOfFine] using hkeptData.2
    have hotherTarget :
        encoding.relaxedRecursiveOrientedLegalTriple
          term sigma otherRelaxed.1 ∈ ambient := by
      unfold ambient CWCoarseFieldEncoding.relaxedRecursiveAmbientTargets
      exact Finset.mem_image.mpr ⟨otherRelaxed.1, otherRelaxed.2, rfl⟩
    have hotherSurvives :
        ProgressionHash.LegalTriple.SurvivesHashFilter (B : Set R) seed
          (encoding.relaxedRecursiveOrientedLegalTriple
            term sigma otherRelaxed.1) :=
      (cwRecursiveApproximateHashKeep_all_iff_relaxedSurvives
        encoding K q term hmultiplicity epsilon sigma alpha B seed otherSource).mp
          hotherData.2
    have hotherFiltered :
        encoding.relaxedRecursiveOrientedLegalTriple
          term sigma otherRelaxed.1 ∈
        ProgressionHash.LegalTriple.filteredTargets ambient B seed :=
      Finset.mem_filter.mpr ⟨hotherTarget, hotherSurvives⟩
    have hxIndex :
        (encoding.relaxedRecursiveOrientedLegalTriple
          term sigma otherRelaxed.1).xIndex =
        (encoding.relaxedRecursiveOrientedLegalTriple
          term sigma keptRelaxed.1).xIndex := by
      rw [show (encoding.relaxedRecursiveOrientedLegalTriple
          term sigma otherRelaxed.1).xIndex =
          encoding.encode ∘ cwRecursiveLabelledChildWord
            depth n (otherSource.1 (sigma .X)) by
        exact encoding.relaxedRecursiveLegalTriple_approximateFine_legIndex
          K q term hmultiplicity epsilon sigma alpha otherSource .X]
      rw [show (encoding.relaxedRecursiveOrientedLegalTriple
          term sigma keptRelaxed.1).xIndex =
          encoding.encode ∘ cwRecursiveLabelledChildWord
            depth n (keptSource.1 (sigma .X)) by
        exact encoding.relaxedRecursiveLegalTriple_approximateFine_legIndex
          K q term hmultiplicity epsilon sigma alpha keptSource .X]
      exact congrArg (fun label ↦
        encoding.encode ∘ cwRecursiveLabelledChildWord depth n label) hlabel
    have htriple :
        encoding.relaxedRecursiveOrientedLegalTriple
            term sigma otherRelaxed.1 =
          encoding.relaxedRecursiveOrientedLegalTriple
            term sigma keptRelaxed.1 :=
      ProgressionHash.LegalTriple.eq_of_mem_markedXIsolatedTargets_of_mem_filteredTargets
        ambient marked hmarked B hB seed hkeptIsolated hotherFiltered hxIndex
    have hsource : otherRelaxed.1 = keptRelaxed.1 :=
      encoding.relaxedRecursiveOrientedLegalTriple_injective term sigma htriple
    calc
      cwRecursiveChildGroup depth n other =
          cwRecursiveCoarseAddressOfLeftShapeWord term sigma otherRelaxed.1 := by
        simpa [otherRelaxed, otherSource] using
          (cwRecursiveCoarseAddress_approximateRelaxedSourceOfFine
            K q term hmultiplicity epsilon sigma alpha otherSource).symm
      _ = cwRecursiveCoarseAddressOfLeftShapeWord term sigma keptRelaxed.1 :=
        congrArg _ hsource
      _ = cwRecursiveChildGroup depth n kept := by
        simpa [keptRelaxed, keptSource] using
          cwRecursiveCoarseAddress_approximateRelaxedSourceOfFine
            K q term hmultiplicity epsilon sigma alpha keptSource

/-- The approximate parent restricts to the entire present fine preimage of every relaxed
isolated target.  Empty intended fibers remain explicit holes rather than disappearing from the
survivor count. -/
theorem cwRecursiveApproximateAlphaMarginalSelectedTerm_restricts_relaxedIsolatedFine
    {R : Type v} [Field R] [Fintype R] [NeZero (2 : R)]
    (encoding : CWCoarseFieldEncoding R depth)
    (K : Type u) [CommRing K] (q : ℕ) {n : ℕ}
    (term : ExactInterfaceTermParameters (depth + 1))
    (hmultiplicity : term.multiplicity = n + 1)
    (epsilon : ℝ) (sigma : Orientation)
    (alpha : ExactRecursiveSplitType
      (cwRecursiveLogicalParent term sigma) (coarseTotal depth) (n + 1))
    (B : Finset R) (hB : ThreeAPFree (B : Set R))
    (seed : ProgressionHash.Seed R (Fin ((n + 1) + (n + 1)))) :
    let selected := cwRecursiveApproximateAlphaMarginalSelectedTerm
      K q term hmultiplicity epsilon sigma alpha
    let coarseKept := encoding.relaxedRecursiveMarkedXIsolatedCoarseSupport
      term sigma alpha B seed
    let isolatedSupport := cwRecursiveFineSupportOverCoarseSupport
      selected.support coarseKept
    Restricts selected.realize (selected.withSupport isolatedSupport).realize := by
  classical
  let selected := cwRecursiveApproximateAlphaMarginalSelectedTerm
    K q term hmultiplicity epsilon sigma alpha
  let filteredSupport := cwRecursiveApproximateOrientedHashFilteredFineSupport
    encoding K q term hmultiplicity epsilon sigma alpha B seed
  let filtered := selected.withSupport filteredSupport
  let coarseKept := encoding.relaxedRecursiveMarkedXIsolatedCoarseSupport
    term sigma alpha B seed
  let isolatedSupport := cwRecursiveFineSupportOverCoarseSupport
    selected.support coarseKept
  have hfirst : Restricts selected.realize filtered.realize := by
    simpa [selected, filtered, filteredSupport] using
      cwRecursiveApproximateAlphaMarginalSelectedTerm_restricts_hashFilteredFine
        encoding K q term hmultiplicity epsilon sigma alpha B seed
  have hunique : HasGroupUniqueLegFibers filteredSupport isolatedSupport
      (cwRecursiveChildGroup depth n) (sigma .X) := by
    simpa [selected, filteredSupport, coarseKept, isolatedSupport] using
      cwRecursiveApproximateRelaxedIsolatedFine_hasGroupUniqueLegFibers
        encoding K q term hmultiplicity epsilon sigma alpha B hB seed
  have hambient : filteredSupport ⊆ selected.support := by
    intro address haddress
    exact (mem_cwRecursiveApproximateOrientedHashFilteredFineSupport
      encoding K q term hmultiplicity epsilon sigma alpha B seed address).mp haddress |>.1
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

end AlgebraicComplexity.Examples
