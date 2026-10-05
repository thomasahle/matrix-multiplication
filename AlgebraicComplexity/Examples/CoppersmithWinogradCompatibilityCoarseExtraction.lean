/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinogradCompatibilityCoarseCleanup
import AlgebraicComplexity.Combinatorics.LegwiseHashingExtraction
import AlgebraicComplexity.Tensor.PartitionedGroupingBoxes

/-!
# Tensor-level coarse hashing and grouped CW cleanup

The affine hash acts on coarse constituent words, while compatibility cleanup acts on fine
complete-split blocks.  This module proves the missing semantic bridge: hash filtering and
`X`-isolation are genuine variable zero-outs on the fine tensor, but they retain every fine
monomial lying over a surviving coarse constituent.

Everything is orientation-parametric.  Logical `X` is the physical leg `sigma X`; no enumeration
of the six permutations is used.
-/

namespace AlgebraicComplexity

open Tensor

universe u v

namespace ProgressionHash.LegalTriple

variable {R : Type u} [Field R]
variable {I : Type v} [Fintype I]
variable {target : R}

/-- Relabel the three coordinates of a legal hashing triple by an arbitrary tensor orientation. -/
def orient (sigma : Orientation) (triple : LegalTriple R I target) :
    LegalTriple R I target where
  xIndex := triple.legIndex (sigma .X)
  yIndex := triple.legIndex (sigma .Y)
  zIndex := triple.legIndex (sigma .Z)
  legal sample := by
    have hperm :
        (∑ c : Leg, triple.legIndex (sigma c) sample) =
          ∑ c : Leg, triple.legIndex c sample :=
      Equiv.sum_comp sigma (fun c : Leg ↦ triple.legIndex c sample)
    have hsum : (∑ c : Leg, triple.legIndex c sample) = target := by
      simpa [Tensor.sum_leg] using triple.legal sample
    simpa [Tensor.sum_leg] using hperm.trans hsum

omit [Fintype I] in
@[simp] theorem orient_legIndex (sigma : Orientation)
    (triple : LegalTriple R I target) (c : Leg) :
    (orient sigma triple).legIndex c = triple.legIndex (sigma c) := by
  cases c <;> rfl

omit [Fintype I] in
@[simp] theorem orient_symm_orient (sigma : Orientation)
    (triple : LegalTriple R I target) :
    orient sigma.symm (orient sigma triple) = triple := by
  have hleg (c : Leg) :
      (orient sigma.symm (orient sigma triple)).legIndex c = triple.legIndex c := by
    rw [orient_legIndex, orient_legIndex, sigma.apply_symm_apply]
  exact LegalTriple.ext (hleg .X) (hleg .Y) (hleg .Z)

omit [Fintype I] in
/-- Coordinate orientation loses no legal hashing target. -/
theorem orient_injective (sigma : Orientation) :
    Function.Injective (orient sigma : LegalTriple R I target → LegalTriple R I target) :=
  (Function.LeftInverse.injective fun triple ↦ orient_symm_orient sigma triple)

end ProgressionHash.LegalTriple

namespace Examples

open MoreAsymmetryCompatibility

/-! ## Oriented coarse legal triples -/

namespace CWCoarseFieldEncoding

variable {R : Type v} [Field R]

/-- The un-oriented coarse legal triple reads each physical leg coordinatewise. -/
theorem legalTriple_legIndex (encoding : CWCoarseFieldEncoding R depth)
    (K : Type u) [CommRing K] (q : ℕ) {n : ℕ}
    (term : ExactInterfaceTermParameters depth)
    (hmultiplicity : term.multiplicity = n + 1)
    (source : {address : BlockAddress
      (fun _c ↦ PositiveWord (CWCoarseDigit depth) n) //
        address ∈ (cwCoarsenedSelectedExactInterfaceTerm
          K q term hmultiplicity).support}) (c : Leg) :
    (encoding.legalTriple K q term hmultiplicity source).legIndex c =
      encoding.encode ∘
        positiveWordEquiv (CWCoarseDigit depth) n (source.1 c) := by
  cases c <;> rfl

/-- Coarse legal triple in logical coordinates under physical orientation `sigma`. -/
def orientedLegalTriple (encoding : CWCoarseFieldEncoding R depth)
    (K : Type u) [CommRing K] (q : ℕ) {n : ℕ}
    (term : ExactInterfaceTermParameters depth)
    (hmultiplicity : term.multiplicity = n + 1) (sigma : Orientation)
    (source : {address : BlockAddress
      (fun _c ↦ PositiveWord (CWCoarseDigit depth) n) //
        address ∈ (cwCoarsenedSelectedExactInterfaceTerm
          K q term hmultiplicity).support}) :
    ProgressionHash.LegalTriple R (Fin (n + 1)) encoding.target :=
  (encoding.legalTriple K q term hmultiplicity source).orient sigma

@[simp] theorem orientedLegalTriple_legIndex
    (encoding : CWCoarseFieldEncoding R depth)
    (K : Type u) [CommRing K] (q : ℕ) {n : ℕ}
    (term : ExactInterfaceTermParameters depth)
    (hmultiplicity : term.multiplicity = n + 1) (sigma : Orientation)
    (source : {address : BlockAddress
      (fun _c ↦ PositiveWord (CWCoarseDigit depth) n) //
        address ∈ (cwCoarsenedSelectedExactInterfaceTerm
          K q term hmultiplicity).support}) (c : Leg) :
    (encoding.orientedLegalTriple K q term hmultiplicity sigma source).legIndex c =
      encoding.encode ∘ positiveWordEquiv (CWCoarseDigit depth) n
        (source.1 (sigma c)) := by
  rw [orientedLegalTriple, ProgressionHash.LegalTriple.orient_legIndex,
    encoding.legalTriple_legIndex]

/-- Oriented coarse legal triples still remember their complete coarse source address. -/
theorem orientedLegalTriple_injective
    (encoding : CWCoarseFieldEncoding R depth)
    (K : Type u) [CommRing K] (q : ℕ) {n : ℕ}
    (term : ExactInterfaceTermParameters depth)
    (hmultiplicity : term.multiplicity = n + 1) (sigma : Orientation) :
    Function.Injective
      (encoding.orientedLegalTriple K q term hmultiplicity sigma) :=
  (ProgressionHash.LegalTriple.orient_injective sigma).comp
    (encoding.legalTriple_injective K q term hmultiplicity)

/-- The full oriented target family represented by the coarsened selected support. -/
noncomputable def orientedLegalTargets
    (encoding : CWCoarseFieldEncoding R depth)
    (K : Type u) [CommRing K] (q : ℕ) {n : ℕ}
    (term : ExactInterfaceTermParameters depth)
    (hmultiplicity : term.multiplicity = n + 1) (sigma : Orientation) :
    Finset (ProgressionHash.LegalTriple R (Fin (n + 1)) encoding.target) := by
  classical
  exact Finset.univ.image
    (encoding.orientedLegalTriple K q term hmultiplicity sigma)

@[simp] theorem card_orientedLegalTargets
    (encoding : CWCoarseFieldEncoding R depth)
    (K : Type u) [CommRing K] (q : ℕ) {n : ℕ}
    (term : ExactInterfaceTermParameters depth)
    (hmultiplicity : term.multiplicity = n + 1) (sigma : Orientation) :
    (encoding.orientedLegalTargets K q term hmultiplicity sigma).card =
      (cwCoarsenedSelectedExactInterfaceTerm K q term hmultiplicity).support.card := by
  classical
  unfold orientedLegalTargets
  rw [Finset.card_image_of_injOn
    (encoding.orientedLegalTriple_injective K q term hmultiplicity sigma).injOn]
  simp

/-- Coarse sources surviving oriented complete logical-`X` isolation. -/
noncomputable def orientedXIsolatedSources
    (encoding : CWCoarseFieldEncoding R depth)
    (K : Type u) [CommRing K] (q : ℕ) {n : ℕ}
    (term : ExactInterfaceTermParameters depth)
    (hmultiplicity : term.multiplicity = n + 1) (sigma : Orientation)
    (B : Finset R) (seed : ProgressionHash.Seed R (Fin (n + 1))) := by
  classical
  exact Finset.univ.filter fun source ↦
    encoding.orientedLegalTriple K q term hmultiplicity sigma source ∈
      ProgressionHash.LegalTriple.xIsolatedTargets
        (encoding.orientedLegalTargets K q term hmultiplicity sigma) B seed

/-- Actual coarse addresses surviving the oriented logical-`X` isolation. -/
noncomputable def orientedXIsolatedCoarseSupport
    (encoding : CWCoarseFieldEncoding R depth)
    (K : Type u) [CommRing K] (q : ℕ) {n : ℕ}
    (term : ExactInterfaceTermParameters depth)
    (hmultiplicity : term.multiplicity = n + 1) (sigma : Orientation)
    (B : Finset R) (seed : ProgressionHash.Seed R (Fin (n + 1))) :
    Finset (BlockAddress (fun _c ↦ PositiveWord (CWCoarseDigit depth) n)) := by
  classical
  exact (encoding.orientedXIsolatedSources
    K q term hmultiplicity sigma B seed).image Subtype.val

@[simp] theorem mem_orientedXIsolatedCoarseSupport_iff
    (encoding : CWCoarseFieldEncoding R depth)
    (K : Type u) [CommRing K] (q : ℕ) {n : ℕ}
    (term : ExactInterfaceTermParameters depth)
    (hmultiplicity : term.multiplicity = n + 1) (sigma : Orientation)
    (B : Finset R) (seed : ProgressionHash.Seed R (Fin (n + 1)))
    (source : {address : BlockAddress
      (fun _c ↦ PositiveWord (CWCoarseDigit depth) n) //
        address ∈ (cwCoarsenedSelectedExactInterfaceTerm
          K q term hmultiplicity).support}) :
    source.1 ∈ encoding.orientedXIsolatedCoarseSupport
        K q term hmultiplicity sigma B seed ↔
      encoding.orientedLegalTriple K q term hmultiplicity sigma source ∈
        ProgressionHash.LegalTriple.xIsolatedTargets
          (encoding.orientedLegalTargets K q term hmultiplicity sigma) B seed := by
  classical
  constructor
  · intro hsource
    rw [orientedXIsolatedCoarseSupport, Finset.mem_image] at hsource
    obtain ⟨other, hother, hval⟩ := hsource
    have heq : other = source := Subtype.ext hval
    subst other
    exact (Finset.mem_filter.mp hother).2
  · intro hsource
    unfold orientedXIsolatedCoarseSupport orientedXIsolatedSources
    exact Finset.mem_image.mpr
      ⟨source, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hsource⟩, rfl⟩

/-- Oriented isolated coarse addresses are still supported coarse constituents. -/
theorem orientedXIsolatedCoarseSupport_subset
    (encoding : CWCoarseFieldEncoding R depth)
    (K : Type u) [CommRing K] (q : ℕ) {n : ℕ}
    (term : ExactInterfaceTermParameters depth)
    (hmultiplicity : term.multiplicity = n + 1) (sigma : Orientation)
    (B : Finset R) (seed : ProgressionHash.Seed R (Fin (n + 1))) :
    encoding.orientedXIsolatedCoarseSupport K q term hmultiplicity sigma B seed ⊆
      (cwCoarsenedSelectedExactInterfaceTerm K q term hmultiplicity).support := by
  classical
  intro address haddress
  rw [orientedXIsolatedCoarseSupport, Finset.mem_image] at haddress
  obtain ⟨source, _hsource, rfl⟩ := haddress
  exact source.2

/-- Oriented source-side and legal-triple-side isolated families have equal cardinality. -/
theorem card_orientedXIsolatedCoarseSupport
    (encoding : CWCoarseFieldEncoding R depth)
    [NeZero (2 : R)]
    (K : Type u) [CommRing K] (q : ℕ) {n : ℕ}
    (term : ExactInterfaceTermParameters depth)
    (hmultiplicity : term.multiplicity = n + 1) (sigma : Orientation)
    (B : Finset R) (seed : ProgressionHash.Seed R (Fin (n + 1))) :
    (encoding.orientedXIsolatedCoarseSupport
      K q term hmultiplicity sigma B seed).card =
      (ProgressionHash.LegalTriple.xIsolatedTargets
        (encoding.orientedLegalTargets K q term hmultiplicity sigma) B seed).card := by
  classical
  let sources := encoding.orientedXIsolatedSources
    K q term hmultiplicity sigma B seed
  let targets := encoding.orientedLegalTargets K q term hmultiplicity sigma
  let isolated := ProgressionHash.LegalTriple.xIsolatedTargets targets B seed
  have himage : isolated = sources.image
      (encoding.orientedLegalTriple K q term hmultiplicity sigma) := by
    ext triple
    constructor
    · intro htriple
      have htarget : triple ∈ targets := by
        exact ProgressionHash.LegalTriple.filteredTargets_subset targets B seed
          (ProgressionHash.LegalTriple.xIsolatedTargets_subset_filteredTargets
            targets B seed htriple)
      unfold targets orientedLegalTargets at htarget
      obtain ⟨source, _hsource, rfl⟩ := Finset.mem_image.mp htarget
      apply Finset.mem_image.mpr
      exact ⟨source, Finset.mem_filter.mpr ⟨Finset.mem_univ _, htriple⟩, rfl⟩
    · intro htriple
      obtain ⟨source, hsource, rfl⟩ := Finset.mem_image.mp htriple
      exact (Finset.mem_filter.mp hsource).2
  unfold orientedXIsolatedCoarseSupport
  rw [Finset.card_image_of_injOn Subtype.val_injective.injOn]
  calc
    sources.card =
        (sources.image
          (encoding.orientedLegalTriple K q term hmultiplicity sigma)).card :=
      (Finset.card_image_of_injOn
        (encoding.orientedLegalTriple_injective
          K q term hmultiplicity sigma).injOn).symm
    _ = isolated.card := congrArg Finset.card himage.symm

/-- Oriented logical-`X` isolation makes physical `sigma X` coarse labels injective. -/
theorem orientedX_injectiveOn_orientedXIsolatedCoarseSupport
    (encoding : CWCoarseFieldEncoding R depth)
    [Fintype R] [NeZero (2 : R)]
    (K : Type u) [CommRing K] (q : ℕ) {n : ℕ}
    (term : ExactInterfaceTermParameters depth)
    (hmultiplicity : term.multiplicity = n + 1) (sigma : Orientation)
    (B : Finset R) (seed : ProgressionHash.Seed R (Fin (n + 1))) :
    Set.InjOn
      (fun address : BlockAddress
        (fun _c ↦ PositiveWord (CWCoarseDigit depth) n) ↦ address (sigma .X))
      (encoding.orientedXIsolatedCoarseSupport
        K q term hmultiplicity sigma B seed : Set _) := by
  classical
  let targets := encoding.orientedLegalTargets K q term hmultiplicity sigma
  let isolated := ProgressionHash.LegalTriple.xIsolatedTargets targets B seed
  intro left hleft right hright hx
  change left ∈ encoding.orientedXIsolatedCoarseSupport
    K q term hmultiplicity sigma B seed at hleft
  change right ∈ encoding.orientedXIsolatedCoarseSupport
    K q term hmultiplicity sigma B seed at hright
  rw [orientedXIsolatedCoarseSupport, Finset.mem_image] at hleft hright
  obtain ⟨leftSource, hleftSource, rfl⟩ := hleft
  obtain ⟨rightSource, hrightSource, rfl⟩ := hright
  have hleftIsolated :
      encoding.orientedLegalTriple K q term hmultiplicity sigma leftSource ∈ isolated :=
    (Finset.mem_filter.mp hleftSource).2
  have hrightIsolated :
      encoding.orientedLegalTriple K q term hmultiplicity sigma rightSource ∈ isolated :=
    (Finset.mem_filter.mp hrightSource).2
  have hindex :
      (encoding.orientedLegalTriple K q term hmultiplicity sigma leftSource).xIndex =
        (encoding.orientedLegalTriple K q term hmultiplicity sigma rightSource).xIndex := by
    rw [show (encoding.orientedLegalTriple K q term hmultiplicity sigma leftSource).xIndex =
        (encoding.orientedLegalTriple K q term hmultiplicity sigma leftSource).legIndex .X by rfl,
      show (encoding.orientedLegalTriple K q term hmultiplicity sigma rightSource).xIndex =
        (encoding.orientedLegalTriple K q term hmultiplicity sigma rightSource).legIndex .X by rfl,
      encoding.orientedLegalTriple_legIndex, encoding.orientedLegalTriple_legIndex]
    change leftSource.1 (sigma .X) = rightSource.1 (sigma .X) at hx
    rw [hx]
  have htargetInj : Set.InjOn
      (fun triple : ProgressionHash.LegalTriple R (Fin (n + 1)) encoding.target ↦
        triple.xIndex)
      (isolated : Set (ProgressionHash.LegalTriple
        R (Fin (n + 1)) encoding.target)) := by
    apply ProgressionHash.Seed.xIndex_injectiveOn_isolatedTargets
      targets B ProgressionHash.LegalTriple.xIndex ProgressionHash.LegalTriple.yIndex
      (ProgressionHash.LegalTriple.xCompetitorYIndices targets) seed
    intro triple htriple other hother hne hx
    exact ProgressionHash.LegalTriple.yIndex_mem_xCompetitorYIndices
      targets hother hne hx
  have htriple := htargetInj hleftIsolated hrightIsolated hindex
  exact congrArg Subtype.val
    (encoding.orientedLegalTriple_injective K q term hmultiplicity sigma htriple)

/-- Orientation-parametric finite coarse hashing extraction with the exact division-free count. -/
theorem exists_seed_many_orientedXIsolatedCoarseSupport
    (encoding : CWCoarseFieldEncoding R depth)
    [Fintype R] [NeZero (2 : R)]
    (K : Type u) [CommRing K] (q : ℕ) {n : ℕ}
    (term : ExactInterfaceTermParameters depth)
    (hmultiplicity : term.multiplicity = n + 1) (sigma : Orientation)
    (B : Finset R)
    (hquarter : ∀ triple ∈
      encoding.orientedLegalTargets K q term hmultiplicity sigma,
      4 * (ProgressionHash.LegalTriple.xCompetitorYIndices
        (encoding.orientedLegalTargets K q term hmultiplicity sigma) triple).card ≤
          Fintype.card R) :
    ∃ seed : ProgressionHash.Seed R (Fin (n + 1)),
      3 * (cwCoarsenedSelectedExactInterfaceTerm K q term hmultiplicity).support.card *
          B.card ≤
        4 * (Fintype.card R * Fintype.card R) *
          (encoding.orientedXIsolatedCoarseSupport
            K q term hmultiplicity sigma B seed).card ∧
      encoding.orientedXIsolatedCoarseSupport K q term hmultiplicity sigma B seed ⊆
        (cwCoarsenedSelectedExactInterfaceTerm K q term hmultiplicity).support ∧
      Set.InjOn
        (fun address : BlockAddress
          (fun _c ↦ PositiveWord (CWCoarseDigit depth) n) ↦ address (sigma .X))
        (encoding.orientedXIsolatedCoarseSupport
          K q term hmultiplicity sigma B seed : Set _) := by
  obtain ⟨seed, hcount, _hfiltered, _hinjective⟩ :=
    ProgressionHash.LegalTriple.exists_seed_many_xIsolatedTargets
      (encoding.orientedLegalTargets K q term hmultiplicity sigma) B hquarter
  refine ⟨seed, ?_,
    encoding.orientedXIsolatedCoarseSupport_subset
      K q term hmultiplicity sigma B seed,
    encoding.orientedX_injectiveOn_orientedXIsolatedCoarseSupport
      K q term hmultiplicity sigma B seed⟩
  simpa [encoding.card_orientedLegalTargets K q term hmultiplicity sigma,
    encoding.card_orientedXIsolatedCoarseSupport
      K q term hmultiplicity sigma B seed] using hcount

end CWCoarseFieldEncoding

/-! ## Fine preimages and exact tensor zero-outs -/

/-- The supported coarse address containing one supported fine exact-interface address. -/
def cwCoarseSourceOfFine
    (K : Type u) [CommRing K] (q : ℕ) {depth n : ℕ}
    (term : ExactInterfaceTermParameters depth)
    (hmultiplicity : term.multiplicity = n + 1)
    (source : {address : BlockAddress (fun _c ↦
      PositiveWord (PositiveWord CWBlock (2 ^ depth - 1)) n) //
      address ∈ (cwSelectedExactInterfaceTerm K q term hmultiplicity).support}) :
    {address : BlockAddress (fun _c ↦ PositiveWord (CWCoarseDigit depth) n) //
      address ∈ (cwCoarsenedSelectedExactInterfaceTerm
        K q term hmultiplicity).support} := by
  refine ⟨cwExactInterfaceCoarseGroup depth n source.1, ?_⟩
  change cwExactInterfaceCoarseGroup depth n source.1 ∈
    ((cwSelectedExactInterfaceTerm K q term hmultiplicity).coarsen
      (cwExactInterfaceCoarsening depth n)).support
  rw [PartitionedTensor.coarsen_support]
  exact Finset.mem_image.mpr ⟨source.1, source.2, rfl⟩

@[simp] theorem cwCoarseSourceOfFine_val
    (K : Type u) [CommRing K] (q : ℕ) {depth n : ℕ}
    (term : ExactInterfaceTermParameters depth)
    (hmultiplicity : term.multiplicity = n + 1)
    (source : {address : BlockAddress (fun _c ↦
      PositiveWord (PositiveWord CWBlock (2 ^ depth - 1)) n) //
      address ∈ (cwSelectedExactInterfaceTerm K q term hmultiplicity).support}) :
    (cwCoarseSourceOfFine K q term hmultiplicity source).1 =
      cwExactInterfaceCoarseGroup depth n source.1 :=
  rfl

/-- Independent physical block predicate implementing the oriented coarse hash filter on fine
labels. -/
noncomputable def cwOrientedCoarseHashKeepFineBlock
    {R : Type v} [Field R] (encoding : CWCoarseFieldEncoding R depth)
    (n : ℕ) (sigma : Orientation) (B : Finset R)
    (seed : ProgressionHash.Seed R (Fin (n + 1))) :
    (c : Leg) → PositiveWord (PositiveWord CWBlock (2 ^ depth - 1)) n → Prop :=
  fun c label ↦
    let coarse := cwOuterCoarseWord depth n label
    match sigma.symm c with
    | .X => seed.xHash
        (encoding.encode ∘ positiveWordEquiv (CWCoarseDigit depth) n coarse) ∈ B
    | .Y => seed.yHash
        (encoding.encode ∘ positiveWordEquiv (CWCoarseDigit depth) n coarse) ∈ B
    | .Z => seed.zHash encoding.target
        (encoding.encode ∘ positiveWordEquiv (CWCoarseDigit depth) n coarse) ∈ B

@[simp] theorem cwOrientedCoarseHashKeepFineBlock_sigma_X
    {R : Type v} [Field R] (encoding : CWCoarseFieldEncoding R depth)
    (n : ℕ) (sigma : Orientation) (B : Finset R)
    (seed : ProgressionHash.Seed R (Fin (n + 1))) (label) :
    cwOrientedCoarseHashKeepFineBlock encoding n sigma B seed (sigma .X) label ↔
      seed.xHash (encoding.encode ∘ positiveWordEquiv (CWCoarseDigit depth) n
        (cwOuterCoarseWord depth n label)) ∈ B := by
  simp [cwOrientedCoarseHashKeepFineBlock]

@[simp] theorem cwOrientedCoarseHashKeepFineBlock_sigma_Y
    {R : Type v} [Field R] (encoding : CWCoarseFieldEncoding R depth)
    (n : ℕ) (sigma : Orientation) (B : Finset R)
    (seed : ProgressionHash.Seed R (Fin (n + 1))) (label) :
    cwOrientedCoarseHashKeepFineBlock encoding n sigma B seed (sigma .Y) label ↔
      seed.yHash (encoding.encode ∘ positiveWordEquiv (CWCoarseDigit depth) n
        (cwOuterCoarseWord depth n label)) ∈ B := by
  simp [cwOrientedCoarseHashKeepFineBlock]

@[simp] theorem cwOrientedCoarseHashKeepFineBlock_sigma_Z
    {R : Type v} [Field R] (encoding : CWCoarseFieldEncoding R depth)
    (n : ℕ) (sigma : Orientation) (B : Finset R)
    (seed : ProgressionHash.Seed R (Fin (n + 1))) (label) :
    cwOrientedCoarseHashKeepFineBlock encoding n sigma B seed (sigma .Z) label ↔
      seed.zHash encoding.target
        (encoding.encode ∘ positiveWordEquiv (CWCoarseDigit depth) n
          (cwOuterCoarseWord depth n label)) ∈ B := by
  simp [cwOrientedCoarseHashKeepFineBlock]

/-- Fine support after the three independent oriented coarse-hash block zero-outs. -/
noncomputable def cwOrientedHashFilteredFineSupport
    {R : Type v} [Field R] (encoding : CWCoarseFieldEncoding R depth)
    (K : Type u) [CommRing K] (q : ℕ) {n : ℕ}
    (term : ExactInterfaceTermParameters depth)
    (hmultiplicity : term.multiplicity = n + 1) (sigma : Orientation)
    (B : Finset R) (seed : ProgressionHash.Seed R (Fin (n + 1))) := by
  classical
  exact (cwSelectedExactInterfaceTerm K q term hmultiplicity).support.filter
    (fun address ↦ ∀ c,
      cwOrientedCoarseHashKeepFineBlock encoding n sigma B seed c (address c))

@[simp] theorem mem_cwOrientedHashFilteredFineSupport
    {R : Type v} [Field R] (encoding : CWCoarseFieldEncoding R depth)
    (K : Type u) [CommRing K] (q : ℕ) {n : ℕ}
    (term : ExactInterfaceTermParameters depth)
    (hmultiplicity : term.multiplicity = n + 1) (sigma : Orientation)
    (B : Finset R) (seed : ProgressionHash.Seed R (Fin (n + 1))) (address) :
    address ∈ cwOrientedHashFilteredFineSupport
        encoding K q term hmultiplicity sigma B seed ↔
      address ∈ (cwSelectedExactInterfaceTerm K q term hmultiplicity).support ∧
        ∀ c, cwOrientedCoarseHashKeepFineBlock
          encoding n sigma B seed c (address c) := by
  classical
  simp [cwOrientedHashFilteredFineSupport]

/-- The independent fine block predicates are exactly survival of the associated oriented coarse
legal triple. -/
theorem cwOrientedCoarseHashKeepFineBlock_all_iff_survives
    {R : Type v} [Field R] (encoding : CWCoarseFieldEncoding R depth)
    (K : Type u) [CommRing K] (q : ℕ) {n : ℕ}
    (term : ExactInterfaceTermParameters depth)
    (hmultiplicity : term.multiplicity = n + 1) (sigma : Orientation)
    (B : Finset R) (seed : ProgressionHash.Seed R (Fin (n + 1)))
    (source : {address : BlockAddress (fun _c ↦
      PositiveWord (PositiveWord CWBlock (2 ^ depth - 1)) n) //
      address ∈ (cwSelectedExactInterfaceTerm K q term hmultiplicity).support}) :
    (∀ c, cwOrientedCoarseHashKeepFineBlock
      encoding n sigma B seed c (source.1 c)) ↔
      ProgressionHash.LegalTriple.SurvivesHashFilter (B : Set R) seed
        (encoding.orientedLegalTriple K q term hmultiplicity sigma
          (cwCoarseSourceOfFine K q term hmultiplicity source)) := by
  let coarseSource := cwCoarseSourceOfFine K q term hmultiplicity source
  have hleg (logical : Leg) :
      (encoding.orientedLegalTriple K q term hmultiplicity sigma coarseSource).legIndex
          logical =
        encoding.encode ∘ positiveWordEquiv (CWCoarseDigit depth) n
          (cwOuterCoarseWord depth n (source.1 (sigma logical))) := by
    simpa [coarseSource, cwExactInterfaceCoarseGroup_apply] using
      encoding.orientedLegalTriple_legIndex
        K q term hmultiplicity sigma coarseSource logical
  dsimp only [coarseSource] at hleg
  constructor
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · have hk := (cwOrientedCoarseHashKeepFineBlock_sigma_X
          encoding n sigma B seed (source.1 (sigma .X))).mp (h (sigma .X))
      change seed.xHash
        ((encoding.orientedLegalTriple K q term hmultiplicity sigma
          (cwCoarseSourceOfFine K q term hmultiplicity source)).legIndex .X) ∈
            (B : Set R)
      rw [hleg .X]
      simpa using hk
    · have hk := (cwOrientedCoarseHashKeepFineBlock_sigma_Y
          encoding n sigma B seed (source.1 (sigma .Y))).mp (h (sigma .Y))
      change seed.yHash
        ((encoding.orientedLegalTriple K q term hmultiplicity sigma
          (cwCoarseSourceOfFine K q term hmultiplicity source)).legIndex .Y) ∈
            (B : Set R)
      rw [hleg .Y]
      simpa using hk
    · have hk := (cwOrientedCoarseHashKeepFineBlock_sigma_Z
          encoding n sigma B seed (source.1 (sigma .Z))).mp (h (sigma .Z))
      change seed.zHash encoding.target
        ((encoding.orientedLegalTriple K q term hmultiplicity sigma
          (cwCoarseSourceOfFine K q term hmultiplicity source)).legIndex .Z) ∈
            (B : Set R)
      rw [hleg .Z]
      simpa using hk
  · rintro ⟨hx, hy, hz⟩ c
    rw [← sigma.apply_symm_apply c]
    generalize hlogical : sigma.symm c = logical
    cases logical with
    | X =>
        apply (cwOrientedCoarseHashKeepFineBlock_sigma_X
          encoding n sigma B seed (source.1 (sigma .X))).mpr
        have hx' : seed.xHash
            ((encoding.orientedLegalTriple K q term hmultiplicity sigma
              (cwCoarseSourceOfFine K q term hmultiplicity source)).legIndex .X) ∈
              (B : Set R) := hx
        rw [hleg .X] at hx'
        simpa using hx'
    | Y =>
        apply (cwOrientedCoarseHashKeepFineBlock_sigma_Y
          encoding n sigma B seed (source.1 (sigma .Y))).mpr
        have hy' : seed.yHash
            ((encoding.orientedLegalTriple K q term hmultiplicity sigma
              (cwCoarseSourceOfFine K q term hmultiplicity source)).legIndex .Y) ∈
              (B : Set R) := hy
        rw [hleg .Y] at hy'
        simpa using hy'
    | Z =>
        apply (cwOrientedCoarseHashKeepFineBlock_sigma_Z
          encoding n sigma B seed (source.1 (sigma .Z))).mpr
        have hz' : seed.zHash encoding.target
            ((encoding.orientedLegalTriple K q term hmultiplicity sigma
              (cwCoarseSourceOfFine K q term hmultiplicity source)).legIndex .Z) ∈
              (B : Set R) := hz
        rw [hleg .Z] at hz'
        simpa using hz'

/-- The first, independent coarse hash filter is an exact variable zero-out on the fine tensor. -/
theorem cwSelectedExactInterfaceTerm_restricts_orientedHashFilteredFine
    {R : Type v} [Field R] (encoding : CWCoarseFieldEncoding R depth)
    (K : Type u) [CommRing K] (q : ℕ) {n : ℕ}
    (term : ExactInterfaceTermParameters depth)
    (hmultiplicity : term.multiplicity = n + 1) (sigma : Orientation)
    (B : Finset R) (seed : ProgressionHash.Seed R (Fin (n + 1))) :
    let selected := cwSelectedExactInterfaceTerm K q term hmultiplicity
    let filtered := selected.withSupport
      (cwOrientedHashFilteredFineSupport
        encoding K q term hmultiplicity sigma B seed)
    Restricts selected.realize filtered.realize := by
  classical
  let selected := cwSelectedExactInterfaceTerm K q term hmultiplicity
  let keep := cwOrientedCoarseHashKeepFineBlock encoding n sigma B seed
  let filteredSupport := cwOrientedHashFilteredFineSupport
    encoding K q term hmultiplicity sigma B seed
  let filtered := selected.withSupport filteredSupport
  have hselect := Tensor.Restricts.partitionedSelect selected keep
  apply hselect.trans (Restricts.of_eq ?_)
  apply PartitionedTensor.realize_eq_of_support_eq
  · rfl
  · intro address _haddress
    rfl

/-- Oriented isolated fine preimages have a coarse group readable from physical `sigma X`
inside the hash-filtered fine ambient support. -/
theorem cwOrientedXIsolatedFine_hasGroupUniqueLegFibers
    {R : Type v} [Field R] [Fintype R] [NeZero (2 : R)]
    (encoding : CWCoarseFieldEncoding R depth)
    (K : Type u) [CommRing K] (q : ℕ) {n : ℕ}
    (term : ExactInterfaceTermParameters depth)
    (hmultiplicity : term.multiplicity = n + 1) (sigma : Orientation)
    (B : Finset R) (hB : ThreeAPFree (B : Set R))
    (seed : ProgressionHash.Seed R (Fin (n + 1))) :
    let selected := cwSelectedExactInterfaceTerm K q term hmultiplicity
    let filteredSupport := cwOrientedHashFilteredFineSupport
      encoding K q term hmultiplicity sigma B seed
    let coarseKept := encoding.orientedXIsolatedCoarseSupport
      K q term hmultiplicity sigma B seed
    let isolatedSupport := cwFineSupportOverCoarseSupport selected.support coarseKept
    HasGroupUniqueLegFibers filteredSupport isolatedSupport
      (cwExactInterfaceCoarseGroup depth n) (sigma .X) := by
  classical
  let selected := cwSelectedExactInterfaceTerm K q term hmultiplicity
  let filteredSupport := cwOrientedHashFilteredFineSupport
    encoding K q term hmultiplicity sigma B seed
  let coarseKept := encoding.orientedXIsolatedCoarseSupport
    K q term hmultiplicity sigma B seed
  let isolatedSupport := cwFineSupportOverCoarseSupport selected.support coarseKept
  let targets := encoding.orientedLegalTargets K q term hmultiplicity sigma
  refine ⟨?_, ?_⟩
  · intro address haddress
    have hisolated := (mem_cwFineSupportOverCoarseSupport
      selected.support coarseKept address).mp haddress
    let source : {address // address ∈ selected.support} :=
      ⟨address, hisolated.1⟩
    have hcoarseIsolated :
        (cwCoarseSourceOfFine K q term hmultiplicity source).1 ∈ coarseKept := by
      simpa [coarseKept, source] using hisolated.2
    have htripleIsolated :=
      (encoding.mem_orientedXIsolatedCoarseSupport_iff
        K q term hmultiplicity sigma B seed
          (cwCoarseSourceOfFine K q term hmultiplicity source)).mp hcoarseIsolated
    have htripleFiltered :=
      ProgressionHash.LegalTriple.xIsolatedTargets_subset_filteredTargets
        targets B seed htripleIsolated
    have hsurvives : ProgressionHash.LegalTriple.SurvivesHashFilter (B : Set R) seed
        (encoding.orientedLegalTriple K q term hmultiplicity sigma
          (cwCoarseSourceOfFine K q term hmultiplicity source)) :=
      (Finset.mem_filter.mp htripleFiltered).2
    apply (mem_cwOrientedHashFilteredFineSupport
      encoding K q term hmultiplicity sigma B seed address).mpr
    refine ⟨hisolated.1, ?_⟩
    simpa [source] using
      (cwOrientedCoarseHashKeepFineBlock_all_iff_survives
        encoding K q term hmultiplicity sigma B seed source).mpr hsurvives
  · intro kept hkept other hother hlabel
    have hkeptData := (mem_cwFineSupportOverCoarseSupport
      selected.support coarseKept kept).mp hkept
    have hotherData := (mem_cwOrientedHashFilteredFineSupport
      encoding K q term hmultiplicity sigma B seed other).mp hother
    let keptSource : {address // address ∈ selected.support} :=
      ⟨kept, hkeptData.1⟩
    let otherSource : {address // address ∈ selected.support} :=
      ⟨other, hotherData.1⟩
    let keptCoarse := cwCoarseSourceOfFine K q term hmultiplicity keptSource
    let otherCoarse := cwCoarseSourceOfFine K q term hmultiplicity otherSource
    have hkeptIsolated :
        encoding.orientedLegalTriple K q term hmultiplicity sigma keptCoarse ∈
          ProgressionHash.LegalTriple.xIsolatedTargets targets B seed := by
      apply (encoding.mem_orientedXIsolatedCoarseSupport_iff
        K q term hmultiplicity sigma B seed keptCoarse).mp
      simpa [coarseKept, keptCoarse, keptSource] using hkeptData.2
    have hotherTarget :
        encoding.orientedLegalTriple K q term hmultiplicity sigma otherCoarse ∈
          targets := by
      unfold targets CWCoarseFieldEncoding.orientedLegalTargets
      exact Finset.mem_image.mpr ⟨otherCoarse, Finset.mem_univ _, rfl⟩
    have hotherSurvives :
        ProgressionHash.LegalTriple.SurvivesHashFilter (B : Set R) seed
          (encoding.orientedLegalTriple K q term hmultiplicity sigma otherCoarse) :=
      (cwOrientedCoarseHashKeepFineBlock_all_iff_survives
        encoding K q term hmultiplicity sigma B seed otherSource).mp hotherData.2
    have hotherFiltered :
        encoding.orientedLegalTriple K q term hmultiplicity sigma otherCoarse ∈
          ProgressionHash.LegalTriple.filteredTargets targets B seed :=
      Finset.mem_filter.mpr ⟨hotherTarget, hotherSurvives⟩
    have hxIndex :
        (encoding.orientedLegalTriple K q term hmultiplicity sigma otherCoarse).xIndex =
          (encoding.orientedLegalTriple K q term hmultiplicity sigma keptCoarse).xIndex := by
      rw [show (encoding.orientedLegalTriple K q term hmultiplicity sigma otherCoarse).xIndex =
          (encoding.orientedLegalTriple K q term hmultiplicity sigma otherCoarse).legIndex .X by rfl,
        show (encoding.orientedLegalTriple K q term hmultiplicity sigma keptCoarse).xIndex =
          (encoding.orientedLegalTriple K q term hmultiplicity sigma keptCoarse).legIndex .X by rfl,
        encoding.orientedLegalTriple_legIndex, encoding.orientedLegalTriple_legIndex]
      change encoding.encode ∘ positiveWordEquiv (CWCoarseDigit depth) n
          (cwOuterCoarseWord depth n (other (sigma .X))) =
        encoding.encode ∘ positiveWordEquiv (CWCoarseDigit depth) n
          (cwOuterCoarseWord depth n (kept (sigma .X)))
      rw [hlabel]
    have htriple :
        encoding.orientedLegalTriple K q term hmultiplicity sigma otherCoarse =
          encoding.orientedLegalTriple K q term hmultiplicity sigma keptCoarse :=
      ProgressionHash.LegalTriple.eq_of_mem_xIsolatedTargets_of_mem_filteredTargets
        targets B hB seed hkeptIsolated hotherFiltered hxIndex
    have hsource : otherCoarse = keptCoarse :=
      encoding.orientedLegalTriple_injective K q term hmultiplicity sigma htriple
    exact congrArg Subtype.val hsource

/-- The fine preimage of a coarse address set keeps whole coarse groups. -/
theorem cwFineSupportOverCoarseSupport_isGroupSaturatedIn
    {depth n : ℕ}
    (fine ambient : Finset (BlockAddress (fun _c ↦
      PositiveWord (PositiveWord CWBlock (2 ^ depth - 1)) n)))
    (coarse : Finset (BlockAddress
      (fun _c ↦ PositiveWord (CWCoarseDigit depth) n)))
    (hambient : ambient ⊆ fine) :
    IsGroupSaturatedIn ambient (cwFineSupportOverCoarseSupport fine coarse)
      (cwExactInterfaceCoarseGroup depth n) := by
  intro selected hselectedMem other hother hgroup
  have hselectedData :=
    (mem_cwFineSupportOverCoarseSupport fine coarse selected).mp hselectedMem
  apply (mem_cwFineSupportOverCoarseSupport fine coarse other).mpr
  exact ⟨hambient hother, hgroup.symm ▸ hselectedData.2⟩

/-- Complete tensor-level oriented coarse hash extraction: the selected fine term restricts to
the full fine preimage of the isolated coarse support. -/
theorem cwSelectedExactInterfaceTerm_restricts_orientedXIsolatedFine
    {R : Type v} [Field R] [Fintype R] [NeZero (2 : R)]
    (encoding : CWCoarseFieldEncoding R depth)
    (K : Type u) [CommRing K] (q : ℕ) {n : ℕ}
    (term : ExactInterfaceTermParameters depth)
    (hmultiplicity : term.multiplicity = n + 1) (sigma : Orientation)
    (B : Finset R) (hB : ThreeAPFree (B : Set R))
    (seed : ProgressionHash.Seed R (Fin (n + 1))) :
    let selected := cwSelectedExactInterfaceTerm K q term hmultiplicity
    let coarseKept := encoding.orientedXIsolatedCoarseSupport
      K q term hmultiplicity sigma B seed
    let isolatedSupport := cwFineSupportOverCoarseSupport selected.support coarseKept
    Restricts selected.realize (selected.withSupport isolatedSupport).realize := by
  classical
  let selected := cwSelectedExactInterfaceTerm K q term hmultiplicity
  let filteredSupport := cwOrientedHashFilteredFineSupport
    encoding K q term hmultiplicity sigma B seed
  let filtered := selected.withSupport filteredSupport
  let coarseKept := encoding.orientedXIsolatedCoarseSupport
    K q term hmultiplicity sigma B seed
  let isolatedSupport := cwFineSupportOverCoarseSupport selected.support coarseKept
  have hfirst : Restricts selected.realize filtered.realize := by
    simpa [selected, filtered, filteredSupport] using
      cwSelectedExactInterfaceTerm_restricts_orientedHashFilteredFine
        encoding K q term hmultiplicity sigma B seed
  have hunique : HasGroupUniqueLegFibers filteredSupport isolatedSupport
      (cwExactInterfaceCoarseGroup depth n) (sigma .X) := by
    simpa [selected, filteredSupport, coarseKept, isolatedSupport] using
      cwOrientedXIsolatedFine_hasGroupUniqueLegFibers
        encoding K q term hmultiplicity sigma B hB seed
  have hambient : filteredSupport ⊆ selected.support := by
    intro address haddress
    exact (mem_cwOrientedHashFilteredFineSupport
      encoding K q term hmultiplicity sigma B seed address).mp haddress |>.1
  have hsaturated : IsGroupSaturatedIn filteredSupport isolatedSupport
      (cwExactInterfaceCoarseGroup depth n) :=
    cwFineSupportOverCoarseSupport_isGroupSaturatedIn
      selected.support filteredSupport coarseKept hambient
  have hsecond : Restricts filtered.realize
      (filtered.withSupport isolatedSupport).realize := by
    exact Tensor.Restricts.partitionedGroupSaturated filtered isolatedSupport
      (cwExactInterfaceCoarseGroup depth n) (sigma .X)
      (by simpa [filtered] using hunique) hsaturated
  exact hfirst.trans (hsecond.trans (Restricts.of_eq (by rfl)))

/-- The complete paper-order compatibility/profile cleanup is a Cartesian variable deletion
inside the hash-retained fine tensor.  More precisely, its final support is projection-closed on
all three legs in the hash-retained support.

This is the exact finite fact needed to regard every final coarse fiber as a damaged box of its
ideal, pre-cleanup coarse fiber; it does not yet identify those ideal fibers with one canonical
child interface tensor. -/
theorem cwSelectedExactInterfaceTerm_orientedGroupedCleanup_isProjectionClosed
    (K : Type u) [CommRing K] (q : ℕ) {Part : Type v} [DecidableEq Part]
    {depth n : ℕ} (partAt : Fin (n + 1) → Part)
    (term : ExactInterfaceTermParameters depth)
    (hmultiplicity : term.multiplicity = n + 1)
    (sigma : Orientation) (targets : CompatibilityTargets Part depth)
    (pooled : PooledAllTargets targets)
    (coarseKept : Finset (BlockAddress (fun _c ↦
      PositiveWord (CWCoarseDigit depth) n)))
    (hcoarseX : Set.InjOn
      (fun address : BlockAddress (fun _c ↦
        PositiveWord (CWCoarseDigit depth) n) ↦ address (sigma .X)) coarseKept) :
    let selected := cwSelectedExactInterfaceTerm K q term hmultiplicity
    let group := cwExactInterfaceCoarseGroup depth n
    let fineAmbient := cwFineSupportOverCoarseSupport selected.support coarseKept
    let hashed := selected.withSupport fineAmbient
    let model := cwExactInterfaceCompatibilityModel depth n partAt
    let xSupport := groupStableSupport hashed.support (fun address ↦
      model.MatchesExact (logicalAddress sigma address) .X targets.xExact)
    let xUseful := hashed.withSupport xSupport
    let yFirst := cwPooledYFirstZeroOut xUseful sigma partAt pooled.yAll
    let compatibleY := OrientedCompatibleY
      (A := fun _c ↦ PositiveWord (PositiveWord CWBlock (2 ^ depth - 1)) n)
      sigma model targets
    let ySupport := groupCompatibilityIsolatedSupport
      yFirst.support group (sigma .Y) compatibleY
    let yIsolated := yFirst.withSupport ySupport
    let yUsefulSupport := groupStableSupport yIsolated.support (fun address ↦
      model.MatchesExact (logicalAddress sigma address) .Y targets.yExact)
    let yUseful := yIsolated.withSupport yUsefulSupport
    let zFirst := cwPooledZFirstZeroOut yUseful sigma partAt pooled.zAll
    let compatibleZ := OrientedCompatibleZ
      (A := fun _c ↦ PositiveWord (PositiveWord CWBlock (2 ^ depth - 1)) n)
      sigma model targets
    let zSupport := groupCompatibilityIsolatedSupport
      zFirst.support group (sigma .Z) compatibleZ
    let zIsolated := zFirst.withSupport zSupport
    let zUsefulSupport := groupStableSupport zIsolated.support (fun address ↦
      model.MatchesExact (logicalAddress sigma address) .Z targets.zExact)
    let zUseful := zIsolated.withSupport zUsefulSupport
    IsProjectionClosed hashed.support zUseful.support Finset.univ := by
  classical
  let selected := cwSelectedExactInterfaceTerm K q term hmultiplicity
  let group := cwExactInterfaceCoarseGroup depth n
  let fineAmbient := cwFineSupportOverCoarseSupport selected.support coarseKept
  let hashed := selected.withSupport fineAmbient
  let model := cwExactInterfaceCompatibilityModel depth n partAt
  let xKeep := fun address : BlockAddress (fun _c ↦
      PositiveWord (PositiveWord CWBlock (2 ^ depth - 1)) n) ↦
    model.MatchesExact (logicalAddress sigma address) .X targets.xExact
  let xSupport := groupStableSupport hashed.support xKeep
  let xUseful := hashed.withSupport xSupport
  let yFirst := cwPooledYFirstZeroOut xUseful sigma partAt pooled.yAll
  let compatibleY := OrientedCompatibleY
    (A := fun _c ↦ PositiveWord (PositiveWord CWBlock (2 ^ depth - 1)) n)
    sigma model targets
  let ySupport := groupCompatibilityIsolatedSupport
    yFirst.support group (sigma .Y) compatibleY
  let yIsolated := yFirst.withSupport ySupport
  let yKeep := fun address : BlockAddress (fun _c ↦
      PositiveWord (PositiveWord CWBlock (2 ^ depth - 1)) n) ↦
    model.MatchesExact (logicalAddress sigma address) .Y targets.yExact
  let yUsefulSupport := groupStableSupport yIsolated.support yKeep
  let yUseful := yIsolated.withSupport yUsefulSupport
  let zFirst := cwPooledZFirstZeroOut yUseful sigma partAt pooled.zAll
  let compatibleZ := OrientedCompatibleZ
    (A := fun _c ↦ PositiveWord (PositiveWord CWBlock (2 ^ depth - 1)) n)
    sigma model targets
  let zSupport := groupCompatibilityIsolatedSupport
    zFirst.support group (sigma .Z) compatibleZ
  let zIsolated := zFirst.withSupport zSupport
  let zKeep := fun address : BlockAddress (fun _c ↦
      PositiveWord (PositiveWord CWBlock (2 ^ depth - 1)) n) ↦
    model.MatchesExact (logicalAddress sigma address) .Z targets.zExact
  let zUsefulSupport := groupStableSupport zIsolated.support zKeep
  let zUseful := zIsolated.withSupport zUsefulSupport

  have hXHashed : HasGroupUniqueLegFibers hashed.support hashed.support
      group (sigma .X) := by
    simpa [hashed, fineAmbient, group] using
      cwFineSupportOverCoarseSupport_hasGroupUniqueLegFibers
        selected.support coarseKept (sigma .X) hcoarseX
  have hxSubset : xSupport ⊆ hashed.support :=
    groupStableSupport_subset hashed.support xKeep
  have hXYFirstSubset : yFirst.support ⊆ xSupport := by
    intro address haddress
    exact (mem_cwPooledYFirstZeroOut_support
      xUseful sigma partAt pooled.yAll address).mp haddress |>.1
  have hYSubset : ySupport ⊆ yFirst.support :=
    groupCompatibilityIsolatedSupport_subset
      yFirst.support group (sigma .Y) compatibleY
  have hYUsefulSubset : yUsefulSupport ⊆ ySupport := by
    change groupStableSupport ySupport yKeep ⊆ ySupport
    exact groupStableSupport_subset ySupport yKeep
  have hZFirstSubset : zFirst.support ⊆ yUsefulSupport := by
    intro address haddress
    exact (mem_cwPooledZFirstZeroOut_support
      yUseful sigma partAt pooled.zAll address).mp haddress |>.1
  have hZSubset : zSupport ⊆ zFirst.support :=
    groupCompatibilityIsolatedSupport_subset
      zFirst.support group (sigma .Z) compatibleZ

  have hYFirstSubsetSelected : yFirst.support ⊆ selected.support := by
    intro address haddress
    have hx := hXYFirstSubset haddress
    have hhash := hxSubset hx
    exact (mem_cwFineSupportOverCoarseSupport
      selected.support coarseKept address).mp hhash |>.1
  have hYProfiles : ∀ address ∈ yFirst.support,
      CWPooledAllYProfileMatches sigma partAt targets pooled address := by
    intro address haddress
    have hfirst := (mem_cwPooledYFirstZeroOut_support
      xUseful sigma partAt pooled.yAll address).mp haddress
    have hxData : address ∈ hashed.support ∧ xKeep address := by
      simpa [xUseful, xSupport, groupStableSupport] using hfirst.1
    refine ⟨hxData.2, ?_⟩
    exact (cw_matchesYPooledAll_iff_labelMatches
      sigma partAt pooled.yAll address).mpr hfirst.2
  have hSoundY : IsCompatibilitySound yFirst.support (sigma .Y) compatibleY := by
    exact cwSelectedExactInterfaceTerm_orientedYCompatibility_sound
      K q partAt term hmultiplicity sigma targets pooled yFirst.support
        hYFirstSubsetSelected hYProfiles
  have hYGroup : HasGroupUniqueLegFibers yFirst.support ySupport
      group (sigma .Y) :=
    groupCompatibilityIsolatedSupport_hasGroupUniqueLegFibers
      yFirst.support group (sigma .Y) compatibleY hSoundY
  have hYGroupSelf : HasGroupUniqueLegFibers ySupport ySupport
      group (sigma .Y) := hYGroup.toSelf

  have hZFirstSubsetSelected : zFirst.support ⊆ selected.support := by
    intro address haddress
    exact hYFirstSubsetSelected
      (hYSubset (hYUsefulSubset (hZFirstSubset haddress)))
  have hZProfiles : ∀ address ∈ zFirst.support,
      CWPooledAllZProfileMatches sigma partAt targets pooled address := by
    intro address haddress
    have hfirst := (mem_cwPooledZFirstZeroOut_support
      yUseful sigma partAt pooled.zAll address).mp haddress
    have hyData : address ∈ ySupport ∧ yKeep address := by
      simpa [yUseful, yUsefulSupport, yIsolated, groupStableSupport] using hfirst.1
    have hyFirstMem := hYSubset hyData.1
    have hyFirstData := (mem_cwPooledYFirstZeroOut_support
      xUseful sigma partAt pooled.yAll address).mp hyFirstMem
    have hxData : address ∈ hashed.support ∧ xKeep address := by
      simpa [xUseful, xSupport, groupStableSupport] using hyFirstData.1
    refine ⟨hxData.2, hyData.2, ?_⟩
    exact (cw_matchesZPooledAll_iff_labelMatches
      sigma partAt pooled.zAll address).mpr hfirst.2
  have hSoundZ : IsCompatibilitySound zFirst.support (sigma .Z) compatibleZ := by
    exact cwSelectedExactInterfaceTerm_orientedZCompatibility_sound
      K q partAt term hmultiplicity sigma targets pooled zFirst.support
        hZFirstSubsetSelected hZProfiles
  have hZGroup : HasGroupUniqueLegFibers zFirst.support zSupport
      group (sigma .Z) :=
    groupCompatibilityIsolatedSupport_hasGroupUniqueLegFibers
      zFirst.support group (sigma .Z) compatibleZ hSoundZ
  have hZGroupSelf : HasGroupUniqueLegFibers zSupport zSupport
      group (sigma .Z) := hZGroup.toSelf

  have hxClosed : IsProjectionClosed hashed.support xSupport {sigma .X} :=
    groupStableSupport_isProjectionClosed hashed.support group (sigma .X) xKeep
      hXHashed (cwMatchesExact_isGroupLabelStable
        partAt sigma hashed.support .X targets.xExact)
  have hyFirstClosed : IsProjectionClosed xUseful.support yFirst.support Finset.univ := by
    simpa [yFirst, cwPooledYFirstZeroOut] using
      (PartitionedTensor.select_support_isProjectionClosed_univ xUseful
        (fun c label ↦ c ≠ sigma .Y ∨
          CWPooledAllLabelMatches partAt pooled.yAll label))
  have hyCompatibilityClosed :
      IsProjectionClosed yFirst.support ySupport {sigma .Y} := by
    exact groupCompatibilityIsolatedSupport_isProjectionClosed
      yFirst.support group (sigma .Y) compatibleY hSoundY
  have hyUsefulClosed :
      IsProjectionClosed yIsolated.support yUsefulSupport {sigma .Y} := by
    simpa [yUsefulSupport, yIsolated] using
      groupStableSupport_isProjectionClosed ySupport group (sigma .Y) yKeep
        hYGroupSelf (cwMatchesExact_isGroupLabelStable
          partAt sigma ySupport .Y targets.yExact)
  have hzFirstClosed : IsProjectionClosed yUseful.support zFirst.support Finset.univ := by
    simpa [zFirst, cwPooledZFirstZeroOut] using
      (PartitionedTensor.select_support_isProjectionClosed_univ yUseful
        (fun c label ↦ c ≠ sigma .Z ∨
          CWPooledAllLabelMatches partAt pooled.zAll label))
  have hzCompatibilityClosed :
      IsProjectionClosed zFirst.support zSupport {sigma .Z} := by
    exact groupCompatibilityIsolatedSupport_isProjectionClosed
      zFirst.support group (sigma .Z) compatibleZ hSoundZ
  have hzUsefulClosed :
      IsProjectionClosed zIsolated.support zUsefulSupport {sigma .Z} := by
    simpa [zUsefulSupport, zIsolated] using
      groupStableSupport_isProjectionClosed zSupport group (sigma .Z) zKeep
        hZGroupSelf (cwMatchesExact_isGroupLabelStable
          partAt sigma zSupport .Z targets.zExact)

  have hthroughYFirst :
      IsProjectionClosed hashed.support yFirst.support Finset.univ := by
    simpa [xUseful] using hxClosed.trans_union hyFirstClosed
  have hthroughYCompatibility :
      IsProjectionClosed hashed.support ySupport Finset.univ := by
    simpa using hthroughYFirst.trans_union hyCompatibilityClosed
  have hthroughYUseful :
      IsProjectionClosed hashed.support yUsefulSupport Finset.univ := by
    simpa [yIsolated] using hthroughYCompatibility.trans_union hyUsefulClosed
  have hthroughZFirst :
      IsProjectionClosed hashed.support zFirst.support Finset.univ := by
    simpa [yUseful] using hthroughYUseful.trans_union hzFirstClosed
  have hthroughZCompatibility :
      IsProjectionClosed hashed.support zSupport Finset.univ := by
    simpa using hthroughZFirst.trans_union hzCompatibilityClosed
  have hthroughZUseful :
      IsProjectionClosed hashed.support zUsefulSupport Finset.univ := by
    simpa [zIsolated] using hthroughZCompatibility.trans_union hzUsefulClosed
  change IsProjectionClosed fineAmbient zUsefulSupport Finset.univ
  exact hthroughZUseful

/-- One oriented hash pass followed by the complete grouped compatibility/profile cleanup.
The output is a genuine indexed direct sum over coarse constituent addresses. -/
theorem cwSelectedExactInterfaceTerm_orientedHashAndGroupedCleanup_to_groupedIndexedDirectSum
    {R : Type v} [Field R] [Fintype R] [NeZero (2 : R)]
    (encoding : CWCoarseFieldEncoding R depth)
    (K : Type u) [CommRing K] (q : ℕ) {Part : Type v} [DecidableEq Part]
    {n : ℕ} (partAt : Fin (n + 1) → Part)
    (term : ExactInterfaceTermParameters depth)
    (hmultiplicity : term.multiplicity = n + 1)
    (sigma : Orientation) (targets : CompatibilityTargets Part depth)
    (pooled : PooledAllTargets targets) (B : Finset R)
    (hB : ThreeAPFree (B : Set R))
    (seed : ProgressionHash.Seed R (Fin (n + 1))) :
    let selected := cwSelectedExactInterfaceTerm K q term hmultiplicity
    let coarseKept := encoding.orientedXIsolatedCoarseSupport
      K q term hmultiplicity sigma B seed
    let fineAmbient := cwFineSupportOverCoarseSupport selected.support coarseKept
    let hashed := selected.withSupport fineAmbient
    let model := cwExactInterfaceCompatibilityModel depth n partAt
    let xSupport := groupStableSupport hashed.support (fun address ↦
      model.MatchesExact (logicalAddress sigma address) .X targets.xExact)
    let xUseful := hashed.withSupport xSupport
    let yFirst := cwPooledYFirstZeroOut xUseful sigma partAt pooled.yAll
    let compatibleY := OrientedCompatibleY
      (A := fun _c ↦ PositiveWord (PositiveWord CWBlock (2 ^ depth - 1)) n)
      sigma model targets
    let ySupport := groupCompatibilityIsolatedSupport yFirst.support
      (cwExactInterfaceCoarseGroup depth n) (sigma .Y) compatibleY
    let yIsolated := yFirst.withSupport ySupport
    let yUsefulSupport := groupStableSupport yIsolated.support (fun address ↦
      model.MatchesExact (logicalAddress sigma address) .Y targets.yExact)
    let yUseful := yIsolated.withSupport yUsefulSupport
    let zFirst := cwPooledZFirstZeroOut yUseful sigma partAt pooled.zAll
    let compatibleZ := OrientedCompatibleZ
      (A := fun _c ↦ PositiveWord (PositiveWord CWBlock (2 ^ depth - 1)) n)
      sigma model targets
    let zSupport := groupCompatibilityIsolatedSupport zFirst.support
      (cwExactInterfaceCoarseGroup depth n) (sigma .Z) compatibleZ
    let zIsolated := zFirst.withSupport zSupport
    let zUsefulSupport := groupStableSupport zIsolated.support (fun address ↦
      model.MatchesExact (logicalAddress sigma address) .Z targets.zExact)
    let zUseful := zIsolated.withSupport zUsefulSupport
    ∃ G : zUseful.LegGrouping
        (BlockAddress (fun _c ↦ PositiveWord (CWCoarseDigit depth) n)),
      Restricts selected.realize
        (Tensor.indexedDirectSum (fun coarse ↦ (G.fiber coarse).realize)) := by
  classical
  let selected := cwSelectedExactInterfaceTerm K q term hmultiplicity
  let coarseKept := encoding.orientedXIsolatedCoarseSupport
    K q term hmultiplicity sigma B seed
  let fineAmbient := cwFineSupportOverCoarseSupport selected.support coarseKept
  let hashed := selected.withSupport fineAmbient
  have hhash : Restricts selected.realize hashed.realize := by
    simpa [selected, coarseKept, fineAmbient, hashed] using
      cwSelectedExactInterfaceTerm_restricts_orientedXIsolatedFine
        encoding K q term hmultiplicity sigma B hB seed
  obtain ⟨G, hcleanup⟩ :=
    cwSelectedExactInterfaceTerm_orientedGroupedCleanup_to_groupedIndexedDirectSum
      K q partAt term hmultiplicity sigma targets pooled coarseKept
        (encoding.orientedX_injectiveOn_orientedXIsolatedCoarseSupport
          K q term hmultiplicity sigma B seed)
  exact ⟨G, hhash.trans hcleanup⟩

/-- Strengthened finite coarse extraction: besides the grouped indexed-direct-sum restriction,
the final cleanup support is certified to be a Cartesian variable deletion from the hash-retained
fine support.  This is the precise semantic input for damaged-box normalization. -/
theorem cwSelectedExactInterfaceTerm_orientedHashAndGroupedCleanup_withProjectionClosure
    {R : Type v} [Field R] [Fintype R] [NeZero (2 : R)]
    (encoding : CWCoarseFieldEncoding R depth)
    (K : Type u) [CommRing K] (q : ℕ) {Part : Type v} [DecidableEq Part]
    {n : ℕ} (partAt : Fin (n + 1) → Part)
    (term : ExactInterfaceTermParameters depth)
    (hmultiplicity : term.multiplicity = n + 1)
    (sigma : Orientation) (targets : CompatibilityTargets Part depth)
    (pooled : PooledAllTargets targets) (B : Finset R)
    (hB : ThreeAPFree (B : Set R))
    (seed : ProgressionHash.Seed R (Fin (n + 1))) :
    let selected := cwSelectedExactInterfaceTerm K q term hmultiplicity
    let coarseKept := encoding.orientedXIsolatedCoarseSupport
      K q term hmultiplicity sigma B seed
    let fineAmbient := cwFineSupportOverCoarseSupport selected.support coarseKept
    let hashed := selected.withSupport fineAmbient
    let model := cwExactInterfaceCompatibilityModel depth n partAt
    let xSupport := groupStableSupport hashed.support (fun address ↦
      model.MatchesExact (logicalAddress sigma address) .X targets.xExact)
    let xUseful := hashed.withSupport xSupport
    let yFirst := cwPooledYFirstZeroOut xUseful sigma partAt pooled.yAll
    let compatibleY := OrientedCompatibleY
      (A := fun _c ↦ PositiveWord (PositiveWord CWBlock (2 ^ depth - 1)) n)
      sigma model targets
    let ySupport := groupCompatibilityIsolatedSupport yFirst.support
      (cwExactInterfaceCoarseGroup depth n) (sigma .Y) compatibleY
    let yIsolated := yFirst.withSupport ySupport
    let yUsefulSupport := groupStableSupport yIsolated.support (fun address ↦
      model.MatchesExact (logicalAddress sigma address) .Y targets.yExact)
    let yUseful := yIsolated.withSupport yUsefulSupport
    let zFirst := cwPooledZFirstZeroOut yUseful sigma partAt pooled.zAll
    let compatibleZ := OrientedCompatibleZ
      (A := fun _c ↦ PositiveWord (PositiveWord CWBlock (2 ^ depth - 1)) n)
      sigma model targets
    let zSupport := groupCompatibilityIsolatedSupport zFirst.support
      (cwExactInterfaceCoarseGroup depth n) (sigma .Z) compatibleZ
    let zIsolated := zFirst.withSupport zSupport
    let zUsefulSupport := groupStableSupport zIsolated.support (fun address ↦
      model.MatchesExact (logicalAddress sigma address) .Z targets.zExact)
    let zUseful := zIsolated.withSupport zUsefulSupport
    ∃ G : zUseful.LegGrouping
        (BlockAddress (fun _c ↦ PositiveWord (CWCoarseDigit depth) n)),
      Restricts selected.realize
          (Tensor.indexedDirectSum (fun coarse ↦ (G.fiber coarse).realize)) ∧
        IsProjectionClosed hashed.support zUseful.support Finset.univ := by
  classical
  let selected := cwSelectedExactInterfaceTerm K q term hmultiplicity
  let coarseKept := encoding.orientedXIsolatedCoarseSupport
    K q term hmultiplicity sigma B seed
  let fineAmbient := cwFineSupportOverCoarseSupport selected.support coarseKept
  let hashed := selected.withSupport fineAmbient
  let model := cwExactInterfaceCompatibilityModel depth n partAt
  let xSupport := groupStableSupport hashed.support (fun address ↦
    model.MatchesExact (logicalAddress sigma address) .X targets.xExact)
  let xUseful := hashed.withSupport xSupport
  let yFirst := cwPooledYFirstZeroOut xUseful sigma partAt pooled.yAll
  let compatibleY := OrientedCompatibleY
    (A := fun _c ↦ PositiveWord (PositiveWord CWBlock (2 ^ depth - 1)) n)
    sigma model targets
  let ySupport := groupCompatibilityIsolatedSupport yFirst.support
    (cwExactInterfaceCoarseGroup depth n) (sigma .Y) compatibleY
  let yIsolated := yFirst.withSupport ySupport
  let yUsefulSupport := groupStableSupport yIsolated.support (fun address ↦
    model.MatchesExact (logicalAddress sigma address) .Y targets.yExact)
  let yUseful := yIsolated.withSupport yUsefulSupport
  let zFirst := cwPooledZFirstZeroOut yUseful sigma partAt pooled.zAll
  let compatibleZ := OrientedCompatibleZ
    (A := fun _c ↦ PositiveWord (PositiveWord CWBlock (2 ^ depth - 1)) n)
    sigma model targets
  let zSupport := groupCompatibilityIsolatedSupport zFirst.support
    (cwExactInterfaceCoarseGroup depth n) (sigma .Z) compatibleZ
  let zIsolated := zFirst.withSupport zSupport
  let zUsefulSupport := groupStableSupport zIsolated.support (fun address ↦
    model.MatchesExact (logicalAddress sigma address) .Z targets.zExact)
  let zUseful := zIsolated.withSupport zUsefulSupport
  obtain ⟨G, hrestrict⟩ :=
    cwSelectedExactInterfaceTerm_orientedHashAndGroupedCleanup_to_groupedIndexedDirectSum
      encoding K q partAt term hmultiplicity sigma targets pooled B hB seed
  have hclosed : IsProjectionClosed hashed.support zUseful.support Finset.univ := by
    simpa [selected, coarseKept, fineAmbient, hashed, model, xSupport, xUseful,
      yFirst, compatibleY, ySupport, yIsolated, yUsefulSupport, yUseful,
      zFirst, compatibleZ, zSupport, zIsolated, zUsefulSupport, zUseful] using
      cwSelectedExactInterfaceTerm_orientedGroupedCleanup_isProjectionClosed
        K q partAt term hmultiplicity sigma targets pooled coarseKept
          (encoding.orientedX_injectiveOn_orientedXIsolatedCoarseSupport
            K q term hmultiplicity sigma B seed)
  exact ⟨G, hrestrict, hclosed⟩

/-- A single finite extraction statement combining the averaging choice of hash seed with the
tensor-level grouped cleanup.  The cardinality inequality counts the isolated coarse constituents
*before* compatibility/profile cleanup; proving that sufficiently many of the returned fibers are
nonzero is the remaining paper-specific competitor/type-count estimate. -/
theorem exists_seed_many_orientedXIsolatedCoarseSupport_and_groupedCleanup
    {R : Type v} [Field R] [Fintype R] [NeZero (2 : R)]
    (encoding : CWCoarseFieldEncoding R depth)
    (K : Type u) [CommRing K] (q : ℕ) {Part : Type v} [DecidableEq Part]
    {n : ℕ} (partAt : Fin (n + 1) → Part)
    (term : ExactInterfaceTermParameters depth)
    (hmultiplicity : term.multiplicity = n + 1)
    (sigma : Orientation) (targets : CompatibilityTargets Part depth)
    (pooled : PooledAllTargets targets) (B : Finset R)
    (hB : ThreeAPFree (B : Set R))
    (hquarter : ∀ triple ∈
      encoding.orientedLegalTargets K q term hmultiplicity sigma,
      4 * (ProgressionHash.LegalTriple.xCompetitorYIndices
        (encoding.orientedLegalTargets K q term hmultiplicity sigma) triple).card ≤
          Fintype.card R) :
    ∃ seed : ProgressionHash.Seed R (Fin (n + 1)),
      3 * (cwCoarsenedSelectedExactInterfaceTerm K q term hmultiplicity).support.card *
          B.card ≤
        4 * (Fintype.card R * Fintype.card R) *
          (encoding.orientedXIsolatedCoarseSupport
            K q term hmultiplicity sigma B seed).card ∧
      (let selected := cwSelectedExactInterfaceTerm K q term hmultiplicity
       let coarseKept := encoding.orientedXIsolatedCoarseSupport
         K q term hmultiplicity sigma B seed
       let fineAmbient := cwFineSupportOverCoarseSupport selected.support coarseKept
       let hashed := selected.withSupport fineAmbient
       let model := cwExactInterfaceCompatibilityModel depth n partAt
       let xSupport := groupStableSupport hashed.support (fun address ↦
         model.MatchesExact (logicalAddress sigma address) .X targets.xExact)
       let xUseful := hashed.withSupport xSupport
       let yFirst := cwPooledYFirstZeroOut xUseful sigma partAt pooled.yAll
       let compatibleY := OrientedCompatibleY
         (A := fun _c ↦ PositiveWord (PositiveWord CWBlock (2 ^ depth - 1)) n)
         sigma model targets
       let ySupport := groupCompatibilityIsolatedSupport yFirst.support
         (cwExactInterfaceCoarseGroup depth n) (sigma .Y) compatibleY
       let yIsolated := yFirst.withSupport ySupport
       let yUsefulSupport := groupStableSupport yIsolated.support (fun address ↦
         model.MatchesExact (logicalAddress sigma address) .Y targets.yExact)
       let yUseful := yIsolated.withSupport yUsefulSupport
       let zFirst := cwPooledZFirstZeroOut yUseful sigma partAt pooled.zAll
       let compatibleZ := OrientedCompatibleZ
         (A := fun _c ↦ PositiveWord (PositiveWord CWBlock (2 ^ depth - 1)) n)
         sigma model targets
       let zSupport := groupCompatibilityIsolatedSupport zFirst.support
         (cwExactInterfaceCoarseGroup depth n) (sigma .Z) compatibleZ
       let zIsolated := zFirst.withSupport zSupport
       let zUsefulSupport := groupStableSupport zIsolated.support (fun address ↦
         model.MatchesExact (logicalAddress sigma address) .Z targets.zExact)
       let zUseful := zIsolated.withSupport zUsefulSupport
       ∃ G : zUseful.LegGrouping
           (BlockAddress (fun _c ↦ PositiveWord (CWCoarseDigit depth) n)),
         Restricts selected.realize
           (Tensor.indexedDirectSum (fun coarse ↦ (G.fiber coarse).realize))) := by
  obtain ⟨seed, hcount, _hsubset, _hinjective⟩ :=
    encoding.exists_seed_many_orientedXIsolatedCoarseSupport
      K q term hmultiplicity sigma B hquarter
  refine ⟨seed, hcount, ?_⟩
  exact cwSelectedExactInterfaceTerm_orientedHashAndGroupedCleanup_to_groupedIndexedDirectSum
    encoding K q partAt term hmultiplicity sigma targets pooled B hB seed

end Examples
end AlgebraicComplexity
