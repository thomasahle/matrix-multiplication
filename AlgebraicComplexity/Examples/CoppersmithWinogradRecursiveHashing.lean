/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinogradCompatibilityCoarseHashing
import AlgebraicComplexity.Examples.CoppersmithWinogradRecursiveCoarsening
import AlgebraicComplexity.Combinatorics.MarkedXHashingExtraction

/-!
# Marked affine hashing for recursive CW child words

This module turns the quotient constructed in
`CoppersmithWinogradRecursiveCoarsening` into the exact ambient/marked pair used by the
recursive constituent theorem.  Ambient targets have the three prescribed `alpha` marginals;
marked targets additionally have joint ordered-left type `alpha`.  Both are represented by the
full labelled left-plus-right child word when hashed.

The definitions are finite and orientation-parametric.  This file does not supply the competitor
degree estimate, compatibility cleanup, or hole repair; those are downstream quantitative
obligations.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor MoreAsymmetryCompatibility

universe u v

/-- One ordered-left coordinate word in logical coordinates. -/
def cwRecursiveLogicalLeftCoordinateWord {depth n : ℕ} (sigma : Orientation)
    (address : CWRecursiveCoarseAddress depth n) (logicalLeg : Leg) :
    Fin (n + 1) → CWRecursiveChildDigit depth :=
  fun sample ↦ address (sigma logicalLeg) (Fin.castAdd (n + 1) sample)

/-- The ordered-left visible triple word in logical coordinates. -/
def cwRecursiveLogicalLeftTripleWord {depth n : ℕ} (sigma : Orientation)
    (address : CWRecursiveCoarseAddress depth n) :
    Fin (n + 1) → ExactRecursiveSplitType.CoordinateTriple (coarseTotal depth) :=
  fun sample ↦
    (cwRecursiveLogicalLeftCoordinateWord sigma address .X sample,
      cwRecursiveLogicalLeftCoordinateWord sigma address .Y sample,
      cwRecursiveLogicalLeftCoordinateWord sigma address .Z sample)

/-- A coarse target is marked exactly when its ordered-left joint type is `alpha`. -/
def CWRecursiveMatchesAlpha
    {depth n : ℕ} {term : ExactInterfaceTermParameters (depth + 1)}
    (sigma : Orientation)
    (alpha : ExactRecursiveSplitType
      (cwRecursiveLogicalParent term sigma) (coarseTotal depth) (n + 1))
    (address : CWRecursiveCoarseAddress depth n) : Prop :=
  WordType.multiplicity (cwRecursiveLogicalLeftTripleWord sigma address) =
    alpha.coordinateTripleCount

noncomputable instance cwRecursiveMatchesAlphaDecidable
    {depth n : ℕ} {term : ExactInterfaceTermParameters (depth + 1)}
    (sigma : Orientation)
    (alpha : ExactRecursiveSplitType
      (cwRecursiveLogicalParent term sigma) (coarseTotal depth) (n + 1))
    (address : CWRecursiveCoarseAddress depth n) :
    Decidable (CWRecursiveMatchesAlpha sigma alpha address) := by
  classical
  unfold CWRecursiveMatchesAlpha
  infer_instance

/-- A marked ordered joint type automatically has each of the three prescribed marginal types.
This is the finite support inclusion behind the ambient/marked distinction in combination-loss
hashing. -/
theorem multiplicity_cwRecursiveLogicalLeftCoordinateWord_eq_marginalCount
    {depth n : ℕ} {term : ExactInterfaceTermParameters (depth + 1)}
    (sigma : Orientation)
    (alpha : ExactRecursiveSplitType
      (cwRecursiveLogicalParent term sigma) (coarseTotal depth) (n + 1))
    (address : CWRecursiveCoarseAddress depth n)
    (hmarked : CWRecursiveMatchesAlpha sigma alpha address)
    (logicalLeg : Leg) :
    WordType.multiplicity
        (cwRecursiveLogicalLeftCoordinateWord sigma address logicalLeg) =
      alpha.marginalCount logicalLeg := by
  unfold CWRecursiveMatchesAlpha at hmarked
  cases logicalLeg with
  | X =>
      calc
        WordType.multiplicity
            (cwRecursiveLogicalLeftCoordinateWord sigma address .X) =
            WordType.multiplicity
              (Prod.fst ∘ cwRecursiveLogicalLeftTripleWord sigma address) := by
                rfl
        _ = WordType.mappedType Prod.fst
              (WordType.multiplicity
                (cwRecursiveLogicalLeftTripleWord sigma address)) :=
              WordType.multiplicity_comp_eq_mappedType _ _
        _ = WordType.mappedType Prod.fst alpha.coordinateTripleCount := by
              rw [hmarked]
        _ = alpha.marginalCount .X :=
              alpha.mappedType_coordinateTripleCount_fst
  | Y =>
      let projectY := fun triple : ExactRecursiveSplitType.CoordinateTriple
          (coarseTotal depth) ↦ triple.2.1
      calc
        WordType.multiplicity
            (cwRecursiveLogicalLeftCoordinateWord sigma address .Y) =
            WordType.multiplicity
              (projectY ∘ cwRecursiveLogicalLeftTripleWord sigma address) := by
                rfl
        _ = WordType.mappedType projectY
              (WordType.multiplicity
                (cwRecursiveLogicalLeftTripleWord sigma address)) :=
              WordType.multiplicity_comp_eq_mappedType _ _
        _ = WordType.mappedType projectY alpha.coordinateTripleCount := by
              rw [hmarked]
        _ = alpha.marginalCount .Y :=
              alpha.mappedType_coordinateTripleCount_snd_fst
  | Z =>
      let projectZ := fun triple : ExactRecursiveSplitType.CoordinateTriple
          (coarseTotal depth) ↦ triple.2.2
      calc
        WordType.multiplicity
            (cwRecursiveLogicalLeftCoordinateWord sigma address .Z) =
            WordType.multiplicity
              (projectZ ∘ cwRecursiveLogicalLeftTripleWord sigma address) := by
                rfl
        _ = WordType.mappedType projectZ
              (WordType.multiplicity
                (cwRecursiveLogicalLeftTripleWord sigma address)) :=
              WordType.multiplicity_comp_eq_mappedType _ _
        _ = WordType.mappedType projectZ alpha.coordinateTripleCount := by
              rw [hmarked]
        _ = alpha.marginalCount .Z :=
              alpha.mappedType_coordinateTripleCount_snd_snd

/-- On an actual fine CW address, the visible logical coordinate triples of the coarsened
ordered-left word are exactly the three-coordinate observations of the intrinsic ordered child
shapes.  In particular, the marked joint-type predicate describes the paper's split variable,
not an unrelated quotient statistic. -/
theorem cwRecursiveLogicalLeftTripleWord_coarsenBlockAddress
    (K : Type u) [CommRing K] (q : ℕ) {depth n : ℕ}
    (term : ExactInterfaceTermParameters (depth + 1))
    (hmultiplicity : term.multiplicity = n + 1)
    (sigma : Orientation)
    (fine : BlockAddress (fun _c ↦
      PositiveWord (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n))
    (hfine : fine ∈
      (cwSelectedExactInterfaceTerm K q term hmultiplicity).support) :
    cwRecursiveLogicalLeftTripleWord sigma
        (coarsenBlockAddress (cwRecursiveChildCoarsening depth n) fine) =
      ExactRecursiveSplitType.coordinateTriple ∘
        cwRecursiveOrientedLeftChildShapeWord
          K q PUnit.unit term hmultiplicity sigma fine hfine := by
  let partAt : Fin (n + 1) → (PUnit : Type) := fun _ ↦ PUnit.unit
  have hcoordinate (logicalLeg : Leg) (sample : Fin (n + 1)) :
      cwRecursiveLogicalLeftCoordinateWord sigma
          (coarsenBlockAddress (cwRecursiveChildCoarsening depth n) fine)
          logicalLeg sample =
        ExactRecursiveSplitType.coordinate logicalLeg
          (cwRecursiveOrientedLeftChildShapeWord
            K q PUnit.unit term hmultiplicity sigma fine hfine sample) := by
    apply Fin.ext
    change
      (cwRecursiveLogicalLeftCoordinateWord sigma
          (coarsenBlockAddress (cwRecursiveChildCoarsening depth n) fine)
          logicalLeg sample : ℕ) =
        (cwRecursiveOrientedLeftChildShapeWord
          K q PUnit.unit term hmultiplicity sigma fine hfine sample).get logicalLeg
    have hword := congrArg Fin.val <| congrFun
      (cwRecursiveLabelledChildWord_eq_model_get
        depth n partAt (logicalAddress sigma fine) logicalLeg)
      (Fin.castAdd (n + 1) sample)
    have hword' :
        (cwRecursiveLogicalLeftCoordinateWord sigma
          (coarsenBlockAddress (cwRecursiveChildCoarsening depth n) fine)
          logicalLeg sample : ℕ) =
        ((recursiveChildCompatibilityModel
            (fun _c ↦ cwChunkSplitWord (depth + 1))
            (fun _ : Fin (n + 1) ↦ PUnit.unit)).coarse
          (logicalAddress sigma fine) (Fin.castAdd (n + 1) sample)).get logicalLeg := by
      simpa only [cwRecursiveLogicalLeftCoordinateWord, coarsenBlockAddress_apply,
        cwRecursiveChildCoarsening, logicalAddress_apply, partAt,
        cwRecursiveChildCompatibilityModel] using hword
    have hshapeIndex := recursiveLeftChildShape_toCoarseIndex
      (fun _c ↦ cwChunkSplitWord (depth + 1)) PUnit.unit
      (logicalAddress sigma fine) (cwRecursiveLogicalParent term sigma)
      (cwRecursive_parentWeight_logicalAddress_of_mem_selected_support
        K q term hmultiplicity sigma fine hfine)
      (cwRecursive_isParentFineLegal_logicalAddress_of_mem_selected_support
        K q term hmultiplicity sigma fine hfine) sample
    have hshape := congrArg (fun index ↦ index.get logicalLeg) hshapeIndex
    have hshape' :
        (cwRecursiveOrientedLeftChildShapeWord
          K q PUnit.unit term hmultiplicity sigma fine hfine sample).get logicalLeg =
        ((recursiveChildCompatibilityModel
            (fun _c ↦ cwChunkSplitWord (depth + 1))
            (fun _ : Fin (n + 1) ↦ PUnit.unit)).coarse
          (logicalAddress sigma fine) (Fin.castAdd (n + 1) sample)).get logicalLeg := by
      simpa only [cwRecursiveOrientedLeftChildShapeWord,
        RecursiveChildShape.toCoarseIndex_get] using hshape
    exact hword'.trans hshape'.symm
  funext sample
  apply Prod.ext
  · exact hcoordinate .X sample
  · apply Prod.ext
    · exact hcoordinate .Y sample
    · exact hcoordinate .Z sample

/-- For a supported fine address, the coarse marked predicate is equivalent to the exact
ordered child-shape type used by the recursive compatibility model. -/
theorem cwRecursiveMatchesAlpha_coarsenBlockAddress_iff
    (K : Type u) [CommRing K] (q : ℕ) {depth n : ℕ}
    (term : ExactInterfaceTermParameters (depth + 1))
    (hmultiplicity : term.multiplicity = n + 1)
    (sigma : Orientation)
    (alpha : ExactRecursiveSplitType
      (cwRecursiveLogicalParent term sigma) (coarseTotal depth) (n + 1))
    (fine : BlockAddress (fun _c ↦
      PositiveWord (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n))
    (hfine : fine ∈
      (cwSelectedExactInterfaceTerm K q term hmultiplicity).support) :
    CWRecursiveMatchesAlpha sigma alpha
        (coarsenBlockAddress (cwRecursiveChildCoarsening depth n) fine) ↔
      CWRecursiveOrientedMatchesLeftChildType
        K q PUnit.unit term hmultiplicity sigma fine hfine alpha := by
  unfold CWRecursiveMatchesAlpha CWRecursiveOrientedMatchesLeftChildType
  rw [cwRecursiveLogicalLeftTripleWord_coarsenBlockAddress
      K q term hmultiplicity sigma fine hfine,
    alpha.multiplicity_coordinateTriple_comp_eq_coordinateTripleCount_iff]

/-- Marked coarse support inside the complete three-marginal ambient quotient. -/
noncomputable def cwRecursiveMarkedCoarseSupport
    (K : Type u) [CommRing K] (q : ℕ) {depth n : ℕ}
    (term : ExactInterfaceTermParameters (depth + 1))
    (hmultiplicity : term.multiplicity = n + 1)
    (sigma : Orientation)
    (alpha : ExactRecursiveSplitType
      (cwRecursiveLogicalParent term sigma) (coarseTotal depth) (n + 1)) :
    Finset (CWRecursiveCoarseAddress depth n) := by
  classical
  exact (cwRecursiveCoarsenedAlphaMarginalTerm
    K q term hmultiplicity sigma alpha).support.filter
      (CWRecursiveMatchesAlpha sigma alpha)

@[simp] theorem mem_cwRecursiveMarkedCoarseSupport
    (K : Type u) [CommRing K] (q : ℕ) {depth n : ℕ}
    (term : ExactInterfaceTermParameters (depth + 1))
    (hmultiplicity : term.multiplicity = n + 1)
    (sigma : Orientation)
    (alpha : ExactRecursiveSplitType
      (cwRecursiveLogicalParent term sigma) (coarseTotal depth) (n + 1))
    (address : CWRecursiveCoarseAddress depth n) :
    address ∈ cwRecursiveMarkedCoarseSupport
        K q term hmultiplicity sigma alpha ↔
      address ∈ (cwRecursiveCoarsenedAlphaMarginalTerm
          K q term hmultiplicity sigma alpha).support ∧
        WordType.multiplicity (cwRecursiveLogicalLeftTripleWord sigma address) =
          alpha.coordinateTripleCount := by
  classical
  simp [cwRecursiveMarkedCoarseSupport, CWRecursiveMatchesAlpha]

/-- Fine-lift characterization of the marked recursive quotient.  The witness is a member of the
actual three-marginal selected tensor, and its additional condition is exactly the ordered joint
split type `alpha`.  Thus no assembled degeneration is hidden in the definition of the marked
family. -/
theorem mem_cwRecursiveMarkedCoarseSupport_iff_exists_fine
    (K : Type u) [CommRing K] (q : ℕ) {depth n : ℕ}
    (term : ExactInterfaceTermParameters (depth + 1))
    (hmultiplicity : term.multiplicity = n + 1)
    (sigma : Orientation)
    (alpha : ExactRecursiveSplitType
      (cwRecursiveLogicalParent term sigma) (coarseTotal depth) (n + 1))
    (address : CWRecursiveCoarseAddress depth n) :
    address ∈ cwRecursiveMarkedCoarseSupport
        K q term hmultiplicity sigma alpha ↔
      ∃ fine : BlockAddress (fun _c ↦
          PositiveWord (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n),
        ∃ hfine : fine ∈ (cwRecursiveAlphaMarginalSelectedTerm
            K q term hmultiplicity sigma alpha).support,
        coarsenBlockAddress (cwRecursiveChildCoarsening depth n) fine = address ∧
        CWRecursiveOrientedMatchesLeftChildType K q PUnit.unit term hmultiplicity sigma
          fine
          ((mem_cwRecursiveAlphaMarginalSelectedTerm_support
            K q term hmultiplicity sigma alpha fine).mp hfine).1
          alpha := by
  classical
  rw [mem_cwRecursiveMarkedCoarseSupport]
  constructor
  · rintro ⟨hcoarse, hmarked⟩
    change address ∈
      ((cwRecursiveAlphaMarginalSelectedTerm
        K q term hmultiplicity sigma alpha).coarsen
          (cwRecursiveChildCoarsening depth n)).support at hcoarse
    rw [PartitionedTensor.coarsen_support, Finset.mem_image] at hcoarse
    obtain ⟨fine, hfine, hgroup⟩ := hcoarse
    let hselected :=
      ((mem_cwRecursiveAlphaMarginalSelectedTerm_support
        K q term hmultiplicity sigma alpha fine).mp hfine).1
    refine ⟨fine, hfine, hgroup, ?_⟩
    apply (cwRecursiveMatchesAlpha_coarsenBlockAddress_iff
      K q term hmultiplicity sigma alpha fine hselected).mp
    unfold CWRecursiveMatchesAlpha
    rw [hgroup]
    exact hmarked
  · rintro ⟨fine, hfine, hgroup, htype⟩
    constructor
    · change address ∈
        ((cwRecursiveAlphaMarginalSelectedTerm
          K q term hmultiplicity sigma alpha).coarsen
            (cwRecursiveChildCoarsening depth n)).support
      rw [PartitionedTensor.coarsen_support, Finset.mem_image]
      exact ⟨fine, hfine, hgroup⟩
    · have hselected :=
        ((mem_cwRecursiveAlphaMarginalSelectedTerm_support
          K q term hmultiplicity sigma alpha fine).mp hfine).1
      have hmarked := (cwRecursiveMatchesAlpha_coarsenBlockAddress_iff
        K q term hmultiplicity sigma alpha fine hselected).mpr htype
      unfold CWRecursiveMatchesAlpha at hmarked
      rw [← hgroup]
      exact hmarked

/-- Every marked recursive quotient block has a fine lift whose complete labelled child-shape
word realizes the exact occurrence law `alpha(u) + alpha(s-u)`.  The result is an existence
statement about the actual selected tensor support, not an abstract word-count surrogate. -/
theorem exists_fine_with_occurrenceCount_of_mem_cwRecursiveMarkedCoarseSupport
    (K : Type u) [CommRing K] (q : ℕ) {depth n : ℕ}
    (term : ExactInterfaceTermParameters (depth + 1))
    (hmultiplicity : term.multiplicity = n + 1)
    (sigma : Orientation)
    (alpha : ExactRecursiveSplitType
      (cwRecursiveLogicalParent term sigma) (coarseTotal depth) (n + 1))
    (address : CWRecursiveCoarseAddress depth n)
    (haddress : address ∈ cwRecursiveMarkedCoarseSupport
      K q term hmultiplicity sigma alpha) :
    ∃ fine : BlockAddress (fun _c ↦
        PositiveWord (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n),
      ∃ hfine : fine ∈ (cwRecursiveAlphaMarginalSelectedTerm
          K q term hmultiplicity sigma alpha).support,
      coarsenBlockAddress (cwRecursiveChildCoarsening depth n) fine = address ∧
      WordType.multiplicity
          (cwRecursiveOrientedChildShapeWord K q PUnit.unit term hmultiplicity sigma fine
            ((mem_cwRecursiveAlphaMarginalSelectedTerm_support
              K q term hmultiplicity sigma alpha fine).mp hfine).1) =
        alpha.occurrenceCount (cwRecursiveLogicalParent_total term sigma) := by
  obtain ⟨fine, hfine, hgroup, htype⟩ :=
    (mem_cwRecursiveMarkedCoarseSupport_iff_exists_fine
      K q term hmultiplicity sigma alpha address).mp haddress
  refine ⟨fine, hfine, hgroup, ?_⟩
  exact multiplicity_cwRecursiveOrientedChildShapeWord_eq_occurrenceCount
    K q PUnit.unit term hmultiplicity sigma fine
      ((mem_cwRecursiveAlphaMarginalSelectedTerm_support
        K q term hmultiplicity sigma alpha fine).mp hfine).1
      alpha htype

/-- Every supported child quotient obeys the coordinatewise tight-support equation at every
labelled occurrence. -/
theorem cwRecursiveCoarsenedAlphaMarginalTerm_coarse_sum
    (K : Type u) [CommRing K] (q : ℕ) {depth n : ℕ}
    (term : ExactInterfaceTermParameters (depth + 1))
    (hmultiplicity : term.multiplicity = n + 1)
    (sigma : Orientation)
    (alpha : ExactRecursiveSplitType
      (cwRecursiveLogicalParent term sigma) (coarseTotal depth) (n + 1))
    (address : CWRecursiveCoarseAddress depth n)
    (haddress : address ∈
      (cwRecursiveCoarsenedAlphaMarginalTerm
        K q term hmultiplicity sigma alpha).support)
    (occurrence : Fin ((n + 1) + (n + 1))) :
    (address .X occurrence : ℕ) + (address .Y occurrence : ℕ) +
        (address .Z occurrence : ℕ) = coarseTotal depth := by
  classical
  change address ∈
    ((cwRecursiveAlphaMarginalSelectedTerm
      K q term hmultiplicity sigma alpha).coarsen
        (cwRecursiveChildCoarsening depth n)).support at haddress
  rw [PartitionedTensor.coarsen_support, Finset.mem_image] at haddress
  obtain ⟨fine, hfine, hcoarse⟩ := haddress
  have hparent : fine ∈
      (cwSelectedExactInterfaceTerm K q term hmultiplicity).support :=
    (mem_cwRecursiveAlphaMarginalSelectedTerm_support
      K q term hmultiplicity sigma alpha fine).mp hfine |>.1
  let partAt : Fin (n + 1) → (PUnit : Type) := fun _ ↦ PUnit.unit
  let model := cwRecursiveChildCompatibilityModel depth n partAt
  have hlegal : model.IsFineLegal fine :=
    cwRecursiveChildCompatibilityModel_isFineLegal_of_mem_selected_support
      K q partAt term hmultiplicity fine hparent
  have hweights : model.HasCoarseWeights fine :=
    recursiveChildCompatibilityModel_hasCoarseWeights
      (fun _c ↦ cwChunkSplitWord (depth + 1)) partAt fine
  have hsum := model.coarse_sum_eq_coarseTotal fine hlegal hweights occurrence
  have hgroup (c : Leg) :
      address c occurrence =
        cwRecursiveLabelledChildWord depth n (fine c) occurrence := by
    rw [← hcoarse]
    rfl
  have hmodel (c : Leg) :
      (address c occurrence : ℕ) = (model.coarse fine occurrence).get c := by
    rw [hgroup c]
    exact congrArg Fin.val <|
      congrFun (cwRecursiveLabelledChildWord_eq_model_get
        depth n partAt fine c) occurrence
  calc
    (address .X occurrence : ℕ) + (address .Y occurrence : ℕ) +
        (address .Z occurrence : ℕ) =
      (model.coarse fine occurrence).get .X +
        (model.coarse fine occurrence).get .Y +
        (model.coarse fine occurrence).get .Z := by
          rw [hmodel .X, hmodel .Y, hmodel .Z]
    _ = (model.coarse fine occurrence).x +
        (model.coarse fine occurrence).y +
        (model.coarse fine occurrence).z := rfl
    _ = coarseTotal depth := hsum

namespace CWCoarseFieldEncoding

variable {R : Type v} [Field R]

/-- One supported recursive quotient address, bundled as a legal affine-hashing triple in an
arbitrary logical orientation. -/
def recursiveOrientedLegalTriple
    (encoding : CWCoarseFieldEncoding R depth)
    (K : Type u) [CommRing K] (q : ℕ) {n : ℕ}
    (term : ExactInterfaceTermParameters (depth + 1))
    (hmultiplicity : term.multiplicity = n + 1)
    (sigma : Orientation)
    (alpha : ExactRecursiveSplitType
      (cwRecursiveLogicalParent term sigma) (coarseTotal depth) (n + 1))
    (source : {address : CWRecursiveCoarseAddress depth n //
      address ∈ (cwRecursiveCoarsenedAlphaMarginalTerm
        K q term hmultiplicity sigma alpha).support}) :
    ProgressionHash.LegalTriple R (Fin ((n + 1) + (n + 1))) encoding.target where
  xIndex occurrence := encoding.encode (source.1 (sigma .X) occurrence)
  yIndex occurrence := encoding.encode (source.1 (sigma .Y) occurrence)
  zIndex occurrence := encoding.encode (source.1 (sigma .Z) occurrence)
  legal occurrence := by
    apply encoding.legal_of_val_sum
    have hsum := cwRecursiveCoarsenedAlphaMarginalTerm_coarse_sum
      K q term hmultiplicity sigma alpha source.1 source.2 occurrence
    have hperm :
        (∑ c : Leg, (source.1 (sigma c) occurrence : ℕ)) =
          ∑ c : Leg, (source.1 c occurrence : ℕ) :=
      Equiv.sum_comp sigma fun c : Leg ↦ (source.1 c occurrence : ℕ)
    calc
      (source.1 (sigma .X) occurrence : ℕ) +
          (source.1 (sigma .Y) occurrence : ℕ) +
          (source.1 (sigma .Z) occurrence : ℕ) =
        ∑ c : Leg, (source.1 (sigma c) occurrence : ℕ) := by
          simp [Tensor.sum_leg]
      _ = ∑ c : Leg, (source.1 c occurrence : ℕ) := hperm
      _ = coarseTotal depth := by simpa [Tensor.sum_leg] using hsum

/-- The legal triple remembers the complete recursive coarse address. -/
theorem recursiveOrientedLegalTriple_injective
    (encoding : CWCoarseFieldEncoding R depth)
    (K : Type u) [CommRing K] (q : ℕ) {n : ℕ}
    (term : ExactInterfaceTermParameters (depth + 1))
    (hmultiplicity : term.multiplicity = n + 1)
    (sigma : Orientation)
    (alpha : ExactRecursiveSplitType
      (cwRecursiveLogicalParent term sigma) (coarseTotal depth) (n + 1)) :
    Function.Injective
      (encoding.recursiveOrientedLegalTriple
        K q term hmultiplicity sigma alpha) := by
  intro left right heq
  apply Subtype.ext
  funext physicalLeg occurrence
  generalize hlogical : sigma.symm physicalLeg = logicalLeg
  have hphysical : sigma logicalLeg = physicalLeg := by
    rw [← hlogical]
    exact sigma.apply_symm_apply physicalLeg
  apply encoding.encode_injective
  cases logicalLeg with
  | X =>
      rw [← hphysical]
      simpa [recursiveOrientedLegalTriple] using
        congrFun (congrArg ProgressionHash.LegalTriple.xIndex heq) occurrence
  | Y =>
      rw [← hphysical]
      simpa [recursiveOrientedLegalTriple] using
        congrFun (congrArg ProgressionHash.LegalTriple.yIndex heq) occurrence
  | Z =>
      rw [← hphysical]
      simpa [recursiveOrientedLegalTriple] using
        congrFun (congrArg ProgressionHash.LegalTriple.zIndex heq) occurrence

/-- Complete three-marginal ambient hashing family. -/
noncomputable def recursiveAmbientTargets
    (encoding : CWCoarseFieldEncoding R depth)
    (K : Type u) [CommRing K] (q : ℕ) {n : ℕ}
    (term : ExactInterfaceTermParameters (depth + 1))
    (hmultiplicity : term.multiplicity = n + 1)
    (sigma : Orientation)
    (alpha : ExactRecursiveSplitType
      (cwRecursiveLogicalParent term sigma) (coarseTotal depth) (n + 1)) :
    Finset (ProgressionHash.LegalTriple R
      (Fin ((n + 1) + (n + 1))) encoding.target) := by
  classical
  exact Finset.univ.image
    (encoding.recursiveOrientedLegalTriple
      K q term hmultiplicity sigma alpha)

/-- Marked `alpha` joint-type hashing family, isolated against the whole ambient marginal
fiber. -/
noncomputable def recursiveMarkedTargets
    (encoding : CWCoarseFieldEncoding R depth)
    (K : Type u) [CommRing K] (q : ℕ) {n : ℕ}
    (term : ExactInterfaceTermParameters (depth + 1))
    (hmultiplicity : term.multiplicity = n + 1)
    (sigma : Orientation)
    (alpha : ExactRecursiveSplitType
      (cwRecursiveLogicalParent term sigma) (coarseTotal depth) (n + 1)) :
    Finset (ProgressionHash.LegalTriple R
      (Fin ((n + 1) + (n + 1))) encoding.target) := by
  classical
  exact (Finset.univ.filter fun source : {address : CWRecursiveCoarseAddress depth n //
      address ∈ (cwRecursiveCoarsenedAlphaMarginalTerm
        K q term hmultiplicity sigma alpha).support} ↦
    CWRecursiveMatchesAlpha sigma alpha source.1).image
      (encoding.recursiveOrientedLegalTriple
        K q term hmultiplicity sigma alpha)

/-- Every marked recursive target is an ambient target. -/
theorem recursiveMarkedTargets_subset_ambientTargets
    (encoding : CWCoarseFieldEncoding R depth)
    (K : Type u) [CommRing K] (q : ℕ) {n : ℕ}
    (term : ExactInterfaceTermParameters (depth + 1))
    (hmultiplicity : term.multiplicity = n + 1)
    (sigma : Orientation)
    (alpha : ExactRecursiveSplitType
      (cwRecursiveLogicalParent term sigma) (coarseTotal depth) (n + 1)) :
    encoding.recursiveMarkedTargets K q term hmultiplicity sigma alpha ⊆
      encoding.recursiveAmbientTargets K q term hmultiplicity sigma alpha := by
  classical
  intro triple htriple
  rw [recursiveMarkedTargets, Finset.mem_image] at htriple
  obtain ⟨source, _hsource, rfl⟩ := htriple
  unfold recursiveAmbientTargets
  exact Finset.mem_image.mpr ⟨source, Finset.mem_univ _, rfl⟩

end CWCoarseFieldEncoding

end AlgebraicComplexity.Examples
