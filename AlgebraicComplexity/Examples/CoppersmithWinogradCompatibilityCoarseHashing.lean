/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinogradCompatibility
import AlgebraicComplexity.Examples.CoppersmithWinogradTotalWeightCore
import AlgebraicComplexity.Combinatorics.HashingExtraction
import AlgebraicComplexity.Tensor.PartitionedCoarsening

/-!
# Coarse hashing for selected Coppersmith--Winograd interface terms

The hashing step in the recursive CW construction acts on the coarse weight words, not on the
underlying complete-split chunk words.  This module makes that boundary explicit.  It first
coarsens a selected exact interface term by the total weight of every chunk, and only then turns
its support into legal triples for the affine hashing theorem.

In particular, the isolation theorem below proves injectivity of the retained **coarse** `X`
labels.  It deliberately does not assert injectivity of the fine complete-split labels inside a
coarse constituent.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor MoreAsymmetryCompatibility

universe u v w

/-- Forget a fine chunk except for its total weight. -/
def cwChunkCoarseDigit (depth : ℕ)
    (chunk : PositiveWord CWBlock (2 ^ depth - 1)) : CWCoarseDigit depth :=
  ⟨splitWordWeight (cwChunkSplitWord depth chunk),
    Nat.lt_succ_iff.mpr (splitWordWeight_le_coarseTotal depth _)⟩

@[simp] theorem cwChunkCoarseDigit_val (depth : ℕ)
    (chunk : PositiveWord CWBlock (2 ^ depth - 1)) :
    (cwChunkCoarseDigit depth chunk : ℕ) =
      splitWordWeight (cwChunkSplitWord depth chunk) :=
  rfl

/-- Coarsen every sample of one outer interface word independently. -/
def cwOuterCoarseWord (depth n : ℕ)
    (word : PositiveWord (PositiveWord CWBlock (2 ^ depth - 1)) n) :
    PositiveWord (CWCoarseDigit depth) n :=
  positiveWordMap (cwChunkCoarseDigit depth) n word

@[simp] theorem positiveWordEquiv_cwOuterCoarseWord (depth n : ℕ)
    (word : PositiveWord (PositiveWord CWBlock (2 ^ depth - 1)) n) :
    positiveWordEquiv (CWCoarseDigit depth) n (cwOuterCoarseWord depth n word) =
      cwChunkCoarseDigit depth ∘
        positiveWordEquiv (PositiveWord CWBlock (2 ^ depth - 1)) n word := by
  exact positiveWordEquiv_map (cwChunkCoarseDigit depth) n word

/-- Legwise coarse-weight map used to regroup an exact interface term. -/
def cwExactInterfaceCoarsening (depth n : ℕ) :
    ∀ _c : Leg,
      PositiveWord (PositiveWord CWBlock (2 ^ depth - 1)) n →
        PositiveWord (CWCoarseDigit depth) n :=
  fun _c ↦ cwOuterCoarseWord depth n

/-- The selected exact interface term, regrouped by its three coarse weight words. -/
noncomputable def cwCoarsenedSelectedExactInterfaceTerm
    (K : Type u) [CommRing K] (q : ℕ) {depth n : ℕ}
    (term : ExactInterfaceTermParameters depth)
    (hmultiplicity : term.multiplicity = n + 1) :=
  (cwSelectedExactInterfaceTerm K q term hmultiplicity).coarsen
    (cwExactInterfaceCoarsening depth n)

/-- Every address in the coarsened selected support obeys the paper's coordinatewise equation
`I_t + J_t + K_t = 2^(depth+1)`. -/
theorem cwCoarsenedSelectedExactInterfaceTerm_coarse_sum
    (K : Type u) [CommRing K] (q : ℕ) {depth n : ℕ}
    (term : ExactInterfaceTermParameters depth)
    (hmultiplicity : term.multiplicity = n + 1)
    (address : BlockAddress (fun _c ↦ PositiveWord (CWCoarseDigit depth) n))
    (haddress : address ∈
      (cwCoarsenedSelectedExactInterfaceTerm K q term hmultiplicity).support)
    (sample : Fin (n + 1)) :
    (positiveWordEquiv (CWCoarseDigit depth) n (address .X) sample : ℕ) +
        (positiveWordEquiv (CWCoarseDigit depth) n (address .Y) sample : ℕ) +
        (positiveWordEquiv (CWCoarseDigit depth) n (address .Z) sample : ℕ) =
      coarseTotal depth := by
  classical
  change address ∈
    ((cwSelectedExactInterfaceTerm K q term hmultiplicity).coarsen
      (cwExactInterfaceCoarsening depth n)).support at haddress
  rw [PartitionedTensor.coarsen_support, Finset.mem_image] at haddress
  obtain ⟨fine, hfine, hcoarse⟩ := haddress
  rw [← hcoarse]
  let partAt : Fin (n + 1) → Unit := fun _ ↦ ()
  let model := cwExactInterfaceCompatibilityModel depth n partAt
  have hlegal : model.IsFineLegal fine :=
    cwExactInterfaceCompatibilityModel_isFineLegal_of_mem_selected_support
      K q partAt term hmultiplicity fine hfine
  have hweights : model.HasCoarseWeights fine :=
    cwExactInterfaceCompatibilityModel_hasCoarseWeights depth n partAt fine
  have hsum := model.coarse_sum_eq_coarseTotal fine hlegal hweights sample
  simpa [coarsenBlockAddress, cwExactInterfaceCoarsening, cwOuterCoarseWord,
    positiveWordEquiv_map, Function.comp_apply, model, partAt,
    cwExactInterfaceCompatibilityModel, encodedPositiveWordCompatibilityModel] using hsum

/-! ## Affine hashing of the coarsened support -/

/-- A field realization of the bounded integer coarse digits.  The last field says exactly what
is needed to transport the integer equation `i+j+k=coarseTotal` into the fixed-sum equation used
by affine hashing.  Concrete prime-field clients may take `encode i = i` once the characteristic
is large enough. -/
structure CWCoarseFieldEncoding (R : Type v) [Field R] (depth : ℕ) where
  encode : CWCoarseDigit depth → R
  target : R
  encode_injective : Function.Injective encode
  legal_of_val_sum : ∀ (x y z : CWCoarseDigit depth),
    (x : ℕ) + (y : ℕ) + (z : ℕ) = coarseTotal depth →
      encode x + encode y + encode z = target

/-- Canonical coarse encoding by natural-number casts in any field whose characteristic is
larger than the largest coarse digit. -/
def cwNatCastCoarseFieldEncoding {R : Type v} [Field R] {p : ℕ} [CharP R p]
    (depth : ℕ) (hcharacteristic : coarseTotal depth < p) :
    CWCoarseFieldEncoding R depth where
  encode digit := (digit.val : R)
  target := (coarseTotal depth : R)
  encode_injective := by
    intro left right heq
    apply Fin.ext
    apply CharP.natCast_injOn_Iio (R := R) p
    · exact (Nat.lt_succ_iff.mp left.isLt).trans_lt hcharacteristic
    · exact (Nat.lt_succ_iff.mp right.isLt).trans_lt hcharacteristic
    · exact heq
  legal_of_val_sum := by
    intro x y z hsum
    have hcast := congrArg (fun m : ℕ ↦ (m : R)) hsum
    simpa only [Nat.cast_add] using hcast

namespace CWCoarseFieldEncoding

variable {R : Type v} [Field R]

/-- One coarsened supported address, bundled as a legal affine-hashing triple. -/
def legalTriple (encoding : CWCoarseFieldEncoding R depth)
    (K : Type u) [CommRing K] (q : ℕ) {n : ℕ}
    (term : ExactInterfaceTermParameters depth)
    (hmultiplicity : term.multiplicity = n + 1)
    (source : {address : BlockAddress (fun _c ↦ PositiveWord (CWCoarseDigit depth) n) //
      address ∈ (cwCoarsenedSelectedExactInterfaceTerm K q term hmultiplicity).support}) :
    ProgressionHash.LegalTriple R (Fin (n + 1)) encoding.target where
  xIndex sample := encoding.encode
    (positiveWordEquiv (CWCoarseDigit depth) n (source.1 .X) sample)
  yIndex sample := encoding.encode
    (positiveWordEquiv (CWCoarseDigit depth) n (source.1 .Y) sample)
  zIndex sample := encoding.encode
    (positiveWordEquiv (CWCoarseDigit depth) n (source.1 .Z) sample)
  legal sample := encoding.legal_of_val_sum _ _ _
    (cwCoarsenedSelectedExactInterfaceTerm_coarse_sum
      K q term hmultiplicity source.1 source.2 sample)

/-- Coarse supported addresses have distinct bundled hashing triples.  This is injectivity only
at the coarsened block level; it makes no claim about fine addresses in a coarsening fiber. -/
theorem legalTriple_injective (encoding : CWCoarseFieldEncoding R depth)
    (K : Type u) [CommRing K] (q : ℕ) {n : ℕ}
    (term : ExactInterfaceTermParameters depth)
    (hmultiplicity : term.multiplicity = n + 1) :
    Function.Injective (encoding.legalTriple K q term hmultiplicity) := by
  intro left right heq
  apply Subtype.ext
  funext c
  apply (positiveWordEquiv (CWCoarseDigit depth) n).injective
  funext sample
  apply encoding.encode_injective
  cases c with
  | X => exact congrFun (congrArg ProgressionHash.LegalTriple.xIndex heq) sample
  | Y => exact congrFun (congrArg ProgressionHash.LegalTriple.yIndex heq) sample
  | Z => exact congrFun (congrArg ProgressionHash.LegalTriple.zIndex heq) sample

/-- The finite target family obtained by bundling the entire coarsened selected support. -/
noncomputable def legalTargets (encoding : CWCoarseFieldEncoding R depth)
    (K : Type u) [CommRing K] (q : ℕ) {n : ℕ}
    (term : ExactInterfaceTermParameters depth)
    (hmultiplicity : term.multiplicity = n + 1) :
    Finset (ProgressionHash.LegalTriple R (Fin (n + 1)) encoding.target) := by
  classical
  exact Finset.univ.image (encoding.legalTriple K q term hmultiplicity)

/-- Bundling the coarsened support as legal hashing triples preserves its cardinality exactly. -/
@[simp] theorem card_legalTargets (encoding : CWCoarseFieldEncoding R depth)
    (K : Type u) [CommRing K] (q : ℕ) {n : ℕ}
    (term : ExactInterfaceTermParameters depth)
    (hmultiplicity : term.multiplicity = n + 1) :
    (encoding.legalTargets K q term hmultiplicity).card =
      (cwCoarsenedSelectedExactInterfaceTerm K q term hmultiplicity).support.card := by
  classical
  unfold legalTargets
  rw [Finset.card_image_of_injOn
    (encoding.legalTriple_injective K q term hmultiplicity).injOn]
  simp

/-- Coarse supported sources whose bundled triples survive complete `X`-fiber isolation. -/
noncomputable def xIsolatedSources (encoding : CWCoarseFieldEncoding R depth)
    (K : Type u) [CommRing K] (q : ℕ) {n : ℕ}
    (term : ExactInterfaceTermParameters depth)
    (hmultiplicity : term.multiplicity = n + 1) (B : Finset R)
    (seed : ProgressionHash.Seed R (Fin (n + 1))) := by
  classical
  exact Finset.univ.filter fun source ↦
    encoding.legalTriple K q term hmultiplicity source ∈
      ProgressionHash.LegalTriple.xIsolatedTargets
        (encoding.legalTargets K q term hmultiplicity) B seed

/-- The actual coarsened block-address support retained by the `X`-isolation pass. -/
noncomputable def xIsolatedCoarseSupport (encoding : CWCoarseFieldEncoding R depth)
    (K : Type u) [CommRing K] (q : ℕ) {n : ℕ}
    (term : ExactInterfaceTermParameters depth)
    (hmultiplicity : term.multiplicity = n + 1) (B : Finset R)
    (seed : ProgressionHash.Seed R (Fin (n + 1))) :
    Finset (BlockAddress (fun _c ↦ PositiveWord (CWCoarseDigit depth) n)) := by
  classical
  exact (encoding.xIsolatedSources K q term hmultiplicity B seed).image Subtype.val

/-- The retained address support is a subfamily of the coarsened selected support. -/
theorem xIsolatedCoarseSupport_subset (encoding : CWCoarseFieldEncoding R depth)
    (K : Type u) [CommRing K] (q : ℕ) {n : ℕ}
    (term : ExactInterfaceTermParameters depth)
    (hmultiplicity : term.multiplicity = n + 1) (B : Finset R)
    (seed : ProgressionHash.Seed R (Fin (n + 1))) :
    encoding.xIsolatedCoarseSupport K q term hmultiplicity B seed ⊆
      (cwCoarsenedSelectedExactInterfaceTerm K q term hmultiplicity).support := by
  classical
  intro address haddress
  rw [xIsolatedCoarseSupport, Finset.mem_image] at haddress
  obtain ⟨source, _hsource, rfl⟩ := haddress
  exact source.2

/-- The source-side and legal-triple-side isolated families have the same cardinality. -/
theorem card_xIsolatedCoarseSupport (encoding : CWCoarseFieldEncoding R depth)
    (K : Type u) [CommRing K] (q : ℕ) {n : ℕ}
    (term : ExactInterfaceTermParameters depth)
    (hmultiplicity : term.multiplicity = n + 1) (B : Finset R)
    (seed : ProgressionHash.Seed R (Fin (n + 1))) :
    (encoding.xIsolatedCoarseSupport K q term hmultiplicity B seed).card =
      (ProgressionHash.LegalTriple.xIsolatedTargets
        (encoding.legalTargets K q term hmultiplicity) B seed).card := by
  classical
  let sources := encoding.xIsolatedSources K q term hmultiplicity B seed
  let targets := encoding.legalTargets K q term hmultiplicity
  let isolated := ProgressionHash.LegalTriple.xIsolatedTargets targets B seed
  have himage : isolated = sources.image
      (encoding.legalTriple K q term hmultiplicity) := by
    ext triple
    constructor
    · intro htriple
      have htarget : triple ∈ targets := by
        change triple ∈ ProgressionHash.LegalTriple.xIsolatedTargets
          targets B seed at htriple
        unfold ProgressionHash.LegalTriple.xIsolatedTargets
          ProgressionHash.Seed.isolatedTargets at htriple
        obtain ⟨pair, hpair, rfl⟩ := Finset.mem_image.mp htriple
        exact (Finset.mem_product.mp (Finset.mem_filter.mp hpair).1).1
      change triple ∈ encoding.legalTargets K q term hmultiplicity at htarget
      rw [legalTargets, Finset.mem_image] at htarget
      obtain ⟨source, _hsource, rfl⟩ := htarget
      apply Finset.mem_image.mpr
      refine ⟨source, ?_, rfl⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, htriple⟩
    · intro htriple
      rw [Finset.mem_image] at htriple
      obtain ⟨source, hsource, rfl⟩ := htriple
      exact (Finset.mem_filter.mp hsource).2
  unfold xIsolatedCoarseSupport
  rw [Finset.card_image_of_injOn Subtype.val_injective.injOn]
  change sources.card = isolated.card
  rw [himage, Finset.card_image_of_injOn
    (encoding.legalTriple_injective K q term hmultiplicity).injOn]

/-- Complete `X`-fiber isolation makes the retained coarse `X` block words pairwise distinct.
This is the precise injectivity licensed by the paper's hash pass. -/
theorem x_injectiveOn_xIsolatedCoarseSupport
    (encoding : CWCoarseFieldEncoding R depth)
    (K : Type u) [CommRing K] (q : ℕ) {n : ℕ}
    (term : ExactInterfaceTermParameters depth)
    (hmultiplicity : term.multiplicity = n + 1) (B : Finset R)
    (seed : ProgressionHash.Seed R (Fin (n + 1))) :
    Set.InjOn
      (fun address : BlockAddress
        (fun _c ↦ PositiveWord (CWCoarseDigit depth) n) ↦ address .X)
      (encoding.xIsolatedCoarseSupport K q term hmultiplicity B seed :
        Set (BlockAddress (fun _c ↦ PositiveWord (CWCoarseDigit depth) n))) := by
  classical
  let targets := encoding.legalTargets K q term hmultiplicity
  let isolated := ProgressionHash.LegalTriple.xIsolatedTargets targets B seed
  have htargetInj : Set.InjOn
      (fun triple : ProgressionHash.LegalTriple R (Fin (n + 1)) encoding.target ↦
        triple.xIndex) (isolated : Set _) := by
    apply ProgressionHash.Seed.xIndex_injectiveOn_isolatedTargets
      targets B ProgressionHash.LegalTriple.xIndex ProgressionHash.LegalTriple.yIndex
      (ProgressionHash.LegalTriple.xCompetitorYIndices targets) seed
    intro triple htriple other hother hne hx
    exact ProgressionHash.LegalTriple.yIndex_mem_xCompetitorYIndices
      targets hother hne hx
  intro left hleft right hright hx
  change left ∈ encoding.xIsolatedCoarseSupport
    K q term hmultiplicity B seed at hleft
  change right ∈ encoding.xIsolatedCoarseSupport
    K q term hmultiplicity B seed at hright
  rw [xIsolatedCoarseSupport, Finset.mem_image] at hleft hright
  obtain ⟨leftSource, hleftSource, rfl⟩ := hleft
  obtain ⟨rightSource, hrightSource, rfl⟩ := hright
  have hleftIsolated : encoding.legalTriple K q term hmultiplicity leftSource ∈
      isolated := by
    exact (Finset.mem_filter.mp hleftSource).2
  have hrightIsolated : encoding.legalTriple K q term hmultiplicity rightSource ∈
      isolated := by
    exact (Finset.mem_filter.mp hrightSource).2
  have hxIndex :
      (encoding.legalTriple K q term hmultiplicity leftSource).xIndex =
        (encoding.legalTriple K q term hmultiplicity rightSource).xIndex := by
    change leftSource.1 .X = rightSource.1 .X at hx
    funext sample
    change encoding.encode
        (positiveWordEquiv (CWCoarseDigit depth) n (leftSource.1 .X) sample) =
      encoding.encode
        (positiveWordEquiv (CWCoarseDigit depth) n (rightSource.1 .X) sample)
    rw [hx]
  have htriple := htargetInj hleftIsolated hrightIsolated hxIndex
  exact congrArg Subtype.val
    (encoding.legalTriple_injective K q term hmultiplicity htriple)

/-- Paper-level coarse hashing extraction.  Under the standard competitor-degree hypothesis,
some seed retains a coarse support with the exact finite lower bound and pairwise distinct coarse
`X` words.  No fine-address injectivity is asserted or used. -/
theorem exists_seed_many_xIsolatedCoarseSupport
    (encoding : CWCoarseFieldEncoding R depth)
    [Fintype R] [NeZero (2 : R)]
    (K : Type u) [CommRing K] (q : ℕ) {n : ℕ}
    (term : ExactInterfaceTermParameters depth)
    (hmultiplicity : term.multiplicity = n + 1) (B : Finset R)
    (hquarter : ∀ triple ∈ encoding.legalTargets K q term hmultiplicity,
      4 * (ProgressionHash.LegalTriple.xCompetitorYIndices
        (encoding.legalTargets K q term hmultiplicity) triple).card ≤
          Fintype.card R) :
    ∃ seed : ProgressionHash.Seed R (Fin (n + 1)),
      3 * (cwCoarsenedSelectedExactInterfaceTerm K q term hmultiplicity).support.card *
          B.card ≤
        4 * (Fintype.card R * Fintype.card R) *
          (encoding.xIsolatedCoarseSupport K q term hmultiplicity B seed).card ∧
      encoding.xIsolatedCoarseSupport K q term hmultiplicity B seed ⊆
        (cwCoarsenedSelectedExactInterfaceTerm K q term hmultiplicity).support ∧
      Set.InjOn
        (fun address : BlockAddress
          (fun _c ↦ PositiveWord (CWCoarseDigit depth) n) ↦ address .X)
        (encoding.xIsolatedCoarseSupport K q term hmultiplicity B seed :
          Set (BlockAddress (fun _c ↦ PositiveWord (CWCoarseDigit depth) n))) := by
  classical
  obtain ⟨seed, hcount, _hfiltered, _hinjective⟩ :=
    ProgressionHash.LegalTriple.exists_seed_many_xIsolatedTargets
      (encoding.legalTargets K q term hmultiplicity) B hquarter
  refine ⟨seed, ?_,
    encoding.xIsolatedCoarseSupport_subset K q term hmultiplicity B seed,
    encoding.x_injectiveOn_xIsolatedCoarseSupport K q term hmultiplicity B seed⟩
  simpa [encoding.card_legalTargets K q term hmultiplicity,
    encoding.card_xIsolatedCoarseSupport K q term hmultiplicity B seed] using hcount

end CWCoarseFieldEncoding

end AlgebraicComplexity.Examples
