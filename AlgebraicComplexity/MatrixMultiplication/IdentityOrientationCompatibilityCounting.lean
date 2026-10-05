/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Combinatorics.IdentityOrientationCompetitorCount
import AlgebraicComplexity.MatrixMultiplication.CompatibilityIsolationCounting
import AlgebraicComplexity.MatrixMultiplication.MoreAsymmetryCompatibility

/-!
# Loss-free identity-orientation compatibility counts

For one fixed coarse address, only finitely many compatibility cells occur even though the raw
cell datatype permits arbitrary natural coordinates.  This module restricts to that finite image
and injects every compatible fine label into the conditional type class whose joint table is the
prescribed complete-split cell profile.  The resulting count is exactly a product of cell
multinomials, with no asymptotic loss.

The basic theorem exposes legality and the first marginal explicitly.  The stronger
`..._of_self` theorem derives both facts from the address's own compatible pivot label.  Thus,
after the first compatibility zero-out, neither condition remains as a certificate-facing
level-four obligation: only membership of the pivot label and injectivity of the concrete chunk
encoding are needed.  No tensor degeneration, hashing conclusion, or repair premise appears
here.
-/

open scoped BigOperators

namespace AlgebraicComplexity

open Tensor

universe u v w

/-- Cells that actually occur in one fixed finite source word. -/
def observedCells {Cell : Type u} [DecidableEq Cell] {samples : ℕ}
    (cells : Fin samples → Cell) : Finset Cell :=
  Finset.univ.image cells

/-- The finite alphabet of cells occurring in `cells`. -/
abbrev ObservedCell {Cell : Type u} [DecidableEq Cell] {samples : ℕ}
    (cells : Fin samples → Cell) :=
  {cell // cell ∈ observedCells cells}

/-- The source cell word, now valued in its finite observed-cell alphabet. -/
def observedCellWord {Cell : Type u} [DecidableEq Cell] {samples : ℕ}
    (cells : Fin samples → Cell) : Fin samples → ObservedCell cells :=
  fun sample ↦ ⟨cells sample, Finset.mem_image.mpr ⟨sample, Finset.mem_univ _, rfl⟩⟩

/-- Joint multiplicity over the observed-cell subtype is the concrete raw cell multiplicity. -/
theorem multiplicity_jointWord_observedCellWord_eq_cellMultiplicity
    {Cell : Type u} [DecidableEq Cell]
    {Symbol : Type v} [Fintype Symbol] [DecidableEq Symbol]
    {samples : ℕ} (cells : Fin samples → Cell) (symbols : Fin samples → Symbol)
    (cell : ObservedCell cells) (symbol : Symbol) :
    WordType.multiplicity
        (WordType.jointWord (observedCellWord cells) symbols) (cell, symbol) =
      MoreAsymmetryCompatibility.cellMultiplicity cells symbols cell.1 symbol := by
  classical
  unfold WordType.multiplicity WordType.jointWord
    MoreAsymmetryCompatibility.cellMultiplicity
  congr 1
  ext sample
  simp [observedCellWord, Prod.ext_iff, Subtype.ext_iff]

/-- Generic fixed-address encoding by a prescribed profile on the observed cells. -/
noncomputable def cellProfileConditionalCompatibleLabelEncoding
    {A : Leg → Type w} [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]
    {pivot : Leg} (labels : Finset (A pivot))
    (compatible : A pivot → BlockAddress A → Prop) (address : BlockAddress A)
    {Cell : Type u} [DecidableEq Cell]
    {Symbol : Type v} [Fintype Symbol] [DecidableEq Symbol]
    {samples : ℕ} (cells : Fin samples → Cell)
    (refinement : A pivot → Fin samples → Symbol)
    (profile : Cell → Symbol → ℕ)
    (hprofile : ∀ label ∈ compatibleLabels labels compatible address,
      ∀ cell symbol,
        MoreAsymmetryCompatibility.cellMultiplicity cells (refinement label) cell symbol =
          profile cell symbol)
    (hinjective : Set.InjOn refinement labels)
    (hlegal : (fun pair : ObservedCell cells × Symbol ↦
        profile pair.1.1 pair.2) ∈
      WordType.types (ObservedCell cells × Symbol) samples)
    (hfst : WordType.mappedType Prod.fst
        (fun pair : ObservedCell cells × Symbol ↦ profile pair.1.1 pair.2) =
      WordType.multiplicity (observedCellWord cells)) :
    ConditionalCompatibleLabelEncoding labels compatible address
      (ObservedCell cells) Symbol samples where
  source := observedCellWord cells
  jointType := fun pair ↦ profile pair.1.1 pair.2
  jointType_legal := hlegal
  jointType_fst := hfst
  refinement label := refinement label.1
  refinement_mem label := by
    rw [WordType.mem_conditionalTypeClass]
    funext pair
    obtain ⟨cell, symbol⟩ := pair
    rw [multiplicity_jointWord_observedCellWord_eq_cellMultiplicity]
    exact hprofile label.1 label.2 cell.1 symbol
  refinement_injective := by
    intro left right heq
    apply Subtype.ext
    exact hinjective
      ((mem_compatibleLabels labels compatible address left.1).1 left.2).1
      ((mem_compatibleLabels labels compatible address right.1).1 right.2).1 heq

/-- Loss-free compatible-label bound for an arbitrary concrete cell profile. -/
theorem card_compatibleLabels_le_prod_observedCell_multinomial
    {A : Leg → Type w} [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]
    {pivot : Leg} (labels : Finset (A pivot))
    (compatible : A pivot → BlockAddress A → Prop) (address : BlockAddress A)
    {Cell : Type u} [DecidableEq Cell]
    {Symbol : Type v} [Fintype Symbol] [DecidableEq Symbol]
    {samples : ℕ} (cells : Fin samples → Cell)
    (refinement : A pivot → Fin samples → Symbol)
    (profile : Cell → Symbol → ℕ)
    (hprofile : ∀ label ∈ compatibleLabels labels compatible address,
      ∀ cell symbol,
        MoreAsymmetryCompatibility.cellMultiplicity cells (refinement label) cell symbol =
          profile cell symbol)
    (hinjective : Set.InjOn refinement labels)
    (hlegal : (fun pair : ObservedCell cells × Symbol ↦
        profile pair.1.1 pair.2) ∈
      WordType.types (ObservedCell cells × Symbol) samples)
    (hfst : WordType.mappedType Prod.fst
        (fun pair : ObservedCell cells × Symbol ↦ profile pair.1.1 pair.2) =
      WordType.multiplicity (observedCellWord cells)) :
    (compatibleLabels labels compatible address).card ≤
      ∏ cell : ObservedCell cells,
        Nat.multinomial Finset.univ (profile cell.1) := by
  let encoding := cellProfileConditionalCompatibleLabelEncoding labels compatible address
    cells refinement profile hprofile hinjective hlegal hfst
  calc
    (compatibleLabels labels compatible address).card ≤
        (WordType.conditionalTypeClass encoding.source encoding.jointType).card :=
      encoding.card_compatibleLabels_le_card_conditionalTypeClass
    _ = ∏ cell : ObservedCell cells,
        Nat.multinomial Finset.univ (profile cell.1) := by
      simpa [encoding, cellProfileConditionalCompatibleLabelEncoding] using
        WordType.card_conditionalTypeClass_eq_prod_multinomial
          encoding.source encoding.jointType encoding.jointType_legal encoding.jointType_fst

/-- The fixed address itself supplies legality and the first-marginal identity.

This is the form used after compatibility soundness has been proved: the address's own pivot
label belongs to the candidate label set and realizes the prescribed cell profile.  Hence the
profile table is the multiplicity of an actual joint word, so clients do not have to reprove its
legality or its cell marginal separately. -/
theorem card_compatibleLabels_le_prod_observedCell_multinomial_of_self
    {A : Leg → Type w} [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]
    {pivot : Leg} (labels : Finset (A pivot))
    (compatible : A pivot → BlockAddress A → Prop) (address : BlockAddress A)
    {Cell : Type u} [DecidableEq Cell]
    {Symbol : Type v} [Fintype Symbol] [DecidableEq Symbol]
    {samples : ℕ} (cells : Fin samples → Cell)
    (refinement : A pivot → Fin samples → Symbol)
    (profile : Cell → Symbol → ℕ)
    (hprofile : ∀ label ∈ compatibleLabels labels compatible address,
      ∀ cell symbol,
        MoreAsymmetryCompatibility.cellMultiplicity cells (refinement label) cell symbol =
          profile cell symbol)
    (hinjective : Set.InjOn refinement labels)
    (hself_mem : address pivot ∈ labels)
    (hself : compatible (address pivot) address) :
    (compatibleLabels labels compatible address).card ≤
      ∏ cell : ObservedCell cells,
        Nat.multinomial Finset.univ (profile cell.1) := by
  let source := observedCellWord cells
  let jointType : ObservedCell cells × Symbol → ℕ :=
    fun pair ↦ profile pair.1.1 pair.2
  have hself_mem' : address pivot ∈ compatibleLabels labels compatible address :=
    (mem_compatibleLabels labels compatible address (address pivot)).2
      ⟨hself_mem, hself⟩
  have hjoint :
      jointType = WordType.multiplicity
        (WordType.jointWord source (refinement (address pivot))) := by
    funext pair
    obtain ⟨cell, symbol⟩ := pair
    change profile cell.1 symbol = _
    rw [multiplicity_jointWord_observedCellWord_eq_cellMultiplicity]
    exact (hprofile (address pivot) hself_mem' cell.1 symbol).symm
  have hlegal : jointType ∈
      WordType.types (ObservedCell cells × Symbol) samples := by
    rw [hjoint]
    exact WordType.multiplicity_mem_types _
  have hfst : WordType.mappedType Prod.fst jointType =
      WordType.multiplicity source := by
    rw [hjoint]
    have hpush := WordType.multiplicity_comp_eq_mappedType Prod.fst
      (WordType.jointWord source (refinement (address pivot)))
    rw [← hpush]
    congr 1
  exact card_compatibleLabels_le_prod_observedCell_multinomial labels compatible address
    cells refinement profile hprofile hinjective hlegal hfst

namespace MoreAsymmetryCompatibility.CompatibilityModel

variable {A : Leg → Type w} [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]
variable {Part : Type u} [DecidableEq Part]
variable {depth samples : ℕ}

/-- Raw identity-oriented `Y` compatibility-cell word of one address. -/
def yCellWord (model : CompatibilityModel A Part depth samples)
    (address : BlockAddress A) : Fin samples → YCompatibilityCell Part :=
  fun sample ↦ yCompatibilityCell (model.coarse address sample)

/-- Raw identity-oriented `Z` compatibility-cell word of one address. -/
def zCellWord (model : CompatibilityModel A Part depth samples)
    (address : BlockAddress A) : Fin samples → ZCompatibilityCell Part :=
  fun sample ↦ zCompatibilityCell (model.coarse address sample)

/-- Loss-free identity-orientation `Y` count over exactly the cells occurring in `address`. -/
theorem card_compatibleLabelsY_le_prod_multinomial
    (model : CompatibilityModel A Part depth samples)
    (targets : CompatibilityTargets Part depth)
    (labels : Finset (A .Y)) (address : BlockAddress A)
    (hlegal : (fun pair : ObservedCell (model.yCellWord address) × SplitWord depth ↦
        targets.yCellProfile pair.1.1 pair.2) ∈
      WordType.types (ObservedCell (model.yCellWord address) × SplitWord depth) samples)
    (hfst : WordType.mappedType Prod.fst
        (fun pair : ObservedCell (model.yCellWord address) × SplitWord depth ↦
          targets.yCellProfile pair.1.1 pair.2) =
      WordType.multiplicity (observedCellWord (model.yCellWord address)))
    (hinjective : Set.InjOn (model.chunks .Y) labels) :
    (compatibleLabels labels (model.CompatibleY targets) address).card ≤
      ∏ cell : ObservedCell (model.yCellWord address),
        Nat.multinomial Finset.univ (targets.yCellProfile cell.1) := by
  apply card_compatibleLabels_le_prod_observedCell_multinomial labels
    (model.CompatibleY targets) address (model.yCellWord address)
      (model.chunks .Y) targets.yCellProfile
  · intro label hlabel cell word
    exact ((mem_compatibleLabels labels (model.CompatibleY targets) address label).1 hlabel).2
      cell word
  · exact hinjective
  · exact hlegal
  · exact hfst

/-- Identity-oriented `Y` count with legality and the cell marginal obtained from the address's
own compatible `Y` label. -/
theorem card_compatibleLabelsY_le_prod_multinomial_of_self
    (model : CompatibilityModel A Part depth samples)
    (targets : CompatibilityTargets Part depth)
    (labels : Finset (A .Y)) (address : BlockAddress A)
    (hinjective : Set.InjOn (model.chunks .Y) labels)
    (hself_mem : address .Y ∈ labels)
    (hself : model.CompatibleY targets (address .Y) address) :
    (compatibleLabels labels (model.CompatibleY targets) address).card ≤
      ∏ cell : ObservedCell (model.yCellWord address),
        Nat.multinomial Finset.univ (targets.yCellProfile cell.1) := by
  apply card_compatibleLabels_le_prod_observedCell_multinomial_of_self labels
    (model.CompatibleY targets) address (model.yCellWord address)
      (model.chunks .Y) targets.yCellProfile
  · intro label hlabel cell word
    exact ((mem_compatibleLabels labels (model.CompatibleY targets) address label).1 hlabel).2
      cell word
  · exact hinjective
  · exact hself_mem
  · exact hself

/-- Loss-free identity-orientation `Z` count over exactly the cells occurring in `address`. -/
theorem card_compatibleLabelsZ_le_prod_multinomial
    (model : CompatibilityModel A Part depth samples)
    (targets : CompatibilityTargets Part depth)
    (labels : Finset (A .Z)) (address : BlockAddress A)
    (hlegal : (fun pair : ObservedCell (model.zCellWord address) × SplitWord depth ↦
        targets.zCellProfile pair.1.1 pair.2) ∈
      WordType.types (ObservedCell (model.zCellWord address) × SplitWord depth) samples)
    (hfst : WordType.mappedType Prod.fst
        (fun pair : ObservedCell (model.zCellWord address) × SplitWord depth ↦
          targets.zCellProfile pair.1.1 pair.2) =
      WordType.multiplicity (observedCellWord (model.zCellWord address)))
    (hinjective : Set.InjOn (model.chunks .Z) labels) :
    (compatibleLabels labels (model.CompatibleZ targets) address).card ≤
      ∏ cell : ObservedCell (model.zCellWord address),
        Nat.multinomial Finset.univ (targets.zCellProfile cell.1) := by
  apply card_compatibleLabels_le_prod_observedCell_multinomial labels
    (model.CompatibleZ targets) address (model.zCellWord address)
      (model.chunks .Z) targets.zCellProfile
  · intro label hlabel cell word
    exact ((mem_compatibleLabels labels (model.CompatibleZ targets) address label).1 hlabel).2
      cell word
  · exact hinjective
  · exact hlegal
  · exact hfst

/-- Identity-oriented `Z` count with legality and the cell marginal obtained from the address's
own compatible `Z` label. -/
theorem card_compatibleLabelsZ_le_prod_multinomial_of_self
    (model : CompatibilityModel A Part depth samples)
    (targets : CompatibilityTargets Part depth)
    (labels : Finset (A .Z)) (address : BlockAddress A)
    (hinjective : Set.InjOn (model.chunks .Z) labels)
    (hself_mem : address .Z ∈ labels)
    (hself : model.CompatibleZ targets (address .Z) address) :
    (compatibleLabels labels (model.CompatibleZ targets) address).card ≤
      ∏ cell : ObservedCell (model.zCellWord address),
        Nat.multinomial Finset.univ (targets.zCellProfile cell.1) := by
  apply card_compatibleLabels_le_prod_observedCell_multinomial_of_self labels
    (model.CompatibleZ targets) address (model.zCellWord address)
      (model.chunks .Z) targets.zCellProfile
  · intro label hlabel cell word
    exact ((mem_compatibleLabels labels (model.CompatibleZ targets) address label).1 hlabel).2
      cell word
  · exact hinjective
  · exact hself_mem
  · exact hself

end MoreAsymmetryCompatibility.CompatibilityModel
end AlgebraicComplexity
