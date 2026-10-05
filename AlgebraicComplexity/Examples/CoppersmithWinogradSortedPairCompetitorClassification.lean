/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Combinatorics.ConditionalFeatureWordType
import AlgebraicComplexity.Examples.CoppersmithWinogradSortedPairCounting

/-!
# Concrete competitor classes for the sorted-pair quotient

This module constructs, rather than assumes, the injective maps used to count compatibility.
A supported quotient address is transposed back to its unique word of supported level-two atoms
and tagged by the recursive region at every sample.  It records both orientations of the same
finite bipartite incidence:

* for a fixed `Y` or `Z` label, compatible quotient addresses inject into a conditional-feature
  class of complete tagged atom words;
* for a fixed quotient address, compatible labels inject into an ordinary conditional class
  whose source is the realized compatibility-cell word and whose joint type is exactly the
  evaluator target profile.

The exact double-counting theorem in `CompatibilityIsolationCounting` identifies the sums of
these two families.  The second orientation is the finite quantity `Q` counted in the paper.

In the first orientation the finite objects have:

* source word: the fixed quotient label;
* target word: the full tagged quotient-support atom word;
* feature: `yCompatibilityCell` or `zCompatibilityCell` of the atom's coarse shape;
* prescribed joint type: the pushed-forward target cell profile.

The target atom word retains the complete supported address, so the maps are genuinely
injective.  In the transposed orientation the positive-word equivalence gives the injective map
on labels.  No representative choice inside a quotient fiber and no damaged-box repair is used.

These are finite counting statements.  Turning them into a lower bound for a hash-selected
isolated support additionally requires the affine-hashing collision budget; it is intentionally
not hidden in the type-class bounds below.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor MoreAsymmetryCompatibility
open scoped BigOperators

universe u v

section SupportedAtomWords

variable (K : Type u) [CommRing K] (q n : ℕ)

/-- The unique supported source word underlying an address in a positive power. -/
noncomputable def cwSortedPairSupportedWordOfAddress
    (address : BlockAddress (fun _c ↦ PositiveWord (SplitWord 1) n))
    (haddress : address ∈
      (((cwChunkPartitionedTensor K q 1).coarsen
        cwSortedPairChunkCoarsening).positivePower n).support) :
    PositiveWord (CWSortedPairCoarseSupport K q) n := by
  classical
  exact Classical.choose
    (((cwChunkPartitionedTensor K q 1).coarsen
      cwSortedPairChunkCoarsening).exists_positiveSupportWord_of_mem_positivePower_support
        n haddress)

/-- Transposing the recovered source word returns the original positive-power address. -/
theorem positiveSupportWordBlockAddress_cwSortedPairSupportedWordOfAddress
    (address : BlockAddress (fun _c ↦ PositiveWord (SplitWord 1) n))
    (haddress : address ∈
      (((cwChunkPartitionedTensor K q 1).coarsen
        cwSortedPairChunkCoarsening).positivePower n).support) :
    positiveSupportWordBlockAddress (CWSortedPairCoarseSupport K q) n
        (cwSortedPairSupportedWordOfAddress K q n address haddress) = address :=
  Classical.choose_spec
    (((cwChunkPartitionedTensor K q 1).coarsen
      cwSortedPairChunkCoarsening).exists_positiveSupportWord_of_mem_positivePower_support
        n haddress)

/-- One full supported quotient atom, tagged by the recursive region containing its sample. -/
abbrev CWSortedPairTaggedAtom (Part : Type v) :=
  Part × CWSortedPairCoarseSupport K q

/-- Recover the complete tagged quotient-support atom at every sample. -/
noncomputable def cwSortedPairTaggedAtomWord
    {Part : Type v} (partAt : Fin (n + 1) → Part)
    (address : BlockAddress (fun _c ↦ PositiveWord (SplitWord 1) n))
    (haddress : address ∈
      (((cwChunkPartitionedTensor K q 1).coarsen
        cwSortedPairChunkCoarsening).positivePower n).support) :
    Fin (n + 1) → CWSortedPairTaggedAtom K q Part :=
  fun sample ↦
    (partAt sample,
      positiveWordEquiv (CWSortedPairCoarseSupport K q) n
        (cwSortedPairSupportedWordOfAddress K q n address haddress) sample)

/-- The supported atom word remembers every quotient leg word coordinatewise. -/
theorem cwSortedPairTaggedAtomWord_address_apply
    {Part : Type v} (partAt : Fin (n + 1) → Part)
    (address : BlockAddress (fun _c ↦ PositiveWord (SplitWord 1) n))
    (haddress : address ∈
      (((cwChunkPartitionedTensor K q 1).coarsen
        cwSortedPairChunkCoarsening).positivePower n).support)
    (sample : Fin (n + 1)) (c : Leg) :
    ((cwSortedPairTaggedAtomWord K q n partAt address haddress sample).2.1 c) =
      positiveWordEquiv (SplitWord 1) n (address c) sample := by
  have htranspose := positiveWordEquiv_positiveSupportWordBlockAddress
    (CWSortedPairCoarseSupport K q) n
    (cwSortedPairSupportedWordOfAddress K q n address haddress) c
  rw [positiveSupportWordBlockAddress_cwSortedPairSupportedWordOfAddress
    K q n address haddress] at htranspose
  exact (congrFun htranspose sample).symm

/-- Complete tagged atom words are injective in the supported positive-power address. -/
theorem cwSortedPairTaggedAtomWord_injective
    {Part : Type v} (partAt : Fin (n + 1) → Part)
    {left right : BlockAddress (fun _c ↦ PositiveWord (SplitWord 1) n)}
    (hleft : left ∈
      (((cwChunkPartitionedTensor K q 1).coarsen
        cwSortedPairChunkCoarsening).positivePower n).support)
    (hright : right ∈
      (((cwChunkPartitionedTensor K q 1).coarsen
        cwSortedPairChunkCoarsening).positivePower n).support)
    (hword : cwSortedPairTaggedAtomWord K q n partAt left hleft =
      cwSortedPairTaggedAtomWord K q n partAt right hright) :
    left = right := by
  funext c
  apply (positiveWordEquiv (SplitWord 1) n).injective
  funext sample
  rw [← cwSortedPairTaggedAtomWord_address_apply K q n partAt left hleft sample c,
    ← cwSortedPairTaggedAtomWord_address_apply K q n partAt right hright sample c]
  exact congrArg (fun word ↦ (word sample).2.1 c) hword

/-- Coarse index carried by one complete tagged quotient atom. -/
def cwSortedPairTaggedAtomCoarseIndex
    {Part : Type v} (atom : CWSortedPairTaggedAtom K q Part) : CoarseIndex Part where
  part := atom.1
  x := splitWordWeight (atom.2.1 .X)
  y := splitWordWeight (atom.2.1 .Y)
  z := splitWordWeight (atom.2.1 .Z)

/-- The atom-level coarse index agrees with the concrete feature model's sample index. -/
theorem cwSortedPairTaggedAtomCoarseIndex_atomWord
    {Part : Type v} (partAt : Fin (n + 1) → Part)
    (address : BlockAddress (fun _c ↦ PositiveWord (SplitWord 1) n))
    (haddress : address ∈
      (((cwChunkPartitionedTensor K q 1).coarsen
        cwSortedPairChunkCoarsening).positivePower n).support)
    (sample : Fin (n + 1)) :
    cwSortedPairTaggedAtomCoarseIndex K q
        (cwSortedPairTaggedAtomWord K q n partAt address haddress sample) =
      (cwSortedPairFeatureCompatibilityModel n partAt).coarse address sample := by
  have hx := congrArg splitWordWeight
    (cwSortedPairTaggedAtomWord_address_apply K q n partAt
      address haddress sample .X)
  have hy := congrArg splitWordWeight
    (cwSortedPairTaggedAtomWord_address_apply K q n partAt
      address haddress sample .Y)
  have hz := congrArg splitWordWeight
    (cwSortedPairTaggedAtomWord_address_apply K q n partAt
      address haddress sample .Z)
  change CoarseIndex.mk (partAt sample)
      (splitWordWeight
        ((cwSortedPairTaggedAtomWord K q n partAt address haddress sample).2.1 .X))
      (splitWordWeight
        ((cwSortedPairTaggedAtomWord K q n partAt address haddress sample).2.1 .Y))
      (splitWordWeight
        ((cwSortedPairTaggedAtomWord K q n partAt address haddress sample).2.1 .Z)) =
    CoarseIndex.mk (partAt sample)
      (splitWordWeight
        (positiveWordEquiv (SplitWord 1) n (address .X) sample))
      (splitWordWeight
        (positiveWordEquiv (SplitWord 1) n (address .Y) sample))
      (splitWordWeight
        (positiveWordEquiv (SplitWord 1) n (address .Z) sample))
  rw [hx, hy, hz]

end SupportedAtomWords

/-! ## Evaluator source words, features, and joint profiles -/

/-- The `Y` cell feature of a complete tagged quotient atom. -/
def cwSortedPairYCellOfTaggedAtom
    (K : Type u) [CommRing K] (q : ℕ)
    {Part : Type v} [DecidableEq Part] :
    CWSortedPairTaggedAtom K q Part → YCompatibilityCell Part :=
  yCompatibilityCell ∘ cwSortedPairTaggedAtomCoarseIndex K q

/-- The `Z` cell feature of a complete tagged quotient atom. -/
def cwSortedPairZCellOfTaggedAtom
    (K : Type u) [CommRing K] (q : ℕ)
    {Part : Type v} [DecidableEq Part] :
    CWSortedPairTaggedAtom K q Part → ZCompatibilityCell Part :=
  zCompatibilityCell ∘ cwSortedPairTaggedAtomCoarseIndex K q

/-- The finite `Y` cell alphabet actually realized by supported tagged quotient atoms.  The
ambient inductive cell type contains arbitrary natural indices and is therefore infinite; this
image subtype is the correct finite alphabet seen by the evaluator. -/
noncomputable def cwSortedPairYCellAlphabet
    (K : Type u) [CommRing K] (q : ℕ)
    (Part : Type v) [Fintype Part] [DecidableEq Part] :
    Finset (YCompatibilityCell Part) := by
  classical
  exact Finset.univ.image (cwSortedPairYCellOfTaggedAtom K q)

/-- Finite subtype of realized `Y` compatibility cells. -/
abbrev CWSortedPairYCell
    (K : Type u) [CommRing K] (q : ℕ)
    (Part : Type v) [Fintype Part] [DecidableEq Part] :=
  {cell // cell ∈ cwSortedPairYCellAlphabet K q Part}

/-- Every supported tagged atom maps canonically to the finite realized `Y` cell alphabet. -/
noncomputable def cwSortedPairYFiniteCellOfTaggedAtom
    (K : Type u) [CommRing K] (q : ℕ)
    {Part : Type v} [Fintype Part] [DecidableEq Part]
    (atom : CWSortedPairTaggedAtom K q Part) :
    CWSortedPairYCell K q Part := by
  classical
  exact ⟨cwSortedPairYCellOfTaggedAtom K q atom,
    Finset.mem_image.mpr ⟨atom, Finset.mem_univ _, rfl⟩⟩

/-- The finite `Z` cell alphabet actually realized by supported tagged quotient atoms. -/
noncomputable def cwSortedPairZCellAlphabet
    (K : Type u) [CommRing K] (q : ℕ)
    (Part : Type v) [Fintype Part] [DecidableEq Part] :
    Finset (ZCompatibilityCell Part) := by
  classical
  exact Finset.univ.image (cwSortedPairZCellOfTaggedAtom K q)

/-- Finite subtype of realized `Z` compatibility cells. -/
abbrev CWSortedPairZCell
    (K : Type u) [CommRing K] (q : ℕ)
    (Part : Type v) [Fintype Part] [DecidableEq Part] :=
  {cell // cell ∈ cwSortedPairZCellAlphabet K q Part}

/-- Every supported tagged atom maps canonically to the finite realized `Z` cell alphabet. -/
noncomputable def cwSortedPairZFiniteCellOfTaggedAtom
    (K : Type u) [CommRing K] (q : ℕ)
    {Part : Type v} [Fintype Part] [DecidableEq Part]
    (atom : CWSortedPairTaggedAtom K q Part) :
    CWSortedPairZCell K q Part := by
  classical
  exact ⟨cwSortedPairZCellOfTaggedAtom K q atom,
    Finset.mem_image.mpr ⟨atom, Finset.mem_univ _, rfl⟩⟩

/-- Joint `(fixed symbol, Y-cell)` type used by the compatibility evaluator. -/
noncomputable def cwSortedPairYEvaluatorJointType
    (K : Type u) [CommRing K] (q : ℕ)
    {Part : Type v} [Fintype Part] [DecidableEq Part]
    (rawTargets : CompatibilityTargets Part 1) :
    SplitWord 1 × CWSortedPairYCell K q Part → ℕ :=
  fun pair ↦
    (cwSortedPairPushforwardTargets rawTargets).yCellProfile pair.2.1 pair.1

/-- Joint `(fixed symbol, Z-cell)` type used by the compatibility evaluator. -/
noncomputable def cwSortedPairZEvaluatorJointType
    (K : Type u) [CommRing K] (q : ℕ)
    {Part : Type v} [Fintype Part] [DecidableEq Part]
    (rawTargets : CompatibilityTargets Part 1) :
    SplitWord 1 × CWSortedPairZCell K q Part → ℕ :=
  fun pair ↦
    (cwSortedPairPushforwardTargets rawTargets).zCellProfile pair.2.1 pair.1

/-- Joint `(Y-cell, variable symbol)` type in the fixed-address orientation used by the
paper's compatibility count. -/
noncomputable def cwSortedPairYCellSymbolJointType
    (K : Type u) [CommRing K] (q : ℕ)
    {Part : Type v} [Fintype Part] [DecidableEq Part]
    (rawTargets : CompatibilityTargets Part 1) :
    CWSortedPairYCell K q Part × SplitWord 1 → ℕ :=
  fun pair ↦
    (cwSortedPairPushforwardTargets rawTargets).yCellProfile pair.1.1 pair.2

/-- Joint `(Z-cell, variable symbol)` type in the fixed-address orientation used by the
paper's compatibility count. -/
noncomputable def cwSortedPairZCellSymbolJointType
    (K : Type u) [CommRing K] (q : ℕ)
    {Part : Type v} [Fintype Part] [DecidableEq Part]
    (rawTargets : CompatibilityTargets Part 1) :
    CWSortedPairZCell K q Part × SplitWord 1 → ℕ :=
  fun pair ↦
    (cwSortedPairPushforwardTargets rawTargets).zCellProfile pair.1.1 pair.2

/-- Swapping the two coordinates in `cellMultiplicity` presents it as the ordinary joint type
of the fixed symbol word and the variable compatibility-cell word. -/
theorem multiplicity_jointWord_eq_cellMultiplicity
    {samples : ℕ} {Symbol Cell : Type*}
    [Fintype Symbol] [DecidableEq Symbol] [Fintype Cell] [DecidableEq Cell]
    (symbols : Fin samples → Symbol) (cells : Fin samples → Cell)
    (symbol : Symbol) (cell : Cell) :
    WordType.multiplicity (WordType.jointWord symbols cells) (symbol, cell) =
      cellMultiplicity cells symbols cell symbol := by
  classical
  unfold WordType.multiplicity WordType.jointWord cellMultiplicity
  congr 1
  ext sample
  simp [Prod.ext_iff, and_comm]

/-- With the cell word first, ordinary joint multiplicity is literally `cellMultiplicity`. -/
theorem multiplicity_jointWord_cells_eq_cellMultiplicity
    {samples : ℕ} {Cell Symbol : Type*}
    [Fintype Cell] [DecidableEq Cell] [Fintype Symbol] [DecidableEq Symbol]
    (cells : Fin samples → Cell) (symbols : Fin samples → Symbol)
    (cell : Cell) (symbol : Symbol) :
    WordType.multiplicity (WordType.jointWord cells symbols) (cell, symbol) =
      cellMultiplicity cells symbols cell symbol := by
  classical
  unfold WordType.multiplicity WordType.jointWord cellMultiplicity
  congr 1
  ext sample
  simp [Prod.ext_iff]

/-- Counting a subtype-valued cell word is the same as counting its underlying cells. -/
theorem cellMultiplicity_subtype_val
    {samples : ℕ} {Cell Symbol : Type*}
    [DecidableEq Cell] [DecidableEq Symbol]
    {cells : Finset Cell} (cellWord : Fin samples → {cell // cell ∈ cells})
    (symbols : Fin samples → Symbol) (cell : {cell // cell ∈ cells})
    (symbol : Symbol) :
    cellMultiplicity cellWord symbols cell symbol =
      cellMultiplicity (fun sample ↦ (cellWord sample).1) symbols cell.1 symbol := by
  classical
  unfold cellMultiplicity
  congr 1
  ext sample
  simp

/-! ## Fixed-address compatible-label encodings -/

/-- The realized `Y`-cell sequence of one supported sorted-pair quotient address. -/
noncomputable def cwSortedPairYCellWord
    (K : Type u) [CommRing K] (q n : ℕ)
    {Part : Type v} [Fintype Part] [DecidableEq Part]
    (partAt : Fin (n + 1) → Part)
    (address : BlockAddress (fun _c ↦ PositiveWord (SplitWord 1) n))
    (haddress : address ∈
      (((cwChunkPartitionedTensor K q 1).coarsen
        cwSortedPairChunkCoarsening).positivePower n).support) :
    Fin (n + 1) → CWSortedPairYCell K q Part :=
  cwSortedPairYFiniteCellOfTaggedAtom K q ∘
    cwSortedPairTaggedAtomWord K q n partAt address haddress

/-- The realized `Z`-cell sequence of one supported sorted-pair quotient address. -/
noncomputable def cwSortedPairZCellWord
    (K : Type u) [CommRing K] (q n : ℕ)
    {Part : Type v} [Fintype Part] [DecidableEq Part]
    (partAt : Fin (n + 1) → Part)
    (address : BlockAddress (fun _c ↦ PositiveWord (SplitWord 1) n))
    (haddress : address ∈
      (((cwChunkPartitionedTensor K q 1).coarsen
        cwSortedPairChunkCoarsening).positivePower n).support) :
    Fin (n + 1) → CWSortedPairZCell K q Part :=
  cwSortedPairZFiniteCellOfTaggedAtom K q ∘
    cwSortedPairTaggedAtomWord K q n partAt address haddress

/-- Concrete `Y` compatibility is exactly membership in the fixed-address joint type. -/
theorem cwSortedPairYCellSymbolJointType_eq_multiplicity_of_compatible
    (K : Type u) [CommRing K] (q n : ℕ)
    {Part : Type v} [Fintype Part] [DecidableEq Part]
    (partAt : Fin (n + 1) → Part) (rawTargets : CompatibilityTargets Part 1)
    (address : BlockAddress (fun _c ↦ PositiveWord (SplitWord 1) n))
    (haddress : address ∈
      (((cwChunkPartitionedTensor K q 1).coarsen
        cwSortedPairChunkCoarsening).positivePower n).support)
    (label : PositiveWord (SplitWord 1) n)
    (hcompatible : cwSortedPairCompatibilityY n partAt rawTargets label address) :
    WordType.multiplicity
        (WordType.jointWord
          (cwSortedPairYCellWord K q n partAt address haddress)
          (positiveWordEquiv (SplitWord 1) n label)) =
      cwSortedPairYCellSymbolJointType K q rawTargets := by
  funext pair
  obtain ⟨cell, symbol⟩ := pair
  rw [multiplicity_jointWord_cells_eq_cellMultiplicity,
    cellMultiplicity_subtype_val]
  have hcells :
      (fun sample ↦
        ((cwSortedPairYCellWord K q n partAt address haddress sample).1)) =
      (fun sample ↦ yCompatibilityCell
        ((cwSortedPairFeatureCompatibilityModel n partAt).coarse address sample)) := by
    funext sample
    change yCompatibilityCell
        (cwSortedPairTaggedAtomCoarseIndex K q
          (cwSortedPairTaggedAtomWord K q n partAt address haddress sample)) = _
    rw [cwSortedPairTaggedAtomCoarseIndex_atomWord]
  rw [hcells]
  exact hcompatible cell.1 symbol

/-- Concrete `Z` compatibility is exactly membership in the fixed-address joint type. -/
theorem cwSortedPairZCellSymbolJointType_eq_multiplicity_of_compatible
    (K : Type u) [CommRing K] (q n : ℕ)
    {Part : Type v} [Fintype Part] [DecidableEq Part]
    (partAt : Fin (n + 1) → Part) (rawTargets : CompatibilityTargets Part 1)
    (address : BlockAddress (fun _c ↦ PositiveWord (SplitWord 1) n))
    (haddress : address ∈
      (((cwChunkPartitionedTensor K q 1).coarsen
        cwSortedPairChunkCoarsening).positivePower n).support)
    (label : PositiveWord (SplitWord 1) n)
    (hcompatible : cwSortedPairCompatibilityZ n partAt rawTargets label address) :
    WordType.multiplicity
        (WordType.jointWord
          (cwSortedPairZCellWord K q n partAt address haddress)
          (positiveWordEquiv (SplitWord 1) n label)) =
      cwSortedPairZCellSymbolJointType K q rawTargets := by
  funext pair
  obtain ⟨cell, symbol⟩ := pair
  rw [multiplicity_jointWord_cells_eq_cellMultiplicity,
    cellMultiplicity_subtype_val]
  have hcells :
      (fun sample ↦
        ((cwSortedPairZCellWord K q n partAt address haddress sample).1)) =
      (fun sample ↦ zCompatibilityCell
        ((cwSortedPairFeatureCompatibilityModel n partAt).coarse address sample)) := by
    funext sample
    change zCompatibilityCell
        (cwSortedPairTaggedAtomCoarseIndex K q
          (cwSortedPairTaggedAtomWord K q n partAt address haddress sample)) = _
    rw [cwSortedPairTaggedAtomCoarseIndex_atomWord]
  rw [hcells]
  exact hcompatible cell.1 symbol

/-- Fully constructed fixed-address `Y` compatible-label encoding.  Its source word is the
actual realized compatibility-cell sequence, its joint type is exactly the evaluator profile,
and its refinement map is the positive-word equivalence. -/
noncomputable def cwSortedPairYCompatibleLabelEncoding
    (K : Type u) [CommRing K] (q n : ℕ)
    {Part : Type v} [Fintype Part] [DecidableEq Part]
    (partAt : Fin (n + 1) → Part) (rawTargets : CompatibilityTargets Part 1)
    (labels : Finset (PositiveWord (SplitWord 1) n))
    (address : BlockAddress (fun _c ↦ PositiveWord (SplitWord 1) n))
    (haddress : address ∈
      (((cwChunkPartitionedTensor K q 1).coarsen
        cwSortedPairChunkCoarsening).positivePower n).support)
    (hself : cwSortedPairCompatibilityY n partAt rawTargets (address .Y) address) :
    ConditionalCompatibleLabelEncoding (pivot := .Y) labels
      (cwSortedPairCompatibilityY n partAt rawTargets) address
      (CWSortedPairYCell K q Part) (SplitWord 1) (n + 1) where
  source := cwSortedPairYCellWord K q n partAt address haddress
  jointType := cwSortedPairYCellSymbolJointType K q rawTargets
  jointType_legal := by
    rw [← cwSortedPairYCellSymbolJointType_eq_multiplicity_of_compatible
      K q n partAt rawTargets address haddress (address .Y) hself]
    exact WordType.multiplicity_mem_types _
  jointType_fst := by
    rw [← cwSortedPairYCellSymbolJointType_eq_multiplicity_of_compatible
      K q n partAt rawTargets address haddress (address .Y) hself]
    have hpush := WordType.multiplicity_comp_eq_mappedType Prod.fst
      (WordType.jointWord
        (cwSortedPairYCellWord K q n partAt address haddress)
        (positiveWordEquiv (SplitWord 1) n (address .Y)))
    rw [← hpush]
    congr 1
  refinement := fun label ↦ positiveWordEquiv (SplitWord 1) n label.1
  refinement_mem := by
    intro label
    rw [WordType.mem_conditionalTypeClass]
    exact cwSortedPairYCellSymbolJointType_eq_multiplicity_of_compatible
      K q n partAt rawTargets address haddress label.1
        ((mem_compatibleLabels labels
          (cwSortedPairCompatibilityY n partAt rawTargets) address label.1).1
            label.2).2
  refinement_injective := by
    intro left right h
    apply Subtype.ext
    exact (positiveWordEquiv (SplitWord 1) n).injective h

/-- Fully constructed fixed-address `Z` compatible-label encoding. -/
noncomputable def cwSortedPairZCompatibleLabelEncoding
    (K : Type u) [CommRing K] (q n : ℕ)
    {Part : Type v} [Fintype Part] [DecidableEq Part]
    (partAt : Fin (n + 1) → Part) (rawTargets : CompatibilityTargets Part 1)
    (labels : Finset (PositiveWord (SplitWord 1) n))
    (address : BlockAddress (fun _c ↦ PositiveWord (SplitWord 1) n))
    (haddress : address ∈
      (((cwChunkPartitionedTensor K q 1).coarsen
        cwSortedPairChunkCoarsening).positivePower n).support)
    (hself : cwSortedPairCompatibilityZ n partAt rawTargets (address .Z) address) :
    ConditionalCompatibleLabelEncoding (pivot := .Z) labels
      (cwSortedPairCompatibilityZ n partAt rawTargets) address
      (CWSortedPairZCell K q Part) (SplitWord 1) (n + 1) where
  source := cwSortedPairZCellWord K q n partAt address haddress
  jointType := cwSortedPairZCellSymbolJointType K q rawTargets
  jointType_legal := by
    rw [← cwSortedPairZCellSymbolJointType_eq_multiplicity_of_compatible
      K q n partAt rawTargets address haddress (address .Z) hself]
    exact WordType.multiplicity_mem_types _
  jointType_fst := by
    rw [← cwSortedPairZCellSymbolJointType_eq_multiplicity_of_compatible
      K q n partAt rawTargets address haddress (address .Z) hself]
    have hpush := WordType.multiplicity_comp_eq_mappedType Prod.fst
      (WordType.jointWord
        (cwSortedPairZCellWord K q n partAt address haddress)
        (positiveWordEquiv (SplitWord 1) n (address .Z)))
    rw [← hpush]
    congr 1
  refinement := fun label ↦ positiveWordEquiv (SplitWord 1) n label.1
  refinement_mem := by
    intro label
    rw [WordType.mem_conditionalTypeClass]
    exact cwSortedPairZCellSymbolJointType_eq_multiplicity_of_compatible
      K q n partAt rawTargets address haddress label.1
        ((mem_compatibleLabels labels
          (cwSortedPairCompatibilityZ n partAt rawTargets) address label.1).1
            label.2).2
  refinement_injective := by
    intro left right h
    apply Subtype.ext
    exact (positiveWordEquiv (SplitWord 1) n).injective h

/-- Exact conditional-type bound for the `Y` labels compatible with one fixed quotient
address. -/
theorem cwSortedPair_card_compatibleLabelsY_le_conditionalTypeClass
    (K : Type u) [CommRing K] (q n : ℕ)
    {Part : Type v} [Fintype Part] [DecidableEq Part]
    (partAt : Fin (n + 1) → Part) (rawTargets : CompatibilityTargets Part 1)
    (labels : Finset (PositiveWord (SplitWord 1) n))
    (address : BlockAddress (fun _c ↦ PositiveWord (SplitWord 1) n))
    (haddress : address ∈
      (((cwChunkPartitionedTensor K q 1).coarsen
        cwSortedPairChunkCoarsening).positivePower n).support)
    (hself : cwSortedPairCompatibilityY n partAt rawTargets (address .Y) address) :
    (compatibleLabels (pivot := .Y) labels
        (cwSortedPairCompatibilityY n partAt rawTargets) address).card ≤
      (WordType.conditionalTypeClass
        (cwSortedPairYCellWord K q n partAt address haddress)
        (cwSortedPairYCellSymbolJointType K q rawTargets)).card :=
  (cwSortedPairYCompatibleLabelEncoding K q n partAt rawTargets labels address
    haddress hself).card_compatibleLabels_le_card_conditionalTypeClass

/-- Exact conditional-type bound for the `Z` labels compatible with one fixed quotient
address. -/
theorem cwSortedPair_card_compatibleLabelsZ_le_conditionalTypeClass
    (K : Type u) [CommRing K] (q n : ℕ)
    {Part : Type v} [Fintype Part] [DecidableEq Part]
    (partAt : Fin (n + 1) → Part) (rawTargets : CompatibilityTargets Part 1)
    (labels : Finset (PositiveWord (SplitWord 1) n))
    (address : BlockAddress (fun _c ↦ PositiveWord (SplitWord 1) n))
    (haddress : address ∈
      (((cwChunkPartitionedTensor K q 1).coarsen
        cwSortedPairChunkCoarsening).positivePower n).support)
    (hself : cwSortedPairCompatibilityZ n partAt rawTargets (address .Z) address) :
    (compatibleLabels (pivot := .Z) labels
        (cwSortedPairCompatibilityZ n partAt rawTargets) address).card ≤
      (WordType.conditionalTypeClass
        (cwSortedPairZCellWord K q n partAt address haddress)
        (cwSortedPairZCellSymbolJointType K q rawTargets)).card :=
  (cwSortedPairZCompatibleLabelEncoding K q n partAt rawTargets labels address
    haddress hself).card_compatibleLabels_le_card_conditionalTypeClass

/-- Division-free multinomial form of the concrete fixed-address `Y` count. -/
theorem cwSortedPair_multinomial_YCellType_mul_card_compatibleLabels_le_joint
    (K : Type u) [CommRing K] (q n : ℕ)
    {Part : Type v} [Fintype Part] [DecidableEq Part]
    (partAt : Fin (n + 1) → Part) (rawTargets : CompatibilityTargets Part 1)
    (labels : Finset (PositiveWord (SplitWord 1) n))
    (address : BlockAddress (fun _c ↦ PositiveWord (SplitWord 1) n))
    (haddress : address ∈
      (((cwChunkPartitionedTensor K q 1).coarsen
        cwSortedPairChunkCoarsening).positivePower n).support)
    (hself : cwSortedPairCompatibilityY n partAt rawTargets (address .Y) address) :
    Nat.multinomial Finset.univ
        (WordType.multiplicity
          (cwSortedPairYCellWord K q n partAt address haddress)) *
        (compatibleLabels (pivot := .Y) labels
          (cwSortedPairCompatibilityY n partAt rawTargets) address).card ≤
      Nat.multinomial Finset.univ
        (cwSortedPairYCellSymbolJointType K q rawTargets) :=
  (cwSortedPairYCompatibleLabelEncoding K q n partAt rawTargets labels address
    haddress hself).multinomial_source_mul_card_compatibleLabels_le_multinomial_joint

/-- Division-free multinomial form of the concrete fixed-address `Z` count. -/
theorem cwSortedPair_multinomial_ZCellType_mul_card_compatibleLabels_le_joint
    (K : Type u) [CommRing K] (q n : ℕ)
    {Part : Type v} [Fintype Part] [DecidableEq Part]
    (partAt : Fin (n + 1) → Part) (rawTargets : CompatibilityTargets Part 1)
    (labels : Finset (PositiveWord (SplitWord 1) n))
    (address : BlockAddress (fun _c ↦ PositiveWord (SplitWord 1) n))
    (haddress : address ∈
      (((cwChunkPartitionedTensor K q 1).coarsen
        cwSortedPairChunkCoarsening).positivePower n).support)
    (hself : cwSortedPairCompatibilityZ n partAt rawTargets (address .Z) address) :
    Nat.multinomial Finset.univ
        (WordType.multiplicity
          (cwSortedPairZCellWord K q n partAt address haddress)) *
        (compatibleLabels (pivot := .Z) labels
          (cwSortedPairCompatibilityZ n partAt rawTargets) address).card ≤
      Nat.multinomial Finset.univ
        (cwSortedPairZCellSymbolJointType K q rawTargets) :=
  (cwSortedPairZCompatibleLabelEncoding K q n partAt rawTargets labels address
    haddress hself).multinomial_source_mul_card_compatibleLabels_le_multinomial_joint

/-- The concrete `Y` compatibility-pair count `Q`, first summed over labels, is bounded by the
sum of the evaluator's fixed-address conditional type classes.  This theorem combines the exact
label/address double count with the constructed quotient encoding; no abstract injection remains. -/
theorem cwSortedPair_sum_card_compatibleAddressesY_le_sum_conditionalTypeClasses
    (K : Type u) [CommRing K] (q n : ℕ)
    {Part : Type v} [Fintype Part] [DecidableEq Part]
    (partAt : Fin (n + 1) → Part) (rawTargets : CompatibilityTargets Part 1)
    (labels : Finset (PositiveWord (SplitWord 1) n))
    (ambient : Finset
      (BlockAddress (fun _c ↦ PositiveWord (SplitWord 1) n)))
    (hambient : ambient ⊆
      (((cwChunkPartitionedTensor K q 1).coarsen
        cwSortedPairChunkCoarsening).positivePower n).support)
    (hsound : IsCompatibilitySound ambient .Y
      (cwSortedPairCompatibilityY n partAt rawTargets)) :
    (∑ label ∈ labels,
        (compatibleAddresses (pivot := .Y) ambient
          (cwSortedPairCompatibilityY n partAt rawTargets) label).card) ≤
      ∑ address : ambient,
        (WordType.conditionalTypeClass
          (cwSortedPairYCellWord K q n partAt address.1 (hambient address.2))
          (cwSortedPairYCellSymbolJointType K q rawTargets)).card := by
  have hdouble := sum_card_compatibleAddresses_eq_sum_card_compatibleLabels
    (A := fun _c ↦ PositiveWord (SplitWord 1) n) ambient (pivot := .Y)
      labels (cwSortedPairCompatibilityY n partAt rawTargets)
  rw [hdouble]
  rw [← Finset.sum_attach]
  simpa only [Finset.attach_eq_univ] using
    (Finset.sum_le_sum (s := ambient.attach) (fun address _haddress ↦
      cwSortedPair_card_compatibleLabelsY_le_conditionalTypeClass
        K q n partAt rawTargets labels address.1 (hambient address.2)
          (hsound address.1 address.2)))

/-- `Z` analogue of
`cwSortedPair_sum_card_compatibleAddressesY_le_sum_conditionalTypeClasses`. -/
theorem cwSortedPair_sum_card_compatibleAddressesZ_le_sum_conditionalTypeClasses
    (K : Type u) [CommRing K] (q n : ℕ)
    {Part : Type v} [Fintype Part] [DecidableEq Part]
    (partAt : Fin (n + 1) → Part) (rawTargets : CompatibilityTargets Part 1)
    (labels : Finset (PositiveWord (SplitWord 1) n))
    (ambient : Finset
      (BlockAddress (fun _c ↦ PositiveWord (SplitWord 1) n)))
    (hambient : ambient ⊆
      (((cwChunkPartitionedTensor K q 1).coarsen
        cwSortedPairChunkCoarsening).positivePower n).support)
    (hsound : IsCompatibilitySound ambient .Z
      (cwSortedPairCompatibilityZ n partAt rawTargets)) :
    (∑ label ∈ labels,
        (compatibleAddresses (pivot := .Z) ambient
          (cwSortedPairCompatibilityZ n partAt rawTargets) label).card) ≤
      ∑ address : ambient,
        (WordType.conditionalTypeClass
          (cwSortedPairZCellWord K q n partAt address.1 (hambient address.2))
          (cwSortedPairZCellSymbolJointType K q rawTargets)).card := by
  have hdouble := sum_card_compatibleAddresses_eq_sum_card_compatibleLabels
    (A := fun _c ↦ PositiveWord (SplitWord 1) n) ambient (pivot := .Z)
      labels (cwSortedPairCompatibilityZ n partAt rawTargets)
  rw [hdouble]
  rw [← Finset.sum_attach]
  simpa only [Finset.attach_eq_univ] using
    (Finset.sum_le_sum (s := ambient.attach) (fun address _haddress ↦
      cwSortedPair_card_compatibleLabelsZ_le_conditionalTypeClass
        K q n partAt rawTargets labels address.1 (hambient address.2)
          (hsound address.1 address.2)))

/-! ## Concrete compatibility type classes -/

/-- Full tagged quotient-atom words compatible with one fixed `Y` label. -/
noncomputable def cwSortedPairYCompetitorTypeClass
    (K : Type u) [CommRing K] (q n : ℕ)
    {Part : Type v} [Fintype Part] [DecidableEq Part]
    (rawTargets : CompatibilityTargets Part 1)
    (label : PositiveWord (SplitWord 1) n) :
    Finset (Fin (n + 1) → CWSortedPairTaggedAtom K q Part) := by
  classical
  exact Finset.univ.filter fun atomWord ↦
    WordType.multiplicity
        (WordType.jointWord
          (positiveWordEquiv (SplitWord 1) n label)
          (cwSortedPairYFiniteCellOfTaggedAtom K q ∘ atomWord)) =
      cwSortedPairYEvaluatorJointType K q rawTargets

/-- Full tagged quotient-atom words compatible with one fixed `Z` label. -/
noncomputable def cwSortedPairZCompetitorTypeClass
    (K : Type u) [CommRing K] (q n : ℕ)
    {Part : Type v} [Fintype Part] [DecidableEq Part]
    (rawTargets : CompatibilityTargets Part 1)
    (label : PositiveWord (SplitWord 1) n) :
    Finset (Fin (n + 1) → CWSortedPairTaggedAtom K q Part) := by
  classical
  exact Finset.univ.filter fun atomWord ↦
    WordType.multiplicity
        (WordType.jointWord
          (positiveWordEquiv (SplitWord 1) n label)
          (cwSortedPairZFiniteCellOfTaggedAtom K q ∘ atomWord)) =
      cwSortedPairZEvaluatorJointType K q rawTargets

@[simp] theorem mem_cwSortedPairYCompetitorTypeClass
    (K : Type u) [CommRing K] (q n : ℕ)
    {Part : Type v} [Fintype Part] [DecidableEq Part]
    (rawTargets : CompatibilityTargets Part 1)
    (label : PositiveWord (SplitWord 1) n)
    (atomWord : Fin (n + 1) → CWSortedPairTaggedAtom K q Part) :
    atomWord ∈ cwSortedPairYCompetitorTypeClass K q n rawTargets label ↔
      WordType.multiplicity
          (WordType.jointWord
            (positiveWordEquiv (SplitWord 1) n label)
            (cwSortedPairYFiniteCellOfTaggedAtom K q ∘ atomWord)) =
        cwSortedPairYEvaluatorJointType K q rawTargets := by
  classical
  simp [cwSortedPairYCompetitorTypeClass]

@[simp] theorem mem_cwSortedPairZCompetitorTypeClass
    (K : Type u) [CommRing K] (q n : ℕ)
    {Part : Type v} [Fintype Part] [DecidableEq Part]
    (rawTargets : CompatibilityTargets Part 1)
    (label : PositiveWord (SplitWord 1) n)
    (atomWord : Fin (n + 1) → CWSortedPairTaggedAtom K q Part) :
    atomWord ∈ cwSortedPairZCompetitorTypeClass K q n rawTargets label ↔
      WordType.multiplicity
          (WordType.jointWord
            (positiveWordEquiv (SplitWord 1) n label)
            (cwSortedPairZFiniteCellOfTaggedAtom K q ∘ atomWord)) =
        cwSortedPairZEvaluatorJointType K q rawTargets := by
  classical
  simp [cwSortedPairZCompetitorTypeClass]

/-- The concrete `Y` evaluator class is exactly the generic conditional-feature class. -/
theorem cwSortedPairYCompetitorTypeClass_eq_conditionalFeatureTypeClass
    (K : Type u) [CommRing K] (q n : ℕ)
    {Part : Type v} [Fintype Part] [DecidableEq Part]
    (rawTargets : CompatibilityTargets Part 1)
    (label : PositiveWord (SplitWord 1) n) :
    cwSortedPairYCompetitorTypeClass K q n rawTargets label =
      WordType.conditionalFeatureTypeClass
        (positiveWordEquiv (SplitWord 1) n label)
        (cwSortedPairYFiniteCellOfTaggedAtom K q)
        (cwSortedPairYEvaluatorJointType K q rawTargets) := by
  rfl

/-- The concrete `Z` evaluator class is exactly the generic conditional-feature class. -/
theorem cwSortedPairZCompetitorTypeClass_eq_conditionalFeatureTypeClass
    (K : Type u) [CommRing K] (q n : ℕ)
    {Part : Type v} [Fintype Part] [DecidableEq Part]
    (rawTargets : CompatibilityTargets Part 1)
    (label : PositiveWord (SplitWord 1) n) :
    cwSortedPairZCompetitorTypeClass K q n rawTargets label =
      WordType.conditionalFeatureTypeClass
        (positiveWordEquiv (SplitWord 1) n label)
        (cwSortedPairZFiniteCellOfTaggedAtom K q)
        (cwSortedPairZEvaluatorJointType K q rawTargets) := by
  rfl

/-- Full `(fixed Y symbol, tagged quotient atom)` empirical types feasible for the evaluator's
prescribed visible `Y` compatibility profile. -/
noncomputable abbrev cwSortedPairYFeasibleCompetitorTypes
    (K : Type u) [CommRing K] (q n : ℕ)
    {Part : Type v} [Fintype Part] [DecidableEq Part]
    (rawTargets : CompatibilityTargets Part 1) :=
  WordType.feasibleConditionalFeatureTypes
    (cwSortedPairYFiniteCellOfTaggedAtom K q)
    (cwSortedPairYEvaluatorJointType K q rawTargets) (n + 1)

/-- Full `(fixed Z symbol, tagged quotient atom)` empirical types feasible for the evaluator's
prescribed visible `Z` compatibility profile. -/
noncomputable abbrev cwSortedPairZFeasibleCompetitorTypes
    (K : Type u) [CommRing K] (q n : ℕ)
    {Part : Type v} [Fintype Part] [DecidableEq Part]
    (rawTargets : CompatibilityTargets Part 1) :=
  WordType.feasibleConditionalFeatureTypes
    (cwSortedPairZFiniteCellOfTaggedAtom K q)
    (cwSortedPairZEvaluatorJointType K q rawTargets) (n + 1)

/-- Exact method-of-types decomposition of one concrete `Y` competitor class. -/
theorem cwSortedPair_card_YCompetitorTypeClass_le_sum_fullJointTypes
    (K : Type u) [CommRing K] (q n : ℕ)
    {Part : Type v} [Fintype Part] [DecidableEq Part]
    (rawTargets : CompatibilityTargets Part 1)
    (label : PositiveWord (SplitWord 1) n) :
    (cwSortedPairYCompetitorTypeClass K q n rawTargets label).card ≤
      ∑ jointType ∈ cwSortedPairYFeasibleCompetitorTypes K q n rawTargets,
        (WordType.conditionalTypeClass
          (positiveWordEquiv (SplitWord 1) n label) jointType).card := by
  rw [cwSortedPairYCompetitorTypeClass_eq_conditionalFeatureTypeClass]
  exact WordType.card_conditionalFeatureTypeClass_le_sum_conditionalTypeClasses
    (positiveWordEquiv (SplitWord 1) n label)
    (cwSortedPairYFiniteCellOfTaggedAtom K q)
    (cwSortedPairYEvaluatorJointType K q rawTargets)

/-- Exact method-of-types decomposition of one concrete `Z` competitor class. -/
theorem cwSortedPair_card_ZCompetitorTypeClass_le_sum_fullJointTypes
    (K : Type u) [CommRing K] (q n : ℕ)
    {Part : Type v} [Fintype Part] [DecidableEq Part]
    (rawTargets : CompatibilityTargets Part 1)
    (label : PositiveWord (SplitWord 1) n) :
    (cwSortedPairZCompetitorTypeClass K q n rawTargets label).card ≤
      ∑ jointType ∈ cwSortedPairZFeasibleCompetitorTypes K q n rawTargets,
        (WordType.conditionalTypeClass
          (positiveWordEquiv (SplitWord 1) n label) jointType).card := by
  rw [cwSortedPairZCompetitorTypeClass_eq_conditionalFeatureTypeClass]
  exact WordType.card_conditionalFeatureTypeClass_le_sum_conditionalTypeClasses
    (positiveWordEquiv (SplitWord 1) n label)
    (cwSortedPairZFiniteCellOfTaggedAtom K q)
    (cwSortedPairZEvaluatorJointType K q rawTargets)

/-- Polynomial-overhead maximum-type bound for one concrete `Y` competitor class. -/
theorem cwSortedPair_card_YCompetitorTypeClass_le_polynomial_mul
    (K : Type u) [CommRing K] (q n : ℕ)
    {Part : Type v} [Fintype Part] [DecidableEq Part]
    (rawTargets : CompatibilityTargets Part 1)
    (label : PositiveWord (SplitWord 1) n) (bound : ℕ)
    (hbound : ∀ jointType ∈
      cwSortedPairYFeasibleCompetitorTypes K q n rawTargets,
      (WordType.conditionalTypeClass
        (positiveWordEquiv (SplitWord 1) n label) jointType).card ≤ bound) :
    (cwSortedPairYCompetitorTypeClass K q n rawTargets label).card ≤
      (n + 2) ^ Fintype.card
        (SplitWord 1 × CWSortedPairTaggedAtom K q Part) * bound := by
  rw [cwSortedPairYCompetitorTypeClass_eq_conditionalFeatureTypeClass]
  simpa only [Nat.add_assoc] using
    (WordType.card_conditionalFeatureTypeClass_le_succ_pow_mul
      (positiveWordEquiv (SplitWord 1) n label)
      (cwSortedPairYFiniteCellOfTaggedAtom K q)
      (cwSortedPairYEvaluatorJointType K q rawTargets) bound hbound)

/-- Polynomial-overhead maximum-type bound for one concrete `Z` competitor class. -/
theorem cwSortedPair_card_ZCompetitorTypeClass_le_polynomial_mul
    (K : Type u) [CommRing K] (q n : ℕ)
    {Part : Type v} [Fintype Part] [DecidableEq Part]
    (rawTargets : CompatibilityTargets Part 1)
    (label : PositiveWord (SplitWord 1) n) (bound : ℕ)
    (hbound : ∀ jointType ∈
      cwSortedPairZFeasibleCompetitorTypes K q n rawTargets,
      (WordType.conditionalTypeClass
        (positiveWordEquiv (SplitWord 1) n label) jointType).card ≤ bound) :
    (cwSortedPairZCompetitorTypeClass K q n rawTargets label).card ≤
      (n + 2) ^ Fintype.card
        (SplitWord 1 × CWSortedPairTaggedAtom K q Part) * bound := by
  rw [cwSortedPairZCompetitorTypeClass_eq_conditionalFeatureTypeClass]
  simpa only [Nat.add_assoc] using
    (WordType.card_conditionalFeatureTypeClass_le_succ_pow_mul
      (positiveWordEquiv (SplitWord 1) n label)
      (cwSortedPairZFiniteCellOfTaggedAtom K q)
      (cwSortedPairZEvaluatorJointType K q rawTargets) bound hbound)

/-! ## Constructed competitor injections -/

/-- Every concrete sorted-pair `Y` competitor maps injectively into the evaluator's exact
conditional feature-type class. -/
theorem cwSortedPair_card_compatibilityCompetitorsY_le_typeClass
    (K : Type u) [CommRing K] (q n : ℕ)
    {Part : Type v} [Fintype Part] [DecidableEq Part]
    (partAt : Fin (n + 1) → Part) (rawTargets : CompatibilityTargets Part 1)
    (ambient : Finset
      (BlockAddress (fun _c ↦ PositiveWord (SplitWord 1) n)))
    (hambient : ambient ⊆
      (((cwChunkPartitionedTensor K q 1).coarsen
        cwSortedPairChunkCoarsening).positivePower n).support)
    (address : BlockAddress (fun _c ↦ PositiveWord (SplitWord 1) n)) :
    (compatibilityCompetitors ambient .Y
        (cwSortedPairCompatibilityY n partAt rawTargets) address).card ≤
      (cwSortedPairYCompetitorTypeClass K q n rawTargets (address .Y)).card := by
  classical
  let competitors := compatibilityCompetitors ambient .Y
    (cwSortedPairCompatibilityY n partAt rawTargets) address
  let targetClass := cwSortedPairYCompetitorTypeClass K q n rawTargets (address .Y)
  let refinement : {other // other ∈ competitors} →
      Fin (n + 1) → CWSortedPairTaggedAtom K q Part := fun other ↦
    cwSortedPairTaggedAtomWord K q n partAt other.1
      (hambient (((mem_compatibilityCompetitors ambient .Y
        (cwSortedPairCompatibilityY n partAt rawTargets) address other.1).1 other.2).1))
  have hrefinement_mem (other : {other // other ∈ competitors}) :
      refinement other ∈ targetClass := by
    have hmem := (mem_compatibilityCompetitors ambient .Y
      (cwSortedPairCompatibilityY n partAt rawTargets) address other.1).1 other.2
    have hcompatible := hmem.2.2
    rw [mem_cwSortedPairYCompetitorTypeClass]
    funext pair
    obtain ⟨symbol, cell⟩ := pair
    rw [multiplicity_jointWord_eq_cellMultiplicity]
    rw [cellMultiplicity_subtype_val]
    have hcells :
        (fun sample ↦
          ((cwSortedPairYFiniteCellOfTaggedAtom K q ∘ refinement other) sample).1) =
        (fun sample ↦ yCompatibilityCell
          ((cwSortedPairFeatureCompatibilityModel n partAt).coarse other.1 sample)) := by
      funext sample
      change yCompatibilityCell
          (cwSortedPairTaggedAtomCoarseIndex K q
            (cwSortedPairTaggedAtomWord K q n partAt other.1
              (hambient hmem.1) sample)) = _
      rw [cwSortedPairTaggedAtomCoarseIndex_atomWord]
    rw [hcells]
    exact hcompatible cell.1 symbol
  let f : {other // other ∈ competitors} → {word // word ∈ targetClass} :=
    fun other ↦ ⟨refinement other, hrefinement_mem other⟩
  have hf : Function.Injective f := by
    intro left right h
    apply Subtype.ext
    apply cwSortedPairTaggedAtomWord_injective K q n partAt
      (hambient ((mem_compatibilityCompetitors ambient .Y
        (cwSortedPairCompatibilityY n partAt rawTargets) address left.1).1 left.2).1)
      (hambient ((mem_compatibilityCompetitors ambient .Y
        (cwSortedPairCompatibilityY n partAt rawTargets) address right.1).1 right.2).1)
    exact congrArg Subtype.val h
  simpa only [competitors, targetClass, Fintype.card_coe] using
    Fintype.card_le_of_injective f hf

/-- Every concrete sorted-pair `Z` competitor maps injectively into the evaluator's exact
conditional feature-type class. -/
theorem cwSortedPair_card_compatibilityCompetitorsZ_le_typeClass
    (K : Type u) [CommRing K] (q n : ℕ)
    {Part : Type v} [Fintype Part] [DecidableEq Part]
    (partAt : Fin (n + 1) → Part) (rawTargets : CompatibilityTargets Part 1)
    (ambient : Finset
      (BlockAddress (fun _c ↦ PositiveWord (SplitWord 1) n)))
    (hambient : ambient ⊆
      (((cwChunkPartitionedTensor K q 1).coarsen
        cwSortedPairChunkCoarsening).positivePower n).support)
    (address : BlockAddress (fun _c ↦ PositiveWord (SplitWord 1) n)) :
    (compatibilityCompetitors ambient .Z
        (cwSortedPairCompatibilityZ n partAt rawTargets) address).card ≤
      (cwSortedPairZCompetitorTypeClass K q n rawTargets (address .Z)).card := by
  classical
  let competitors := compatibilityCompetitors ambient .Z
    (cwSortedPairCompatibilityZ n partAt rawTargets) address
  let targetClass := cwSortedPairZCompetitorTypeClass K q n rawTargets (address .Z)
  let refinement : {other // other ∈ competitors} →
      Fin (n + 1) → CWSortedPairTaggedAtom K q Part := fun other ↦
    cwSortedPairTaggedAtomWord K q n partAt other.1
      (hambient (((mem_compatibilityCompetitors ambient .Z
        (cwSortedPairCompatibilityZ n partAt rawTargets) address other.1).1 other.2).1))
  have hrefinement_mem (other : {other // other ∈ competitors}) :
      refinement other ∈ targetClass := by
    have hmem := (mem_compatibilityCompetitors ambient .Z
      (cwSortedPairCompatibilityZ n partAt rawTargets) address other.1).1 other.2
    have hcompatible := hmem.2.2
    rw [mem_cwSortedPairZCompetitorTypeClass]
    funext pair
    obtain ⟨symbol, cell⟩ := pair
    rw [multiplicity_jointWord_eq_cellMultiplicity]
    rw [cellMultiplicity_subtype_val]
    have hcells :
        (fun sample ↦
          ((cwSortedPairZFiniteCellOfTaggedAtom K q ∘ refinement other) sample).1) =
        (fun sample ↦ zCompatibilityCell
          ((cwSortedPairFeatureCompatibilityModel n partAt).coarse other.1 sample)) := by
      funext sample
      change zCompatibilityCell
          (cwSortedPairTaggedAtomCoarseIndex K q
            (cwSortedPairTaggedAtomWord K q n partAt other.1
              (hambient hmem.1) sample)) = _
      rw [cwSortedPairTaggedAtomCoarseIndex_atomWord]
    rw [hcells]
    exact hcompatible cell.1 symbol
  let f : {other // other ∈ competitors} → {word // word ∈ targetClass} :=
    fun other ↦ ⟨refinement other, hrefinement_mem other⟩
  have hf : Function.Injective f := by
    intro left right h
    apply Subtype.ext
    apply cwSortedPairTaggedAtomWord_injective K q n partAt
      (hambient ((mem_compatibilityCompetitors ambient .Z
        (cwSortedPairCompatibilityZ n partAt rawTargets) address left.1).1 left.2).1)
      (hambient ((mem_compatibilityCompetitors ambient .Z
        (cwSortedPairCompatibilityZ n partAt rawTargets) address right.1).1 right.2).1)
    exact congrArg Subtype.val h
  simpa only [competitors, targetClass, Fintype.card_coe] using
    Fintype.card_le_of_injective f hf

/-- Fully concrete quotient count after no-hole cleanup.  Every loss term is now the cardinality
of an explicit evaluator type class; no abstract competitor encoding remains. -/
theorem cwSortedPair_card_ambient_le_card_YZIsolatedSupport_add_evaluatorTypeCounts
    (K : Type u) [CommRing K] (q n : ℕ)
    {Part : Type v} [Fintype Part] [DecidableEq Part]
    (partAt : Fin (n + 1) → Part) (rawTargets : CompatibilityTargets Part 1)
    (ambient : Finset
      (BlockAddress (fun _c ↦ PositiveWord (SplitWord 1) n)))
    (hambient : ambient ⊆
      (((cwChunkPartitionedTensor K q 1).coarsen
        cwSortedPairChunkCoarsening).positivePower n).support) :
    ambient.card ≤
      (cwSortedPairYZIsolatedSupport n partAt rawTargets ambient).card +
        (∑ address ∈ ambient,
          (cwSortedPairYCompetitorTypeClass K q n rawTargets (address .Y)).card) +
        (∑ address ∈ cwSortedPairYIsolatedSupport n partAt rawTargets ambient,
          (cwSortedPairZCompetitorTypeClass K q n rawTargets (address .Z)).card) := by
  apply cwSortedPair_card_ambient_le_card_YZIsolatedSupport_add_budgets
    n partAt rawTargets ambient
  · unfold cwSortedPairYCompetitorIncidence compatibilityCompetitorIncidence
    apply Finset.sum_le_sum
    intro address _haddress
    exact cwSortedPair_card_compatibilityCompetitorsY_le_typeClass
      K q n partAt rawTargets ambient hambient address
  · unfold cwSortedPairZCompetitorIncidence compatibilityCompetitorIncidence
    apply Finset.sum_le_sum
    intro address _haddress
    apply cwSortedPair_card_compatibilityCompetitorsZ_le_typeClass
      K q n partAt rawTargets
      (cwSortedPairYIsolatedSupport n partAt rawTargets ambient)
    · exact (compatibilityIsolatedSupport_subset ambient .Y
        (cwSortedPairCompatibilityY n partAt rawTargets)).trans hambient

/-- Fully expanded exact method-of-types form of the conservative directed-competitor quotient
count.  The inner sums range over feasible full `(fixed label symbol, tagged quotient atom)` joint
types, and their summands are ordinary conditional type classes.  The fixed-address transposed
theorems above expose separately the paper's `Q` orientation. -/
theorem cwSortedPair_card_ambient_le_card_YZIsolatedSupport_add_fullJointTypeCounts
    (K : Type u) [CommRing K] (q n : ℕ)
    {Part : Type v} [Fintype Part] [DecidableEq Part]
    (partAt : Fin (n + 1) → Part) (rawTargets : CompatibilityTargets Part 1)
    (ambient : Finset
      (BlockAddress (fun _c ↦ PositiveWord (SplitWord 1) n)))
    (hambient : ambient ⊆
      (((cwChunkPartitionedTensor K q 1).coarsen
        cwSortedPairChunkCoarsening).positivePower n).support) :
    ambient.card ≤
      (cwSortedPairYZIsolatedSupport n partAt rawTargets ambient).card +
        (∑ address ∈ ambient,
          ∑ jointType ∈ cwSortedPairYFeasibleCompetitorTypes K q n rawTargets,
            (WordType.conditionalTypeClass
              (positiveWordEquiv (SplitWord 1) n (address .Y)) jointType).card) +
        (∑ address ∈ cwSortedPairYIsolatedSupport n partAt rawTargets ambient,
          ∑ jointType ∈ cwSortedPairZFeasibleCompetitorTypes K q n rawTargets,
            (WordType.conditionalTypeClass
              (positiveWordEquiv (SplitWord 1) n (address .Z)) jointType).card) := by
  have hbase :=
    cwSortedPair_card_ambient_le_card_YZIsolatedSupport_add_evaluatorTypeCounts
      K q n partAt rawTargets ambient hambient
  refine hbase.trans ?_
  gcongr with address haddress
  · exact cwSortedPair_card_YCompetitorTypeClass_le_sum_fullJointTypes
      K q n rawTargets (address .Y)
  · exact cwSortedPair_card_ZCompetitorTypeClass_le_sum_fullJointTypes
      K q n rawTargets (address .Z)

end AlgebraicComplexity.Examples
