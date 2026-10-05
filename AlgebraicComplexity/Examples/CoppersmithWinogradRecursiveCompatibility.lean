/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinogradCompatibility
import AlgebraicComplexity.MatrixMultiplication.RecursiveChildType

set_option autoImplicit false

/-!
# Recursive labelled-child compatibility for exact CW interface terms

This module instantiates the generic labelled-child model on native Coppersmith--Winograd chunks.
A selected level-`depth+2` interface term is observed through its two consecutive level-`depth+1`
children.  Fine legality and the fixed parent coordinates are derived from the selected source
support, rather than supplied as certificate assumptions.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor MoreAsymmetryCompatibility
open scoped BigOperators

universe u v

/-- Compatibility model on the two labelled children of every selected native CW parent chunk. -/
def cwRecursiveChildCompatibilityModel {Part : Type v} (depth n : ℕ)
    (partAt : Fin (n + 1) → Part) :=
  recursiveChildCompatibilityModel
    (A := fun _c ↦ PositiveWord CWBlock (2 ^ (depth + 1) - 1))
    (fun _c ↦ cwChunkSplitWord (depth + 1)) partAt

@[simp] theorem cwRecursiveChildCompatibilityModel_chunks
    {Part : Type v} (depth n : ℕ) (partAt : Fin (n + 1) → Part)
    (c : Leg)
    (word : PositiveWord (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n) :
    (cwRecursiveChildCompatibilityModel depth n partAt).chunks c word =
      positiveWordLabelledChildren (cwChunkSplitWord (depth + 1)) word :=
  rfl

/-- Membership in an exact selected parent interface term implies parent-word fine legality. -/
theorem cwRecursive_isParentFineLegal_of_mem_selected_support
    (K : Type u) [CommRing K] (q : ℕ) {depth n : ℕ}
    (term : ExactInterfaceTermParameters (depth + 1))
    (hmultiplicity : term.multiplicity = n + 1)
    (address : BlockAddress (fun _c ↦
      PositiveWord (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n))
    (haddress : address ∈
      (cwSelectedExactInterfaceTerm K q term hmultiplicity).support) :
    IsParentFineLegal (fun _c ↦ cwChunkSplitWord (depth + 1)) address := by
  let partAt : Fin (n + 1) → (PUnit : Type) := fun _ ↦ PUnit.unit
  have hparent :=
    cwExactInterfaceCompatibilityModel_isFineLegal_of_mem_selected_support
      K q partAt term hmultiplicity address haddress
  simpa [IsParentFineLegal, CompatibilityModel.IsFineLegal,
    partAt, cwExactInterfaceCompatibilityModel,
    encodedPositiveWordCompatibilityModel] using hparent

/-- Every parent chunk of a selected exact interface address has the coordinate prescribed by
the parent constituent index. -/
theorem cwRecursive_parentWeight_of_mem_selected_support
    (K : Type u) [CommRing K] (q : ℕ) {depth n : ℕ}
    (term : ExactInterfaceTermParameters (depth + 1))
    (hmultiplicity : term.multiplicity = n + 1)
    (address : BlockAddress (fun _c ↦
      PositiveWord (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n))
    (haddress : address ∈
      (cwSelectedExactInterfaceTerm K q term hmultiplicity).support)
    (c : Leg) (sample : Fin (n + 1)) :
    splitWordWeight
        (cwChunkSplitWord (depth + 1)
          (positiveWordEquiv _ n (address c) sample)) =
      term.index.count c := by
  exact selectedExactInterfaceTerm_chunkWeight
    (cwChunkPartitionedTensor K q (depth + 1))
    (fun _c ↦ cwChunkSplitWord (depth + 1)) term hmultiplicity
    address haddress c sample

/-- The three coordinates of a parent interface index equal twice the child coarse total. -/
theorem cwRecursive_parentTotal
    {depth : ℕ} (term : ExactInterfaceTermParameters (depth + 1)) :
    term.index.count .X + term.index.count .Y + term.index.count .Z =
      2 * coarseTotal depth := by
  have h := term.index.total
  simpa [Tensor.sum_leg, coarseTotal, pow_succ, Nat.mul_comm, Nat.mul_left_comm,
    Nat.mul_assoc] using h

/-! ## Arbitrary region orientations -/

/-- Parent coordinates as seen in the logical coordinate order of one oriented region. -/
def cwRecursiveLogicalParent {depth : ℕ}
    (term : ExactInterfaceTermParameters (depth + 1)) (sigma : Orientation) : Leg → ℕ :=
  fun c ↦ term.index.count (sigma c)

@[simp] theorem cwRecursiveLogicalParent_apply {depth : ℕ}
    (term : ExactInterfaceTermParameters (depth + 1)) (sigma : Orientation) (c : Leg) :
    cwRecursiveLogicalParent term sigma c = term.index.count (sigma c) :=
  rfl

/-- Coordinate relabelling preserves the parent total needed for child complementation. -/
theorem cwRecursiveLogicalParent_total {depth : ℕ}
    (term : ExactInterfaceTermParameters (depth + 1)) (sigma : Orientation) :
    cwRecursiveLogicalParent term sigma .X + cwRecursiveLogicalParent term sigma .Y +
        cwRecursiveLogicalParent term sigma .Z =
      2 * coarseTotal depth := by
  have hperm :
      (∑ c : Leg, term.index.count (sigma c)) =
        ∑ c : Leg, term.index.count c :=
    Fintype.sum_equiv sigma _ _ (fun _ ↦ rfl)
  calc
    cwRecursiveLogicalParent term sigma .X + cwRecursiveLogicalParent term sigma .Y +
        cwRecursiveLogicalParent term sigma .Z =
        ∑ c : Leg, term.index.count (sigma c) := by
          simp [cwRecursiveLogicalParent, Tensor.sum_leg]
    _ = ∑ c : Leg, term.index.count c := hperm
    _ = 2 * coarseTotal depth := by
      simpa [Tensor.sum_leg] using cwRecursive_parentTotal term

/-- Selected-support legality after any logical coordinate orientation. -/
theorem cwRecursive_isParentFineLegal_logicalAddress_of_mem_selected_support
    (K : Type u) [CommRing K] (q : ℕ) {depth n : ℕ}
    (term : ExactInterfaceTermParameters (depth + 1))
    (hmultiplicity : term.multiplicity = n + 1) (sigma : Orientation)
    (address : BlockAddress (fun _c ↦
      PositiveWord (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n))
    (haddress : address ∈
      (cwSelectedExactInterfaceTerm K q term hmultiplicity).support) :
    IsParentFineLegal (fun _c ↦ cwChunkSplitWord (depth + 1))
      (logicalAddress sigma address) := by
  let partAt : Fin (n + 1) → (PUnit : Type) := fun _ ↦ PUnit.unit
  have hparent :=
    cwExactInterfaceCompatibilityModel_isFineLegal_logicalAddress_of_mem_selected_support
      K q partAt term hmultiplicity sigma address haddress
  simpa [IsParentFineLegal, CompatibilityModel.IsFineLegal,
    partAt, cwExactInterfaceCompatibilityModel,
    encodedPositiveWordCompatibilityModel] using hparent

/-- Selected-support parent coordinates after any logical coordinate orientation. -/
theorem cwRecursive_parentWeight_logicalAddress_of_mem_selected_support
    (K : Type u) [CommRing K] (q : ℕ) {depth n : ℕ}
    (term : ExactInterfaceTermParameters (depth + 1))
    (hmultiplicity : term.multiplicity = n + 1) (sigma : Orientation)
    (address : BlockAddress (fun _c ↦
      PositiveWord (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n))
    (haddress : address ∈
      (cwSelectedExactInterfaceTerm K q term hmultiplicity).support)
    (c : Leg) (sample : Fin (n + 1)) :
    splitWordWeight
        (cwChunkSplitWord (depth + 1)
          (positiveWordEquiv _ n ((logicalAddress sigma address) c) sample)) =
      cwRecursiveLogicalParent term sigma c := by
  simpa [logicalAddress_apply, cwRecursiveLogicalParent] using
    cwRecursive_parentWeight_of_mem_selected_support
      K q term hmultiplicity address haddress (sigma c) sample

/-- The labelled-child compatibility model is fine-legal in every oriented region. -/
theorem cwRecursiveChildCompatibilityModel_isFineLegal_logicalAddress_of_mem_selected_support
    (K : Type u) [CommRing K] (q : ℕ) {Part : Type v} {depth n : ℕ}
    (partAt : Fin (n + 1) → Part)
    (term : ExactInterfaceTermParameters (depth + 1))
    (hmultiplicity : term.multiplicity = n + 1) (sigma : Orientation)
    (address : BlockAddress (fun _c ↦
      PositiveWord (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n))
    (haddress : address ∈
      (cwSelectedExactInterfaceTerm K q term hmultiplicity).support) :
    (cwRecursiveChildCompatibilityModel depth n partAt).IsFineLegal
      (logicalAddress sigma address) := by
  exact recursiveChildCompatibilityModel_isFineLegal
    (fun _c ↦ cwChunkSplitWord (depth + 1)) partAt (logicalAddress sigma address)
    (cwRecursive_isParentFineLegal_logicalAddress_of_mem_selected_support
      K q term hmultiplicity sigma address haddress)

/-- Any address in the selected parent term is fine-legal for the labelled-child compatibility
model. -/
theorem cwRecursiveChildCompatibilityModel_isFineLegal_of_mem_selected_support
    (K : Type u) [CommRing K] (q : ℕ) {Part : Type v} {depth n : ℕ}
    (partAt : Fin (n + 1) → Part)
    (term : ExactInterfaceTermParameters (depth + 1))
    (hmultiplicity : term.multiplicity = n + 1)
    (address : BlockAddress (fun _c ↦
      PositiveWord (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n))
    (haddress : address ∈
      (cwSelectedExactInterfaceTerm K q term hmultiplicity).support) :
    (cwRecursiveChildCompatibilityModel depth n partAt).IsFineLegal address := by
  exact recursiveChildCompatibilityModel_isFineLegal
    (fun _c ↦ cwChunkSplitWord (depth + 1)) partAt address
    (cwRecursive_isParentFineLegal_of_mem_selected_support
      K q term hmultiplicity address haddress)

/-- The concrete finite child-shape word attached to one selected parent address. -/
def cwRecursiveChildShapeWord
    (K : Type u) [CommRing K] (q : ℕ) {Part : Type v} {depth n : ℕ}
    (part : Part)
    (term : ExactInterfaceTermParameters (depth + 1))
    (hmultiplicity : term.multiplicity = n + 1)
    (address : BlockAddress (fun _c ↦
      PositiveWord (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n))
    (haddress : address ∈
      (cwSelectedExactInterfaceTerm K q term hmultiplicity).support) :
    Fin ((n + 1) + (n + 1)) →
      RecursiveChildShape term.index.count (coarseTotal depth) :=
  recursiveChildShapeWord
    (fun _c ↦ cwChunkSplitWord (depth + 1)) part address term.index.count
    (cwRecursive_parentTotal term)
    (cwRecursive_parentWeight_of_mem_selected_support
      K q term hmultiplicity address haddress)
    (cwRecursive_isParentFineLegal_of_mem_selected_support
      K q term hmultiplicity address haddress)

/-- The ordered left-child shape word in an arbitrary logical region orientation. -/
def cwRecursiveOrientedLeftChildShapeWord
    (K : Type u) [CommRing K] (q : ℕ) {Part : Type v} {depth n : ℕ}
    (part : Part)
    (term : ExactInterfaceTermParameters (depth + 1))
    (hmultiplicity : term.multiplicity = n + 1) (sigma : Orientation)
    (address : BlockAddress (fun _c ↦
      PositiveWord (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n))
    (haddress : address ∈
      (cwSelectedExactInterfaceTerm K q term hmultiplicity).support) :
    Fin (n + 1) →
      RecursiveChildShape (cwRecursiveLogicalParent term sigma) (coarseTotal depth) :=
  recursiveLeftChildShape
    (fun _c ↦ cwChunkSplitWord (depth + 1)) part (logicalAddress sigma address)
    (cwRecursiveLogicalParent term sigma)
    (cwRecursive_parentWeight_logicalAddress_of_mem_selected_support
      K q term hmultiplicity sigma address haddress)
    (cwRecursive_isParentFineLegal_logicalAddress_of_mem_selected_support
      K q term hmultiplicity sigma address haddress)

/-- The finite labelled-child shape word in an arbitrary logical region orientation. -/
def cwRecursiveOrientedChildShapeWord
    (K : Type u) [CommRing K] (q : ℕ) {Part : Type v} {depth n : ℕ}
    (part : Part)
    (term : ExactInterfaceTermParameters (depth + 1))
    (hmultiplicity : term.multiplicity = n + 1) (sigma : Orientation)
    (address : BlockAddress (fun _c ↦
      PositiveWord (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n))
    (haddress : address ∈
      (cwSelectedExactInterfaceTerm K q term hmultiplicity).support) :
    Fin ((n + 1) + (n + 1)) →
      RecursiveChildShape (cwRecursiveLogicalParent term sigma) (coarseTotal depth) :=
  let left := cwRecursiveOrientedLeftChildShapeWord
    K q part term hmultiplicity sigma address haddress
  Fin.append left
    ((RecursiveChildShape.complementPerm
      (cwRecursiveLogicalParent_total term sigma)) ∘ left)

/-- The concrete child-shape word reproduces the entire coarse word used by recursive hashing and
compatibility. -/
theorem cwRecursiveChildCompatibilityModel_coarse_eq_shapeWord
    (K : Type u) [CommRing K] (q : ℕ) {Part : Type v} {depth n : ℕ}
    (part : Part)
    (term : ExactInterfaceTermParameters (depth + 1))
    (hmultiplicity : term.multiplicity = n + 1)
    (address : BlockAddress (fun _c ↦
      PositiveWord (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n))
    (haddress : address ∈
      (cwSelectedExactInterfaceTerm K q term hmultiplicity).support) :
    (cwRecursiveChildCompatibilityModel depth n (fun _ ↦ part)).coarse address =
      RecursiveChildShape.toCoarseIndex part ∘
        cwRecursiveChildShapeWord K q part term hmultiplicity address haddress := by
  exact recursiveChildCompatibilityModel_coarse_eq_shapeWord
    (fun _c ↦ cwChunkSplitWord (depth + 1)) part address term.index.count
    (cwRecursive_parentTotal term)
    (cwRecursive_parentWeight_of_mem_selected_support
      K q term hmultiplicity address haddress)
    (cwRecursive_isParentFineLegal_of_mem_selected_support
      K q term hmultiplicity address haddress)

/-- In every orientation, the concrete finite child-shape word reproduces the complete coarse
word used by recursive hashing and compatibility. -/
theorem cwRecursiveChildCompatibilityModel_coarse_logicalAddress_eq_shapeWord
    (K : Type u) [CommRing K] (q : ℕ) {Part : Type v} {depth n : ℕ}
    (part : Part)
    (term : ExactInterfaceTermParameters (depth + 1))
    (hmultiplicity : term.multiplicity = n + 1) (sigma : Orientation)
    (address : BlockAddress (fun _c ↦
      PositiveWord (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n))
    (haddress : address ∈
      (cwSelectedExactInterfaceTerm K q term hmultiplicity).support) :
    (cwRecursiveChildCompatibilityModel depth n (fun _ ↦ part)).coarse
        (logicalAddress sigma address) =
      RecursiveChildShape.toCoarseIndex part ∘
        cwRecursiveOrientedChildShapeWord
          K q part term hmultiplicity sigma address haddress := by
  exact recursiveChildCompatibilityModel_coarse_eq_shapeWord
    (fun _c ↦ cwChunkSplitWord (depth + 1)) part (logicalAddress sigma address)
    (cwRecursiveLogicalParent term sigma)
    (cwRecursiveLogicalParent_total term sigma)
    (cwRecursive_parentWeight_logicalAddress_of_mem_selected_support
      K q term hmultiplicity sigma address haddress)
    (cwRecursive_isParentFineLegal_logicalAddress_of_mem_selected_support
      K q term hmultiplicity sigma address haddress)

/-- Exact oriented occurrence profile.  In particular, a self-complementary child shape is
counted once as a left occurrence and once as a right occurrence, exactly as in Proposition 6.3. -/
theorem multiplicity_cwRecursiveOrientedChildShapeWord_apply
    (K : Type u) [CommRing K] (q : ℕ) {Part : Type v} {depth n : ℕ}
    (part : Part)
    (term : ExactInterfaceTermParameters (depth + 1))
    (hmultiplicity : term.multiplicity = n + 1) (sigma : Orientation)
    (address : BlockAddress (fun _c ↦
      PositiveWord (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n))
    (haddress : address ∈
      (cwSelectedExactInterfaceTerm K q term hmultiplicity).support)
    (child : RecursiveChildShape
      (cwRecursiveLogicalParent term sigma) (coarseTotal depth)) :
    WordType.multiplicity
        (cwRecursiveOrientedChildShapeWord
          K q part term hmultiplicity sigma address haddress) child =
      WordType.multiplicity
          (cwRecursiveOrientedLeftChildShapeWord
            K q part term hmultiplicity sigma address haddress) child +
        WordType.multiplicity
          (cwRecursiveOrientedLeftChildShapeWord
            K q part term hmultiplicity sigma address haddress)
          ((RecursiveChildShape.complementPerm
            (cwRecursiveLogicalParent_total term sigma)).symm child) := by
  exact WordType.multiplicity_append_complement_apply
    (RecursiveChildShape.complementPerm (cwRecursiveLogicalParent_total term sigma))
    (cwRecursiveOrientedLeftChildShapeWord
      K q part term hmultiplicity sigma address haddress) child

/-- Imposing the certificate's exact ordered split type on the left children forces the literal
full child-occurrence law in every oriented region. -/
theorem multiplicity_cwRecursiveOrientedChildShapeWord_eq_of_leftType
    (K : Type u) [CommRing K] (q : ℕ) {Part : Type v} {depth n : ℕ}
    (part : Part)
    (term : ExactInterfaceTermParameters (depth + 1))
    (hmultiplicity : term.multiplicity = n + 1) (sigma : Orientation)
    (address : BlockAddress (fun _c ↦
      PositiveWord (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n))
    (haddress : address ∈
      (cwSelectedExactInterfaceTerm K q term hmultiplicity).support)
    (alphaCounts : RecursiveChildShape
      (cwRecursiveLogicalParent term sigma) (coarseTotal depth) → ℕ)
    (hleft : WordType.multiplicity
      (cwRecursiveOrientedLeftChildShapeWord
        K q part term hmultiplicity sigma address haddress) = alphaCounts) :
    WordType.multiplicity
        (cwRecursiveOrientedChildShapeWord
          K q part term hmultiplicity sigma address haddress) =
      fun child ↦ alphaCounts child +
        alphaCounts ((RecursiveChildShape.complementPerm
          (cwRecursiveLogicalParent_total term sigma)).symm child) := by
  funext child
  rw [multiplicity_cwRecursiveOrientedChildShapeWord_apply]
  simp only [hleft]

/-- The exact ordered split counts necessarily sum to the number of parent occurrences. -/
theorem sum_alphaCounts_eq_of_cwRecursiveOrientedLeftChildType
    (K : Type u) [CommRing K] (q : ℕ) {Part : Type v} {depth n : ℕ}
    (part : Part)
    (term : ExactInterfaceTermParameters (depth + 1))
    (hmultiplicity : term.multiplicity = n + 1) (sigma : Orientation)
    (address : BlockAddress (fun _c ↦
      PositiveWord (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n))
    (haddress : address ∈
      (cwSelectedExactInterfaceTerm K q term hmultiplicity).support)
    (alphaCounts : RecursiveChildShape
      (cwRecursiveLogicalParent term sigma) (coarseTotal depth) → ℕ)
    (hleft : WordType.multiplicity
      (cwRecursiveOrientedLeftChildShapeWord
        K q part term hmultiplicity sigma address haddress) = alphaCounts) :
    (∑ child, alphaCounts child) = n + 1 := by
  rw [← hleft]
  exact WordType.sum_multiplicity
    (cwRecursiveOrientedLeftChildShapeWord
      K q part term hmultiplicity sigma address haddress)

/-- Certificate-facing predicate: the selected CW address has the prescribed exact ordered
left-child split type in one oriented region. -/
def CWRecursiveOrientedMatchesLeftChildType
    (K : Type u) [CommRing K] (q : ℕ) {Part : Type v} {depth n : ℕ}
    (part : Part)
    (term : ExactInterfaceTermParameters (depth + 1))
    (hmultiplicity : term.multiplicity = n + 1) (sigma : Orientation)
    (address : BlockAddress (fun _c ↦
      PositiveWord (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n))
    (haddress : address ∈
      (cwSelectedExactInterfaceTerm K q term hmultiplicity).support)
    (alpha : ExactRecursiveSplitType
      (cwRecursiveLogicalParent term sigma) (coarseTotal depth) (n + 1)) : Prop :=
  WordType.multiplicity
    (cwRecursiveOrientedLeftChildShapeWord
      K q part term hmultiplicity sigma address haddress) = alpha.count

/-- A CW address satisfying its exact ordered split type has exactly the paper's full labelled
child-occurrence profile. -/
theorem multiplicity_cwRecursiveOrientedChildShapeWord_eq_occurrenceCount
    (K : Type u) [CommRing K] (q : ℕ) {Part : Type v} {depth n : ℕ}
    (part : Part)
    (term : ExactInterfaceTermParameters (depth + 1))
    (hmultiplicity : term.multiplicity = n + 1) (sigma : Orientation)
    (address : BlockAddress (fun _c ↦
      PositiveWord (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n))
    (haddress : address ∈
      (cwSelectedExactInterfaceTerm K q term hmultiplicity).support)
    (alpha : ExactRecursiveSplitType
      (cwRecursiveLogicalParent term sigma) (coarseTotal depth) (n + 1))
    (hmatches : CWRecursiveOrientedMatchesLeftChildType
      K q part term hmultiplicity sigma address haddress alpha) :
    WordType.multiplicity
        (cwRecursiveOrientedChildShapeWord
          K q part term hmultiplicity sigma address haddress) =
      alpha.occurrenceCount (cwRecursiveLogicalParent_total term sigma) := by
  exact multiplicity_cwRecursiveOrientedChildShapeWord_eq_of_leftType
    K q part term hmultiplicity sigma address haddress alpha.count hmatches

end AlgebraicComplexity.Examples
