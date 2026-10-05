/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import Init

/-!
# Executable schema definitions for simplified-volume certificates

This module contains only the finite data structures and executable validity predicates used by
generated certificate literals.  It deliberately avoids the semantic probability-table adapters
in `SimplifiedVolumeSchema.lean`.  Exact checkers which only inspect arrays and natural numbers can
therefore load the certificate schema without importing real analysis or the probability library.
-/

namespace MatrixMultiplication.Generated.SimplifiedVolume

/-! ## Small executable list predicates -/

/-- Every entry of a finite list satisfies `predicate`.

This local definition avoids importing the theorem-heavy Mathlib list API into generated exact
checkers. -/
def All {α : Type} (predicate : α → Prop) : List α → Prop
  | [] => True
  | value :: values => predicate value ∧ All predicate values

/-- Pointwise relation between two lists of the same length. -/
def All₂ {α β : Type} (relation : α → β → Prop) : List α → List β → Prop
  | [], [] => True
  | left :: lefts, right :: rights => relation left right ∧ All₂ relation lefts rights
  | _, _ => False

private def allDecidable {α : Type} (predicate : α → Prop)
    [∀ value, Decidable (predicate value)] : ∀ values : List α, Decidable (All predicate values)
  | [] => isTrue trivial
  | value :: values =>
      match (inferInstance : Decidable (predicate value)), allDecidable predicate values with
      | isTrue hvalue, isTrue hvalues => isTrue ⟨hvalue, hvalues⟩
      | isFalse hvalue, _ => isFalse fun h => hvalue h.1
      | _, isFalse hvalues => isFalse fun h => hvalues h.2

instance {α : Type} (predicate : α → Prop) [∀ value, Decidable (predicate value)]
    (values : List α) : Decidable (All predicate values) :=
  allDecidable predicate values

private def all₂Decidable {α β : Type} (relation : α → β → Prop)
    [∀ left right, Decidable (relation left right)] :
    ∀ lefts : List α, ∀ rights : List β, Decidable (All₂ relation lefts rights)
  | [], [] => isTrue trivial
  | left :: lefts, right :: rights =>
      match (inferInstance : Decidable (relation left right)),
          all₂Decidable relation lefts rights with
      | isTrue hhead, isTrue htail => isTrue ⟨hhead, htail⟩
      | isFalse hhead, _ => isFalse fun h => hhead h.1
      | _, isFalse htail => isFalse fun h => htail h.2
  | [], _ :: _ => isFalse id
  | _ :: _, [] => isFalse id

instance {α β : Type} (relation : α → β → Prop)
    [∀ left right, Decidable (relation left right)] (lefts : List α) (rights : List β) :
    Decidable (All₂ relation lefts rights) :=
  all₂Decidable relation lefts rights

namespace All

/-- A member of a list satisfying `All predicate` satisfies `predicate`. -/
theorem of_mem {α : Type} {predicate : α → Prop} {value : α} :
    ∀ {values : List α}, All predicate values → value ∈ values → predicate value
  | _ :: _, ⟨hhead, _⟩, .head _ => hhead
  | _ :: _, ⟨_, htail⟩, .tail _ hmem => of_mem htail hmem

end All

namespace All₂

/-- Read the pointwise relation at a common valid list index. -/
theorem get {α β : Type} {relation : α → β → Prop} :
    ∀ {lefts : List α} {rights : List β}, All₂ relation lefts rights →
      ∀ index (hleft : index < lefts.length) (hright : index < rights.length),
        relation (lefts.get ⟨index, hleft⟩) (rights.get ⟨index, hright⟩)
  | _ :: _, _ :: _, ⟨hhead, _⟩, 0, _, _ => hhead
  | _ :: _lefts, _ :: _rights, ⟨_, htail⟩, index + 1, hleft, hright =>
      get htail index (Nat.lt_of_succ_lt_succ hleft) (Nat.lt_of_succ_lt_succ hright)

end All₂

/-- Linear-time executable check that a serialized natural-number index map is strictly sorted. -/
def StrictlyIncreasing : List Nat → Prop
  | [] => True
  | [_] => True
  | first :: second :: rest =>
      first < second ∧ StrictlyIncreasing (second :: rest)

/-- Computable decision procedure following the adjacent comparisons exactly once. -/
def strictlyIncreasingDecidable : ∀ indices : List Nat, Decidable (StrictlyIncreasing indices)
  | [] => isTrue trivial
  | [_] => isTrue trivial
  | first :: second :: rest =>
      match (inferInstance : Decidable (first < second)),
          strictlyIncreasingDecidable (second :: rest) with
      | isTrue hfirst, isTrue hrest => isTrue ⟨hfirst, hrest⟩
      | isFalse hfirst, _ => isFalse fun h => hfirst h.1
      | _, isFalse hrest => isFalse fun h => hrest h.2

instance (indices : List Nat) : Decidable (StrictlyIncreasing indices) :=
  strictlyIncreasingDecidable indices

/-- A member of the tail of a strictly increasing list is larger than its head. -/
theorem head_lt_of_mem_tail {head value : Nat} {tail : List Nat}
    (hsorted : StrictlyIncreasing (head :: tail)) (hmem : value ∈ tail) :
    head < value := by
  induction tail generalizing head with
  | nil => simp at hmem
  | cons next tail ih =>
      simp only [StrictlyIncreasing] at hsorted
      rcases hsorted with ⟨hhead, htail⟩
      simp only [List.mem_cons] at hmem
      rcases hmem with rfl | hmem
      · exact hhead
      · exact Nat.lt_trans hhead (ih htail hmem)

/-- A strictly increasing serialized index map is injective. -/
theorem strictlyIncreasing_nodup {indices : List Nat}
    (hsorted : StrictlyIncreasing indices) : indices.Nodup := by
  induction indices with
  | nil => simp
  | cons head tail ih =>
      constructor
      · intro value hmem heq
        subst value
        exact (Nat.lt_irrefl head) (head_lt_of_mem_tail hsorted hmem)
      · apply ih
        cases tail with
        | nil => trivial
        | cons next tail => exact hsorted.2

/-- Safely read one nested natural-number row. -/
def natRow (rows : Array (Array Nat)) (index : Nat) : Array Nat :=
  rows[index]?.getD #[]

/-- A chunk of positive coordinates from one globally normalized sparse distribution. -/
structure SparseMassChunk where
  atomIndices : Array Nat
  numerators : Array Nat

namespace SparseMassChunk

/-- Number of serialized positive coordinates. -/
def valueCount (data : SparseMassChunk) : Nat := data.numerators.size

/-- Exact numerator subtotal carried by this chunk. -/
def total (data : SparseMassChunk) : Nat := data.numerators.toList.sum

/-- Exact shape, positivity, and injective ambient-index checks for a mass chunk. -/
def IsValid (ambientAtoms lower upper : Nat) (data : SparseMassChunk) : Prop :=
  data.atomIndices.size = data.numerators.size ∧
  StrictlyIncreasing data.atomIndices.toList ∧
  All (fun index => lower ≤ index ∧ index < upper ∧ index < ambientAtoms)
    data.atomIndices.toList ∧
  All (fun numerator => 0 < numerator) data.numerators.toList

end SparseMassChunk

/-- Sparse dyadic rows together with their exact ambient row and symbol maps. -/
structure SparseDyadicChunk where
  rowIndices : Array Nat
  supportRows : Array (Array Nat)
  numeratorRows : Array (Array Nat)

namespace SparseDyadicChunk

/-- The support map for one local row, with an empty fallback for malformed data. -/
def supportRow (data : SparseDyadicChunk) (row : Fin data.rowIndices.size) : Array Nat :=
  natRow data.supportRows row.val

/-- The positive numerator list for one local row, with an empty fallback for malformed data. -/
def numeratorRow (data : SparseDyadicChunk) (row : Fin data.rowIndices.size) : Array Nat :=
  natRow data.numeratorRows row.val

/-- Row-dependent compressed alphabet width. -/
def width (data : SparseDyadicChunk) (row : Fin data.rowIndices.size) : Nat :=
  (data.supportRow row).size

/-- Number of serialized positive coordinates. -/
def valueCount (data : SparseDyadicChunk) : Nat :=
  (data.numeratorRows.toList.map Array.size).sum

/-- Exact shape, simplex, support-map, and ambient-row-index checks. -/
def IsValid (bits ambientRows ambientSymbols lower upper : Nat)
    (data : SparseDyadicChunk) : Prop :=
  data.supportRows.size = data.rowIndices.size ∧
  data.numeratorRows.size = data.rowIndices.size ∧
  StrictlyIncreasing data.rowIndices.toList ∧
  All (fun row => lower ≤ row ∧ row < upper ∧ row < ambientRows)
    data.rowIndices.toList ∧
  All (fun support =>
    StrictlyIncreasing support.toList ∧
    All (fun symbol => symbol < ambientSymbols) support.toList)
    data.supportRows.toList ∧
  All₂ (fun numerators support =>
      numerators.size = support.size ∧
      All (fun numerator => 0 < numerator) numerators.toList)
    data.numeratorRows.toList data.supportRows.toList ∧
  All (fun numerators => numerators.toList.sum = 2 ^ bits) data.numeratorRows.toList

/-- Read the ambient row represented by a local dictionary row. -/
def ambientRow (data : SparseDyadicChunk) (row : Fin data.rowIndices.size) : Nat :=
  data.rowIndices[row]

/-- Read the ambient symbol represented by a local compressed symbol. -/
def ambientSymbol (data : SparseDyadicChunk) (row : Fin data.rowIndices.size)
    (symbol : Fin (data.width row)) : Nat :=
  (data.supportRow row)[symbol.val]'(by simpa [width] using symbol.isLt)

end SparseDyadicChunk

/-- Sparse scalar parameters with a shared dyadic denominator. -/
structure SparseScalarChunk where
  scalarIndices : Array Nat
  numerators : Array Nat

namespace SparseScalarChunk

/-- Number of serialized positive scalar coordinates. -/
def valueCount (data : SparseScalarChunk) : Nat := data.numerators.size

/-- Exact index-map and open-interval checks for the positive-edge parameter `mu`. -/
def IsValid (bits ambientScalars lower upper : Nat) (data : SparseScalarChunk) : Prop :=
  data.scalarIndices.size = data.numerators.size ∧
  StrictlyIncreasing data.scalarIndices.toList ∧
  All (fun index => lower ≤ index ∧ index < upper ∧ index < ambientScalars)
    data.scalarIndices.toList ∧
  All (fun numerator => 0 < numerator ∧ numerator < 2 ^ bits / 2)
    data.numerators.toList

end SparseScalarChunk

/-- Exact IEEE-754 binary32 payload rows for maximum-entropy dual witnesses. -/
structure Float32BitsChunk where
  rowIndices : Array Nat
  bitRows : Array (Array Nat)

namespace Float32BitsChunk

/-- Number of serialized binary32 coordinates. -/
def valueCount (data : Float32BitsChunk) : Nat :=
  (data.bitRows.toList.map Array.size).sum

/-- The exponent field of a binary32 payload. -/
def exponentField (bits : Nat) : Nat := bits / (2 ^ 23) % (2 ^ 8)

/-- Exact row shape, finite-payload, and ambient-index checks for dual rows. -/
def IsValid (width ambientRows lower upper : Nat) (data : Float32BitsChunk) : Prop :=
  data.bitRows.size = data.rowIndices.size ∧
  StrictlyIncreasing data.rowIndices.toList ∧
  All (fun row => lower ≤ row ∧ row < upper ∧ row < ambientRows)
    data.rowIndices.toList ∧
  All (fun row => row.size = width ∧
    All (fun bits => bits < 2 ^ 32 ∧ exponentField bits < 255) row.toList)
    data.bitRows.toList

end Float32BitsChunk

end MatrixMultiplication.Generated.SimplifiedVolume
