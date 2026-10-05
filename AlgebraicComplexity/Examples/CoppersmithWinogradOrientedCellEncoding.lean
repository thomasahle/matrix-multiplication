/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinogradCompatibilityTargetFiber
import AlgebraicComplexity.Combinatorics.WordType

/-!
# Encoding tagged oriented CW cell words

A full tagged coarse-cell type is counted as an ordinary word type, while the compatibility
extraction consumes a position-label function together with a three-leg coarse address.  These
are not merely equinumerous: for every orientation they are canonically equivalent.

This module records that equivalence, transports a word type class across it, and proves that every
legal cell type is represented by an actual labelled address.  No tensor restriction, hashing
choice, asymptotic estimate, or certificate datum is involved.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor

universe v

/-- A tagged oriented coarse-cell word is equivalent to its position labels together with the
three physical-leg coarse words.

The inverse reads the physical leg `c` from the logical coordinate `sigma.symm c`.  The two inverse
laws therefore also fix the orientation convention used by the total-weight clients. -/
def cwOrientedFiniteCellEncodingEquiv (Part : Type v) (depth n : ℕ)
    (sigma : Orientation) :
    ((Fin (n + 1) → Part) ×
        BlockAddress (fun _c ↦ PositiveWord (CWCoarseDigit depth) n)) ≃
      (Fin (n + 1) → CWOrientedCoarseCell Part depth) where
  toFun encoded :=
    cwOrientedFiniteCellSequence depth n encoded.1 sigma encoded.2
  invFun cells :=
    (⟨fun sample ↦ (cells sample).1,
      fun physicalLeg ↦ (positiveWordEquiv (CWCoarseDigit depth) n).symm
        (fun sample ↦ (cells sample).2 (sigma.symm physicalLeg))⟩)
  left_inv := by
    rintro ⟨partAt, address⟩
    apply Prod.ext
    · rfl
    · funext physicalLeg
      apply (positiveWordEquiv (CWCoarseDigit depth) n).injective
      funext sample
      dsimp
      rw [Equiv.apply_symm_apply]
      exact congrArg
        (fun c ↦ (positiveWordEquiv (CWCoarseDigit depth) n) (address c) sample)
        (sigma.apply_symm_apply physicalLeg)
  right_inv := by
    intro cells
    funext sample
    apply Prod.ext
    · rfl
    · funext logicalLeg
      unfold cwOrientedFiniteCellSequence
      dsimp
      rw [Equiv.apply_symm_apply]
      exact congrArg (fun c ↦ (cells sample).2 c)
        (sigma.symm_apply_apply logicalLeg)

@[simp] theorem cwOrientedFiniteCellEncodingEquiv_apply
    (Part : Type v) (depth n : ℕ) (sigma : Orientation)
    (encoded : (Fin (n + 1) → Part) ×
      BlockAddress (fun _c ↦ PositiveWord (CWCoarseDigit depth) n)) :
    cwOrientedFiniteCellEncodingEquiv Part depth n sigma encoded =
      cwOrientedFiniteCellSequence depth n encoded.1 sigma encoded.2 :=
  rfl

/-- For the singleton tag alphabet, tagged cell words are equivalent to three-leg coarse
addresses alone.  This removes the otherwise explicit position-label component without changing
the type-class cardinality. -/
noncomputable def cwOrientedFiniteCellAddressEquivPUnit (depth n : ℕ)
    (sigma : Orientation) :
    BlockAddress (fun _c ↦ PositiveWord (CWCoarseDigit depth) n) ≃
      (Fin (n + 1) → CWOrientedCoarseCell PUnit depth) :=
  Equiv.ofBijective
    (fun address ↦
      cwOrientedFiniteCellSequence depth n (fun _ ↦ PUnit.unit) sigma address)
    ⟨by
      intro left right h
      let encoding := cwOrientedFiniteCellEncodingEquiv PUnit depth n sigma
      have hpairs :
          encoding ((fun _ ↦ PUnit.unit), left) =
            encoding ((fun _ ↦ PUnit.unit), right) := h
      exact congrArg Prod.snd (encoding.injective hpairs),
    by
      intro cells
      let encoding := cwOrientedFiniteCellEncodingEquiv PUnit depth n sigma
      let encoded := encoding.symm cells
      refine ⟨encoded.2, ?_⟩
      have hpartAt : encoded.1 = fun _ ↦ PUnit.unit := Subsingleton.elim _ _
      have hinverse :
          cwOrientedFiniteCellSequence depth n encoded.1 sigma encoded.2 = cells := by
        have h := encoding.apply_symm_apply cells
        change cwOrientedFiniteCellSequence depth n encoded.1 sigma encoded.2 = cells at h
        exact h
      simpa only [hpartAt] using hinverse⟩

@[simp] theorem cwOrientedFiniteCellAddressEquivPUnit_apply
    (depth n : ℕ) (sigma : Orientation)
    (address : BlockAddress (fun _c ↦ PositiveWord (CWCoarseDigit depth) n)) :
    cwOrientedFiniteCellAddressEquivPUnit depth n sigma address =
      cwOrientedFiniteCellSequence depth n (fun _ ↦ PUnit.unit) sigma address :=
  rfl

/-- The labelled coarse-address family having one prescribed full tagged oriented cell type.

It is defined by transporting the ordinary word type class through the inverse encoding
equivalence.  Consequently its cardinality is definitionally protected from an accidental extra
factor for position labels or tensor legs. -/
noncomputable def cwOrientedFullCellTypeFamily
    (Part : Type v) [Fintype Part] [DecidableEq Part]
    (depth n : ℕ) (sigma : Orientation)
    (cellType : CWOrientedCoarseCell Part depth → ℕ) :
    Finset ((Fin (n + 1) → Part) ×
      BlockAddress (fun _c ↦ PositiveWord (CWCoarseDigit depth) n)) :=
  (WordType.typeClass (n + 1) cellType).map
    (cwOrientedFiniteCellEncodingEquiv Part depth n sigma).symm.toEmbedding

@[simp] theorem mem_cwOrientedFullCellTypeFamily_iff
    (Part : Type v) [Fintype Part] [DecidableEq Part]
    (depth n : ℕ) (sigma : Orientation)
    (cellType : CWOrientedCoarseCell Part depth → ℕ)
    (encoded : (Fin (n + 1) → Part) ×
      BlockAddress (fun _c ↦ PositiveWord (CWCoarseDigit depth) n)) :
    encoded ∈ cwOrientedFullCellTypeFamily Part depth n sigma cellType ↔
      WordType.multiplicity
        (cwOrientedFiniteCellSequence depth n encoded.1 sigma encoded.2) = cellType := by
  simp [cwOrientedFullCellTypeFamily, WordType.mem_typeClass]

/-- Encoding does not change the size of a full tagged coarse-cell type class. -/
@[simp] theorem card_cwOrientedFullCellTypeFamily
    (Part : Type v) [Fintype Part] [DecidableEq Part]
    (depth n : ℕ) (sigma : Orientation)
    (cellType : CWOrientedCoarseCell Part depth → ℕ) :
    (cwOrientedFullCellTypeFamily Part depth n sigma cellType).card =
      (WordType.typeClass (n + 1) cellType).card := by
  simp [cwOrientedFullCellTypeFamily]

/-- Addresses with one prescribed full oriented cell type when there is no nontrivial position
tag. -/
noncomputable def cwOrientedFullCellTypeAddressesPUnit
    (depth n : ℕ) (sigma : Orientation)
    (cellType : CWOrientedCoarseCell PUnit depth → ℕ) :
    Finset (BlockAddress (fun _c ↦ PositiveWord (CWCoarseDigit depth) n)) :=
  (WordType.typeClass (n + 1) cellType).map
    (cwOrientedFiniteCellAddressEquivPUnit depth n sigma).symm.toEmbedding

@[simp] theorem mem_cwOrientedFullCellTypeAddressesPUnit_iff
    (depth n : ℕ) (sigma : Orientation)
    (cellType : CWOrientedCoarseCell PUnit depth → ℕ)
    (address : BlockAddress (fun _c ↦ PositiveWord (CWCoarseDigit depth) n)) :
    address ∈ cwOrientedFullCellTypeAddressesPUnit depth n sigma cellType ↔
      WordType.multiplicity
        (cwOrientedFiniteCellSequence depth n (fun _ ↦ PUnit.unit) sigma address) =
          cellType := by
  simp [cwOrientedFullCellTypeAddressesPUnit, WordType.mem_typeClass]

/-- With singleton position tags, the address family has exactly the ordinary cell type-class
cardinality. -/
@[simp] theorem card_cwOrientedFullCellTypeAddressesPUnit
    (depth n : ℕ) (sigma : Orientation)
    (cellType : CWOrientedCoarseCell PUnit depth → ℕ) :
    (cwOrientedFullCellTypeAddressesPUnit depth n sigma cellType).card =
      (WordType.typeClass (n + 1) cellType).card := by
  simp [cwOrientedFullCellTypeAddressesPUnit]

/-- Every legal tagged coarse-cell type is realized by concrete position labels and a concrete
three-leg coarse address. -/
theorem exists_partAt_address_multiplicity_eq_of_mem_types
    (Part : Type v) [Fintype Part] [DecidableEq Part]
    (depth n : ℕ) (sigma : Orientation)
    (cellType : CWOrientedCoarseCell Part depth → ℕ)
    (hcellType : cellType ∈ WordType.types (CWOrientedCoarseCell Part depth) (n + 1)) :
    ∃ (partAt : Fin (n + 1) → Part)
        (address : BlockAddress (fun _c ↦ PositiveWord (CWCoarseDigit depth) n)),
      WordType.multiplicity
        (cwOrientedFiniteCellSequence depth n partAt sigma address) = cellType := by
  obtain ⟨cells, hcells⟩ := WordType.typeClass_nonempty cellType hcellType
  let encoded := (cwOrientedFiniteCellEncodingEquiv Part depth n sigma).symm cells
  refine ⟨encoded.1, encoded.2, ?_⟩
  have hinverse :
      cwOrientedFiniteCellSequence depth n encoded.1 sigma encoded.2 = cells := by
    simpa only [cwOrientedFiniteCellEncodingEquiv_apply] using
      (cwOrientedFiniteCellEncodingEquiv Part depth n sigma).apply_symm_apply cells
  rw [hinverse]
  exact WordType.mem_typeClass.mp hcells

/-- With a singleton tag alphabet, every legal full-cell type is realized using the canonical
constant position labelling.  This is the form used by one-region depth-one clients. -/
theorem exists_address_multiplicity_eq_of_mem_types_pUnit
    (depth n : ℕ) (sigma : Orientation)
    (cellType : CWOrientedCoarseCell PUnit depth → ℕ)
    (hcellType : cellType ∈ WordType.types (CWOrientedCoarseCell PUnit depth) (n + 1)) :
    ∃ address : BlockAddress (fun _c ↦ PositiveWord (CWCoarseDigit depth) n),
      WordType.multiplicity
        (cwOrientedFiniteCellSequence depth n (fun _ ↦ PUnit.unit) sigma address) =
          cellType := by
  obtain ⟨cells, hcells⟩ := WordType.typeClass_nonempty cellType hcellType
  refine ⟨(cwOrientedFiniteCellAddressEquivPUnit depth n sigma).symm cells, ?_⟩
  rw [← cwOrientedFiniteCellAddressEquivPUnit_apply,
    (cwOrientedFiniteCellAddressEquivPUnit depth n sigma).apply_symm_apply]
  exact WordType.mem_typeClass.mp hcells

end AlgebraicComplexity.Examples
