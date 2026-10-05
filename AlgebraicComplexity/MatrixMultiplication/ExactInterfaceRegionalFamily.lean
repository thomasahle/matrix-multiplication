/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.InterfaceTensorRegionalDivisionFamily

/-!
# Exact regional families with one constituent index

The global and recursive CW constructions divide one exact interface term among finitely many
labelled regions.  Every region has the same constituent index, while its multiplicity and three
complete-split profiles may differ.  This module packages precisely that finite datum and turns
its binary parenthesization into `ExactInterfaceTermDivisionTree`.

Parent terms are computed by adding the child profiles.  Consequently the binary-division laws
are definitional consequences of `CompleteSplitProfile.add`; no independently asserted parent
profile or assembled tensor restriction enters the construction.  The six-leaf constructor is
only a convenient parenthesization of six labelled regions.  It records neither orientations nor
a distinctness condition, so clients may attach any six orientations, including repetitions, to
the leaves before supplying their local extraction stages.
-/

namespace AlgebraicComplexity

open Tensor

/-- One regional exact-interface term whose constituent index is fixed by the ambient family.

The multiplicity case is stored explicitly so a zero region remains the canonical tensor unit and
a positive client retains its exact predecessor/equality witness. -/
structure ExactInterfaceRegionalLeaf {depth : ℕ} (index : LevelConstituentIndex depth) where
  multiplicity : ℕ
  split : ∀ c, CompleteSplitProfile depth (index.count c) multiplicity
  multiplicityCase : ExactInterfaceTermMultiplicityCase
    { multiplicity := multiplicity, index := index, split := split }

namespace ExactInterfaceRegionalLeaf

variable {depth : ℕ} {index : LevelConstituentIndex depth}

/-- Forget the fixed-index packaging and obtain the ordinary exact interface term. -/
def toTerm (leaf : ExactInterfaceRegionalLeaf index) : ExactInterfaceTermParameters depth where
  multiplicity := leaf.multiplicity
  index := index
  split := leaf.split

@[simp] theorem toTerm_multiplicity (leaf : ExactInterfaceRegionalLeaf index) :
    leaf.toTerm.multiplicity = leaf.multiplicity :=
  rfl

@[simp] theorem toTerm_index (leaf : ExactInterfaceRegionalLeaf index) :
    leaf.toTerm.index = index :=
  rfl

@[simp] theorem toTerm_split (leaf : ExactInterfaceRegionalLeaf index) (c : Leg) :
    leaf.toTerm.split c = leaf.split c :=
  rfl

end ExactInterfaceRegionalLeaf

/-- A binary parenthesization of finitely many regional profiles sharing one constituent index. -/
inductive ExactInterfaceRegionalFamily {depth : ℕ} (index : LevelConstituentIndex depth) where
  | leaf (regionalLeaf : ExactInterfaceRegionalLeaf index)
  | branch (left right : ExactInterfaceRegionalFamily index)

namespace ExactInterfaceRegionalFamily

variable {depth : ℕ} {index : LevelConstituentIndex depth}

/-- Total sample multiplicity of all leaves in a regional family. -/
def multiplicity : ExactInterfaceRegionalFamily index → ℕ
  | .leaf regionalLeaf => regionalLeaf.multiplicity
  | .branch left right => left.multiplicity + right.multiplicity

/-- Sum of all regional complete-split profiles, with the same parenthesization as the family. -/
def split (family : ExactInterfaceRegionalFamily index) :
    ∀ c, CompleteSplitProfile depth (index.count c) family.multiplicity :=
  match family with
  | .leaf regionalLeaf => regionalLeaf.split
  | .branch left right => fun c => (left.split c).add (right.split c)

/-- The exact parent term obtained by summing every regional leaf. -/
def toTerm (family : ExactInterfaceRegionalFamily index) : ExactInterfaceTermParameters depth where
  multiplicity := family.multiplicity
  index := index
  split := family.split

@[simp] theorem toTerm_multiplicity (family : ExactInterfaceRegionalFamily index) :
    family.toTerm.multiplicity = family.multiplicity :=
  rfl

@[simp] theorem toTerm_index (family : ExactInterfaceRegionalFamily index) :
    family.toTerm.index = index :=
  rfl

@[simp] theorem toTerm_split (family : ExactInterfaceRegionalFamily index) (c : Leg) :
    family.toTerm.split c = family.split c :=
  rfl

/-- The exact binary division computed by one branch of a regional family. -/
def branchDivision (left right : ExactInterfaceRegionalFamily index) :
    ExactInterfaceTermBinaryDivision (ExactInterfaceRegionalFamily.branch left right).toTerm where
  leftMultiplicity := left.multiplicity
  rightMultiplicity := right.multiplicity
  multiplicity_eq := rfl
  leftSplit := left.split
  rightSplit := right.split
  split_counts_eq := by
    intro c word
    rfl

@[simp] theorem branchDivision_leftTerm (left right : ExactInterfaceRegionalFamily index) :
    (branchDivision left right).leftTerm = left.toTerm :=
  rfl

@[simp] theorem branchDivision_rightTerm (left right : ExactInterfaceRegionalFamily index) :
    (branchDivision left right).rightTerm = right.toTerm :=
  rfl

/-- Convert the computed regional hierarchy into the exact division tree used by tensor assembly. -/
def toDivisionTree : (family : ExactInterfaceRegionalFamily index) →
    ExactInterfaceTermDivisionTree family.toTerm
  | .leaf regionalLeaf => .leaf regionalLeaf.multiplicityCase
  | .branch left right =>
      .branch (branchDivision left right) left.toDivisionTree right.toDivisionTree

/-- The conventional balanced parenthesization of six labelled regions.

The inputs are ordered labels, not orientations.  In particular, this constructor is unchanged
when two or more regions later receive the same orientation. -/
def six
    (r₁ r₂ r₃ r₄ r₅ r₆ : ExactInterfaceRegionalFamily index) :
    ExactInterfaceRegionalFamily index :=
  .branch (.branch r₁ (.branch r₂ r₃)) (.branch r₄ (.branch r₅ r₆))

@[simp] theorem six_multiplicity
    (r₁ r₂ r₃ r₄ r₅ r₆ : ExactInterfaceRegionalFamily index) :
    (six r₁ r₂ r₃ r₄ r₅ r₆).multiplicity =
      (r₁.multiplicity + (r₂.multiplicity + r₃.multiplicity)) +
        (r₄.multiplicity + (r₅.multiplicity + r₆.multiplicity)) :=
  rfl

end ExactInterfaceRegionalFamily

end AlgebraicComplexity
