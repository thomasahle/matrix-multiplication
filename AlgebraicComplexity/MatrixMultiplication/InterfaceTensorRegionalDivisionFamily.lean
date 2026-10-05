/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.InterfaceTensorRegionalDivisionZero

/-!
# Finite families of exact regional divisions

This module assembles the four binary regional-division cases into a paper-independent finite
tree API.  A leaf explicitly records whether its multiplicity is zero or positive.  Consequently,
zero-weight regions retain their correct tensor-unit semantics and are never represented by a
nonempty `PositiveWord`.

Every finite recursive family of binary regional divisions has the shape of
`ExactInterfaceTermDivisionTree`.  Its leaf target is the recursively parenthesized external
product of all selected leaf tensors.  The main theorem proves an exact restriction from the
selected root tensor to that leaf product; a second theorem starts directly from the appropriate
power of the common source tensor.
-/

namespace AlgebraicComplexity

open Tensor

universe u v w

/-- A multiplicity is either the tensor-unit exponent zero or a positive exponent with an
explicit predecessor. -/
inductive ExactInterfaceTermMultiplicityCase {depth : ℕ}
    (term : ExactInterfaceTermParameters depth) where
  | zero (hmultiplicity : term.multiplicity = 0)
  | positive (pred : ℕ) (hmultiplicity : term.multiplicity = pred + 1)

namespace ExactInterfaceTermMultiplicityCase

variable {depth : ℕ} {term : ExactInterfaceTermParameters depth}

/-- Every exact interface term has a canonical zero-or-positive multiplicity case. -/
def ofTerm (term : ExactInterfaceTermParameters depth) :
    ExactInterfaceTermMultiplicityCase term :=
  match h : term.multiplicity with
  | 0 => .zero h
  | n + 1 => .positive n h

end ExactInterfaceTermMultiplicityCase

section

variable {K : Type u} [CommSemiring K]
variable {depth : ℕ}
variable {A : Leg → Type w} [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]
variable {V : ∀ c, A c → Type (max u v)}
variable [∀ c a, AddCommMonoid (V c a)] [∀ c a, Module K (V c a)]

/-- Select an exact interface term at positive multiplicity and use the canonical tensor unit at
multiplicity zero. -/
noncomputable def Tensor.PartitionedTensor.exactInterfaceTermPowerRestriction
    (P : PartitionedTensor (K := K) (A := A) V)
    (encode : ∀ c, A c → SplitWord depth)
    {term : ExactInterfaceTermParameters depth}
    (multiplicityCase : ExactInterfaceTermMultiplicityCase term) :
    PowerRestriction.{u, max u (max v w), max u (max v w)} P.realize :=
  match multiplicityCase with
  | .zero hmultiplicity =>
      { exponent := term.multiplicity
        Target := LegModuleFamily.of.{u, max u (max v w)} (K := K)
          (PowerSpace K (PartitionedSpace K V) 0)
        target := Tensor.power P.realize 0
        restricts :=
          (Tensor.Isomorphic.power_congr P.realize hmultiplicity).restricts }
  | .positive _pred hmultiplicity =>
      let selected := P.selectEncodedExactInterfaceTerm encode term hmultiplicity
      { exponent := term.multiplicity
        Target := LegModuleFamily.of.{u, max u (max v w)} (K := K) _
        target := selected.realize
        restricts :=
          ((Tensor.Isomorphic.power_congr P.realize hmultiplicity).restricts).trans
            (Tensor.Restricts.power_selectEncodedExactInterfaceTerm
              P encode term hmultiplicity) }

@[simp] theorem Tensor.PartitionedTensor.exactInterfaceTermPowerRestriction_exponent
    (P : PartitionedTensor (K := K) (A := A) V)
    (encode : ∀ c, A c → SplitWord depth)
    {term : ExactInterfaceTermParameters depth}
    (multiplicityCase : ExactInterfaceTermMultiplicityCase term) :
    (P.exactInterfaceTermPowerRestriction encode multiplicityCase).exponent =
      term.multiplicity := by
  cases multiplicityCase <;>
    rfl

/-- Combine the multiplicity cases of two child regions into the induced parent case. -/
def ExactInterfaceTermBinaryDivision.combineMultiplicityCase
    {parent : ExactInterfaceTermParameters depth}
    (division : ExactInterfaceTermBinaryDivision parent)
    (leftCase : ExactInterfaceTermMultiplicityCase division.leftTerm)
    (rightCase : ExactInterfaceTermMultiplicityCase division.rightTerm) :
    ExactInterfaceTermMultiplicityCase parent :=
  match leftCase, rightCase with
  | .zero hleft, .zero hright =>
      .zero (division.parentMultiplicity_eq_zero hleft hright)
  | .zero hleft, .positive n hright =>
      .positive n (division.parentMultiplicity_eq_right_of_left_zero hleft hright)
  | .positive n hleft, .zero hright =>
      .positive n (division.parentMultiplicity_eq_left_of_right_zero hleft hright)
  | .positive n hleft, .positive m hright =>
      .positive (n + m + 1) (by
        have h := division.parentMultiplicity_eq hleft hright
        omega)

/-- Uniform binary regional division, including all zero-multiplicity boundary cases. -/
theorem Tensor.Restricts.exactInterfaceTermPowerRestriction_binaryDivision
    (P : PartitionedTensor (K := K) (A := A) V)
    (encode : ∀ c, A c → SplitWord depth)
    {parent : ExactInterfaceTermParameters depth}
    (division : ExactInterfaceTermBinaryDivision parent)
    (leftCase : ExactInterfaceTermMultiplicityCase division.leftTerm)
    (rightCase : ExactInterfaceTermMultiplicityCase division.rightTerm) :
    Restricts
      (P.exactInterfaceTermPowerRestriction encode
        (division.combineMultiplicityCase leftCase rightCase)).target
      (Tensor.external
        (P.exactInterfaceTermPowerRestriction encode leftCase).target
        (P.exactInterfaceTermPowerRestriction encode rightCase).target) := by
  cases leftCase with
  | zero hleft =>
      cases rightCase with
      | zero hright =>
          simp only [ExactInterfaceTermBinaryDivision.combineMultiplicityCase,
            Tensor.PartitionedTensor.exactInterfaceTermPowerRestriction]
          exact (Tensor.Isomorphic.powerZeroExternalLeft P.realize
            (Tensor.power P.realize 0)).symm.restricts
      | positive m hright =>
          change Restricts
            (P.selectEncodedExactInterfaceTerm encode parent
              (division.parentMultiplicity_eq_right_of_left_zero hleft hright)).realize
            (Tensor.external (Tensor.power P.realize 0)
              (P.selectEncodedExactInterfaceTerm encode division.rightTerm hright).realize)
          exact Tensor.Restricts.selectEncodedExactInterfaceTerm_binaryDivision_leftZero
            P encode division hleft hright
  | positive n hleft =>
      cases rightCase with
      | zero hright =>
          change Restricts
            (P.selectEncodedExactInterfaceTerm encode parent
              (division.parentMultiplicity_eq_left_of_right_zero hleft hright)).realize
            (Tensor.external
              (P.selectEncodedExactInterfaceTerm encode division.leftTerm hleft).realize
              (Tensor.power P.realize 0))
          exact Tensor.Restricts.selectEncodedExactInterfaceTerm_binaryDivision_rightZero
            P encode division hleft hright
      | positive m hright =>
          change Restricts
            (P.selectEncodedExactInterfaceTerm encode parent
              (division.parentMultiplicity_eq hleft hright)).realize
            (Tensor.external
              (P.selectEncodedExactInterfaceTerm encode division.leftTerm hleft).realize
              (P.selectEncodedExactInterfaceTerm encode division.rightTerm hright).realize)
          exact Tensor.Restricts.selectEncodedExactInterfaceTerm_binaryDivision
            P encode division hleft hright

/-- A finite rooted tree of exact binary regional divisions.  Leaves retain an explicit
zero-or-positive multiplicity case, so zero-weight regions never have to be encoded as
`PositiveWord`s. -/
inductive ExactInterfaceTermDivisionTree :
    ExactInterfaceTermParameters depth → Type where
  | leaf {term : ExactInterfaceTermParameters depth}
      (multiplicityCase : ExactInterfaceTermMultiplicityCase term) :
      ExactInterfaceTermDivisionTree term
  | branch {parent : ExactInterfaceTermParameters depth}
      (division : ExactInterfaceTermBinaryDivision parent)
      (left : ExactInterfaceTermDivisionTree division.leftTerm)
      (right : ExactInterfaceTermDivisionTree division.rightTerm) :
      ExactInterfaceTermDivisionTree parent

namespace ExactInterfaceTermDivisionTree

/-- The root multiplicity case induced recursively from the leaf cases. -/
def rootMultiplicityCase {term : ExactInterfaceTermParameters depth}
    (tree : ExactInterfaceTermDivisionTree term) :
    ExactInterfaceTermMultiplicityCase term :=
  match tree with
  | .leaf multiplicityCase => multiplicityCase
  | .branch division left right =>
      division.combineMultiplicityCase left.rootMultiplicityCase right.rootMultiplicityCase

/-- The recursively parenthesized external product of all selected leaf tensors, packaged as a
restriction of a power of the common partitioned tensor realization. -/
noncomputable def leafPowerRestriction
    (P : PartitionedTensor (K := K) (A := A) V)
    (encode : ∀ c, A c → SplitWord depth) :
    {term : ExactInterfaceTermParameters depth} →
      ExactInterfaceTermDivisionTree term →
      PowerRestriction.{u, max u (max v w), max u (max v w)} P.realize
  | _, .leaf multiplicityCase =>
      P.exactInterfaceTermPowerRestriction encode multiplicityCase
  | _, .branch _division left right =>
      (left.leafPowerRestriction P encode).external
        (right.leafPowerRestriction P encode)

/-- The source exponent of the assembled leaf product is exactly the root multiplicity. -/
theorem leafPowerRestriction_exponent
    (P : PartitionedTensor (K := K) (A := A) V)
    (encode : ∀ c, A c → SplitWord depth)
    {term : ExactInterfaceTermParameters depth}
    (tree : ExactInterfaceTermDivisionTree term) :
    (tree.leafPowerRestriction P encode).exponent = term.multiplicity := by
  induction tree with
  | leaf multiplicityCase =>
      cases multiplicityCase <;>
        rfl
  | branch division left right ihleft ihright =>
      rw [leafPowerRestriction, PowerRestriction.external_exponent,
        ihleft, ihright]
      exact division.multiplicity_eq.symm

end ExactInterfaceTermDivisionTree

/-- A selected exact root term restricts to the recursively parenthesized external product of
all selected leaves of a finite regional-division tree. -/
theorem Tensor.Restricts.exactInterfaceTermPowerRestriction_divisionTree
    (P : PartitionedTensor (K := K) (A := A) V)
    (encode : ∀ c, A c → SplitWord depth)
    {term : ExactInterfaceTermParameters depth}
    (tree : ExactInterfaceTermDivisionTree term) :
    Restricts
      (P.exactInterfaceTermPowerRestriction encode tree.rootMultiplicityCase).target
      (tree.leafPowerRestriction P encode).target := by
  induction tree with
  | leaf multiplicityCase =>
      exact Tensor.Restricts.refl _
  | branch division left right ihleft ihright =>
      exact
        (Tensor.Restricts.exactInterfaceTermPowerRestriction_binaryDivision
          P encode division left.rootMultiplicityCase right.rootMultiplicityCase).trans
        (ihleft.external ihright)

/-- Direct source-power form of finite recursive regional division. -/
theorem Tensor.Restricts.power_exactInterfaceTermDivisionTree
    (P : PartitionedTensor (K := K) (A := A) V)
    (encode : ∀ c, A c → SplitWord depth)
    {term : ExactInterfaceTermParameters depth}
    (tree : ExactInterfaceTermDivisionTree term) :
    Restricts (Tensor.power P.realize term.multiplicity)
      (tree.leafPowerRestriction P encode).target := by
  have h :=
    (P.exactInterfaceTermPowerRestriction encode tree.rootMultiplicityCase).restricts.trans
      (Tensor.Restricts.exactInterfaceTermPowerRestriction_divisionTree P encode tree)
  exact
    ((Tensor.Isomorphic.power_congr P.realize
      (P.exactInterfaceTermPowerRestriction_exponent
        encode tree.rootMultiplicityCase).symm).restricts).trans h

end

end AlgebraicComplexity
