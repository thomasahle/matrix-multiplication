/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.InterfaceTensorWordCore
import AlgebraicComplexity.Tensor.Leg

set_option autoImplicit false

/-!
# Lightweight exact compatibility targets

This module isolates the finite data shared by complete-split compatibility arguments: tagged
coarse indices, exact cell multiplicities, and the exact and pooled target tables prescribed on
the three tensor legs.  It also records the target support conditions used to recover a coarse
coordinate from an observed split word.  Keeping this core independent of tensor cleanup and
asymptotic counting lets exact-target clients state their finite obligations without importing the
full Coppersmith--Winograd extraction stack.

The target tables transcribe the exact and pooled complete-split conditions in
[alman2025more], Claim 6.18 (`papers/sources/2404.16349/constituent.tex:404-429`), using the
integer multiplicities of the complete-split definition
(`papers/sources/2404.16349/prelim.tex:249-269`).  This module proves only elementary finite data
laws; compatibility soundness and counting remain in downstream modules.
-/

namespace AlgebraicComplexity
namespace MoreAsymmetryCompatibility

open Tensor

universe u v

/-- A tagged coarse constituent coordinate.  The tag is trivial in the global stage and records
the surrounding interface term in the recursive constituent stage. -/
structure CoarseIndex (Part : Type u) where
  part : Part
  x : ℕ
  y : ℕ
  z : ℕ
  deriving DecidableEq

/-- Coarse indices are determined by their tag and three coordinate values. -/
@[ext] theorem CoarseIndex.ext {Part : Type u} {left right : CoarseIndex Part}
    (hpart : left.part = right.part) (hx : left.x = right.x)
    (hy : left.y = right.y) (hz : left.z = right.z) : left = right := by
  cases left
  cases right
  simp_all

/-- Read one coordinate of a coarse constituent index. -/
def CoarseIndex.get {Part : Type u} (q : CoarseIndex Part) : Leg → ℕ
  | .X => q.x
  | .Y => q.y
  | .Z => q.z

/-- Exact multiplicity of `symbol` among the positions assigned to `cell`. -/
noncomputable def cellMultiplicity {ι Cell Symbol : Type*}
    [Fintype ι] [DecidableEq Cell] [DecidableEq Symbol]
    (cellOf : ι → Cell) (word : ι → Symbol) (cell : Cell) (symbol : Symbol) : ℕ := by
  classical
  exact (Finset.univ.filter fun position ↦
    cellOf position = cell ∧ word position = symbol).card

/-- One observed `(cell, symbol)` pair contributes positively to its empirical multiplicity. -/
theorem cellMultiplicity_pos_of_apply_eq
    {I Cell Symbol : Type*} [Fintype I]
    [DecidableEq Cell] [DecidableEq Symbol]
    (cellOf : I → Cell) (word : I → Symbol) (position : I)
    (cell : Cell) (symbol : Symbol)
    (hcell : cellOf position = cell) (hsymbol : word position = symbol) :
    0 < cellMultiplicity cellOf word cell symbol := by
  classical
  unfold cellMultiplicity
  rw [Finset.card_pos]
  exact ⟨position, by simp [hcell, hsymbol]⟩

/-- Total digit weight of a legal depth-`depth` CW chunk triple. -/
def coarseTotal (depth : ℕ) : ℕ := 2 ^ (depth + 1)

/-- Exact, denominator-free profile tables used by the two compatibility predicates.  The three
boundary identities are the finite form of the paper's required complete-split symmetries. -/
structure CompatibilityTargets (Part : Type u) (depth : ℕ) where
  xExact : CoarseIndex Part → SplitWord depth → ℕ
  yExact : CoarseIndex Part → SplitWord depth → ℕ
  zExact : CoarseIndex Part → SplitWord depth → ℕ
  yPooled : Part → ℕ → SplitWord depth → ℕ
  zPooled : Part → ℕ → SplitWord depth → ℕ
  yBoundary : ∀ q, q.z = 0 → ∀ word,
    yExact q word = xExact q (complementSplitWord word)
  zBoundaryOfX : ∀ q, q.y = 0 → ∀ word,
    zExact q word = xExact q (complementSplitWord word)
  zBoundaryOfY : ∀ q, q.x = 0 → ∀ word,
    zExact q word = yExact q (complementSplitWord word)

namespace CompatibilityTargets

variable {Part : Type u} {depth : ℕ}

/-- Select the exact per-cell target table for a logical tensor leg. -/
def exactProfile {Part : Type v} {depth : ℕ}
    (targets : CompatibilityTargets Part depth) :
    Leg → CoarseIndex Part → SplitWord depth → ℕ
  | .X => targets.xExact
  | .Y => targets.yExact
  | .Z => targets.zExact

/-- On the `X` leg the exact profile selector returns the `X` target table. -/
@[simp] theorem exactProfile_X {Part : Type v} {depth : ℕ}
    (targets : CompatibilityTargets Part depth) :
    targets.exactProfile .X = targets.xExact :=
  rfl

/-- On the `Y` leg the exact profile selector returns the `Y` target table. -/
@[simp] theorem exactProfile_Y {Part : Type v} {depth : ℕ}
    (targets : CompatibilityTargets Part depth) :
    targets.exactProfile .Y = targets.yExact :=
  rfl

/-- On the `Z` leg the exact profile selector returns the `Z` target table. -/
@[simp] theorem exactProfile_Z {Part : Type v} {depth : ℕ}
    (targets : CompatibilityTargets Part depth) :
    targets.exactProfile .Z = targets.zExact :=
  rfl

/-- Every raw symbol with positive prescribed exact `X` multiplicity has the coarse
logical-`X` value of its constituent. -/
def IsXWeightSupported
    (targets : CompatibilityTargets Part depth) : Prop :=
  ∀ q word, 0 < targets.xExact q word →
    splitWordWeight word = q.x

/-- The exact and pooled raw `Y` profiles are supported on split words of the coordinate
recorded by their cells. -/
def IsYWeightSupported
    (targets : CompatibilityTargets Part depth) : Prop :=
  (∀ q word, 0 < targets.yExact q word →
      splitWordWeight word = q.y) ∧
    (∀ part total word, 0 < targets.yPooled part total word →
      splitWordWeight word = total)

/-- The exact and pooled raw `Z` profiles are supported on split words of the coordinate
recorded by their cells. -/
def IsZWeightSupported
    (targets : CompatibilityTargets Part depth) : Prop :=
  (∀ q word, 0 < targets.zExact q word →
      splitWordWeight word = q.z) ∧
    (∀ part total word, 0 < targets.zPooled part total word →
      splitWordWeight word = total)

/-- All split-word support invariants expected of compatibility targets reconstructed from
complete-split profiles. -/
def IsWeightSupported
    (targets : CompatibilityTargets Part depth) : Prop :=
  targets.IsXWeightSupported ∧
    targets.IsYWeightSupported ∧
    targets.IsZWeightSupported

end CompatibilityTargets

end MoreAsymmetryCompatibility
end AlgebraicComplexity
