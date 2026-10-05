/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.SegmentMultiplicityJointWord

set_option autoImplicit false

/-!
# Conditional types as segmented multiplicity restrictions

Layer 3 (`AlgebraicComplexity/MatrixMultiplication/`).  A conditional joint type over an arbitrary
finite cell alphabet is exactly a family of empirical multiplicities, one for each cell.  This
module supplies the canonical enumeration of cells and proves that spelling equivalence.

The result is an interface lemma rather than a new counting theorem.  Its intended client is the
fully path-tagged inner-stage construction for the Total-Weight method: there, the finite cell is a
complete recursive invocation path, and retaining the conditional joint type must mean retaining
the prescribed type separately on every path.  This is the distinction made by the family
`L_t(\boldsymbol{\tau})` in `better_bound/paper.tex:1715-1775`.  In the source proof, the analogous
complete-split condition appears in the definition of `P` and is then deliberately dropped only
for the upper bound on `Q` in Claim 6.18 of [alman2025more]
(`papers/sources/2404.16349/constituent.tex:376-440`).

No tensor restriction, compatibility count, asymptotic estimate, or Total-Weight certificate is
asserted here.
-/

namespace AlgebraicComplexity.WordType

universe u v

variable {Cell : Type u} {Symbol : Type v}

/-- Enumerate an arbitrary finite cell alphabet by `Fin` so that it can serve as the segment map
used by `segmentMultiplicity` and `SegmentedSplitRestriction`.

The enumeration is deliberately canonical only up to `Fintype.equivFin`; all public statements
translate back through the equivalence and hence do not depend on its concrete order. -/
noncomputable def finiteCellSegmentation [Fintype Cell] {n : ℕ}
    (source : Fin n → Cell) : Fin n → Fin (Fintype.card Cell) :=
  Fintype.equivFin Cell ∘ source

/-- The segment multiplicity at the enumerated cell is the corresponding entry of the original
joint-word multiplicity. -/
theorem segmentMultiplicity_finiteCellSegmentation
    [Fintype Cell] [DecidableEq Symbol]
    {n : ℕ} (source : Fin n → Cell) (word : Fin n → Symbol)
    (cell : Cell) (symbol : Symbol) :
    segmentMultiplicity (finiteCellSegmentation source) word
        (Fintype.equivFin Cell cell) symbol =
      multiplicity (jointWord source word) (cell, symbol) := by
  classical
  rw [multiplicity_eq_card_filter]
  unfold segmentMultiplicity finiteCellSegmentation jointWord
  congr 1
  ext i
  simp [Function.comp_apply]

/-- Membership in a conditional type class is equivalent to prescribing every segment's complete
multiplicity function.

The right-hand side keeps the cell label visible through `Fintype.equivFin.symm`; in particular,
two distinct invocation paths with numerically equal target profiles remain separate segments. -/
theorem mem_conditionalTypeClass_iff_segmentMultiplicity
    [Fintype Cell] [Fintype Symbol] [DecidableEq Symbol]
    {n : ℕ} (source : Fin n → Cell) (jointType : Cell × Symbol → ℕ)
    (word : Fin n → Symbol) :
    word ∈ conditionalTypeClass source jointType ↔
      ∀ segment : Fin (Fintype.card Cell),
        segmentMultiplicity (finiteCellSegmentation source) word segment =
          fun symbol ↦ jointType ((Fintype.equivFin Cell).symm segment, symbol) := by
  classical
  rw [mem_conditionalTypeClass]
  constructor
  · intro h segment
    funext symbol
    calc
      segmentMultiplicity (finiteCellSegmentation source) word segment symbol =
          multiplicity (jointWord source word)
            ((Fintype.equivFin Cell).symm segment, symbol) := by
        simpa only [Equiv.apply_symm_apply] using
          segmentMultiplicity_finiteCellSegmentation source word
            ((Fintype.equivFin Cell).symm segment) symbol
      _ = jointType ((Fintype.equivFin Cell).symm segment, symbol) :=
        congrFun h _
  · intro h
    funext pair
    rcases pair with ⟨cell, symbol⟩
    have hsegment := congrFun (h (Fintype.equivFin Cell cell)) symbol
    rw [segmentMultiplicity_finiteCellSegmentation source word cell symbol,
      Equiv.symm_apply_apply] at hsegment
    exact hsegment

end AlgebraicComplexity.WordType
