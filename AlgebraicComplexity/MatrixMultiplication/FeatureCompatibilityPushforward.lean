/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Combinatorics.ConditionalWordTypeCore
import AlgebraicComplexity.MatrixMultiplication.FeatureCompatibility

/-!
# Cell multiplicities under a finite feature quotient

Compatibility predicates count symbols separately inside finitely many coarse cells.  If a
feature map forgets part of a symbol, the quotient count is exactly the pushforward of the fine
cell-count profile.  This module records that fact independently of any tensor construction.

The map need not be injective.  This is the algebraic bridge used when complete-split symbols are
replaced by their total weights: every quotient multiplicity is the sum over its complete-split
fiber, with no choice of a representative.
-/

namespace AlgebraicComplexity
namespace MoreAsymmetryCompatibility

/-- The multiplicity of a `(symbol, cell)` pair in the joint word is the symbol's multiplicity
inside that cell.  This is the coordinate order used by conditional feature type classes. -/
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

/-- Replacing a finite cell alphabet by a subtype carrying membership proofs does not change any
cell multiplicity. -/
theorem cellMultiplicity_subtype_val
    {samples : ℕ} {Cell Symbol : Type*}
    [DecidableEq Cell] [DecidableEq Symbol]
    {allowed : Finset Cell} (cells : Fin samples → {cell // cell ∈ allowed})
    (symbols : Fin samples → Symbol) (cell : {cell // cell ∈ allowed})
    (symbol : Symbol) :
    cellMultiplicity cells symbols cell symbol =
      cellMultiplicity (fun sample ↦ (cells sample).1) symbols cell.1 symbol := by
  classical
  unfold cellMultiplicity
  congr 1
  ext sample
  simp

/-- Counting the image symbols in one cell is exactly the finite pushforward of the fine-symbol
cell profile.  No injectivity or surjectivity assumption on `feature` is needed.

Proof sketch: restrict the position set to the requested cell, partition it by the fine symbol,
and sum precisely the fibers whose image is the requested quotient symbol. -/
theorem cellMultiplicity_comp_eq_mappedType
    {I Cell Fine Coarse : Type*}
    [Fintype I] [Fintype Fine]
    [DecidableEq Cell] [DecidableEq Fine] [DecidableEq Coarse]
    (cellOf : I → Cell) (word : I → Fine) (feature : Fine → Coarse)
    (cell : Cell) :
    cellMultiplicity cellOf (feature ∘ word) cell =
      WordType.mappedType feature (cellMultiplicity cellOf word cell) := by
  classical
  funext symbol
  unfold cellMultiplicity WordType.mappedType
  simpa [WordType.letterFiber, Function.comp_apply, Finset.filter_filter, and_assoc] using
    (Finset.sum_card_fiberwise_eq_card_filter
      (Finset.univ.filter fun position ↦ cellOf position = cell)
      (WordType.letterFiber feature symbol) word).symm

/-- A tiny noninjective client: collapsing both Boolean symbols to one feature still satisfies the
exact cellwise pushforward identity. -/
example (cellOf : Fin 3 → Bool) (word : Fin 3 → Bool) (cell : Bool) :
    cellMultiplicity cellOf ((fun _ : Bool ↦ ()) ∘ word) cell =
      WordType.mappedType (fun _ : Bool ↦ ())
        (cellMultiplicity cellOf word cell) := by
  exact cellMultiplicity_comp_eq_mappedType
    cellOf word (fun _ : Bool ↦ ()) cell

end MoreAsymmetryCompatibility
end AlgebraicComplexity
