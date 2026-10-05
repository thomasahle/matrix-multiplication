/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Combinatorics.ComplementaryOccurrenceProfile
import AlgebraicComplexity.Combinatorics.IdentityOrientationCompetitorCount

/-!
# Conditional type counting for labelled complementary occurrences

This module applies the generic conditional method of types to the exact complementary-occurrence
profiles in `ComplementaryOccurrenceProfile`.  It provides an exact loss-free count, its
proportional entropy bound, and one bound uniform over a finite family of recursive nodes.

A client must still inject its concrete competitor family into the displayed conditional type
class.  Hence the hypotheses remain per-profile and finite: no compatibility containment or
assembled tensor degeneration is accepted here.
-/

open scoped BigOperators

namespace AlgebraicComplexity

universe u v w

namespace ComplementaryOccurrenceLaw

variable {State : Type u} [Fintype State]
variable {Symbol : Type v} [Fintype Symbol]
variable {Cell : Type w} [Fintype Cell] [DecidableEq Cell]
variable {profile : State → ℕ}

/-- Exact loss-free count of symbol words with the occurrence-correct joint profile over a fixed
cell word. -/
theorem card_conditionalTypeClass_eq_prod_multinomial
    (law : ComplementaryOccurrenceLaw profile Symbol)
    (complement : Equiv.Perm State) (cellOf : State → Cell)
    (source : Fin (WordType.profileMass
      (complementaryOccurrenceCellProfile profile complement cellOf)) → Cell)
    (hsource : WordType.multiplicity source =
      complementaryOccurrenceCellProfile profile complement cellOf) :
    (WordType.conditionalTypeClass source (law.cellJointProfile complement cellOf)).card =
      ∏ cell, Nat.multinomial Finset.univ fun symbol ↦
        law.cellJointProfile complement cellOf (cell, symbol) := by
  apply WordType.card_conditionalTypeClass_eq_prod_multinomial_of_law source
    (fun cell symbol ↦ law.cellJointProfile complement cellOf (cell, symbol))
  intro cell
  rw [← WordType.mappedType_fst_apply]
  exact congrFun ((law.mappedType_fst_cellJointProfile complement cellOf).trans hsource.symm) cell

/-- Proportional conditional-type bound for one node, with the exponential base displayed as the
product of occurrence-correct cell entropy bases. -/
theorem card_proportionalConditionalTypeClass_le
    (law : ComplementaryOccurrenceLaw profile Symbol)
    (complement : Equiv.Perm State) (cellOf : State → Cell)
    (hmass : 0 < WordType.profileMass
      (complementaryOccurrenceCellProfile profile complement cellOf))
    (k : ℕ) (hk : 0 < k)
    (source : Fin (WordType.profileMass
      (complementaryOccurrenceCellProfile profile complement cellOf) * k) → Cell)
    (hsource : WordType.multiplicity source = WordType.proportionalCounts
      (complementaryOccurrenceCellProfile profile complement cellOf) k) :
    ((WordType.conditionalTypeClass source (WordType.proportionalCounts
      (law.cellJointProfile complement cellOf) k)).card : ℝ) ≤
      WordType.pushedConditionalTypeLoss
          (complementaryOccurrenceCellProfile profile complement cellOf) k *
        (∏ cell, Real.exp
          ((complementaryOccurrenceCellProfile profile complement cellOf cell : ℝ) *
            WordType.profileEntropyNats fun symbol ↦
              law.cellJointProfile complement cellOf (cell, symbol))) ^ k := by
  exact WordType.card_proportionalConditionalTypeClass_le_loss_mul_prod_cellBase_pow
    (complementaryOccurrenceCellProfile profile complement cellOf)
    (law.cellJointProfile complement cellOf)
    (law.mappedType_fst_cellJointProfile complement cellOf) hmass k hk source hsource

end ComplementaryOccurrenceLaw

/-! ## Uniformity over a finite recursive node family -/

section Family

variable {Node : Type u} [DecidableEq Node]
variable {State : Type v} [Fintype State]
variable {Symbol Cell : Type w} [Fintype Symbol] [Fintype Cell] [DecidableEq Cell]

/-- The maximum occurrence-correct conditional-type loss over finitely many recursive nodes is
still subexponential. -/
theorem subexponential_sup_complementaryOccurrenceLoss
    (nodes : Finset Node) (hne : nodes.Nonempty)
    (profile : Node → State → ℕ) (complement : Node → Equiv.Perm State)
    (cellOf : Node → State → Cell) :
    Growth.Subexponential (fun k ↦ nodes.sup' hne fun node ↦
      WordType.pushedConditionalTypeLoss
        (complementaryOccurrenceCellProfile
          (profile node) (complement node) (cellOf node)) k) :=
  WordType.subexponential_sup'_pushedConditionalTypeLoss nodes hne
    (fun node ↦ complementaryOccurrenceCellProfile
      (profile node) (complement node) (cellOf node))

/-- One occurrence-correct competitor bound valid uniformly over every node in a finite family.
This is the form needed for a fixed-depth recursive composition. -/
theorem card_proportionalComplementaryOccurrenceTypeClass_le_uniform
    (nodes : Finset Node) (hne : nodes.Nonempty)
    (profile : Node → State → ℕ)
    (law : ∀ node, ComplementaryOccurrenceLaw (profile node) Symbol)
    (complement : Node → Equiv.Perm State) (cellOf : Node → State → Cell)
    (hmass : ∀ node, 0 < WordType.profileMass
      (complementaryOccurrenceCellProfile
        (profile node) (complement node) (cellOf node)))
    (k : ℕ) (hk : 0 < k)
    (source : ∀ node, Fin (WordType.profileMass
      (complementaryOccurrenceCellProfile
        (profile node) (complement node) (cellOf node)) * k) → Cell)
    (hsource : ∀ node, WordType.multiplicity (source node) =
      WordType.proportionalCounts
        (complementaryOccurrenceCellProfile
          (profile node) (complement node) (cellOf node)) k)
    {node : Node} (hnode : node ∈ nodes) :
    ((WordType.conditionalTypeClass (source node) (WordType.proportionalCounts
      ((law node).cellJointProfile (complement node) (cellOf node)) k)).card : ℝ) ≤
      (nodes.sup' hne fun m ↦ WordType.pushedConditionalTypeLoss
        (complementaryOccurrenceCellProfile
          (profile m) (complement m) (cellOf m)) k) *
      (nodes.sup' hne fun m ↦ ∏ cell, Real.exp
        ((complementaryOccurrenceCellProfile
            (profile m) (complement m) (cellOf m) cell : ℝ) *
          WordType.profileEntropyNats fun symbol ↦
            (law m).cellJointProfile (complement m) (cellOf m) (cell, symbol))) ^ k := by
  exact WordType.card_proportionalConditionalTypeClass_le_sup'_loss_mul_sup'_base_pow
    nodes hne
    (fun m ↦ complementaryOccurrenceCellProfile
      (profile m) (complement m) (cellOf m))
    (fun m ↦ (law m).cellJointProfile (complement m) (cellOf m))
    (fun m ↦ (law m).mappedType_fst_cellJointProfile (complement m) (cellOf m))
    hmass k hk source hsource hnode

end Family

end AlgebraicComplexity
