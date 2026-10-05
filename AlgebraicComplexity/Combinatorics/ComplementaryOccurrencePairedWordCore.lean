/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Combinatorics.ConditionalWordTypeCore

/-!
# Paired words and complementary occurrence multiplicities

This dependency-minimal module identifies a doubled labelled child word with the two labelled
marginals of its parent-pair word.  The probability-model adapter is kept in
`ComplementaryOccurrencePairedWord` so finite counting clients do not import real analysis.
-/

namespace AlgebraicComplexity
namespace ComplementaryOccurrenceLaw

universe u v

variable {State : Type u} [Fintype State]
variable {Symbol : Type v} [Fintype Symbol]

/-- Pair the two labelled child halves at each ordered parent position. -/
def parentPairWord (state : Fin n → State)
    (left right : Fin n → Symbol) : Fin n → State × (Symbol × Symbol) :=
  WordType.jointWord state fun i ↦ (left i, right i)

/-- Concatenate the labelled left occurrences with the complemented right occurrences. -/
def labelledChildWord (complement : Equiv.Perm State) (state : Fin n → State)
    (left right : Fin n → Symbol) : Fin (n + n) → State × Symbol :=
  Fin.append (fun i ↦ (state i, left i))
    (fun i ↦ (complement (state i), right i))

/-- The ordered-state marginal of the parent-pair word is the original state multiplicity. -/
theorem mappedType_fst_multiplicity_parentPairWord
    (state : Fin n → State) (left right : Fin n → Symbol) :
    WordType.mappedType Prod.fst
        (WordType.multiplicity (parentPairWord state left right)) =
      WordType.multiplicity state := by
  rw [← WordType.multiplicity_comp_eq_mappedType]
  rfl

/-- The sum of the two labelled marginals of the parent-pair word is exactly the multiplicity
of the doubled labelled child word.  In particular, fixed points of `complement` are counted in
both summands rather than deduplicated. -/
theorem pooledMappedType_multiplicity_parentPairWord
    (complement : Equiv.Perm State) (state : Fin n → State)
    (left right : Fin n → Symbol) (child : State × Symbol) :
    WordType.mappedType
          (fun sample : State × (Symbol × Symbol) ↦ (sample.1, sample.2.1))
          (WordType.multiplicity (parentPairWord state left right)) child +
        WordType.mappedType
          (fun sample : State × (Symbol × Symbol) ↦
            (complement sample.1, sample.2.2))
          (WordType.multiplicity (parentPairWord state left right)) child =
      WordType.multiplicity (labelledChildWord complement state left right) child := by
  have hleft :
      WordType.mappedType
          (fun sample : State × (Symbol × Symbol) ↦ (sample.1, sample.2.1))
          (WordType.multiplicity (parentPairWord state left right)) =
        WordType.multiplicity (fun i ↦ (state i, left i)) := by
    rw [← WordType.multiplicity_comp_eq_mappedType]
    rfl
  have hright :
      WordType.mappedType
          (fun sample : State × (Symbol × Symbol) ↦
            (complement sample.1, sample.2.2))
          (WordType.multiplicity (parentPairWord state left right)) =
        WordType.multiplicity (fun i ↦ (complement (state i), right i)) := by
    rw [← WordType.multiplicity_comp_eq_mappedType]
    rfl
  rw [hleft, hright]
  exact congrFun
    (WordType.multiplicity_append
      (fun i ↦ (state i, left i))
      (fun i ↦ (complement (state i), right i))).symm child

end ComplementaryOccurrenceLaw
end AlgebraicComplexity
