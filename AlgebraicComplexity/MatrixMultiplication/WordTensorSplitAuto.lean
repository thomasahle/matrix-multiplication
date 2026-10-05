/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.WordTensorReindex

/-!
# The multiplicity side condition of a word split, discharged

Layer 3 (`AlgebraicComplexity/MatrixMultiplication/`).
`MatrixMultiplication/WordTensorReindex.lean` splits a word tensor into two blocks provided the
concatenation of the intended blocks has the same letter multiset as the original word.  That side
condition is stated about `positiveWordAppend`, which is awkward for a client holding *counts*.

The committed `WordType.multiplicity_positiveWordAppend`
(`MatrixMultiplication/PartitionedTypeAssembly.lean`) computes it: the multiplicities of a
concatenation are the pointwise sum of the multiplicities of its parts.
`hasTauWeight_wordTensor_split_of_multiplicity`
then takes the side condition in additive form, which is what an orbit or type computation
naturally produces.
-/

namespace AlgebraicComplexity

open Tensor
open scoped BigOperators

universe u v w

/-! ## Multiplicities of a concatenation -/

section Multiplicity

variable {I : Type w} [Fintype I] [DecidableEq I]

omit [Fintype I] in
/-- Multiplicity as a sum of indicators. -/
theorem multiplicity_eq_sum_ite {n : ℕ} (word : Fin n → I) (s : I) :
    WordType.multiplicity word s = ∑ i, if word i = s then 1 else 0 := by
  classical
  unfold WordType.multiplicity
  rw [Finset.card_filter]
  exact Finset.sum_congr rfl fun _ _ ↦ by congr 1

end Multiplicity

/-! ## The split with an additive side condition -/

section Split

variable {K : Type u} [CommSemiring K]
variable {A : Leg → Type w} [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]
variable {V : ∀ c, A c → Type (max u v)}
variable [∀ c a, AddCommMonoid (V c a)] [∀ c a, Module K (V c a)]

/-- **The word split, with the side condition in additive form.**

A client exhibits the two blocks and checks, letter by letter, that the original multiplicities
are the sum of the two blocks' multiplicities.  That is exactly what a counting argument produces,
and it no longer mentions `positiveWordAppend`. -/
theorem hasTauWeight_wordTensor_split_of_multiplicity
    (P : PartitionedTensor (K := K) (A := A) V) {τ a b : ℝ} {n m : ℕ}
    (q : PositiveWord P.support (n + m + 1))
    (left : PositiveWord P.support n) (right : PositiveWord P.support m)
    (hmult : ∀ s, WordType.multiplicity (positiveWordEquiv P.support (n + m + 1) q) s =
      WordType.multiplicity (positiveWordEquiv P.support n left) s +
        WordType.multiplicity (positiveWordEquiv P.support m right) s)
    (hleft : HasTauWeight K (PartitionedTensor.positiveSupportWordTensor P n left) τ a)
    (hright : HasTauWeight K (PartitionedTensor.positiveSupportWordTensor P m right) τ b)
    (ha : 0 ≤ a) (hb : 0 ≤ b) :
    HasTauWeight K (PartitionedTensor.positiveSupportWordTensor P (n + m + 1) q) τ (a * b) :=
  hasTauWeight_wordTensor_split P q left right
    ((funext hmult).trans (WordType.multiplicity_positiveWordAppend left right).symm)
    hleft hright ha hb

end Split

end AlgebraicComplexity
