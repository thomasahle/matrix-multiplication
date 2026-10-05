/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Tensor.BasicDefs
import Mathlib.Algebra.BigOperators.Fin

/-!
# Minimal constructive tensor-rank definitions

This is the lowest rank layer.  It defines constructive upper-bound witnesses, ordinary rank as
the least witness length, and the calculus using only the additive structure of an abstract
three-legged tensor.  It deliberately does not import leg maps, restrictions, external products,
or direct sums.

`Tensor/RankCore.lean` adds map/restriction/isomorphism laws, and `Tensor/Rank.lean` adds
external-product and direct-sum laws.  The split keeps the public names unchanged while allowing
the matrix-exponent definition to depend only on the notion of rank that occurs in its statement.
-/

namespace AlgebraicComplexity.Tensor

universe u v

variable {K : Type u} [CommSemiring K]
variable {V : Leg → Type v}
variable [∀ i, AddCommMonoid (V i)] [∀ i, Module K (V i)]

/-- Reindex a mapped list sum by the canonical finite index type: summing `f` over the entries of
`l` in list order is the same as summing `f (l.get j)` over `j : Fin l.length`.

This is the standard bridge from the list-based certificates used throughout the rank calculus to
`Finset`-indexed spanning and dimension arguments.

Proof sketch: induct on the list.  For a cons, expose the successor finite index type explicitly;
`Fin.sum_univ_succ` separates its head coordinate from the tail, and both `List.get` equations are
definitionally equal. -/
theorem list_map_sum_eq_fin_sum {α : Type*} {β : Type*} [AddCommMonoid β]
    (f : α → β) (l : List α) :
    (l.map f).sum = ∑ j : Fin l.length, f (l.get j) := by
  induction l with
  | nil => simp
  | cons a l ih =>
      rw [List.map_cons, List.sum_cons, ih]
      change f a + (∑ j : Fin l.length, f (l.get j)) =
        ∑ j : Fin (l.length + 1), f ((a :: l).get j)
      rw [Fin.sum_univ_succ]
      rfl

/-- A tensor is a sum of at most `r` pure tensors. -/
def RankLE (r : ℕ) (T : Tensor3 K V) : Prop :=
  ∃ terms : List (∀ i, V i),
    terms.length ≤ r ∧ T = (terms.map pure).sum

namespace RankLE

/-- The zero tensor has rank at most `0`, witnessed by the empty decomposition. -/
theorem zero : RankLE 0 (0 : Tensor3 K V) := by
  exact ⟨[], by simp, by simp⟩

/-- A pure tensor has rank at most `1`, witnessed by the one-term decomposition. -/
theorem pure_tensor (x : ∀ i, V i) : RankLE 1 (pure (K := K) x) := by
  exact ⟨[x], by simp, by simp⟩

/-- The list itself is a rank certificate for the sum of its pure tensors. -/
theorem list_sum_pure (terms : List (∀ i, V i)) :
    RankLE terms.length (terms.map (pure (K := K))).sum := by
  exact ⟨terms, le_rfl, rfl⟩

/-- A finite sum of pure tensors has rank at most the size of its index set. -/
theorem finset_sum_pure {α : Type*} [DecidableEq α] (s : Finset α)
    (x : α → ∀ i, V i) :
    RankLE s.card (∑ a ∈ s, pure (K := K) (x a)) := by
  refine ⟨s.toList.map x, ?_, ?_⟩
  · simp
  · simp [Function.comp_def]

/-- A sum of pure tensors indexed by a finite type has the cardinality rank bound. -/
theorem fintype_sum_pure {α : Type*} [Fintype α] (x : α → ∀ i, V i) :
    RankLE (Fintype.card α) (∑ a, pure (K := K) (x a)) := by
  classical
  simpa using finset_sum_pure (K := K) (V := V) (Finset.univ : Finset α) x

/-- Rank upper bounds are monotone in the bound: a witness for rank at most `r` is also a
witness for rank at most any larger `s`. -/
theorem mono {r s : ℕ} {T : Tensor3 K V} (h : RankLE r T) (hrs : r ≤ s) : RankLE s T := by
  rcases h with ⟨terms, hlen, hsum⟩
  exact ⟨terms, hlen.trans hrs, hsum⟩

/-- A tensor with rank at most `0` is the zero tensor. -/
theorem eq_zero {T : Tensor3 K V} (h : RankLE 0 T) : T = 0 := by
  rcases h with ⟨terms, hlen, hsum⟩
  cases terms with
  | nil => simpa using hsum
  | cons x terms => simp at hlen

/-- Rank upper bounds are subadditive: concatenating a decomposition of `T` with one of `S`
bounds the rank of `T + S` by `r + s`. -/
theorem add {r s : ℕ} {T S : Tensor3 K V} (hT : RankLE r T) (hS : RankLE s S) :
    RankLE (r + s) (T + S) := by
  rcases hT with ⟨left, hleft, rfl⟩
  rcases hS with ⟨right, hright, rfl⟩
  refine ⟨left ++ right, ?_, ?_⟩
  · simpa only [List.length_append] using Nat.add_le_add hleft hright
  · simp

/-- A sum of uniformly bounded-rank tensors has the cardinality-times-rank bound. -/
theorem finset_sum {α : Type*} [DecidableEq α] (s : Finset α)
    (F : α → Tensor3 K V) (r : ℕ)
    (hF : ∀ a ∈ s, RankLE r (F a)) :
    RankLE (s.card * r) (∑ a ∈ s, F a) := by
  induction s using Finset.induction_on with
  | empty => simpa using (zero (K := K) (V := V))
  | @insert a s ha ih =>
      have haRank : RankLE r (F a) := hF a (Finset.mem_insert_self a s)
      have hsRank : RankLE (s.card * r) (∑ x ∈ s, F x) :=
        ih fun x hx ↦ hF x (Finset.mem_insert_of_mem hx)
      simpa [Finset.sum_insert ha, Finset.card_insert_of_notMem ha,
        Nat.add_mul, Nat.add_comm] using add haRank hsRank

/-- A finite list sum of uniformly bounded-rank tensors has the length-times-rank bound. -/
theorem list_sum (terms : List (Tensor3 K V)) (r : ℕ)
    (hterms : ∀ T ∈ terms, RankLE r T) :
    RankLE (terms.length * r) terms.sum := by
  induction terms with
  | nil => simpa using (zero (K := K) (V := V))
  | cons T terms ih =>
      have hT : RankLE r T := hterms T (by simp)
      have hrest : RankLE (terms.length * r) terms.sum :=
        ih fun S hS ↦ hterms S (by simp [hS])
      simpa [Nat.add_mul, Nat.add_comm] using hT.add hrest

end RankLE

/-- Every algebraic tensor is a finite sum of pure tensors. -/
theorem exists_rankLE (T : Tensor3 K V) : ∃ r, RankLE r T := by
  refine PiTensorProduct.induction_on T ?_ ?_
  · intro a x
    refine ⟨1, ?_⟩
    rw [← ofLegs_eta x, ← pure_ofLegs_smul_X]
    exact RankLE.pure_tensor _
  · intro T S hT hS
    rcases hT with ⟨r, hT⟩
    rcases hS with ⟨s, hS⟩
    exact ⟨r + s, hT.add hS⟩

/-- Ordinary tensor rank, defined as the least length of a pure-tensor decomposition. -/
noncomputable def rank (T : Tensor3 K V) : ℕ := by
  classical
  exact Nat.find (exists_rankLE T)

/-- The defining property of `rank`: every tensor admits an explicit decomposition into at most
`rank T` pure tensors. -/
theorem rank_spec (T : Tensor3 K V) : RankLE (rank T) T := by
  classical
  exact Nat.find_spec (exists_rankLE T)

/-- The numerical rank and constructive upper-bound predicate contain the same information. -/
theorem rank_le_iff {T : Tensor3 K V} {r : ℕ} : rank T ≤ r ↔ RankLE r T := by
  classical
  constructor
  · intro h
    exact (rank_spec T).mono h
  · intro h
    exact Nat.find_min' (exists_rankLE T) h

/-- The zero tensor has rank exactly `0`. -/
@[simp] theorem rank_zero : rank (0 : Tensor3 K V) = 0 := by
  exact Nat.eq_zero_of_le_zero (rank_le_iff.mpr (RankLE.zero (K := K) (V := V)))

/-- A tensor has rank `0` if and only if it is the zero tensor. -/
@[simp] theorem rank_eq_zero {T : Tensor3 K V} : rank T = 0 ↔ T = 0 := by
  constructor
  · intro h
    have hrank := rank_spec T
    rw [h] at hrank
    exact hrank.eq_zero
  · intro h
    subst T
    exact rank_zero

/-- A pure tensor has rank at most `1`. -/
theorem rank_pure_le_one (x : ∀ c, V c) : rank (pure (K := K) x) ≤ 1 :=
  rank_le_iff.mpr (RankLE.pure_tensor x)

/-- Ordinary tensor rank is subadditive: the rank of `T + S` is at most `rank T + rank S`. -/
theorem rank_add_le (T S : Tensor3 K V) : rank (T + S) ≤ rank T + rank S :=
  rank_le_iff.mpr ((rank_spec T).add (rank_spec S))

end AlgebraicComplexity.Tensor
