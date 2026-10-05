/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Tensor.IndexedDirectSum
import AlgebraicComplexity.Tensor.Power
import Mathlib.Data.Fin.Tuple.Basic

/-!
# Word expansions of powers of finite indexed tensor sums

The `n`th power of a finite direct sum expands into one term for every word of length `n` in the
summand alphabet. This file records that expansion inside the canonical tensor-power ambient
spaces. Grouping the words by multiplicity type is a combinatorics bridge and lives in
`Combinatorics/IndexedPowerType.lean`, keeping the tensor foundation independent of word types.
-/

namespace AlgebraicComplexity.Tensor

open scoped DirectSum

universe u v w

variable {K : Type u} [CommSemiring K]
variable {ι : Type w} [Fintype ι]
variable {V : ι → Leg → Type v}
variable [∀ i c, AddCommMonoid (V i c)] [∀ i c, Module K (V i c)]

/-- The ambient leg family of a finite indexed direct sum. -/
abbrev IndexedSumSpace (K : Type u) [CommSemiring K]
    (V : ι → Leg → Type v)
    [∀ i c, AddCommMonoid (V i c)] [∀ i c, Module K (V i c)] :=
  IndexedDirectSumSpace K V

/-- The tensor-power term selected by a word of summand indices.

Every letter is first included in the corresponding direct-sum block.  The selected tensors are
then multiplied using the same canonical `TensorPower.mulEquiv` used by `Tensor.power`, ensuring
that the word terms and the full power inhabit definitionally identical ambient spaces. -/
noncomputable def indexedWordPower (T : ∀ i, Tensor3 K (V i)) :
    (n : ℕ) → (Fin n → ι) → Tensor3 K (PowerSpace K (IndexedSumSpace K V) n)
  | 0, _ => pure (K := K) (powerUnit (K := K) (V := IndexedSumSpace K V))
  | n + 1, word =>
      powerMul n 1
        (indexedWordPower T n (Fin.init word))
        (powerOne
          (map (indexedInclude (K := K) (V := V) (word (Fin.last n)))
            (T (word (Fin.last n)))))

omit [Fintype ι] in
@[simp] theorem indexedWordPower_zero (T : ∀ i, Tensor3 K (V i))
    (word : Fin 0 → ι) :
    indexedWordPower T 0 word =
      pure (K := K) (powerUnit (K := K) (V := IndexedSumSpace K V)) := rfl

omit [Fintype ι] in
@[simp] theorem indexedWordPower_succ (T : ∀ i, Tensor3 K (V i)) (n : ℕ)
    (word : Fin (n + 1) → ι) :
    indexedWordPower T (n + 1) word =
      powerMul n 1
        (indexedWordPower T n (Fin.init word))
        (powerOne
          (map (indexedInclude (K := K) (V := V) (word (Fin.last n)))
            (T (word (Fin.last n))))) := rfl

/-- Exact word expansion of a canonical power of an indexed direct sum. -/
theorem power_indexedDirectSum_eq_sum_wordPower
    (T : ∀ i, Tensor3 K (V i)) (n : ℕ) :
    power (indexedDirectSum T) n =
      ∑ word : Fin n → ι, indexedWordPower T n word := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [power_succ, ih]
      have hone :
          powerOne (indexedDirectSum T) =
            ∑ i, powerOne
              (map (indexedInclude (K := K) (V := V) i) (T i)) := by
        unfold indexedDirectSum
        exact powerOne_sum _
      rw [hone, powerMul_sum_sum]
      let e : ((Fin n → ι) × ι) ≃ (Fin (n + 1) → ι) :=
        (Equiv.prodComm (Fin n → ι) ι).trans
          (Fin.snocEquiv (fun _ : Fin (n + 1) ↦ ι))
      calc
        (∑ word : Fin n → ι, ∑ i,
            powerMul n 1 (indexedWordPower T n word)
              (powerOne (map (indexedInclude (K := K) (V := V) i) (T i)))) =
            ∑ q : (Fin n → ι) × ι,
              powerMul n 1 (indexedWordPower T n q.1)
                (powerOne (map (indexedInclude (K := K) (V := V) q.2) (T q.2))) := by
                  rw [Fintype.sum_prod_type]
        _ = ∑ word : Fin (n + 1) → ι, indexedWordPower T (n + 1) word := by
          apply Fintype.sum_equiv e
          intro q
          change
            powerMul n 1 (indexedWordPower T n q.1)
                (powerOne (map (indexedInclude (K := K) (V := V) q.2) (T q.2))) =
              indexedWordPower T (n + 1) (Fin.snoc q.1 q.2)
          rw [indexedWordPower_succ, Fin.init_snoc, Fin.snoc_last]

end AlgebraicComplexity.Tensor
