import AlgebraicComplexity.Tensor.Coordinates
import AlgebraicComplexity.Tensor.Rank
import Mathlib.Tactic

set_option linter.style.header false

/-!
# The Coppersmith--Winograd tensor

This file defines the standard tensor `CW_q` in coordinate function spaces. The familiar
`3q + 3`-term presentation is formalized as an ordinary rank certificate. Its much stronger border
rank bound `q + 2` belongs to the future general-degeneration layer.
-/

namespace AlgebraicComplexity
namespace TriTensor

universe u

variable {K : Type u} [CommSemiring K]

/-- Index `0` among the `q+2` Coppersmith--Winograd variables. -/
def cwZero (q : ℕ) : Fin (q + 2) :=
  ⟨0, by omega⟩

/-- The middle variable indexed by `i : Fin q`, shifted by one. -/
def cwMiddle (q : ℕ) (i : Fin q) : Fin (q + 2) :=
  ⟨i.1 + 1, by omega⟩

/-- The final special variable, indexed by `q+1`. -/
def cwLast (q : ℕ) : Fin (q + 2) :=
  ⟨q + 1, by omega⟩

/-- Coordinate module used by `CW_q`. -/
abbrev CWVariableSpace (K : Type u) (q : ℕ) := Fin (q + 2) → K

/-- A standard-basis variable of the Coppersmith--Winograd tensor. -/
def cwVariable (q : ℕ) (i : Fin (q + 2)) : CWVariableSpace K q :=
  CoordinateTensor.basisVector (K := K) i

/-- The `3q` middle terms of `CW_q`. -/
def coppersmithWinogradMiddle (K : Type u) [CommSemiring K] (q : ℕ) :
    TriTensor K (CWVariableSpace K q) (CWVariableSpace K q) (CWVariableSpace K q) :=
  ∑ i : Fin q,
    pure (cwVariable (K := K) q (cwZero q))
      (cwVariable (K := K) q (cwMiddle q i))
      (cwVariable (K := K) q (cwMiddle q i)) +
    pure (cwVariable (K := K) q (cwMiddle q i))
      (cwVariable (K := K) q (cwZero q))
      (cwVariable (K := K) q (cwMiddle q i)) +
    pure (cwVariable (K := K) q (cwMiddle q i))
      (cwVariable (K := K) q (cwMiddle q i))
      (cwVariable (K := K) q (cwZero q))

/-- The three corner terms of `CW_q`. -/
def coppersmithWinogradCorners (K : Type u) [CommSemiring K] (q : ℕ) :
    TriTensor K (CWVariableSpace K q) (CWVariableSpace K q) (CWVariableSpace K q) :=
  pure (cwVariable (K := K) q (cwZero q))
      (cwVariable (K := K) q (cwZero q))
      (cwVariable (K := K) q (cwLast q)) +
    pure (cwVariable (K := K) q (cwZero q))
      (cwVariable (K := K) q (cwLast q))
      (cwVariable (K := K) q (cwZero q)) +
    pure (cwVariable (K := K) q (cwLast q))
      (cwVariable (K := K) q (cwZero q))
      (cwVariable (K := K) q (cwZero q))

/-- The standard Coppersmith--Winograd tensor `CW_q`. -/
def coppersmithWinogradTensor (K : Type u) [CommSemiring K] (q : ℕ) :
    TriTensor K (CWVariableSpace K q) (CWVariableSpace K q) (CWVariableSpace K q) :=
  coppersmithWinogradMiddle K q + coppersmithWinogradCorners K q

/-- The displayed `3q` middle terms give the corresponding elementary rank certificate. -/
theorem coppersmithWinogradMiddle_rank_le (q : ℕ) :
    HasRankAtMost (K := K) (q * 3) (coppersmithWinogradMiddle K q) := by
  have h :
      HasRankAtMost (K := K) (∑ _i : Fin q, 3) (coppersmithWinogradMiddle K q) := by
    unfold coppersmithWinogradMiddle
    refine HasRankAtMost.fintype_sum
      (fun _i : Fin q => 3)
      (fun i : Fin q =>
        pure (cwVariable (K := K) q (cwZero q))
            (cwVariable (K := K) q (cwMiddle q i))
            (cwVariable (K := K) q (cwMiddle q i)) +
          pure (cwVariable (K := K) q (cwMiddle q i))
            (cwVariable (K := K) q (cwZero q))
            (cwVariable (K := K) q (cwMiddle q i)) +
          pure (cwVariable (K := K) q (cwMiddle q i))
            (cwVariable (K := K) q (cwMiddle q i))
            (cwVariable (K := K) q (cwZero q))) ?_
    intro i
    exact ((HasRankAtMost.pure
      (cwVariable (K := K) q (cwZero q))
      (cwVariable (K := K) q (cwMiddle q i))
      (cwVariable (K := K) q (cwMiddle q i))).add
      (HasRankAtMost.pure
        (cwVariable (K := K) q (cwMiddle q i))
        (cwVariable (K := K) q (cwZero q))
        (cwVariable (K := K) q (cwMiddle q i)))).add
      (HasRankAtMost.pure
        (cwVariable (K := K) q (cwMiddle q i))
        (cwVariable (K := K) q (cwMiddle q i))
        (cwVariable (K := K) q (cwZero q)))
  simpa using h

/-- The three corner terms have rank at most three. -/
theorem coppersmithWinogradCorners_rank_le (q : ℕ) :
    HasRankAtMost (K := K) 3 (coppersmithWinogradCorners K q) := by
  unfold coppersmithWinogradCorners
  exact ((HasRankAtMost.pure
    (cwVariable (K := K) q (cwZero q))
    (cwVariable (K := K) q (cwZero q))
    (cwVariable (K := K) q (cwLast q))).add
    (HasRankAtMost.pure
      (cwVariable (K := K) q (cwZero q))
      (cwVariable (K := K) q (cwLast q))
      (cwVariable (K := K) q (cwZero q)))).add
    (HasRankAtMost.pure
      (cwVariable (K := K) q (cwLast q))
      (cwVariable (K := K) q (cwZero q))
      (cwVariable (K := K) q (cwZero q)))

/-- The direct presentation certifies ordinary rank at most `3q+3`. -/
theorem coppersmithWinogradTensor_rank_le (q : ℕ) :
    HasRankAtMost (K := K) (q * 3 + 3) (coppersmithWinogradTensor K q) := by
  exact (coppersmithWinogradMiddle_rank_le (K := K) q).add
    (coppersmithWinogradCorners_rank_le (K := K) q)

/-- `CW_q` is invariant under cyclic permutation of its three coordinate roles. -/
theorem cycleLeft_coppersmithWinogradTensor (q : ℕ) :
    cycleLeft (coppersmithWinogradTensor K q) = coppersmithWinogradTensor K q := by
  classical
  unfold coppersmithWinogradTensor coppersmithWinogradMiddle coppersmithWinogradCorners
  simp only [map_add, map_sum, cycleLeft_pure]
  congr 1
  · apply Finset.sum_congr rfl
    intro i _
    abel
  · abel

end TriTensor
end AlgebraicComplexity
