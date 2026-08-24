import AlgebraicComplexity.Tensor.Rank
import Mathlib.LinearAlgebra.Matrix.StdBasis

set_option linter.style.header false

/-!
# Matrix-multiplication tensors

The tensor `matrixMultiplicationTensor K m n p` is the usual structure tensor

`∑ i, j, k, xᵢⱼ ⊗ yⱼₖ ⊗ zₖᵢ`

for multiplying an `m × n` matrix by an `n × p` matrix.
-/

namespace AlgebraicComplexity
namespace TriTensor

universe u v w x

private theorem sum_cycleLeft
    {A : Type v} {B : Type w} {C : Type x} {M : Type u}
    [Fintype A] [Fintype B] [Fintype C] [AddCommMonoid M]
    (f : A → B → C → M) :
    (∑ a, ∑ b, ∑ c, f a b c) = ∑ b, ∑ c, ∑ a, f a b c := by
  classical
  calc
    (∑ a, ∑ b, ∑ c, f a b c) = ∑ b, ∑ a, ∑ c, f a b c := by
      rw [Finset.sum_comm]
    _ = ∑ b, ∑ c, ∑ a, f a b c := by
      apply Finset.sum_congr rfl
      intro b _
      rw [Finset.sum_comm]

private theorem sum_cycleRight
    {A : Type v} {B : Type w} {C : Type x} {M : Type u}
    [Fintype A] [Fintype B] [Fintype C] [AddCommMonoid M]
    (f : A → B → C → M) :
    (∑ a, ∑ b, ∑ c, f a b c) = ∑ c, ∑ a, ∑ b, f a b c := by
  calc
    (∑ a, ∑ b, ∑ c, f a b c) = ∑ b, ∑ c, ∑ a, f a b c := sum_cycleLeft f
    _ = ∑ c, ∑ a, ∑ b, f a b c :=
      sum_cycleLeft (fun b c a => f a b c)

/-- The `m × n` coordinate matrix space over `K`. -/
abbrev MatrixSpace (K : Type u) (m n : ℕ) := Matrix (Fin m) (Fin n) K

variable {K : Type u} [CommSemiring K]

/-- The rectangular matrix-multiplication tensor `⟨m,n,p⟩`. -/
def matrixMultiplicationTensor (K : Type u) [CommSemiring K] (m n p : ℕ) :
    TriTensor K (MatrixSpace K m n) (MatrixSpace K n p) (MatrixSpace K p m) :=
  ∑ i : Fin m, ∑ j : Fin n, ∑ k : Fin p,
    pure (K := K)
      (Matrix.single i j (1 : K))
      (Matrix.single j k (1 : K))
      (Matrix.single k i (1 : K))

@[simp]
theorem matrixMultiplicationTensor_zero_left (n p : ℕ) :
    matrixMultiplicationTensor K 0 n p = 0 := by
  simp [matrixMultiplicationTensor]

@[simp]
theorem matrixMultiplicationTensor_zero_middle (m p : ℕ) :
    matrixMultiplicationTensor K m 0 p = 0 := by
  simp [matrixMultiplicationTensor]

@[simp]
theorem matrixMultiplicationTensor_zero_right (m n : ℕ) :
    matrixMultiplicationTensor K m n 0 = 0 := by
  simp [matrixMultiplicationTensor]

/-- The schoolbook decomposition certifies rank at most `m*n*p`. -/
theorem matrixMultiplicationTensor_rank_le (m n p : ℕ) :
    HasRankAtMost (K := K) (m * n * p) (matrixMultiplicationTensor K m n p) := by
  have h :
      HasRankAtMost (K := K)
        (∑ _i : Fin m, ∑ _j : Fin n, ∑ _k : Fin p, (1 : ℕ))
        (matrixMultiplicationTensor K m n p) := by
    unfold matrixMultiplicationTensor
    refine HasRankAtMost.fintype_sum
      (fun _i : Fin m => ∑ _j : Fin n, ∑ _k : Fin p, (1 : ℕ))
      (fun i : Fin m => ∑ j : Fin n, ∑ k : Fin p,
        pure (K := K)
          (Matrix.single i j (1 : K))
          (Matrix.single j k (1 : K))
          (Matrix.single k i (1 : K))) ?_
    intro i
    refine HasRankAtMost.fintype_sum
      (fun _j : Fin n => ∑ _k : Fin p, (1 : ℕ))
      (fun j : Fin n => ∑ k : Fin p,
        pure (K := K)
          (Matrix.single i j (1 : K))
          (Matrix.single j k (1 : K))
          (Matrix.single k i (1 : K))) ?_
    intro j
    refine HasRankAtMost.fintype_sum
      (fun _k : Fin p => (1 : ℕ))
      (fun k : Fin p =>
        pure (K := K)
          (Matrix.single i j (1 : K))
          (Matrix.single j k (1 : K))
          (Matrix.single k i (1 : K))) ?_
    intro k
    exact HasRankAtMost.pure
      (Matrix.single i j (1 : K))
      (Matrix.single j k (1 : K))
      (Matrix.single k i (1 : K))
  simpa [Nat.mul_assoc] using h

/-- Cyclically rotating tensor coordinates cyclically rotates the matrix dimensions. -/
theorem cycleLeft_matrixMultiplicationTensor (m n p : ℕ) :
    cycleLeft (matrixMultiplicationTensor K m n p) =
      matrixMultiplicationTensor K n p m := by
  simp only [matrixMultiplicationTensor, map_sum, cycleLeft_pure]
  exact sum_cycleLeft fun i j k =>
    pure (K := K)
      (Matrix.single j k (1 : K))
      (Matrix.single k i (1 : K))
      (Matrix.single i j (1 : K))

/-- The inverse cyclic rotation gives the opposite cyclic dimension rotation. -/
theorem cycleRight_matrixMultiplicationTensor (m n p : ℕ) :
    cycleRight (matrixMultiplicationTensor K m n p) =
      matrixMultiplicationTensor K p m n := by
  simp only [matrixMultiplicationTensor, map_sum, cycleRight_pure]
  exact sum_cycleRight fun i j k =>
    pure (K := K)
      (Matrix.single k i (1 : K))
      (Matrix.single i j (1 : K))
      (Matrix.single j k (1 : K))

end TriTensor
end AlgebraicComplexity
