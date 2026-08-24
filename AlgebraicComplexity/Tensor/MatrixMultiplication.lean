import AlgebraicComplexity.Tensor.Basic
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

universe u

/-- The `m × n` coordinate matrix space over `K`. -/
abbrev MatrixSpace (K : Type u) (m n : ℕ) := Matrix (Fin m) (Fin n) K

variable {K : Type u} [CommSemiring K]

/-- The rectangular matrix-multiplication tensor `⟨m,n,p⟩`. -/
def matrixMultiplicationTensor (K : Type u) [CommSemiring K] (m n p : ℕ) :
    TriTensor K (MatrixSpace K m n) (MatrixSpace K n p) (MatrixSpace K p m) :=
  ∑ i : Fin m, ∑ j : Fin n, ∑ k : Fin p,
    pure (Matrix.single i j 1) (Matrix.single j k 1) (Matrix.single k i 1)

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

/-- Cyclically rotating tensor coordinates cyclically rotates the matrix dimensions. -/
theorem cycleLeft_matrixMultiplicationTensor (m n p : ℕ) :
    cycleLeft (matrixMultiplicationTensor K m n p) =
      matrixMultiplicationTensor K n p m := by
  simp only [matrixMultiplicationTensor, map_sum, cycleLeft_pure]
  rw [Fintype.sum_comm]
  congr with j
  rw [Fintype.sum_comm]

/-- The inverse cyclic rotation gives the opposite cyclic dimension rotation. -/
theorem cycleRight_matrixMultiplicationTensor (m n p : ℕ) :
    cycleRight (matrixMultiplicationTensor K m n p) =
      matrixMultiplicationTensor K p m n := by
  apply (cycleLeft (K := K)
    (X := MatrixSpace K p m) (Y := MatrixSpace K m n) (Z := MatrixSpace K n p)).injective
  simp [cycleLeft_matrixMultiplicationTensor]

end TriTensor
end AlgebraicComplexity
