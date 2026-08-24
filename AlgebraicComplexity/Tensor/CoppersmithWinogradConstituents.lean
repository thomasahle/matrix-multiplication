import AlgebraicComplexity.Tensor.CoppersmithWinogradPartition
import AlgebraicComplexity.Tensor.MatrixMultiplication
import AlgebraicComplexity.Tensor.Restriction
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Matrix-multiplication restrictions of the nontrivial `CW_q` constituents

Each of the three `q`-term constituents restricts exactly onto the appropriate rectangular
matrix-multiplication tensor. This is the finite algebraic input used by the laser method.
-/

namespace AlgebraicComplexity
namespace TriTensor

universe u

variable {K : Type u} [CommSemiring K]

/-- The shifted middle-variable indexing is injective. -/
@[simp]
theorem cwMiddle_inj (q : ℕ) (i j : Fin q) :
    cwMiddle q i = cwMiddle q j ↔ i = j := by
  constructor
  · intro h
    apply Fin.ext
    simpa [cwMiddle] using congrArg Fin.val h
  · rintro rfl
    rfl

/-- Read the `x₀` coordinate as a `1 × 1` matrix. -/
def cw011ProjectX (q : ℕ) :
    CWVariableSpace K q →ₗ[K] MatrixSpace K 1 1 where
  toFun v := fun _ _ => v (cwZero q)
  map_add' x y := by ext <;> simp
  map_smul' c x := by ext <;> simp

/-- Read the middle `y` coordinates as a `1 × q` matrix. -/
def cw011ProjectY (q : ℕ) :
    CWVariableSpace K q →ₗ[K] MatrixSpace K 1 q where
  toFun v := fun _ k => v (cwMiddle q k)
  map_add' x y := by ext <;> simp
  map_smul' c x := by ext <;> simp

/-- Read the middle `z` coordinates as a `q × 1` matrix. -/
def cw011ProjectZ (q : ℕ) :
    CWVariableSpace K q →ₗ[K] MatrixSpace K q 1 where
  toFun v := fun k _ => v (cwMiddle q k)
  map_add' x y := by ext <;> simp
  map_smul' c x := by ext <;> simp

@[simp]
theorem cw011ProjectX_zero (q : ℕ) :
    cw011ProjectX (K := K) q (cwVariable (K := K) q (cwZero q)) =
      Matrix.single 0 0 1 := by
  ext i j
  fin_cases i
  fin_cases j
  simp [cw011ProjectX, cwVariable, CoordinateTensor.basisVector]

@[simp]
theorem cw011ProjectY_middle (q : ℕ) (i : Fin q) :
    cw011ProjectY (K := K) q (cwVariable (K := K) q (cwMiddle q i)) =
      Matrix.single 0 i 1 := by
  ext row col
  fin_cases row
  simp [cw011ProjectY, cwVariable, CoordinateTensor.basisVector]

@[simp]
theorem cw011ProjectZ_middle (q : ℕ) (i : Fin q) :
    cw011ProjectZ (K := K) q (cwVariable (K := K) q (cwMiddle q i)) =
      Matrix.single i 0 1 := by
  ext row col
  fin_cases col
  simp [cw011ProjectZ, cwVariable, CoordinateTensor.basisVector]

/-- The `(0,1,1)` constituent restricts to `⟨1,1,q⟩`. -/
theorem cw011_restricts_matrixMultiplication (q : ℕ) :
    Restricts (cw011 (K := K) q) (matrixMultiplicationTensor K 1 1 q) := by
  refine ⟨cw011ProjectX (K := K) q, cw011ProjectY (K := K) q,
    cw011ProjectZ (K := K) q, ?_⟩
  simp [cw011, matrixMultiplicationTensor]

/-- Read the middle `x` coordinates as a `1 × q` matrix. -/
def cw110ProjectX (q : ℕ) :
    CWVariableSpace K q →ₗ[K] MatrixSpace K 1 q where
  toFun v := fun _ k => v (cwMiddle q k)
  map_add' x y := by ext <;> simp
  map_smul' c x := by ext <;> simp

/-- Read the middle `y` coordinates as a `q × 1` matrix. -/
def cw110ProjectY (q : ℕ) :
    CWVariableSpace K q →ₗ[K] MatrixSpace K q 1 where
  toFun v := fun k _ => v (cwMiddle q k)
  map_add' x y := by ext <;> simp
  map_smul' c x := by ext <;> simp

/-- Read `z₀` as a `1 × 1` matrix. -/
def cw110ProjectZ (q : ℕ) :
    CWVariableSpace K q →ₗ[K] MatrixSpace K 1 1 where
  toFun v := fun _ _ => v (cwZero q)
  map_add' x y := by ext <;> simp
  map_smul' c x := by ext <;> simp

@[simp]
theorem cw110ProjectX_middle (q : ℕ) (i : Fin q) :
    cw110ProjectX (K := K) q (cwVariable (K := K) q (cwMiddle q i)) =
      Matrix.single 0 i 1 := by
  ext row col
  fin_cases row
  simp [cw110ProjectX, cwVariable, CoordinateTensor.basisVector]

@[simp]
theorem cw110ProjectY_middle (q : ℕ) (i : Fin q) :
    cw110ProjectY (K := K) q (cwVariable (K := K) q (cwMiddle q i)) =
      Matrix.single i 0 1 := by
  ext row col
  fin_cases col
  simp [cw110ProjectY, cwVariable, CoordinateTensor.basisVector]

@[simp]
theorem cw110ProjectZ_zero (q : ℕ) :
    cw110ProjectZ (K := K) q (cwVariable (K := K) q (cwZero q)) =
      Matrix.single 0 0 1 := by
  ext i j
  fin_cases i
  fin_cases j
  simp [cw110ProjectZ, cwVariable, CoordinateTensor.basisVector]

/-- The `(1,1,0)` constituent restricts to `⟨1,q,1⟩`. -/
theorem cw110_restricts_matrixMultiplication (q : ℕ) :
    Restricts (cw110 (K := K) q) (matrixMultiplicationTensor K 1 q 1) := by
  refine ⟨cw110ProjectX (K := K) q, cw110ProjectY (K := K) q,
    cw110ProjectZ (K := K) q, ?_⟩
  simp [cw110, matrixMultiplicationTensor]

/-- Read the middle `x` coordinates as a `q × 1` matrix. -/
def cw101ProjectX (q : ℕ) :
    CWVariableSpace K q →ₗ[K] MatrixSpace K q 1 where
  toFun v := fun k _ => v (cwMiddle q k)
  map_add' x y := by ext <;> simp
  map_smul' c x := by ext <;> simp

/-- Read `y₀` as a `1 × 1` matrix. -/
def cw101ProjectY (q : ℕ) :
    CWVariableSpace K q →ₗ[K] MatrixSpace K 1 1 where
  toFun v := fun _ _ => v (cwZero q)
  map_add' x y := by ext <;> simp
  map_smul' c x := by ext <;> simp

/-- Read the middle `z` coordinates as a `1 × q` matrix. -/
def cw101ProjectZ (q : ℕ) :
    CWVariableSpace K q →ₗ[K] MatrixSpace K 1 q where
  toFun v := fun _ k => v (cwMiddle q k)
  map_add' x y := by ext <;> simp
  map_smul' c x := by ext <;> simp

@[simp]
theorem cw101ProjectX_middle (q : ℕ) (i : Fin q) :
    cw101ProjectX (K := K) q (cwVariable (K := K) q (cwMiddle q i)) =
      Matrix.single i 0 1 := by
  ext row col
  fin_cases col
  simp [cw101ProjectX, cwVariable, CoordinateTensor.basisVector]

@[simp]
theorem cw101ProjectY_zero (q : ℕ) :
    cw101ProjectY (K := K) q (cwVariable (K := K) q (cwZero q)) =
      Matrix.single 0 0 1 := by
  ext i j
  fin_cases i
  fin_cases j
  simp [cw101ProjectY, cwVariable, CoordinateTensor.basisVector]

@[simp]
theorem cw101ProjectZ_middle (q : ℕ) (i : Fin q) :
    cw101ProjectZ (K := K) q (cwVariable (K := K) q (cwMiddle q i)) =
      Matrix.single 0 i 1 := by
  ext row col
  fin_cases row
  simp [cw101ProjectZ, cwVariable, CoordinateTensor.basisVector]

/-- The `(1,0,1)` constituent restricts to `⟨q,1,1⟩`. -/
theorem cw101_restricts_matrixMultiplication (q : ℕ) :
    Restricts (cw101 (K := K) q) (matrixMultiplicationTensor K q 1 1) := by
  refine ⟨cw101ProjectX (K := K) q, cw101ProjectY (K := K) q,
    cw101ProjectZ (K := K) q, ?_⟩
  simp [cw101, matrixMultiplicationTensor]

end TriTensor
end AlgebraicComplexity
