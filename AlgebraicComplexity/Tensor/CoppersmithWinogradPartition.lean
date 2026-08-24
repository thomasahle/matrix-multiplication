import AlgebraicComplexity.Tensor.CoppersmithWinograd
import Mathlib.Tactic

set_option linter.style.header false

/-!
# The six constituent blocks of the Coppersmith--Winograd tensor

The standard partition has tight support
`{(0,0,2), (0,1,1), (1,0,1), (1,1,0), (0,2,0), (2,0,0)}`.
This file makes each constituent an explicit abstract trilinear tensor and proves that their sum is
`CW_q`.
-/

namespace AlgebraicComplexity
namespace TriTensor

universe u

variable {K : Type u} [CommSemiring K]

/-- The six labels in the standard `CW_q` partition. -/
inductive CWConstituent
  | c002 | c011 | c101 | c110 | c020 | c200
  deriving DecidableEq, Fintype

namespace CWConstituent

/-- Shape of a constituent in the three variable blocks `0`, `1`, `2`. -/
def shape : CWConstituent → Fin 3 → ℕ
  | c002 => ![0, 0, 2]
  | c011 => ![0, 1, 1]
  | c101 => ![1, 0, 1]
  | c110 => ![1, 1, 0]
  | c020 => ![0, 2, 0]
  | c200 => ![2, 0, 0]

/-- Every support shape is tight of total degree two. -/
theorem shape_tight (s : CWConstituent) :
    ∑ d : Fin 3, s.shape d = 2 := by
  cases s <;> decide

/-- Cyclically rotate a constituent label. -/
def cycleLeft : CWConstituent → CWConstituent
  | c002 => c020
  | c020 => c200
  | c200 => c002
  | c011 => c110
  | c110 => c101
  | c101 => c011

@[simp]
theorem cycleLeft_three (s : CWConstituent) :
    s.cycleLeft.cycleLeft.cycleLeft = s := by
  cases s <;> rfl

end CWConstituent

/-- The `(0,0,2)` corner constituent. -/
def cw002 (q : ℕ) :
    TriTensor K (CWVariableSpace K q) (CWVariableSpace K q) (CWVariableSpace K q) :=
  pure
    (cwVariable (K := K) q (cwZero q))
    (cwVariable (K := K) q (cwZero q))
    (cwVariable (K := K) q (cwLast q))

/-- The `(0,2,0)` corner constituent. -/
def cw020 (q : ℕ) :
    TriTensor K (CWVariableSpace K q) (CWVariableSpace K q) (CWVariableSpace K q) :=
  pure
    (cwVariable (K := K) q (cwZero q))
    (cwVariable (K := K) q (cwLast q))
    (cwVariable (K := K) q (cwZero q))

/-- The `(2,0,0)` corner constituent. -/
def cw200 (q : ℕ) :
    TriTensor K (CWVariableSpace K q) (CWVariableSpace K q) (CWVariableSpace K q) :=
  pure
    (cwVariable (K := K) q (cwLast q))
    (cwVariable (K := K) q (cwZero q))
    (cwVariable (K := K) q (cwZero q))

/-- The `(0,1,1)` constituent with `q` diagonal terms. -/
def cw011 (q : ℕ) :
    TriTensor K (CWVariableSpace K q) (CWVariableSpace K q) (CWVariableSpace K q) :=
  ∑ i : Fin q,
    pure
      (cwVariable (K := K) q (cwZero q))
      (cwVariable (K := K) q (cwMiddle q i))
      (cwVariable (K := K) q (cwMiddle q i))

/-- The `(1,0,1)` constituent with `q` diagonal terms. -/
def cw101 (q : ℕ) :
    TriTensor K (CWVariableSpace K q) (CWVariableSpace K q) (CWVariableSpace K q) :=
  ∑ i : Fin q,
    pure
      (cwVariable (K := K) q (cwMiddle q i))
      (cwVariable (K := K) q (cwZero q))
      (cwVariable (K := K) q (cwMiddle q i))

/-- The `(1,1,0)` constituent with `q` diagonal terms. -/
def cw110 (q : ℕ) :
    TriTensor K (CWVariableSpace K q) (CWVariableSpace K q) (CWVariableSpace K q) :=
  ∑ i : Fin q,
    pure
      (cwVariable (K := K) q (cwMiddle q i))
      (cwVariable (K := K) q (cwMiddle q i))
      (cwVariable (K := K) q (cwZero q))

/-- Interpret a constituent label as its tensor. -/
def cwConstituent (q : ℕ) : CWConstituent →
    TriTensor K (CWVariableSpace K q) (CWVariableSpace K q) (CWVariableSpace K q)
  | .c002 => cw002 q
  | .c011 => cw011 q
  | .c101 => cw101 q
  | .c110 => cw110 q
  | .c020 => cw020 q
  | .c200 => cw200 q

/-- The six constituent tensors sum exactly to `CW_q`. -/
theorem sum_cwConstituents (q : ℕ) :
    ∑ s : CWConstituent, cwConstituent (K := K) q s =
      coppersmithWinogradTensor K q := by
  classical
  simp [cwConstituent, cw002, cw011, cw101, cw110, cw020, cw200,
    coppersmithWinogradTensor, coppersmithWinogradMiddle,
    coppersmithWinogradCorners]
  abel

/-- Cyclic rotation sends the `(0,0,2)` corner to `(0,2,0)`. -/
@[simp]
theorem cycleLeft_cw002 (q : ℕ) : cycleLeft (cw002 (K := K) q) = cw020 q := by
  simp [cw002, cw020]

/-- Cyclic rotation sends `(0,2,0)` to `(2,0,0)`. -/
@[simp]
theorem cycleLeft_cw020 (q : ℕ) : cycleLeft (cw020 (K := K) q) = cw200 q := by
  simp [cw020, cw200]

/-- Cyclic rotation sends `(2,0,0)` back to `(0,0,2)`. -/
@[simp]
theorem cycleLeft_cw200 (q : ℕ) : cycleLeft (cw200 (K := K) q) = cw002 q := by
  simp [cw200, cw002]

/-- Cyclic rotation sends `(0,1,1)` to `(1,1,0)`. -/
@[simp]
theorem cycleLeft_cw011 (q : ℕ) : cycleLeft (cw011 (K := K) q) = cw110 q := by
  simp [cw011, cw110]

/-- Cyclic rotation sends `(1,1,0)` to `(1,0,1)`. -/
@[simp]
theorem cycleLeft_cw110 (q : ℕ) : cycleLeft (cw110 (K := K) q) = cw101 q := by
  simp [cw110, cw101]

/-- Cyclic rotation sends `(1,0,1)` back to `(0,1,1)`. -/
@[simp]
theorem cycleLeft_cw101 (q : ℕ) : cycleLeft (cw101 (K := K) q) = cw011 q := by
  simp [cw101, cw011]

end TriTensor
end AlgebraicComplexity
