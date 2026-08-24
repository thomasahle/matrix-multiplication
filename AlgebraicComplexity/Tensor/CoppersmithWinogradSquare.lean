import AlgebraicComplexity.Tensor.CoppersmithWinogradConstituents
import AlgebraicComplexity.Tensor.ExternalProduct

set_option linter.style.header false

/-!
# Components of the tensor square of `CW_q`

The historical Coppersmith--Winograd bound analyzes the second tensor power. This file exposes the
four orbit representatives used in that analysis. In particular, `cwSquare211` is definitionally the
four-term tight-support decomposition appearing in the classical proof.
-/

open scoped TensorProduct

namespace AlgebraicComplexity
namespace TriTensor

universe u

variable {K : Type u} [CommSemiring K]

/-- Coordinate space of one factor of `CW_q ⊠ CW_q`. -/
abbrev CWSquareVariableSpace (K : Type u) [CommSemiring K] (q : ℕ) :=
  CWVariableSpace K q ⊗[K] CWVariableSpace K q

/-- The representative component of shape `(4,0,0)`. -/
def cwSquare400 (q : ℕ) :
    TriTensor K (CWSquareVariableSpace K q)
      (CWSquareVariableSpace K q) (CWSquareVariableSpace K q) :=
  externalProduct (cw200 (K := K) q) (cw200 q)

/-- The representative component of shape `(3,1,0)`. -/
def cwSquare310 (q : ℕ) :
    TriTensor K (CWSquareVariableSpace K q)
      (CWSquareVariableSpace K q) (CWSquareVariableSpace K q) :=
  externalProduct (cw200 (K := K) q) (cw110 q) +
    externalProduct (cw110 (K := K) q) (cw200 q)

/-- The representative component of shape `(2,2,0)`. -/
def cwSquare220 (q : ℕ) :
    TriTensor K (CWSquareVariableSpace K q)
      (CWSquareVariableSpace K q) (CWSquareVariableSpace K q) :=
  externalProduct (cw200 (K := K) q) (cw020 q) +
    externalProduct (cw020 (K := K) q) (cw200 q) +
    externalProduct (cw110 (K := K) q) (cw110 q)

/-- First summand of the exceptional `(2,1,1)` component. -/
def cwSquare211a (q : ℕ) :
    TriTensor K (CWSquareVariableSpace K q)
      (CWSquareVariableSpace K q) (CWSquareVariableSpace K q) :=
  externalProduct (cw200 (K := K) q) (cw011 q)

/-- Second summand of the exceptional `(2,1,1)` component. -/
def cwSquare211b (q : ℕ) :
    TriTensor K (CWSquareVariableSpace K q)
      (CWSquareVariableSpace K q) (CWSquareVariableSpace K q) :=
  externalProduct (cw110 (K := K) q) (cw101 q)

/-- Third summand of the exceptional `(2,1,1)` component. -/
def cwSquare211c (q : ℕ) :
    TriTensor K (CWSquareVariableSpace K q)
      (CWSquareVariableSpace K q) (CWSquareVariableSpace K q) :=
  externalProduct (cw101 (K := K) q) (cw110 q)

/-- Fourth summand of the exceptional `(2,1,1)` component. -/
def cwSquare211d (q : ℕ) :
    TriTensor K (CWSquareVariableSpace K q)
      (CWSquareVariableSpace K q) (CWSquareVariableSpace K q) :=
  externalProduct (cw011 (K := K) q) (cw200 q)

/-- The exceptional component of shape `(2,1,1)`. -/
def cwSquare211 (q : ℕ) :
    TriTensor K (CWSquareVariableSpace K q)
      (CWSquareVariableSpace K q) (CWSquareVariableSpace K q) :=
  cwSquare211a (K := K) q + cwSquare211b q + cwSquare211c q + cwSquare211d q

/-- The displayed four-term decomposition of the exceptional component. -/
theorem cwSquare211_decomposition (q : ℕ) :
    cwSquare211 (K := K) q =
      externalProduct (cw200 (K := K) q) (cw011 q) +
      externalProduct (cw110 (K := K) q) (cw101 q) +
      externalProduct (cw101 (K := K) q) (cw110 q) +
      externalProduct (cw011 (K := K) q) (cw200 q) := by
  rfl

/-- Expanding the six constituents gives all 36 terms of the tensor square. -/
theorem externalProduct_cw_expansion (q : ℕ) :
    externalProduct (coppersmithWinogradTensor K q) (coppersmithWinogradTensor K q) =
      externalProduct
        (cw002 (K := K) q + cw011 q + cw101 q + cw110 q + cw020 q + cw200 q)
        (cw002 (K := K) q + cw011 q + cw101 q + cw110 q + cw020 q + cw200 q) := by
  rw [sum_cwConstituents]

end TriTensor
end AlgebraicComplexity
