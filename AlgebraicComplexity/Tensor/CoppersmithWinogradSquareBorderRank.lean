import AlgebraicComplexity.Tensor.BorderRankProduct
import AlgebraicComplexity.Tensor.CoppersmithWinogradBorderRankTheorem

set_option linter.style.header false

/-!
# Border rank of the tensor square of `CW_q`

The constructive `q+2` border-rank degeneration tensor-products with itself.  Consequently the
coordinate tensor square of `CW_q` has border rank at most `(q+2)^2`; in particular, the `q=6`
square used in the original Coppersmith--Winograd analysis has border rank at most `64`.
-/

namespace AlgebraicComplexity
namespace CoordinateTensor

universe u

variable {K : Type u} [CommRing K]

/-- Coordinate external square of the big Coppersmith--Winograd tensor. -/
def coppersmithWinogradCoordinateSquare (K : Type u) [CommRing K] (q : ℕ) :
    CoordinateTensor K (CWIndex q × CWIndex q) (CWIndex q × CWIndex q)
      (CWIndex q × CWIndex q) :=
  CoordinateTensor.externalProduct
    (coppersmithWinogradCoordinateTensor K q)
    (coppersmithWinogradCoordinateTensor K q)

/-- The coordinate square of `CW_q` has constructive border rank at most `(q+2)^2`. -/
theorem coppersmithWinogradSquare_borderRank_le (q : ℕ) :
    HasBorderRankAtMost ((q + 2) * (q + 2))
      (coppersmithWinogradCoordinateSquare K q) := by
  exact HasBorderRankAtMost.externalProduct
    (coppersmithWinograd_borderRank_le (K := K) q)
    (coppersmithWinograd_borderRank_le (K := K) q)

/-- The historical `q=6` square has border rank at most `64`. -/
theorem coppersmithWinogradSixSquare_borderRank_le_sixtyFour :
    HasBorderRankAtMost 64 (coppersmithWinogradCoordinateSquare K 6) := by
  simpa using coppersmithWinogradSquare_borderRank_le (K := K) 6

#print axioms coppersmithWinogradSquare_borderRank_le
#print axioms coppersmithWinogradSixSquare_borderRank_le_sixtyFour

end CoordinateTensor
end AlgebraicComplexity
