/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinogradCore
import AlgebraicComplexity.MatrixMultiplication.Core
import AlgebraicComplexity.Tensor.BorderRank
import AlgebraicComplexity.Tensor.Monomial
import Mathlib.Tactic.IntervalCases

/-!
# The Coppersmith--Winograd tensor

This file defines the full Coppersmith--Winograd tensor in a named coordinate space and verifies
its classical `q + 2` polynomial border-rank certificate.  It is deliberately a downstream
regression client: the polynomial and border-rank APIs contain no CW-specific definitions.

## Algebraic hypotheses

The file is split by the weakest hypothesis each result actually needs.

* `section Semiring` (`[CommSemiring K]`): the basis vectors, the summands `cwMiddle` and
  `cwCorners`, the tensor `coppersmithWinograd` itself, its monomial degeneration onto the
  middle block, and the three exact restrictions onto `⟨1,1,q⟩`, `⟨q,1,1⟩`, `⟨1,q,1⟩`.  These
  are all sums and coordinate projections, so no subtraction is involved.
* `section Ring` (`[CommRing K]`): the polynomial approximation curves and the border-rank
  certificate `coppersmithWinograd_borderRankLE`.  Subtraction is essential here: the
  cancellation curve carries the negated degree-zero and degree-three terms.

Downstream clients over a field are unaffected by the split.

Primary source: D. Coppersmith and S. Winograd, *Matrix multiplication via arithmetic
progressions*, J. Symbolic Comput. **9** (1990), 251--280.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor
open Tensor.PolynomialVector

universe u

section Semiring

variable (K : Type u) [CommSemiring K]
variable (q : ℕ)

private abbrev e₀ : CWIndex q → K := cwZeroVector K q
private abbrev e₂ : CWIndex q → K := cwLastVector K q
private abbrev e₁ (i : Fin q) : CWIndex q → K := cwMiddleVector K q i

/-- Weight the final CW coordinate positively and every other coordinate by zero. -/
def cwMiddleWeight (_ : Leg) : CWIndex q → ℕ
  | .last => 1
  | _ => 0

/-- A basic laser-method regression: diagonal monomial weighting removes the three corner terms
and retains precisely the middle block of the full CW tensor. -/
theorem coppersmithWinograd_monomialDegenerates_middle :
    MonomialDegenerates
      (coppersmithWinograd K q)
      (∑ i : Fin q, cwMiddle K q i) := by
  refine ⟨cwMiddleWeight q, 0, ?_⟩
  constructor
  · unfold coppersmithWinograd
    rw [monomialTransform_add, monomialTransform_fintype_sum]
    simp_rw [cwMiddle, monomialTransform_add]
    unfold cwCorners
    simp_rw [monomialTransform_add]
    simp [cwMiddleWeight, monomialTransform_basis_ofLegs,
      cwBasis]
  · intro e he
    omega

/-- Select the `(0,1,1)` CW constituent and identify its coordinates with `⟨1,1,q⟩`. -/
def cw011Index : ∀ c, MMIndex 1 1 q c → CWIndex q
  | .X => fun _ ↦ .zero
  | .Y => fun a ↦ .middle a.2
  | .Z => fun a ↦ .middle a.1

/-- Coordinate projection from the full CW spaces to the `(0,1,1)` constituent. -/
def cw011Map : ∀ c, CWSpace K q c →ₗ[K] MMSpace K 1 1 q c :=
  fun c ↦ LinearMap.funLeft K K (cw011Index q c)

/-- Projecting `CW_q` to its `(0,1,1)` constituent gives the matrix-multiplication tensor
`⟨1,1,q⟩`. -/
theorem map_cw011Map_coppersmithWinograd :
    map (cw011Map K q) (coppersmithWinograd K q) =
      matrixMultiplication (K := K) 1 1 q := by
  apply standardCoordinate_ext
  intro a
  unfold cw011Map
  rw [standardCoordinateEquiv_map_funLeft]
  rcases hX : a .X with ⟨i, j⟩
  rcases hY : a .Y with ⟨j', k⟩
  rcases hZ : a .Z with ⟨k', i'⟩
  fin_cases i
  fin_cases j
  fin_cases j'
  fin_cases i'
  simp [coppersmithWinograd, cwMiddle, cwCorners, cw011Index,
    cwBasis, Pi.single_apply, hX, hY, hZ,
    standardCoordinateEquiv_pure, prod_leg, matrixMultiplication,
    mmTermOfTriple, mmTerm, Fintype.sum_prod_type]

/-- The full CW tensor exactly restricts to the rectangular tensor `⟨1,1,q⟩`. -/
theorem coppersmithWinograd_restricts_011 :
    Restricts (coppersmithWinograd K q)
      (matrixMultiplication (K := K) 1 1 q) :=
  ⟨cw011Map K q, map_cw011Map_coppersmithWinograd K q⟩

/-- Select the `(1,0,1)` CW constituent and identify it with `⟨q,1,1⟩`. -/
def cw101Index : ∀ c, MMIndex q 1 1 c → CWIndex q
  | .X => fun a ↦ .middle a.1
  | .Y => fun _ ↦ .zero
  | .Z => fun a ↦ .middle a.2

def cw101Map : ∀ c, CWSpace K q c →ₗ[K] MMSpace K q 1 1 c :=
  fun c ↦ LinearMap.funLeft K K (cw101Index q c)

theorem map_cw101Map_coppersmithWinograd :
    map (cw101Map K q) (coppersmithWinograd K q) =
      matrixMultiplication (K := K) q 1 1 := by
  apply standardCoordinate_ext
  intro a
  unfold cw101Map
  rw [standardCoordinateEquiv_map_funLeft]
  rcases hX : a .X with ⟨i, j⟩
  rcases hY : a .Y with ⟨j', k⟩
  rcases hZ : a .Z with ⟨k', i'⟩
  fin_cases j
  fin_cases j'
  fin_cases k
  fin_cases k'
  simp [coppersmithWinograd, cwMiddle, cwCorners, cw101Index,
    cwBasis, Pi.single_apply, hX, hY, hZ,
    standardCoordinateEquiv_pure, prod_leg, matrixMultiplication,
    mmTermOfTriple, mmTerm, Fintype.sum_prod_type]

theorem coppersmithWinograd_restricts_101 :
    Restricts (coppersmithWinograd K q)
      (matrixMultiplication (K := K) q 1 1) :=
  ⟨cw101Map K q, map_cw101Map_coppersmithWinograd K q⟩

/-- Select the `(1,1,0)` CW constituent and identify it with `⟨1,q,1⟩`. -/
def cw110Index : ∀ c, MMIndex 1 q 1 c → CWIndex q
  | .X => fun a ↦ .middle a.2
  | .Y => fun a ↦ .middle a.1
  | .Z => fun _ ↦ .zero

def cw110Map : ∀ c, CWSpace K q c →ₗ[K] MMSpace K 1 q 1 c :=
  fun c ↦ LinearMap.funLeft K K (cw110Index q c)

theorem map_cw110Map_coppersmithWinograd :
    map (cw110Map K q) (coppersmithWinograd K q) =
      matrixMultiplication (K := K) 1 q 1 := by
  apply standardCoordinate_ext
  intro a
  unfold cw110Map
  rw [standardCoordinateEquiv_map_funLeft]
  rcases hX : a .X with ⟨i, j⟩
  rcases hY : a .Y with ⟨j', k⟩
  rcases hZ : a .Z with ⟨k', i'⟩
  fin_cases i
  fin_cases k
  fin_cases k'
  fin_cases i'
  simp [coppersmithWinograd, cwMiddle, cwCorners, cw110Index,
    cwBasis, Pi.single_apply, hX, hY, hZ,
    standardCoordinateEquiv_pure, prod_leg, matrixMultiplication,
    mmTermOfTriple, mmTerm, Fintype.sum_prod_type]

theorem coppersmithWinograd_restricts_110 :
    Restricts (coppersmithWinograd K q)
      (matrixMultiplication (K := K) 1 q 1) :=
  ⟨cw110Map K q, map_cw110Map_coppersmithWinograd K q⟩

end Semiring

section Ring

variable (K : Type u) [CommRing K]
variable (q : ℕ)

private noncomputable def cwBase : Tensor3 K (CWSpace K q) :=
  pure (K := K) (ofLegs (e₀ K q) (e₀ K q) (e₀ K q))

private noncomputable def cwLinear (i : Fin q) : Tensor3 K (CWSpace K q) :=
  pure (K := K) (ofLegs (e₁ K q i) (e₀ K q) (e₀ K q)) +
  pure (K := K) (ofLegs (e₀ K q) (e₁ K q i) (e₀ K q)) +
  pure (K := K) (ofLegs (e₀ K q) (e₀ K q) (e₁ K q i))

private abbrev PolyVec := PolynomialVector (CWIndex q → K)

/-- One of the `q` rank-one polynomial curves in the CW approximation. -/
noncomputable def cwIndexedCurve (i : Fin q) : ∀ _ : Leg, PolyVec K q :=
  ofLegs
    (monomial 1 (e₀ K q) + monomial 3 (e₁ K q i))
    (constant (e₀ K q) + monomial 2 (e₁ K q i))
    (constant (e₀ K q) + monomial 2 (e₁ K q i))

@[simp] theorem cwIndexedCurve_coeff_zero (i : Fin q) :
    polynomialPure (K := K) (cwIndexedCurve K q i) 0 = 0 := by
  simp [cwIndexedCurve, constant]

@[simp] theorem cwIndexedCurve_coeff_one (i : Fin q) :
    polynomialPure (K := K) (cwIndexedCurve K q i) 1 = cwBase K q := by
  simp [cwIndexedCurve, cwBase, constant]

@[simp] theorem cwIndexedCurve_coeff_two (i : Fin q) :
    polynomialPure (K := K) (cwIndexedCurve K q i) 2 = 0 := by
  simp [cwIndexedCurve, constant]

@[simp] theorem cwIndexedCurve_coeff_three (i : Fin q) :
    polynomialPure (K := K) (cwIndexedCurve K q i) 3 = cwLinear K q i := by
  simp [cwIndexedCurve, cwLinear, constant]

@[simp] theorem cwIndexedCurve_coeff_four (i : Fin q) :
    polynomialPure (K := K) (cwIndexedCurve K q i) 4 = 0 := by
  simp [cwIndexedCurve, constant]

@[simp] theorem cwIndexedCurve_coeff_five (i : Fin q) :
    polynomialPure (K := K) (cwIndexedCurve K q i) 5 = cwMiddle K q i := by
  simp [cwIndexedCurve, cwMiddle, constant]
  abel

private noncomputable def middleBasisSum : CWIndex q → K :=
  ∑ i : Fin q, e₁ K q i

/-- The rank-one curve cancelling the degree-zero and degree-three terms. -/
noncomputable def cwCancellationCurve : ∀ _ : Leg, PolyVec K q :=
  ofLegs
    (monomial 0 (-e₀ K q) + monomial 3 (-middleBasisSum K q))
    (constant (e₀ K q) + monomial 3 (middleBasisSum K q))
    (constant (e₀ K q) + monomial 3 (middleBasisSum K q))

@[simp] theorem cwCancellationCurve_coeff_zero :
    polynomialPure (K := K) (cwCancellationCurve K q) 0 = -cwBase K q := by
  simp [cwCancellationCurve, cwBase, constant]

@[simp] theorem cwCancellationCurve_coeff_one :
    polynomialPure (K := K) (cwCancellationCurve K q) 1 = 0 := by
  simp [cwCancellationCurve, constant]

@[simp] theorem cwCancellationCurve_coeff_two :
    polynomialPure (K := K) (cwCancellationCurve K q) 2 = 0 := by
  simp [cwCancellationCurve, constant]

@[simp] theorem cwCancellationCurve_coeff_three :
    polynomialPure (K := K) (cwCancellationCurve K q) 3 =
      -(∑ i : Fin q, cwLinear K q i) := by
  classical
  simp [cwCancellationCurve, middleBasisSum, cwLinear, constant,
    pure_ofLegs_fintype_sum_X, pure_ofLegs_fintype_sum_Y,
    pure_ofLegs_fintype_sum_Z]
  simp_rw [Finset.sum_add_distrib]
  abel

@[simp] theorem cwCancellationCurve_coeff_four :
    polynomialPure (K := K) (cwCancellationCurve K q) 4 = 0 := by
  simp [cwCancellationCurve, constant]

@[simp] theorem cwCancellationCurve_coeff_five :
    polynomialPure (K := K) (cwCancellationCurve K q) 5 = 0 := by
  simp [cwCancellationCurve, constant]

/-- The final rank-one curve supplies the three corner terms and cancels degree one. -/
noncomputable def cwCornerCurve : ∀ _ : Leg, PolyVec K q :=
  ofLegs
    (monomial 0 (e₀ K q) +
      monomial 1 (-((q : K) • e₀ K q)) +
      monomial 5 (e₂ K q) +
      monomial 6 (-((q : K) • e₂ K q)))
    (constant (e₀ K q) + monomial 5 (e₂ K q))
    (constant (e₀ K q) + monomial 5 (e₂ K q))

@[simp] theorem cwCornerCurve_coeff_zero :
    polynomialPure (K := K) (cwCornerCurve K q) 0 = cwBase K q := by
  simp [cwCornerCurve, cwBase, constant]

@[simp] theorem cwCornerCurve_coeff_one :
    polynomialPure (K := K) (cwCornerCurve K q) 1 =
      -((q : K) • cwBase K q) := by
  simp [cwCornerCurve, cwBase, constant]

@[simp] theorem cwCornerCurve_coeff_two :
    polynomialPure (K := K) (cwCornerCurve K q) 2 = 0 := by
  simp [cwCornerCurve, constant]

@[simp] theorem cwCornerCurve_coeff_three :
    polynomialPure (K := K) (cwCornerCurve K q) 3 = 0 := by
  simp [cwCornerCurve, constant]

@[simp] theorem cwCornerCurve_coeff_four :
    polynomialPure (K := K) (cwCornerCurve K q) 4 = 0 := by
  simp [cwCornerCurve, constant]

@[simp] theorem cwCornerCurve_coeff_five :
    polynomialPure (K := K) (cwCornerCurve K q) 5 = cwCorners K q := by
  simp [cwCornerCurve, cwCorners, constant]

/-- The explicit list of `q + 2` polynomial pure tensors in the CW approximation. -/
noncomputable def cwBorderTerms : List (∀ _ : Leg, PolyVec K q) :=
  (Finset.univ : Finset (Fin q)).toList.map (cwIndexedCurve K q) ++
    [cwCancellationCurve K q, cwCornerCurve K q]

@[simp] theorem cwBorderTerms_length : (cwBorderTerms K q).length = q + 2 := by
  classical
  simp [cwBorderTerms]

/-- The polynomial tensor path represented by the explicit CW certificate. -/
noncomputable def cwBorderPath : PolynomialTensor K (CWSpace K q) :=
  (cwBorderTerms K q).map (polynomialPure (K := K)) |>.sum

theorem cwBorderPath_eq :
    cwBorderPath K q =
      (∑ i : Fin q, polynomialPure (K := K) (cwIndexedCurve K q i)) +
        polynomialPure (K := K) (cwCancellationCurve K q) +
        polynomialPure (K := K) (cwCornerCurve K q) := by
  classical
  simp [cwBorderPath, cwBorderTerms, Function.comp_def, add_assoc]

/-- The CW polynomial path has the full CW tensor as its degree-five leading term. -/
theorem cwBorderPath_leading :
    HasLeadingTerm (cwBorderPath K q) 5 (coppersmithWinograd K q) := by
  rw [cwBorderPath_eq]
  constructor
  · simp [coppersmithWinograd]
  · intro d hd
    interval_cases d <;>
      simp [Nat.cast_smul_eq_nsmul]

/-- The classical constructive bound `borderRank(CW_q) ≤ q + 2`. -/
theorem coppersmithWinograd_borderRankLE :
    BorderRankLE (q + 2) (coppersmithWinograd K q) := by
  refine ⟨5, cwBorderTerms K q, ?_, cwBorderPath_leading K q⟩
  simp

end Ring

end AlgebraicComplexity.Examples
