import AlgebraicComplexity.Tensor.MonomialDegeneration
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Constructive polynomial degenerations and border-rank certificates

For a coordinate tensor, a border-rank upper bound can be certified without invoking topology.
A certificate consists of a polynomial family that is a sum of at most `r` rank-one tensors and
whose first nonzero coefficient is the target tensor. This is the constructive form used by
Coppersmith--Winograd degenerations.
-/

namespace AlgebraicComplexity
namespace CoordinateTensor

universe uK uI uJ uL

variable
    {K : Type uK} {I : Type uI} {J : Type uJ} {L : Type uL}
    [CommSemiring K]

/-- A rank-one tensor whose three coordinate vectors have polynomial entries. -/
structure PolynomialPureTerm where
  x : I → Polynomial K
  y : J → Polynomial K
  z : L → Polynomial K

namespace PolynomialPureTerm

/-- Interpret a polynomial rank-one witness as a polynomial coordinate tensor. -/
noncomputable def toTensor
    (p : PolynomialPureTerm (K := K) (I := I) (J := J) (L := L)) :
    CoordinateTensor (Polynomial K) I J L :=
  fun i j k => p.x i * p.y j * p.z k

@[simp]
theorem toTensor_apply
    (p : PolynomialPureTerm (K := K) (I := I) (J := J) (L := L))
    (i : I) (j : J) (k : L) :
    p.toTensor i j k = p.x i * p.y j * p.z k :=
  rfl

end PolynomialPureTerm

/-- Sum a finite list of polynomial rank-one tensors. -/
noncomputable def realizePolynomial
    (terms : List (PolynomialPureTerm (K := K) (I := I) (J := J) (L := L))) :
    CoordinateTensor (Polynomial K) I J L :=
  fun i j k => (terms.map fun p => p.toTensor i j k).sum

@[simp]
theorem realizePolynomial_nil :
    realizePolynomial
      ([] : List (PolynomialPureTerm (K := K) (I := I) (J := J) (L := L))) = 0 := by
  rfl

@[simp]
theorem realizePolynomial_cons
    (p : PolynomialPureTerm (K := K) (I := I) (J := J) (L := L))
    (terms : List (PolynomialPureTerm (K := K) (I := I) (J := J) (L := L))) :
    realizePolynomial (p :: terms) = p.toTensor + realizePolynomial terms := by
  funext i j k
  simp [realizePolynomial]

@[simp]
theorem realizePolynomial_append
    (left right : List (PolynomialPureTerm (K := K) (I := I) (J := J) (L := L))) :
    realizePolynomial (left ++ right) = realizePolynomial left + realizePolynomial right := by
  funext i j k
  simp [realizePolynomial]

/-- Take one coefficient of every coordinate polynomial. -/
def coeffTensor (degree : ℕ) (T : CoordinateTensor (Polynomial K) I J L) :
    CoordinateTensor K I J L :=
  fun i j k => (T i j k).coeff degree

@[simp]
theorem coeffTensor_apply
    (degree : ℕ) (T : CoordinateTensor (Polynomial K) I J L)
    (i : I) (j : J) (k : L) :
    coeffTensor degree T i j k = (T i j k).coeff degree :=
  rfl

@[simp]
theorem coeffTensor_zero (degree : ℕ) :
    coeffTensor degree (0 : CoordinateTensor (Polynomial K) I J L) = 0 := by
  rfl

@[simp]
theorem coeffTensor_add (degree : ℕ)
    (T S : CoordinateTensor (Polynomial K) I J L) :
    coeffTensor degree (T + S) = coeffTensor degree T + coeffTensor degree S := by
  funext i j k
  simp [coeffTensor]

/-- Every coefficient below `order` vanishes. -/
def VanishesBelow (order : ℕ) (T : CoordinateTensor (Polynomial K) I J L) : Prop :=
  ∀ degree < order, coeffTensor degree T = 0

/--
A constructive border-rank certificate. The polynomial family represented by `terms` vanishes below
`order`, and its coefficient of degree `order` is exactly `T`.
-/
noncomputable def HasBorderRankAtMost (r : ℕ) (T : CoordinateTensor K I J L) : Prop :=
  ∃ order : ℕ,
    ∃ terms : List (PolynomialPureTerm (K := K) (I := I) (J := J) (L := L)),
      terms.length ≤ r ∧
      VanishesBelow order (realizePolynomial terms) ∧
      coeffTensor order (realizePolynomial terms) = T

namespace HasBorderRankAtMost

/-- A concrete polynomial family yields a border-rank certificate. -/
theorem of_terms
    {r order : ℕ} {T : CoordinateTensor K I J L}
    (terms : List (PolynomialPureTerm (K := K) (I := I) (J := J) (L := L)))
    (hlen : terms.length ≤ r)
    (hvanish : VanishesBelow order (realizePolynomial terms))
    (hlead : coeffTensor order (realizePolynomial terms) = T) :
    HasBorderRankAtMost r T :=
  ⟨order, terms, hlen, hvanish, hlead⟩

/-- Weakening the numerical upper bound preserves a border-rank certificate. -/
theorem mono {r s : ℕ} {T : CoordinateTensor K I J L}
    (h : HasBorderRankAtMost r T) (hrs : r ≤ s) : HasBorderRankAtMost s T := by
  rcases h with ⟨order, terms, hlen, hvanish, hlead⟩
  exact ⟨order, terms, hlen.trans hrs, hvanish, hlead⟩

end HasBorderRankAtMost
end CoordinateTensor
end AlgebraicComplexity
