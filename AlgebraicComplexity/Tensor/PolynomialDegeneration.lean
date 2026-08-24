import AlgebraicComplexity.Tensor.MonomialDegeneration
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Constructive polynomial degenerations and border-rank certificates

For a coordinate tensor, a border-rank upper bound can be certified without invoking topology.
A certificate consists of a finite polynomial family of rank-one tensors whose coefficients below a
chosen order vanish and whose coefficient at that order is the target tensor.
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

/-- Sum a family of polynomial rank-one tensors indexed by `Fin n`. -/
noncomputable def realizePolynomialFamily {n : ℕ}
    (terms : Fin n → PolynomialPureTerm (K := K) (I := I) (J := J) (L := L)) :
    CoordinateTensor (Polynomial K) I J L :=
  fun i j k => ∑ a : Fin n, (terms a).toTensor i j k

@[simp]
theorem realizePolynomialFamily_zero
    (terms : Fin 0 → PolynomialPureTerm (K := K) (I := I) (J := J) (L := L)) :
    realizePolynomialFamily terms = 0 := by
  funext i j k
  simp [realizePolynomialFamily]

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
A constructive border-rank certificate. The polynomial family has at most `r` rank-one members,
vanishes below `order`, and has target tensor `T` as its coefficient at `order`.
-/
noncomputable def HasBorderRankAtMost (r : ℕ) (T : CoordinateTensor K I J L) : Prop :=
  ∃ n : ℕ,
    n ≤ r ∧
      ∃ order : ℕ,
        ∃ terms : Fin n → PolynomialPureTerm (K := K) (I := I) (J := J) (L := L),
          VanishesBelow order (realizePolynomialFamily terms) ∧
          coeffTensor order (realizePolynomialFamily terms) = T

namespace HasBorderRankAtMost

/-- A concrete finite polynomial family yields a border-rank certificate. -/
theorem of_family
    {r n order : ℕ} {T : CoordinateTensor K I J L}
    (terms : Fin n → PolynomialPureTerm (K := K) (I := I) (J := J) (L := L))
    (hsize : n ≤ r)
    (hvanish : VanishesBelow order (realizePolynomialFamily terms))
    (hlead : coeffTensor order (realizePolynomialFamily terms) = T) :
    HasBorderRankAtMost r T :=
  ⟨n, hsize, order, terms, hvanish, hlead⟩

/-- Weakening the numerical upper bound preserves a border-rank certificate. -/
theorem mono {r s : ℕ} {T : CoordinateTensor K I J L}
    (h : HasBorderRankAtMost r T) (hrs : r ≤ s) : HasBorderRankAtMost s T := by
  rcases h with ⟨n, hn, order, terms, hvanish, hlead⟩
  exact ⟨n, hn.trans hrs, order, terms, hvanish, hlead⟩

end HasBorderRankAtMost
end CoordinateTensor
end AlgebraicComplexity
