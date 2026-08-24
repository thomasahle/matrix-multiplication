import AlgebraicComplexity.Tensor.PolynomialDegeneration
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Border rank under coordinate external products

Constructive polynomial border-rank certificates multiply. If two polynomial curves first become
nonzero in degrees `a` and `b`, their external product first becomes nonzero in degree `a+b`, and
its leading coefficient is the external product of the two leading coefficients.
-/

namespace AlgebraicComplexity
namespace CoordinateTensor

universe u

variable
    {K I J L I' J' L' : Type u}
    [CommSemiring K]

/-- Pair the coordinates of two coordinate tensors and multiply their coefficients. -/
def externalProduct
    (T : CoordinateTensor K I J L) (S : CoordinateTensor K I' J' L') :
    CoordinateTensor K (I × I') (J × J') (L × L') :=
  fun i j k => T i.1 j.1 k.1 * S i.2 j.2 k.2

@[simp]
theorem externalProduct_apply
    (T : CoordinateTensor K I J L) (S : CoordinateTensor K I' J' L')
    (i : I × I') (j : J × J') (k : L × L') :
    externalProduct T S i j k = T i.1 j.1 k.1 * S i.2 j.2 k.2 :=
  rfl

namespace PolynomialPureTerm

/-- Pair two polynomial rank-one witnesses coordinatewise. -/
noncomputable def externalProduct
    (p : PolynomialPureTerm (K := K) (I := I) (J := J) (L := L))
    (q : PolynomialPureTerm (K := K) (I := I') (J := J') (L := L')) :
    PolynomialPureTerm (K := K) (I := I × I') (J := J × J') (L := L × L') where
  x i := p.x i.1 * q.x i.2
  y j := p.y j.1 * q.y j.2
  z k := p.z k.1 * q.z k.2

@[simp]
theorem toTensor_externalProduct
    (p : PolynomialPureTerm (K := K) (I := I) (J := J) (L := L))
    (q : PolynomialPureTerm (K := K) (I := I') (J := J') (L := L')) :
    (p.externalProduct q).toTensor =
      CoordinateTensor.externalProduct p.toTensor q.toTensor := by
  funext i j k
  simp [PolynomialPureTerm.externalProduct, PolynomialPureTerm.toTensor,
    CoordinateTensor.externalProduct]
  ring

end PolynomialPureTerm

/-- Sum polynomial pure tensors over an arbitrary finite index type. -/
noncomputable def realizePolynomialFintypeFamily
    {A : Type u} [Fintype A]
    (terms : A → PolynomialPureTerm (K := K) (I := I) (J := J) (L := L)) :
    CoordinateTensor (Polynomial K) I J L :=
  fun i j k => ∑ a : A, (terms a).toTensor i j k

/-- Reindex an arbitrary finite family by the canonical `Fin` type of the same cardinality. -/
noncomputable def finReindexPolynomialFamily
    {A : Type u} [Fintype A]
    (terms : A → PolynomialPureTerm (K := K) (I := I) (J := J) (L := L)) :
    Fin (Fintype.card A) → PolynomialPureTerm (K := K) (I := I) (J := J) (L := L) :=
  fun i => terms ((Fintype.equivFin A).symm i)

/-- Reindexing a finite family does not change its realized polynomial tensor. -/
theorem realize_finReindexPolynomialFamily
    {A : Type u} [Fintype A]
    (terms : A → PolynomialPureTerm (K := K) (I := I) (J := J) (L := L)) :
    realizePolynomialFamily (finReindexPolynomialFamily terms) =
      realizePolynomialFintypeFamily terms := by
  classical
  funext i j k
  exact Fintype.sum_equiv (Fintype.equivFin A).symm
    (fun x => (terms ((Fintype.equivFin A).symm x)).toTensor i j k)
    (fun x => (terms x).toTensor i j k)
    (fun _ => rfl)

namespace HasBorderRankAtMost

/-- A polynomial family indexed by any finite type gives a border-rank certificate. -/
theorem of_fintype_family
    {A : Type u} [Fintype A]
    {r order : ℕ} {T : CoordinateTensor K I J L}
    (terms : A → PolynomialPureTerm (K := K) (I := I) (J := J) (L := L))
    (hsize : Fintype.card A ≤ r)
    (hvanish : VanishesBelow order (realizePolynomialFintypeFamily terms))
    (hlead : coeffTensor order (realizePolynomialFintypeFamily terms) = T) :
    HasBorderRankAtMost r T := by
  refine HasBorderRankAtMost.of_family (order := order)
    (finReindexPolynomialFamily terms) hsize ?_ ?_
  · rw [realize_finReindexPolynomialFamily]
    exact hvanish
  · rw [realize_finReindexPolynomialFamily]
    exact hlead

end HasBorderRankAtMost

/-- Realization of the Cartesian product family is the coefficientwise external product. -/
theorem realizePolynomialFintypeFamily_externalProduct
    {A B : Type u} [Fintype A] [Fintype B]
    (left : A → PolynomialPureTerm (K := K) (I := I) (J := J) (L := L))
    (right : B → PolynomialPureTerm (K := K) (I := I') (J := J') (L := L')) :
    realizePolynomialFintypeFamily
        (fun p : A × B => (left p.1).externalProduct (right p.2)) =
      CoordinateTensor.externalProduct
        (realizePolynomialFintypeFamily left)
        (realizePolynomialFintypeFamily right) := by
  classical
  funext i j k
  rw [show (∑ p : A × B,
      ((left p.1).externalProduct (right p.2)).toTensor i j k) =
      ∑ a : A, ∑ b : B,
        ((left a).externalProduct (right b)).toTensor i j k by
    exact Fintype.sum_prod_type _]
  simp only [PolynomialPureTerm.toTensor_externalProduct,
    CoordinateTensor.externalProduct_apply]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.mul_sum]

/-- A scalar polynomial product vanishes below the sum of two vanishing orders. -/
theorem Polynomial.coeff_mul_eq_zero_of_lt_add
    (p q : Polynomial K) (a b degree : ℕ)
    (hp : ∀ d < a, p.coeff d = 0)
    (hq : ∀ d < b, q.coeff d = 0)
    (hdegree : degree < a + b) :
    (p * q).coeff degree = 0 := by
  rw [Polynomial.coeff_mul]
  apply Finset.sum_eq_zero
  intro x hx
  have hsum : x.1 + x.2 = degree := Finset.mem_antidiagonal.mp hx
  by_cases hxa : x.1 < a
  · rw [hp x.1 hxa, zero_mul]
  · have hxb : x.2 < b := by omega
    rw [hq x.2 hxb, mul_zero]

/-- At the sum of the two vanishing orders, only the product of leading coefficients survives. -/
theorem Polynomial.coeff_mul_add_orders
    (p q : Polynomial K) (a b : ℕ)
    (hp : ∀ d < a, p.coeff d = 0)
    (hq : ∀ d < b, q.coeff d = 0) :
    (p * q).coeff (a + b) = p.coeff a * q.coeff b := by
  rw [Polynomial.coeff_mul]
  refine Finset.sum_eq_single (a, b) ?_ ?_
  · intro x hx hne
    have hsum : x.1 + x.2 = a + b := Finset.mem_antidiagonal.mp hx
    by_cases hxa : x.1 < a
    · rw [hp x.1 hxa, zero_mul]
    · by_cases hxeq : x.1 = a
      · have hyeq : x.2 = b := by omega
        exact (hne (Prod.ext hxeq hyeq)).elim
      · have hxb : x.2 < b := by omega
        rw [hq x.2 hxb, mul_zero]
  · simp

/-- Tensor external products add polynomial vanishing orders. -/
theorem externalProduct_vanishesBelow
    {a b : ℕ}
    {T : CoordinateTensor (Polynomial K) I J L}
    {S : CoordinateTensor (Polynomial K) I' J' L'}
    (hT : VanishesBelow a T) (hS : VanishesBelow b S) :
    VanishesBelow (a + b) (CoordinateTensor.externalProduct T S) := by
  intro degree hdegree
  funext i j k
  apply Polynomial.coeff_mul_eq_zero_of_lt_add
  · intro d hd
    have h := congrFun (congrFun (congrFun (hT d hd) i.1) j.1) k.1
    simpa [coeffTensor] using h
  · intro d hd
    have h := congrFun (congrFun (congrFun (hS d hd) i.2) j.2) k.2
    simpa [coeffTensor] using h
  · exact hdegree

/-- The leading coefficient tensor of an external product is the product of leading tensors. -/
theorem coeffTensor_externalProduct_add_orders
    {a b : ℕ}
    {T : CoordinateTensor (Polynomial K) I J L}
    {S : CoordinateTensor (Polynomial K) I' J' L'}
    (hT : VanishesBelow a T) (hS : VanishesBelow b S) :
    coeffTensor (a + b) (CoordinateTensor.externalProduct T S) =
      CoordinateTensor.externalProduct (coeffTensor a T) (coeffTensor b S) := by
  funext i j k
  apply Polynomial.coeff_mul_add_orders
  · intro d hd
    have h := congrFun (congrFun (congrFun (hT d hd) i.1) j.1) k.1
    simpa [coeffTensor] using h
  · intro d hd
    have h := congrFun (congrFun (congrFun (hS d hd) i.2) j.2) k.2
    simpa [coeffTensor] using h

namespace HasBorderRankAtMost

/-- Constructive border-rank bounds multiply under coordinate external products. -/
theorem externalProduct
    {r s : ℕ}
    {T : CoordinateTensor K I J L}
    {S : CoordinateTensor K I' J' L'}
    (hT : HasBorderRankAtMost r T)
    (hS : HasBorderRankAtMost s S) :
    HasBorderRankAtMost (r * s) (CoordinateTensor.externalProduct T S) := by
  rcases hT with ⟨n, hn, a, left, hleftVanish, hleftLead⟩
  rcases hS with ⟨m, hm, b, right, hrightVanish, hrightLead⟩
  let terms : Fin n × Fin m →
      PolynomialPureTerm (K := K) (I := I × I') (J := J × J') (L := L × L') :=
    fun p => (left p.1).externalProduct (right p.2)
  refine of_fintype_family (A := Fin n × Fin m) (order := a + b) terms ?_ ?_ ?_
  · simpa using Nat.mul_le_mul hn hm
  · rw [realizePolynomialFintypeFamily_externalProduct]
    exact externalProduct_vanishesBelow hleftVanish hrightVanish
  · rw [realizePolynomialFintypeFamily_externalProduct,
      coeffTensor_externalProduct_add_orders hleftVanish hrightVanish,
      hleftLead, hrightLead]

end HasBorderRankAtMost

#print axioms Polynomial.coeff_mul_eq_zero_of_lt_add
#print axioms Polynomial.coeff_mul_add_orders
#print axioms HasBorderRankAtMost.externalProduct

end CoordinateTensor
end AlgebraicComplexity
