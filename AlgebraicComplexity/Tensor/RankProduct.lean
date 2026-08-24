import AlgebraicComplexity.Tensor.ExternalProduct
import AlgebraicComplexity.Tensor.Rank

set_option linter.style.header false

/-!
# Rank under external products

Concrete rank decompositions multiply under the external product of trilinear tensors.  The proof
constructs the Cartesian product of the two lists of rank-one witnesses.
-/

open scoped TensorProduct

namespace AlgebraicComplexity
namespace TriTensor

universe u

variable
    {K X Y Z X' Y' Z' : Type u}
    [CommSemiring K]
    [AddCommMonoid X] [AddCommMonoid Y] [AddCommMonoid Z]
    [AddCommMonoid X'] [AddCommMonoid Y'] [AddCommMonoid Z']
    [Module K X] [Module K Y] [Module K Z]
    [Module K X'] [Module K Y'] [Module K Z']

namespace PureTerm

/-- Pair two rank-one witnesses coordinatewise. -/
def externalProduct
    (p : PureTerm K X Y Z) (q : PureTerm K X' Y' Z') :
    PureTerm K (X ⊗[K] X') (Y ⊗[K] Y') (Z ⊗[K] Z') :=
  ⟨p.x ⊗ₜ[K] q.x, p.y ⊗ₜ[K] q.y, p.z ⊗ₜ[K] q.z⟩

@[simp]
theorem toTensor_externalProduct
    (p : PureTerm K X Y Z) (q : PureTerm K X' Y' Z') :
    (p.externalProduct q).toTensor =
      TriTensor.externalProduct p.toTensor q.toTensor := by
  cases p
  cases q
  rfl

end PureTerm

/-- Cartesian product of two lists of pure tensor witnesses. -/
def externalProductTerms
    (left : List (PureTerm K X Y Z))
    (right : List (PureTerm K X' Y' Z')) :
    List (PureTerm K (X ⊗[K] X') (Y ⊗[K] Y') (Z ⊗[K] Z')) :=
  left.flatMap fun p => right.map p.externalProduct

@[simp]
theorem externalProductTerms_nil_left
    (right : List (PureTerm K X' Y' Z')) :
    externalProductTerms ([] : List (PureTerm K X Y Z)) right = [] :=
  rfl

@[simp]
theorem externalProductTerms_cons
    (p : PureTerm K X Y Z) (left : List (PureTerm K X Y Z))
    (right : List (PureTerm K X' Y' Z')) :
    externalProductTerms (p :: left) right =
      right.map p.externalProduct ++ externalProductTerms left right :=
  rfl

/-- The witness Cartesian product has the product of the two list lengths. -/
theorem length_externalProductTerms
    (left : List (PureTerm K X Y Z))
    (right : List (PureTerm K X' Y' Z')) :
    (externalProductTerms left right).length = left.length * right.length := by
  induction left with
  | nil => simp
  | cons p left ih => simp [externalProductTerms, ih, Nat.add_mul]

/-- Realizing all products with one fixed left witness distributes over the right realization. -/
theorem realize_map_externalProduct_left
    (p : PureTerm K X Y Z)
    (right : List (PureTerm K X' Y' Z')) :
    realize (right.map p.externalProduct) =
      TriTensor.externalProduct p.toTensor (realize right) := by
  induction right with
  | nil => simp
  | cons q right ih =>
      simp [ih, TriTensor.externalProduct_add_right]

/-- Realization of the witness Cartesian product is the external product of realizations. -/
theorem realize_externalProductTerms
    (left : List (PureTerm K X Y Z))
    (right : List (PureTerm K X' Y' Z')) :
    realize (externalProductTerms left right) =
      TriTensor.externalProduct (realize left) (realize right) := by
  induction left with
  | nil => simp
  | cons p left ih =>
      simp [externalProductTerms, realize_map_externalProduct_left, ih,
        TriTensor.externalProduct_add_left]

/-- Tensor rank bounds multiply under the external product. -/
theorem HasRankAtMost.externalProduct {r s : ℕ}
    {T : TriTensor K X Y Z} {S : TriTensor K X' Y' Z'}
    (hT : HasRankAtMost (K := K) r T)
    (hS : HasRankAtMost (K := K) s S) :
    HasRankAtMost (K := K) (r * s) (TriTensor.externalProduct T S) := by
  rcases hT with ⟨left, hleft, hrealizeLeft⟩
  rcases hS with ⟨right, hright, hrealizeRight⟩
  refine ⟨externalProductTerms left right, ?_, ?_⟩
  · rw [length_externalProductTerms]
    exact Nat.mul_le_mul hleft hright
  · rw [realize_externalProductTerms, hrealizeLeft, hrealizeRight]

end TriTensor
end AlgebraicComplexity
