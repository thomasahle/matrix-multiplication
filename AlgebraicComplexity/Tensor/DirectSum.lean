import AlgebraicComplexity.Tensor.Rank
import Mathlib.LinearAlgebra.Prod

set_option linter.style.header false

/-!
# Direct sums of trilinear tensors

The direct sum places two tensors in the corresponding product modules. Projection onto either
factor is an exact tensor restriction.
-/

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

/-- Block-diagonal direct sum of two trilinear tensors. -/
def directSum (T : TriTensor K X Y Z) (S : TriTensor K X' Y' Z') :
    TriTensor K (X × X') (Y × Y') (Z × Z') :=
  map3 (LinearMap.inl K X X') (LinearMap.inl K Y Y') (LinearMap.inl K Z Z') T +
    map3 (LinearMap.inr K X X') (LinearMap.inr K Y Y') (LinearMap.inr K Z Z') S

/-- The direct sum restricts to its left summand. -/
theorem directSum_restricts_left (T : TriTensor K X Y Z) (S : TriTensor K X' Y' Z') :
    Restricts (directSum T S) T := by
  refine ⟨LinearMap.fst K X X', LinearMap.fst K Y Y', LinearMap.fst K Z Z', ?_⟩
  simp only [directSum, map_add, map3_map3]
  simp [map3]

/-- The direct sum restricts to its right summand. -/
theorem directSum_restricts_right (T : TriTensor K X Y Z) (S : TriTensor K X' Y' Z') :
    Restricts (directSum T S) S := by
  refine ⟨LinearMap.snd K X X', LinearMap.snd K Y Y', LinearMap.snd K Z Z', ?_⟩
  simp only [directSum, map_add, map3_map3]
  simp [map3]

/-- Concrete rank witnesses combine additively under direct sum. -/
theorem HasRankAtMost.directSum {r s : ℕ}
    {T : TriTensor K X Y Z} {S : TriTensor K X' Y' Z'}
    (hT : HasRankAtMost (K := K) r T) (hS : HasRankAtMost (K := K) s S) :
    HasRankAtMost (K := K) (r + s) (directSum T S) := by
  exact (hT.map (LinearMap.inl K X X') (LinearMap.inl K Y Y') (LinearMap.inl K Z Z')).add
    (hS.map (LinearMap.inr K X X') (LinearMap.inr K Y Y') (LinearMap.inr K Z Z'))

end TriTensor
end AlgebraicComplexity
