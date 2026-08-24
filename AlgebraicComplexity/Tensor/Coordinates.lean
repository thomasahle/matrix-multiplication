import AlgebraicComplexity.Tensor.MonomialDegeneration
import AlgebraicComplexity.Tensor.Restriction
import Mathlib.LinearAlgebra.StdBasis

set_option linter.style.header false

/-!
# From coordinate arrays to abstract trilinear tensors

For finite index types, a coefficient function can be interpreted in the standard bases of the
three function modules. This file also proves that variable zeroing is realized by coordinatewise
linear projections, hence is an exact tensor restriction as well as a monomial degeneration.
-/

namespace AlgebraicComplexity
namespace CoordinateTensor

universe u

variable
    {K I J L : Type u}
    [CommSemiring K]
    [Fintype I] [Fintype J] [Fintype L]
    [DecidableEq I] [DecidableEq J] [DecidableEq L]

/-- A standard basis vector in the coordinate module `I → K`. -/
def basisVector (i : I) : I → K :=
  Pi.single i 1

@[simp]
theorem basisVector_apply (i i' : I) :
    basisVector (K := K) i i' = if i' = i then 1 else 0 := by
  by_cases h : i' = i
  · subst i'
    simp [basisVector]
  · have h' : i ≠ i' := Ne.symm h
    simp [basisVector, h, h']

/-- Interpret a finite coordinate tensor as an abstract trilinear tensor. -/
def toTriTensor (T : CoordinateTensor K I J L) :
    TriTensor K (I → K) (J → K) (L → K) :=
  ∑ i : I, ∑ j : J, ∑ k : L,
    T i j k • TriTensor.pure
      (basisVector (K := K) i)
      (basisVector (K := K) j)
      (basisVector (K := K) k)

/-- Project a coordinate module onto a chosen subset of its standard basis variables. -/
def coordinateFilter (keep : I → Prop) [DecidablePred keep] :
    (I → K) →ₗ[K] (I → K) where
  toFun v i := if keep i then v i else 0
  map_add' x y := by
    funext i
    by_cases hi : keep i <;> simp [hi]
  map_smul' c x := by
    funext i
    by_cases hi : keep i <;> simp [hi]

@[simp]
theorem coordinateFilter_apply
    (keep : I → Prop) [DecidablePred keep] (v : I → K) (i : I) :
    coordinateFilter (K := K) keep v i = if keep i then v i else 0 :=
  rfl

@[simp]
theorem coordinateFilter_basisVector
    (keep : I → Prop) [DecidablePred keep] (i : I) :
    coordinateFilter (K := K) keep (basisVector (K := K) i) =
      if keep i then basisVector (K := K) i else 0 := by
  funext i'
  by_cases hi : keep i <;> by_cases hEq : i' = i
  · subst i'
    simp [coordinateFilter, basisVector, hi]
  · have hNe : i ≠ i' := Ne.symm hEq
    simp [coordinateFilter, basisVector, hi, hEq, hNe]
  · subst i'
    simp [coordinateFilter, basisVector, hi]
  · have hNe : i ≠ i' := Ne.symm hEq
    simp [coordinateFilter, basisVector, hi, hEq, hNe]

/-- Standard-basis interpretation commutes with coordinate variable zeroing. -/
theorem map3_toTriTensor_zeroOutside
    (keepX : I → Prop) (keepY : J → Prop) (keepZ : L → Prop)
    [DecidablePred keepX] [DecidablePred keepY] [DecidablePred keepZ]
    (T : CoordinateTensor K I J L) :
    TriTensor.map3
      (coordinateFilter (K := K) keepX)
      (coordinateFilter (K := K) keepY)
      (coordinateFilter (K := K) keepZ)
      (toTriTensor T) =
    toTriTensor (zeroOutside keepX keepY keepZ T) := by
  classical
  simp only [toTriTensor, map_sum, map_smul, TriTensor.map3_pure]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  by_cases hi : keepX i <;> by_cases hj : keepY j <;> by_cases hk : keepZ k <;>
    simp [zeroOutside, hi, hj, hk]

/-- Variable zeroing is an exact restriction after standard-basis realization. -/
theorem toTriTensor_restricts_zeroOutside
    (keepX : I → Prop) (keepY : J → Prop) (keepZ : L → Prop)
    [DecidablePred keepX] [DecidablePred keepY] [DecidablePred keepZ]
    (T : CoordinateTensor K I J L) :
    TriTensor.Restricts
      (toTriTensor T)
      (toTriTensor (zeroOutside keepX keepY keepZ T)) := by
  exact ⟨coordinateFilter (K := K) keepX,
    coordinateFilter (K := K) keepY,
    coordinateFilter (K := K) keepZ,
    map3_toTriTensor_zeroOutside keepX keepY keepZ T⟩

end CoordinateTensor
end AlgebraicComplexity
