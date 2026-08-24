import Mathlib.Tactic

set_option linter.style.header false

/-!
# Coordinate tensors and monomial degenerations

This file gives the constructive degeneration notion most directly used by laser-method zeroing.
A coordinate tensor is a coefficient function `I → J → L → K`. Integer weights are assigned to
variables in the three coordinates. After rescaling by a common lowest degree, the terms of exactly
that degree survive.

This is intentionally a coordinate-level theory. A later basis bridge will relate these coefficient
functions to abstract elements of `TriTensor`.
-/

namespace AlgebraicComplexity

universe uK uI uJ uL

/-- A finite or infinite coordinate presentation of a trilinear tensor. -/
abbrev CoordinateTensor (K : Type uK) (I : Type uI) (J : Type uJ) (L : Type uL) :=
  I → J → L → K

namespace CoordinateTensor

variable
    {K : Type uK} {I : Type uI} {J : Type uJ} {L : Type uL}
    [Zero K]

/-- Total exponent assigned to a coefficient by three variable-weight functions. -/
def totalWeight (wX : I → ℤ) (wY : J → ℤ) (wZ : L → ℤ)
    (i : I) (j : J) (k : L) : ℤ :=
  wX i + wY j + wZ k

/-- Keep precisely the coefficients whose total weight is the selected leading degree. -/
def leadingPart (wX : I → ℤ) (wY : J → ℤ) (wZ : L → ℤ) (degree : ℤ)
    (T : CoordinateTensor K I J L) : CoordinateTensor K I J L :=
  fun i j k => if totalWeight wX wY wZ i j k = degree then T i j k else 0

@[simp]
theorem leadingPart_apply
    (wX : I → ℤ) (wY : J → ℤ) (wZ : L → ℤ) (degree : ℤ)
    (T : CoordinateTensor K I J L) (i : I) (j : J) (k : L) :
    leadingPart wX wY wZ degree T i j k =
      if totalWeight wX wY wZ i j k = degree then T i j k else 0 :=
  rfl

/-- Every nonzero source coefficient has weight at least the selected leading degree. -/
def AdmissibleWeighting (wX : I → ℤ) (wY : J → ℤ) (wZ : L → ℤ) (degree : ℤ)
    (T : CoordinateTensor K I J L) : Prop :=
  ∀ i j k, T i j k ≠ 0 → degree ≤ totalWeight wX wY wZ i j k

/--
`T` monomially degenerates to `S` if some admissible integer weighting has `S` as its leading part.
-/
def MonomialDegenerates (T S : CoordinateTensor K I J L) : Prop :=
  ∃ wX : I → ℤ, ∃ wY : J → ℤ, ∃ wZ : L → ℤ, ∃ degree : ℤ,
    AdmissibleWeighting wX wY wZ degree T ∧
      S = leadingPart wX wY wZ degree T

/-- Monomial degeneration is reflexive. -/
theorem monomialDegenerates_refl (T : CoordinateTensor K I J L) :
    MonomialDegenerates T T := by
  refine ⟨fun _ => 0, fun _ => 0, fun _ => 0, 0, ?_, ?_⟩
  · intro i j k _
    simp [totalWeight]
  · funext i j k
    simp [leadingPart, totalWeight]

/-- The `0/1` weight that retains a chosen set of coordinate variables. -/
def indicatorWeight (keep : I → Prop) [DecidablePred keep] : I → ℤ :=
  fun i => if keep i then 0 else 1

/-- Zero every coefficient using at least one coordinate outside the selected variable sets. -/
def zeroOutside
    (keepX : I → Prop) (keepY : J → Prop) (keepZ : L → Prop)
    [DecidablePred keepX] [DecidablePred keepY] [DecidablePred keepZ]
    (T : CoordinateTensor K I J L) : CoordinateTensor K I J L :=
  fun i j k => if keepX i ∧ keepY j ∧ keepZ k then T i j k else 0

@[simp]
theorem zeroOutside_apply
    (keepX : I → Prop) (keepY : J → Prop) (keepZ : L → Prop)
    [DecidablePred keepX] [DecidablePred keepY] [DecidablePred keepZ]
    (T : CoordinateTensor K I J L) (i : I) (j : J) (k : L) :
    zeroOutside keepX keepY keepZ T i j k =
      if keepX i ∧ keepY j ∧ keepZ k then T i j k else 0 :=
  rfl

/-- Ordinary variable zeroing is a monomial degeneration. -/
theorem zeroOutside_monomialDegenerates
    (keepX : I → Prop) (keepY : J → Prop) (keepZ : L → Prop)
    [DecidablePred keepX] [DecidablePred keepY] [DecidablePred keepZ]
    (T : CoordinateTensor K I J L) :
    MonomialDegenerates T (zeroOutside keepX keepY keepZ T) := by
  refine ⟨indicatorWeight keepX, indicatorWeight keepY, indicatorWeight keepZ, 0, ?_, ?_⟩
  · intro i j k _
    by_cases hi : keepX i <;> by_cases hj : keepY j <;> by_cases hk : keepZ k <;>
      simp [totalWeight, indicatorWeight, hi, hj, hk]
  · funext i j k
    by_cases hi : keepX i <;> by_cases hj : keepY j <;> by_cases hk : keepZ k <;>
      simp [zeroOutside, leadingPart, totalWeight, indicatorWeight, hi, hj, hk]

/-- A monomial degeneration never invents a nonzero coefficient outside the source support. -/
theorem support_mono_of_monomialDegenerates
    {T S : CoordinateTensor K I J L} (h : MonomialDegenerates T S)
    {i : I} {j : J} {k : L} (hS : S i j k ≠ 0) :
    T i j k ≠ 0 := by
  rcases h with ⟨wX, wY, wZ, degree, _, rfl⟩
  by_contra hT
  simp [leadingPart, hT] at hS

end CoordinateTensor
end AlgebraicComplexity
