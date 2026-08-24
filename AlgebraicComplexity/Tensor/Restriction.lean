import AlgebraicComplexity.Tensor.Basic

set_option linter.style.header false

/-!
# Tensor restrictions

A trilinear tensor `T` restricts to `S` when three coordinatewise linear maps send `T` to `S`.
This is the standard exact restriction preorder used in algebraic complexity.
-/

namespace AlgebraicComplexity
namespace TriTensor

universe uK uX uY uZ uX' uY' uZ' uX'' uY'' uZ''

variable
    {K : Type uK} [CommSemiring K]
    {X : Type uX} {Y : Type uY} {Z : Type uZ}
    {X' : Type uX'} {Y' : Type uY'} {Z' : Type uZ'}
    {X'' : Type uX''} {Y'' : Type uY''} {Z'' : Type uZ''}
    [AddCommMonoid X] [AddCommMonoid Y] [AddCommMonoid Z]
    [AddCommMonoid X'] [AddCommMonoid Y'] [AddCommMonoid Z']
    [AddCommMonoid X''] [AddCommMonoid Y''] [AddCommMonoid Z'']
    [Module K X] [Module K Y] [Module K Z]
    [Module K X'] [Module K Y'] [Module K Z']
    [Module K X''] [Module K Y''] [Module K Z'']

/-- `Restricts T S` means that coordinatewise linear maps send `T` exactly to `S`. -/
def Restricts (T : TriTensor K X Y Z) (S : TriTensor K X' Y' Z') : Prop :=
  ∃ f : X →ₗ[K] X', ∃ g : Y →ₗ[K] Y', ∃ h : Z →ₗ[K] Z', map3 f g h T = S

/-- A short notation for exact tensor restriction. -/
scoped infix:50 " ⪰ₜ " => Restricts

namespace Restricts

/-- Every tensor restricts to itself. -/
theorem refl (T : TriTensor K X Y Z) : Restricts T T := by
  refine ⟨LinearMap.id, LinearMap.id, LinearMap.id, ?_⟩
  simp

/-- Exact tensor restriction is transitive. -/
theorem trans {T : TriTensor K X Y Z} {S : TriTensor K X' Y' Z'}
    {U : TriTensor K X'' Y'' Z''}
    (hTS : Restricts T S) (hSU : Restricts S U) : Restricts T U := by
  rcases hTS with ⟨f₁, g₁, h₁, hTS⟩
  rcases hSU with ⟨f₂, g₂, h₂, hSU⟩
  refine ⟨f₂.comp f₁, g₂.comp g₁, h₂.comp h₁, ?_⟩
  rw [map3_comp]
  simp only [LinearMap.comp_apply, hTS, hSU]

/-- Any coordinatewise image is a restriction. -/
theorem map3 (T : TriTensor K X Y Z)
    (f : X →ₗ[K] X') (g : Y →ₗ[K] Y') (h : Z →ₗ[K] Z') :
    Restricts T (TriTensor.map3 f g h T) :=
  ⟨f, g, h, rfl⟩

/-- Equality implies restriction. -/
theorem of_eq {T S : TriTensor K X Y Z} (h : T = S) : Restricts T S := by
  subst h
  exact refl T

/-- Every tensor restricts to zero. -/
theorem zero (T : TriTensor K X Y Z) :
    Restricts T (0 : TriTensor K X' Y' Z') := by
  refine ⟨0, 0, 0, ?_⟩
  simp [TriTensor.map3]

/-- Restriction is stable under further coordinate maps on the target. -/
theorem post_map {T : TriTensor K X Y Z} {S : TriTensor K X' Y' Z'}
    (hTS : Restricts T S)
    (f : X' →ₗ[K] X'') (g : Y' →ₗ[K] Y'') (h : Z' →ₗ[K] Z'') :
    Restricts T (TriTensor.map3 f g h S) :=
  trans hTS (map3 S f g h)

/-- Mutually restricting tensors are restriction-equivalent. -/
def Equivalent (T : TriTensor K X Y Z) (S : TriTensor K X' Y' Z') : Prop :=
  Restricts T S ∧ Restricts S T

namespace Equivalent

/-- Restriction-equivalence is reflexive. -/
theorem refl (T : TriTensor K X Y Z) : Equivalent T T :=
  ⟨Restricts.refl T, Restricts.refl T⟩

/-- Restriction-equivalence is symmetric. -/
theorem symm {T : TriTensor K X Y Z} {S : TriTensor K X' Y' Z'}
    (h : Equivalent T S) : Equivalent S T :=
  ⟨h.2, h.1⟩

/-- Restriction-equivalence is transitive. -/
theorem trans {T : TriTensor K X Y Z} {S : TriTensor K X' Y' Z'}
    {U : TriTensor K X'' Y'' Z''}
    (hTS : Equivalent T S) (hSU : Equivalent S U) : Equivalent T U :=
  ⟨Restricts.trans hTS.1 hSU.1, Restricts.trans hSU.2 hTS.2⟩

end Equivalent
end Restricts
end TriTensor
end AlgebraicComplexity
