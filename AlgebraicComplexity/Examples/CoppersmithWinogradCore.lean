/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Tensor.Basic
import Mathlib.LinearAlgebra.Pi

/-!
# The Coppersmith--Winograd tensor: lightweight definitions

This file defines the coordinate space and the tensor `CW_q`.  Border-rank curves, monomial
degenerations, and matrix-multiplication projections live in the public re-exporting module
`CoppersmithWinograd`; elementary support and partition clients should import this core.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor

universe u

/-- The zero, middle, and final coordinate blocks of the full CW tensor. -/
inductive CWIndex (q : ℕ)
  | zero
  | middle (i : Fin q)
  | last
  deriving DecidableEq

private def cwIndexEquiv (q : ℕ) : Option (Fin q ⊕ Unit) ≃ CWIndex q where
  toFun
    | none => .zero
    | some (.inl i) => .middle i
    | some (.inr _) => .last
  invFun
    | .zero => none
    | .middle i => some (.inl i)
    | .last => some (.inr ())
  left_inv x := by
    rcases x with _ | (i | u)
    · rfl
    · rfl
    · cases u
      rfl
  right_inv x := by cases x <;> rfl

instance (q : ℕ) : Fintype (CWIndex q) :=
  Fintype.ofEquiv (Option (Fin q ⊕ Unit)) (cwIndexEquiv q)

/-- All three legs of `CW_q` use the same `q + 2` coordinate space. -/
abbrev CWSpace (K : Type u) (q : ℕ) (_ : Leg) := CWIndex q → K

/-- All three legs of `CW_q` carry the same finite index type `CWIndex q`; this is the index family
in the form expected by `standardCoordinateEquiv`. -/
abbrev CWCoordIndex (q : ℕ) : Leg → Type := fun _ ↦ CWIndex q

/-- An index triple of `CW_q` equals `ofLegs x y z` exactly when its three components are `x`, `y`
and `z`. -/
theorem cwIndex_eq_ofLegs_iff (q : ℕ) (a : ∀ c, CWCoordIndex q c) (x y z : CWIndex q) :
    a = ofLegs x y z ↔ a .X = x ∧ a .Y = y ∧ a .Z = z := by
  constructor
  · rintro rfl
    exact ⟨rfl, rfl, rfl⟩
  · rintro ⟨h1, h2, h3⟩
    funext c
    cases c
    · exact h1
    · exact h2
    · exact h3

section Semiring

variable (K : Type u) [CommSemiring K]
variable (q : ℕ)

/-- Standard coordinate vector in the CW ambient space. -/
def cwBasis (a : CWIndex q) : CWIndex q → K :=
  Pi.single a 1

/-- Standard vector in the zero block. -/
abbrev cwZeroVector : CWIndex q → K := cwBasis K q .zero

/-- Standard vector in the final block. -/
abbrev cwLastVector : CWIndex q → K := cwBasis K q .last

/-- Standard vector `i` in the middle block. -/
abbrev cwMiddleVector (i : Fin q) : CWIndex q → K := cwBasis K q (.middle i)

private abbrev e₀ : CWIndex q → K := cwZeroVector K q
private abbrev e₂ : CWIndex q → K := cwLastVector K q
private abbrev e₁ (i : Fin q) : CWIndex q → K := cwMiddleVector K q i

/-- The three symmetric middle summands associated to index `i`. -/
noncomputable def cwMiddle (i : Fin q) : Tensor3 K (CWSpace K q) :=
  pure (K := K) (ofLegs (e₀ K q) (e₁ K q i) (e₁ K q i)) +
  pure (K := K) (ofLegs (e₁ K q i) (e₀ K q) (e₁ K q i)) +
  pure (K := K) (ofLegs (e₁ K q i) (e₁ K q i) (e₀ K q))

/-- The three corner summands involving the final coordinate. -/
noncomputable def cwCorners : Tensor3 K (CWSpace K q) :=
  pure (K := K) (ofLegs (e₂ K q) (e₀ K q) (e₀ K q)) +
  pure (K := K) (ofLegs (e₀ K q) (e₂ K q) (e₀ K q)) +
  pure (K := K) (ofLegs (e₀ K q) (e₀ K q) (e₂ K q))

/-- The full Coppersmith--Winograd tensor `CW_q`. -/
noncomputable def coppersmithWinograd : Tensor3 K (CWSpace K q) :=
  (∑ i : Fin q, cwMiddle K q i) + cwCorners K q

/-- The three middle summands of `CW_q`, restated in the public standard-basis names. -/
theorem cwMiddle_eq_pure (i : Fin q) :
    cwMiddle K q i =
      pure (K := K) (ofLegs (V := CWSpace K q)
          (cwBasis K q .zero) (cwBasis K q (.middle i)) (cwBasis K q (.middle i))) +
        pure (K := K) (ofLegs (V := CWSpace K q)
          (cwBasis K q (.middle i)) (cwBasis K q .zero) (cwBasis K q (.middle i))) +
        pure (K := K) (ofLegs (V := CWSpace K q)
          (cwBasis K q (.middle i)) (cwBasis K q (.middle i)) (cwBasis K q .zero)) :=
  rfl

/-- The three corner summands of `CW_q`, restated in the public standard-basis names. -/
theorem cwCorners_eq_pure :
    cwCorners K q =
      pure (K := K) (ofLegs (V := CWSpace K q)
          (cwBasis K q .last) (cwBasis K q .zero) (cwBasis K q .zero)) +
        pure (K := K) (ofLegs (V := CWSpace K q)
          (cwBasis K q .zero) (cwBasis K q .last) (cwBasis K q .zero)) +
        pure (K := K) (ofLegs (V := CWSpace K q)
          (cwBasis K q .zero) (cwBasis K q .zero) (cwBasis K q .last)) :=
  rfl

end Semiring

end AlgebraicComplexity.Examples
