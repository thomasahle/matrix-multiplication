/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Tensor.Degeneration
import AlgebraicComplexity.Tensor.Coordinates

/-!
# Monomial tensor degeneration

Natural-number weights on basis coordinates define diagonal polynomial map families. This file
turns those compact weight certificates into the basis-free polynomial degeneration semantics of
`Tensor.Degeneration`, proves reflexivity using the zero weight, and provides exact leading-term
calculations for finite coordinate expansions.
-/

namespace AlgebraicComplexity.Tensor

universe u v

variable {K : Type u} [CommSemiring K]

namespace Monomial

/-- The degree-`d` coefficient of the diagonal family associated to a coordinate weight. -/
def weightCoefficient {κ : Type v} (w : κ → ℕ) (d : ℕ) :
    (κ → K) →ₗ[K] (κ → K) :=
  LinearMap.pi fun a ↦ if w a = d then LinearMap.proj a else 0

@[simp] theorem weightCoefficient_apply {κ : Type v} (w : κ → ℕ)
    (d : ℕ) (x : κ → K) (a : κ) :
    weightCoefficient (K := K) w d x a = if w a = d then x a else 0 := by
  by_cases h : w a = d <;> simp [weightCoefficient, h]

/-- The finitely supported polynomial diagonal map `e_a ↦ ε^(w a)e_a`. -/
noncomputable def weightFamily {κ : Type v} [Fintype κ]
    (w : κ → ℕ) : PolynomialLinearMap K (κ → K) (κ → K) := by
  classical
  refine Finsupp.onFinset (Finset.univ.image w)
    (weightCoefficient (K := K) w) ?_
  intro d hd
  by_contra hmem
  apply hd
  ext x a
  have hwa : w a ≠ d := by
    intro h
    apply hmem
    rw [← h]
    exact Finset.mem_image_of_mem w (Finset.mem_univ a)
  simp [weightCoefficient_apply, hwa]

@[simp] theorem weightFamily_coeff {κ : Type v} [Fintype κ]
    (w : κ → ℕ) (d : ℕ) :
    weightFamily (K := K) w d = weightCoefficient (K := K) w d := by
  classical
  simp [weightFamily]

@[simp] theorem weightCoefficient_single {κ : Type v} [Fintype κ]
    [DecidableEq κ] (w : κ → ℕ) (d : ℕ) (a : κ) :
    weightCoefficient (K := K) w d (Pi.single a 1) =
      if w a = d then Pi.single a 1 else 0 := by
  ext b
  by_cases h : w a = d
  · subst d
    by_cases hb : w b = w a
    · simp [weightCoefficient_apply, hb]
    · have hba : b ≠ a := by
        intro hEq
        subst b
        exact hb rfl
      simp [weightCoefficient_apply, hb, hba]
  · by_cases hb : w b = d
    · have hba : b ≠ a := by
        intro hEq
        subst b
        exact h hb
      simp [weightCoefficient_apply, h, hb, hba]
    · simp [weightCoefficient_apply, h, hb]

@[simp] theorem applyVector_weightFamily_single {κ : Type v} [Fintype κ]
    [DecidableEq κ] (w : κ → ℕ) (a : κ) :
    PolynomialLinearMap.applyVector (weightFamily (K := K) w) (Pi.single a 1) =
      PolynomialVector.monomial (w a) (Pi.single a 1) := by
  ext d
  rw [PolynomialLinearMap.applyVector_coeff, weightFamily_coeff,
    weightCoefficient_single]
  by_cases h : w a = d
  · subst d
    simp
  · simp [h, Ne.symm h]

end Monomial

variable {κ : Leg → Type v} [∀ c, Fintype (κ c)]

/-- Sum of the three coordinate weights on a pure basis tensor. -/
def monomialTotalWeight (w : ∀ c, κ c → ℕ) (p : ∀ c, κ c) : ℕ :=
  w .X (p .X) + w .Y (p .Y) + w .Z (p .Z)

/-- The polynomial tensor path induced by diagonal monomial weights. -/
noncomputable def monomialTransform (w : ∀ c, κ c → ℕ)
    (T : Tensor3 K (CoordinateSpace K κ)) :
    PolynomialTensor K (CoordinateSpace K κ) :=
  polynomialTransform (fun c ↦ Monomial.weightFamily (K := K) (w c)) T

@[simp] theorem monomialTransform_zero (w : ∀ c, κ c → ℕ) :
    monomialTransform (K := K) w (0 : Tensor3 K (CoordinateSpace K κ)) = 0 := by
  exact polynomialTransform_zero _

theorem monomialTransform_add (w : ∀ c, κ c → ℕ)
    (T S : Tensor3 K (CoordinateSpace K κ)) :
    monomialTransform (K := K) w (T + S) =
      monomialTransform (K := K) w T + monomialTransform (K := K) w S := by
  exact polynomialTransform_add _ _ _

theorem monomialTransform_smul (w : ∀ c, κ c → ℕ)
    (r : K) (T : Tensor3 K (CoordinateSpace K κ)) :
    monomialTransform (K := K) w (r • T) = r • monomialTransform (K := K) w T := by
  exact polynomialTransform_smul _ _ _

theorem monomialTransform_fintype_sum {I : Type*} [Fintype I]
    (w : ∀ c, κ c → ℕ) (T : I → Tensor3 K (CoordinateSpace K κ)) :
    monomialTransform (K := K) w (∑ i, T i) =
      ∑ i, monomialTransform (K := K) w (T i) := by
  exact polynomialTransform_fintype_sum _ _

/-- A monomial certificate is a polynomial degeneration via diagonal coordinate weights. -/
def MonomialDegenerates (T S : Tensor3 K (CoordinateSpace K κ)) : Prop :=
  ∃ (w : ∀ c, κ c → ℕ) (d : ℕ),
    HasLeadingTerm (monomialTransform w T) d S

/-- The all-zero coordinate weight induces the constant identity map family. -/
private theorem weightFamily_zero (c : Leg) :
    Monomial.weightFamily (K := K) (fun _ : κ c ↦ 0) =
      PolynomialLinearMap.constant (LinearMap.id (R := K) (M := CoordinateSpace K κ c)) := by
  classical
  refine Finsupp.ext fun d ↦ LinearMap.ext fun x ↦ funext fun a ↦ ?_
  rw [Monomial.weightFamily_coeff, Monomial.weightCoefficient_apply]
  by_cases hd : d = 0
  · subst hd
    simp [PolynomialLinearMap.constant, PolynomialLinearMap.monomial,
      PolynomialVector.monomial]
  · simp [PolynomialLinearMap.constant, PolynomialLinearMap.monomial,
      PolynomialVector.monomial, hd, Ne.symm hd]

/-- **Monomial degeneration is reflexive.**  Every coordinate tensor monomially degenerates to
itself via the all-zero weight and threshold `0`.

Proof sketch: with all weights zero the diagonal family is the constant identity, so the induced
polynomial path is constant at `T` and has leading term `T` in degree zero. -/
theorem MonomialDegenerates.refl (T : Tensor3 K (CoordinateSpace K κ)) :
    MonomialDegenerates T T := by
  refine ⟨fun _ _ ↦ 0, 0, ?_⟩
  have hfam : (fun c ↦ Monomial.weightFamily (K := K) (fun _ : κ c ↦ 0)) =
      fun c ↦ PolynomialLinearMap.constant
        (LinearMap.id (R := K) (M := CoordinateSpace K κ c)) := by
    funext c
    exact weightFamily_zero c
  show HasLeadingTerm (monomialTransform (fun _ _ ↦ 0) T) 0 T
  unfold monomialTransform
  rw [hfam, polynomialTransform_constant]
  have hmap : map (fun c ↦ LinearMap.id (R := K) (M := CoordinateSpace K κ c)) T = T := by
    simp
  rw [hmap]
  exact HasLeadingTerm.monomial 0 T

/-- Monomial degeneration is a special case of basis-free polynomial degeneration. -/
theorem MonomialDegenerates.toPolynomial {T S : Tensor3 K (CoordinateSpace K κ)}
    (h : MonomialDegenerates T S) : PolynomialDegenerates T S := by
  rcases h with ⟨w, d, hlead⟩
  exact ⟨fun c ↦ Monomial.weightFamily (K := K) (w c), d, hlead⟩

/-- Constructive border rank is monotone under monomial degeneration. -/
theorem BorderRankLE.of_monomialDegenerates
    {r : ℕ} {T S : Tensor3 K (CoordinateSpace K κ)}
    (hT : BorderRankLE r T) (hTS : MonomialDegenerates T S) : BorderRankLE r S :=
  hT.of_polynomialDegenerates hTS.toPolynomial

/-- A weighted pure basis tensor becomes a tensor monomial of the total weight. -/
theorem monomialTransform_basis [∀ c, DecidableEq (κ c)]
    (w : ∀ c, κ c → ℕ) (p : ∀ c, κ c) :
    monomialTransform (K := K) w
        (pure (K := K) (fun c ↦ Pi.single (p c) 1)) =
      PolynomialVector.monomial (monomialTotalWeight w p)
        (pure (K := K) (fun c ↦ Pi.single (p c) 1)) := by
  rw [monomialTransform, polynomialTransform_pure]
  change polynomialPure (K := K)
      (fun c ↦ PolynomialLinearMap.applyVector
        (Monomial.weightFamily (K := K) (w c)) (Pi.single (p c) 1)) = _
  simp only [Monomial.applyVector_weightFamily_single]
  have hpoly :
      (fun c ↦ PolynomialVector.monomial (w c (p c))
        (Pi.single (p c) (1 : K) : κ c → K)) =
        ofLegs (V := fun c ↦ PolynomialVector (κ c → K))
          (PolynomialVector.monomial (w .X (p .X))
            (Pi.single (p .X) (1 : K) : κ .X → K))
          (PolynomialVector.monomial (w .Y (p .Y))
            (Pi.single (p .Y) (1 : K) : κ .Y → K))
          (PolynomialVector.monomial (w .Z (p .Z))
            (Pi.single (p .Z) (1 : K) : κ .Z → K)) :=
    (ofLegs_eta _).symm
  have hbasis :
      (fun c ↦ (Pi.single (p c) (1 : K) : κ c → K)) =
        ofLegs (V := CoordinateSpace K κ)
          (Pi.single (p .X) 1) (Pi.single (p .Y) 1) (Pi.single (p .Z) 1) :=
    (ofLegs_eta _).symm
  rw [hpoly, hbasis]
  simp [monomialTotalWeight, Nat.add_assoc]

/-- Three-coordinate form of `monomialTransform_basis`, convenient for displayed tensors. -/
theorem monomialTransform_basis_ofLegs [∀ c, DecidableEq (κ c)]
    (w : ∀ c, κ c → ℕ) (x : κ .X) (y : κ .Y) (z : κ .Z) :
    monomialTransform (K := K) w
        (pure (K := K) (ofLegs (Pi.single x 1) (Pi.single y 1) (Pi.single z 1))) =
      PolynomialVector.monomial (w .X x + w .Y y + w .Z z)
        (pure (K := K) (ofLegs (Pi.single x 1) (Pi.single y 1) (Pi.single z 1))) := by
  have hbasis :
      (fun c ↦ (Pi.single (ofLegs x y z c) (1 : K) : κ c → K)) =
        ofLegs (Pi.single x 1) (Pi.single y 1) (Pi.single z 1) := by
    funext c
    cases c <;> rfl
  have h := monomialTransform_basis (K := K) w (ofLegs x y z)
  rw [hbasis] at h
  simpa [monomialTotalWeight] using h

/-- Scalar multiples of coordinate basis tensors retain their coefficient under a monomial
weighting. -/
theorem monomialTransform_smul_basis [∀ c, DecidableEq (κ c)]
    (w : ∀ c, κ c → ℕ) (a : K) (p : ∀ c, κ c) :
    monomialTransform (K := K) w
        (a • pure (K := K) (fun c ↦ Pi.single (p c) 1)) =
      PolynomialVector.monomial (monomialTotalWeight w p)
        (a • pure (K := K) (fun c ↦ Pi.single (p c) 1)) := by
  rw [monomialTransform, polynomialTransform_smul, ← monomialTransform,
    monomialTransform_basis, ← PolynomialVector.monomial_smul]

/-- A monomial transform acts termwise on an explicit finite coordinate expansion. -/
theorem monomialTransform_fintype_sum_basis
    {α : Type*} [Fintype α] [∀ c, DecidableEq (κ c)]
    (w : ∀ c, κ c → ℕ) (a : α → K) (p : α → ∀ c, κ c) :
    monomialTransform (K := K) w
        (∑ i, a i • pure (K := K) (fun c ↦ Pi.single (p i c) 1)) =
      ∑ i, PolynomialVector.monomial (monomialTotalWeight w (p i))
        (a i • pure (K := K) (fun c ↦ Pi.single (p i c) 1)) := by
  rw [monomialTransform, polynomialTransform_fintype_sum]
  change (∑ i, monomialTransform (K := K) w
    (a i • pure (K := K) (fun c ↦ Pi.single (p i c) 1))) = _
  simp_rw [monomialTransform_smul_basis]

/-- If all displayed coordinate terms have weight at least `d`, the degree-`d` leading tensor is
exactly the sum of the terms whose total weight is `d`.  This is the reusable semantic theorem
behind support zeroing and monomial laser certificates. -/
theorem monomialTransform_fintype_sum_basis_leading
    {α : Type*} [Fintype α] [∀ c, DecidableEq (κ c)]
    (w : ∀ c, κ c → ℕ) (a : α → K) (p : α → ∀ c, κ c)
    (d : ℕ) (hmin : ∀ i, d ≤ monomialTotalWeight w (p i)) :
    HasLeadingTerm
      (monomialTransform (K := K) w
        (∑ i, a i • pure (K := K) (fun c ↦ Pi.single (p i c) 1)))
      d
      (∑ i, if monomialTotalWeight w (p i) = d then
        a i • pure (K := K) (fun c ↦ Pi.single (p i c) 1) else 0) := by
  classical
  rw [monomialTransform_fintype_sum_basis]
  constructor
  · rw [Finsupp.finsetSum_apply]
    apply Finset.sum_congr rfl
    intro i hi
    by_cases hweight : monomialTotalWeight w (p i) = d
    · subst d
      simp
    · have hne : d ≠ monomialTotalWeight w (p i) := Ne.symm hweight
      simp [PolynomialVector.monomial_coeff_of_ne hne, hweight]
  · intro e he
    rw [Finsupp.finsetSum_apply]
    apply Finset.sum_eq_zero
    intro i hi
    have hne : e ≠ monomialTotalWeight w (p i) :=
      Nat.ne_of_lt (he.trans_le (hmin i))
    exact PolynomialVector.monomial_coeff_of_ne hne _

/-- **Support form of the minimum-weight leading term.**  Only the *displayed terms that actually
occur* need to have weight at least `d`: a term with vanishing coefficient contributes nothing to
any coefficient of the polynomial path, so its weight is irrelevant.

This is the form consumed by support-combinatorial clients, where the weights are designed to be
minimal on the support of a coefficient table and nothing is known about them off the support; see
`Tensor/MonomialIndependence.lean`.  `monomialTransform_fintype_sum_basis_leading` is the special
case `hmin i (fun _ ↦ trivial)`.

Proof sketch: identical to the unconditional version except in the vanishing of the coefficients
below degree `d`, where a summand with `a i = 0` is the zero polynomial vector and a summand with
`a i ≠ 0` has weight at least `d` by hypothesis. -/
theorem monomialTransform_fintype_sum_basis_leading_of_support
    {α : Type*} [Fintype α] [∀ c, DecidableEq (κ c)]
    (w : ∀ c, κ c → ℕ) (a : α → K) (p : α → ∀ c, κ c)
    (d : ℕ) (hmin : ∀ i, a i ≠ 0 → d ≤ monomialTotalWeight w (p i)) :
    HasLeadingTerm
      (monomialTransform (K := K) w
        (∑ i, a i • pure (K := K) (fun c ↦ Pi.single (p i c) 1)))
      d
      (∑ i, if monomialTotalWeight w (p i) = d then
        a i • pure (K := K) (fun c ↦ Pi.single (p i c) 1) else 0) := by
  classical
  rw [monomialTransform_fintype_sum_basis]
  constructor
  · rw [Finsupp.finsetSum_apply]
    apply Finset.sum_congr rfl
    intro i hi
    by_cases hweight : monomialTotalWeight w (p i) = d
    · subst d
      simp
    · have hne : d ≠ monomialTotalWeight w (p i) := Ne.symm hweight
      simp [PolynomialVector.monomial_coeff_of_ne hne, hweight]
  · intro e he
    rw [Finsupp.finsetSum_apply]
    apply Finset.sum_eq_zero
    intro i hi
    by_cases ha : a i = 0
    · simp [ha]
    · have hne : e ≠ monomialTotalWeight w (p i) :=
        Nat.ne_of_lt (he.trans_le (hmin i ha))
      exact PolynomialVector.monomial_coeff_of_ne hne _

/-- Package the preceding minimum-weight calculation as a monomial degeneration certificate. -/
theorem monomialDegenerates_fintype_sum_basis
    {α : Type*} [Fintype α] [∀ c, DecidableEq (κ c)]
    (w : ∀ c, κ c → ℕ) (a : α → K) (p : α → ∀ c, κ c)
    (d : ℕ) (hmin : ∀ i, d ≤ monomialTotalWeight w (p i)) :
    MonomialDegenerates
      (∑ i, a i • pure (K := K) (fun c ↦ Pi.single (p i c) 1))
      (∑ i, if monomialTotalWeight w (p i) = d then
        a i • pure (K := K) (fun c ↦ Pi.single (p i c) 1) else 0) := by
  exact ⟨w, d, monomialTransform_fintype_sum_basis_leading w a p d hmin⟩

/-- **Support form of the minimum-weight monomial degeneration certificate.**  A coefficient table
whose *occurring* terms all have weight at least `d` monomially degenerates to the part of it
supported on the terms of weight exactly `d`. -/
theorem monomialDegenerates_fintype_sum_basis_of_support
    {α : Type*} [Fintype α] [∀ c, DecidableEq (κ c)]
    (w : ∀ c, κ c → ℕ) (a : α → K) (p : α → ∀ c, κ c)
    (d : ℕ) (hmin : ∀ i, a i ≠ 0 → d ≤ monomialTotalWeight w (p i)) :
    MonomialDegenerates
      (∑ i, a i • pure (K := K) (fun c ↦ Pi.single (p i c) 1))
      (∑ i, if monomialTotalWeight w (p i) = d then
        a i • pure (K := K) (fun c ↦ Pi.single (p i c) 1) else 0) :=
  ⟨w, d, monomialTransform_fintype_sum_basis_leading_of_support w a p d hmin⟩

end AlgebraicComplexity.Tensor
