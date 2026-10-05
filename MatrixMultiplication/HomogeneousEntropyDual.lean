import MatrixMultiplication.EntropyDual
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Homogeneous maximum-entropy duality

Recursive laser arguments use finite nonnegative mass vectors whose total mass need not be one.
Their natural entropy is the homogeneous extension

`Hhom(p) = H(p) - negMulLog (sum p)`,

which is exactly `(sum p) * H(p / sum p)`.  Consequently the ordinary exponential-family
maximum-entropy dual scales by the same total mass.  This module proves that reduction once, over
an arbitrary finite support, so recursive certificate checkers do not need to assume that a
subprobability row is normalized.
-/

open scoped BigOperators

namespace MatrixMultiplication.HomogeneousEntropyDual

open MatrixMultiplication.EntropyDual

noncomputable section

variable {A X Y Z : Type*}

/-- Total mass of a finite real-valued row. -/
def totalMass [Fintype A] (p : A → ℝ) : ℝ :=
  ∑ a, p a

/-- Normalize a positive-mass row. -/
def normalize [Fintype A] (p : A → ℝ) (a : A) : ℝ :=
  p a / totalMass p

/-- Homogeneous Shannon entropy in nats. -/
def homogeneousEntropy [Fintype A] (p : A → ℝ) : ℝ :=
  entropy p - Real.negMulLog (totalMass p)

/-- Homogeneous Shannon entropy in bits. -/
def homogeneousEntropyBits [Fintype A] (p : A → ℝ) : ℝ :=
  homogeneousEntropy p / Real.log 2

/-- Homogeneous coordinate dual in bits.  The partition term is multiplied by the total mass,
while the coordinate-potential expectation is taken against the original mass row. -/
def homogeneousCoordinateDualBits
    [Fintype A] [Fintype X] [Fintype Y] [Fintype Z]
    [DecidableEq X] [DecidableEq Y] [DecidableEq Z]
    (coordX : A → X) (coordY : A → Y) (coordZ : A → Z)
    (p : A → ℝ) (uX : X → ℝ) (uY : Y → ℝ) (uZ : Z → ℝ) : ℝ :=
  totalMass p *
      (Real.log (partitionTwo (coordinateScore coordX coordY coordZ uX uY uZ)) /
        Real.log 2) -
    ((∑ x, uX x * marginal coordX p x) +
     (∑ y, uY y * marginal coordY p y) +
     (∑ z, uZ z * marginal coordZ p z))

theorem sum_normalize [Fintype A] (p : A → ℝ) (hmass : 0 < totalMass p) :
    ∑ a, normalize p a = 1 := by
  simp only [normalize, div_eq_mul_inv]
  rw [← Finset.sum_mul]
  change totalMass p * (totalMass p)⁻¹ = 1
  exact mul_inv_cancel₀ hmass.ne'

theorem normalize_nonneg [Fintype A] (p : A → ℝ)
    (hp : ∀ a, 0 ≤ p a) (hmass : 0 < totalMass p) (a : A) :
    0 ≤ normalize p a := by
  exact div_nonneg (hp a) hmass.le

theorem expectation_normalize [Fintype A] (p : A → ℝ) (f : A → ℝ)
    (_hmass : 0 < totalMass p) :
    ∑ a, normalize p a * f a = (∑ a, p a * f a) / totalMass p := by
  simp only [normalize, div_eq_mul_inv]
  calc
    ∑ a, p a * (totalMass p)⁻¹ * f a =
        ∑ a, (p a * f a) * (totalMass p)⁻¹ := by
      apply Finset.sum_congr rfl
      intro a _
      ring
    _ = (∑ a, p a * f a) * (totalMass p)⁻¹ := by
      rw [Finset.sum_mul]

/-- Homogeneous entropy is total mass times the entropy of the normalized row. -/
theorem homogeneousEntropy_eq_mass_mul_entropy_normalize
    [Fintype A] (p : A → ℝ) (hmass : 0 < totalMass p) :
    homogeneousEntropy p = totalMass p * entropy (normalize p) := by
  have hpoint (a : A) :
      Real.negMulLog (p a) =
        normalize p a * Real.negMulLog (totalMass p) +
          totalMass p * Real.negMulLog (normalize p a) := by
    have hp_repr : totalMass p * normalize p a = p a := by
      unfold normalize
      exact mul_div_cancel₀ (p a) hmass.ne'
    rw [← hp_repr, Real.negMulLog_mul]
  unfold homogeneousEntropy entropy
  simp_rw [hpoint]
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, sum_normalize p hmass,
    one_mul, ← Finset.mul_sum]
  ring

theorem homogeneousEntropyBits_eq_mass_mul_entropyBits_normalize
    [Fintype A] (p : A → ℝ) (hmass : 0 < totalMass p) :
    homogeneousEntropyBits p = totalMass p * entropyBits (normalize p) := by
  rw [homogeneousEntropyBits, homogeneousEntropy_eq_mass_mul_entropy_normalize p hmass]
  unfold entropyBits
  ring

/-- The homogeneous coordinate dual is the total mass times the ordinary dual of the normalized
row. -/
theorem homogeneousCoordinateDualBits_eq_mass_mul_coordinateDualBits_normalize
    [Fintype A] [Fintype X] [Fintype Y] [Fintype Z]
    [DecidableEq X] [DecidableEq Y] [DecidableEq Z]
    (coordX : A → X) (coordY : A → Y) (coordZ : A → Z)
    (p : A → ℝ) (uX : X → ℝ) (uY : Y → ℝ) (uZ : Z → ℝ)
    (hmass : 0 < totalMass p) :
    homogeneousCoordinateDualBits coordX coordY coordZ p uX uY uZ =
      totalMass p *
        coordinateDualBits coordX coordY coordZ (normalize p) uX uY uZ := by
  rw [coordinateDualBits, ← coordinateScore_expectation]
  rw [expectation_normalize p
    (coordinateScore coordX coordY coordZ uX uY uZ) hmass]
  unfold homogeneousCoordinateDualBits
  rw [← coordinateScore_expectation coordX coordY coordZ p uX uY uZ]
  field_simp [hmass.ne']

/-- Exponential-family duality for arbitrary positive finite mass rows. -/
theorem homogeneousEntropyBits_le_coordinateDual
    [Fintype A] [Nonempty A] [Fintype X] [Fintype Y] [Fintype Z]
    [DecidableEq X] [DecidableEq Y] [DecidableEq Z]
    (coordX : A → X) (coordY : A → Y) (coordZ : A → Z)
    (p : A → ℝ) (uX : X → ℝ) (uY : Y → ℝ) (uZ : Z → ℝ)
    (hp : ∀ a, 0 ≤ p a) (hmass : 0 < totalMass p) :
    homogeneousEntropyBits p ≤
      homogeneousCoordinateDualBits coordX coordY coordZ p uX uY uZ := by
  rw [homogeneousEntropyBits_eq_mass_mul_entropyBits_normalize p hmass,
    homogeneousCoordinateDualBits_eq_mass_mul_coordinateDualBits_normalize
      coordX coordY coordZ p uX uY uZ hmass]
  exact mul_le_mul_of_nonneg_left
    (entropyBits_le_coordinateDual coordX coordY coordZ (normalize p) uX uY uZ
      (normalize_nonneg p hp hmass) (sum_normalize p hmass)) hmass.le

/-- Two finite mass rows have the same total mass and all three coordinate marginals. -/
def SameMassAndMarginals
    [Fintype A] [Fintype X] [Fintype Y] [Fintype Z]
    [DecidableEq X] [DecidableEq Y] [DecidableEq Z]
    (coordX : A → X) (coordY : A → Y) (coordZ : A → Z)
    (p q : A → ℝ) : Prop :=
  totalMass p = totalMass q ∧ SameMarginals coordX coordY coordZ p q

theorem homogeneousCoordinateDualBits_eq_of_sameMassAndMarginals
    [Fintype A] [Fintype X] [Fintype Y] [Fintype Z]
    [DecidableEq X] [DecidableEq Y] [DecidableEq Z]
    (coordX : A → X) (coordY : A → Y) (coordZ : A → Z)
    (p q : A → ℝ) (uX : X → ℝ) (uY : Y → ℝ) (uZ : Z → ℝ)
    (h : SameMassAndMarginals coordX coordY coordZ p q) :
    homogeneousCoordinateDualBits coordX coordY coordZ p uX uY uZ =
      homogeneousCoordinateDualBits coordX coordY coordZ q uX uY uZ := by
  rcases h with ⟨hmass, hX, hY, hZ⟩
  unfold homogeneousCoordinateDualBits
  rw [hmass, hX, hY, hZ]

/-- Supremal homogeneous entropy among nonnegative rows with fixed mass and three marginals. -/
def maximumHomogeneousEntropyBits
    [Fintype A] [Fintype X] [Fintype Y] [Fintype Z]
    [DecidableEq X] [DecidableEq Y] [DecidableEq Z]
    (coordX : A → X) (coordY : A → Y) (coordZ : A → Z)
    (reference : A → ℝ) : ℝ :=
  sSup {h : ℝ | ∃ p : A → ℝ,
    (∀ a, 0 ≤ p a) ∧
      SameMassAndMarginals coordX coordY coordZ p reference ∧
      h = homogeneousEntropyBits p}

theorem eq_zero_of_nonneg_of_totalMass_eq_zero
    [Fintype A] (p : A → ℝ) (hp : ∀ a, 0 ≤ p a)
    (hmass : totalMass p = 0) : p = 0 := by
  apply (Fintype.sum_eq_zero_iff_of_nonneg hp).mp
  simpa [totalMass] using hmass

/-- Homogeneous analogue of the finite maximum-entropy dual theorem. -/
theorem maximumHomogeneousEntropyBits_le_coordinateDual
    [Fintype A] [Nonempty A] [Fintype X] [Fintype Y] [Fintype Z]
    [DecidableEq X] [DecidableEq Y] [DecidableEq Z]
    (coordX : A → X) (coordY : A → Y) (coordZ : A → Z)
    (reference : A → ℝ) (uX : X → ℝ) (uY : Y → ℝ) (uZ : Z → ℝ)
    (href : ∀ a, 0 ≤ reference a) (hmass : 0 < totalMass reference) :
    maximumHomogeneousEntropyBits coordX coordY coordZ reference ≤
      homogeneousCoordinateDualBits coordX coordY coordZ reference uX uY uZ := by
  apply csSup_le
  · refine ⟨homogeneousEntropyBits reference, reference, href, ?_, rfl⟩
    exact ⟨rfl, rfl, rfl, rfl⟩
  · intro h hh
    rcases hh with ⟨p, hp, hsame, rfl⟩
    have hpmass : 0 < totalMass p := by
      rw [hsame.1]
      exact hmass
    exact (homogeneousEntropyBits_le_coordinateDual coordX coordY coordZ p uX uY uZ
      hp hpmass).trans_eq
        (homogeneousCoordinateDualBits_eq_of_sameMassAndMarginals
          coordX coordY coordZ p reference uX uY uZ hsame)

/-- Zero-safe homogeneous maximum-entropy duality.  Nonnegativity of the reference row alone is
enough; a zero-mass row and every feasible competitor are identically zero. -/
theorem maximumHomogeneousEntropyBits_le_coordinateDual_of_nonnegative
    [Fintype A] [Nonempty A] [Fintype X] [Fintype Y] [Fintype Z]
    [DecidableEq X] [DecidableEq Y] [DecidableEq Z]
    (coordX : A → X) (coordY : A → Y) (coordZ : A → Z)
    (reference : A → ℝ) (uX : X → ℝ) (uY : Y → ℝ) (uZ : Z → ℝ)
    (href : ∀ a, 0 ≤ reference a) :
    maximumHomogeneousEntropyBits coordX coordY coordZ reference ≤
      homogeneousCoordinateDualBits coordX coordY coordZ reference uX uY uZ := by
  by_cases hzero : totalMass reference = 0
  · have hrefZero : reference = 0 :=
      eq_zero_of_nonneg_of_totalMass_eq_zero reference href hzero
    subst reference
    have hdualZero :
        homogeneousCoordinateDualBits coordX coordY coordZ (0 : A → ℝ) uX uY uZ = 0 := by
      simp [homogeneousCoordinateDualBits, totalMass, marginal]
    rw [hdualZero]
    unfold maximumHomogeneousEntropyBits
    apply csSup_le
    · refine ⟨0, (0 : A → ℝ), (by simp), ?_, ?_⟩
      · exact ⟨rfl, rfl, rfl, rfl⟩
      · simp [homogeneousEntropyBits, homogeneousEntropy, entropy, totalMass]
    · intro h hh
      rcases hh with ⟨p, hp, hsame, rfl⟩
      have hpmass : totalMass p = 0 := by
        simpa [totalMass] using hsame.1
      have hpZero : p = 0 := eq_zero_of_nonneg_of_totalMass_eq_zero p hp hpmass
      subst p
      simp [homogeneousEntropyBits, homogeneousEntropy, entropy, totalMass]
  · apply maximumHomogeneousEntropyBits_le_coordinateDual
      coordX coordY coordZ reference uX uY uZ href
    exact lt_of_le_of_ne (Finset.sum_nonneg fun a _ ↦ href a) (Ne.symm hzero)

end

end MatrixMultiplication.HomogeneousEntropyDual
