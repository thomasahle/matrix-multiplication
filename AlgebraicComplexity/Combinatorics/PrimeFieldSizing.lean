import AlgebraicComplexity.Analysis.Subexponential
import AlgebraicComplexity.Combinatorics.ProgressionFree
import Mathlib.NumberTheory.Bertrand

/-!
# Prime-field sizing for finite hashing

Finite affine-hashing arguments need a field whose cardinality dominates an exact collision
requirement.  They may also need a lower bound on the characteristic in order to inject a fixed
finite alphabet.  This file makes the standard Bertrand choice canonical and separates its
constant-factor cost from the exponential rate.

The chosen prime is strictly larger than both the requested cardinality and a supplied
characteristic floor.  Small or zero requirements are handled uniformly by including `1` in the
Bertrand input.  The accompanying loss theorem shows that, whenever the requirement is bounded
by `loss r * base ^ r`, the prime cardinality has the same exponential base and only a positive
subexponential multiplicative loss.
-/

namespace AlgebraicComplexity.PrimeFieldSizing

/-- Positive input to Bertrand's postulate, dominating the characteristic floor and the exact
finite cardinality requirement. -/
def bertrandInput (characteristicFloor requirement : ℕ) : ℕ :=
  max (max characteristicFloor requirement) 1

theorem bertrandInput_ne_zero (characteristicFloor requirement : ℕ) :
    bertrandInput characteristicFloor requirement ≠ 0 := by
  unfold bertrandInput
  omega

/-- Canonical prime supplied by Bertrand's postulate. -/
noncomputable def modulus (characteristicFloor requirement : ℕ) : ℕ :=
  Classical.choose
    (Nat.exists_prime_lt_and_le_two_mul
      (bertrandInput characteristicFloor requirement)
      (bertrandInput_ne_zero characteristicFloor requirement))

theorem modulus_prime (characteristicFloor requirement : ℕ) :
    (modulus characteristicFloor requirement).Prime := by
  exact (Classical.choose_spec
    (Nat.exists_prime_lt_and_le_two_mul
      (bertrandInput characteristicFloor requirement)
      (bertrandInput_ne_zero characteristicFloor requirement))).1

theorem bertrandInput_lt_modulus (characteristicFloor requirement : ℕ) :
    bertrandInput characteristicFloor requirement < modulus characteristicFloor requirement := by
  exact (Classical.choose_spec
    (Nat.exists_prime_lt_and_le_two_mul
      (bertrandInput characteristicFloor requirement)
      (bertrandInput_ne_zero characteristicFloor requirement))).2.1

theorem modulus_le_two_mul_bertrandInput (characteristicFloor requirement : ℕ) :
    modulus characteristicFloor requirement ≤
      2 * bertrandInput characteristicFloor requirement := by
  exact (Classical.choose_spec
    (Nat.exists_prime_lt_and_le_two_mul
      (bertrandInput characteristicFloor requirement)
      (bertrandInput_ne_zero characteristicFloor requirement))).2.2

/-- The selected prime strictly exceeds the requested field cardinality. -/
theorem requirement_lt_modulus (characteristicFloor requirement : ℕ) :
    requirement < modulus characteristicFloor requirement := by
  exact (Nat.le_max_right characteristicFloor requirement |>.trans
    (Nat.le_max_left (max characteristicFloor requirement) 1)).trans_lt
      (bertrandInput_lt_modulus characteristicFloor requirement)

/-- The selected prime strictly exceeds the characteristic floor. -/
theorem characteristicFloor_lt_modulus (characteristicFloor requirement : ℕ) :
    characteristicFloor < modulus characteristicFloor requirement := by
  exact (Nat.le_max_left characteristicFloor requirement |>.trans
    (Nat.le_max_left (max characteristicFloor requirement) 1)).trans_lt
      (bertrandInput_lt_modulus characteristicFloor requirement)

/-- A coarse additive upper bound convenient for real-valued asymptotic estimates. -/
theorem modulus_le_two_mul_add (characteristicFloor requirement : ℕ) :
    modulus characteristicFloor requirement ≤
      2 * (characteristicFloor + requirement + 1) := by
  apply (modulus_le_two_mul_bertrandInput characteristicFloor requirement).trans
  apply Nat.mul_le_mul_left
  unfold bertrandInput
  omega

/-- The canonical modulus carries its prime fact without any client-side choice. -/
noncomputable instance instFactModulusPrime (characteristicFloor requirement : ℕ) :
    Fact (modulus characteristicFloor requirement).Prime :=
  ⟨modulus_prime characteristicFloor requirement⟩

/-- If the requested characteristic floor is at least two, then two is nonzero in the selected
prime field. -/
theorem neZeroTwo (characteristicFloor requirement : ℕ)
    (hfloor : 2 ≤ characteristicFloor) :
    NeZero (2 : ZMod (modulus characteristicFloor requirement)) := by
  have hthree : 3 ≤ modulus characteristicFloor requirement := by
    have hlower := characteristicFloor_lt_modulus characteristicFloor requirement
    omega
  exact neZero_two_zmod_of_three_le hthree

/-- Explicit multiplicative loss incurred by the safe prime-field choice. -/
noncomputable def loss (characteristicFloor : ℕ) (inputLoss : ℕ → ℝ) (r : ℕ) : ℝ :=
  2 * (inputLoss r + ((characteristicFloor : ℝ) + 1))

/-- Prime-field sizing preserves subexponential growth. -/
theorem loss_subexponential (characteristicFloor : ℕ) {inputLoss : ℕ → ℝ}
    (hinput : Growth.Subexponential inputLoss) :
    Growth.Subexponential (loss characteristicFloor inputLoss) := by
  have hconstant : Growth.Subexponential
      (fun _ : ℕ ↦ ((characteristicFloor : ℝ) + 1)) :=
    Growth.Subexponential.const (by positivity)
  have hadd : Growth.Subexponential
      (fun r ↦ inputLoss r + ((characteristicFloor : ℝ) + 1)) :=
    hinput.add hconstant
  change Growth.Subexponential
    (fun r ↦ 2 * (inputLoss r + ((characteristicFloor : ℝ) + 1)))
  exact hadd.const_mul (show (0 : ℝ) ≤ 2 by norm_num)

/-- Pointwise prime-cardinality bound with the exponential base unchanged.

The additive characteristic floor and the small-requirement safeguard are absorbed by `loss`;
only `base ^ r` remains exponential. -/
theorem modulus_cast_le_loss_mul_pow
    (characteristicFloor requirement r : ℕ)
    (inputLoss base : ℝ)
    (hbase : 1 ≤ base)
    (hrequirement : (requirement : ℝ) ≤ inputLoss * base ^ r) :
    (modulus characteristicFloor requirement : ℝ) ≤
      (2 * (inputLoss + characteristicFloor + 1)) * base ^ r := by
  have hmodulus : (modulus characteristicFloor requirement : ℝ) ≤
      2 * ((characteristicFloor : ℝ) + requirement + 1) := by
    exact_mod_cast modulus_le_two_mul_add characteristicFloor requirement
  have hpow : 1 ≤ base ^ r := one_le_pow₀ hbase
  calc
    (modulus characteristicFloor requirement : ℝ) ≤
        2 * ((characteristicFloor : ℝ) + requirement + 1) := hmodulus
    _ ≤ 2 * ((characteristicFloor : ℝ) + inputLoss * base ^ r + 1) := by
      gcongr
    _ ≤ (2 * (inputLoss + characteristicFloor + 1)) * base ^ r := by
      nlinarith [mul_nonneg
        (show (0 : ℝ) ≤ (characteristicFloor : ℝ) + 1 by positivity)
        (sub_nonneg.mpr hpow)]

/-- Sequence form of `modulus_cast_le_loss_mul_pow`. -/
theorem modulus_cast_le_sequenceLoss_mul_pow
    (characteristicFloor : ℕ) (requirement : ℕ → ℕ)
    (inputLoss : ℕ → ℝ) (base : ℝ)
    (hbase : 1 ≤ base)
    (hrequirement : ∀ r, (requirement r : ℝ) ≤ inputLoss r * base ^ r) :
    ∀ r, (modulus characteristicFloor (requirement r) : ℝ) ≤
      loss characteristicFloor inputLoss r * base ^ r := by
  intro r
  simpa only [loss, add_assoc] using
    (modulus_cast_le_loss_mul_pow characteristicFloor (requirement r) r
      (inputLoss r) base hbase (hrequirement r))

end AlgebraicComplexity.PrimeFieldSizing
