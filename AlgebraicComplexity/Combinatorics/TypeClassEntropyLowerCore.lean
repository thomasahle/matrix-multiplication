/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Analysis.StructuralZeroMultinomialLossCore
import AlgebraicComplexity.Combinatorics.WordTypeCardinalityCore
import AlgebraicComplexity.Probability.IntegralProfileEntropyDefs

set_option autoImplicit false

/-!
# Lightweight entropy lower bound for an arbitrary exact type class

This file contains the lower half of the arbitrary-length method of types and its base-two
restatement.  It deliberately does not import the general subexponential copy-growth, conditional
fiber, pigeonhole, or cutoff layers.  Tensor clients that need only a finite directed lower bound
can therefore use this core without loading the much broader `TypeClassCounting` environment.
-/

namespace AlgebraicComplexity.WordType

open scoped BigOperators

universe u

variable {ι : Type u} [Fintype ι]

/-- The Stirling loss separating one exact type class from its entropy exponent, at an arbitrary
word length.  Structural zeroes are harmless because every factor is shifted by one. -/
noncomputable def typeClassEntropyLoss (ι : Type u) [Fintype ι] (n : ℕ) : ℝ :=
  Real.exp 1 ^ Fintype.card ι * (((n + 1 : ℕ) : ℝ)) ^ Fintype.card ι

theorem typeClassEntropyLoss_pos (ι : Type u) [Fintype ι] (n : ℕ) :
    0 < typeClassEntropyLoss ι n := by
  unfold typeClassEntropyLoss
  positivity

/-- At repetition one the structural-zero multinomial loss is bounded by the uniform
arbitrary-length loss. -/
theorem structuralZeroMultinomialLoss_one_le_typeClassEntropyLoss {n : ℕ}
    {a : ι → ℕ} (ha : a ∈ types ι n) :
    structuralZeroMultinomialLoss a 1 ≤ typeClassEntropyLoss ι n := by
  have hprod : (∏ i, (((a i * 1 + 1 : ℕ) : ℝ))) ≤
      (((n + 1 : ℕ) : ℝ)) ^ Fintype.card ι := by
    calc
      (∏ i, (((a i * 1 + 1 : ℕ) : ℝ))) ≤
          ∏ _i : ι, (((n + 1 : ℕ) : ℝ)) := by
        refine Finset.prod_le_prod (fun i _ ↦ by positivity) (fun i _ ↦ ?_)
        have hcoord : a i ≤ n := by
          rw [mem_types] at ha
          rw [← ha]
          exact Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ i)
        have hi : a i * 1 + 1 ≤ n + 1 := Nat.succ_le_succ (by simpa using hcoord)
        exact_mod_cast hi
      _ = (((n + 1 : ℕ) : ℝ)) ^ Fintype.card ι := by
        rw [Finset.prod_const, Finset.card_univ]
  unfold structuralZeroMultinomialLoss typeClassEntropyLoss
  exact mul_le_mul_of_nonneg_left hprod (by positivity)

/-- A legal type of length `n` has total mass `n`. -/
theorem profileMass_eq_of_mem_types {n : ℕ} {a : ι → ℕ} (ha : a ∈ types ι n) :
    profileMass a = n := by
  unfold profileMass
  exact mem_types.mp ha

/-- Method-of-types lower bound at an arbitrary word length, with an explicit polynomial loss. -/
theorem exp_profileEntropy_le_typeClassEntropyLoss_mul_card_typeClass {n : ℕ} (a : ι → ℕ)
    (ha : a ∈ types ι n) (hn : 0 < n) :
    Real.exp ((n : ℝ) * profileEntropyNats a) ≤
      typeClassEntropyLoss ι n * (((typeClass n a).card : ℕ) : ℝ) := by
  have hmass : profileMass a = n := profileMass_eq_of_mem_types ha
  have hprop : proportionalCounts a 1 = a := by
    funext i
    simp [proportionalCounts]
  have hbase := proportionalEntropyBase_pow_le_structuralZeroLoss_mul_multinomial a 1
  rw [pow_one, hprop,
    proportionalEntropyBase_eq_exp_profileEntropy a (by rw [hmass]; exact hn), hmass] at hbase
  calc
    Real.exp ((n : ℝ) * profileEntropyNats a) ≤
        structuralZeroMultinomialLoss a 1 *
          ((Nat.multinomial Finset.univ a : ℕ) : ℝ) := hbase
    _ ≤ typeClassEntropyLoss ι n * ((Nat.multinomial Finset.univ a : ℕ) : ℝ) :=
      mul_le_mul_of_nonneg_right
        (structuralZeroMultinomialLoss_one_le_typeClassEntropyLoss ha) (by positivity)
    _ = typeClassEntropyLoss ι n * (((typeClass n a).card : ℕ) : ℝ) := by
      rw [card_typeClass_eq_multinomial_light a ha]

/-- Convert the natural-exponential entropy expression to base two. -/
theorem two_rpow_mul_profileEntropyBits (a : ι → ℕ) (t : ℝ) :
    (2 : ℝ) ^ (t * profileEntropyBits a) = Real.exp (t * profileEntropyNats a) := by
  have hlog : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
  congr 1
  unfold profileEntropyBits
  field_simp

/-- Base-two form of the arbitrary-length method-of-types lower bound. -/
theorem two_rpow_profileEntropyBits_le_typeClassEntropyLoss_mul_card_typeClass {n : ℕ}
    (a : ι → ℕ) (ha : a ∈ types ι n) (hn : 0 < n) :
    (2 : ℝ) ^ ((n : ℝ) * profileEntropyBits a) ≤
      typeClassEntropyLoss ι n * (((typeClass n a).card : ℕ) : ℝ) := by
  rw [two_rpow_mul_profileEntropyBits]
  exact exp_profileEntropy_le_typeClassEntropyLoss_mul_card_typeClass a ha hn

end AlgebraicComplexity.WordType
