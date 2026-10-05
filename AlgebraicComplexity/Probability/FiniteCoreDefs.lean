/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Real.Basic

set_option autoImplicit false

/-!
# Core definitions for finite probability vectors

This definition-level leaf contains the finite probability structure and the three constructions
needed by zero-safe finite disintegration: deterministic pushforward, a joint law from an outer
law and conditional rows, and point masses.  Keeping this interface below the full finite-
probability API lets exact certificate checkers import only their semantic prerequisites.

## References

- [alman2025more] Josh Alman et al., *More Asymmetry Yields Faster Matrix Multiplication*.
- [dupont2026improving] Emilien Dupont et al., *Improving the Matrix Multiplication Exponent with
  Modern Optimization and AlphaEvolve*.
-/

open scoped BigOperators

namespace AlgebraicComplexity

universe u

/-- A real probability vector on a finite type. -/
structure ProbabilityVector (ι : Type u) [Fintype ι] where
  weight : ι → ℝ
  nonneg : ∀ i, 0 ≤ weight i
  total : ∑ i, weight i = 1

namespace ProbabilityVector

variable {ι : Type u} [Fintype ι]

/-- Push a finite probability vector forward along an arbitrary map. -/
def pushforward {κ : Type*} [Fintype κ] [DecidableEq κ]
    (f : ι → κ) (p : ProbabilityVector ι) : ProbabilityVector κ where
  weight k := ∑ i, if f i = k then p.weight i else 0
  nonneg k := Finset.sum_nonneg fun i _ ↦ by
    by_cases h : f i = k
    · simpa [h] using p.nonneg i
    · simp [h]
  total := by
    classical
    rw [Finset.sum_comm]
    calc
      (∑ i, ∑ k, if f i = k then p.weight i else 0) = ∑ i, p.weight i := by
        apply Finset.sum_congr rfl
        intro i _
        simp
      _ = 1 := p.total

@[simp] theorem pushforward_weight {κ : Type*} [Fintype κ] [DecidableEq κ]
    (f : ι → κ) (p : ProbabilityVector ι) (k : κ) :
    (p.pushforward f).weight k = ∑ i, if f i = k then p.weight i else 0 :=
  rfl

/-- Joint law obtained from an outer distribution and a finite conditional family. -/
def joint {κ : Type*} [Fintype κ]
    (p : ProbabilityVector ι) (family : ι → ProbabilityVector κ) :
    ProbabilityVector (ι × κ) where
  weight x := p.weight x.1 * (family x.1).weight x.2
  nonneg x := mul_nonneg (p.nonneg x.1) ((family x.1).nonneg x.2)
  total := by
    classical
    rw [Fintype.sum_prod_type]
    simp_rw [← Finset.mul_sum, (family _).total, mul_one]
    exact p.total

/-- Probability vectors are determined by their weights. -/
@[ext] theorem ext {p q : ProbabilityVector ι} (h : p.weight = q.weight) : p = q := by
  cases p
  cases q
  cases h
  rfl

/-- The point mass at `i`, equivalently the one-hot probability vector selecting `i`. -/
def pointMass [DecidableEq ι] (i : ι) : ProbabilityVector ι where
  weight j := if j = i then 1 else 0
  nonneg j := by
    by_cases h : j = i <;> simp [h]
  total := by
    classical
    simp

end ProbabilityVector

end AlgebraicComplexity
