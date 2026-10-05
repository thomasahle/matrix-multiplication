/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Tensor.IteratedProduct
import AlgebraicComplexity.Tensor.PowerCoherence

/-!
# Products of heterogeneous restrictions of powers

An interface tensor is a finite external product of terms, where the `t`th term is a restriction
of a possibly different power `T^(n_t)`.  `PowerRestriction` packages one such term while keeping
its target leg spaces dependent.  Its product operation proves that the assembled target is a
restriction of the single flat power whose exponent is the sum of the term exponents.

This is optimizer-independent tensor infrastructure.  It is useful for interface tensors, but
also for any construction that combines heterogeneous clients of one source tensor.
-/

namespace AlgebraicComplexity.Tensor

universe u v w

variable {K : Type u} [CommSemiring K]
variable {V : Leg → Type v}
variable [∀ c, AddCommMonoid (V c)] [∀ c, Module K (V c)]

/-- Sum a weight over a nonempty recursively represented word. -/
def positiveWordSum {A : Type*} (weight : A → ℕ) :
    (n : ℕ) → PositiveWord A n → ℕ
  | 0, a => weight a
  | n + 1, word => positiveWordSum weight n word.1 + weight word.2

@[simp] theorem positiveWordSum_zero {A : Type*} (weight : A → ℕ) (a : A) :
    positiveWordSum weight 0 a = weight a :=
  rfl

@[simp] theorem positiveWordSum_succ {A : Type*} (weight : A → ℕ) (n : ℕ)
    (word : PositiveWord A (n + 1)) :
    positiveWordSum weight (n + 1) word =
      positiveWordSum weight n word.1 + weight word.2 :=
  rfl

/-- A common left factor distributes through a positive-word sum. -/
theorem positiveWordSum_mul_left {A : Type*} (k : ℕ) (weight : A → ℕ)
    (n : ℕ) (word : PositiveWord A n) :
    positiveWordSum (fun a ↦ k * weight a) n word =
      k * positiveWordSum weight n word := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [positiveWordSum_succ, positiveWordSum_succ, ih, Nat.mul_add]

/-- Summing after letterwise mapping is summing the pulled-back weight. -/
theorem positiveWordSum_map {A B : Type*} (f : A → B) (weight : B → ℕ)
    (n : ℕ) (word : PositiveWord A n) :
    positiveWordSum weight n (positiveWordMap f n word) =
      positiveWordSum (weight ∘ f) n word := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [positiveWordMap_succ]
      change positiveWordSum weight n (positiveWordMap f n word.1) + weight (f word.2) =
        positiveWordSum (weight ∘ f) n word.1 + (weight ∘ f) word.2
      rw [ih]
      rfl

/-- One heterogeneous target tensor together with a proof that it is a restriction of a
canonical power of the fixed source tensor `T`. -/
structure PowerRestriction (T : Tensor3 K V) where
  exponent : ℕ
  Target : LegModuleFamily.{u, w} K
  target : Tensor3 K Target.Space
  restricts : Restricts (power T exponent) target

namespace PowerRestriction

variable {T : Tensor3 K V}

/-- Externally multiply two targets.  Their source exponents add, and power coherence turns the
two source powers into one canonical flat power. -/
noncomputable def external
    (left right : PowerRestriction.{u, v, w} T) : PowerRestriction.{u, v, w} T where
  exponent := left.exponent + right.exponent
  Target := left.Target.external right.Target
  target := Tensor.external left.target right.target
  restricts := by
    have hmul : Isomorphic
        (Tensor.external (power T left.exponent) (power T right.exponent))
        (power T (left.exponent + right.exponent)) := by
      have h := Isomorphic.map
        (Tensor.external (power T left.exponent) (power T right.exponent))
        (powerMulEquiv (K := K) (V := V) left.exponent right.exponent)
      change Isomorphic
        (Tensor.external (power T left.exponent) (power T right.exponent))
        (powerMul left.exponent right.exponent
          (power T left.exponent) (power T right.exponent)) at h
      rw [powerMul_power] at h
      exact h
    exact hmul.symm.restricts.trans (left.restricts.external right.restricts)

@[simp] theorem external_exponent
    (left right : PowerRestriction.{u, v, w} T) :
    (left.external right).exponent = left.exponent + right.exponent :=
  rfl

/-- Assemble a nonempty heterogeneous family of power restrictions. -/
noncomputable def positiveProduct :
    (n : ℕ) → PositiveWord (PowerRestriction.{u, v, w} T) n →
      PowerRestriction.{u, v, w} T
  | 0, term => term
  | n + 1, terms => (positiveProduct n terms.1).external terms.2

@[simp] theorem positiveProduct_zero (term : PowerRestriction.{u, v, w} T) :
    positiveProduct 0 term = term :=
  rfl

@[simp] theorem positiveProduct_succ (n : ℕ)
    (terms : PositiveWord (PowerRestriction.{u, v, w} T) (n + 1)) :
    positiveProduct (n + 1) terms = (positiveProduct n terms.1).external terms.2 :=
  rfl

/-- The source exponent of an assembled family is exactly the sum of its term exponents. -/
theorem positiveProduct_exponent (n : ℕ)
    (terms : PositiveWord (PowerRestriction.{u, v, w} T) n) :
    (positiveProduct n terms).exponent = positiveWordSum PowerRestriction.exponent n terms := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change (positiveProduct n terms.1).exponent + terms.2.exponent =
        positiveWordSum PowerRestriction.exponent n terms.1 + terms.2.exponent
      rw [ih terms.1]

end PowerRestriction

end AlgebraicComplexity.Tensor
