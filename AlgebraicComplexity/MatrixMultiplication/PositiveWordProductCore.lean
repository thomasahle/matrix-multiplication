/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import Init.Prelude
import AlgebraicComplexity.Tensor.PositiveWordDefs

/-!
# Numerical products along positive tensor words

This lightweight semantic leaf defines the product of a natural-valued letter parameter along
the recursively represented nonempty words used by tensor powers.  It also proves the recursive
simplification laws and positivity.  In particular, it deliberately does not import finite big
operators: the equivalence with a product over `Fin` lives downstream in `PositiveWordProduct`.

Keeping the recursive API here lets tensor-dimension clients avoid loading Mathlib's finite
big-operator environment when they never convert a word into its function representation.
-/

namespace AlgebraicComplexity

universe w

variable {I : Type w}

/-- Product of a numerical parameter along a recursively represented positive word. -/
def positiveWordProduct (x : I → Nat) :
    (r : Nat) → Tensor.PositiveWord I r → Nat
  | Nat.zero, i => x i
  | Nat.succ r, q => Nat.mul (positiveWordProduct x r q.1) (x q.2)

@[simp] theorem positiveWordProduct_zero (x : I → Nat)
    (i : Tensor.PositiveWord I Nat.zero) :
    positiveWordProduct x Nat.zero i = x i := rfl

@[simp] theorem positiveWordProduct_succ (x : I → Nat) (r : Nat)
    (q : Tensor.PositiveWord I (Nat.succ r)) :
    positiveWordProduct x (Nat.succ r) q =
      Nat.mul (positiveWordProduct x r q.1) (x q.2) := rfl

/-- A product along a nonempty recursive word is positive when every letter value is positive.

Proof sketch: induct on the recursive word length.  The base case is the supplied pointwise
positivity, and the successor case is the product of the positive prefix and final letter. -/
theorem positiveWordProduct_pos_of_forall
    (dimension : I → Nat) (hpositive : ∀ i, Nat.lt Nat.zero (dimension i)) :
    (r : Nat) → (word : Tensor.PositiveWord I r) →
      Nat.lt Nat.zero (positiveWordProduct dimension r word)
  | Nat.zero, word => hpositive word
  | Nat.succ r, word =>
      Nat.mul_pos
        (positiveWordProduct_pos_of_forall dimension hpositive r word.1)
        (hpositive word.2)

end AlgebraicComplexity
