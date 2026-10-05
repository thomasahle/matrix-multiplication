/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

/-!
# Recursively represented nonempty words: definition leaf

`PositiveWord I n` is a left-associated word of `n + 1` letters in `I`.  This file contains only
that recursive datatype and deliberately has no Mathlib import.  Equivalences, finite instances,
and word operations live downstream in `PositiveWord` and `IteratedProduct`.
-/

namespace AlgebraicComplexity.Tensor

universe w

/-- A recursively parenthesized word of length `n + 1`. -/
def PositiveWord (I : Type w) : Nat → Type w
  | Nat.zero => I
  | Nat.succ n => Prod (PositiveWord I n) I

end AlgebraicComplexity.Tensor
