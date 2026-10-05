/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Tensor.PositiveWordDefs

/-!
# Constant recursively represented nonempty words

This definition-only leaf constructs the positive word whose every letter is a fixed value.  It
is independent of tensor products and of the equivalence with functions on `Fin (n + 1)`.
-/

namespace AlgebraicComplexity.Tensor

universe w

variable {I : Type w}

/-- The recursively represented positive word whose every letter is `i`.  Its parameter `n`
means that it contains `n + 1` copies of `i`, as for every `PositiveWord`. -/
def positiveWordConst (i : I) : (n : Nat) → PositiveWord I n
  | Nat.zero => i
  | Nat.succ n => Prod.mk (positiveWordConst i n) i

end AlgebraicComplexity.Tensor
