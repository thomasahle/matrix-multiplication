/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Tensor.PositiveWordInstances
import Mathlib.Data.Fin.Tuple.Basic

/-!
# Recursively represented nonempty words

`PositiveWord I n` is a left-associated word of `n + 1` letters in `I`; its definition lives in
the import-free `PositiveWordDefs` leaf.  This module adds the canonical equivalence with functions
on `Fin (n + 1)` and the standard finite instances.  It remains independent of tensors,
polynomial degenerations, and indexed products.

The operations on words and the tensor products indexed by them remain in
`Tensor.IteratedProduct`, which re-exports this module.
-/

namespace AlgebraicComplexity.Tensor

universe w

/-- Recursive words are canonically equivalent to functions on `Fin (n + 1)`. -/
def positiveWordEquiv (I : Type w) :
    (n : ℕ) → PositiveWord I n ≃ (Fin (n + 1) → I)
  | 0 => (Equiv.funUnique (Fin 1) I).symm
  | n + 1 =>
      (Equiv.prodCongr (positiveWordEquiv I n) (Equiv.refl I)).trans
        ((Equiv.prodComm (Fin (n + 1) → I) I).trans
          (Fin.snocEquiv (fun _ : Fin (n + 2) ↦ I)))

@[simp] theorem positiveWordEquiv_zero_apply (I : Type w) (i : PositiveWord I 0) :
    positiveWordEquiv I 0 i = fun _ ↦ i := by
  rfl

@[simp] theorem positiveWordEquiv_succ_apply (I : Type w) (n : ℕ)
    (q : PositiveWord I (n + 1)) :
    positiveWordEquiv I (n + 1) q =
      Fin.snoc (positiveWordEquiv I n q.1) q.2 := by
  rfl

end AlgebraicComplexity.Tensor
