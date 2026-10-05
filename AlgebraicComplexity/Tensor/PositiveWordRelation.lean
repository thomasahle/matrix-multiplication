/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Tensor.IteratedProduct
import AlgebraicComplexity.Tensor.Product

set_option autoImplicit false

/-!
# Factorwise restrictions of positive-word tensor products

This layer-1 module proves that exact tensor restriction is compatible with the heterogeneous
left-associated products represented by `Tensor.positiveWordTensor`.  A separate restriction may
be supplied for every letter of the indexing alphabet; reading any positive word then gives the
external product of precisely those restrictions.

The result isolates the factorwise functoriality used implicitly when Coppersmith and Winograd
take a large power of the exceptional `(1,1,2)` constituent and replace its factors by their local
restrictions [CoppersmithWinograd1990, pp. 270--272], transcribed in
`papers/notes/MMult1987.tex:174-285`.  It is also the product step in Theorem
`thm:exact-nested-total-weight-leaf` of `better_bound/paper.tex:1684-1718`.  This module proves only
that algebraic step: identifying a complete coarsening fiber with such a word product, grouping
shared variables, and counting the surviving words belong to later modules.

## Reference

- [CoppersmithWinograd1990] Don Coppersmith and Shmuel Winograd, *Matrix Multiplication via
  Arithmetic Progressions*.
-/

namespace AlgebraicComplexity.Tensor

universe u v w z

variable {K : Type u} [CommSemiring K]

namespace Restricts

/-- Exact restrictions of every letter induce an exact restriction of every positive-word tensor.

In human-readable terms, suppose that for each index `i`, the source tensor `T i` restricts to the
target tensor `S i`.  Then the left-associated external product selected by any nonempty word in
the sources restricts to the product selected by the same word in the targets.

Proof sketch: recurse on the positive word.  A one-letter word is exactly the supplied local
restriction.  At a successor, apply the induction hypothesis to the prefix and the supplied local
restriction to the last letter, then combine them with compatibility of `Restricts` under the
external product. -/
theorem positiveWordTensor
    {I : Type z}
    (W : I → LegModuleFamily.{u, v} K)
    (W' : I → LegModuleFamily.{u, w} K)
    (T : ∀ i, Tensor3 K (W i).Space)
    (S : ∀ i, Tensor3 K (W' i).Space)
    (h : ∀ i, Restricts (T i) (S i)) :
    ∀ (n : ℕ) (word : PositiveWord I n),
      Restricts (positiveWordTensor W T n word)
        (positiveWordTensor W' S n word)
  | 0, i => h i
  | n + 1, word =>
      (positiveWordTensor W W' T S h n word.1).external (h word.2)

end Restricts

end AlgebraicComplexity.Tensor
