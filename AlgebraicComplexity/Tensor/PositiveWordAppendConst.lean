/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Tensor.IteratedProduct
import AlgebraicComplexity.Tensor.PositiveWordConst

set_option autoImplicit false

/-!
# A constant word is the concatenation of constant words

Layer 1 (`AlgebraicComplexity/Tensor/`).  `positiveWordAppend`
(`Tensor/IteratedProduct.lean`) concatenates two nonempty recursively parenthesized words, and
`positiveWordConst` (`Tensor/PositiveWordConst.lean`) is the constant one.  This module records
that the two commute, which is what a *regional* division of a leaf whose coarse target is
constant on every leg needs: `SegmentedRegionalWeights`
(`MatrixMultiplication/SegmentedLocalizedDivisionIterated.lean`) asks its client for
`∀ c, target c = positiveWordAppend (targetHead c) _ (targetTail c)`, and when the target is a
constant word per leg --- as every cell of `[duan2023faster]`'s section 6.3 leaf has --- that
obligation is exactly this lemma.

The statement is one induction on the right-hand length: `positiveWordAppend` peels its last
letter and `positiveWordConst` supplies the same letter, so the two recursions line up with no
arithmetic on the length parameters (`n + (m + 1) + 1` and `(n + m + 1) + 1` are the same numeral
by the definition of `Nat.add`).

Nothing here mentions a tensor, a partition or a Coppersmith--Winograd constant.

Exact source lines: `papers/sources/2210.10173/global_value.tex:332-378` (§6.3).
-/

namespace AlgebraicComplexity.Tensor

universe w

/-- **A constant word splits as constant words.**  Concatenating the constant words of parameters
`n` and `m` gives the constant word of parameter `n + m + 1`. -/
theorem positiveWordAppend_const {I : Type w} (a : I) (n m : ℕ) :
    positiveWordAppend (positiveWordConst a n) m (positiveWordConst a m) =
      positiveWordConst a (n + m + 1) := by
  induction m with
  | zero => rfl
  | succ m ih =>
      show (positiveWordAppend (positiveWordConst a n) m (positiveWordConst a m), a) = _
      rw [ih]
      rfl

/-- **The legwise corollary.**  A block address that is a constant word on every leg splits as the
two block addresses that are constant on every leg with the same letters --- the `htarget`
obligation of a regional division, at a constant coarse target. -/
theorem ofLegs_positiveWordAppend_const {I : Type w} (x y z : I) (n m : ℕ) (c : Leg) :
    ofLegs (V := fun _ : Leg ↦ PositiveWord I (n + m + 1)) (positiveWordConst x (n + m + 1))
        (positiveWordConst y (n + m + 1)) (positiveWordConst z (n + m + 1)) c =
      positiveWordAppend
        (ofLegs (V := fun _ : Leg ↦ PositiveWord I n) (positiveWordConst x n)
          (positiveWordConst y n) (positiveWordConst z n) c)
        m
        (ofLegs (V := fun _ : Leg ↦ PositiveWord I m) (positiveWordConst x m)
          (positiveWordConst y m) (positiveWordConst z m) c) := by
  cases c
  · exact (positiveWordAppend_const x n m).symm
  · exact (positiveWordAppend_const y n m).symm
  · exact (positiveWordAppend_const z n m).symm

end AlgebraicComplexity.Tensor
