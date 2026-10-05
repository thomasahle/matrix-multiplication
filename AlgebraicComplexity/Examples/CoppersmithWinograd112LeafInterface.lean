/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinograd112Global
import AlgebraicComplexity.Examples.CoppersmithWinograd112TypedLeaf

/-!
# Interface between the finite CW `112` extraction and its rational typed-leaf rates

The finite shared-Z/C-tensor development and the entropy-facing rational typed-leaf development
are intentionally independent.  This module is their narrow integration boundary.  It proves
that the square matrix side appearing in the finite degeneration is exactly the product of the
three primitive rectangular dimensions recorded by the typed leaf.

Keeping this equality here prevents probability and real-analysis imports from entering the
finite semantic extraction, while giving recursive certificate clients a checked translation
between the two APIs.
-/

open scoped BigOperators

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor

/-- The finite square side `q^(4G+2L)` is exactly the product of the three dimension coordinates
of the canonical rational `112` leaf.

Proof sketch: the primitive dimensions are `q^(2G)`, `q^(2L)`, and `q^(2G)`; multiply them and
add the exponents. -/
theorem cw112FiniteLeafSquareSide_eq_typedLeaf_dimensionProduct
    (q L G : ℕ) (hq : 0 < q) (hL : 0 < L) (hG : 0 < G) :
    cw112FiniteLeafSquareSide q L G =
      ∏ c, (cw112RationalTypedLeaf q L G hq hL hG).dimensionProduct c := by
  let leaf := cw112RationalTypedLeaf q L G hq hL hG
  have hexponent : 4 * G + 2 * L = (2 * G + 2 * L) + 2 * G := by
    omega
  have hnumeric : cw112FiniteLeafSquareSide q L G =
      q ^ (2 * G) * q ^ (2 * L) * q ^ (2 * G) := by
    unfold cw112FiniteLeafSquareSide
    calc
      q ^ (4 * G + 2 * L) = q ^ ((2 * G + 2 * L) + 2 * G) :=
        congrArg (fun e : ℕ ↦ q ^ e) hexponent
      _ = q ^ (2 * G) * q ^ (2 * L) * q ^ (2 * G) := by
        rw [pow_add, pow_add]
  have hx : q ^ (2 * G) = leaf.dimensionProduct .X :=
    (cw112RationalTypedLeaf_dimensionProduct_X q L G hq hL hG).symm
  have hy : q ^ (2 * L) = leaf.dimensionProduct .Y :=
    (cw112RationalTypedLeaf_dimensionProduct_Y q L G hq hL hG).symm
  have hz : q ^ (2 * G) = leaf.dimensionProduct .Z :=
    (cw112RationalTypedLeaf_dimensionProduct_Z q L G hq hL hG).symm
  calc
    cw112FiniteLeafSquareSide q L G =
        q ^ (2 * G) * q ^ (2 * L) * q ^ (2 * G) := hnumeric
    _ = leaf.dimensionProduct .X * q ^ (2 * L) * q ^ (2 * G) :=
      congrArg (fun a : ℕ ↦ a * q ^ (2 * L) * q ^ (2 * G)) hx
    _ = leaf.dimensionProduct .X * leaf.dimensionProduct .Y * q ^ (2 * G) :=
      congrArg (fun b : ℕ ↦ leaf.dimensionProduct .X * b * q ^ (2 * G)) hy
    _ = leaf.dimensionProduct .X * leaf.dimensionProduct .Y * leaf.dimensionProduct .Z :=
      congrArg (fun c : ℕ ↦ leaf.dimensionProduct .X * leaf.dimensionProduct .Y * c) hz
    _ = ∏ c, leaf.dimensionProduct c := (prod_leg _).symm

end AlgebraicComplexity.Examples
