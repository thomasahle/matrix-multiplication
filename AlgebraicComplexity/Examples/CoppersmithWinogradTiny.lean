/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinograd

/-!
# Tiny Coppersmith--Winograd instances `CW_1` and `CW_2`

This file instantiates the generic classical Coppersmith--Winograd construction of
`Examples/CoppersmithWinograd.lean` at the two smallest parameters `q = 1` and `q = 2`, as
required by the trust policy in `DESIGN.md`: small named instances catch relation-direction,
certificate-length, and index-convention errors in the generic development before they can hide
inside a large proof.

The results are all direct specializations of the generic theorems:

- the border-rank certificates `BorderRankLE 3 CW_1` and `BorderRankLE 4 CW_2`
  (the generic bound is `q + 2`);
- the explicit certificate lists have lengths `3` and `4`;
- the monomial weighting of `CW_1` retains exactly its single symmetric middle summand;
- `CW_2` exactly restricts to `⟨1,1,2⟩`, so `⟨1,1,2⟩` inherits `BorderRankLE 4`.

This is a layer-4 regression client downstream of the generic CW client; it proves nothing new
about the construction and must stay free of paper-specific data.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor

universe u

variable (K : Type u) [CommRing K]

/-- The smallest Coppersmith--Winograd tensor `CW_1` has border rank at most `1 + 2 = 3`.

Direct instance of the generic polynomial certificate; it would catch an off-by-one in the
`q + 2` certificate count. -/
theorem coppersmithWinograd_one_borderRankLE :
    BorderRankLE 3 (coppersmithWinograd K 1) := by
  simpa using coppersmithWinograd_borderRankLE K 1

/-- The Coppersmith--Winograd tensor `CW_2` has border rank at most `2 + 2 = 4`. -/
theorem coppersmithWinograd_two_borderRankLE :
    BorderRankLE 4 (coppersmithWinograd K 2) := by
  simpa using coppersmithWinograd_borderRankLE K 2

/-- The explicit `CW_1` polynomial certificate consists of exactly `3` rank-one curves.

A sanity check on the certificate list itself, not just the inequality it witnesses. -/
theorem cwBorderTerms_one_length : (cwBorderTerms K 1).length = 3 := by
  simp

/-- The explicit `CW_2` polynomial certificate consists of exactly `4` rank-one curves. -/
theorem cwBorderTerms_two_length : (cwBorderTerms K 2).length = 4 := by
  simp

/-- Weighting the final coordinate of `CW_1` removes its three corner terms and retains exactly
the single symmetric middle summand `cwMiddle K 1 0`.

The `q = 1` middle block has one member, so the generic sum collapses; this would catch a
monomial-weight convention that kept the wrong constituents. -/
theorem coppersmithWinograd_one_monomialDegenerates_middle :
    MonomialDegenerates (coppersmithWinograd K 1) (cwMiddle K 1 0) := by
  simpa using coppersmithWinograd_monomialDegenerates_middle K 1

/-- `CW_2` exactly restricts to `⟨1,1,2⟩`, so the rectangular matrix-multiplication tensor
`⟨1,1,2⟩` inherits the border-rank bound `4` of `CW_2`.

This composes the generic `(0,1,1)`-constituent restriction with monotonicity of border rank
under restriction; a reversed `Restricts` direction would make the composition fail. -/
theorem matrixMultiplication_one_one_two_borderRankLE :
    BorderRankLE 4 (matrixMultiplication (K := K) 1 1 2) :=
  (coppersmithWinograd_two_borderRankLE K).of_restricts
    (coppersmithWinograd_restricts_011 K 2)

end AlgebraicComplexity.Examples
