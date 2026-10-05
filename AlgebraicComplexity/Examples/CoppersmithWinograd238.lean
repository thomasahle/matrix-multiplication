/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinograd238Arithmetic
import AlgebraicComplexity.Examples.CoppersmithWinogradSquare112TauValueGrowth

/-!
# The classical Coppersmith--Winograd bound `ω < 2.38`

This is the directed-arithmetic client of the modern CW-square value construction.  The chosen
integer profile is a nearby exact rationalization of the rounded parameters printed in
Coppersmith--Winograd 1990, §8:

```text
q = 6,  τ = 119/150,
(a,b,c,d) = (459, 24655, 202168, 405224),
(L,G) = (1,36),  d = [2(L+G)]³.
```

Its outer stride is `1971483`.  Both strict entropy bases are taken to be one half of their exact
method-of-types bases.  This constant-factor reserve disappears after normalization (costing only
`2 log 2 / 1971483` in the final logarithm) and avoids any appeal to supremum attainment.

All logarithmic estimates are rational atanh certificates from `Analysis/Log.lean`; no floating
point evaluation, compiled Boolean shortcut, or unproved numerical oracle is used.  The theorem
deliberately targets the clean regression value `2.38`, not the more tightly optimized `2.375477`
printed in the paper.

Primary source: Don Coppersmith and Shmuel Winograd, *Matrix Multiplication via Arithmetic
Progressions*, Journal of Symbolic Computation 9(3), 251--280 (1990), Sections 6--8,
DOI 10.1016/S0747-7171(08)80013-2.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity
open AlgebraicComplexity.Analysis
open Tensor

universe u

noncomputable section

variable (K : Type u) [Field K]

/-! ## Exact rational profile -/

/-- Value parameter `τ = 119/150`, so the resulting exponent target is `3τ = 2.38`. -/
def cwSquare238Tau : ℝ := 119 / 150
/-- Multiplicity of one address in the outer `004` orbit. -/
def cwSquare238A : ℕ := 459
/-- Multiplicity of one address in the outer `013` orbit. -/
def cwSquare238B : ℕ := 24655
/-- Multiplicity of one address in the outer `022` orbit. -/
def cwSquare238C : ℕ := 202168
/-- Light-letter multiplicity in the exceptional `(112)` leaf. -/
def cwSquare238L : ℕ := 1
/-- Heavy-letter multiplicity in the exceptional `(112)` leaf. -/
def cwSquare238G : ℕ := 36

/-- The exceptional-orbit multiplicity forced by the cyclic `(112)` profile. -/
abbrev cwSquare238D : ℕ :=
  cwSquareSymmetric112Multiplicity cwSquare238L cwSquare238G

/-- The exceptional-orbit multiplicity is exactly `74³ = 405224`. -/
theorem cwSquare238D_eq : cwSquare238D = 405224 := by
  norm_num [cwSquare238D, cwSquareSymmetric112Multiplicity,
    cwSquare238L, cwSquare238G]

/-- The complete outer profile has total mass `1971483`. -/
theorem cwSquare238Stride_eq :
    cwSquareStride cwSquare238A cwSquare238B cwSquare238C cwSquare238D = 1971483 := by
  norm_num [cwSquare238A, cwSquare238B, cwSquare238C, cwSquare238D,
    cwSquareSymmetric112Multiplicity, cwSquare238L, cwSquare238G, cwSquareStride]

private theorem cwSquare238A_pos : 0 < cwSquare238A := by norm_num [cwSquare238A]
private theorem cwSquare238B_pos : 0 < cwSquare238B := by norm_num [cwSquare238B]
private theorem cwSquare238C_pos : 0 < cwSquare238C := by norm_num [cwSquare238C]
private theorem cwSquare238L_pos : 0 < cwSquare238L := by norm_num [cwSquare238L]
private theorem cwSquare238G_pos : 0 < cwSquare238G := by norm_num [cwSquare238G]

/-- Strict outer copy base, with a harmless factor-two reserve below the exact entropy base. -/
noncomputable def cwSquare238OuterBase : ℝ :=
  cwSquareOuterEntropyBase cwSquare238A cwSquare238B cwSquare238C cwSquare238D / 2

/-- Strict inner copy base, again with a factor-two reserve. -/
noncomputable def cwSquare238InnerCopyBase : ℝ :=
  cw112SymmetricMarginalEntropyBase K 6 cwSquare238L cwSquare238G
    (by norm_num) cwSquare238L_pos cwSquare238G_pos / 2

/-- The reserved outer survivor base remains positive. -/
theorem cwSquare238OuterBase_pos : 0 < cwSquare238OuterBase := by
  unfold cwSquare238OuterBase cwSquareOuterEntropyBase
  exact div_pos
    (WordType.proportionalEntropyBase_pos_zeroSafe
      (cwSquareBaseMarginal cwSquare238A cwSquare238B cwSquare238C cwSquare238D))
    (by norm_num)

/-- The reserved outer base is strictly below the exact marginal-entropy base. -/
theorem cwSquare238OuterBase_lt :
    cwSquare238OuterBase <
      cwSquareOuterEntropyBase cwSquare238A cwSquare238B cwSquare238C cwSquare238D := by
  unfold cwSquare238OuterBase
  exact div_lt_self
    (by
      unfold cwSquareOuterEntropyBase
      exact WordType.proportionalEntropyBase_pos_zeroSafe _)
    (by norm_num)

/-- The reserved inner visible-copy base remains positive. -/
theorem cwSquare238InnerCopyBase_pos : 0 < cwSquare238InnerCopyBase K := by
  unfold cwSquare238InnerCopyBase
  exact div_pos
    (cw112SymmetricMarginalEntropyBase_pos
      K 6 cwSquare238L cwSquare238G (by norm_num) cwSquare238L_pos cwSquare238G_pos)
    (by norm_num)

/-- The reserved inner base is strictly below the exact visible marginal-entropy base. -/
theorem cwSquare238InnerCopyBase_lt :
    cwSquare238InnerCopyBase K <
      cw112SymmetricMarginalEntropyBase K 6 cwSquare238L cwSquare238G
        (by norm_num) cwSquare238L_pos cwSquare238G_pos := by
  unfold cwSquare238InnerCopyBase
  exact div_lt_self
    (cw112SymmetricMarginalEntropyBase_pos
      K 6 cwSquare238L cwSquare238G (by norm_num) cwSquare238L_pos cwSquare238G_pos)
    (by norm_num)

/-! ## Exact logarithmic identities -/

/-- Exact logarithm of the five-coordinate outer entropy base. -/
theorem log_cwSquare238OuterEntropyBase :
    Real.log (cwSquareOuterEntropyBase
      cwSquare238A cwSquare238B cwSquare238C cwSquare238D) =
      252396 * Real.log (1971483 / 252396 : ℝ) +
      859758 * Real.log (1971483 / 859758 : ℝ) +
      809560 * Real.log (1971483 / 809560 : ℝ) +
      49310 * Real.log (1971483 / 49310 : ℝ) +
      459 * Real.log (1971483 / 459 : ℝ) := by
  rw [log_cwSquareOuterEntropyBase
    cwSquare238A_pos cwSquare238B_pos cwSquare238C_pos
      (cwSquareSymmetric112Multiplicity_pos cwSquare238L_pos)]
  rw [show (Finset.univ : Finset (Fin 5)) = {0, 1, 2, 3, 4} by decide,
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  norm_num [cwSquareBaseMarginal, cwSquareMarginalType, cwSquareStride,
    cwSquare238A, cwSquare238B, cwSquare238C, cwSquare238D,
    cwSquareSymmetric112Multiplicity, cwSquare238L, cwSquare238G]
  ring

/-- Exact logarithm of the symmetric inner entropy base at `(L,G)=(1,36)`. -/
theorem log_cwSquare238InnerEntropyBase :
    Real.log
        (cw112SymmetricMarginalEntropyBase K 6 cwSquare238L cwSquare238G
          (by norm_num) cwSquare238L_pos cwSquare238G_pos) =
      2 * 405224 * Real.log 2 +
        10952 * Real.log 74 + 394272 * Real.log (37 / 36 : ℝ) := by
  rw [log_cw112SymmetricMarginalEntropyBase
    K 6 cwSquare238L cwSquare238G
      (by norm_num) cwSquare238L_pos cwSquare238G_pos]
  norm_num [cwSquare238L, cwSquare238G]

/-- Exact logarithm of the strict outer survivor base.  Dividing by two contributes the first
of the two constant-factor reserve costs in the final scalar certificate. -/
theorem log_cwSquare238OuterBase :
    Real.log cwSquare238OuterBase =
      252396 * Real.log (1971483 / 252396 : ℝ) +
      859758 * Real.log (1971483 / 859758 : ℝ) +
      809560 * Real.log (1971483 / 809560 : ℝ) +
      49310 * Real.log (1971483 / 49310 : ℝ) +
      459 * Real.log (1971483 / 459 : ℝ) - Real.log 2 := by
  have houter : 0 < cwSquareOuterEntropyBase
      cwSquare238A cwSquare238B cwSquare238C cwSquare238D := by
    unfold cwSquareOuterEntropyBase
    exact WordType.proportionalEntropyBase_pos_zeroSafe _
  rw [cwSquare238OuterBase,
    Real.log_div houter.ne' (by norm_num : (2 : ℝ) ≠ 0),
    log_cwSquare238OuterEntropyBase]

/-- Exact logarithm of the strict inner visible-copy base.  Its factor-two reserve is the second
constant-factor cost in the final certificate. -/
theorem log_cwSquare238InnerCopyBase :
    Real.log (cwSquare238InnerCopyBase K) =
      2 * 405224 * Real.log 2 +
        10952 * Real.log 74 + 394272 * Real.log (37 / 36 : ℝ) - Real.log 2 := by
  rw [cwSquare238InnerCopyBase,
    Real.log_div
      (cw112SymmetricMarginalEntropyBase_pos
        K 6 cwSquare238L cwSquare238G
          (by norm_num) cwSquare238L_pos cwSquare238G_pos).ne'
      (by norm_num : (2 : ℝ) ≠ 0),
    log_cwSquare238InnerEntropyBase]

/-- The ordinary square constituents contribute `12^(2b)` and `38^c` on every leg.  At the
chosen profile their cube-volume logarithm is the displayed linear combination. -/
theorem log_cwSquare238OrdinaryVolume :
    Real.log
        ((cwSquareOrdinaryDimensionBase 6 cwSquare238B cwSquare238C *
          cwSquareOrdinaryDimensionBase 6 cwSquare238B cwSquare238C *
          cwSquareOrdinaryDimensionBase 6 cwSquare238B cwSquare238C : ℕ) : ℝ) =
      147930 * Real.log 12 + 606504 * Real.log 38 := by
  rw [log_cwSquareOrdinaryVolume 6 cwSquare238B cwSquare238C (by norm_num)]
  norm_num [cwSquare238B, cwSquare238C]

/-- The symmetric inner `(112)` leaf has matrix-volume logarithm `2398488 log 6` at
`(L,G)=(1,36)`. -/
theorem log_cwSquare238InnerDimensionVolume :
    Real.log
        (((cw112SymmetricLeaf K 6 cwSquare238L cwSquare238G
              (by norm_num) cwSquare238L_pos cwSquare238G_pos).dimensionProduct .X *
          (cw112SymmetricLeaf K 6 cwSquare238L cwSquare238G
              (by norm_num) cwSquare238L_pos cwSquare238G_pos).dimensionProduct .Y *
          (cw112SymmetricLeaf K 6 cwSquare238L cwSquare238G
              (by norm_num) cwSquare238L_pos cwSquare238G_pos).dimensionProduct .Z : ℕ) : ℝ) =
      2398488 * Real.log 6 := by
  rw [log_cw112SymmetricDimensionVolume
    K 6 cwSquare238L cwSquare238G
      (by norm_num) cwSquare238L_pos cwSquare238G_pos]
  norm_num [cwSquare238L, cwSquare238G]

/-- The normalized inner lower term used by the `q=6` square certificate. -/
noncomputable def cwSquare238InnerTerm : ℝ :=
  cw112SymmetricLimitLowerTerm K (cwSquare238InnerCopyBase K) cwSquare238Tau
    6 cwSquare238L cwSquare238G (by norm_num) cwSquare238L_pos cwSquare238G_pos

/-- The chosen inner lower term is strictly positive. -/
theorem cwSquare238InnerTerm_pos : 0 < cwSquare238InnerTerm K := by
  unfold cwSquare238InnerTerm
  exact cw112SymmetricLimitLowerTerm_pos K
    (cwSquare238InnerCopyBase_pos K) cwSquare238Tau
      6 cwSquare238L cwSquare238G (by norm_num) cwSquare238L_pos cwSquare238G_pos

/-- Clearing the inner normalization exposes exactly one visible-copy logarithm and one
matrix-volume logarithm.

Proof sketch: `log_cw112SymmetricLimitLowerTerm` divides their sum by three times the profile
mass.  Here that mass is `74³ = 405224`; substitute the two exact logarithm formulas above and
clear the nonzero rational denominator. -/
theorem scaled_log_cwSquare238InnerTerm :
    (3 * 405224 : ℝ) * Real.log (cwSquare238InnerTerm K) =
      (2 * 405224 * Real.log 2 +
        10952 * Real.log 74 + 394272 * Real.log (37 / 36 : ℝ) - Real.log 2) +
      (119 / 150 : ℝ) * (2398488 * Real.log 6) := by
  have h := log_cw112SymmetricLimitLowerTerm K
    (cwSquare238InnerCopyBase_pos K) cwSquare238Tau
      6 cwSquare238L cwSquare238G (by norm_num) cwSquare238L_pos cwSquare238G_pos
  rw [cw112SymmetricLeaf_profile_mass,
    log_cwSquare238InnerCopyBase,
    log_cwSquare238InnerDimensionVolume] at h
  change Real.log (cwSquare238InnerTerm K) = _ at h
  norm_num [cwSquare238L, cwSquare238G, cwSquare238Tau] at h ⊢
  linarith

/-! ## Semantic scalar comparison and exponent conclusion -/

/-- The logarithmic hypothesis required by the generic stable value theorem holds for the exact
integer profile above.

Proof sketch: expand the outer, ordinary, and normalized-inner logarithms.  After collecting the
two factor-two reserves, the right side is precisely the expression certified in
`cw238_scalar_log_inequality`; `log 64 = 6 log 2` identifies its left side. -/
theorem cwSquare238_log_sufficient :
    ((cwSquareStride cwSquare238A cwSquare238B cwSquare238C cwSquare238D : ℕ) : ℝ) *
        Real.log 64 <
      Real.log cwSquare238OuterBase +
        cwSquare238Tau *
          Real.log
            ((cwSquareOrdinaryDimensionBase 6 cwSquare238B cwSquare238C *
              cwSquareOrdinaryDimensionBase 6 cwSquare238B cwSquare238C *
              cwSquareOrdinaryDimensionBase 6 cwSquare238B cwSquare238C : ℕ) : ℝ) +
        ((3 * cwSquare238D : ℕ) : ℝ) * Real.log (cwSquare238InnerTerm K) := by
  have hlog64 : Real.log 64 = 6 * Real.log 2 := by
    rw [show (64 : ℝ) = 2 ^ 6 by norm_num, Real.log_pow]
    norm_num
  rw [cwSquare238Stride_eq, hlog64, log_cwSquare238OuterBase,
    log_cwSquare238OrdinaryVolume]
  have hinner := scaled_log_cwSquare238InnerTerm K
  norm_num [cwSquare238D, cwSquareSymmetric112Multiplicity,
    cwSquare238L, cwSquare238G] at hinner ⊢
  rw [hinner]
  convert cw238_scalar_log_inequality using 1
  all_goals norm_num [cwSquare238Tau]
  all_goals ring

/-- The stable modern square-value lower term is strictly larger than the square border-rank
budget `64 = (6+2)²`. -/
theorem cwSquare238_stable_value_gt_64 :
    (64 : ℝ) <
      cwSquareSymmetric112LimitLowerTerm K
        cwSquare238OuterBase (cwSquare238InnerCopyBase K) cwSquare238Tau
        6 cwSquare238A cwSquare238B cwSquare238C cwSquare238L cwSquare238G
        (by norm_num) cwSquare238L_pos cwSquare238G_pos := by
  unfold cwSquareSymmetric112LimitLowerTerm
  change (64 : ℝ) < cwSquareTauValueLimitLowerTerm
    cwSquare238OuterBase (cwSquare238InnerTerm K) cwSquare238Tau
      6 cwSquare238A cwSquare238B cwSquare238C cwSquare238D
  apply lt_cwSquareTauValueLimitLowerTerm_of_log_lt
  · norm_num
  · exact cwSquare238OuterBase_pos
  · exact cwSquare238InnerTerm_pos K
  · norm_num
  · norm_num [cwSquareStride, cwSquare238A, cwSquare238B, cwSquare238C,
      cwSquare238D, cwSquareSymmetric112Multiplicity, cwSquare238L, cwSquare238G]
  · exact cwSquare238_log_sufficient K

/-- **Classical Coppersmith--Winograd square bound:** over every field, the matrix-multiplication
exponent satisfies `ω < 2.38`.

Proof sketch: the preceding theorem verifies the sole scalar hypothesis of the modern symmetric
`(112)` value endpoint.  Its finite certificates are genuine polynomial degenerations of powers
of the CW square; the generic value calculus and Schönhage's asymptotic sum inequality then give
`ω < 3τ = 119/50`. -/
theorem coppersmithWinograd_square_omega_lt_238 :
    omega K < (119 / 50 : ℝ) := by
  have h := cwSquareSymmetric112_omega_lt_three_mul
    K cwSquare238Tau 6
      cwSquare238A cwSquare238B cwSquare238C cwSquare238L cwSquare238G
      (by norm_num) cwSquare238A_pos cwSquare238B_pos cwSquare238C_pos
      cwSquare238L_pos cwSquare238G_pos
      cwSquare238OuterBase_pos cwSquare238OuterBase_lt
      (cwSquare238InnerCopyBase_pos K) (cwSquare238InnerCopyBase_lt K)
      (by simpa using cwSquare238_stable_value_gt_64 K)
  norm_num [cwSquare238Tau] at h ⊢
  exact h

end

end AlgebraicComplexity.Examples
