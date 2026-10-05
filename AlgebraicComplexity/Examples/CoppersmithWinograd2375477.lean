/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinograd2375477Arithmetic
import AlgebraicComplexity.Examples.CoppersmithWinogradSquare112TauValueGrowth

/-!
# The classical Coppersmith--Winograd bound `ω < 2.375477`

This is the exact-parameter client for the modern CW-square value construction.  It sharpens the
coarser `2.38` regression without changing its tensor proof: the finite symmetric `(112)`
extraction, cyclic grouping, tau-value calculus, border-rank certificate, and Schönhage soundness
are all supplied by reusable modules.

The paper prints only rounded normalized parameters.  We use the nearby exactly feasible integral
profile

```text
q = 6,  tau = 2375477 / 3000000,
(A,B,C,D) = (148446, 7976570, 65404408, 131096512),
(L,G) = (7,247),  D = [2(L+G)]^3,
N = 637807518.
```

It normalizes to
`(a,b,c,d) ≈ (0.0002327442, 0.0125062339, 0.1025456837, 0.2055424376)`, within
the rounding precision of the optimizer reported on journal page 269.  The two strict entropy
bases retain the transparent factor-two reserves used by the regression proof.  Despite those
reserves, the sharp directed logarithm certificate has positive margin.

Primary source: Don Coppersmith and Shmuel Winograd, *Matrix Multiplication via Arithmetic
Progressions*, Journal of Symbolic Computation 9(3), 251--280 (1990), pp. 267--272,
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

/-- Value parameter `tau = 2375477/3000000`, so `3 tau = 2.375477`. -/
def cwSquare2375477Tau : ℝ := 2375477 / 3000000

/-- Multiplicity of one address in the outer `004` orbit. -/
def cwSquare2375477A : ℕ := 148446

/-- Multiplicity of one address in the outer `013` orbit. -/
def cwSquare2375477B : ℕ := 7976570

/-- Multiplicity of one address in the outer `022` orbit. -/
def cwSquare2375477C : ℕ := 65404408

/-- Light-letter multiplicity in the exceptional `(112)` leaf. -/
def cwSquare2375477L : ℕ := 7

/-- Heavy-letter multiplicity in the exceptional `(112)` leaf. -/
def cwSquare2375477G : ℕ := 247

/-- Exceptional-orbit multiplicity forced by the cyclic `(112)` profile. -/
abbrev cwSquare2375477D : ℕ :=
  cwSquareSymmetric112Multiplicity cwSquare2375477L cwSquare2375477G

/-- The exceptional multiplicity is exactly `508^3 = 131096512`. -/
theorem cwSquare2375477D_eq : cwSquare2375477D = 131096512 := by
  norm_num [cwSquare2375477D, cwSquareSymmetric112Multiplicity,
    cwSquare2375477L, cwSquare2375477G]

/-- The complete outer profile has total mass `637807518`. -/
theorem cwSquare2375477Stride_eq :
    cwSquareStride cwSquare2375477A cwSquare2375477B
      cwSquare2375477C cwSquare2375477D = 637807518 := by
  norm_num [cwSquare2375477A, cwSquare2375477B, cwSquare2375477C,
    cwSquare2375477D, cwSquareSymmetric112Multiplicity,
    cwSquare2375477L, cwSquare2375477G, cwSquareStride]

private theorem cwSquare2375477A_pos : 0 < cwSquare2375477A := by
  norm_num [cwSquare2375477A]

private theorem cwSquare2375477B_pos : 0 < cwSquare2375477B := by
  norm_num [cwSquare2375477B]

private theorem cwSquare2375477C_pos : 0 < cwSquare2375477C := by
  norm_num [cwSquare2375477C]

private theorem cwSquare2375477L_pos : 0 < cwSquare2375477L := by
  norm_num [cwSquare2375477L]

private theorem cwSquare2375477G_pos : 0 < cwSquare2375477G := by
  norm_num [cwSquare2375477G]

/-- Strict outer copy base, with a factor-two reserve below the exact entropy base. -/
noncomputable def cwSquare2375477OuterBase : ℝ :=
  cwSquareOuterEntropyBase cwSquare2375477A cwSquare2375477B
    cwSquare2375477C cwSquare2375477D / 2

/-- Strict inner copy base, with the same factor-two reserve. -/
noncomputable def cwSquare2375477InnerCopyBase : ℝ :=
  cw112SymmetricMarginalEntropyBase K 6 cwSquare2375477L cwSquare2375477G
    (by norm_num) cwSquare2375477L_pos cwSquare2375477G_pos / 2

/-- The reserved outer survivor base remains positive. -/
theorem cwSquare2375477OuterBase_pos : 0 < cwSquare2375477OuterBase := by
  unfold cwSquare2375477OuterBase cwSquareOuterEntropyBase
  exact div_pos
    (WordType.proportionalEntropyBase_pos_zeroSafe
      (cwSquareBaseMarginal cwSquare2375477A cwSquare2375477B
        cwSquare2375477C cwSquare2375477D))
    (by norm_num)

/-- The reserved outer base is strictly below the exact marginal-entropy base. -/
theorem cwSquare2375477OuterBase_lt :
    cwSquare2375477OuterBase <
      cwSquareOuterEntropyBase cwSquare2375477A cwSquare2375477B
        cwSquare2375477C cwSquare2375477D := by
  unfold cwSquare2375477OuterBase
  exact div_lt_self
    (by
      unfold cwSquareOuterEntropyBase
      exact WordType.proportionalEntropyBase_pos_zeroSafe _)
    (by norm_num)

/-- The reserved inner visible-copy base remains positive. -/
theorem cwSquare2375477InnerCopyBase_pos : 0 < cwSquare2375477InnerCopyBase K := by
  unfold cwSquare2375477InnerCopyBase
  exact div_pos
    (cw112SymmetricMarginalEntropyBase_pos
      K 6 cwSquare2375477L cwSquare2375477G
        (by norm_num) cwSquare2375477L_pos cwSquare2375477G_pos)
    (by norm_num)

/-- The reserved inner base is strictly below the exact visible marginal-entropy base. -/
theorem cwSquare2375477InnerCopyBase_lt :
    cwSquare2375477InnerCopyBase K <
      cw112SymmetricMarginalEntropyBase K 6 cwSquare2375477L cwSquare2375477G
        (by norm_num) cwSquare2375477L_pos cwSquare2375477G_pos := by
  unfold cwSquare2375477InnerCopyBase
  exact div_lt_self
    (cw112SymmetricMarginalEntropyBase_pos
      K 6 cwSquare2375477L cwSquare2375477G
        (by norm_num) cwSquare2375477L_pos cwSquare2375477G_pos)
    (by norm_num)

/-! ## Exact logarithmic identities -/

/-- Exact logarithm of the five-coordinate outer entropy base. -/
theorem log_cwSquare2375477OuterEntropyBase :
    Real.log (cwSquareOuterEntropyBase cwSquare2375477A cwSquare2375477B
      cwSquare2375477C cwSquare2375477D) =
      81654440 * Real.log (637807518 / 81654440 : ℝ) +
      278146164 * Real.log (637807518 / 278146164 : ℝ) +
      261905328 * Real.log (637807518 / 261905328 : ℝ) +
      15953140 * Real.log (637807518 / 15953140 : ℝ) +
      148446 * Real.log (637807518 / 148446 : ℝ) := by
  rw [log_cwSquareOuterEntropyBase
    cwSquare2375477A_pos cwSquare2375477B_pos
    cwSquare2375477C_pos (cwSquareSymmetric112Multiplicity_pos cwSquare2375477L_pos)]
  rw [show (Finset.univ : Finset (Fin 5)) = {0, 1, 2, 3, 4} by decide,
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  norm_num [cwSquareBaseMarginal, cwSquareMarginalType, cwSquareStride,
    cwSquare2375477A, cwSquare2375477B, cwSquare2375477C,
    cwSquare2375477D, cwSquareSymmetric112Multiplicity,
    cwSquare2375477L, cwSquare2375477G]
  ring

/-- Exact logarithm of the symmetric inner entropy base at `(L,G)=(7,247)`. -/
theorem log_cwSquare2375477InnerEntropyBase :
    Real.log
        (cw112SymmetricMarginalEntropyBase K 6 cwSquare2375477L cwSquare2375477G
          (by norm_num) cwSquare2375477L_pos cwSquare2375477G_pos) =
      2 * 131096512 * Real.log 2 +
        3612896 * Real.log (508 / 7 : ℝ) +
        127483616 * Real.log (254 / 247 : ℝ) := by
  rw [log_cw112SymmetricMarginalEntropyBase
    K 6 cwSquare2375477L cwSquare2375477G
      (by norm_num) cwSquare2375477L_pos cwSquare2375477G_pos]
  norm_num [cwSquare2375477L, cwSquare2375477G]

/-- Exact logarithm of the strict outer survivor base. -/
theorem log_cwSquare2375477OuterBase :
    Real.log cwSquare2375477OuterBase =
      81654440 * Real.log (637807518 / 81654440 : ℝ) +
      278146164 * Real.log (637807518 / 278146164 : ℝ) +
      261905328 * Real.log (637807518 / 261905328 : ℝ) +
      15953140 * Real.log (637807518 / 15953140 : ℝ) +
      148446 * Real.log (637807518 / 148446 : ℝ) - Real.log 2 := by
  have houter : 0 < cwSquareOuterEntropyBase cwSquare2375477A cwSquare2375477B
      cwSquare2375477C cwSquare2375477D := by
    unfold cwSquareOuterEntropyBase
    exact WordType.proportionalEntropyBase_pos_zeroSafe _
  rw [cwSquare2375477OuterBase,
    Real.log_div houter.ne' (by norm_num : (2 : ℝ) ≠ 0),
    log_cwSquare2375477OuterEntropyBase]

/-- Exact logarithm of the strict inner visible-copy base. -/
theorem log_cwSquare2375477InnerCopyBase :
    Real.log (cwSquare2375477InnerCopyBase K) =
      2 * 131096512 * Real.log 2 +
        3612896 * Real.log (508 / 7 : ℝ) +
        127483616 * Real.log (254 / 247 : ℝ) - Real.log 2 := by
  rw [cwSquare2375477InnerCopyBase,
    Real.log_div
      (cw112SymmetricMarginalEntropyBase_pos
        K 6 cwSquare2375477L cwSquare2375477G
          (by norm_num) cwSquare2375477L_pos cwSquare2375477G_pos).ne'
      (by norm_num : (2 : ℝ) ≠ 0),
    log_cwSquare2375477InnerEntropyBase]

/-- Ordinary square constituents contribute `12^(6B)` and `38^(3C)` in cube volume. -/
theorem log_cwSquare2375477OrdinaryVolume :
    Real.log
        ((cwSquareOrdinaryDimensionBase 6 cwSquare2375477B cwSquare2375477C *
          cwSquareOrdinaryDimensionBase 6 cwSquare2375477B cwSquare2375477C *
          cwSquareOrdinaryDimensionBase 6 cwSquare2375477B cwSquare2375477C : ℕ) : ℝ) =
      47859420 * Real.log 12 + 196213224 * Real.log 38 := by
  rw [log_cwSquareOrdinaryVolume 6 cwSquare2375477B cwSquare2375477C (by norm_num)]
  norm_num [cwSquare2375477B, cwSquare2375477C]

/-- The symmetric inner `(112)` leaf has matrix-volume logarithm `775740384 log 6`. -/
theorem log_cwSquare2375477InnerDimensionVolume :
    Real.log
        (((cw112SymmetricLeaf K 6 cwSquare2375477L cwSquare2375477G
              (by norm_num) cwSquare2375477L_pos cwSquare2375477G_pos).dimensionProduct .X *
          (cw112SymmetricLeaf K 6 cwSquare2375477L cwSquare2375477G
              (by norm_num) cwSquare2375477L_pos cwSquare2375477G_pos).dimensionProduct .Y *
          (cw112SymmetricLeaf K 6 cwSquare2375477L cwSquare2375477G
              (by norm_num) cwSquare2375477L_pos cwSquare2375477G_pos).dimensionProduct .Z : ℕ) :
            ℝ) =
      775740384 * Real.log 6 := by
  rw [log_cw112SymmetricDimensionVolume
    K 6 cwSquare2375477L cwSquare2375477G
      (by norm_num) cwSquare2375477L_pos cwSquare2375477G_pos]
  norm_num [cwSquare2375477L, cwSquare2375477G]

/-- Normalized inner lower term used by the sharp `q=6` square certificate. -/
noncomputable def cwSquare2375477InnerTerm : ℝ :=
  cw112SymmetricLimitLowerTerm K (cwSquare2375477InnerCopyBase K) cwSquare2375477Tau
    6 cwSquare2375477L cwSquare2375477G
      (by norm_num) cwSquare2375477L_pos cwSquare2375477G_pos

/-- The chosen inner lower term is strictly positive. -/
theorem cwSquare2375477InnerTerm_pos : 0 < cwSquare2375477InnerTerm K := by
  unfold cwSquare2375477InnerTerm
  exact cw112SymmetricLimitLowerTerm_pos K
    (cwSquare2375477InnerCopyBase_pos K) cwSquare2375477Tau
      6 cwSquare2375477L cwSquare2375477G
        (by norm_num) cwSquare2375477L_pos cwSquare2375477G_pos

/-- Clearing the inner normalization exposes one visible-copy logarithm and one matrix-volume
logarithm.

Proof sketch: specialize `log_cw112SymmetricLimitLowerTerm`, substitute the exact entropy and
dimension identities, and clear the nonzero profile-mass denominator `3 * 131096512`. -/
theorem scaled_log_cwSquare2375477InnerTerm :
    (3 * 131096512 : ℝ) * Real.log (cwSquare2375477InnerTerm K) =
      (2 * 131096512 * Real.log 2 +
        3612896 * Real.log (508 / 7 : ℝ) +
        127483616 * Real.log (254 / 247 : ℝ) - Real.log 2) +
      (2375477 / 3000000 : ℝ) * (775740384 * Real.log 6) := by
  have h := log_cw112SymmetricLimitLowerTerm K
    (cwSquare2375477InnerCopyBase_pos K) cwSquare2375477Tau
      6 cwSquare2375477L cwSquare2375477G
        (by norm_num) cwSquare2375477L_pos cwSquare2375477G_pos
  rw [cw112SymmetricLeaf_profile_mass,
    log_cwSquare2375477InnerCopyBase,
    log_cwSquare2375477InnerDimensionVolume] at h
  change Real.log (cwSquare2375477InnerTerm K) = _ at h
  norm_num [cwSquare2375477L, cwSquare2375477G, cwSquare2375477Tau] at h ⊢
  linarith

/-! ## Semantic scalar comparison and exponent conclusion -/

/-- The logarithmic hypothesis of the generic stable-value theorem holds for the exact profile.

Proof sketch: expand the outer, ordinary, and normalized-inner logarithms.  The two strictness
reserves together subtract `2 log 2`; after collecting terms, the goal is exactly
`cw2375477_scalar_log_inequality`. -/
theorem cwSquare2375477_log_sufficient :
    ((cwSquareStride cwSquare2375477A cwSquare2375477B
        cwSquare2375477C cwSquare2375477D : ℕ) : ℝ) * Real.log 64 <
      Real.log cwSquare2375477OuterBase +
        cwSquare2375477Tau *
          Real.log
            ((cwSquareOrdinaryDimensionBase 6 cwSquare2375477B cwSquare2375477C *
              cwSquareOrdinaryDimensionBase 6 cwSquare2375477B cwSquare2375477C *
              cwSquareOrdinaryDimensionBase 6 cwSquare2375477B cwSquare2375477C : ℕ) : ℝ) +
        ((3 * cwSquare2375477D : ℕ) : ℝ) *
          Real.log (cwSquare2375477InnerTerm K) := by
  have hlog64 : Real.log 64 = 6 * Real.log 2 := by
    rw [show (64 : ℝ) = 2 ^ 6 by norm_num, Real.log_pow]
    norm_num
  rw [cwSquare2375477Stride_eq, hlog64, log_cwSquare2375477OuterBase,
    log_cwSquare2375477OrdinaryVolume]
  have hinner := scaled_log_cwSquare2375477InnerTerm K
  norm_num [cwSquare2375477D, cwSquareSymmetric112Multiplicity,
    cwSquare2375477L, cwSquare2375477G] at hinner ⊢
  rw [hinner]
  convert cw2375477_scalar_log_inequality using 1
  all_goals norm_num [cwSquare2375477Tau]
  all_goals ring

/-- The stable modern square-value lower term exceeds the square border-rank budget `64`. -/
theorem cwSquare2375477_stable_value_gt_64 :
    (64 : ℝ) <
      cwSquareSymmetric112LimitLowerTerm K
        cwSquare2375477OuterBase (cwSquare2375477InnerCopyBase K) cwSquare2375477Tau
        6 cwSquare2375477A cwSquare2375477B cwSquare2375477C
          cwSquare2375477L cwSquare2375477G
        (by norm_num) cwSquare2375477L_pos cwSquare2375477G_pos := by
  unfold cwSquareSymmetric112LimitLowerTerm
  change (64 : ℝ) < cwSquareTauValueLimitLowerTerm
    cwSquare2375477OuterBase (cwSquare2375477InnerTerm K) cwSquare2375477Tau
      6 cwSquare2375477A cwSquare2375477B cwSquare2375477C cwSquare2375477D
  apply lt_cwSquareTauValueLimitLowerTerm_of_log_lt
  · norm_num
  · exact cwSquare2375477OuterBase_pos
  · exact cwSquare2375477InnerTerm_pos K
  · norm_num
  · norm_num [cwSquareStride, cwSquare2375477A, cwSquare2375477B,
      cwSquare2375477C, cwSquare2375477D, cwSquareSymmetric112Multiplicity,
      cwSquare2375477L, cwSquare2375477G]
  · exact cwSquare2375477_log_sufficient K

/-- **Coppersmith--Winograd's classical tensor-square bound:** over every field,
`omega < 2.375477`.

Proof sketch: the preceding exact arithmetic verifies the strict value inequality for the finite
integral profile.  The reusable symmetric `(112)` construction supplies genuine polynomial
degenerations of powers of the CW square; the tau-value soundness theorem and Schönhage's
asymptotic sum inequality then give `omega < 3 tau = 2375477/1000000`. -/
theorem coppersmithWinograd_square_omega_lt_2375477 :
    omega K < (2375477 / 1000000 : ℝ) := by
  have h := cwSquareSymmetric112_omega_lt_three_mul
    K cwSquare2375477Tau 6
      cwSquare2375477A cwSquare2375477B cwSquare2375477C
      cwSquare2375477L cwSquare2375477G
      (by norm_num) cwSquare2375477A_pos cwSquare2375477B_pos
      cwSquare2375477C_pos cwSquare2375477L_pos cwSquare2375477G_pos
      cwSquare2375477OuterBase_pos cwSquare2375477OuterBase_lt
      (cwSquare2375477InnerCopyBase_pos K) (cwSquare2375477InnerCopyBase_lt K)
      (by simpa using cwSquare2375477_stable_value_gt_64 K)
  norm_num [cwSquare2375477Tau] at h ⊢
  exact h

end

end AlgebraicComplexity.Examples
