/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinogradSquareOrdinarySymmetry
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoGlobalArithmetic
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoCounting
import AlgebraicComplexity.MatrixMultiplication.TauValueDirectSum
import AlgebraicComplexity.Tensor.PermutationCoherence

/-!
# The fifteen constituent values of the Duan--Wu--Zhou level-two endpoint

`Examples/DuanWuZhouLevelTwoGlobalArithmetic.lean` carries `dwz63LogVal`, the logarithm of
[DuanWuZhou2022] section 6.3's leaf value rate

`alphabar_val = prod_{i+j+k=4} V(T_{i,j,k}, alphatilde_{i,j,k}) ^ alpha(i,j,k)`,

in *certificate normal form*: a single linear combination of the nine logarithm atoms
`log 2`, `log 3`, `log 19`, `log (10^8/3477403)`, `log (5*10^7/46522597)`,
`log (10^7/9995797)`, `log (2*10^7/4203)`, `log (25*10^8/2430977783)` and
`log (5*10^9/69022217)`.  Nothing in that file records *which component contributes which
term*.  This module restores the factorization and discharges the twelve factors that are
plain matrix-multiplication values.

## The fifteen factors

With `q = 6`, `tau = dwz63Tau`, `a = dwz63A`, `b = dwz63B` and `beta = dwz63Beta`, section 6.3
assigns

| components | `alpha` (over `10^8`) | `V` |
| - | - | - |
| `(0,0,4) (0,4,0) (4,0,0)` | `20860 24731 24731` | `1` |
| `(0,1,3) (0,3,1) (1,0,3) (1,3,0) (3,0,1) (3,1,0)` | `1211153 1333318 1211153 1251758 1333318 1251758` | `(2q)^tau` |
| `(2,2,0)` | `10045791` | `(q^2+2)^tau` |
| `(0,2,2) (2,0,2)` | `10366945 10366945` | the `a`-split value |
| `(1,1,2)` | `20088623` | the `b`-split value |
| `(1,2,1) (2,1,1)` | `20734458 20734458` | `lem:non-rot-values` (d) at `beta` |

The three split parameters are the `mu = L / (2(L+G))` of the committed cyclic `(112)` profile
`(L,L,G,G)`: `a = 3477403/10^8` (no `(L,G)` --- it is a `tau`-weighted Gibbs split, not a
`(112)` one), `b = 21015/10^8` at `(L,G) = (4203, 9995797)` and
`beta = 69022217/(5*10^9)` at `(L,G) = (69022217, 2430977783)`.  Reading the atoms off:
`log (1/(1-2b)) = log ((L+G)/G)` and `log (1/b) = log (2(L+G)/L)`, and likewise for `beta`.

`dwz63_logVal_eq` below is the exact identity that these six numbers, weighted by `alpha`,
reproduce `dwz63LogVal`.

## What is discharged here

Twelve of the fifteen are *non-rotational* values of matrix-multiplication tensors and are
proved outright, reusing the exact constituent restrictions of
`Examples/CoppersmithWinogradSquareOrdinarySymmetry.lean`:

* the three corners restrict to `<1,1,1>`, value `1`;
* the six `(0,1,3)`-type components restrict to an oriented `<1,1,2q>`, value `(2q)^tau = 12^tau`;
* `(2,2,0)` restricts to `<1,q^2+2,1>`, value `(q^2+2)^tau = 38^tau`;
* `(0,2,2)` and `(2,0,2)` restrict to an oriented `<1,1,q^2+2>` as well, and section 6.3's
  `a`-split value is *below* `(q^2+2)^tau` because `a = 0.03477403` is not the maximizer
  `1/(q^2+2)`.  The comparison is `dwz63_logVal022_le_logVal220`, a two-term Gibbs inequality
  (`Real.log_le_sub_one_of_pos` against the weights `(1, q^2, 1)`); it needs **no** logarithm
  enclosure and is exact.

The remaining three --- `(1,1,2)`, `(1,2,1)` and `(2,1,1)` --- are the orbit of the one
component that is *not* a matrix-multiplication tensor ([DuanWuZhou2022], footnote to
`remark:alpha_sym`).  Their factors exceed every non-rotational weight the constituent alone
carries, so they enter here as hypotheses; see the module note `Exceptional orbit` below.

Primary source: Ran Duan, Hongxun Wu and Renfei Zhou, *Faster Matrix Multiplication via
Asymmetric Hashing*, arXiv:2210.10173, `global_value.tex` section 6.3 and `lem:non-rot-values`.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor

universe u v

noncomputable section

/-! ## Elementary logarithm identities

The three composite constants of the value table, resolved into the atoms `log 2`, `log 3` and
`log 19` that `dwz63LogVal` is written over. -/

/-- `log 12 = 2 log 2 + log 3`; `12 = 2q` is the `(0,1,3)` dimension at `q = 6`. -/
theorem dwz63_log_twelve : Real.log 12 = 2 * Real.log 2 + Real.log 3 := by
  rw [show (12 : ℝ) = 2 ^ 2 * 3 by norm_num, Real.log_mul (by positivity) (by norm_num),
    Real.log_pow]
  push_cast
  ring

/-- `log 36 = 2 log 2 + 2 log 3`; `36 = q^2` at `q = 6`. -/
theorem dwz63_log_thirtysix : Real.log 36 = 2 * Real.log 2 + 2 * Real.log 3 := by
  rw [show (36 : ℝ) = 2 ^ 2 * 3 ^ 2 by norm_num, Real.log_mul (by positivity) (by positivity),
    Real.log_pow, Real.log_pow]
  push_cast
  ring

/-- `log 38 = log 2 + log 19`; `38 = q^2 + 2` at `q = 6`. -/
theorem dwz63_log_thirtyeight : Real.log 38 = Real.log 2 + Real.log 19 := by
  rw [show (38 : ℝ) = 2 * 19 by norm_num, Real.log_mul (by norm_num) (by norm_num)]

/-! ## A weighted extraction from a single matrix-multiplication tensor

`HasTauWeight` is stated for a family of rectangular targets; the one-element family recovers the
familiar `(abc)^tau`.  This is the `HasTauWeight` shadow of
`TauValueCertificate.matrixMultiplication`, obtained without going through the certificate's
projections. -/

/-- **`<a,b,c>` carries the weight `(abc)^tau`.** -/
theorem hasTauWeight_matrixMultiplication (K : Type u) [CommSemiring K] {a b c : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (τ : ℝ) :
    HasTauWeight K (matrixMultiplication (K := K) a b c) τ (((a * b * c : ℕ) : ℝ) ^ τ) := by
  refine ⟨1, fun _ ↦ a, fun _ ↦ b, fun _ ↦ c, fun _ ↦ ha, fun _ ↦ hb, fun _ ↦ hc, ?_, ?_⟩
  · refine PolynomialDegenerates.of_restricts ?_
    exact (Tensor.Isomorphic.indexedDirectSum_unique (ι := Fin 1)
      (matrixMultiplication (K := K) a b c)).symm.restricts
  · refine le_of_eq ?_
    simp [matrixMultiplicationVolumePowerSum, matrixMultiplicationVolume]

/-! ## The six distinct logarithmic factors

Each definition is the logarithm of one entry of the section 6.3 value table, written over the
same nine atoms as `dwz63LogVal` so that `dwz63_logVal_eq` is a pure ring identity. -/

/-- `log V(T_{0,0,4}) = 0`: the corner components are scalar multiplications, `V = 1`
(`lem:non-rot-values` (a)). -/
def dwz63LogVal004 : ℝ := 0

/-- `log V(T_{0,1,3}) = tau log (2q)`, at `q = 6` the atom combination `tau (2 log 2 + log 3)`
(`lem:non-rot-values` (b)). -/
def dwz63LogVal013 : ℝ := dwz63Tau * (2 * Real.log 2 + Real.log 3)

/-- `log V(T_{2,2,0}) = tau log (q^2+2)`, at `q = 6` the atom combination
`tau (log 2 + log 19)` (`lem:non-rot-values` (c)). -/
def dwz63LogVal220 : ℝ := dwz63Tau * (Real.log 2 + Real.log 19)

/-- `log V(T_{0,2,2}, alphatilde)` at the split `(a, 1-2a, a)`: section 6.3's

`V = (q^(2(1-2a)) / (a^(2a) (1-2a)^(1-2a)))^tau`,

whose logarithm is `tau (2(1-2a) log q + 2a log (1/a) + (1-2a) log (1/(1-2a)))`.  The two
non-elementary atoms are `log (1/a) = log (10^8/3477403)` and
`log (1/(1-2a)) = log (5*10^7/46522597)`. -/
def dwz63LogVal022 : ℝ :=
  dwz63Tau * (2 * (1 - 2 * dwz63A) * (Real.log 2 + Real.log 3)
    + 2 * dwz63A * Real.log (100000000 / 3477403)
    + (1 - 2 * dwz63A) * Real.log (50000000 / 46522597))

/-- `log V(T_{1,1,2}, alphatilde)` at the split `(b, 1-2b, b)`: section 6.3's

`V = (4 / ((1-2b)^(1-2b) b^(2b)))^(1/3) q^((2-2b) tau)`.

The `1/3` is the three-symmetrization of `lem:non-rot-values` (d); the atoms are
`log (1/(1-2b)) = log (10^7/9995797)` and `log (1/b) = log (2*10^7/4203)`. -/
def dwz63LogVal112 : ℝ :=
  (2 * Real.log 2 + (1 - 2 * dwz63B) * Real.log (10000000 / 9995797)
      + 2 * dwz63B * Real.log (20000000 / 4203)) / 3
    + (2 - 2 * dwz63B) * dwz63Tau * (Real.log 2 + Real.log 3)

/-- `log V(T_{1,2,1}, alphatilde) = log V(T_{2,1,1}, alphatilde)`: the same `lem:non-rot-values`
(d) formula as `(1,1,2)`, evaluated at the *free* rational `beta = dwz63Beta` instead of `b`.
The atoms are `log (1/(1-2 beta)) = log (25*10^8/2430977783)` and
`log (1/beta) = log (5*10^9/69022217)`. -/
def dwz63LogVal121 : ℝ :=
  (2 * Real.log 2 + (1 - 2 * dwz63Beta) * Real.log (2500000000 / 2430977783)
      + 2 * dwz63Beta * Real.log (5000000000 / 69022217)) / 3
    + (2 - 2 * dwz63Beta) * dwz63Tau * (Real.log 2 + Real.log 3)

/-- The corner value `V(T_{0,0,4}) = 1`. -/
def dwz63Val004 : ℝ := Real.exp dwz63LogVal004

/-- The `(0,1,3)`-type value `V = (2q)^tau`. -/
def dwz63Val013 : ℝ := Real.exp dwz63LogVal013

/-- The `(2,2,0)` value `V = (q^2+2)^tau`. -/
def dwz63Val220 : ℝ := Real.exp dwz63LogVal220

/-- The `a`-split value of `(0,2,2)` and `(2,0,2)`. -/
def dwz63Val022 : ℝ := Real.exp dwz63LogVal022

/-- The `b`-split value of `(1,1,2)`. -/
def dwz63Val112 : ℝ := Real.exp dwz63LogVal112

/-- The `beta`-split value of `(1,2,1)` and `(2,1,1)`. -/
def dwz63Val121 : ℝ := Real.exp dwz63LogVal121

/-! ## The factorization of `dwz63LogVal` -/

/-- **`dwz63LogVal` is the `alpha`-weighted sum of the fifteen component logarithms.**

Grouping the fifteen cells of `table:result-2nd` by their value, the masses are
`70322` (corners), `7592458` (`(0,1,3)` type), `20733890` (`(0,2,2)` type), `20088623`
(`(1,1,2)`), `41468916` (`(1,2,1)` type) and `10045791` (`(2,2,0)`), summing to `10^8`.

This is the identity that turns the certificate normal form of
`Examples/DuanWuZhouLevelTwoGlobalArithmetic.lean` back into a product of per-constituent
values.  Both sides are linear combinations of the same nine logarithm atoms, so `ring`
verifies it exactly. -/
theorem dwz63_logVal_eq :
    dwz63LogVal =
      70322 / 100000000 * dwz63LogVal004
        + 7592458 / 100000000 * dwz63LogVal013
        + 20733890 / 100000000 * dwz63LogVal022
        + 20088623 / 100000000 * dwz63LogVal112
        + 41468916 / 100000000 * dwz63LogVal121
        + 10045791 / 100000000 * dwz63LogVal220 := by
  simp only [dwz63LogVal, dwz63LogVal004, dwz63LogVal013, dwz63LogVal022, dwz63LogVal112,
    dwz63LogVal121, dwz63LogVal220, dwz63Tau, dwz63A, dwz63B, dwz63Beta]
  ring

/-! ## The `(0,2,2)` comparison

Section 6.3 evaluates the `(0,2,2)` restricted-splitting value at `a = 0.03477403`, which is
*not* the maximizer `1/(q^2+2) = 1/38` of `lem:non-rot-values` (c).  The value it obtains is
therefore strictly below `(q^2+2)^tau`, and the plain `<1,1,q^2+2>` restriction of the
constituent already carries it.

The comparison is Gibbs' inequality for the three-point distribution `(a, 1-2a, a)` against the
weights `(1, q^2, 1)`, in the elementary form `log x <= x - 1`. -/

/-- **The `a`-split logarithm is below `log (q^2+2)`.**

`2(1-2a) log 6 + 2a log (1/a) + (1-2a) log (1/(1-2a)) <= log 38`, the `tau`-free content of the
`(0,2,2)` comparison.  Proof: apply `log x <= x - 1` at `x = 1/(38a)` with weight `2a` and at
`x = 36/(38(1-2a))` with weight `1-2a`; the two right-hand sides cancel to
`2/38 + 36/38 - 1 = 0`. -/
theorem dwz63_split022_le_log_thirtyeight :
    2 * (1 - 2 * dwz63A) * (Real.log 2 + Real.log 3)
        + 2 * dwz63A * Real.log (100000000 / 3477403)
        + (1 - 2 * dwz63A) * Real.log (50000000 / 46522597)
      ≤ Real.log 2 + Real.log 19 := by
  have h1 := Real.log_le_sub_one_of_pos
    (show (0 : ℝ) < 100000000 / 3477403 / 38 by norm_num)
  rw [Real.log_div (by norm_num) (by norm_num), dwz63_log_thirtyeight] at h1
  have h2 := Real.log_le_sub_one_of_pos
    (show (0 : ℝ) < 36 * (50000000 / 46522597) / 38 by norm_num)
  rw [Real.log_div (by norm_num) (by norm_num),
    Real.log_mul (by norm_num) (by norm_num), dwz63_log_thirtysix,
    dwz63_log_thirtyeight] at h2
  simp only [dwz63A]
  linarith

/-- **`log V(T_{0,2,2}, alphatilde) <= log V(T_{2,2,0})`.** -/
theorem dwz63_logVal022_le_logVal220 : dwz63LogVal022 ≤ dwz63LogVal220 := by
  have hτ : (0 : ℝ) ≤ dwz63Tau := by norm_num [dwz63Tau]
  simpa only [dwz63LogVal022, dwz63LogVal220] using
    mul_le_mul_of_nonneg_left dwz63_split022_le_log_thirtyeight hτ

/-- **`V(T_{0,2,2}, alphatilde) <= V(T_{2,2,0}) = (q^2+2)^tau`.** -/
theorem dwz63_val022_le_val220 : dwz63Val022 ≤ dwz63Val220 :=
  Real.exp_le_exp.mpr dwz63_logVal022_le_logVal220

/-! ## Closed forms of the three elementary values -/

/-- The corner value is `1`. -/
@[simp] theorem dwz63Val004_eq_one : dwz63Val004 = 1 := by
  simp [dwz63Val004, dwz63LogVal004]

/-- The `(0,1,3)`-type value is `(2q)^tau = 12^tau`. -/
theorem dwz63Val013_eq : dwz63Val013 = (12 : ℝ) ^ dwz63Tau := by
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 12), dwz63_log_twelve]
  unfold dwz63Val013 dwz63LogVal013
  congr 1
  ring

/-- The `(2,2,0)` value is `(q^2+2)^tau = 38^tau`. -/
theorem dwz63Val220_eq : dwz63Val220 = (38 : ℝ) ^ dwz63Tau := by
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 38), dwz63_log_thirtyeight]
  unfold dwz63Val220 dwz63LogVal220
  congr 1
  ring

/-! ## The twelve ordinary constituent weights

Each is the exact oriented matrix-multiplication restriction of
`Examples/CoppersmithWinogradSquareOrdinarySymmetry.lean` composed with
`hasTauWeight_matrixMultiplication`.  The `dwz63Q` volumes are `1 * 1 * 1 = 1`,
`1 * 1 * 12 = 12` (in each of its three orientations) and `1 * 38 * 1 = 38` (likewise). -/

section Ordinary

variable (K : Type u) [CommRing K]

/-- Value `1` on the `(0,0,4)` constituent. -/
theorem dwz63_hasTauWeight_004 :
    HasTauWeight K ((cwSquarePartitionedTensor K dwz63Q).constituent cwSquare004)
      dwz63Tau dwz63Val004 := by
  refine HasTauWeight.of_restricts (cwSquareConstituent_004_restricts K dwz63Q) ?_
  have h := hasTauWeight_matrixMultiplication (K := K) (a := 1) (b := 1) (c := 1)
    Nat.one_pos Nat.one_pos Nat.one_pos dwz63Tau
  simpa using h

/-- Value `1` on the `(4,0,0)` constituent. -/
theorem dwz63_hasTauWeight_400 :
    HasTauWeight K ((cwSquarePartitionedTensor K dwz63Q).constituent cwSquare400)
      dwz63Tau dwz63Val004 := by
  refine HasTauWeight.of_restricts (cwSquareConstituent_400_restricts K dwz63Q) ?_
  have h := hasTauWeight_matrixMultiplication (K := K) (a := 1) (b := 1) (c := 1)
    Nat.one_pos Nat.one_pos Nat.one_pos dwz63Tau
  simpa using h

/-- Value `1` on the `(0,4,0)` constituent. -/
theorem dwz63_hasTauWeight_040 :
    HasTauWeight K ((cwSquarePartitionedTensor K dwz63Q).constituent cwSquare040)
      dwz63Tau dwz63Val004 := by
  refine HasTauWeight.of_restricts (cwSquareConstituent_040_restricts K dwz63Q) ?_
  have h := hasTauWeight_matrixMultiplication (K := K) (a := 1) (b := 1) (c := 1)
    Nat.one_pos Nat.one_pos Nat.one_pos dwz63Tau
  simpa using h

/-- Value `(2q)^tau` on the `(0,1,3)` constituent. -/
theorem dwz63_hasTauWeight_013 :
    HasTauWeight K ((cwSquarePartitionedTensor K dwz63Q).constituent cwSquare013)
      dwz63Tau dwz63Val013 := by
  refine HasTauWeight.of_restricts (cwSquareConstituent_013_restricts K dwz63Q) ?_
  have h := hasTauWeight_matrixMultiplication (K := K) (a := 1) (b := 1) (c := 2 * dwz63Q)
    Nat.one_pos Nat.one_pos (by norm_num [dwz63Q]) dwz63Tau
  rw [show ((1 * 1 * (2 * dwz63Q) : ℕ) : ℝ) = 12 by norm_num [dwz63Q]] at h
  rwa [dwz63Val013_eq]

/-- Value `(2q)^tau` on the `(0,3,1)` constituent. -/
theorem dwz63_hasTauWeight_031 :
    HasTauWeight K ((cwSquarePartitionedTensor K dwz63Q).constituent cwSquare031)
      dwz63Tau dwz63Val013 := by
  refine HasTauWeight.of_restricts (cwSquareConstituent_031_restricts K dwz63Q) ?_
  have h := hasTauWeight_matrixMultiplication (K := K) (a := 1) (b := 1) (c := 2 * dwz63Q)
    Nat.one_pos Nat.one_pos (by norm_num [dwz63Q]) dwz63Tau
  rw [show ((1 * 1 * (2 * dwz63Q) : ℕ) : ℝ) = 12 by norm_num [dwz63Q]] at h
  rwa [dwz63Val013_eq]

/-- Value `(2q)^tau` on the `(3,0,1)` constituent. -/
theorem dwz63_hasTauWeight_301 :
    HasTauWeight K ((cwSquarePartitionedTensor K dwz63Q).constituent cwSquare301)
      dwz63Tau dwz63Val013 := by
  refine HasTauWeight.of_restricts (cwSquareConstituent_301_restricts K dwz63Q) ?_
  have h := hasTauWeight_matrixMultiplication (K := K) (a := 2 * dwz63Q) (b := 1) (c := 1)
    (by norm_num [dwz63Q]) Nat.one_pos Nat.one_pos dwz63Tau
  rw [show (((2 * dwz63Q) * 1 * 1 : ℕ) : ℝ) = 12 by norm_num [dwz63Q]] at h
  rwa [dwz63Val013_eq]

/-- Value `(2q)^tau` on the `(1,0,3)` constituent. -/
theorem dwz63_hasTauWeight_103 :
    HasTauWeight K ((cwSquarePartitionedTensor K dwz63Q).constituent cwSquare103)
      dwz63Tau dwz63Val013 := by
  refine HasTauWeight.of_restricts (cwSquareConstituent_103_restricts K dwz63Q) ?_
  have h := hasTauWeight_matrixMultiplication (K := K) (a := 2 * dwz63Q) (b := 1) (c := 1)
    (by norm_num [dwz63Q]) Nat.one_pos Nat.one_pos dwz63Tau
  rw [show (((2 * dwz63Q) * 1 * 1 : ℕ) : ℝ) = 12 by norm_num [dwz63Q]] at h
  rwa [dwz63Val013_eq]

/-- Value `(2q)^tau` on the `(1,3,0)` constituent. -/
theorem dwz63_hasTauWeight_130 :
    HasTauWeight K ((cwSquarePartitionedTensor K dwz63Q).constituent cwSquare130)
      dwz63Tau dwz63Val013 := by
  refine HasTauWeight.of_restricts (cwSquareConstituent_130_restricts K dwz63Q) ?_
  have h := hasTauWeight_matrixMultiplication (K := K) (a := 1) (b := 2 * dwz63Q) (c := 1)
    Nat.one_pos (by norm_num [dwz63Q]) Nat.one_pos dwz63Tau
  rw [show ((1 * (2 * dwz63Q) * 1 : ℕ) : ℝ) = 12 by norm_num [dwz63Q]] at h
  rwa [dwz63Val013_eq]

/-- Value `(2q)^tau` on the `(3,1,0)` constituent. -/
theorem dwz63_hasTauWeight_310 :
    HasTauWeight K ((cwSquarePartitionedTensor K dwz63Q).constituent cwSquare310)
      dwz63Tau dwz63Val013 := by
  refine HasTauWeight.of_restricts (cwSquareConstituent_310_restricts K dwz63Q) ?_
  have h := hasTauWeight_matrixMultiplication (K := K) (a := 1) (b := 2 * dwz63Q) (c := 1)
    Nat.one_pos (by norm_num [dwz63Q]) Nat.one_pos dwz63Tau
  rw [show ((1 * (2 * dwz63Q) * 1 : ℕ) : ℝ) = 12 by norm_num [dwz63Q]] at h
  rwa [dwz63Val013_eq]

/-- Value `(q^2+2)^tau` on the `(2,2,0)` constituent. -/
theorem dwz63_hasTauWeight_220 :
    HasTauWeight K ((cwSquarePartitionedTensor K dwz63Q).constituent cwSquare220)
      dwz63Tau dwz63Val220 := by
  refine HasTauWeight.of_restricts (cwSquareConstituent_220_restricts K dwz63Q) ?_
  have h := hasTauWeight_matrixMultiplication (K := K) (a := 1) (b := dwz63Q ^ 2 + 2) (c := 1)
    Nat.one_pos (by norm_num [dwz63Q]) Nat.one_pos dwz63Tau
  rw [show ((1 * (dwz63Q ^ 2 + 2) * 1 : ℕ) : ℝ) = 38 by norm_num [dwz63Q]] at h
  rwa [dwz63Val220_eq]

/-- **The `a`-split value on the `(0,2,2)` constituent.**  The constituent restricts to
`<1,1,q^2+2>`, whose weight `(q^2+2)^tau` dominates the `a`-split value by
`dwz63_val022_le_val220`. -/
theorem dwz63_hasTauWeight_022 :
    HasTauWeight K ((cwSquarePartitionedTensor K dwz63Q).constituent cwSquare022)
      dwz63Tau dwz63Val022 := by
  refine HasTauWeight.of_restricts (cwSquareConstituent_022_restricts K dwz63Q) ?_
  have h := hasTauWeight_matrixMultiplication (K := K) (a := 1) (b := 1) (c := dwz63Q ^ 2 + 2)
    Nat.one_pos Nat.one_pos (by norm_num [dwz63Q]) dwz63Tau
  rw [show ((1 * 1 * (dwz63Q ^ 2 + 2) : ℕ) : ℝ) = 38 by norm_num [dwz63Q]] at h
  exact h.mono (dwz63_val022_le_val220.trans_eq dwz63Val220_eq)

/-- **The `a`-split value on the `(2,0,2)` constituent.** -/
theorem dwz63_hasTauWeight_202 :
    HasTauWeight K ((cwSquarePartitionedTensor K dwz63Q).constituent cwSquare202)
      dwz63Tau dwz63Val022 := by
  refine HasTauWeight.of_restricts (cwSquareConstituent_202_restricts K dwz63Q) ?_
  have h := hasTauWeight_matrixMultiplication (K := K) (a := dwz63Q ^ 2 + 2) (b := 1) (c := 1)
    (by norm_num [dwz63Q]) Nat.one_pos Nat.one_pos dwz63Tau
  rw [show (((dwz63Q ^ 2 + 2) * 1 * 1 : ℕ) : ℝ) = 38 by norm_num [dwz63Q]] at h
  exact h.mono (dwz63_val022_le_val220.trans_eq dwz63Val220_eq)

end Ordinary

/-! ## The exceptional orbit

`T_{1,1,2}` is the unique level-two component that is not a matrix-multiplication tensor: it is
the `2 x 2` block tensor whose diagonal blocks are inner products `<1,q,1>` and whose
off-diagonal blocks are outer products `<q,1,q>`.  Zeroing it out onto a direct sum of
matrix-multiplication tensors keeps at most `q^(2 tau)` (one off-diagonal block) or `2 q^tau`
(the two diagonal blocks), both far below the table's `27.3...`; the published bound
`lem:non-rot-values` (d) is a bound on the **three-symmetrized** value `V^{(3)}`, and
[DuanWuZhou2022] explicitly records that no non-rotational bound is available for it.

Consequently `HasTauWeight K (constituent cwSquare112) dwz63Tau dwz63Val112` --- and likewise for
the two rotations at `dwz63Val121` --- is *not* provable from the constituent alone.  These three
factors are therefore hypotheses of the packaged statement below, to be supplied by the
symmetrized `(112)` certificate chain (`Examples/CoppersmithWinograd112*`), which produces the
weight on a power of `symThree` of the constituent rather than on the constituent itself.

Note that `dwz63Val121 > dwz63Val112`: `beta = 69022217/5000000000` is the ten-digit
rationalization of the maximizer `1/(2 + q^(3 tau))` of the `(d)` formula, while
`b = 21015/10^8` is far from it.  So the `(1,2,1)` and `(2,1,1)` factors do **not** follow from
the `(1,1,2)` factor by `HasTauWeight.mono`; they need the same certificate chain instantiated at
`beta`, transported along `cwSquareConstituent_211_isomorphic_cycle` and
`cwSquareConstituent_121_isomorphic_cycleSymm`. -/

/-! ## Orientation invariance

The six-orientation word of the level-two engine presents each constituent through a leg
permutation.  The generic invariance is already committed as
`HasTauWeight.permute` (`MatrixMultiplication/SixSymmetrizedValue.lean`); the two-way form is
recorded here because the word tensor consumes it as a rewrite.  The round-trip isomorphism it
needs is the committed `Tensor.Isomorphic.cancel_permute_symm_left`
(`Tensor/PermutationCoherence.lean`). -/

/-- **A weighted extraction is invariant under every permutation of the three legs.**

`HasTauWeight.permute` (`MatrixMultiplication/SixSymmetrizedValue.lean`) is the forward
direction: the degenerating family of rectangular targets permutes to rectangular targets with
the same volume sum.  The converse follows by permuting back. -/
theorem hasTauWeight_permute_iff {K : Type u} [CommSemiring K] {V : Leg → Type v}
    [∀ c, AddCommMonoid (V c)] [∀ c, Module K (V c)] {X : Tensor3 K V} {τ value : ℝ}
    (e : Orientation) :
    HasTauWeight K (Tensor.permute e X) τ value ↔ HasTauWeight K X τ value :=
  ⟨fun h ↦ (h.permute e.symm).of_restricts
      (Tensor.Isomorphic.cancel_permute_symm_left e X).symm.restricts,
    fun h ↦ h.permute e⟩

/-- The fifteen coarse addresses of `table:result-2nd`, in the order of `dwz63Alpha`. -/
def dwz63Component : Fin 15 → CWSquareAddress :=
  ![cwSquareAddress 0 0 4, cwSquareAddress 0 1 3, cwSquareAddress 0 2 2,
    cwSquareAddress 0 3 1, cwSquareAddress 0 4 0,
    cwSquareAddress 1 0 3, cwSquareAddress 1 1 2, cwSquareAddress 1 2 1,
    cwSquareAddress 1 3 0,
    cwSquareAddress 2 0 2, cwSquareAddress 2 1 1, cwSquareAddress 2 2 0,
    cwSquareAddress 3 0 1, cwSquareAddress 3 1 0, cwSquareAddress 4 0 0]

/-- The fifteen component logarithms, in the order of `dwz63Alpha`. -/
def dwz63LogValComponent : Fin 15 → ℝ :=
  ![dwz63LogVal004, dwz63LogVal013, dwz63LogVal022, dwz63LogVal013, dwz63LogVal004,
    dwz63LogVal013, dwz63LogVal112, dwz63LogVal121, dwz63LogVal013,
    dwz63LogVal022, dwz63LogVal121, dwz63LogVal220,
    dwz63LogVal013, dwz63LogVal013, dwz63LogVal004]

/-- The fifteen component values, in the order of `dwz63Alpha`. -/
def dwz63Val : Fin 15 → ℝ := fun j ↦ Real.exp (dwz63LogValComponent j)

/-- Every component value is positive. -/
theorem dwz63Val_pos (j : Fin 15) : 0 < dwz63Val j := Real.exp_pos _

/-- The logarithm of a component value is its component logarithm. -/
@[simp] theorem log_dwz63Val (j : Fin 15) :
    Real.log (dwz63Val j) = dwz63LogValComponent j := Real.log_exp _

/-- **The fifteen-factor form of `dwz63LogVal`.** -/
theorem dwz63_logVal_eq_sum :
    dwz63LogVal = ∑ j : Fin 15, ((dwz63Alpha j : ℝ) / 100000000) * Real.log (dwz63Val j) := by
  simp only [log_dwz63Val, dwz63LogValComponent, dwz63Alpha, Fin.sum_univ_succ,
    Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_fin_one,
    Nat.cast_ofNat]
  rw [dwz63_logVal_eq]
  ring

/-- The `alpha`-weighted sum of the component logarithms, cleared of the denominator `10^8`. -/
theorem dwz63_sum_alpha_mul_log :
    ∑ j : Fin 15, (dwz63Alpha j : ℝ) * Real.log (dwz63Val j) = 100000000 * dwz63LogVal := by
  rw [dwz63_logVal_eq_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  ring

/-- **One full period of the leaf value rate is the `alpha`-weighted product of the fifteen
component values.**

`dwz63LogVal` is by construction `log prod V^alpha` over the mass `10^8` of `dwz63Alpha`, so this
is an *equality*, not an estimate: no rational under-approximation enters until `dwz63ValRate`
is compared with `Real.exp dwz63LogVal` downstream. -/
theorem dwz63_exp_logVal_pow_eq_prod :
    Real.exp dwz63LogVal ^ (100000000 : ℕ) = ∏ j : Fin 15, dwz63Val j ^ dwz63Alpha j := by
  have hkey : (∏ j : Fin 15, dwz63Val j ^ dwz63Alpha j)
      = Real.exp (∑ j : Fin 15, (dwz63Alpha j : ℝ) * Real.log (dwz63Val j)) := by
    rw [Real.exp_sum]
    refine Finset.prod_congr rfl fun j _ ↦ ?_
    rw [← Real.rpow_natCast (dwz63Val j) (dwz63Alpha j),
      Real.rpow_def_of_pos (dwz63Val_pos j), mul_comm]
  rw [hkey, dwz63_sum_alpha_mul_log,
    ← Real.rpow_natCast (Real.exp dwz63LogVal) 100000000,
    Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
  congr 1
  push_cast
  ring

/-- **The fifteen per-constituent weights of section 6.3.**

Twelve are discharged above; the three components of the `(1,1,2)` orbit enter as hypotheses,
for the reason recorded in the module note. -/
theorem dwz63_hasTauWeight_component (K : Type u) [CommRing K]
    (h112 : HasTauWeight K ((cwSquarePartitionedTensor K dwz63Q).constituent cwSquare112)
      dwz63Tau dwz63Val112)
    (h121 : HasTauWeight K ((cwSquarePartitionedTensor K dwz63Q).constituent cwSquare121)
      dwz63Tau dwz63Val121)
    (h211 : HasTauWeight K ((cwSquarePartitionedTensor K dwz63Q).constituent cwSquare211)
      dwz63Tau dwz63Val121)
    (j : Fin 15) :
    HasTauWeight K ((cwSquarePartitionedTensor K dwz63Q).constituent (dwz63Component j))
      dwz63Tau (dwz63Val j) := by
  have h400 := dwz63_hasTauWeight_400 K
  have h040 := dwz63_hasTauWeight_040 K
  have h031 := dwz63_hasTauWeight_031 K
  have h301 := dwz63_hasTauWeight_301 K
  have h103 := dwz63_hasTauWeight_103 K
  have h130 := dwz63_hasTauWeight_130 K
  have h310 := dwz63_hasTauWeight_310 K
  have h202 := dwz63_hasTauWeight_202 K
  have h220 := dwz63_hasTauWeight_220 K
  rw [cwSquare400_eq] at h400
  rw [cwSquare040_eq] at h040
  rw [cwSquare031_eq] at h031
  rw [cwSquare301_eq] at h301
  rw [cwSquare103_eq] at h103
  rw [cwSquare130_eq] at h130
  rw [cwSquare310_eq] at h310
  rw [cwSquare202_eq] at h202
  rw [cwSquare220_eq] at h220
  fin_cases j
  · exact dwz63_hasTauWeight_004 K
  · exact dwz63_hasTauWeight_013 K
  · exact dwz63_hasTauWeight_022 K
  · exact h031
  · exact h040
  · exact h103
  · exact h112
  · exact h121
  · exact h130
  · exact h202
  · exact h211
  · exact h220
  · exact h301
  · exact h310
  · exact h400

/-! ## The address-indexed form

`WordType`-based clients index letters by the coarse address rather than by a position in the
`dwz63Alpha` table.  `dwz63ValOf` is the same fifteen numbers presented that way, following the
`cwSquareOrdinaryM/N/P` idiom of `Examples/CoppersmithWinogradSquareOrdinarySymmetry.lean`. -/

/-- The section 6.3 value attached to a coarse square address.  Off the fifteen-address support
the fall-through branch returns the `(0,1,3)` value; no client reads it there. -/
def dwz63ValOf (s : CWSquareAddress) : ℝ :=
  if s = cwSquareAddress 0 2 2 ∨ s = cwSquareAddress 2 0 2 then dwz63Val022
  else if s = cwSquareAddress 1 1 2 then dwz63Val112
  else if s = cwSquareAddress 1 2 1 ∨ s = cwSquareAddress 2 1 1 then dwz63Val121
  else if s = cwSquareAddress 2 2 0 then dwz63Val220
  else if s = cwSquareAddress 0 0 4 ∨ s = cwSquareAddress 0 4 0 ∨ s = cwSquareAddress 4 0 0
    then dwz63Val004
  else dwz63Val013

/-- The two presentations of the fifteen values agree. -/
@[simp] theorem dwz63ValOf_dwz63Component (j : Fin 15) :
    dwz63ValOf (dwz63Component j) = dwz63Val j := by
  fin_cases j <;>
    simp [dwz63ValOf, dwz63Component, dwz63Val, dwz63LogValComponent, dwz63Val004,
      dwz63Val013, dwz63Val022, dwz63Val112, dwz63Val121, dwz63Val220]

/-- **The fifteen per-constituent weights, indexed by coarse address.**

Twelve are discharged above; the three components of the `(1,1,2)` orbit enter as hypotheses,
for the reason recorded in the module note. -/
theorem dwz63_hasTauWeight_of_mem_support (K : Type u) [CommRing K]
    (h112 : HasTauWeight K ((cwSquarePartitionedTensor K dwz63Q).constituent cwSquare112)
      dwz63Tau dwz63Val112)
    (h121 : HasTauWeight K ((cwSquarePartitionedTensor K dwz63Q).constituent cwSquare121)
      dwz63Tau dwz63Val121)
    (h211 : HasTauWeight K ((cwSquarePartitionedTensor K dwz63Q).constituent cwSquare211)
      dwz63Tau dwz63Val121)
    (s : CWSquareAddress) (hs : s ∈ cwSquareSupport) :
    HasTauWeight K ((cwSquarePartitionedTensor K dwz63Q).constituent s)
      dwz63Tau (dwz63ValOf s) := by
  have h400 := dwz63_hasTauWeight_400 K
  have h040 := dwz63_hasTauWeight_040 K
  have h031 := dwz63_hasTauWeight_031 K
  have h301 := dwz63_hasTauWeight_301 K
  have h103 := dwz63_hasTauWeight_103 K
  have h130 := dwz63_hasTauWeight_130 K
  have h310 := dwz63_hasTauWeight_310 K
  have h202 := dwz63_hasTauWeight_202 K
  have h220 := dwz63_hasTauWeight_220 K
  rw [cwSquare400_eq] at h400
  rw [cwSquare040_eq] at h040
  rw [cwSquare031_eq] at h031
  rw [cwSquare301_eq] at h301
  rw [cwSquare103_eq] at h103
  rw [cwSquare130_eq] at h130
  rw [cwSquare310_eq] at h310
  rw [cwSquare202_eq] at h202
  rw [cwSquare220_eq] at h220
  rw [cwSquareSupport_eq_antidiagonal] at hs
  simp only [cwSquareAntidiagonal, Finset.mem_insert, Finset.mem_singleton] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [dwz63ValOf, cwSquareAddress_eq_iff, or_true, true_or, and_true, if_true]
  · exact dwz63_hasTauWeight_004 K
  · exact dwz63_hasTauWeight_013 K
  · exact dwz63_hasTauWeight_022 K
  · exact h031
  · exact h040
  · exact h103
  · exact h112
  · exact h121
  · exact h130
  · exact h202
  · exact h211
  · exact h220
  · exact h301
  · exact h310
  · exact h400

end

end AlgebraicComplexity.Examples
