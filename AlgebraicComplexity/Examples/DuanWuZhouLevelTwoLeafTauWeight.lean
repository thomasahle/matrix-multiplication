/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinograd112SymmetricGrowth
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoGlobalArithmetic
import AlgebraicComplexity.MatrixMultiplication.SixSymmetrizedValue

/-!
# The `(1,1,2)` factor of the `[DuanWuZhou2022]` level-two leaf, as a `tau`-weight

`Examples/DuanWuZhouLevelTwoGlobalStage.lean` reduces `omega < 2.374631` to
`DwzLevelTwoCountingStage`, whose only genuinely tensor-side content is
`exists_value_of_repairedStage_true`: at each word length a count-side client must exhibit a
restriction of `sym_6(T)^{tensor n}` onto `card beta` copies of a *leaf*, a `HasTauWeight` for that
leaf, and the value bound `exp(dwz63LogVal) ^ (6 n) <= leafValue`.

The leaf is a tensor product over the fifteen level-two components `T_{i,j,k}`, each restricted to
the split distribution `[DuanWuZhou2022]` section 6.3 prescribes.  Since `HasTauWeight` is
multiplicative under `Tensor.external`, the leaf's weight is the product of the fifteen component
weights, and each factor can be produced independently.  This module produces the **hardest single
factor**, the one `[DuanWuZhou2022]` `lem:non-rot-values` (d) supplies: the component `(1,1,2)`,
which is the only level-two component that is not itself a matrix-multiplication tensor and the
only one whose value bound is available exclusively in three-symmetrized form.

## The parameter identification

`[DuanWuZhou2022]` `second_power_appendix.tex` proves (d) by hashing `sym_3` of the type-restricted
power and counting

`C(m, m/2)^2 * C(m; 2a'm, b'm, b'm)` disjoint triples, each isomorphic to
`<q^{(4a'+2b')m}, q^{(4a'+2b')m}, q^{(4a'+2b')m}>`,

with `2a' + 2b' = 1` and Z-marginal split `(b', 2a', b')`.  That is *exactly* the committed
`Examples/CoppersmithWinograd112SymmetricGrowth.lean` chain: its symmetric typed leaf has visible
marginal entropy `2 + H_2(mu, mu, 1 - 2mu)` per unit of profile mass with `mu = L / (2(L+G))`, so
`b' = mu` and the whole of `lem:non-rot-values` (d) is the specialization at

`L = 4203,  G = 9995797,  q = 6`,

which is `b = 21015 / 10^8 = L / (2(L+G))`, the split of `(1,1,2)` recorded in
`better_bound/dwz_endpoint_prep/PREP.md` section 6.  Two independent checks pin this down:

* the entropy atoms `2(L+G)/L = 20000000/4203 = 1/b` and `(L+G)/G = 10000000/9995797 = 1/(1-2b)`
  are *literally* two of the nine logarithm atoms of `dwz63LogVal`; and
* `dwz63LogVal_112_atom_coefficients` below checks that their `dwz63LogVal` coefficients are
  `alpha(1,1,2) = 20088623 / 10^8` times the coefficients this module produces.

The classical Coppersmith--Winograd client `Examples/CoppersmithWinograd2375477.lean` instantiates
the same chain at `(L,G) = (7,247)`, the *unconstrained* optimum `1/(2+q^{3 tau})`.  That is the
free-`beta` member `[DuanWuZhou2022]` uses for `(1,2,1)` and `(2,1,1)`; it is **not** the
`(1,1,2)` split, which section 6.3's compatibility constraint pins to `b`.  Reusing `(7,247)` here
would be a silent parameter error, so the two are kept apart by name.

## What is produced

`exists_eventually_dwz112LeafHasTauWeight` --- for every sufficiently large proportional repetition
`k`,

`HasTauWeight K (sym_3(T_{1,1,2})^{tensor D k}) dwz63Tau (dwz112LeafTerm K ^ (3 D k))`,

where `D = [2(L+G)]^3 = 8 * 10^21` is the leaf's profile mass and `T_{1,1,2}` is the coarsened
`(112)` constituent `cw112PartitionedTensor K 6`.  Its companion
`exists_eventually_dwz112LeafHasTauWeight_exp` restates the weight in the exponential shape the
`hvalue` premise of `exists_value_of_repairedStage_true` consumes, and
`exists_eventually_dwz112ConstituentHasTauWeight` transports it, through
`cwSquareConstituent_112_restricts_partitioned`, onto the coarse level-two constituent
`(cwSquarePartitionedTensor K dwz63Q).constituent cwSquare112` that a per-constituent value law
consumes.  All three land on a power of `sym_3` of the constituent, never on the bare constituent:
`[DuanWuZhou2022]` `note:T112` records that `T_{1,1,2}` has no non-rotational value at all, so a
three-symmetrized weight is the strongest statement that exists.  By
`cwSquareConstituent_121_isomorphic_cycleSymm` and `cwSquareConstituent_211_isomorphic_cycle` this
is simultaneously a weight on the external product of the `(1,1,2)`, `(1,2,1)` and `(2,1,1)`
constituents, which is how `[DuanWuZhou2022]` uses it.

`dwz112LogValue` is the logarithm of `PREP.md` section 1.6's `(1,1,2)` entry

`(4 / ((1-2b)^{1-2b} b^{2b}))^{1/3} q^{(2-2b) tau} = 27.0947543121752429`,

and `log_dwz112LeafTerm_eq` proves that the achieved term's logarithm is *exactly*
`dwz112LogValue - log 2 / (3 D)`.  The deficit is the standard strict-base reserve of
`Examples/CoppersmithWinograd112SymmetricGrowth.lean` (any base strictly below the entropy base is
attained, the base itself need not be); at `D = 8 * 10^21` it is below `3 * 10 ^ (-23)` nats, i.e.
five thousand times smaller than section 6.3's tightest published slack of
`1.7446 * 10 ^ (-7)` nats.  `dwz112_exp_le_leafTerm` records it as the round `10 ^ (-22)`.

## What is *not* produced here, and is therefore hypothesis-free

Nothing in this module is conditional: every statement below is proved outright.  What it does
*not* do is equally important to state, because these are the remaining obligations of the
count side and none of them is discharged by any theorem here:

1. **the restriction** `Restricts (Tensor.power (symSix F T) n) (indexedDirectSum ... leaf)` --- the
   marked two-leg hashing, compatibility cleanup and hole repair of section 6.  This module says
   nothing about how the `(1,1,2)` factor sits inside `sym_6(T)^{tensor n}`;
2. **the other fourteen components** --- `(1,2,1)` and `(2,1,1)` are the same chain at
   `L = 69022217, G = 2430977783` (Stage B), `(0,2,2)`/`(2,0,2)` need the `a`-split of
   `Tensor.Restricts.restrictedSplittingPower_ternaryDivision` and a multinomial count,
   `(2,2,0)`, `(0,1,3)` and the three corners are matrix-multiplication tensors;
3. **the product** --- assembling the fifteen factors through `HasTauWeight.external` and matching
   the exponent bookkeeping of `exp(dwz63LogVal) ^ (6 n)`;
4. **the identification** of `cw112PartitionedTensor K 6` with `[DuanWuZhou2022]`'s `T_{1,1,2}` as
   it occurs inside the level-two partition of `CW_6^{tensor 2}`, and of the symmetric typed leaf's
   marked-word family with `T_{1,1,2}^{tensor m}[alphatilde_A]`.  Both are true by construction of
   `Examples/CoppersmithWinograd112Partition.lean`, but neither is stated as a theorem yet.

## Position in the library

Layer 4 (a client).  It imports the committed classical `(112)` symmetric growth chain, the
`[DuanWuZhou2022]` rational arithmetic, and the six-symmetrized value bridge; it defines no new
tensor and no new hashing argument.

Primary source: Ran Duan, Hongxun Wu and Renfei Zhou, *Faster Matrix Multiplication via Asymmetric
Hashing*, arXiv:2210.10173, `second_power.tex` `lem:non-rot-values` (d) and `global_value.tex`
section 6.3.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor

universe u v w

/-! ## The `(1,1,2)` split parameters -/

/-- Light letter count of the `[DuanWuZhou2022]` section 6.3 `(1,1,2)` split.  Together with
`dwz112G` it encodes `b = 21015 / 10^8 = L / (2 (L + G))`. -/
def dwz112L : ℕ := 4203

/-- Heavy letter count of the `[DuanWuZhou2022]` section 6.3 `(1,1,2)` split. -/
def dwz112G : ℕ := 9995797

theorem dwz112L_pos : 0 < dwz112L := by norm_num [dwz112L]

theorem dwz112G_pos : 0 < dwz112G := by norm_num [dwz112G]

/-- The stride `2 (L + G)` is exactly `2 * 10 ^ 7`, so `L / (2 (L+G)) = 21015 / 10 ^ 8 = b`. -/
theorem dwz112Stride_eq : 2 * (dwz112L + dwz112G) = 20000000 := by
  norm_num [dwz112L, dwz112G]

/-- Profile mass of the symmetric `(112)` typed leaf at the DWZ split: `D = [2(L+G)]^3`. -/
abbrev dwz112Mass : ℕ := (2 * (dwz112L + dwz112G)) ^ 3

theorem dwz112Mass_eq : dwz112Mass = 8000000000000000000000 := by
  norm_num [dwz112Mass, dwz112L, dwz112G]

/-- **The parameter check.**  The two `b`-dependent logarithm atoms of `dwz63LogVal` carry exactly
`alpha(1,1,2) = 20088623 / 10 ^ 8` times the coefficients this module's `dwz112LogValue` gives
them.  This is what identifies `(L, G) = (4203, 9995797)` as *the* `[DuanWuZhou2022]` section 6.3
`(1,1,2)` split rather than the free-`beta` split of `(1,2,1)` and `(2,1,1)`. -/
theorem dwz63LogVal_112_atom_coefficients :
    (20088623 / 100000000 : ℝ) * (9995797 / 30000000) =
        200801797517531 / 3000000000000000 ∧
      (20088623 / 100000000 : ℝ) * (4203 / 30000000) =
        28144160823 / 1000000000000000 := by
  constructor <;> norm_num

noncomputable section

variable (K : Type u) [Field K]

/-! ## Symbolic logarithms of the symmetric `(112)` chain

The three identities below are stated and proved for arbitrary `(q, L, G)`; they are the entropy /
volume / normalization bridge every rational parameter client of
`Examples/CoppersmithWinograd112SymmetricGrowth.lean` needs.

They duplicate `log_cw112SymmetricMarginalEntropyBase`, `log_cw112SymmetricDimensionVolume`,
`log_cw112SymmetricLimitLowerTerm` and `cw112SymmetricLimitLowerTerm_pos` of
`Examples/CoppersmithWinogradSquare112TauValueGrowth.lean`.  That module is *not* imported here on
purpose: it drags in the whole Coppersmith--Winograd *square outer hashing* cone (31 further
modules, none of which this file uses), and at the time of writing one of them,
`Examples/CoppersmithWinogradSquareEntropy.lean`, does not elaborate --- it uses
`ProbabilityVector.klDiv_eq_entropy_sub_of_expectation_log_eq` without importing
`Probability/KullbackLeiblerBasic.lean`, which is not in its import closure.  Once that import is
repaired the four declarations below should be deleted and the upstream ones imported instead. -/

/-- The stable normalized value of the symmetric inner leaf is positive for a positive copy
base. -/
theorem dwzCw112SymmetricLimitLowerTerm_pos
    {innerCopyBase : ℝ} (hinnerCopyBase : 0 < innerCopyBase)
    (τ : ℝ) (q L G : ℕ) (hq : 0 < q) (hL : 0 < L) (hG : 0 < G) :
    0 < cw112SymmetricLimitLowerTerm K innerCopyBase τ q L G hq hL hG := by
  have hx := (cw112SymmetricLeaf K q L G hq hL hG).dimensionProduct_pos .X
  have hy := (cw112SymmetricLeaf K q L G hq hL hG).dimensionProduct_pos .Y
  have hz := (cw112SymmetricLeaf K q L G hq hL hG).dimensionProduct_pos .Z
  have hvolumeNat : 0 <
      (cw112SymmetricLeaf K q L G hq hL hG).dimensionProduct .X *
        (cw112SymmetricLeaf K q L G hq hL hG).dimensionProduct .Y *
        (cw112SymmetricLeaf K q L G hq hL hG).dimensionProduct .Z :=
    Nat.mul_pos (Nat.mul_pos hx hy) hz
  have hvolume : (0 : ℝ) <
      ((cw112SymmetricLeaf K q L G hq hL hG).dimensionProduct .X *
        (cw112SymmetricLeaf K q L G hq hL hG).dimensionProduct .Y *
        (cw112SymmetricLeaf K q L G hq hL hG).dimensionProduct .Z : ℕ) := by
    exact_mod_cast hvolumeNat
  unfold cw112SymmetricLimitLowerTerm
  exact Real.rpow_pos_of_pos
    (mul_pos hinnerCopyBase (Real.rpow_pos_of_pos hvolume τ)) _

/-- Exact logarithm of the common visible marginal-entropy base of the symmetric `(112)` leaf.

Writing `s = 2(L+G)` and `D = s^3`, the formula is
`2 D log 2 + 2 L s^2 log (s/L) + 2 G s^2 log ((L+G)/G)`. -/
theorem dwz_log_cw112SymmetricMarginalEntropyBase
    (q L G : ℕ) (hq : 0 < q) (hL : 0 < L) (hG : 0 < G) :
    Real.log (cw112SymmetricMarginalEntropyBase K q L G hq hL hG) =
      (2 * (2 * (L + G)) ^ 3 : ℕ) * Real.log 2 +
        (2 * L * (2 * (L + G)) ^ 2 : ℕ) *
          Real.log (((2 * (L + G) : ℕ) : ℝ) / (L : ℝ)) +
        (2 * G * (2 * (L + G)) ^ 2 : ℕ) *
          Real.log (((L + G : ℕ) : ℝ) / (G : ℝ)) := by
  rw [cw112SymmetricMarginalEntropyBase_eq_exp, Real.log_exp]
  unfold cw112MuEntropyBits cw112Mu
  have hsumNat : 0 < L + G := Nat.add_pos_left hL G
  have hsum : (0 : ℝ) < L + G := by exact_mod_cast hsumNat
  have hLReal : (0 : ℝ) < L := by exact_mod_cast hL
  have hGReal : (0 : ℝ) < G := by exact_mod_cast hG
  have hlogTwo : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num)).ne'
  have hgrid :
      1 - 2 * ((L : ℝ) / (2 * (L + G) : ℕ)) = (G : ℝ) / (L + G) := by
    push_cast
    field_simp [hsum.ne']
    ring
  rw [hgrid]
  have hneg (x : ℝ) : Real.negMulLog x = x * Real.log x⁻¹ := by
    rw [Real.negMulLog_eq_neg, Real.log_inv]
    ring
  rw [hneg, hneg]
  simp only [inv_div]
  push_cast
  field_simp [hlogTwo, hsum.ne', hLReal.ne', hGReal.ne']
  ring

/-- Exact logarithm of the symmetric inner matrix-volume product: each leg dimension is
`q^((4G+2L)(2(L+G))²)`. -/
theorem dwz_log_cw112SymmetricDimensionVolume
    (q L G : ℕ) (hq : 0 < q) (hL : 0 < L) (hG : 0 < G) :
    Real.log
        (((cw112SymmetricLeaf K q L G hq hL hG).dimensionProduct .X *
          (cw112SymmetricLeaf K q L G hq hL hG).dimensionProduct .Y *
          (cw112SymmetricLeaf K q L G hq hL hG).dimensionProduct .Z : ℕ) : ℝ) =
      (((3 * ((2 * (L + G)) ^ 2) * (4 * G + 2 * L) : ℕ) : ℝ)) *
        Real.log q := by
  simp_rw [cw112SymmetricLeaf,
    cw112SymmetricPartitionRationalTypedLeaf_dimensionProduct]
  have hside : 0 < cw112FiniteLeafSquareSide q L G := by
    unfold cw112FiniteLeafSquareSide
    positivity
  norm_num only [Nat.cast_mul, Nat.cast_pow]
  rw [Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity)]
  simp only [Real.log_pow]
  push_cast
  ring

/-- Logarithm of the stable normalized symmetric inner lower term. -/
theorem dwz_log_cw112SymmetricLimitLowerTerm
    {innerCopyBase : ℝ} (hinnerCopyBase : 0 < innerCopyBase)
    (τ : ℝ) (q L G : ℕ) (hq : 0 < q) (hL : 0 < L) (hG : 0 < G) :
    Real.log (cw112SymmetricLimitLowerTerm
      K innerCopyBase τ q L G hq hL hG) =
      (((3 * (cw112SymmetricLeaf K q L G hq hL hG).profile.mass : ℕ) : ℝ)⁻¹) *
        (Real.log innerCopyBase +
          τ * Real.log
            (((cw112SymmetricLeaf K q L G hq hL hG).dimensionProduct .X *
              (cw112SymmetricLeaf K q L G hq hL hG).dimensionProduct .Y *
              (cw112SymmetricLeaf K q L G hq hL hG).dimensionProduct .Z : ℕ) : ℝ)) := by
  have hx := (cw112SymmetricLeaf K q L G hq hL hG).dimensionProduct_pos .X
  have hy := (cw112SymmetricLeaf K q L G hq hL hG).dimensionProduct_pos .Y
  have hz := (cw112SymmetricLeaf K q L G hq hL hG).dimensionProduct_pos .Z
  have hvolumeNat : 0 <
      (cw112SymmetricLeaf K q L G hq hL hG).dimensionProduct .X *
        (cw112SymmetricLeaf K q L G hq hL hG).dimensionProduct .Y *
        (cw112SymmetricLeaf K q L G hq hL hG).dimensionProduct .Z :=
    Nat.mul_pos (Nat.mul_pos hx hy) hz
  have hvolume : (0 : ℝ) <
      ((cw112SymmetricLeaf K q L G hq hL hG).dimensionProduct .X *
        (cw112SymmetricLeaf K q L G hq hL hG).dimensionProduct .Y *
        (cw112SymmetricLeaf K q L G hq hL hG).dimensionProduct .Z : ℕ) := by
    exact_mod_cast hvolumeNat
  unfold cw112SymmetricLimitLowerTerm
  rw [Real.log_rpow (mul_pos hinnerCopyBase
    (Real.rpow_pos_of_pos hvolume τ)),
    Real.log_mul hinnerCopyBase.ne' (Real.rpow_pos_of_pos hvolume τ).ne',
    Real.log_rpow hvolume]

/-! ## The strict inner copy base -/

/-- Strict inner visible-copy base at the DWZ `(1,1,2)` split, with the factor-two reserve the
committed growth theorem requires.  The reserve costs `log 2 / (3 D)` nats, i.e. under
`3 * 10 ^ (-23)`. -/
noncomputable def dwz112InnerCopyBase : ℝ :=
  cw112SymmetricMarginalEntropyBase K 6 dwz112L dwz112G
    (by norm_num) dwz112L_pos dwz112G_pos / 2

theorem dwz112InnerCopyBase_pos : 0 < dwz112InnerCopyBase K := by
  unfold dwz112InnerCopyBase
  exact div_pos
    (cw112SymmetricMarginalEntropyBase_pos K 6 dwz112L dwz112G
      (by norm_num) dwz112L_pos dwz112G_pos)
    (by norm_num)

theorem dwz112InnerCopyBase_lt :
    dwz112InnerCopyBase K <
      cw112SymmetricMarginalEntropyBase K 6 dwz112L dwz112G
        (by norm_num) dwz112L_pos dwz112G_pos := by
  unfold dwz112InnerCopyBase
  exact div_lt_self
    (cw112SymmetricMarginalEntropyBase_pos K 6 dwz112L dwz112G
      (by norm_num) dwz112L_pos dwz112G_pos)
    (by norm_num)

/-! ## Exact logarithmic identities at the DWZ split -/

/-- Exact logarithm of the symmetric inner entropy base at `(L,G) = (4203, 9995797)`.

The two non-`log 2` atoms are `1/b = 20000000/4203` and `1/(1-2b) = 10000000/9995797`, which are
literally two of the nine atoms of `dwz63LogVal`. -/
theorem log_dwz112InnerEntropyBase :
    Real.log
        (cw112SymmetricMarginalEntropyBase K 6 dwz112L dwz112G
          (by norm_num) dwz112L_pos dwz112G_pos) =
      2 * 8000000000000000000000 * Real.log 2 +
        3362400000000000000 * Real.log (20000000 / 4203 : ℝ) +
        7996637600000000000000 * Real.log (10000000 / 9995797 : ℝ) := by
  rw [dwz_log_cw112SymmetricMarginalEntropyBase K 6 dwz112L dwz112G
    (by norm_num) dwz112L_pos dwz112G_pos]
  norm_num [dwz112Mass, dwz112L, dwz112G]

/-- Exact logarithm of the strict inner visible-copy base: the entropy base less `log 2`. -/
theorem log_dwz112InnerCopyBase :
    Real.log (dwz112InnerCopyBase K) =
      2 * 8000000000000000000000 * Real.log 2 +
        3362400000000000000 * Real.log (20000000 / 4203 : ℝ) +
        7996637600000000000000 * Real.log (10000000 / 9995797 : ℝ) - Real.log 2 := by
  rw [dwz112InnerCopyBase,
    Real.log_div
      (cw112SymmetricMarginalEntropyBase_pos K 6 dwz112L dwz112G
        (by norm_num) dwz112L_pos dwz112G_pos).ne'
      (by norm_num : (2 : ℝ) ≠ 0),
    log_dwz112InnerEntropyBase]

/-- The symmetric `(112)` leaf at the DWZ split has matrix-volume logarithm
`3 [2(L+G)]^2 (4G + 2L) log 6 = 47989912800000000000000 * log 6`. -/
theorem log_dwz112InnerDimensionVolume :
    Real.log
        (((cw112SymmetricLeaf K 6 dwz112L dwz112G
              (by norm_num) dwz112L_pos dwz112G_pos).dimensionProduct .X *
          (cw112SymmetricLeaf K 6 dwz112L dwz112G
              (by norm_num) dwz112L_pos dwz112G_pos).dimensionProduct .Y *
          (cw112SymmetricLeaf K 6 dwz112L dwz112G
              (by norm_num) dwz112L_pos dwz112G_pos).dimensionProduct .Z : ℕ) : ℝ) =
      47989912800000000000000 * Real.log 6 := by
  rw [dwz_log_cw112SymmetricDimensionVolume K 6 dwz112L dwz112G
    (by norm_num) dwz112L_pos dwz112G_pos]
  norm_num [dwz112Mass, dwz112L, dwz112G]

/-! ## The achieved `(1,1,2)` component value -/

/-- The normalized `(1,1,2)` leaf term actually achieved at the DWZ split and at the declared
exponent `dwz63Tau`.  This is `[DuanWuZhou2022]` `lem:non-rot-values` (d) with `beta := b`. -/
noncomputable def dwz112LeafTerm : ℝ :=
  cw112SymmetricLimitLowerTerm K (dwz112InnerCopyBase K) dwz63Tau 6 dwz112L dwz112G
    (by norm_num) dwz112L_pos dwz112G_pos

theorem dwz112LeafTerm_pos : 0 < dwz112LeafTerm K := by
  unfold dwz112LeafTerm
  exact dwzCw112SymmetricLimitLowerTerm_pos K (dwz112InnerCopyBase_pos K) dwz63Tau 6
    dwz112L dwz112G (by norm_num) dwz112L_pos dwz112G_pos

/-- Clearing the `3 D` normalization exposes one visible-copy logarithm and one matrix-volume
logarithm.

Proof sketch: specialize `log_cw112SymmetricLimitLowerTerm`, substitute the exact entropy and
dimension identities, and clear the nonzero profile-mass denominator `3 * 8 * 10 ^ 21`. -/
theorem scaled_log_dwz112LeafTerm :
    (24000000000000000000000 : ℝ) * Real.log (dwz112LeafTerm K) =
      (2 * 8000000000000000000000 * Real.log 2 +
        3362400000000000000 * Real.log (20000000 / 4203 : ℝ) +
        7996637600000000000000 * Real.log (10000000 / 9995797 : ℝ) - Real.log 2) +
      (2374631 / 3000000 : ℝ) * (47989912800000000000000 * Real.log 6) := by
  have h := dwz_log_cw112SymmetricLimitLowerTerm K
    (dwz112InnerCopyBase_pos K) dwz63Tau 6 dwz112L dwz112G
      (by norm_num) dwz112L_pos dwz112G_pos
  rw [cw112SymmetricLeaf_profile_mass, log_dwz112InnerCopyBase,
    log_dwz112InnerDimensionVolume] at h
  change Real.log (dwz112LeafTerm K) = _ at h
  -- ELABORATION RISK (moderate): `norm_num` must normalize the `22`-digit rational
  -- `((3 * (2 * (4203 + 9995797)) ^ 3 : ℕ) : ℝ)⁻¹` on both sides before `linarith` clears it.
  -- Fallback if it stalls: replace the two lines below by
  --   `simp only [dwz112L, dwz112G, dwz63Tau] at h ⊢; push_cast at h ⊢; linarith`.
  norm_num [dwz112L, dwz112G, dwz63Tau] at h ⊢
  linarith

/-- The logarithm of `PREP.md` section 1.6's `(1,1,2)` component value

`(4 / ((1-2b)^{1-2b} b^{2b}))^{1/3} * q^{(2-2b) tau}`,

with `b = 21015/10^8`, `q = 6` and `tau = dwz63Tau`.  Numerically `exp` of this is
`27.0947543121752429`. -/
noncomputable def dwz112LogValue : ℝ :=
  2 / 3 * Real.log 2 +
    4203 / 30000000 * Real.log (20000000 / 4203 : ℝ) +
    9995797 / 30000000 * Real.log (10000000 / 9995797 : ℝ) +
    19995797 / 10000000 * (dwz63Tau * Real.log 6)

/-- **The achieved term is the published component value less the strict-base reserve.**

`log dwz112LeafTerm = dwz112LogValue - log 2 / (3 D)` exactly, with `3 D = 2.4 * 10 ^ 22`. -/
theorem log_dwz112LeafTerm_eq :
    Real.log (dwz112LeafTerm K) =
      dwz112LogValue - Real.log 2 / 24000000000000000000000 := by
  have h := scaled_log_dwz112LeafTerm K
  rw [dwz112LogValue, dwz63Tau]
  linarith

/-- The strict-base reserve is below `10 ^ (-22)` nats, four orders of magnitude inside
`[DuanWuZhou2022]` section 6.3's tightest published slack `1.7446 * 10 ^ (-7)`. -/
theorem dwz112LogValue_sub_le_log_dwz112LeafTerm :
    dwz112LogValue - 1 / 10 ^ 22 ≤ Real.log (dwz112LeafTerm K) := by
  rw [log_dwz112LeafTerm_eq]
  -- the goal is linear in the single atom `Real.log 2` with rational coefficients
  have h2 : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  linarith

/-- Exponential form of the previous bound: the DWZ `(1,1,2)` component value, backed off by
`10 ^ (-22)` nats, is genuinely achieved by the extracted leaf term. -/
theorem dwz112_exp_le_leafTerm :
    Real.exp (dwz112LogValue - 1 / 10 ^ 22) ≤ dwz112LeafTerm K := by
  calc Real.exp (dwz112LogValue - 1 / 10 ^ 22)
      ≤ Real.exp (Real.log (dwz112LeafTerm K)) :=
        Real.exp_le_exp.mpr (dwz112LogValue_sub_le_log_dwz112LeafTerm K)
    _ = dwz112LeafTerm K := Real.exp_log (dwz112LeafTerm_pos K)

/-! ## The `tau`-weight -/

/-- **The `(1,1,2)` factor of the `[DuanWuZhou2022]` level-two leaf carries its published
`tau`-weight.**

At every sufficiently large proportional repetition `k`, the three-symmetrization of the
`D k`-th power of the coarsened `(112)` constituent has a `dwz63Tau`-weight of at least
`dwz112LeafTerm ^ (3 D k)`, with `D = [2(L+G)]^3` the symmetric typed leaf's profile mass.

Proof sketch: `exists_eventually_cw112SymmetricLimitLowerTerm_le_certificate` supplies, past a
cutoff, a canonical cyclic degeneration certificate whose term dominates the normalized limit
term; `CyclicDegenerationCertificate.toTauValueCertificateSymThree` reads it as a value
certificate of `sym_3` of the same length, and `TauValueCertificate.hasTauWeight` turns that into
a weight for the `certificate.power`-th power.  The certificate's term is by definition the
`3 * power`-th root of its volume sum, so raising the domination to the `3 * power` cancels the
root exactly. -/
theorem exists_eventually_dwz112LeafHasTauWeight :
    ∃ N : ℕ, ∀ k : ℕ, N ≤ k →
      HasTauWeight K
        (Tensor.power (symThree K (cw112PartitionedTensor K 6).realize) (dwz112Mass * k))
        dwz63Tau (dwz112LeafTerm K ^ (3 * (dwz112Mass * k))) := by
  obtain ⟨N, hN⟩ :=
    exists_eventually_cw112SymmetricLimitLowerTerm_le_certificate K dwz63Tau 6
      dwz112L dwz112G (by norm_num) dwz112L_pos dwz112G_pos
      (dwz112InnerCopyBase_pos K) (dwz112InnerCopyBase_lt K)
  refine ⟨N, fun k hk ↦ ?_⟩
  obtain ⟨hkpos, seed, hnonempty, hterm⟩ := hN k hk
  set certificate := cw112SymmetricCanonicalDegenerationValueCertificate K dwz63Tau 6
    dwz112L dwz112G k (by norm_num) dwz112L_pos dwz112G_pos hkpos seed hnonempty with hcert
  -- the certificate's length is `D * k`
  have hpower : certificate.power = dwz112Mass * k := by
    rw [hcert, cw112SymmetricCanonicalDegenerationValueCertificate_power,
      RationalTypedLeaf.proportionalDepth_add_one _ hkpos,
      cw112SymmetricLeaf_profile_mass]
  -- the volume sum of the certificate is positive
  have hsumPos : 0 < matrixMultiplicationVolumePowerSum
      certificate.xSize certificate.ySize certificate.zSize dwz63Tau :=
    matrixMultiplicationVolumePowerSum_pos certificate.copies_pos certificate.xSize_pos
      certificate.ySize_pos certificate.zSize_pos dwz63Tau
  -- the certificate's term is the `3 * power`-th root of that volume sum
  have hroot : certificate.term ^ (3 * certificate.power) =
      matrixMultiplicationVolumePowerSum
        certificate.xSize certificate.ySize certificate.zSize dwz63Tau := by
    have hne : ((3 * certificate.power : ℕ) : ℝ) ≠ 0 := by
      have hp := certificate.power_pos
      have : 0 < 3 * certificate.power := by omega
      exact_mod_cast this.ne'
    -- ELABORATION RISK (low): `show` must unfold `CyclicDegenerationCertificate.term`,
    -- `CyclicExtractionCertificate.term` and `cyclicValueTerm`.  Fallback if it fails:
    --   `simp only [CyclicDegenerationCertificate.term, CyclicExtractionCertificate.term,
    --      cyclicValueTerm]` before the `rw`.
    show (matrixMultiplicationVolumePowerSum
        certificate.xSize certificate.ySize certificate.zSize dwz63Tau ^
        (((3 * certificate.power : ℕ) : ℝ))⁻¹) ^ (3 * certificate.power) = _
    rw [← Real.rpow_natCast (matrixMultiplicationVolumePowerSum
        certificate.xSize certificate.ySize certificate.zSize dwz63Tau ^
        (((3 * certificate.power : ℕ) : ℝ))⁻¹) (3 * certificate.power),
      ← Real.rpow_mul hsumPos.le, inv_mul_cancel₀ hne, Real.rpow_one]
  have hweight := (certificate.toTauValueCertificateSymThree).hasTauWeight dwz63Tau
  have hpowerEq : (certificate.toTauValueCertificateSymThree).power = certificate.power := rfl
  rw [hpowerEq, hpower] at hweight
  refine hweight.mono ?_
  have hle : dwz112LeafTerm K ≤ certificate.term := hterm
  -- ELABORATION RISK (low): `pow_le_pow_left` may be spelled `pow_le_pow_left₀` in this
  -- Mathlib revision.  Fallback: `by gcongr; exact (dwz112LeafTerm_pos K).le`.
  have hmono : dwz112LeafTerm K ^ (3 * certificate.power) ≤
      certificate.term ^ (3 * certificate.power) :=
    pow_le_pow_left₀ (dwz112LeafTerm_pos K).le hle _
  rw [hpower] at hmono
  calc dwz112LeafTerm K ^ (3 * (dwz112Mass * k)) ≤ certificate.term ^ (3 * (dwz112Mass * k)) :=
        hmono
    _ = matrixMultiplicationVolumePowerSum
          certificate.xSize certificate.ySize certificate.zSize dwz63Tau := by
        rw [← hpower]; exact hroot

/-! ## Transport to the coarse `(1,1,2)` constituent of the level-two source -/

/-- Exact restrictions pass through the three-symmetrization.  `symThree` is *by definition* the
external product of three leg-permuted copies, so this is `Restricts.external` twice over
`Restricts.permute`; the same two lines already appear inside
`cw112PowerCyclicProduct_restricts_indexedCyclicCTensors`. -/
theorem restricts_symThree_of_restricts {V : Leg → Type v} {W : Leg → Type w}
    [∀ c, AddCommMonoid (V c)] [∀ c, Module K (V c)]
    [∀ c, AddCommMonoid (W c)] [∀ c, Module K (W c)]
    {X : Tensor3 K V} {Y : Tensor3 K W} (h : Restricts X Y) :
    Restricts (symThree K X) (symThree K Y) :=
  (h.external (h.permute cycle)).external (h.permute cycle.symm)

/-- **The `tau`-weight, read on the coarse `(1,1,2)` constituent of the level-two source.**

`cwSquareConstituent_112_restricts_partitioned` restricts the coarse constituent
`(cwSquarePartitionedTensor K dwz63Q).constituent cwSquare112` onto the typed `(112)` partition
the value chain certifies, and `HasTauWeight` transports backwards along restrictions.

The object is a power of `symThree` of the constituent, and that is *forced*, not an artefact:
`[DuanWuZhou2022]` `note:T112` records that `T_{1,1,2}` is the only level-two component that is
not a matrix-multiplication tensor and therefore the only one without a non-rotational value
bound, so only its three-symmetrized value `V^{(3)}` is available.  Since
`cwSquareConstituent_121_isomorphic_cycleSymm` and `cwSquareConstituent_211_isomorphic_cycle`
identify the other two members of the orbit with the cyclic rotations of this one, a weight on
`symThree` of the `(1,1,2)` constituent *is* a weight on the external product of the `(1,1,2)`,
`(1,2,1)` and `(2,1,1)` constituents. -/
theorem exists_eventually_dwz112ConstituentHasTauWeight :
    ∃ N : ℕ, ∀ k : ℕ, N ≤ k →
      HasTauWeight K
        (Tensor.power
          (symThree K ((cwSquarePartitionedTensor K dwz63Q).constituent cwSquare112))
          (dwz112Mass * k))
        dwz63Tau (dwz112LeafTerm K ^ (3 * (dwz112Mass * k))) := by
  obtain ⟨N, hN⟩ := exists_eventually_dwz112LeafHasTauWeight K
  refine ⟨N, fun k hk ↦ (hN k hk).of_restricts ?_⟩
  -- ELABORATION RISK (low): `dwz63Q` must unfold to the literal `6`.  Fallback if the two
  -- `cw112PartitionedTensor` occurrences do not unify: prefix with `simp only [dwz63Q]`.
  exact Tensor.Restricts.power
    (restricts_symThree_of_restricts K
      (cwSquareConstituent_112_restricts_partitioned K dwz63Q)) _

/-- The same weight in the exponential shape the `hvalue` premise of
`exists_value_of_repairedStage_true` consumes: the published `(1,1,2)` component value, backed off
by `10 ^ (-22)` nats, raised to the leaf's total index length `3 D k`. -/
theorem exists_eventually_dwz112LeafHasTauWeight_exp :
    ∃ N : ℕ, ∀ k : ℕ, N ≤ k → ∃ value : ℝ, 0 < value ∧
      HasTauWeight K
        (Tensor.power (symThree K (cw112PartitionedTensor K 6).realize) (dwz112Mass * k))
        dwz63Tau value ∧
      Real.exp (dwz112LogValue - 1 / 10 ^ 22) ^ (3 * (dwz112Mass * k)) ≤ value := by
  obtain ⟨N, hN⟩ := exists_eventually_dwz112LeafHasTauWeight K
  refine ⟨N, fun k hk ↦ ⟨dwz112LeafTerm K ^ (3 * (dwz112Mass * k)),
    pow_pos (dwz112LeafTerm_pos K) _, hN k hk, ?_⟩⟩
  exact pow_le_pow_left₀ (Real.exp_nonneg _) (dwz112_exp_le_leafTerm K) _

end

end AlgebraicComplexity.Examples
