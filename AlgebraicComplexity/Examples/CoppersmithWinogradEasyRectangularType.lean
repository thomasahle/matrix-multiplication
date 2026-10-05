/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinogradEasyHashing
import AlgebraicComplexity.Analysis.ProportionalMultinomial

/-!
# The rectangular multiplicity type for the easy Coppersmith--Winograd tensor

`CoppersmithWinogradEasyHashing` runs the whole laser pipeline for the three-constituent easy CW
tensor `D_q` at the *equal* multiplicity type `easyEqualType k = fun _ ↦ k`, and ends at
`easyCW_omega_le_log : omega K ≤ log ((4/27)·(q+2)^3) / log q`.
Huang and Pan [HP98, Section 6.1, pp. 272--273] observe that the very same pipeline, run at an
*unequal* type, proves a rectangular bound.  This module generalizes the type layer.

## Huang--Pan's block shape

In the `(2+r)N`-th tensor power of the base algorithm they set (verbatim, p. 272):

* `x^{[I]} = 0` unless `I` has exactly `rN` indices of `0` and exactly `2N` indices of `1`;
* `y^{[J]} = 0` unless `J` has exactly `N` indices of `0` and exactly `(1+r)N` indices of `1`;
* and similarly for `z^{[K]}`.

The surviving triples number `((2+r)N; N, N, rN)` (a trinomial coefficient) and each block product
is a matrix product of size `(q^N, q^N, (q^N)^r)`, i.e. `⟨n, n, n^r⟩` for `n = q^N`.

In the block-address language of this repository a tensor factor is labelled by *which leg carries
the zero block*: `easyZeroAddress .X = cw011`, `easyZeroAddress .Y = cw101`,
`easyZeroAddress .Z = cw110`, with constituent dimensions `⟨1,1,q⟩`, `⟨q,1,1⟩`, `⟨1,q,1⟩`.
"`I` has `rN` zeros" is therefore "`cw011` occurs with multiplicity `rN`", and the Huang--Pan type
is the *denominator-free* profile

```
easyRectType a b : cw011 ↦ a,   cw101 ↦ b,   cw110 ↦ b
```

with `r = a / b` and word length `a + 2b`.  The resulting constituent dimensions are `q^b`, `q^b`,
`q^a` (`easyRectType_positiveWordProduct_m/n/p`), which is `⟨n, n, n^r⟩` for `n = q^b`, matching
Huang--Pan exactly; and `a = b` recovers the equal type (`easyRectType_self`) together with every
equal-type statement of `CoppersmithWinogradEasyHashing` (the `*_self` regression lemmas below).

## Main definitions and results

* `easyRectBlockType` / `easyRectType` -- Huang--Pan's `(a, b, b)` multiplicity profile;
* `easyRectTypeDepth`, `easyRectTypeWords`, `card_easyRectTypeWords` -- the word family and its
  exact trinomial cardinality;
* `easyRectType_positiveWordProduct_m/n/p` -- the rectangular dimension formulas `q^b, q^b, q^a`,
  stated at an arbitrary depth so that they specialize *definitionally* to the equal-type ones;
* `proportionalEntropyBase_easyRectType`,
  `easyRectType_entropyBase_pow_le_loss_mul_card` -- the method-of-types (Stirling) estimate
  `((a+2b)^{a+2b} / (a^a b^{2b}))^N ≤ loss · #words(aN, bN)`, which is Huang--Pan's
  "applying Stirling's formula to approximate `H`";
* `easyRectLegProjection_multiplicity`, `card_easyRectLegWordMapFiber` -- the leg-local label
  counts and the exact `2^{middle}` fiber size of the *whole* leg fiber;
* `easyRectLegMarginalType`, `easyRect_mappedType_eq`, `card_easyRectTypedWordMapFiber` -- the
  *type-restricted* leg fiber, whose exact size is `binom(2b, b)` on the `x` leg and
  `binom(a+b, a)` on the other two.  This is Huang--Pan's sharper competitor count `M`;
* `easyRectType_self`, `easyRectTypeDepth_self`, `easyEqualTypeWords_eq_rect`,
  `easyRectType_positiveWordProduct_m/n/p_self` -- the `r = 1` regressions against the existing
  equal-type pipeline.

## What was actually built (M-R6b, delivered)

This module supplies only the type layer.  The pipeline that consumes it is complete; the chain,
with the names to look for, is

1. `Examples/CoppersmithWinogradEasyRectangularHashing.lean` -- the rectangular selection and
   extraction, the hashing step, and the type-restricted competitor count
   `easyRectTypedFiberBound`;
2. `Examples/CoppersmithWinogradEasyRectangularRate.lean` -- the Huang--Pan schedule
   `(a, b) = (p·N, m·N)`, `N → ∞`, the removal of the three subexponential losses, and
   Schönhage's `τ ↓ ω` bootstrap, ending at `easyRect_master_inequality_of_fiberGrowth` (and its
   whole-fiber specialization `easyRect_master_inequality`);
3. `Examples/CoppersmithWinogradEasyRectangularBound.lean` --
   `huangPan_rectangularOmega_le_of_le_one`, **(6.2)** verbatim, and
   `huangPan_rectangularOmega_le_of_one_le`, the whole-fiber `r ≥ 1` branch with the weaker
   constant `2^(1+r) r^r`;
4. `Examples/CoppersmithWinogradEasyRectangularSharpBound.lean` --
   `huangPan_rectangularOmega_le_of_one_le_sharp`, **(6.1)** verbatim, run at the type-restricted
   competitor count of this module, with the numerical corollary `ω(1,1,2) < 3.3399`.

Two departures from the recipe an earlier draft of this note prescribed are worth recording,
because both were forced by the mathematics rather than by taste.

* **There is no single theorem `huangPan_rectangularOmega_le`.**  The `r ≥ 1` and `r ≤ 1` branches
  have genuinely different constants and different competitor counts, so (6.1) and (6.2) are
  separate statements in separate modules, as the next section explains.
* **The exponent packaging does not go through `rectangularOmega_le_of_certificates`.**  The
  schedule produces one geometric family per aspect ratio rather than a covering of every scale,
  so there is no covering hypothesis to discharge.  What the pipeline uses instead is
  `rpow_rectangularOmega_le_of_indexedDirectSum`
  (`MatrixMultiplication/RectangularAsymptoticSum.lean`), which compresses the whole indexed
  direct sum at a near-optimal `κ`-rectangular algorithm and reads the result through
  `rpow_rectangularOmega_le_of_borderRankLE` (`MatrixMultiplication/RectangularBini.lean`).

The rest of the recipe survived: the direct-sum step is
`Tensor.RankLE.matrixMultiplication_compression_general`
(`MatrixMultiplication/Compression.lean`), and the rational schedule is
`(a, b) = (r.num · N, r.den · N)` at fixed `(r.num, r.den)`, with
`Growth.le_of_pow_succ_le_subexponential_mul_pow_succ` cancelling the subexponential losses.

### The two competitor counts

The equal-type pipeline bounds a hashing competitor list by the *whole* leg fiber
(`PartitionHashEncoding.card_legFiber_legalTargets_le_card_wordMapFiber`), whose size is
`2^(number of middle labels)`; `card_easyRectLegWordMapFiber` computes this exactly.  For
`a ≤ b` (that is `r ≤ 1`) the maximum over legs is `2^(2b) = 4^b`, which is exactly Huang--Pan's
`M = 2·((2N; N, N)) + 1`, so **(6.2) is reachable with the whole fiber**.  For `a > b`
(that is `r > 1`) Huang--Pan instead use `M = 2·(((1+r)N; N, rN)) + 1`, the *type-restricted*
fiber, which is strictly smaller than `2^(a+b)` whenever `a ≠ b`.  That restricted count is
`card_easyRectTypedWordMapFiber` below; fed through
`PartitionHashEncoding.card_legFiber_legalTargets_le_card_typedWordMapFiber` it is what upgrades
the `r ≥ 1` branch to the sharp (6.1)
`ω(1,1,r) ≤ log ((1+r)^(1+r) (q+2)^(2+r) / (2+r)^(2+r)) / log q`
in `Examples/CoppersmithWinogradEasyRectangularSharpBound.lean`.  The whole-fiber form yields
only the weaker `ω(1,1,r) ≤ log (2^(1+r) r^r (q+2)^(2+r) / (2+r)^(2+r)) / log q`; the two agree at
`r = 1`, where both are `easyCW_omega_le_log`.

## References

* [HP98] X. Huang and V. Y. Pan, *Fast rectangular matrix multiplication and applications*,
  J. Complexity **14** (1998), 257--299; Section 6.1 (pp. 272--273) for (6.1) and Section 6.2
  (p. 274) for (6.2).
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor
open scoped BigOperators

universe u

/-! ## The rectangular multiplicity profile -/

/-- Huang--Pan's rectangular multiplicity profile on the ambient CW block addresses: the
`x`-distinguished address `cw011` gets multiplicity `a`, the other two get `b`.

With `a = r·N` and `b = N` this is exactly the Section 6.1 zeroing pattern: `rN` factors in which
the `x` variable carries the zero block, and `N` each for `y` and `z`. -/
def easyRectBlockType (a b : ℕ) : CWBlockAddress → ℕ :=
  fun s ↦ if s = cw011 then a else b

@[simp] theorem easyRectBlockType_cw011 (a b : ℕ) : easyRectBlockType a b cw011 = a :=
  if_pos rfl

@[simp] theorem easyRectBlockType_cw101 (a b : ℕ) : easyRectBlockType a b cw101 = b :=
  if_neg (by decide)

@[simp] theorem easyRectBlockType_cw110 (a b : ℕ) : easyRectBlockType a b cw110 = b :=
  if_neg (by decide)

/-- The rectangular multiplicity type on the three easy CW constituents. -/
def easyRectType (a b : ℕ) : easyBlockSupport → ℕ :=
  fun s ↦ easyRectBlockType a b s.1

@[simp] theorem easyRectType_apply (a b : ℕ) (s : easyBlockSupport) :
    easyRectType a b s = easyRectBlockType a b s.1 := rfl

@[simp] theorem easyRectType_zeroAddress_X (a b : ℕ) :
    easyRectType a b (easyZeroAddress .X) = a :=
  easyRectBlockType_cw011 a b

@[simp] theorem easyRectType_zeroAddress_Y (a b : ℕ) :
    easyRectType a b (easyZeroAddress .Y) = b :=
  easyRectBlockType_cw101 a b

@[simp] theorem easyRectType_zeroAddress_Z (a b : ℕ) :
    easyRectType a b (easyZeroAddress .Z) = b :=
  easyRectBlockType_cw110 a b

theorem easyRectType_pos {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (s : easyBlockSupport) :
    0 < easyRectType a b s := by
  unfold easyRectType easyRectBlockType
  split <;> assumption

/-- Total mass of the rectangular profile: the tensor power has `a + 2b` factors. -/
@[simp] theorem sum_easyRectType (a b : ℕ) :
    ∑ s : easyBlockSupport, easyRectType a b s = a + 2 * b := by
  have h : (∑ s : easyBlockSupport, easyRectType a b s) =
      ∑ s ∈ easyBlockSupport, easyRectBlockType a b s :=
    (Finset.sum_subtype easyBlockSupport (fun _ ↦ Iff.rfl) (easyRectBlockType a b)).symm
  rw [h, sum_easyBlockSupport, easyRectBlockType_cw011, easyRectBlockType_cw101,
    easyRectBlockType_cw110]
  ring

/-- `a + 2b - 1` is the positive-word depth representing a tensor power with `a + 2b` factors. -/
def easyRectTypeDepth (a b : ℕ) : ℕ := a + 2 * b - 1

theorem easyRectTypeDepth_add_one {a b : ℕ} (h : 0 < a + 2 * b) :
    easyRectTypeDepth a b + 1 = a + 2 * b := by
  unfold easyRectTypeDepth
  omega

/-- The rectangular profile really is a type of words of the right length. -/
theorem easyRectType_mem_types {a b : ℕ} (h : 0 < a + 2 * b) :
    easyRectType a b ∈ WordType.types easyBlockSupport (easyRectTypeDepth a b + 1) := by
  rw [WordType.mem_types, sum_easyRectType, easyRectTypeDepth_add_one h]

/-- Rectangular-type supported-address words in the `(a + 2b)`-fold easy tensor power. -/
noncomputable def easyRectTypeWords (a b : ℕ) :
    Finset (PositiveWord easyBlockSupport (easyRectTypeDepth a b)) :=
  positiveTypeClass easyBlockSupport (easyRectTypeDepth a b) (easyRectType a b)

/-- Exact trinomial size of the rectangular word family: `((a+2b); a, b, b)`.  This is the count
`((2+r)N; N, N, rN)` of Huang--Pan, p. 272. -/
theorem card_easyRectTypeWords {a b : ℕ} (h : 0 < a + 2 * b) :
    (easyRectTypeWords a b).card = Nat.multinomial Finset.univ (easyRectType a b) :=
  card_positiveTypeClass_eq_multinomial _ _ (easyRectType_mem_types h)

/-! ## The rectangular dimension formulas

These are the `r`-analogues of `easyEqualType_positiveWordProduct_m/n/p`.  They are stated at an
arbitrary depth `d`, so that specializing `a = b = k` and `d = easyEqualTypeDepth k` reproduces
the equal-type statements verbatim (see the regression section). -/

/-- In a rectangular-type word, the first matrix-multiplication dimension multiplies to `q^b`. -/
theorem easyRectType_positiveWordProduct_m (q a b d : ℕ)
    {word : PositiveWord easyBlockSupport d}
    (hword : word ∈ positiveTypeClass easyBlockSupport d (easyRectType a b)) :
    positiveWordProduct (easyConstituentM q) d word = q ^ b := by
  classical
  rw [positiveWordProduct_eq_prod_pow (a := easyRectType a b) (easyConstituentM q) hword]
  change (∏ s : easyBlockSupport,
    (cwConstituentDimensions q s.1).1 ^ easyRectBlockType a b s.1) = q ^ b
  calc
    (∏ s : easyBlockSupport,
        (cwConstituentDimensions q s.1).1 ^ easyRectBlockType a b s.1) =
        ∏ s ∈ easyBlockSupport,
          (cwConstituentDimensions q s).1 ^ easyRectBlockType a b s :=
      (Finset.prod_subtype easyBlockSupport (fun _ ↦ Iff.rfl)
        (fun s ↦ (cwConstituentDimensions q s).1 ^ easyRectBlockType a b s)).symm
    _ = q ^ b := by
      rw [prod_easyBlockSupport]
      simp

/-- In a rectangular-type word, the second matrix-multiplication dimension multiplies to `q^b`. -/
theorem easyRectType_positiveWordProduct_n (q a b d : ℕ)
    {word : PositiveWord easyBlockSupport d}
    (hword : word ∈ positiveTypeClass easyBlockSupport d (easyRectType a b)) :
    positiveWordProduct (easyConstituentN q) d word = q ^ b := by
  classical
  rw [positiveWordProduct_eq_prod_pow (a := easyRectType a b) (easyConstituentN q) hword]
  change (∏ s : easyBlockSupport,
    (cwConstituentDimensions q s.1).2.1 ^ easyRectBlockType a b s.1) = q ^ b
  calc
    (∏ s : easyBlockSupport,
        (cwConstituentDimensions q s.1).2.1 ^ easyRectBlockType a b s.1) =
        ∏ s ∈ easyBlockSupport,
          (cwConstituentDimensions q s).2.1 ^ easyRectBlockType a b s :=
      (Finset.prod_subtype easyBlockSupport (fun _ ↦ Iff.rfl)
        (fun s ↦ (cwConstituentDimensions q s).2.1 ^ easyRectBlockType a b s)).symm
    _ = q ^ b := by
      rw [prod_easyBlockSupport]
      simp

/-- In a rectangular-type word, the third matrix-multiplication dimension multiplies to `q^a`.
This is the stretched leg: with `a = rN`, `b = N` the block product is `⟨q^N, q^N, (q^N)^r⟩`. -/
theorem easyRectType_positiveWordProduct_p (q a b d : ℕ)
    {word : PositiveWord easyBlockSupport d}
    (hword : word ∈ positiveTypeClass easyBlockSupport d (easyRectType a b)) :
    positiveWordProduct (easyConstituentP q) d word = q ^ a := by
  classical
  rw [positiveWordProduct_eq_prod_pow (a := easyRectType a b) (easyConstituentP q) hword]
  change (∏ s : easyBlockSupport,
    (cwConstituentDimensions q s.1).2.2 ^ easyRectBlockType a b s.1) = q ^ a
  calc
    (∏ s : easyBlockSupport,
        (cwConstituentDimensions q s.1).2.2 ^ easyRectBlockType a b s.1) =
        ∏ s ∈ easyBlockSupport,
          (cwConstituentDimensions q s).2.2 ^ easyRectBlockType a b s :=
      (Finset.prod_subtype easyBlockSupport (fun _ ↦ Iff.rfl)
        (fun s ↦ (cwConstituentDimensions q s).2.2 ^ easyRectBlockType a b s)).symm
    _ = q ^ a := by
      rw [prod_easyBlockSupport]
      simp

/-- Typed-support form of the first rectangular dimension formula. -/
theorem easyTensorRectType_positiveWordProduct_m (K : Type u) [CommRing K] (q a b d : ℕ)
    (word : PositiveWord (easyPartitionedTensor K q).support d)
    (hword : word ∈ positiveTypeClass (easyPartitionedTensor K q).support d
      (easyRectType a b)) :
    positiveWordProduct (easyTensorConstituentM K q) d word = q ^ b := by
  change PositiveWord easyBlockSupport d at word
  exact easyRectType_positiveWordProduct_m q a b d hword

/-- Typed-support form of the second rectangular dimension formula. -/
theorem easyTensorRectType_positiveWordProduct_n (K : Type u) [CommRing K] (q a b d : ℕ)
    (word : PositiveWord (easyPartitionedTensor K q).support d)
    (hword : word ∈ positiveTypeClass (easyPartitionedTensor K q).support d
      (easyRectType a b)) :
    positiveWordProduct (easyTensorConstituentN K q) d word = q ^ b := by
  change PositiveWord easyBlockSupport d at word
  exact easyRectType_positiveWordProduct_n q a b d hword

/-- Typed-support form of the third rectangular dimension formula. -/
theorem easyTensorRectType_positiveWordProduct_p (K : Type u) [CommRing K] (q a b d : ℕ)
    (word : PositiveWord (easyPartitionedTensor K q).support d)
    (hword : word ∈ positiveTypeClass (easyPartitionedTensor K q).support d
      (easyRectType a b)) :
    positiveWordProduct (easyTensorConstituentP K q) d word = q ^ a := by
  change PositiveWord easyBlockSupport d at word
  exact easyRectType_positiveWordProduct_p q a b d hword

/-! ## Regression at `r = 1`

Every definition and every dimension formula above collapses to the existing equal-type one when
`a = b`.  This is the faithfulness check for the generalization. -/

/-- At `a = b = k` the rectangular profile *is* the equal profile. -/
@[simp] theorem easyRectType_self (k : ℕ) : easyRectType k k = easyEqualType k := by
  funext s
  unfold easyRectType easyRectBlockType easyEqualType
  split <;> rfl

/-- At `a = b = k` the rectangular depth *is* the equal-type depth `3k - 1`. -/
@[simp] theorem easyRectTypeDepth_self (k : ℕ) :
    easyRectTypeDepth k k = easyEqualTypeDepth k := by
  unfold easyRectTypeDepth easyEqualTypeDepth
  omega

/-- The equal-type word family is the rectangular family at `a = b = k`. -/
theorem easyEqualTypeWords_eq_rect (k : ℕ) :
    easyEqualTypeWords k =
      positiveTypeClass easyBlockSupport (easyEqualTypeDepth k) (easyRectType k k) := by
  unfold easyEqualTypeWords
  rw [easyRectType_self]

/-- Regression: the rectangular first-dimension formula at `a = b = k` is exactly
`easyEqualType_positiveWordProduct_m`. -/
theorem easyRectType_positiveWordProduct_m_self (q k : ℕ)
    (word : PositiveWord easyBlockSupport (easyEqualTypeDepth k))
    (hword : word ∈ easyEqualTypeWords k) :
    positiveWordProduct (easyConstituentM q) (easyEqualTypeDepth k) word = q ^ k :=
  easyRectType_positiveWordProduct_m q k k _
    (by rwa [← easyEqualTypeWords_eq_rect])

/-- Regression: the rectangular second-dimension formula at `a = b = k` is exactly
`easyEqualType_positiveWordProduct_n`. -/
theorem easyRectType_positiveWordProduct_n_self (q k : ℕ)
    (word : PositiveWord easyBlockSupport (easyEqualTypeDepth k))
    (hword : word ∈ easyEqualTypeWords k) :
    positiveWordProduct (easyConstituentN q) (easyEqualTypeDepth k) word = q ^ k :=
  easyRectType_positiveWordProduct_n q k k _
    (by rwa [← easyEqualTypeWords_eq_rect])

/-- Regression: the rectangular third-dimension formula at `a = b = k` is exactly
`easyEqualType_positiveWordProduct_p`. -/
theorem easyRectType_positiveWordProduct_p_self (q k : ℕ)
    (word : PositiveWord easyBlockSupport (easyEqualTypeDepth k))
    (hword : word ∈ easyEqualTypeWords k) :
    positiveWordProduct (easyConstituentP q) (easyEqualTypeDepth k) word = q ^ k :=
  easyRectType_positiveWordProduct_p q k k _
    (by rwa [← easyEqualTypeWords_eq_rect])

/-- Regression: the rectangular trinomial count at `a = b = k` is the equal-type multinomial. -/
theorem card_easyRectTypeWords_self {k : ℕ} (hk : 0 < k) :
    (easyRectTypeWords k k).card = (easyEqualTypeWords k).card := by
  rw [card_easyRectTypeWords (by omega), card_easyEqualTypeWords hk, easyRectType_self]

/-! ## The method-of-types (Stirling) estimate for the rectangular profile

Huang--Pan approximate the trinomial `((2+r)N; N, N, rN)` by Stirling's formula.  The library
form of that step is `WordType.proportionalEntropyBase_pow_le_loss_mul_multinomial`, applied to
the base profile `easyRectType a b` scaled by `N`. -/

/-- Total mass of the rectangular profile. -/
@[simp] theorem profileMass_easyRectType (a b : ℕ) :
    WordType.profileMass (easyRectType a b) = a + 2 * b := by
  unfold WordType.profileMass
  exact sum_easyRectType a b

/-- Scaling the rectangular profile scales its two parameters. -/
@[simp] theorem proportionalCounts_easyRectType (a b N : ℕ) :
    WordType.proportionalCounts (easyRectType a b) N = easyRectType (a * N) (b * N) := by
  funext s
  by_cases h : (s : CWBlockAddress) = cw011 <;>
    simp [WordType.proportionalCounts, easyRectType, easyRectBlockType, h]

/-- The entropy growth base of the rectangular profile is Huang--Pan's trinomial base
`(a + 2b)^(a + 2b) / (a^a · b^(2b))`; at `a = r`, `b = 1` this is `(2+r)^(2+r) / r^r`. -/
theorem proportionalEntropyBase_easyRectType {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    WordType.proportionalEntropyBase (easyRectType a b) =
      ((a + 2 * b : ℕ) : ℝ) ^ (a + 2 * b) / ((a : ℝ) ^ a * (b : ℝ) ^ (2 * b)) := by
  have hane : ((a : ℝ)) ≠ 0 := by positivity
  have hbne : ((b : ℝ)) ≠ 0 := by positivity
  have hene : (Real.exp 1) ≠ 0 := Real.exp_ne_zero 1
  have hprod :
      (∏ s : easyBlockSupport, WordType.factorialEntropyTerm (easyRectType a b s)) =
        WordType.factorialEntropyTerm a *
          (WordType.factorialEntropyTerm b * WordType.factorialEntropyTerm b) := by
    have h : (∏ s : easyBlockSupport, WordType.factorialEntropyTerm (easyRectType a b s)) =
        ∏ s ∈ easyBlockSupport, WordType.factorialEntropyTerm (easyRectBlockType a b s) :=
      (Finset.prod_subtype easyBlockSupport (fun _ ↦ Iff.rfl)
        (fun s ↦ WordType.factorialEntropyTerm (easyRectBlockType a b s))).symm
    rw [h, prod_easyBlockSupport, easyRectBlockType_cw011, easyRectBlockType_cw101,
      easyRectBlockType_cw110]
  unfold WordType.proportionalEntropyBase
  rw [hprod, profileMass_easyRectType]
  unfold WordType.factorialEntropyTerm
  simp only [div_pow]
  have hee : (Real.exp 1) ^ (a + 2 * b) =
      Real.exp 1 ^ a * (Real.exp 1 ^ b * Real.exp 1 ^ b) := by
    rw [two_mul, pow_add, pow_add]
  have hbb : ((b : ℝ)) ^ (2 * b) = (b : ℝ) ^ b * (b : ℝ) ^ b := by
    rw [two_mul, pow_add]
  rw [hee, hbb]
  field_simp

/-- **Method of types for the rectangular profile.**  The Huang--Pan trinomial base, raised to the
`N`-th power, is at most an explicit subexponential loss times the exact number of rectangular
words at the scaled profile `(a·N, b·N)`.  This is the Stirling step of [HP98, p. 273]. -/
theorem easyRectType_entropyBase_pow_le_loss_mul_card {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    {N : ℕ} (hN : 0 < N) :
    (((a + 2 * b : ℕ) : ℝ) ^ (a + 2 * b) / ((a : ℝ) ^ a * (b : ℝ) ^ (2 * b))) ^ N ≤
      WordType.proportionalMultinomialLoss (easyRectType a b) N *
        ((easyRectTypeWords (a * N) (b * N)).card : ℝ) := by
  haveI : Nonempty easyBlockSupport := ⟨easyZeroAddress .X⟩
  have hmul :
      ((easyRectTypeWords (a * N) (b * N)).card : ℝ) =
        (Nat.multinomial Finset.univ
          (WordType.proportionalCounts (easyRectType a b) N) : ℝ) := by
    rw [proportionalCounts_easyRectType,
      card_easyRectTypeWords (a := a * N) (b := b * N) (by positivity)]
  rw [hmul, ← proportionalEntropyBase_easyRectType ha hb]
  exact WordType.proportionalEntropyBase_pow_le_loss_mul_multinomial
    (easyRectType a b) N (easyRectType_pos ha hb) hN

/-- The loss in the rectangular method-of-types estimate is subexponential in `N`. -/
theorem easyRectType_proportionalMultinomialLoss_subexponential (a b : ℕ) :
    Growth.Subexponential
      (WordType.proportionalMultinomialLoss (easyRectType a b)) :=
  WordType.proportionalMultinomialLoss_subexponential _

/-! ## Leg-local label counts

These generalize `easyLegProjection_multiplicity` and `card_easyLegWordMapFiber`, and are what the
hashing stage of M-R6b consumes.  Unlike in the equal case the counts depend on the leg. -/

/-- Number of zero labels the rectangular type puts on leg `c`: `a` on the `x` leg, `b` on the
other two. -/
def easyRectLegZeroCount (a b : ℕ) (c : Leg) : ℕ :=
  easyRectType a b (easyZeroAddress c)

/-- Number of middle labels the rectangular type puts on leg `c`: `2b` on the `x` leg, `a + b` on
the other two. -/
def easyRectLegMiddleCount (a b : ℕ) : Leg → ℕ
  | .X => 2 * b
  | .Y => a + b
  | .Z => a + b

@[simp] theorem easyRectLegZeroCount_X (a b : ℕ) : easyRectLegZeroCount a b .X = a :=
  easyRectType_zeroAddress_X a b
@[simp] theorem easyRectLegZeroCount_Y (a b : ℕ) : easyRectLegZeroCount a b .Y = b :=
  easyRectType_zeroAddress_Y a b
@[simp] theorem easyRectLegZeroCount_Z (a b : ℕ) : easyRectLegZeroCount a b .Z = b :=
  easyRectType_zeroAddress_Z a b

theorem easyRectLegCount_add (a b : ℕ) (c : Leg) :
    easyRectLegZeroCount a b c + easyRectLegMiddleCount a b c = a + 2 * b := by
  cases c <;>
    simp only [easyRectLegZeroCount_X, easyRectLegZeroCount_Y, easyRectLegZeroCount_Z,
      easyRectLegMiddleCount] <;> omega

/-- A leg projection of a rectangular-type word carries `easyRectLegZeroCount a b c` zero labels
and `easyRectLegMiddleCount a b c` middle labels (and no final labels). -/
theorem easyRectLegProjection_multiplicity (a b d : ℕ)
    (w : PositiveWord easyBlockSupport d)
    (hw : w ∈ positiveTypeClass easyBlockSupport d (easyRectType a b)) (c : Leg)
    (β : CWBlock) :
    WordType.multiplicity
        (fun i ↦ (positiveWordEquiv easyBlockSupport d w i).1 c) β =
      match β with
      | .zero => easyRectLegZeroCount a b c
      | .middle => easyRectLegMiddleCount a b c
      | .last => 0 := by
  change WordType.multiplicity
    ((fun s : easyBlockSupport ↦ s.1 c) ∘
      positiveWordEquiv easyBlockSupport d w) β = _
  rw [WordType.multiplicity_comp_eq_sum_letterFiber]
  have htype := mem_positiveTypeClass.mp hw
  simp_rw [htype]
  cases β with
  | zero =>
      rw [easyLegLetterFiber_zero, Finset.sum_singleton]
      rfl
  | middle =>
      show _ = easyRectLegMiddleCount a b c
      rw [easyLegLetterFiber_middle]
      have hsplit := Finset.add_sum_erase (Finset.univ : Finset easyBlockSupport)
        (easyRectType a b) (Finset.mem_univ (easyZeroAddress c))
      have htotal := sum_easyRectType a b
      have hzero : easyRectType a b (easyZeroAddress c) = easyRectLegZeroCount a b c := rfl
      have := easyRectLegCount_add a b c
      omega
  | last => rw [easyLegLetterFiber_last, Finset.sum_empty]

/-- Exact size of the fiber above a fixed leg word of a rectangular-type source word:
`2^(number of middle labels on that leg)`.  On the `x` leg this is `4^b`; on the other two it is
`2^(a+b)`.  It is the quantity Huang--Pan call `M` (p. 273), up to their sharper trinomial
restriction (see the module doc). -/
theorem card_easyRectLegWordMapFiber (a b d : ℕ)
    (w : PositiveWord easyBlockSupport d)
    (hw : w ∈ positiveTypeClass easyBlockSupport d (easyRectType a b)) (c : Leg) :
    (WordType.wordMapFiber (fun s : easyBlockSupport ↦ s.1 c)
      (positiveWordEquiv CWBlock d
        (PartitionHashEncoding.supportWordAddress
          (A := fun _ : Leg ↦ CWBlock) (support := easyBlockSupport) d w c))).card =
      2 ^ easyRectLegMiddleCount a b c := by
  classical
  rw [WordType.card_wordMapFiber]
  rw [PartitionHashEncoding.positiveWordEquiv_supportWordAddress
    (A := fun _ : Leg ↦ CWBlock) (support := easyBlockSupport) d w c]
  rw [WordType.prod_word_eq_prod_pow
    (x := fun β : CWBlock ↦
      (WordType.letterFiber (fun s : easyBlockSupport ↦ s.1 c) β).card)
    (word := fun i ↦
      (positiveWordEquiv easyBlockSupport d w i).1 c)]
  rw [show (Finset.univ : Finset CWBlock) = {.zero, .middle, .last} by decide]
  simp [card_easyLegLetterFiber, easyRectLegProjection_multiplicity a b d w hw c]

/-! ## The type-restricted leg fiber

`card_easyRectLegWordMapFiber` counts *all* lifts of a leg word to the easy support.  Huang--Pan's
competitor list is the smaller set of lifts that still have the selected joint type
`easyRectType a b`, i.e. `WordType.typedWordMapFiber`.  Its exact size is computed here by the
division-free double counting `WordType.card_targetType_mul_card_typedWordMapFiber`: the marginal
type class of the leg word times the typed fiber is the joint type class, and both type classes
are multinomial coefficients, so the fiber is the single binomial coefficient that remains. -/

/-- The pushforward of the rectangular profile along the leg-`c` projection: `zero` occurs
`easyRectLegZeroCount a b c` times, `middle` occurs `easyRectLegMiddleCount a b c` times, and the
final CW block never occurs. -/
def easyRectLegMarginalType (a b : ℕ) (c : Leg) : CWBlock → ℕ
  | .zero => easyRectLegZeroCount a b c
  | .middle => easyRectLegMiddleCount a b c
  | .last => 0

/-- The leg-`c` marginal of the rectangular profile really is `easyRectLegMarginalType`. -/
theorem easyRect_mappedType_eq (a b : ℕ) (c : Leg) :
    WordType.mappedType (fun s : easyBlockSupport ↦ s.1 c) (easyRectType a b) =
      easyRectLegMarginalType a b c := by
  classical
  funext β
  show ∑ s ∈ WordType.letterFiber (fun s : easyBlockSupport ↦ s.1 c) β,
      easyRectType a b s = _
  cases β with
  | zero =>
      rw [easyLegLetterFiber_zero, Finset.sum_singleton]
      rfl
  | middle =>
      show _ = easyRectLegMiddleCount a b c
      rw [easyLegLetterFiber_middle]
      have hsplit := Finset.add_sum_erase (Finset.univ : Finset easyBlockSupport)
        (easyRectType a b) (Finset.mem_univ (easyZeroAddress c))
      have htotal := sum_easyRectType a b
      have hzero : easyRectType a b (easyZeroAddress c) = easyRectLegZeroCount a b c := rfl
      have := easyRectLegCount_add a b c
      omega
  | last => rw [easyLegLetterFiber_last, Finset.sum_empty]; rfl

/-- The leg-`c` marginal profile has the same total mass `a + 2b` as the rectangular profile. -/
@[simp] theorem sum_easyRectLegMarginalType (a b : ℕ) (c : Leg) :
    ∑ β : CWBlock, easyRectLegMarginalType a b c β = a + 2 * b := by
  rw [← easyRect_mappedType_eq a b c, WordType.sum_mappedType, sum_easyRectType]

/-- The multiplicity type of a leg word of a rectangular-type source word is the leg marginal. -/
theorem easyRectLegWord_multiplicity (a b d : ℕ)
    (w : PositiveWord easyBlockSupport d)
    (hw : w ∈ positiveTypeClass easyBlockSupport d (easyRectType a b)) (c : Leg) :
    WordType.multiplicity
        (positiveWordEquiv CWBlock d
          (PartitionHashEncoding.supportWordAddress
            (A := fun _ : Leg ↦ CWBlock) (support := easyBlockSupport) d w c)) =
      easyRectLegMarginalType a b c := by
  rw [PartitionHashEncoding.positiveWordEquiv_supportWordAddress
    (A := fun _ : Leg ↦ CWBlock) (support := easyBlockSupport) d w c]
  change WordType.multiplicity
    ((fun s : easyBlockSupport ↦ s.1 c) ∘ positiveWordEquiv easyBlockSupport d w) = _
  rw [WordType.multiplicity_comp_eq_mappedType, mem_positiveTypeClass.mp hw,
    easyRect_mappedType_eq]

/-- Huang--Pan's sharp competitor count on leg `c`: the binomial coefficient `binom(2b, b)` on the
`x` leg and `binom(a+b, a)` on the other two.  With `a = rN`, `b = N` the latter is the trinomial
`((1+r)N; N, rN)` of [HP98, p. 273]. -/
def easyRectLegTypedFiber (a b : ℕ) : Leg → ℕ
  | .X => Nat.choose (2 * b) b
  | .Y => Nat.choose (a + b) a
  | .Z => Nat.choose (a + b) a

/-- Factorial product of the rectangular profile. -/
theorem prod_factorial_easyRectType (a b : ℕ) :
    (∏ s : easyBlockSupport, (easyRectType a b s).factorial) =
      a.factorial * (b.factorial * b.factorial) := by
  have h : (∏ s : easyBlockSupport, (easyRectType a b s).factorial) =
      ∏ s ∈ easyBlockSupport, (easyRectBlockType a b s).factorial :=
    (Finset.prod_subtype easyBlockSupport (fun _ ↦ Iff.rfl)
      (fun s ↦ (easyRectBlockType a b s).factorial)).symm
  rw [h, prod_easyBlockSupport, easyRectBlockType_cw011, easyRectBlockType_cw101,
    easyRectBlockType_cw110]

/-- Factorial product of the leg marginal profile. -/
theorem prod_factorial_easyRectLegMarginalType (a b : ℕ) (c : Leg) :
    (∏ β : CWBlock, (easyRectLegMarginalType a b c β).factorial) =
      (easyRectLegZeroCount a b c).factorial * (easyRectLegMiddleCount a b c).factorial := by
  rw [show (Finset.univ : Finset CWBlock) = {CWBlock.zero, CWBlock.middle, CWBlock.last} by
    decide]
  simp [easyRectLegMarginalType]

/-- The factorial identity behind the typed fiber count: dividing the marginal factorial product
by the joint one leaves exactly the binomial coefficient `easyRectLegTypedFiber`. -/
theorem factorial_easyRectLegMarginal_eq (a b : ℕ) (c : Leg) :
    (easyRectLegZeroCount a b c).factorial * (easyRectLegMiddleCount a b c).factorial =
      a.factorial * (b.factorial * b.factorial) * easyRectLegTypedFiber a b c := by
  cases c with
  | X =>
      have h := Nat.choose_mul_factorial_mul_factorial (show b ≤ 2 * b by omega)
      rw [show 2 * b - b = b from by omega] at h
      simp only [easyRectLegZeroCount_X, easyRectLegMiddleCount, easyRectLegTypedFiber]
      calc a.factorial * (2 * b).factorial
          = a.factorial * (Nat.choose (2 * b) b * b.factorial * b.factorial) := by rw [h]
        _ = a.factorial * (b.factorial * b.factorial) * Nat.choose (2 * b) b := by ring
  | Y =>
      have h := Nat.choose_mul_factorial_mul_factorial (show a ≤ a + b by omega)
      rw [show a + b - a = b from by omega] at h
      simp only [easyRectLegZeroCount_Y, easyRectLegMiddleCount, easyRectLegTypedFiber]
      calc b.factorial * (a + b).factorial
          = b.factorial * (Nat.choose (a + b) a * a.factorial * b.factorial) := by rw [h]
        _ = a.factorial * (b.factorial * b.factorial) * Nat.choose (a + b) a := by ring
  | Z =>
      have h := Nat.choose_mul_factorial_mul_factorial (show a ≤ a + b by omega)
      rw [show a + b - a = b from by omega] at h
      simp only [easyRectLegZeroCount_Z, easyRectLegMiddleCount, easyRectLegTypedFiber]
      calc b.factorial * (a + b).factorial
          = b.factorial * (Nat.choose (a + b) a * a.factorial * b.factorial) := by rw [h]
        _ = a.factorial * (b.factorial * b.factorial) * Nat.choose (a + b) a := by ring

/-- The joint rectangular multinomial factors as the leg marginal multinomial times the binomial
`easyRectLegTypedFiber`.  This is the division-free form of `((a+2b); a,b,b) / ((a+2b); z, m)`. -/
theorem multinomial_easyRectType_eq (a b : ℕ) (c : Leg) :
    Nat.multinomial (Finset.univ : Finset easyBlockSupport) (easyRectType a b) =
      easyRectLegTypedFiber a b c *
        Nat.multinomial (Finset.univ : Finset CWBlock) (easyRectLegMarginalType a b c) := by
  have h1 := Nat.multinomial_spec (Finset.univ : Finset easyBlockSupport) (easyRectType a b)
  have h2 := Nat.multinomial_spec (Finset.univ : Finset CWBlock)
    (easyRectLegMarginalType a b c)
  rw [prod_factorial_easyRectType, sum_easyRectType] at h1
  rw [prod_factorial_easyRectLegMarginalType, sum_easyRectLegMarginalType,
    factorial_easyRectLegMarginal_eq] at h2
  have hpos : 0 < a.factorial * (b.factorial * b.factorial) :=
    Nat.mul_pos (Nat.factorial_pos a) (Nat.mul_pos (Nat.factorial_pos b) (Nat.factorial_pos b))
  refine Nat.eq_of_mul_eq_mul_left hpos ?_
  calc a.factorial * (b.factorial * b.factorial) *
        Nat.multinomial (Finset.univ : Finset easyBlockSupport) (easyRectType a b)
      = (a + 2 * b).factorial := h1
    _ = a.factorial * (b.factorial * b.factorial) * easyRectLegTypedFiber a b c *
        Nat.multinomial (Finset.univ : Finset CWBlock) (easyRectLegMarginalType a b c) := h2.symm
    _ = a.factorial * (b.factorial * b.factorial) *
        (easyRectLegTypedFiber a b c *
          Nat.multinomial (Finset.univ : Finset CWBlock)
            (easyRectLegMarginalType a b c)) := by ring

/-- **Exact type-restricted leg fiber.**  Among the lifts of a leg word of the rectangular
marginal type, exactly `easyRectLegTypedFiber a b c` again have the joint type `easyRectType a b`:
`binom(2b, b)` on the `x` leg and `binom(a+b, a)` on the other two.

Proof sketch: the joint type class is partitioned by its leg words, all typed fibers over leg
words of one marginal type have equal size
(`WordType.card_targetType_mul_card_typedWordMapFiber`), and both type classes are multinomial
coefficients, whose quotient is `multinomial_easyRectType_eq`. -/
theorem card_easyRectTypedWordMapFiber {a b d : ℕ} (hd : d + 1 = a + 2 * b) (c : Leg)
    (target : Fin (d + 1) → CWBlock)
    (htarget : WordType.multiplicity target = easyRectLegMarginalType a b c) :
    (WordType.typedWordMapFiber (fun s : easyBlockSupport ↦ s.1 c) (easyRectType a b)
        target).card = easyRectLegTypedFiber a b c := by
  classical
  have hdouble := WordType.card_targetType_mul_card_typedWordMapFiber
    (fun s : easyBlockSupport ↦ s.1 c) (easyRectType a b) target
    (by rw [WordType.mem_typeClass, htarget, easyRect_mappedType_eq])
  rw [easyRect_mappedType_eq] at hdouble
  have hmarg : (WordType.typeClass (d + 1) (easyRectLegMarginalType a b c)).card =
      Nat.multinomial Finset.univ (easyRectLegMarginalType a b c) :=
    WordType.card_typeClass_eq_multinomial _
      (by rw [WordType.mem_types, sum_easyRectLegMarginalType, hd])
  have hrect : (WordType.typeClass (d + 1) (easyRectType a b)).card =
      Nat.multinomial Finset.univ (easyRectType a b) :=
    WordType.card_typeClass_eq_multinomial _
      (by rw [WordType.mem_types, sum_easyRectType, hd])
  rw [hmarg, hrect, multinomial_easyRectType_eq a b c] at hdouble
  refine Nat.eq_of_mul_eq_mul_left
    (Nat.multinomial_pos (Finset.univ : Finset CWBlock) (easyRectLegMarginalType a b c)) ?_
  rw [hdouble, Nat.mul_comm]

/-- Regression: at `a = b = k` the type-restricted leg fiber is the central binomial coefficient
`binom(2k, k)` on every leg. -/
theorem easyRectLegTypedFiber_self (k : ℕ) (c : Leg) :
    easyRectLegTypedFiber k k c = Nat.choose (2 * k) k := by
  cases c <;> simp only [easyRectLegTypedFiber, show k + k = 2 * k from by omega]

/-- Regression: at `a = b = k` the leg fiber has the equal-type size `4^k`. -/
theorem card_easyRectLegWordMapFiber_self (k d : ℕ)
    (w : PositiveWord easyBlockSupport d)
    (hw : w ∈ positiveTypeClass easyBlockSupport d (easyRectType k k)) (c : Leg) :
    (WordType.wordMapFiber (fun s : easyBlockSupport ↦ s.1 c)
      (positiveWordEquiv CWBlock d
        (PartitionHashEncoding.supportWordAddress
          (A := fun _ : Leg ↦ CWBlock) (support := easyBlockSupport) d w c))).card =
      4 ^ k := by
  rw [card_easyRectLegWordMapFiber k k d w hw c]
  have h : easyRectLegMiddleCount k k c = 2 * k := by
    cases c <;> simp only [easyRectLegMiddleCount] <;> omega
  rw [h, pow_mul]
  norm_num

end AlgebraicComplexity.Examples
