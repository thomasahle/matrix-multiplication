/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinogradRectangularType
import AlgebraicComplexity.Tensor.PartitionedPower
import AlgebraicComplexity.Tensor.PartitionedProduct

/-!
# The mixed `CW_7`/`CW_6` power and its rectangular type layer

This module is stage 1 of Coppersmith's [Cop97] `α > 0.294`.  Every previous client of the laser
pipeline in this repository takes a tensor power of *one* base tensor and selects *one*
multiplicity type in it.  Coppersmith 1997 instead takes an external product of two different
Coppersmith--Winograd tensors, `CW_7` and `CW_6`, in prescribed proportions, and selects a
multiplicity type on each half independently.  This module supplies that mixed power, its
block-address alphabet, and the type layer over it, modelled throughout on the single-`q` layer
`Examples/CoppersmithWinogradRectangularType.lean`.

## What the paper says, and how it is read here

The formulas of [Cop97] are Type-3 bitmap fonts and do not extract from the PDF; the prose does.
Everything below is reconstructed from the prose plus the internal consistency checks recorded in
this section.  Section and page numbers refer to [Cop97].

* Section 3, p. 43.  The base construction is [CW90, Eq. (10)] for `q ∈ {6, 7}`, called `C_q`
  there and `coppersmithWinograd K q` here.  It "uses `q + 2` multiplications ... The number of
  `x`-variables is also `q + 2`.  This agreement is necessary to achieve the near equality between
  the number of operations and the number of `x`-variables in the larger algorithm."  Its six
  constituents and their matrix-multiplication shapes are already formalized:
  `cwConstituentDimensions q` gives `⟨1,1,q⟩` at `cw011`, `⟨q,1,1⟩` at `cw101`, `⟨1,q,1⟩` at
  `cw110`, and `⟨1,1,1⟩` at the three corners `cw200`, `cw020`, `cw002`.

* Section 4, pp. 44--45.  "Take the tensor product of `9a` copies of construction `C_7` and `8b`
  copies of construction `C_6`."  *The two multipliers of the visible digits `9` and `8` are
  italic letters and are lost by text extraction; they are independent.*  Reading them as a
  common `r` (i.e. `9r` and `8r`) is consistent with every extracted fragment but yields
  `α = 0.294404`, whereas the paper's Theorem 1 states `α = 0.29462…`; two independent
  multipliers reproduce `0.294628905…` on the nose (numeric check, not formalized here; see the
  stage-1 report).  Corroboration from the prose: p. 45 says "We have chosen `_`, `_`, `_`, and
  `_` to make the number of `y`-blocks approximately equal to the number of `x`-blocks" -- four
  quantities, which are exactly `a`, `b`, `s`, `t` below, and which the roadmap already records
  as "a four-parameter type selection".

  The retained blocks are, in the notation of this file (`u`, `v`, `s`, `t` with `a = 2u`,
  `b = v`):

  - `x`-variables: on the `9a = 18u` left indices exactly `a` from block `0`, `7a` from block `1`
    and `a` from block `2`; on the `8b = 8v` right indices exactly `b`, `6b`, `b`.  These are the
    multinomial-maximizing proportions, which is Coppersmith's "selecting multinomial coefficients
    to maximize the total number of `x`-variables", borrowed from [Cop82].
  - `y`- and `z`-variables: on the left `9a/2 + s`, `9a/2 - 2s`, `s`; on the right `4b + t`,
    `4b - 2t`, `t`.

  Compatibility (`x`-, `y`- and `z`-block indices sum to `2` in each of the `9a + 8b` positions)
  then forces the per-position constituent counts, which the paper lists on p. 45: on the left
  `7a/2` copies of `⟨1,7,1⟩`, `7a/2` of `⟨7,1,1⟩`, `a - 2s` of `⟨1,1,7⟩`, and `s`, `s`, `a` of
  `⟨1,1,1⟩`; on the right `3b` of `⟨1,6,1⟩`, `3b` of `⟨6,1,1⟩`, `b - 2t` of `⟨1,1,6⟩`, and
  `t`, `t`, `b` of `⟨1,1,1⟩`.  In the block-address language of this repository that is exactly
  `cwRectType` on each half, at parameters

  ```text
  left  (q = 7):  cwRectType (a - 2s) (7a/2) s a   =  coppersmithLeftType u s   (a = 2u)
  right (q = 6):  cwRectType (b - 2t) (3b)   t b   =  coppersmithRightType v t  (b = v)
  ```

  and `coppersmithLeft_marginal_X`, `coppersmithLeft_marginal_YZ`,
  `coppersmithRight_marginal_X`, `coppersmithRight_marginal_YZ` *prove* that the leg marginals of
  these profiles are the paper's four retention patterns `(a, 7a, a)`, `(9a/2 + s, 9a/2 - 2s, s)`,
  `(b, 6b, b)`, `(4b + t, 4b - 2t, t)`.  That the paper's constituent list and the paper's
  retention patterns are the two faces of one profile is the arithmetic content of p. 45, and it is
  what those four theorems check.

* Section 4, p. 45, and Section 5, pp. 46--47.  The surviving matrix product has size
  `⟨M, M, P⟩` with `M = 7^{7a/2} 6^{3b}` and `P = 7^{a-2s} 6^{b-2t}`; here
  `coppersmithMixed_wordProduct_m/n/p`.  The number of multiplications is `9^{9a} 8^{8b}`, the
  number of `x`-blocks is `(9a; a, 7a, a)·(8b; b, 6b, b)` and the number of `y`-blocks is
  `(9a; 9a/2+s, 9a/2-2s, s)·(8b; 4b+t, 4b-2t, t)`; here `card_coppersmithMixedTypeWords` and
  `card_cwMixedTypeWords`.  Section 5 is the modulus, the Salem--Spencer set, the random weights
  `w_j`, the three block functions and the duplicate pruning; none of that is in this module.

## Note on the word count

The mixed alphabet `CWMixedAddress` tags each letter by the half it comes from, but the *positions*
of the two halves are fixed, not chosen.  Consequently the number of mixed words of a given
profile pair is the **product** `multinomial g₇ * multinomial g₆`
(`card_cwMixedTypeWords`), which is smaller than `Nat.multinomial` of the tagged profile
`cwMixedType g₇ g₆` by the factor `(n₇ + n₆).choose n₇`.  The tagged profile is retained only
because it packages the eight parameters and their masses; it must never be handed to a
type-class cardinality lemma.

## Main definitions and results

* `cwMixedPower` -- the partitioned mixed power
  `(CW_{q₇})^{⊗(n₇+1)} ⊗ (CW_{q₆})^{⊗(n₆+1)}`, with `card_cwMixedPower_support`,
  `mem_cwMixedPower_support` and `cwMixedPower_realize_isomorphic`;
* `cwMixedTypeWords`, `card_cwMixedTypeWords` -- the mixed word family and its exact
  cardinality, a product of two multinomials;
* `cwMixedWordProduct`, `cwMixed_wordProduct_m/n/p` -- the constituent dimension formulas
  `q₇^{b₇} q₆^{b₆}`, `q₇^{b₇} q₆^{b₆}`, `q₇^{a₇} q₆^{a₆}`;
* `cwMixedMarginalType`, `cwMixed_multiplicity_legWord_left/right` -- the leg marginals, per half
  and summed;
* `cwMixedTypedFiber`, `card_cwMixedTypedFiber` -- the type-restricted leg fiber, which
  factorizes across the two halves;
* `coppersmithLeftType`, `coppersmithRightType` and the four marginal theorems -- Coppersmith's
  four-parameter selection and the check that it is the paper's;
* `card_cwMixedTypeWords_cwRect_right_trivial`, `cwMixed_wordProduct_m/n/p_right_trivial`,
  `cwMixedMarginalType_cwRect_right_trivial` -- **the `k₆ = 0` regression**: with an empty second
  half every statement above becomes verbatim the corresponding `cwRect*` statement of
  `Examples/CoppersmithWinogradRectangularType.lean`.

## Plan for stages 2 and 3

Stage 2 (extraction) and stage 3 (rate) should reuse, unchanged:

* `MatrixMultiplication/RectangularAsymptoticSum.lean` -- the self-referential bootstrap.  The
  final scalar step of [Cop97] is a fixed point: from `N ⊙ ⟨M, M, P⟩ ⊴ R` with `R ≈ N·M²` one gets
  `⟨kM, kM, k^α P⟩` for `k^{2+ε} ≤ N`, and the fixed point of
  `α ↦ (α log k + log P)/(log k + log M)` is `α = log P / log M`.  This is exactly the
  "compress at a near-optimal rectangular algorithm, then let `τ ↓ ω(1,1,κ)`" device that
  `RectangularAsymptoticSum.lean` isolates, and it is the reason the answer is `log P / log M` and
  not the non-self-referential `log P / (log M + ½ log N) = 0.2053…`.
* `MatrixMultiplication/RectangularBini.lean` -- `rectangularOmega_le_log_of_borderRankLE`, the
  `Nat.clog`-density packager, needs a single certificate rather than a covering family and is the
  right endpoint for a construction that produces one certificate per `(u, v, s, t, r)`.
* `cwRect_master_inequality_of_fiberGrowth`'s envelope parameterization and
  `Analysis/BinomialEntropyEnvelope.lean` -- the method-of-types estimate.  Here the entropy
  envelope is needed **twice, multiplicatively**: the mixed loss is a product of two
  `WordType.proportionalMultinomialLoss` factors, and a product of two subexponential losses is
  subexponential.  Nothing in the envelope layer has to change.
* The whole `cwRect*` layer of `Examples/CoppersmithWinogradRectangularType.lean`, one half at a
  time: this module reduces every mixed count to two `cwRect*` counts.

New work, in order of expected difficulty:

1. **Mixed hashing.**  `Examples/CoppersmithWinogradRectangularHashing.lean` and
   `MatrixMultiplication/PartitionedPowerHashing.lean` hash the positions of a power of one
   tensor.  Coppersmith's weights `w_j` run over all `9a + 8b` positions of the *mixed* power, so
   the hashing layer has to accept a position set that is a disjoint union of two regions with
   different constituent data.  The block sums that the Salem--Spencer argument needs are still
   sums over all positions, so the natural generalization is to make the hashing input a
   `PartitionedTensor` external product rather than a power; `cwMixedPower` is already in that
   form, and `Tensor/PartitionedProduct.lean` supplies the support and realization bridges.
2. **Two-sided leg selection.**  The single-`q` layer chooses one leg (`cwRectLegTypedFiber_le_Y`
   for `r ≥ 1`, `cwRectLegTypedFiber_le_X` for `r ≤ 1`).  In the mixed layer the competitor count
   is the product `cwRectLegTypedFiber ... .Y * cwRectLegTypedFiber ... .Y` and the *same* leg has
   to be selected on both halves, so the two halves' Schur-type comparisons must be combined
   before the leg is chosen; `card_cwMixedTypedFiber` is the statement they combine into.
3. **The near-equality constraint.**  `R ≤ N·M^{2+ε}` with `R = 9^{9a} 8^{8b}` and
   `N·M² = (#x-blocks)·7^{7a} 6^{6b}` holds for *every* `(a, b)` because `C_q` has `q + 2`
   multiplications and `q + 2` `x`-variables; that is the one place where the paper's remark on
   p. 43 is used, and it is a two-factor maximal-multinomial-term estimate.
4. The numeric optimization of `α` over `(a : b, s/a, t/b)` and the `α > 0.294` endpoint.

**Expected hardest obstruction:** (1), and specifically the *pruning* step of p. 47 ("Some
`y`-blocks will be associated with two or more surviving `x`-blocks.  When this happens we set to
zero all but one"), run over a two-region position set.  The existing pruning machinery
(`Tensor/CompatibilityZeroing.lean`, `Tensor/PartitionedExtraction.lean`) is stated for a power
and its block addresses are words over one alphabet; over a mixed power the addresses are *pairs*
of words, and the compatibility relation is coordinatewise on both halves at once.  The
combinatorics is unchanged, but every zeroing lemma that is currently phrased in terms of
`positiveSupportWordBlockAddress` has to be rephrased for
`ProductBlockIndex`-addressed supports.  That is a mechanical but wide refactor, and it is the
reason stage 2 is a separate milestone rather than a continuation of this one.

## References

* [Cop82] D. Coppersmith, *Rapid multiplication of rectangular matrices*, SIAM J. Comput. **11**
  (1982), 467--471.
* [Cop97] D. Coppersmith, *Rectangular matrix multiplication revisited*, J. Complexity **13**
  (1997), 42--49; Sections 3--5 and Theorem 1 (p. 48).
* [CW90] D. Coppersmith and S. Winograd, *Matrix multiplication via arithmetic progressions*,
  J. Symbolic Comput. **9** (1990), 251--280; Eq. (10).
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor
open scoped BigOperators

universe u

/-! ## The mixed power and its block-address alphabet -/

/-- **The mixed Coppersmith--Winograd power.**  The external product of `n₇ + 1` copies of
`CW_{q₇}` and `n₆ + 1` copies of `CW_{q₆}`, kept in partitioned form.  Its block-address alphabet
is `ProductBlockIndex`, i.e. a *pair* of block-label words, one per half; that pairing is what
lets the two halves carry independent multiplicity types. -/
noncomputable def cwMixedPower (K : Type u) [CommRing K] (q₇ q₆ n₇ n₆ : ℕ) :
    PartitionedTensor (K := K)
      (A := ProductBlockIndex (fun _ : Leg ↦ PositiveWord CWBlock n₇)
        (fun _ : Leg ↦ PositiveWord CWBlock n₆))
      (ProductBlockSpace K (PositivePowerBlockSpace K (CWPartitionBlockSpace K q₇) n₇)
        (PositivePowerBlockSpace K (CWPartitionBlockSpace K q₆) n₆)) :=
  ((cwPartitionedTensor K q₇).positivePower n₇).external
    ((cwPartitionedTensor K q₆).positivePower n₆)

variable (K : Type u) [CommRing K]

/-- A block address of the mixed power is supported exactly when both of its halves are. -/
@[simp] theorem mem_cwMixedPower_support (q₇ q₆ n₇ n₆ : ℕ)
    (address : BlockAddress (ProductBlockIndex (fun _ : Leg ↦ PositiveWord CWBlock n₇)
      (fun _ : Leg ↦ PositiveWord CWBlock n₆))) :
    address ∈ (cwMixedPower K q₇ q₆ n₇ n₆).support ↔
      (fun c ↦ (address c).1) ∈ ((cwPartitionedTensor K q₇).positivePower n₇).support ∧
        (fun c ↦ (address c).2) ∈ ((cwPartitionedTensor K q₆).positivePower n₆).support :=
  PartitionedTensor.mem_external_support _ _ address

/-- The mixed power has one supported constituent for every pair of supported address words. -/
theorem card_cwMixedPower_support (q₇ q₆ n₇ n₆ : ℕ) :
    (cwMixedPower K q₇ q₆ n₇ n₆).support.card =
      cwBlockSupport.card ^ (n₇ + 1) * cwBlockSupport.card ^ (n₆ + 1) := by
  rw [cwMixedPower, PartitionedTensor.card_external_support,
    PartitionedTensor.card_positivePower_support,
    PartitionedTensor.card_positivePower_support]
  rfl

/-- Every supported block of the mixed power comes from a pair of supported CW address words,
one for each half. -/
theorem exists_supportWordPair_of_mem_cwMixedPower_support (q₇ q₆ n₇ n₆ : ℕ)
    {address : BlockAddress (ProductBlockIndex (fun _ : Leg ↦ PositiveWord CWBlock n₇)
      (fun _ : Leg ↦ PositiveWord CWBlock n₆))}
    (haddress : address ∈ (cwMixedPower K q₇ q₆ n₇ n₆).support) :
    ∃ (w₇ : PositiveWord (cwPartitionedTensor K q₇).support n₇)
      (w₆ : PositiveWord (cwPartitionedTensor K q₆).support n₆),
      positiveSupportWordBlockAddress
          (cwPartitionedTensor K q₇).support n₇ w₇ = (fun c ↦ (address c).1) ∧
        positiveSupportWordBlockAddress
          (cwPartitionedTensor K q₆).support n₆ w₆ = (fun c ↦ (address c).2) := by
  obtain ⟨hleft, hright⟩ := (mem_cwMixedPower_support K q₇ q₆ n₇ n₆ address).mp haddress
  obtain ⟨w₇, hw₇⟩ :=
    PartitionedTensor.exists_positiveSupportWord_of_mem_positivePower_support _ n₇ hleft
  obtain ⟨w₆, hw₆⟩ :=
    PartitionedTensor.exists_positiveSupportWord_of_mem_positivePower_support _ n₆ hright
  exact ⟨w₇, w₆, hw₇, hw₆⟩

/-- **The mixed power realizes the external product of the two Coppersmith--Winograd powers.**
Composed with `cwPartitionedTensor_isomorphic` this identifies the realized tensor with
`(CW_{q₇})^{⊗(n₇+1)} ⊗ (CW_{q₆})^{⊗(n₆+1)}`. -/
theorem cwMixedPower_realize_isomorphic (q₇ q₆ n₇ n₆ : ℕ) :
    Isomorphic
        (Tensor.external (Tensor.power (cwPartitionedTensor K q₇).realize (n₇ + 1))
          (Tensor.power (cwPartitionedTensor K q₆).realize (n₆ + 1)))
        (cwMixedPower K q₇ q₆ n₇ n₆).realize :=
  (Isomorphic.external
      (Isomorphic.power_partitionedPositivePower (cwPartitionedTensor K q₇) n₇)
      (Isomorphic.power_partitionedPositivePower (cwPartitionedTensor K q₆) n₆)).trans
    (Isomorphic.partitionedExternal _ _)

/-! ## Tagged profiles -/

/-- The tagged letter alphabet of a mixed power: a supported CW block address together with the
half it occurs in.  See the note above: this alphabet packages the two profiles, but the mixed
*word count* is a product of two multinomials, not a multinomial over this alphabet. -/
abbrev CWMixedAddress := cwBlockSupport ⊕ cwBlockSupport

/-- A pair of multiplicity profiles, packaged over the tagged alphabet. -/
def cwMixedType (g₇ g₆ : cwBlockSupport → ℕ) : CWMixedAddress → ℕ := Sum.elim g₇ g₆

@[simp] theorem cwMixedType_inl (g₇ g₆ : cwBlockSupport → ℕ) (s : cwBlockSupport) :
    cwMixedType g₇ g₆ (.inl s) = g₇ s := rfl

@[simp] theorem cwMixedType_inr (g₇ g₆ : cwBlockSupport → ℕ) (s : cwBlockSupport) :
    cwMixedType g₇ g₆ (.inr s) = g₆ s := rfl

/-- The mixed power has `(∑ g₇) + (∑ g₆)` positions. -/
@[simp] theorem sum_cwMixedType (g₇ g₆ : cwBlockSupport → ℕ) :
    ∑ s, cwMixedType g₇ g₆ s = (∑ s, g₇ s) + (∑ s, g₆ s) :=
  Fintype.sum_sum_type _

/-! ## Mixed words and their exact count -/

/-- Words of the mixed power carrying a prescribed profile on each half. -/
noncomputable def cwMixedTypeWords (g₇ g₆ : cwBlockSupport → ℕ) (n₇ n₆ : ℕ) :
    Finset ((Fin n₇ → cwBlockSupport) × (Fin n₆ → cwBlockSupport)) :=
  (WordType.typeClass n₇ g₇) ×ˢ (WordType.typeClass n₆ g₆)

@[simp] theorem mem_cwMixedTypeWords {g₇ g₆ : cwBlockSupport → ℕ} {n₇ n₆ : ℕ}
    {w : (Fin n₇ → cwBlockSupport) × (Fin n₆ → cwBlockSupport)} :
    w ∈ cwMixedTypeWords g₇ g₆ n₇ n₆ ↔
      WordType.multiplicity w.1 = g₇ ∧ WordType.multiplicity w.2 = g₆ := by
  rw [cwMixedTypeWords, Finset.mem_product, WordType.mem_typeClass, WordType.mem_typeClass]

/-- **Exact mixed word count.**  The two halves contribute independently, so the count is the
product of the two multinomials -- Coppersmith's `(9a; a, 7a, a)·(8b; b, 6b, b)` for the
`x`-blocks and `(9a; 9a/2+s, 9a/2-2s, s)·(8b; 4b+t, 4b-2t, t)` for the `y`-blocks. -/
theorem card_cwMixedTypeWords {g₇ g₆ : cwBlockSupport → ℕ} {n₇ n₆ : ℕ}
    (h₇ : ∑ s, g₇ s = n₇) (h₆ : ∑ s, g₆ s = n₆) :
    (cwMixedTypeWords g₇ g₆ n₇ n₆).card =
      Nat.multinomial Finset.univ g₇ * Nat.multinomial Finset.univ g₆ := by
  rw [cwMixedTypeWords, Finset.card_product,
    WordType.card_typeClass_eq_multinomial _ (WordType.mem_types.mpr h₇),
    WordType.card_typeClass_eq_multinomial _ (WordType.mem_types.mpr h₆)]

theorem cwMixedTypeWords_nonempty {g₇ g₆ : cwBlockSupport → ℕ} {n₇ n₆ : ℕ}
    (h₇ : ∑ s, g₇ s = n₇) (h₆ : ∑ s, g₆ s = n₆) :
    (cwMixedTypeWords g₇ g₆ n₇ n₆).Nonempty := by
  rw [← Finset.card_pos, card_cwMixedTypeWords h₇ h₆]
  exact Nat.mul_pos (Nat.multinomial_pos _ _) (Nat.multinomial_pos _ _)

/-! ## The constituent dimension formulas -/

/-- First matrix-multiplication dimension of the `CW_q` constituent at a supported address. -/
def cwDimM (q : ℕ) (s : cwBlockSupport) : ℕ := (cwConstituentDimensions q s.1).1

/-- Second matrix-multiplication dimension of the `CW_q` constituent at a supported address. -/
def cwDimN (q : ℕ) (s : cwBlockSupport) : ℕ := (cwConstituentDimensions q s.1).2.1

/-- Third matrix-multiplication dimension of the `CW_q` constituent at a supported address. -/
def cwDimP (q : ℕ) (s : cwBlockSupport) : ℕ := (cwConstituentDimensions q s.1).2.2

theorem cwDimM_eq (q : ℕ) : cwDimM q = cwTensorConstituentM K q := rfl

theorem cwDimN_eq (q : ℕ) : cwDimN q = cwTensorConstituentN K q := rfl

theorem cwDimP_eq (q : ℕ) : cwDimP q = cwTensorConstituentP K q := rfl

theorem prod_pow_cwDimM_cwRectType (q a b e f : ℕ) :
    (∏ s : cwBlockSupport, cwDimM q s ^ cwRectType a b e f s) = q ^ b := by
  calc
    _ = ∏ s ∈ cwBlockSupport,
        (cwConstituentDimensions q s).1 ^ cwRectAddressCount a b e f s :=
      (Finset.prod_subtype cwBlockSupport (fun _ ↦ Iff.rfl)
        (fun s ↦ (cwConstituentDimensions q s).1 ^ cwRectAddressCount a b e f s)).symm
    _ = q ^ b := by
      rw [prod_cwBlockSupport]
      simp

theorem prod_pow_cwDimN_cwRectType (q a b e f : ℕ) :
    (∏ s : cwBlockSupport, cwDimN q s ^ cwRectType a b e f s) = q ^ b := by
  calc
    _ = ∏ s ∈ cwBlockSupport,
        (cwConstituentDimensions q s).2.1 ^ cwRectAddressCount a b e f s :=
      (Finset.prod_subtype cwBlockSupport (fun _ ↦ Iff.rfl)
        (fun s ↦ (cwConstituentDimensions q s).2.1 ^ cwRectAddressCount a b e f s)).symm
    _ = q ^ b := by
      rw [prod_cwBlockSupport]
      simp

theorem prod_pow_cwDimP_cwRectType (q a b e f : ℕ) :
    (∏ s : cwBlockSupport, cwDimP q s ^ cwRectType a b e f s) = q ^ a := by
  calc
    _ = ∏ s ∈ cwBlockSupport,
        (cwConstituentDimensions q s).2.2 ^ cwRectAddressCount a b e f s :=
      (Finset.prod_subtype cwBlockSupport (fun _ ↦ Iff.rfl)
        (fun s ↦ (cwConstituentDimensions q s).2.2 ^ cwRectAddressCount a b e f s)).symm
    _ = q ^ a := by
      rw [prod_cwBlockSupport]
      simp

/-- Product of a numerical constituent parameter along a mixed word: the two halves use their own
parameter. -/
def cwMixedWordProduct (x₇ x₆ : cwBlockSupport → ℕ) {n₇ n₆ : ℕ}
    (w : (Fin n₇ → cwBlockSupport) × (Fin n₆ → cwBlockSupport)) : ℕ :=
  (∏ i, x₇ (w.1 i)) * (∏ i, x₆ (w.2 i))

/-- A mixed word product depends only on the pair of multiplicity types. -/
theorem cwMixedWordProduct_eq_prod_pow (x₇ x₆ g₇ g₆ : cwBlockSupport → ℕ) {n₇ n₆ : ℕ}
    {w : (Fin n₇ → cwBlockSupport) × (Fin n₆ → cwBlockSupport)}
    (hw : w ∈ cwMixedTypeWords g₇ g₆ n₇ n₆) :
    cwMixedWordProduct x₇ x₆ w = (∏ s, x₇ s ^ g₇ s) * (∏ s, x₆ s ^ g₆ s) := by
  obtain ⟨h₇, h₆⟩ := mem_cwMixedTypeWords.mp hw
  rw [cwMixedWordProduct, WordType.prod_word_eq_prod_pow x₇ w.1,
    WordType.prod_word_eq_prod_pow x₆ w.2, h₇, h₆]

/-- **First dimension of a mixed rectangular block:** `q₇^{b₇} · q₆^{b₆}`.  At Coppersmith's
parameters this is `M = 7^{7a/2} 6^{3b}`. -/
theorem cwMixed_wordProduct_m (q₇ q₆ a₇ b₇ e₇ f₇ a₆ b₆ e₆ f₆ : ℕ) {n₇ n₆ : ℕ}
    {w : (Fin n₇ → cwBlockSupport) × (Fin n₆ → cwBlockSupport)}
    (hw : w ∈ cwMixedTypeWords (cwRectType a₇ b₇ e₇ f₇) (cwRectType a₆ b₆ e₆ f₆) n₇ n₆) :
    cwMixedWordProduct (cwDimM q₇) (cwDimM q₆) w = q₇ ^ b₇ * q₆ ^ b₆ := by
  rw [cwMixedWordProduct_eq_prod_pow _ _ _ _ hw, prod_pow_cwDimM_cwRectType,
    prod_pow_cwDimM_cwRectType]

/-- **Second dimension of a mixed rectangular block:** `q₇^{b₇} · q₆^{b₆}`. -/
theorem cwMixed_wordProduct_n (q₇ q₆ a₇ b₇ e₇ f₇ a₆ b₆ e₆ f₆ : ℕ) {n₇ n₆ : ℕ}
    {w : (Fin n₇ → cwBlockSupport) × (Fin n₆ → cwBlockSupport)}
    (hw : w ∈ cwMixedTypeWords (cwRectType a₇ b₇ e₇ f₇) (cwRectType a₆ b₆ e₆ f₆) n₇ n₆) :
    cwMixedWordProduct (cwDimN q₇) (cwDimN q₆) w = q₇ ^ b₇ * q₆ ^ b₆ := by
  rw [cwMixedWordProduct_eq_prod_pow _ _ _ _ hw, prod_pow_cwDimN_cwRectType,
    prod_pow_cwDimN_cwRectType]

/-- **Third (short) dimension of a mixed rectangular block:** `q₇^{a₇} · q₆^{a₆}`.  At
Coppersmith's parameters this is `P = 7^{a-2s} 6^{b-2t}`, and the whole point of the construction
is that `log P / log M` is the achievable `α`. -/
theorem cwMixed_wordProduct_p (q₇ q₆ a₇ b₇ e₇ f₇ a₆ b₆ e₆ f₆ : ℕ) {n₇ n₆ : ℕ}
    {w : (Fin n₇ → cwBlockSupport) × (Fin n₆ → cwBlockSupport)}
    (hw : w ∈ cwMixedTypeWords (cwRectType a₇ b₇ e₇ f₇) (cwRectType a₆ b₆ e₆ f₆) n₇ n₆) :
    cwMixedWordProduct (cwDimP q₇) (cwDimP q₆) w = q₇ ^ a₇ * q₆ ^ a₆ := by
  rw [cwMixedWordProduct_eq_prod_pow _ _ _ _ hw, prod_pow_cwDimP_cwRectType,
    prod_pow_cwDimP_cwRectType]

/-! ## The leg marginals -/

/-- The leg-`c` marginal of a mixed profile, obtained by forgetting which half a position lies in.
This is the marginal seen by the hashing stage, whose weights run over all positions. -/
noncomputable def cwMixedMarginalType (g₇ g₆ : cwBlockSupport → ℕ) (c : Leg) (β : CWBlock) : ℕ :=
  WordType.mappedType (fun s : cwBlockSupport ↦ s.1 c) g₇ β +
    WordType.mappedType (fun s : cwBlockSupport ↦ s.1 c) g₆ β

/-- The leg word of the first half of a mixed word has the first half's marginal type. -/
theorem cwMixed_multiplicity_legWord_left {g₇ g₆ : cwBlockSupport → ℕ} {n₇ n₆ : ℕ}
    {w : (Fin n₇ → cwBlockSupport) × (Fin n₆ → cwBlockSupport)}
    (hw : w ∈ cwMixedTypeWords g₇ g₆ n₇ n₆) (c : Leg) :
    WordType.multiplicity ((fun s : cwBlockSupport ↦ s.1 c) ∘ w.1) =
      WordType.mappedType (fun s : cwBlockSupport ↦ s.1 c) g₇ := by
  rw [WordType.multiplicity_comp_eq_mappedType, (mem_cwMixedTypeWords.mp hw).1]

/-- The leg word of the second half of a mixed word has the second half's marginal type. -/
theorem cwMixed_multiplicity_legWord_right {g₇ g₆ : cwBlockSupport → ℕ} {n₇ n₆ : ℕ}
    {w : (Fin n₇ → cwBlockSupport) × (Fin n₆ → cwBlockSupport)}
    (hw : w ∈ cwMixedTypeWords g₇ g₆ n₇ n₆) (c : Leg) :
    WordType.multiplicity ((fun s : cwBlockSupport ↦ s.1 c) ∘ w.2) =
      WordType.mappedType (fun s : cwBlockSupport ↦ s.1 c) g₆ := by
  rw [WordType.multiplicity_comp_eq_mappedType, (mem_cwMixedTypeWords.mp hw).2]

/-- Total mass of a mixed leg marginal is the total number of positions. -/
@[simp] theorem sum_cwMixedMarginalType (g₇ g₆ : cwBlockSupport → ℕ) (c : Leg) :
    ∑ β, cwMixedMarginalType g₇ g₆ c β = (∑ s, g₇ s) + (∑ s, g₆ s) := by
  simp only [cwMixedMarginalType]
  rw [Finset.sum_add_distrib, WordType.sum_mappedType, WordType.sum_mappedType]

/-- The mixed marginal of a pair of rectangular profiles is the sum of the two rectangular leg
marginals. -/
theorem cwMixedMarginalType_cwRect (a₇ b₇ e₇ f₇ a₆ b₆ e₆ f₆ : ℕ) (c : Leg) :
    cwMixedMarginalType (cwRectType a₇ b₇ e₇ f₇) (cwRectType a₆ b₆ e₆ f₆) c =
      fun β ↦ cwRectMarginalType a₇ b₇ e₇ f₇ c β + cwRectMarginalType a₆ b₆ e₆ f₆ c β := by
  funext β
  simp only [cwMixedMarginalType]
  rw [cwRect_mappedType_eq, cwRect_mappedType_eq]

/-! ## The type-restricted leg fiber -/

/-- The mixed competitor set: lifts of a *pair* of leg words that still carry the selected pair of
joint types. -/
noncomputable def cwMixedTypedFiber (g₇ g₆ : cwBlockSupport → ℕ) {n₇ n₆ : ℕ} (c : Leg)
    (t₇ : Fin n₇ → CWBlock) (t₆ : Fin n₆ → CWBlock) :
    Finset ((Fin n₇ → cwBlockSupport) × (Fin n₆ → cwBlockSupport)) :=
  (WordType.typedWordMapFiber (fun s : cwBlockSupport ↦ s.1 c) g₇ t₇) ×ˢ
    (WordType.typedWordMapFiber (fun s : cwBlockSupport ↦ s.1 c) g₆ t₆)

/-- **The mixed competitor count factorizes.**  It is the product of the two single-`q` counts of
`Examples/CoppersmithWinogradRectangularType.lean`, which is why stage 2 can reuse the Schur-type
leg comparisons of that module one half at a time. -/
theorem card_cwMixedTypedFiber {a₇ b₇ e₇ f₇ a₆ b₆ e₆ f₆ d₇ d₆ : ℕ}
    (hd₇ : d₇ + 1 = a₇ + 2 * b₇ + 2 * e₇ + f₇) (hd₆ : d₆ + 1 = a₆ + 2 * b₆ + 2 * e₆ + f₆)
    (c : Leg) (t₇ : Fin (d₇ + 1) → CWBlock) (t₆ : Fin (d₆ + 1) → CWBlock)
    (ht₇ : WordType.multiplicity t₇ = cwRectMarginalType a₇ b₇ e₇ f₇ c)
    (ht₆ : WordType.multiplicity t₆ = cwRectMarginalType a₆ b₆ e₆ f₆ c) :
    (cwMixedTypedFiber (cwRectType a₇ b₇ e₇ f₇) (cwRectType a₆ b₆ e₆ f₆) c t₇ t₆).card =
      cwRectLegTypedFiber a₇ b₇ e₇ f₇ c * cwRectLegTypedFiber a₆ b₆ e₆ f₆ c := by
  rw [cwMixedTypedFiber, Finset.card_product,
    card_cwRectTypedWordMapFiber hd₇ c t₇ ht₇, card_cwRectTypedWordMapFiber hd₆ c t₆ ht₆]

/-! ## Coppersmith's four-parameter selection

The `q = 7` half has `9a = 18u` positions and the `q = 6` half has `8b = 8v` positions; `s` and
`t` are the two block-`2` counts on the `y` leg.  All four parameters are independent, and it is
the freedom in `u : v` -- not just in `s` and `t` -- that produces `0.29462…` rather than
`0.294404…`. -/

/-- Coppersmith's retained profile on the `q = 7` half, `a = 2u`:
`cwRectType (a - 2s) (7a/2) s a`. -/
def coppersmithLeftType (u s : ℕ) : cwBlockSupport → ℕ :=
  cwRectType (2 * (u - s)) (7 * u) s (2 * u)

/-- Coppersmith's retained profile on the `q = 6` half, `b = v`:
`cwRectType (b - 2t) (3b) t b`. -/
def coppersmithRightType (v t : ℕ) : cwBlockSupport → ℕ :=
  cwRectType (v - 2 * t) (3 * v) t v

/-- The `q = 7` half occupies `9a = 18u` positions. -/
@[simp] theorem sum_coppersmithLeftType {u s : ℕ} (hs : s ≤ u) :
    ∑ w, coppersmithLeftType u s w = 18 * u := by
  rw [coppersmithLeftType, sum_cwRectType]
  omega

/-- The `q = 6` half occupies `8b = 8v` positions. -/
@[simp] theorem sum_coppersmithRightType {v t : ℕ} (ht : 2 * t ≤ v) :
    ∑ w, coppersmithRightType v t w = 8 * v := by
  rw [coppersmithRightType, sum_cwRectType]
  omega

/-- The paper's `x`-retention pattern on the `q = 7` half: `(a, 7a, a)` with `a = 2u`. -/
def coppersmithLeftMarginalX (u : ℕ) : CWBlock → ℕ
  | .zero => 2 * u
  | .middle => 14 * u
  | .last => 2 * u

/-- The paper's `y`- and `z`-retention pattern on the `q = 7` half:
`(9a/2 + s, 9a/2 - 2s, s)` with `a = 2u`. -/
def coppersmithLeftMarginalYZ (u s : ℕ) : CWBlock → ℕ
  | .zero => 9 * u + s
  | .middle => 9 * u - 2 * s
  | .last => s

/-- The paper's `x`-retention pattern on the `q = 6` half: `(b, 6b, b)` with `b = v`. -/
def coppersmithRightMarginalX (v : ℕ) : CWBlock → ℕ
  | .zero => v
  | .middle => 6 * v
  | .last => v

/-- The paper's `y`- and `z`-retention pattern on the `q = 6` half: `(4b + t, 4b - 2t, t)`. -/
def coppersmithRightMarginalYZ (v t : ℕ) : CWBlock → ℕ
  | .zero => 4 * v + t
  | .middle => 4 * v - 2 * t
  | .last => t

/-- **The `x` leg of the `q = 7` half is retained exactly as [Cop97, p. 44] prescribes.** -/
theorem coppersmithLeft_marginal_X {u s : ℕ} (hs : s ≤ u) :
    WordType.mappedType (fun w : cwBlockSupport ↦ w.1 .X) (coppersmithLeftType u s) =
      coppersmithLeftMarginalX u := by
  rw [coppersmithLeftType, cwRect_mappedType_eq]
  funext β
  cases β <;> simp only [cwRectMarginalType, coppersmithLeftMarginalX] <;> omega

/-- **The `y` and `z` legs of the `q = 7` half are retained exactly as [Cop97, p. 44]
prescribes.** -/
theorem coppersmithLeft_marginal_YZ {u s : ℕ} (hs : s ≤ u) (c : Leg) (hc : c ≠ .X) :
    WordType.mappedType (fun w : cwBlockSupport ↦ w.1 c) (coppersmithLeftType u s) =
      coppersmithLeftMarginalYZ u s := by
  rw [coppersmithLeftType, cwRect_mappedType_eq]
  funext β
  cases c
  · exact absurd rfl hc
  · cases β <;> simp only [cwRectMarginalType, coppersmithLeftMarginalYZ] <;> omega
  · cases β <;> simp only [cwRectMarginalType, coppersmithLeftMarginalYZ] <;> omega

/-- **The `x` leg of the `q = 6` half is retained exactly as [Cop97, p. 44] prescribes.** -/
theorem coppersmithRight_marginal_X {v t : ℕ} (ht : 2 * t ≤ v) :
    WordType.mappedType (fun w : cwBlockSupport ↦ w.1 .X) (coppersmithRightType v t) =
      coppersmithRightMarginalX v := by
  rw [coppersmithRightType, cwRect_mappedType_eq]
  funext β
  cases β <;> simp only [cwRectMarginalType, coppersmithRightMarginalX] <;> omega

/-- **The `y` and `z` legs of the `q = 6` half are retained exactly as [Cop97, p. 44]
prescribes.** -/
theorem coppersmithRight_marginal_YZ {v t : ℕ} (ht : 2 * t ≤ v) (c : Leg) (hc : c ≠ .X) :
    WordType.mappedType (fun w : cwBlockSupport ↦ w.1 c) (coppersmithRightType v t) =
      coppersmithRightMarginalYZ v t := by
  rw [coppersmithRightType, cwRect_mappedType_eq]
  funext β
  cases c
  · exact absurd rfl hc
  · cases β <;> simp only [cwRectMarginalType, coppersmithRightMarginalYZ] <;> omega
  · cases β <;> simp only [cwRectMarginalType, coppersmithRightMarginalYZ] <;> omega

/-- Coppersmith's mixed word family: `18u + 8v` positions, profile `coppersmithLeftType` on the
first `18u` and `coppersmithRightType` on the last `8v`. -/
noncomputable def coppersmithMixedTypeWords (u s v t : ℕ) :
    Finset ((Fin (18 * u) → cwBlockSupport) × (Fin (8 * v) → cwBlockSupport)) :=
  cwMixedTypeWords (coppersmithLeftType u s) (coppersmithRightType v t) (18 * u) (8 * v)

/-- **The number of retained blocks** at Coppersmith's selection, exactly as on [Cop97, p. 44]:
a product of two trinomial coefficients. -/
theorem card_coppersmithMixedTypeWords {u s v t : ℕ} (hs : s ≤ u) (ht : 2 * t ≤ v) :
    (coppersmithMixedTypeWords u s v t).card =
      Nat.multinomial Finset.univ (coppersmithLeftType u s) *
        Nat.multinomial Finset.univ (coppersmithRightType v t) :=
  card_cwMixedTypeWords (sum_coppersmithLeftType hs) (sum_coppersmithRightType ht)

/-- **`M = 7^{7a/2} 6^{3b}`**, the first dimension of the surviving matrix product
[Cop97, p. 45]. -/
theorem coppersmithMixed_wordProduct_m {u s v t : ℕ}
    {w : (Fin (18 * u) → cwBlockSupport) × (Fin (8 * v) → cwBlockSupport)}
    (hw : w ∈ coppersmithMixedTypeWords u s v t) :
    cwMixedWordProduct (cwDimM 7) (cwDimM 6) w = 7 ^ (7 * u) * 6 ^ (3 * v) :=
  cwMixed_wordProduct_m 7 6 _ _ _ _ _ _ _ _ hw

/-- **`M = 7^{7a/2} 6^{3b}`** on the second leg as well: the surviving product is `⟨M, M, P⟩`. -/
theorem coppersmithMixed_wordProduct_n {u s v t : ℕ}
    {w : (Fin (18 * u) → cwBlockSupport) × (Fin (8 * v) → cwBlockSupport)}
    (hw : w ∈ coppersmithMixedTypeWords u s v t) :
    cwMixedWordProduct (cwDimN 7) (cwDimN 6) w = 7 ^ (7 * u) * 6 ^ (3 * v) :=
  cwMixed_wordProduct_n 7 6 _ _ _ _ _ _ _ _ hw

/-- **`P = 7^{a-2s} 6^{b-2t}`**, the short dimension of the surviving matrix product
[Cop97, p. 47]. -/
theorem coppersmithMixed_wordProduct_p {u s v t : ℕ}
    {w : (Fin (18 * u) → cwBlockSupport) × (Fin (8 * v) → cwBlockSupport)}
    (hw : w ∈ coppersmithMixedTypeWords u s v t) :
    cwMixedWordProduct (cwDimP 7) (cwDimP 6) w = 7 ^ (2 * (u - s)) * 6 ^ (v - 2 * t) :=
  cwMixed_wordProduct_p 7 6 _ _ _ _ _ _ _ _ hw

/-! ## Regression: the empty second half is the single-`q` layer

With `k₆ = 0` -- no `q₆` positions and the zero profile on them -- every statement of this module
becomes the corresponding statement of `Examples/CoppersmithWinogradRectangularType.lean`. -/

@[simp] theorem cwRectType_zero : cwRectType 0 0 0 0 = fun _ ↦ 0 := by
  funext w
  unfold cwRectType cwRectAddressCount
  split <;> rfl

theorem multinomial_zero_cwBlockSupport :
    Nat.multinomial (Finset.univ : Finset cwBlockSupport) (fun _ ↦ 0) = 1 := by
  have h := Nat.multinomial_spec (Finset.univ : Finset cwBlockSupport) (fun _ ↦ 0)
  simpa using h

/-- **Word-count regression.**  At `k₆ = 0` the mixed word count is the single-`q` multinomial. -/
theorem card_cwMixedTypeWords_right_trivial {g₇ : cwBlockSupport → ℕ} {n₇ : ℕ}
    (h₇ : ∑ w, g₇ w = n₇) :
    (cwMixedTypeWords g₇ (fun _ ↦ 0) n₇ 0).card = Nat.multinomial Finset.univ g₇ := by
  rw [card_cwMixedTypeWords h₇ (by simp), multinomial_zero_cwBlockSupport, mul_one]

/-- **Word-count regression, `cwRect` form.**  At `k₆ = 0` the mixed word family has exactly as
many elements as `cwRectTypeWords`. -/
theorem card_cwMixedTypeWords_cwRect_right_trivial {a b e f : ℕ}
    (h : 0 < a + 2 * b + 2 * e + f) :
    (cwMixedTypeWords (cwRectType a b e f) (cwRectType 0 0 0 0)
        (a + 2 * b + 2 * e + f) 0).card = (cwRectTypeWords a b e f).card := by
  rw [cwRectType_zero, card_cwMixedTypeWords_right_trivial (sum_cwRectType a b e f),
    card_cwRectTypeWords h]

@[simp] theorem cwMixedWordProduct_right_trivial (x₇ x₆ : cwBlockSupport → ℕ) {n₇ : ℕ}
    (w : (Fin n₇ → cwBlockSupport) × (Fin 0 → cwBlockSupport)) :
    cwMixedWordProduct x₇ x₆ w = ∏ i, x₇ (w.1 i) := by
  rw [cwMixedWordProduct, Fin.prod_univ_zero, mul_one]

/-- **First-dimension regression.**  At `k₆ = 0` the mixed first dimension is `q₇ ^ b`, the value
of `cwRect_positiveWordProduct_m`. -/
theorem cwMixed_wordProduct_m_right_trivial (q₇ q₆ a b e f : ℕ) {n₇ : ℕ}
    {w : (Fin n₇ → cwBlockSupport) × (Fin 0 → cwBlockSupport)}
    (hw : w ∈ cwMixedTypeWords (cwRectType a b e f) (cwRectType 0 0 0 0) n₇ 0) :
    cwMixedWordProduct (cwDimM q₇) (cwDimM q₆) w = q₇ ^ b := by
  rw [cwMixed_wordProduct_m q₇ q₆ a b e f 0 0 0 0 hw, pow_zero, mul_one]

/-- **Second-dimension regression**, the value of `cwRect_positiveWordProduct_n`. -/
theorem cwMixed_wordProduct_n_right_trivial (q₇ q₆ a b e f : ℕ) {n₇ : ℕ}
    {w : (Fin n₇ → cwBlockSupport) × (Fin 0 → cwBlockSupport)}
    (hw : w ∈ cwMixedTypeWords (cwRectType a b e f) (cwRectType 0 0 0 0) n₇ 0) :
    cwMixedWordProduct (cwDimN q₇) (cwDimN q₆) w = q₇ ^ b := by
  rw [cwMixed_wordProduct_n q₇ q₆ a b e f 0 0 0 0 hw, pow_zero, mul_one]

/-- **Third-dimension regression**, the value of `cwRect_positiveWordProduct_p`. -/
theorem cwMixed_wordProduct_p_right_trivial (q₇ q₆ a b e f : ℕ) {n₇ : ℕ}
    {w : (Fin n₇ → cwBlockSupport) × (Fin 0 → cwBlockSupport)}
    (hw : w ∈ cwMixedTypeWords (cwRectType a b e f) (cwRectType 0 0 0 0) n₇ 0) :
    cwMixedWordProduct (cwDimP q₇) (cwDimP q₆) w = q₇ ^ a := by
  rw [cwMixed_wordProduct_p q₇ q₆ a b e f 0 0 0 0 hw, pow_zero, mul_one]

@[simp] theorem cwMixedMarginalType_right_trivial (g₇ : cwBlockSupport → ℕ) (c : Leg) :
    cwMixedMarginalType g₇ (fun _ ↦ 0) c =
      WordType.mappedType (fun w : cwBlockSupport ↦ w.1 c) g₇ := by
  funext β
  simp [cwMixedMarginalType, WordType.mappedType]

/-- **Marginal regression.**  At `k₆ = 0` the mixed leg marginal is `cwRectMarginalType`. -/
theorem cwMixedMarginalType_cwRect_right_trivial (a b e f : ℕ) (c : Leg) :
    cwMixedMarginalType (cwRectType a b e f) (cwRectType 0 0 0 0) c =
      cwRectMarginalType a b e f c := by
  rw [cwRectType_zero, cwMixedMarginalType_right_trivial, cwRect_mappedType_eq]

/-! ## Bridge to the positive-word representation

The laser pipeline stores words recursively (`PositiveWord`); the mixed layer above stores them as
functions on `Fin n`, which is what makes the `k = 0` regression expressible.  These two lemmas
move between the two representations, one half at a time. -/

theorem mem_cwMixedTypeWords_positiveWordEquiv {g₇ g₆ : cwBlockSupport → ℕ} {d₇ d₆ : ℕ}
    {w₇ : PositiveWord cwBlockSupport d₇} {w₆ : PositiveWord cwBlockSupport d₆} :
    ((positiveWordEquiv cwBlockSupport d₇ w₇, positiveWordEquiv cwBlockSupport d₆ w₆) :
        (Fin (d₇ + 1) → cwBlockSupport) × (Fin (d₆ + 1) → cwBlockSupport))
          ∈ cwMixedTypeWords g₇ g₆ (d₇ + 1) (d₆ + 1) ↔
      w₇ ∈ positiveTypeClass cwBlockSupport d₇ g₇ ∧
        w₆ ∈ positiveTypeClass cwBlockSupport d₆ g₆ := by
  simp

theorem cwMixedWordProduct_positiveWordEquiv (x₇ x₆ : cwBlockSupport → ℕ) (d₇ d₆ : ℕ)
    (w₇ : PositiveWord cwBlockSupport d₇) (w₆ : PositiveWord cwBlockSupport d₆) :
    cwMixedWordProduct x₇ x₆
        ((positiveWordEquiv cwBlockSupport d₇ w₇, positiveWordEquiv cwBlockSupport d₆ w₆) :
          (Fin (d₇ + 1) → cwBlockSupport) × (Fin (d₆ + 1) → cwBlockSupport)) =
      positiveWordProduct x₇ d₇ w₇ * positiveWordProduct x₆ d₆ w₆ := by
  rw [cwMixedWordProduct, positiveWordProduct_eq_fin_prod x₇ d₇ w₇,
    positiveWordProduct_eq_fin_prod x₆ d₆ w₆]

end AlgebraicComplexity.Examples
