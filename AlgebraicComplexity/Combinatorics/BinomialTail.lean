/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Asymptotics
import AlgebraicComplexity.Combinatorics.WordType
import AlgebraicComplexity.Probability.KullbackLeiblerBounds

/-!
# Binomial tails for one marked letter, by the method of types

This module proves the counting lemma behind the near-uniform mass distributions of
Alman--Vassilevska Williams, *Limits on All Known (and Some Unknown) Approaches to Matrix
Multiplication*, arXiv:1810.08671v1, **Lemma 5.1** (used in the proof of Theorem 5.2 and hence
of Corollary 5.1): over an alphabet of size `q`, all but a `q^{-2δn}` fraction of the words of
length `n` have a prescribed letter occurring close to `n / q` times.

## Route: types, not measure theory

AVW derive their bound from Hoeffding's inequality.  Mathlib's Hoeffding inequality is
measure-theoretic, and importing it would drag measure theory into the combinatorics layer, so
this module takes the equivalent *method-of-types* route recommended by the project's barrier
framework.  Nothing here mentions a measure, a random variable, or a filtration.

Only the two-level statistic "does this position carry the marked letter?" matters, so only the
two-level distributions

`tiltWeight letter t = (t on the marked letter, (1 - t)/(q - 1) on each other letter)`

are needed; `uniformVector` is `tiltWeight letter q⁻¹`.  The three steps are:

1. **Counting (`card_multiplicityLevel_mul_pow_le_one`).**  For any probability vector `p` the
   total `p`-mass of all words is `1` (`WordType.sum_prod_word_eq_pow`), and every word in which
   the marked letter occurs exactly `k` times carries the same mass
   `t^k · ((1-t)/(q-1))^{n-k}` (`WordType.prod_word_eq_prod_pow`).  Hence that level set has at
   most `(t^k · ((1-t)/(q-1))^{n-k})⁻¹` elements.  This is the type-counting bound
   `|typeClass| ≤ exp(n·H)` in the form specialized to the marked-letter statistic; no Stirling
   estimate is used.
2. **Divergence (`natCast_mul_klDiv_eq`, `card_multiplicityLevel_le_exp_klDiv`).**  Choosing the
   empirical value `t = k/n` turns that reciprocal into
   `q^n · exp(-n · KL(tilt (k/n) ‖ uniform))`, which is the identity
   `|typeClass| ≤ q^n · exp(-n · KL(type ‖ uniform))`.
3. **Pinsker's inequality (`tailExponent_le_klDiv_tiltVector`).**  The coordinatewise Pinsker
   bound `ProbabilityVector.two_mul_sq_sub_weight_le_klDiv` gives `KL(p ‖ q) ≥ 2(pᵢ - qᵢ)²` in
   nats for every coordinate `i`.  At the marked coordinate, with `d = t - 1/q`, this is
   `KL ≥ 2d² = tailExponent |d|`, the sharp constant.

## Interface for milestone I (AVW Theorem 5.2)

The statement consumed downstream is `card_deviatingWords_le`:

`|{w ∈ ι^n : |mult(w, letter) - n/q| ≥ ε·n}| ≤ (n + 1) · q^n · exp(-n · tailExponent ε)`,

together with its repackaging `card_sub_bound_le_card_concentrated`, which is literally the form
AVW use ("at least `|S| - bound` of the elements of `S` are concentrated"), and the growth-layer
corollary `exponentialRate_deviatingWords_le`.

One honest deviation from the printed statement, recorded here because a later milestone must not
silently assume the printed constants:

* **An explicit polynomial factor `n + 1` remains.**  The method of types splits the deviating
  words into the at most `n + 1` level sets of the marked-letter count and bounds each; AVW's
  Hoeffding route absorbs the two tails into a factor `2` instead.  Every asymptotic consumer of
  Lemma 5.1 divides the bound by an exponentially larger quantity, so a polynomial factor is
  harmless there; `exponentialRate_deviatingWords_le` removes it once and for all.

The exponent constant is AVW's.  Pinsker's inequality gives `tailExponent ε = 2ε²`, so the
faithful `δ`-form proved here (`card_deviatingWords_le_rpow_sqrt`) uses AVW's printed radius
`ε = sqrt(δ · log q)` and concludes with their `≤ (n+1) · q^{(1-2δ)n}`.  The parametric form
`card_deviatingWords_le_rpow` states exactly what the proof gives: any `ε` with
`δ · log q ≤ tailExponent ε` yields `≤ (n+1) · q^{(1-δ)n}`.

## Non-goals

No entropy, word-type, or divergence notion is introduced: `WordType.multiplicity` and
`ProbabilityVector.klDiv`, together with its Pinsker bound, are consumed verbatim.  The
tensor-facing statements of AVW Section 5 (Theorem 5.2, Corollary 5.1) belong to
`MatrixMultiplication/IndependenceMassDistribution.lean` and are deliberately absent.

## References

* J. Alman and V. Vassilevska Williams, *Limits on All Known (and Some Unknown) Approaches to
  Matrix Multiplication*, arXiv:1810.08671v1, Section 5, Lemma 5.1.
-/

open scoped BigOperators

namespace AlgebraicComplexity.BinomialTail

open AlgebraicComplexity.WordType
open ProbabilityVector (uniformVector uniformVector_weight uniformVector_weight_pos)

universe u

variable {ι : Type u} [Fintype ι] [Nonempty ι]

/-! ### Two-level probability vectors -/

/-- The mass that a two-level distribution assigns to each *unmarked* letter: the remaining mass
`1 - t` spread uniformly over the `q - 1` letters other than the marked one. -/
noncomputable def unmarkedWeight (ι : Type u) [Fintype ι] (t : ℝ) : ℝ :=
  (1 - t) / ((Fintype.card ι : ℝ) - 1)

/-- The two-level weights on a finite alphabet: mass `t` on the marked letter and mass
`unmarkedWeight ι t` on every other letter.  This is the only family of distributions the
marked-letter statistic can distinguish, which is why the whole argument stays two-dimensional
even though the alphabet is arbitrary. -/
noncomputable def tiltWeight [DecidableEq ι] (letter : ι) (t : ℝ) : ι → ℝ :=
  fun i ↦ if i = letter then t else unmarkedWeight ι t

omit [Nonempty ι] in
@[simp] theorem tiltWeight_self [DecidableEq ι] (letter : ι) (t : ℝ) :
    tiltWeight letter t letter = t := by
  simp [tiltWeight]

omit [Nonempty ι] in
theorem tiltWeight_of_ne [DecidableEq ι] {letter i : ι} (h : i ≠ letter) (t : ℝ) :
    tiltWeight letter t i = unmarkedWeight ι t := by
  simp [tiltWeight, h]

/-- A two-level weight vector has total mass one. -/
theorem sum_tiltWeight [DecidableEq ι] (letter : ι) (hcard : 2 ≤ Fintype.card ι) (t : ℝ) :
    ∑ i, tiltWeight letter t i = 1 := by
  have hq : ((Fintype.card ι : ℝ) - 1) ≠ 0 := by
    have : (2 : ℝ) ≤ (Fintype.card ι : ℝ) := by exact_mod_cast hcard
    linarith
  rw [sum_eq_of_const_off letter _ (unmarkedWeight ι t)
    (fun i hi ↦ tiltWeight_of_ne hi t), tiltWeight_self]
  unfold unmarkedWeight
  field_simp
  ring

omit [Nonempty ι] in
/-- A two-level weight vector is nonnegative exactly when its marked mass lies in `[0, 1]`. -/
theorem tiltWeight_nonneg [DecidableEq ι] (letter : ι) (hcard : 2 ≤ Fintype.card ι)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (i : ι) :
    0 ≤ tiltWeight letter t i := by
  have hq : (0 : ℝ) < (Fintype.card ι : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (Fintype.card ι : ℝ) := by exact_mod_cast hcard
    linarith
  by_cases h : i = letter
  · simpa [tiltWeight, h] using ht0
  · rw [tiltWeight_of_ne h]
    exact div_nonneg (by linarith) hq.le

/-- At `t = 1/q` the two-level weights are the uniform weights. -/
theorem tiltWeight_inv_card [DecidableEq ι] (letter : ι) (hcard : 2 ≤ Fintype.card ι) (i : ι) :
    tiltWeight letter ((Fintype.card ι : ℝ)⁻¹) i = (Fintype.card ι : ℝ)⁻¹ := by
  have hqpos : (0 : ℝ) < (Fintype.card ι : ℝ) := by
    have : (2 : ℝ) ≤ (Fintype.card ι : ℝ) := by exact_mod_cast hcard
    linarith
  have hq : ((Fintype.card ι : ℝ) - 1) ≠ 0 := by
    have : (2 : ℝ) ≤ (Fintype.card ι : ℝ) := by exact_mod_cast hcard
    linarith
  by_cases h : i = letter
  · simp [tiltWeight, h]
  · rw [tiltWeight_of_ne h]
    unfold unmarkedWeight
    field_simp

/-- The two-level probability vector with marked mass `t`. -/
noncomputable def tiltVector [DecidableEq ι] (letter : ι) (hcard : 2 ≤ Fintype.card ι)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : ProbabilityVector ι where
  weight := tiltWeight letter t
  nonneg := tiltWeight_nonneg letter hcard ht0 ht1
  total := sum_tiltWeight letter hcard t

@[simp] theorem tiltVector_weight [DecidableEq ι] (letter : ι) (hcard : 2 ≤ Fintype.card ι)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (i : ι) :
    (tiltVector letter hcard t ht0 ht1).weight i = tiltWeight letter t i := rfl

/-! ### Level sets of the marked-letter count -/

/-- The words of length `n` in which `letter` occurs exactly `k` times. -/
noncomputable def multiplicityLevel (letter : ι) (n k : ℕ) : Finset (Fin n → ι) :=
  Finset.univ.filter fun word ↦ multiplicity word letter = k

omit [Nonempty ι] in
@[simp] theorem mem_multiplicityLevel {letter : ι} {n k : ℕ} {word : Fin n → ι} :
    word ∈ multiplicityLevel letter n k ↔ multiplicity word letter = k := by
  simp [multiplicityLevel]

/-- **The type-counting bound, marked-letter form.**  For every two-level probability vector, the
level set `{mult(·, letter) = k}` has total mass at most one, and every one of its words carries
the same mass `t^k · unmarkedWeight^{n-k}`.

Proof sketch: `WordType.prod_word_eq_prod_pow` rewrites the product of per-position weights as a
product of powers indexed by the alphabet; off the marked letter the base is constant, so
`Finset.prod_pow_eq_pow_sum` collapses it, and `WordType.sum_multiplicity` identifies the exponent
as `n - k`.  Summing over the level set and comparing with the sum over all words, which is
`(∑ᵢ pᵢ)^n = 1` by `WordType.sum_prod_word_eq_pow`, gives the bound. -/
theorem card_multiplicityLevel_mul_pow_le_one [DecidableEq ι] (letter : ι)
    (hcard : 2 ≤ Fintype.card ι) (n k : ℕ) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ((multiplicityLevel letter n k).card : ℝ) *
        (t ^ k * unmarkedWeight ι t ^ (n - k)) ≤ 1 := by
  classical
  set p : ι → ℝ := tiltWeight letter t with hp
  have hpnonneg : ∀ i, 0 ≤ p i := tiltWeight_nonneg letter hcard ht0 ht1
  have hprodnonneg : ∀ word : Fin n → ι, 0 ≤ ∏ j, p (word j) :=
    fun word ↦ Finset.prod_nonneg fun j _ ↦ hpnonneg _
  have hterm : ∀ word ∈ multiplicityLevel letter n k,
      ∏ j, p (word j) = t ^ k * unmarkedWeight ι t ^ (n - k) := by
    intro word hword
    have hk : multiplicity word letter = k := mem_multiplicityLevel.mp hword
    have hsum : ∑ i ∈ Finset.univ.erase letter, multiplicity word i = n - k := by
      have hall : multiplicity word letter +
          ∑ i ∈ Finset.univ.erase letter, multiplicity word i = n := by
        rw [Finset.add_sum_erase _ _ (Finset.mem_univ letter)]
        exact sum_multiplicity word
      omega
    calc
      ∏ j, p (word j) = ∏ i, p i ^ multiplicity word i := prod_word_eq_prod_pow p word
      _ = p letter ^ multiplicity word letter *
            ∏ i ∈ Finset.univ.erase letter, p i ^ multiplicity word i :=
        (Finset.mul_prod_erase _ _ (Finset.mem_univ letter)).symm
      _ = t ^ k * ∏ i ∈ Finset.univ.erase letter,
            unmarkedWeight ι t ^ multiplicity word i := by
        rw [hp, tiltWeight_self, hk]
        refine congrArg (t ^ k * ·) (Finset.prod_congr rfl fun i hi ↦ ?_)
        rw [tiltWeight_of_ne (Finset.ne_of_mem_erase hi)]
      _ = t ^ k * unmarkedWeight ι t ^ (n - k) := by
        rw [Finset.prod_pow_eq_pow_sum, hsum]
  calc
    ((multiplicityLevel letter n k).card : ℝ) *
        (t ^ k * unmarkedWeight ι t ^ (n - k))
        = ∑ word ∈ multiplicityLevel letter n k, ∏ j, p (word j) := by
      rw [Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ word : Fin n → ι, ∏ j, p (word j) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun word _ _ ↦ hprodnonneg word)
    _ = (∑ i, p i) ^ n := sum_prod_word_eq_pow p n
    _ = 1 := by rw [sum_tiltWeight letter hcard t, one_pow]

/-! ### The divergence step -/

/-- Kullback--Leibler divergence of a two-level vector against the uniform vector, scaled by the
word length.  Both sides are the exponent appearing in the method-of-types estimate:
`n·KL = n·log q + k·log t + (n-k)·log(unmarked)` for the empirical value `t = k/n`.

Proof sketch: `ProbabilityVector.klDiv_eq_neg_entropy_sub_expectation_log` against the constant
uniform reference reduces `KL` to `log q - H`, and `sum_eq_of_const_off` evaluates the two-level
entropy `H = -t log t - (1-t) log(unmarked)`.  Substituting `t = k/n` clears the denominators. -/
theorem natCast_mul_klDiv_eq [DecidableEq ι] (letter : ι) (hcard : 2 ≤ Fintype.card ι)
    (n k : ℕ) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hnt : (n : ℝ) * t = (k : ℝ)) :
    (n : ℝ) * (tiltVector letter hcard t ht0 ht1).klDiv (uniformVector ι) =
      (n : ℝ) * Real.log (Fintype.card ι) + (k : ℝ) * Real.log t +
        ((n : ℝ) - k) * Real.log (unmarkedWeight ι t) := by
  classical
  set w : ℝ := unmarkedWeight ι t with hws
  have hqR : (2 : ℝ) ≤ (Fintype.card ι : ℝ) := by exact_mod_cast hcard
  have hqpos : (0 : ℝ) < (Fintype.card ι : ℝ) := by linarith
  have hqsub : ((Fintype.card ι : ℝ) - 1) ≠ 0 := by linarith
  -- `KL` against the uniform reference is `log q - H`.
  have hkl : (tiltVector letter hcard t ht0 ht1).klDiv (uniformVector ι) =
      -(tiltVector letter hcard t ht0 ht1).entropy + Real.log (Fintype.card ι) := by
    rw [ProbabilityVector.klDiv_eq_neg_entropy_sub_expectation_log _ _
      (fun i ↦ uniformVector_weight_pos i)]
    have hconst : (tiltVector letter hcard t ht0 ht1).expectation
        (fun i ↦ Real.log ((uniformVector ι).weight i)) =
        Real.log ((Fintype.card ι : ℝ)⁻¹) := by
      simpa using ProbabilityVector.expectation_const
        (tiltVector letter hcard t ht0 ht1) (Real.log ((Fintype.card ι : ℝ)⁻¹))
    rw [hconst, Real.log_inv]
    ring
  -- The two-level entropy.
  have hent : (tiltVector letter hcard t ht0 ht1).entropy =
      -(t * Real.log t) + ((Fintype.card ι : ℝ) - 1) * -(w * Real.log w) := by
    unfold ProbabilityVector.entropy
    rw [sum_eq_of_const_off letter _ (-(w * Real.log w)) ?_]
    · simp [tiltVector, Real.negMulLog_eq_neg]
    · intro i hi
      simp [tiltVector, tiltWeight_of_ne hi, Real.negMulLog_eq_neg, hws]
  have hmass : ((Fintype.card ι : ℝ) - 1) * w = 1 - t := by
    rw [hws]
    unfold unmarkedWeight
    field_simp
  rw [hkl, hent]
  have hexpand : (n : ℝ) * (-(-(t * Real.log t) +
      ((Fintype.card ι : ℝ) - 1) * -(w * Real.log w)) + Real.log (Fintype.card ι)) =
      (n : ℝ) * Real.log (Fintype.card ι) + ((n : ℝ) * t) * Real.log t +
        ((n : ℝ) * (((Fintype.card ι : ℝ) - 1) * w)) * Real.log w := by
    ring
  rw [hexpand, hnt, hmass]
  have : (n : ℝ) * (1 - t) = (n : ℝ) - k := by
    rw [← hnt]; ring
  rw [this]

/-- A positive base raised to a natural power is positive as soon as the base is positive whenever
the exponent is nonzero.  This covers the boundary cases `k = 0` and `k = n` of the empirical
distribution, where `0 ^ 0 = 1`. -/
private theorem pow_pos_of_ne_zero_imp {x : ℝ} {m : ℕ} (h : m ≠ 0 → 0 < x) : 0 < x ^ m := by
  cases m with
  | zero => simp
  | succ m => exact pow_pos (h (Nat.succ_ne_zero m)) _

/-- **Method-of-types bound on a level set.**  The number of words of length `n` in which `letter`
occurs exactly `k` times is at most `q^n · exp(-n · KL(empirical ‖ uniform))`.

Proof sketch: `card_multiplicityLevel_mul_pow_le_one` at the empirical value `t = k/n` bounds the
cardinality by `(t^k · w^{n-k})⁻¹`, and `natCast_mul_klDiv_eq` identifies
`q^n · exp(-n·KL) · t^k · w^{n-k}` as a positive real whose logarithm vanishes, hence as `1`. -/
theorem card_multiplicityLevel_le_exp_klDiv [DecidableEq ι] (letter : ι)
    (hcard : 2 ≤ Fintype.card ι) (n k : ℕ) (hn : 0 < n) (hk : k ≤ n)
    (ht0 : (0 : ℝ) ≤ (k : ℝ) / n) (ht1 : (k : ℝ) / n ≤ 1) :
    ((multiplicityLevel letter n k).card : ℝ) ≤
      (Fintype.card ι : ℝ) ^ n *
        Real.exp (-(n : ℝ) *
          (tiltVector letter hcard ((k : ℝ) / n) ht0 ht1).klDiv (uniformVector ι)) := by
  classical
  set t : ℝ := (k : ℝ) / n with hts
  set w : ℝ := unmarkedWeight ι t with hws
  set K : ℝ := (tiltVector letter hcard t ht0 ht1).klDiv (uniformVector ι) with hKs
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hqR : (2 : ℝ) ≤ (Fintype.card ι : ℝ) := by exact_mod_cast hcard
  have hqpos : (0 : ℝ) < (Fintype.card ι : ℝ) := by linarith
  have hqsub : (0 : ℝ) < (Fintype.card ι : ℝ) - 1 := by linarith
  -- positivity of the two powers, including the boundary cases
  have htpow : 0 < t ^ k := by
    refine pow_pos_of_ne_zero_imp fun hkne ↦ ?_
    have : (0 : ℝ) < (k : ℝ) := by
      have : 0 < k := Nat.pos_of_ne_zero hkne
      exact_mod_cast this
    rw [hts]
    positivity
  have hwpow : 0 < w ^ (n - k) := by
    refine pow_pos_of_ne_zero_imp fun hne ↦ ?_
    have hkn : k < n := by omega
    have hklt : t < 1 := by
      rw [hts, div_lt_one hnR]
      exact_mod_cast hkn
    rw [hws]
    unfold unmarkedWeight
    exact div_pos (by linarith) hqsub
  have hcount := card_multiplicityLevel_mul_pow_le_one letter hcard n k ht0 ht1
  rw [← hws] at hcount
  -- the exponential identity
  have hone : (Fintype.card ι : ℝ) ^ n * Real.exp (-(n : ℝ) * K) *
      (t ^ k * w ^ (n - k)) = 1 := by
    have hpos : 0 < (Fintype.card ι : ℝ) ^ n * Real.exp (-(n : ℝ) * K) *
        (t ^ k * w ^ (n - k)) := by positivity
    have hlog : Real.log ((Fintype.card ι : ℝ) ^ n * Real.exp (-(n : ℝ) * K) *
        (t ^ k * w ^ (n - k))) = 0 := by
      rw [Real.log_mul (by positivity) (by positivity),
        Real.log_mul (by positivity) (by positivity),
        Real.log_mul (by positivity) (by positivity)]
      simp only [Real.log_pow, Real.log_exp]
      have hnt : (n : ℝ) * t = (k : ℝ) := by
        rw [hts]; field_simp
      have hid := natCast_mul_klDiv_eq letter hcard n k ht0 ht1 hnt
      rw [← hws, ← hKs] at hid
      have hcast : ((n - k : ℕ) : ℝ) = (n : ℝ) - (k : ℝ) := by
        push_cast [Nat.cast_sub hk]
        ring
      rw [hcast]
      linarith [hid]
    have := Real.exp_log hpos
    rw [hlog, Real.exp_zero] at this
    exact this.symm
  have hprodpos : 0 < t ^ k * w ^ (n - k) := mul_pos htpow hwpow
  have : ((multiplicityLevel letter n k).card : ℝ) * (t ^ k * w ^ (n - k)) ≤
      ((Fintype.card ι : ℝ) ^ n * Real.exp (-(n : ℝ) * K)) * (t ^ k * w ^ (n - k)) := by
    rw [hone]
    exact hcount
  exact le_of_mul_le_mul_right (by linarith [this]) hprodpos

/-! ### The Pinsker lower bound -/

/-- The concentration exponent supplied by Pinsker's inequality: `tailExponent ε = 2ε²`.

This is the sharp constant, the same one Hoeffding's inequality supplies to AVW; it comes from the
coordinatewise Pinsker bound `ProbabilityVector.two_mul_sq_sub_weight_le_klDiv`, whose nats
normalization is exactly `KL ≥ 2 (deviation)²`. -/
noncomputable def tailExponent (ε : ℝ) : ℝ := 2 * ε ^ 2

/-- The concentration exponent is nonnegative.  The hypothesis `0 ≤ ε` is no longer needed now
that the exponent is the sharp `2ε²`; it is kept so that existing call sites, which have it to
hand, do not have to change. -/
theorem tailExponent_nonneg {ε : ℝ} (_hε : 0 ≤ ε) : 0 ≤ tailExponent ε := by
  unfold tailExponent
  positivity

/-- The concentration exponent is monotone in the deviation. -/
theorem tailExponent_mono {ε ε' : ℝ} (hε : 0 ≤ ε) (h : ε ≤ ε') :
    tailExponent ε ≤ tailExponent ε' := by
  unfold tailExponent
  nlinarith [hε, h]

/-- The concentration exponent dominates `ε²`.  The hypotheses `0 ≤ ε` and `ε ≤ 1` are no longer
needed now that the exponent is the sharp `2ε²`; they are kept so that existing call sites, which
have them to hand, do not have to change. -/
theorem sq_le_tailExponent {ε : ℝ} (_hε : 0 ≤ ε) (_hε1 : ε ≤ 1) : ε ^ 2 ≤ tailExponent ε := by
  unfold tailExponent
  nlinarith [sq_nonneg ε]

/-- **Pinsker lower bound on the divergence of a two-level vector from uniform.**
`KL(tilt t ‖ uniform) ≥ tailExponent |t - 1/q| = 2 (t - 1/q)²`.

Proof sketch: `ProbabilityVector.two_mul_sq_sub_weight_le_klDiv` at the marked coordinate, where
the two weights are `t` and `1/q`; `sq_abs` removes the absolute value. -/
theorem tailExponent_le_klDiv_tiltVector [DecidableEq ι] (letter : ι)
    (hcard : 2 ≤ Fintype.card ι) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    tailExponent |t - (Fintype.card ι : ℝ)⁻¹| ≤
      (tiltVector letter hcard t ht0 ht1).klDiv (uniformVector ι) := by
  have h := ProbabilityVector.two_mul_sq_sub_weight_le_klDiv
    (tiltVector letter hcard t ht0 ht1) (uniformVector ι)
    (fun i ↦ uniformVector_weight_pos i) letter
  simpa [tailExponent, sq_abs] using h

/-- Combining the two previous results: an unconditional, distribution-free bound on the size of
one level set in terms of its deviation from the uniform frequency. -/
theorem card_multiplicityLevel_le [DecidableEq ι] (letter : ι) (hcard : 2 ≤ Fintype.card ι)
    (n k : ℕ) (hn : 0 < n) (hk : k ≤ n) :
    ((multiplicityLevel letter n k).card : ℝ) ≤
      (Fintype.card ι : ℝ) ^ n *
        Real.exp (-(n : ℝ) * tailExponent |(k : ℝ) / n - (Fintype.card ι : ℝ)⁻¹|) := by
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have ht0 : (0 : ℝ) ≤ (k : ℝ) / n := by positivity
  have ht1 : (k : ℝ) / n ≤ 1 := by
    rw [div_le_one hnR]
    exact_mod_cast hk
  refine (card_multiplicityLevel_le_exp_klDiv letter hcard n k hn hk ht0 ht1).trans ?_
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity)
  have := tailExponent_le_klDiv_tiltVector letter hcard ht0 ht1
  nlinarith [this, hnR]

/-! ### AVW Lemma 5.1 -/

/-- The words of length `n` in which `letter` occurs at distance at least `ε · n` from the
uniform frequency `n / q`.  AVW's *good* words are those in which `letter` occurs between
`(1/q - ε)n` and `(1/q + ε)n` times; this is the complement, with the boundary counted as
deviating, so the bound below is (very slightly) stronger than the printed statement. -/
noncomputable def deviatingWords (letter : ι) (n : ℕ) (ε : ℝ) : Finset (Fin n → ι) := by
  classical
  exact Finset.univ.filter fun word ↦
    ε * n ≤ |(multiplicity word letter : ℝ) - (n : ℝ) / (Fintype.card ι : ℝ)|

omit [Nonempty ι] in
theorem mem_deviatingWords {letter : ι} {n : ℕ} {ε : ℝ} {word : Fin n → ι} :
    word ∈ deviatingWords letter n ε ↔
      ε * n ≤ |(multiplicity word letter : ℝ) - (n : ℝ) / (Fintype.card ι : ℝ)| := by
  classical
  simp [deviatingWords]

/-- **AVW Lemma 5.1, method-of-types form.**  Over an alphabet of size `q ≥ 2`, the number of
words of length `n` in which a fixed letter occurs at distance at least `ε·n` from `n/q` is at
most `(n + 1) · q^n · exp(-n · tailExponent ε)`.

The polynomial factor `n + 1` counts the possible values of the marked-letter multiplicity; it is
the only loss relative to AVW's Hoeffding route and is removed by
`exponentialRate_deviatingWords_le`.

Proof sketch: partition the deviating words into the at most `n + 1` level sets of the
marked-letter count (`Finset.card_eq_sum_card_fiberwise`).  A nonempty deviating level `k` has
`|k/n - 1/q| ≥ ε`, so `card_multiplicityLevel_le` together with monotonicity of `tailExponent`
bounds it by `q^n · exp(-n · tailExponent ε)`; empty levels are bounded trivially. -/
theorem card_deviatingWords_le [DecidableEq ι] (letter : ι) (hcard : 2 ≤ Fintype.card ι)
    (n : ℕ) {ε : ℝ} (hε : 0 ≤ ε) :
    ((deviatingWords letter n ε).card : ℝ) ≤
      ((n : ℝ) + 1) * (Fintype.card ι : ℝ) ^ n * Real.exp (-(n : ℝ) * tailExponent ε) := by
  classical
  have hqR : (2 : ℝ) ≤ (Fintype.card ι : ℝ) := by exact_mod_cast hcard
  have hqpos : (0 : ℝ) < (Fintype.card ι : ℝ) := by linarith
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have hcardle : (deviatingWords letter 0 ε).card ≤ 1 := by
      have := Finset.card_le_univ (deviatingWords letter 0 ε)
      simpa using this
    have : ((deviatingWords letter 0 ε).card : ℝ) ≤ 1 := by exact_mod_cast hcardle
    simpa using this
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  set bound : ℝ :=
    (Fintype.card ι : ℝ) ^ n * Real.exp (-(n : ℝ) * tailExponent ε) with hbs
  have hboundpos : 0 < bound := by rw [hbs]; positivity
  -- fiberwise decomposition by the marked-letter multiplicity
  have hfiber : (deviatingWords letter n ε).card =
      ∑ k ∈ Finset.range (n + 1),
        ((deviatingWords letter n ε).filter fun word ↦ multiplicity word letter = k).card :=
    Finset.card_eq_sum_card_fiberwise fun word _ ↦
      Finset.mem_range.mpr (Nat.lt_succ_of_le (multiplicity_le_length word letter))
  have hlevel : ∀ k ∈ Finset.range (n + 1),
      (((deviatingWords letter n ε).filter fun word ↦
        multiplicity word letter = k).card : ℝ) ≤ bound := by
    intro k hk
    have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    rcases Finset.eq_empty_or_nonempty
      ((deviatingWords letter n ε).filter fun word ↦ multiplicity word letter = k) with he | ⟨w, hw⟩
    · rw [he]
      simpa using hboundpos.le
    · have hwdev : ε * n ≤
          |(multiplicity w letter : ℝ) - (n : ℝ) / (Fintype.card ι : ℝ)| :=
        mem_deviatingWords.mp (Finset.mem_filter.mp hw).1
      have hwk : multiplicity w letter = k := (Finset.mem_filter.mp hw).2
      rw [hwk] at hwdev
      -- transfer the deviation to the normalized frequency
      have hdev : ε ≤ |(k : ℝ) / n - (Fintype.card ι : ℝ)⁻¹| := by
        have hrw : (k : ℝ) / n - (Fintype.card ι : ℝ)⁻¹ =
            ((k : ℝ) - (n : ℝ) / (Fintype.card ι : ℝ)) / n := by
          field_simp
        rw [hrw, abs_div, abs_of_pos hnR]
        rw [le_div_iff₀ hnR]
        linarith [hwdev]
      have hsubset :
          ((deviatingWords letter n ε).filter fun word ↦ multiplicity word letter = k) ⊆
            multiplicityLevel letter n k := by
        intro word hword
        exact mem_multiplicityLevel.mpr (Finset.mem_filter.mp hword).2
      have hcardle : (((deviatingWords letter n ε).filter fun word ↦
          multiplicity word letter = k).card : ℝ) ≤
          ((multiplicityLevel letter n k).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsubset
      refine hcardle.trans ?_
      refine (card_multiplicityLevel_le letter hcard n k hn hkn).trans ?_
      rw [hbs]
      refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity)
      have hmono := tailExponent_mono hε hdev
      nlinarith [hmono, hnR]
  have hsum : ((deviatingWords letter n ε).card : ℝ) ≤ ((n : ℝ) + 1) * bound := by
    rw [hfiber]
    push_cast
    calc
      (∑ k ∈ Finset.range (n + 1),
          (((deviatingWords letter n ε).filter fun word ↦
            multiplicity word letter = k).card : ℝ))
          ≤ ∑ _k ∈ Finset.range (n + 1), bound := Finset.sum_le_sum hlevel
      _ = ((n : ℝ) + 1) * bound := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        push_cast
        ring
  calc
    ((deviatingWords letter n ε).card : ℝ) ≤ ((n : ℝ) + 1) * bound := hsum
    _ = ((n : ℝ) + 1) * (Fintype.card ι : ℝ) ^ n *
          Real.exp (-(n : ℝ) * tailExponent ε) := by rw [hbs]; ring

/-- The simpler exponent `ε²`, valid for every deviation at most `1`. -/
theorem card_deviatingWords_le_sq [DecidableEq ι] (letter : ι) (hcard : 2 ≤ Fintype.card ι)
    (n : ℕ) {ε : ℝ} (hε : 0 ≤ ε) (hε1 : ε ≤ 1) :
    ((deviatingWords letter n ε).card : ℝ) ≤
      ((n : ℝ) + 1) * (Fintype.card ι : ℝ) ^ n * Real.exp (-(n : ℝ) * ε ^ 2) := by
  have hqR : (2 : ℝ) ≤ (Fintype.card ι : ℝ) := by exact_mod_cast hcard
  refine (card_deviatingWords_le letter hcard n hε).trans ?_
  have hnR : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity)
  nlinarith [sq_le_tailExponent hε hε1, hnR]

/-- **AVW Lemma 5.1, exponent form.**  Whenever `δ · log q ≤ tailExponent ε`, the deviating words
number at most `(n + 1) · q^{(1 - δ)n}`. -/
theorem card_deviatingWords_le_rpow [DecidableEq ι] (letter : ι) (hcard : 2 ≤ Fintype.card ι)
    (n : ℕ) {ε δ : ℝ} (hε : 0 ≤ ε)
    (hδε : δ * Real.log (Fintype.card ι) ≤ tailExponent ε) :
    ((deviatingWords letter n ε).card : ℝ) ≤
      ((n : ℝ) + 1) * (Fintype.card ι : ℝ) ^ ((1 - δ) * (n : ℝ)) := by
  have hqR : (2 : ℝ) ≤ (Fintype.card ι : ℝ) := by exact_mod_cast hcard
  have hqpos : (0 : ℝ) < (Fintype.card ι : ℝ) := by linarith
  have hnR : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  refine (card_deviatingWords_le letter hcard n hε).trans ?_
  have hmul : (n : ℝ) * (δ * Real.log (Fintype.card ι)) ≤ (n : ℝ) * tailExponent ε :=
    mul_le_mul_of_nonneg_left hδε hnR
  have hstep : (Fintype.card ι : ℝ) ^ n * Real.exp (-(n : ℝ) * tailExponent ε) ≤
      (Fintype.card ι : ℝ) ^ ((1 - δ) * (n : ℝ)) := by
    have hpow : (Fintype.card ι : ℝ) ^ n =
        Real.exp ((n : ℝ) * Real.log (Fintype.card ι)) := by
      rw [← Real.rpow_natCast (Fintype.card ι : ℝ) n, Real.rpow_def_of_pos hqpos]
      ring_nf
    have hrpow : (Fintype.card ι : ℝ) ^ ((1 - δ) * (n : ℝ)) =
        Real.exp (Real.log (Fintype.card ι) * ((1 - δ) * (n : ℝ))) :=
      Real.rpow_def_of_pos hqpos _
    rw [hpow, hrpow, ← Real.exp_add]
    refine Real.exp_le_exp.mpr ?_
    nlinarith [hmul]
  rw [mul_assoc]
  refine mul_le_mul_of_nonneg_left hstep ?_
  linarith

/-- **AVW Lemma 5.1, as printed.**  With their radius `ε = sqrt(δ · log q)`, the number of words
in which `letter` occurs outside `(1/q ± ε)n` is at most `(n + 1) · q^{(1 - 2δ)n}`.

The exponent constant is theirs, because `tailExponent ε = 2ε²` is the sharp Pinsker exponent:
`tailExponent (sqrt (δ log q)) = 2δ · log q` exactly.  The only remaining deviation is the factor
`n + 1`, the price of the method-of-types route; see the module documentation. -/
theorem card_deviatingWords_le_rpow_sqrt [DecidableEq ι] (letter : ι)
    (hcard : 2 ≤ Fintype.card ι) (n : ℕ) {δ : ℝ} (hδ : 0 ≤ δ) :
    ((deviatingWords letter n
        (Real.sqrt (δ * Real.log (Fintype.card ι)))).card : ℝ) ≤
      ((n : ℝ) + 1) * (Fintype.card ι : ℝ) ^ ((1 - 2 * δ) * (n : ℝ)) := by
  have hqR : (2 : ℝ) ≤ (Fintype.card ι : ℝ) := by exact_mod_cast hcard
  have hlog : 0 ≤ Real.log (Fintype.card ι) :=
    Real.log_nonneg (by linarith)
  have harg : 0 ≤ δ * Real.log (Fintype.card ι) := by positivity
  set ε : ℝ := Real.sqrt (δ * Real.log (Fintype.card ι)) with hεs
  have hε : 0 ≤ ε := Real.sqrt_nonneg _
  have hsq : ε ^ 2 = δ * Real.log (Fintype.card ι) := Real.sq_sqrt harg
  refine card_deviatingWords_le_rpow letter hcard n hε ?_
  rw [tailExponent, hsq]
  exact le_of_eq (by ring)

/-! ### The interface consumed by AVW Theorem 5.2 -/

/-- The form in which AVW's proof of Theorem 5.2 uses Lemma 5.1: for any finite family `S` of
words, all but at most `(n + 1)·q^n·exp(-n·tailExponent ε)` of its members have the marked letter
occurring strictly inside `(1/q ± ε)n`. -/
theorem card_sub_bound_le_card_concentrated [DecidableEq ι] (letter : ι)
    (hcard : 2 ≤ Fintype.card ι) (n : ℕ) {ε : ℝ} (hε : 0 ≤ ε) (S : Finset (Fin n → ι)) :
    (S.card : ℝ) -
        ((n : ℝ) + 1) * (Fintype.card ι : ℝ) ^ n * Real.exp (-(n : ℝ) * tailExponent ε) ≤
      ((S.filter fun word ↦
        |(multiplicity word letter : ℝ) - (n : ℝ) / (Fintype.card ι : ℝ)| < ε * n).card : ℝ) := by
  classical
  set P : (Fin n → ι) → Prop := fun word ↦
    |(multiplicity word letter : ℝ) - (n : ℝ) / (Fintype.card ι : ℝ)| < ε * n with hPs
  have hsplit : (S.filter P).card + (S.filter fun word ↦ ¬ P word).card = S.card :=
    Finset.card_filter_add_card_filter_not P
  have hsubset : (S.filter fun word ↦ ¬ P word) ⊆ deviatingWords letter n ε := by
    intro word hword
    have := (Finset.mem_filter.mp hword).2
    rw [hPs] at this
    exact mem_deviatingWords.mpr (not_lt.mp this)
  have hcardle : ((S.filter fun word ↦ ¬ P word).card : ℝ) ≤
      ((deviatingWords letter n ε).card : ℝ) := by
    exact_mod_cast Finset.card_le_card hsubset
  have hbound := card_deviatingWords_le letter hcard n hε
  have hsplitR : ((S.filter P).card : ℝ) + ((S.filter fun word ↦ ¬ P word).card : ℝ) =
      (S.card : ℝ) := by exact_mod_cast hsplit
  linarith

/-! ### Real-exponent form for the growth layer -/

/-- **Growth-layer corollary.**  The number of deviating words grows at most like
`(q · exp(-tailExponent ε))^n`: the polynomial factor `n + 1` does not affect the exponential
rate.  This is the form the asymptotic independence-number arguments consume, where the bound is
compared against a genuinely exponential quantity.

Proof sketch: for every base `ρ` strictly above `q·exp(-tailExponent ε)`, pick an intermediate
`σ`; `Growth.ExponentialBound.exists_const_mul_pow_ge_polynomial` absorbs the factor `n + 1` into
the ratio `σ / (q·exp(-tailExponent ε)) > 1`, exhibiting an `ExponentialBound` with base `σ < ρ`. -/
theorem exponentialRate_deviatingWords_le [DecidableEq ι] (letter : ι)
    (hcard : 2 ≤ Fintype.card ι) {ε : ℝ} (hε : 0 ≤ ε) :
    Growth.exponentialRate (fun n ↦ (deviatingWords letter n ε).card) ≤
      (Fintype.card ι : ℝ) * Real.exp (-tailExponent ε) := by
  have hqR : (2 : ℝ) ≤ (Fintype.card ι : ℝ) := by exact_mod_cast hcard
  have hqpos : (0 : ℝ) < (Fintype.card ι : ℝ) := by linarith
  set base : ℝ := (Fintype.card ι : ℝ) * Real.exp (-tailExponent ε) with hbs
  have hbasepos : 0 < base := by rw [hbs]; positivity
  apply le_of_forall_gt
  intro ρ hρ
  set σ : ℝ := (base + ρ) / 2 with hσs
  have hbσ : base < σ := by rw [hσs]; linarith
  have hσρ : σ < ρ := by rw [hσs]; linarith
  have hσpos : 0 < σ := lt_trans hbasepos hbσ
  have hδ : 1 < σ / base := (lt_div_iff₀ hbasepos).mpr (by linarith)
  obtain ⟨A, hA, hpoly⟩ :=
    Growth.ExponentialBound.exists_const_mul_pow_ge_polynomial 1 hδ
  have hbound : Growth.ExponentialBound
      (fun n ↦ (deviatingWords letter n ε).card) σ := by
    refine ⟨hσpos.le, A + 1, by linarith, fun n ↦ ?_⟩
    have hstep := card_deviatingWords_le letter hcard n hε
    have hbasepow : (Fintype.card ι : ℝ) ^ n * Real.exp (-(n : ℝ) * tailExponent ε) =
        base ^ n := by
      rw [hbs, mul_pow, ← Real.exp_nat_mul]
      ring_nf
    have hpolyn : ((n : ℝ) + 1) ≤ (A + 1) * (σ / base) ^ n := by
      have h1 : (n : ℝ) ^ 1 ≤ A * (σ / base) ^ n := hpoly n
      have h2 : (1 : ℝ) ≤ (σ / base) ^ n := one_le_pow₀ (by linarith)
      have hApow : 0 ≤ A * (σ / base) ^ n := by
        have : (0:ℝ) ≤ (σ / base) ^ n := by positivity
        nlinarith [hA]
      simp only [pow_one] at h1
      nlinarith [h1, h2, hA]
    calc
      (((deviatingWords letter n ε).card : ℕ) : ℝ)
          ≤ ((n : ℝ) + 1) * ((Fintype.card ι : ℝ) ^ n *
              Real.exp (-(n : ℝ) * tailExponent ε)) := by
            rw [← mul_assoc]; exact hstep
      _ = ((n : ℝ) + 1) * base ^ n := by rw [hbasepow]
      _ ≤ ((A + 1) * (σ / base) ^ n) * base ^ n := by
            refine mul_le_mul_of_nonneg_right hpolyn (by positivity)
      _ = (A + 1) * σ ^ n := by
            rw [div_pow, mul_assoc, div_mul_cancel₀]
            positivity
  exact lt_of_le_of_lt (Growth.exponentialRate_le hbound) hσρ

/-! ### A tiny sanity client

Two letters, `n = 2`, `ε = 1/2`.  The uniform frequency is `1`, so a word deviates exactly when
`true` occurs `0` or `2` times.  These three facts pin down the direction of the inequality: the
skewed word is counted, the balanced word is not, and the proved bound really is an upper bound
for the resulting nonzero count. -/

/-- The constant word `true true` is a deviating word for `q = 2`, `n = 2`, `ε = 1/2`. -/
theorem const_mem_deviatingWords_bool :
    (fun _ : Fin 2 ↦ true) ∈ deviatingWords (ι := Bool) true 2 (1 / 2) := by
  rw [mem_deviatingWords, multiplicity_const]
  norm_num

/-- The balanced word `true false` is not a deviating word for `q = 2`, `n = 2`, `ε = 1/2`. -/
theorem alternating_notMem_deviatingWords_bool :
    (![true, false] : Fin 2 → Bool) ∉ deviatingWords (ι := Bool) true 2 (1 / 2) := by
  have hmult : multiplicity (![true, false] : Fin 2 → Bool) true = 1 := by
    rw [multiplicity_eq_card_fiber]
    decide
  rw [mem_deviatingWords, hmult]
  norm_num

/-- The count of deviating words for `q = 2`, `n = 2`, `ε = 1/2` is nonzero and lies below the
bound of `card_deviatingWords_le`. -/
theorem sanity_deviatingWords_bool :
    1 ≤ ((deviatingWords (ι := Bool) true 2 (1 / 2)).card : ℝ) ∧
      ((deviatingWords (ι := Bool) true 2 (1 / 2)).card : ℝ) ≤
        ((2 : ℝ) + 1) * (Fintype.card Bool : ℝ) ^ 2 *
          Real.exp (-(2 : ℝ) * tailExponent (1 / 2)) := by
  constructor
  · have hne : (deviatingWords (ι := Bool) true 2 (1 / 2)).Nonempty :=
      ⟨_, const_mem_deviatingWords_bool⟩
    have : 1 ≤ (deviatingWords (ι := Bool) true 2 (1 / 2)).card :=
      Finset.card_pos.mpr hne
    exact_mod_cast this
  · have hcard : 2 ≤ Fintype.card Bool := by decide
    simpa using card_deviatingWords_le (ι := Bool) true hcard 2 (by norm_num : (0:ℝ) ≤ 1 / 2)

/-! ### The averaging form: total occurrences of a letter across a family of words -/

section Averaging

variable {ι : Type u} [Fintype ι] [DecidableEq ι]

/-- **The averaging step of AVW's proof of Theorem 5.2**, stated purely about words.  For any
finite family `W` of length-`n` words over an alphabet of size `q ≥ 2` and any deviation
`0 ≤ ε ≤ 1/q`, the total number of occurrences of a fixed letter `a` across `W` is at least

```text
(|W| - (n+1)·q^n·exp(-n·tailExponent ε)) · n · (1/q - ε).
```

Proof sketch: `BinomialTail.card_sub_bound_le_card_concentrated` says that all but
`(n+1)·q^n·exp(-n·tailExponent ε)` of the words of `W` have `a` occurring within `ε·n` of `n/q`
times; each such word contributes at least `n(1/q - ε)` occurrences, and the remaining words
contribute at least `0`.
-/
theorem card_sub_bound_mul_le_sum_multiplicity (hcard : 2 ≤ Fintype.card ι)
    {n : ℕ} (W : Finset (Fin n → ι)) (a : ι) {ε : ℝ} (hε : 0 ≤ ε)
    (hεq : ε ≤ 1 / (Fintype.card ι : ℝ)) :
    ((W.card : ℝ) -
        ((n : ℝ) + 1) * (Fintype.card ι : ℝ) ^ n * Real.exp (-(n : ℝ) * tailExponent ε)) *
        ((n : ℝ) * (1 / (Fintype.card ι : ℝ) - ε)) ≤
      ∑ w ∈ W, (WordType.multiplicity w a : ℝ) := by
  classical
  haveI : Nonempty ι := Fintype.card_pos_iff.mp (by omega)
  have hqR : (2 : ℝ) ≤ (Fintype.card ι : ℝ) := by exact_mod_cast hcard
  have hqpos : (0 : ℝ) < (Fintype.card ι : ℝ) := by linarith
  have hnn : (0 : ℝ) ≤ (n : ℝ) * (1 / (Fintype.card ι : ℝ) - ε) := by
    have h : (0 : ℝ) ≤ 1 / (Fintype.card ι : ℝ) - ε := by linarith
    positivity
  set C : Finset (Fin n → ι) :=
    W.filter fun word ↦
      |(WordType.multiplicity word a : ℝ) - (n : ℝ) / (Fintype.card ι : ℝ)| < ε * n with hCdef
  have hlow : ∀ w ∈ C, (n : ℝ) * (1 / (Fintype.card ι : ℝ) - ε) ≤
      (WordType.multiplicity w a : ℝ) := by
    intro w hw
    have hmem := (Finset.mem_filter.mp hw).2
    rw [abs_lt] at hmem
    have h1 := hmem.1
    have hdiv : (n : ℝ) * (1 / (Fintype.card ι : ℝ)) = (n : ℝ) / (Fintype.card ι : ℝ) := by
      ring
    nlinarith [h1, hdiv]
  have h1 : (C.card : ℝ) * ((n : ℝ) * (1 / (Fintype.card ι : ℝ) - ε)) ≤
      ∑ w ∈ C, (WordType.multiplicity w a : ℝ) := by
    have := Finset.card_nsmul_le_sum C (fun w ↦ (WordType.multiplicity w a : ℝ))
      ((n : ℝ) * (1 / (Fintype.card ι : ℝ) - ε)) hlow
    rwa [nsmul_eq_mul] at this
  have h2 : ∑ w ∈ C, (WordType.multiplicity w a : ℝ) ≤
      ∑ w ∈ W, (WordType.multiplicity w a : ℝ) :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      fun w _ _ ↦ by positivity
  have h3 := card_sub_bound_le_card_concentrated a hcard n hε W
  have h4 := mul_le_mul_of_nonneg_right h3 hnn
  linarith


end Averaging

end AlgebraicComplexity.BinomialTail
