/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Analysis.CopyGrowth
import AlgebraicComplexity.Combinatorics.PrimeFieldSizing
import AlgebraicComplexity.Examples.CoppersmithWinogradSquareOuterCounting

/-!
# Canonical outer-survivor growth for the Coppersmith--Winograd square

This module isolates the outer hashing half of the CW-square argument from any choice of inner
`(1,1,2)` extraction.  For every positive integral orbit profile `(a,b,c,d)` and proportional
repetition `k`, it chooses a canonical prime field, a Behrend progression-free bucket set, and a
good affine-hashing seed.  The resulting survivor type is exactly the finite direct-sum index
consumed by `CoppersmithWinogradSquareTauValueAssembly`.

The main theorem proves that every positive base strictly below
`cwSquareOuterEntropyBase a b c d` is eventually attained by the *actual number* of surviving
outer blocks.  It uses only:

* exact equal-fiber and maximum-entropy counting for the square support;
* the finite marked-hashing theorem;
* Behrend's progression-free-set bound; and
* the generic removal of a subexponential copy-count loss.

In particular, this file contains no shared-`Z` grouping, inner `112` value formula, matrix
dimensions, Schönhage comparison, or numerical parameter choice.  Its sole CW-specific dependency
is the outer-profile calculus in `CoppersmithWinogradSquareOuterCounting`.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor

/-! ## Canonical finite hashing data -/

/-- Exact field-cardinality requirement for one outer CW-square hashing stage. -/
noncomputable def cwSquareOuterHashRequirement (a b c d k : ℕ) : ℕ :=
  12 * cwSquareAmbientFiberSize a b c d k

/-- Canonical Bertrand prime strictly above the exact outer collision requirement.

The characteristic floor is zero because positivity of the fiber already puts the requirement
above twelve; the resulting prime is therefore automatically large enough to encode `Fin 5`.
-/
noncomputable def cwSquareOuterHashModulus (a b c d k : ℕ) : ℕ :=
  PrimeFieldSizing.modulus 0 (cwSquareOuterHashRequirement a b c d k)

/-- The canonical outer hashing modulus is prime. -/
theorem cwSquareOuterHashModulus_prime (a b c d k : ℕ) :
    (cwSquareOuterHashModulus a b c d k).Prime := by
  exact PrimeFieldSizing.modulus_prime 0 (cwSquareOuterHashRequirement a b c d k)

noncomputable instance instFactCWSquareOuterHashModulusPrime (a b c d k : ℕ) :
    Fact (cwSquareOuterHashModulus a b c d k).Prime :=
  ⟨cwSquareOuterHashModulus_prime a b c d k⟩

/-- The canonical prime strictly exceeds the exact hashing requirement. -/
theorem cwSquareOuterHashRequirement_lt_modulus (a b c d k : ℕ) :
    cwSquareOuterHashRequirement a b c d k <
      cwSquareOuterHashModulus a b c d k := by
  exact PrimeFieldSizing.requirement_lt_modulus 0
    (cwSquareOuterHashRequirement a b c d k)

/-- For a nonempty proportional profile, the canonical prime is at least five and hence
distinguishes the five outer degree labels. -/
theorem cwSquareOuterHashModulus_ge_five
    {a b c d k : ℕ} (hstride : 0 < cwSquareStride a b c d) (hk : 0 < k) :
    5 ≤ cwSquareOuterHashModulus a b c d k := by
  have hfiber := cwSquareAmbientFiberSize_pos hstride hk
  have hlower := cwSquareOuterHashRequirement_lt_modulus a b c d k
  unfold cwSquareOuterHashRequirement at hlower
  omega

/-- Bertrand's postulate bounds the canonical prime by twice the requirement, namely twenty-four
times the common outer leg-fiber size. -/
theorem cwSquareOuterHashModulus_le
    {a b c d k : ℕ} (hstride : 0 < cwSquareStride a b c d) (hk : 0 < k) :
    cwSquareOuterHashModulus a b c d k ≤
      24 * cwSquareAmbientFiberSize a b c d k := by
  have hfiber := cwSquareAmbientFiberSize_pos hstride hk
  have hinput : PrimeFieldSizing.bertrandInput 0
      (cwSquareOuterHashRequirement a b c d k) =
        cwSquareOuterHashRequirement a b c d k := by
    unfold PrimeFieldSizing.bertrandInput cwSquareOuterHashRequirement
    omega
  have hupper := PrimeFieldSizing.modulus_le_two_mul_bertrandInput 0
    (cwSquareOuterHashRequirement a b c d k)
  rw [hinput] at hupper
  change cwSquareOuterHashModulus a b c d k ≤
    2 * (12 * cwSquareAmbientFiberSize a b c d k) at hupper
  calc
    cwSquareOuterHashModulus a b c d k ≤
        2 * (12 * cwSquareAmbientFiberSize a b c d k) := hupper
    _ = 24 * cwSquareAmbientFiberSize a b c d k := by ring

/-- Canonical Behrend bucket set in the canonical prime field. -/
noncomputable def cwSquareOuterBuckets (a b c d k : ℕ) :
    Finset (ZMod (cwSquareOuterHashModulus a b c d k)) :=
  Classical.choose
    (exists_threeAPFree_zmod_half (cwSquareOuterHashModulus a b c d k))

/-- The canonical bucket set has the extremal cardinality used by the Behrend estimate. -/
theorem cwSquareOuterBuckets_card (a b c d k : ℕ) :
    (cwSquareOuterBuckets a b c d k).card =
      rothNumberNat (cwSquareOuterHashModulus a b c d k / 2) :=
  (Classical.choose_spec
    (exists_threeAPFree_zmod_half (cwSquareOuterHashModulus a b c d k))).1

/-- The canonical bucket set contains no nontrivial three-term arithmetic progression. -/
theorem cwSquareOuterBuckets_threeAPFree (a b c d k : ℕ) :
    ThreeAPFree
      (cwSquareOuterBuckets a b c d k :
        Set (ZMod (cwSquareOuterHashModulus a b c d k))) :=
  (Classical.choose_spec
    (exists_threeAPFree_zmod_half (cwSquareOuterHashModulus a b c d k))).2

/-- Canonical constant-sum encoding for one positive outer profile. -/
noncomputable def cwSquareOuterHashEncoding
    (a b c d k : ℕ) (hstride : 0 < cwSquareStride a b c d) (hk : 0 < k) :
    PartitionHashEncoding
      (R := ZMod (cwSquareOuterHashModulus a b c d k)) cwSquareSupport :=
  cwSquarePartitionHashEncoding
    (cwSquareFieldValue_zmod_injective
      (cwSquareOuterHashModulus_ge_five hstride hk))

/-- Canonical affine-seed type for the outer square hash at repetition `k`. -/
noncomputable abbrev CWSquareOuterCanonicalSeed
    (a b c d k : ℕ) (_hstride : 0 < cwSquareStride a b c d) (_hk : 0 < k) :=
  ProgressionHash.Seed
    (ZMod (cwSquareOuterHashModulus a b c d k))
    (Fin (cwSquareDepth a b c d k + 1))

/-- Exact finite survivor type selected by a canonical outer seed. -/
noncomputable abbrev CWSquareOuterCanonicalSurvivor
    (a b c d k : ℕ) (hstride : 0 < cwSquareStride a b c d) (hk : 0 < k)
    (seed : CWSquareOuterCanonicalSeed a b c d k hstride hk) :=
  (cwSquareOuterHashEncoding a b c d k hstride hk).markedLegwiseIsolatedPowerAddresses
    (cwSquareDepth a b c d k)
    (cwSquareAmbientWords a b c d k)
    (cwSquareMarkedWords a b c d k)
    (cwSquareOuterBuckets a b c d k) seed

/-! ## Finite survivor count -/

/-- Every positive repetition has a canonical-field seed satisfying the exact division-free
marked-hashing inequality. -/
theorem exists_cwSquareOuterGoodSeed
    {a b c d k : ℕ} (hstride : 0 < cwSquareStride a b c d) (hk : 0 < k) :
    ∃ seed : CWSquareOuterCanonicalSeed a b c d k hstride hk,
      3 * (cwSquareMarkedWords a b c d k).card *
          (cwSquareOuterBuckets a b c d k).card ≤
        4 * (cwSquareOuterHashModulus a b c d k *
          cwSquareOuterHashModulus a b c d k) *
          Fintype.card
            (CWSquareOuterCanonicalSurvivor a b c d k hstride hk seed) := by
  let p := cwSquareOuterHashModulus a b c d k
  let H := cwSquareOuterHashEncoding a b c d k hstride hk
  let B := cwSquareOuterBuckets a b c d k
  letI : NeZero (2 : ZMod p) :=
    neZero_two_zmod_of_three_le (by
      have hp := cwSquareOuterHashModulus_ge_five hstride hk
      simpa only [p] using (show 3 ≤ cwSquareOuterHashModulus a b c d k by omega))
  have hfield : 12 * cwSquareAmbientFiberSize a b c d k ≤
      Fintype.card (ZMod p) := by
    rw [ZMod.card]
    exact (cwSquareOuterHashRequirement_lt_modulus a b c d k).le
  obtain ⟨seed, hcount, _hsubset, _hinjective⟩ :=
    exists_seed_many_cwSquareMarkedIsolatedPowerAddresses
      H hstride hk B (by
        simpa only [B, p] using
          cwSquareOuterBuckets_threeAPFree a b c d k) hfield
  refine ⟨seed, ?_⟩
  simpa only [p, H, B, ZMod.card, CWSquareOuterCanonicalSurvivor,
    Fintype.card_coe] using hcount

/-- Explicit subexponential loss in the outer survivor-count estimate.

The factors are respectively the lower method-of-types loss for the visible marginal, the
maximum-entropy joint-type selection loss, and the Behrend/hash loss. -/
noncomputable def cwSquareOuterSurvivorLoss (a b c d k : ℕ) : ℝ :=
  WordType.structuralZeroMultinomialLoss (cwSquareBaseMarginal a b c d) k *
    (96 * cwSquareOuterTypeLoss a b c d k *
      Real.exp (cwSquareHashExponentCoefficient a b c d *
        √(((k + 1 : ℕ) : ℝ))))

/-- The entire outer survivor-count loss is subexponential. -/
theorem cwSquareOuterSurvivorLoss_subexponential (a b c d : ℕ) :
    Growth.Subexponential (cwSquareOuterSurvivorLoss a b c d) := by
  have hmarginal := WordType.structuralZeroMultinomialLoss_subexponential
    (cwSquareBaseMarginal a b c d)
  have htype := cwSquareOuterTypeLoss_subexponential a b c d
  have hhash := Growth.Subexponential.exp_mul_sqrt_succ
    (a := cwSquareHashExponentCoefficient a b c d) (by positivity)
  have hright := (htype.const_mul (show (0 : ℝ) ≤ 96 by norm_num)).mul hhash
  convert hmarginal.mul hright using 1
  funext k
  unfold cwSquareOuterSurvivorLoss
  ring

/-- At every positive repetition, some canonical seed realizes the outer entropy base up to the
explicit subexponential loss.

Proof sketch: the lower method-of-types inequality bounds the entropy base by the visible marginal
type-class cardinality.  The finite Behrend/hash estimate bounds that cardinality by the survivor
count, after the maximum-entropy and hashing losses.  Multiplying the two inequalities gives the
claim. -/
theorem exists_cwSquareOuterGoodSeed_count
    {a b c d k : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) (hk : 0 < k) :
    ∃ hstride : 0 < cwSquareStride a b c d,
      ∃ seed : CWSquareOuterCanonicalSeed a b c d k hstride hk,
        cwSquareOuterEntropyBase a b c d ^ k ≤
          cwSquareOuterSurvivorLoss a b c d k *
            Fintype.card
              (CWSquareOuterCanonicalSurvivor a b c d k hstride hk seed) := by
  have hstride : 0 < cwSquareStride a b c d := by
    unfold cwSquareStride
    positivity
  obtain ⟨seed, hcountNat⟩ := exists_cwSquareOuterGoodSeed hstride hk
  refine ⟨hstride, seed, ?_⟩
  let p := cwSquareOuterHashModulus a b c d k
  let copies := Fintype.card
    (CWSquareOuterCanonicalSurvivor a b c d k hstride hk seed)
  have hcount :
      3 * (cwSquareMarkedWords a b c d k).card * rothNumberNat (p / 2) ≤
        4 * (p * p) * copies := by
    simpa only [p, copies, cwSquareOuterBuckets_card] using hcountNat
  have hhashed := cwSquareMarginalCard_le_hashLoss_mul_outerCopies
    ha hb hc hd hk
    (cwSquareOuterHashRequirement_lt_modulus a b c d k)
    (cwSquareOuterHashModulus_le hstride hk) hcount
  have hentropy :=
    WordType.proportionalEntropyBase_pow_le_structuralZeroLoss_mul_multinomial
      (cwSquareBaseMarginal a b c d) k
  rw [← card_cwSquareMarginalTypeClass_eq_multinomial hstride hk] at hentropy
  calc
    cwSquareOuterEntropyBase a b c d ^ k ≤
        WordType.structuralZeroMultinomialLoss
            (cwSquareBaseMarginal a b c d) k *
          ((WordType.typeClass (cwSquareDepth a b c d k + 1)
            (cwSquareMarginalType a b c d k)).card : ℝ) := hentropy
    _ ≤ WordType.structuralZeroMultinomialLoss
            (cwSquareBaseMarginal a b c d) k *
          (96 * cwSquareOuterTypeLoss a b c d k *
            Real.exp (cwSquareHashExponentCoefficient a b c d *
              √(((k + 1 : ℕ) : ℝ))) * (copies : ℝ)) := by
      exact mul_le_mul_of_nonneg_left hhashed
        (WordType.structuralZeroMultinomialLoss_pos _ _).le
    _ = cwSquareOuterSurvivorLoss a b c d k * (copies : ℝ) := by
      unfold cwSquareOuterSurvivorLoss
      ring

/-! ## Eventual entropy-rate growth -/

/-- **Every strict outer marginal-entropy base is eventually attained by the actual survivor
family.**

For every positive `W < cwSquareOuterEntropyBase a b c d`, all sufficiently large proportional
repetitions have a canonical seed with at least `W^k` surviving outer blocks.  The conclusion
retains the positive repetition proof and the exact finite survivor type, so a tensor/value client
can immediately instantiate its finite direct-sum constructor.

Proof sketch: apply the generic subexponential copy-growth theorem to
`cwSquareOuterSurvivorLoss`; the preceding finite theorem supplies its hypothesis at each positive
repetition. -/
theorem exists_eventually_cwSquareOuterSurvivorGrowth
    {a b c d : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    {W : ℝ} (hW : 0 < W) (hWlt : W < cwSquareOuterEntropyBase a b c d) :
    ∃ cutoff : ℕ, ∀ k : ℕ, cutoff ≤ k →
      ∃ hk : 0 < k,
        ∃ hstride : 0 < cwSquareStride a b c d,
          ∃ seed : CWSquareOuterCanonicalSeed a b c d k hstride hk,
            W ^ k ≤ Fintype.card
              (CWSquareOuterCanonicalSurvivor a b c d k hstride hk seed) := by
  obtain ⟨cutoff, hgrowth⟩ :=
    (cwSquareOuterSurvivorLoss_subexponential a b c d).exists_forall_pow_le_natCast_of_pow_le_mul
      hW hWlt
  refine ⟨max cutoff 1, fun k hkcutoff ↦ ?_⟩
  have hk : 0 < k := by
    have : 1 ≤ k := (le_max_right cutoff 1).trans hkcutoff
    omega
  obtain ⟨hstride, seed, hfinite⟩ :=
    exists_cwSquareOuterGoodSeed_count ha hb hc hd hk
  refine ⟨hk, hstride, seed, ?_⟩
  exact hgrowth k
    (Fintype.card
      (CWSquareOuterCanonicalSurvivor a b c d k hstride hk seed))
    ((le_max_left cutoff 1).trans hkcutoff) hfinite

end AlgebraicComplexity.Examples
