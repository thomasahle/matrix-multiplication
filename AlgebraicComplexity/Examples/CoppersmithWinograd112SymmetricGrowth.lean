/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Analysis.BehrendRate
import AlgebraicComplexity.Examples.CoppersmithWinograd112SymmetricValue
import AlgebraicComplexity.MatrixMultiplication.RationalTypedLeafMarginalHashingGrowth
import AlgebraicComplexity.MatrixMultiplication.Volume

/-!
# Survivor growth for the symmetric CW `112` value extraction

This module supplies the asymptotic counting bridge deliberately omitted from
`CoppersmithWinograd112SymmetricValue`.  For each positive proportional repetition it chooses

1. the first prime above the exact three-marginal collision requirement;
2. a Behrend progression-free subset of half that prime field; and
3. a good affine-hashing seed.

The resulting survivor family is the exact finite index type used by the checked cyclic
degeneration-value certificate.  The generic typed-leaf growth theorem shows that the modulus
has exponential base `jointEntropyBase / marginalEntropyBase`; Behrend cancellation therefore
leaves every strict base below `marginalEntropyBase` in the copy count.  For the symmetric CW leaf
that marginal has the desired `2 + H₂(μ,μ,1-2μ)` entropy.

No value superadditivity or final `q = 6` scalar optimization occurs here.  Those consume the
certificate sequence proved in this file.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor

universe u

variable (K : Type u) [CommRing K]

/-- Short name for the actual-partition symmetric rational typed leaf. -/
noncomputable abbrev cw112SymmetricLeaf
    (q L G : ℕ) (hq : 0 < q) (hL : 0 < L) (hG : 0 < G) :=
  cw112SymmetricPartitionRationalTypedLeaf K q L G hq hL hG

/-- The actual partition-support leaf has the same visible marginal entropy formula as its
Cartesian 64-address presentation. -/
theorem cw112SymmetricLeaf_marginalEntropyBits
    (q L G : ℕ) (hq : 0 < q) (hL : 0 < L) (hG : 0 < G) (c : Leg) :
    (cw112SymmetricLeaf K q L G hq hL hG).marginalEntropyBits c =
      2 + cw112MuEntropyBits L G := by
  rw [cw112SymmetricLeaf, cw112SymmetricPartitionRationalTypedLeaf,
    RationalTypedLeaf.marginalEntropyBits_reindex,
    cw112SymmetricRationalTypedLeaf_marginalEntropyBits]

/-- The actual partition-support leaf keeps the exact cyclic profile mass `[2(L+G)]³`. -/
@[simp] theorem cw112SymmetricLeaf_profile_mass
    (q L G : ℕ) (hq : 0 < q) (hL : 0 < L) (hG : 0 < G) :
    (cw112SymmetricLeaf K q L G hq hL hG).profile.mass =
      (2 * (L + G)) ^ 3 := by
  unfold cw112SymmetricLeaf cw112SymmetricPartitionRationalTypedLeaf
  change ((cw112SymmetricRationalTypedLeaf q L G hq hL hG).profile.reindex
    (cw112SymmetricPartitionSupportEquiv K q)).mass = _
  rw [PositiveIntegralProfile.mass_reindex,
    cw112SymmetricRationalTypedLeaf_mass]

/-- Common exponential base of each of the three compound marginal type classes. -/
noncomputable def cw112SymmetricMarginalEntropyBase
    (q L G : ℕ) (hq : 0 < q) (hL : 0 < L) (hG : 0 < G) : ℝ :=
  (cw112SymmetricLeaf K q L G hq hL hG).marginalEntropyBase .X

/-- All three marginal entropy bases agree.  The cyclic product has deliberately made the
rectangular primitive leaf symmetric before hashing. -/
theorem cw112SymmetricLeaf_marginalEntropyBase_eq
    (q L G : ℕ) (hq : 0 < q) (hL : 0 < L) (hG : 0 < G) (c : Leg) :
    (cw112SymmetricLeaf K q L G hq hL hG).marginalEntropyBase c =
      cw112SymmetricMarginalEntropyBase K q L G hq hL hG := by
  unfold cw112SymmetricMarginalEntropyBase
  rw [RationalTypedLeaf.marginalEntropyBase_eq_exp,
    RationalTypedLeaf.marginalEntropyBase_eq_exp,
    cw112SymmetricLeaf_marginalEntropyBits,
    cw112SymmetricLeaf_marginalEntropyBits]

/-- Closed entropy formula for the common visible marginal base. -/
theorem cw112SymmetricMarginalEntropyBase_eq_exp
    (q L G : ℕ) (hq : 0 < q) (hL : 0 < L) (hG : 0 < G) :
    cw112SymmetricMarginalEntropyBase K q L G hq hL hG =
      Real.exp ((((2 * (L + G)) ^ 3 : ℕ) : ℝ) * Real.log 2 *
        (2 + cw112MuEntropyBits L G)) := by
  unfold cw112SymmetricMarginalEntropyBase
  rw [RationalTypedLeaf.marginalEntropyBase_eq_exp,
    cw112SymmetricLeaf_profile_mass,
    cw112SymmetricLeaf_marginalEntropyBits]

/-- Exponential base of the exact 64-address joint type selected before hashing. -/
noncomputable def cw112SymmetricJointEntropyBase
    (q L G : ℕ) (hq : 0 < q) (hL : 0 < L) (hG : 0 < G) : ℝ :=
  (cw112SymmetricLeaf K q L G hq hL hG).jointEntropyBase

/-- Exponential base required by the canonical finite hashing field.

It is the joint-type base divided by one common visible marginal base.  Hashing later divides the
joint count by this field scale and therefore leaves precisely the visible marginal base. -/
noncomputable def cw112SymmetricFieldEntropyBase
    (q L G : ℕ) (hq : 0 < q) (hL : 0 < L) (hG : 0 < G) : ℝ :=
  cw112SymmetricJointEntropyBase K q L G hq hL hG /
    cw112SymmetricMarginalEntropyBase K q L G hq hL hG

/-- The symmetric joint entropy base is positive. -/
theorem cw112SymmetricJointEntropyBase_pos
    (q L G : ℕ) (hq : 0 < q) (hL : 0 < L) (hG : 0 < G) :
    0 < cw112SymmetricJointEntropyBase K q L G hq hL hG := by
  exact (cw112SymmetricLeaf K q L G hq hL hG).jointEntropyBase_pos

/-- The common symmetric marginal entropy base is positive. -/
theorem cw112SymmetricMarginalEntropyBase_pos
    (q L G : ℕ) (hq : 0 < q) (hL : 0 < L) (hG : 0 < G) :
    0 < cw112SymmetricMarginalEntropyBase K q L G hq hL hG := by
  exact (cw112SymmetricLeaf K q L G hq hL hG).marginalEntropyBase_pos .X

/-- The field entropy base is positive. -/
theorem cw112SymmetricFieldEntropyBase_pos
    (q L G : ℕ) (hq : 0 < q) (hL : 0 < L) (hG : 0 < G) :
    0 < cw112SymmetricFieldEntropyBase K q L G hq hL hG := by
  exact div_pos
    (cw112SymmetricJointEntropyBase_pos K q L G hq hL hG)
    (cw112SymmetricMarginalEntropyBase_pos K q L G hq hL hG)

/-- The field entropy base is at least one: it is the entropy base of a deterministic marginal
fiber. -/
theorem cw112SymmetricFieldEntropyBase_one_le
    (q L G : ℕ) (hq : 0 < q) (hL : 0 < L) (hG : 0 < G) :
    1 ≤ cw112SymmetricFieldEntropyBase K q L G hq hL hG := by
  unfold cw112SymmetricFieldEntropyBase cw112SymmetricJointEntropyBase
  exact RationalTypedLeaf.one_le_jointEntropyBase_div_marginalEntropyBase
    (cw112SymmetricLeaf K q L G hq hL hG) .X

/-- The harmless rational factor and the joint-type multinomial loss occurring in the finite
survivor inequality. -/
noncomputable def cw112SymmetricHashCountLoss
    (q L G : ℕ) (hq : 0 < q) (hL : 0 < L) (hG : 0 < G) (k : ℕ) : ℝ :=
  (4 / 3 : ℝ) * (cw112SymmetricLeaf K q L G hq hL hG).jointTypeLoss k

/-- The finite survivor-count loss is subexponential. -/
theorem cw112SymmetricHashCountLoss_subexponential
    (q L G : ℕ) (hq : 0 < q) (hL : 0 < L) (hG : 0 < G) :
    Growth.Subexponential
      (cw112SymmetricHashCountLoss K q L G hq hL hG) := by
  exact (cw112SymmetricLeaf K q L G hq hL hG).jointTypeLoss_subexponential.const_mul
    (by norm_num)

/-- Exact finite collision requirement for symmetric three-marginal hashing. -/
noncomputable def cw112SymmetricHashingRequirement
    (q L G k : ℕ) (hq : 0 < q) (hL : 0 < L) (hG : 0 < G) : ℕ :=
  (cw112SymmetricLeaf K q L G hq hL hG).hashingRequirement k

/-- Canonical safe prime modulus: the first Bertrand prime above both `27` and the exact
collision requirement. -/
noncomputable def cw112SymmetricHashModulus
    (q L G k : ℕ) (hq : 0 < q) (hL : 0 < L) (hG : 0 < G) : ℕ :=
  PrimeFieldSizing.modulus 27
    (cw112SymmetricHashingRequirement K q L G k hq hL hG)

/-- The canonical symmetric hashing modulus is prime. -/
theorem cw112SymmetricHashModulus_prime
    (q L G k : ℕ) (hq : 0 < q) (hL : 0 < L) (hG : 0 < G) :
    (cw112SymmetricHashModulus K q L G k hq hL hG).Prime :=
  PrimeFieldSizing.modulus_prime 27
    (cw112SymmetricHashingRequirement K q L G k hq hL hG)

noncomputable instance instFactCW112SymmetricHashModulusPrime
    (q L G k : ℕ) (hq : 0 < q) (hL : 0 < L) (hG : 0 < G) :
    Fact (cw112SymmetricHashModulus K q L G k hq hL hG).Prime :=
  ⟨cw112SymmetricHashModulus_prime K q L G k hq hL hG⟩

/-- The canonical prime is large enough for the injective 64-address field encoding. -/
theorem cw112SymmetricHashModulus_ge_twentySeven
    (q L G k : ℕ) (hq : 0 < q) (hL : 0 < L) (hG : 0 < G) :
    27 ≤ cw112SymmetricHashModulus K q L G k hq hL hG := by
  have h := PrimeFieldSizing.characteristicFloor_lt_modulus 27
    (cw112SymmetricHashingRequirement K q L G k hq hL hG)
  simpa only [cw112SymmetricHashModulus] using h.le

/-- The canonical prime modulus has the predicted entropy-quotient base, up to the generic
subexponential prime-selection loss. -/
theorem cw112SymmetricHashModulus_cast_le
    (q L G : ℕ) (hq : 0 < q) (hL : 0 < L) (hG : 0 < G)
    {k : ℕ} (hk : 0 < k) :
    (cw112SymmetricHashModulus K q L G k hq hL hG : ℝ) ≤
      (cw112SymmetricLeaf K q L G hq hL hG).hashingModulusLoss k *
        cw112SymmetricFieldEntropyBase K q L G hq hL hG ^ k := by
  simpa only [cw112SymmetricHashModulus, cw112SymmetricHashingRequirement,
    cw112SymmetricFieldEntropyBase, cw112SymmetricJointEntropyBase] using
    (cw112SymmetricLeaf K q L G hq hL hG).hashingModulus_cast_le_loss_mul_entropyQuotient_pow
      (cw112SymmetricPartitionRationalTypedLeaf_isSupportCoordinate
        K q L G hq hL hG)
      (cw112SymmetricPartitionRationalTypedLeaf_isMaximumEntropyBits
        K q L G hq hL hG)
      (cw112SymmetricMarginalEntropyBase K q L G hq hL hG)
      (cw112SymmetricLeaf_marginalEntropyBase_eq K q L G hq hL hG)
      (cw112SymmetricFieldEntropyBase_one_le K q L G hq hL hG) hk

/-- Canonically chosen Behrend bucket set in the safe prime field. -/
noncomputable def cw112SymmetricBuckets
    (q L G k : ℕ) (hq : 0 < q) (hL : 0 < L) (hG : 0 < G) :
    Finset (ZMod (cw112SymmetricHashModulus K q L G k hq hL hG)) :=
  Classical.choose
    (exists_threeAPFree_zmod_half
      (cw112SymmetricHashModulus K q L G k hq hL hG))

/-- The canonical bucket set has the exact Behrend extremal cardinality. -/
theorem cw112SymmetricBuckets_card
    (q L G k : ℕ) (hq : 0 < q) (hL : 0 < L) (hG : 0 < G) :
    (cw112SymmetricBuckets K q L G k hq hL hG).card =
      rothNumberNat
        (cw112SymmetricHashModulus K q L G k hq hL hG / 2) :=
  (Classical.choose_spec
    (exists_threeAPFree_zmod_half
      (cw112SymmetricHashModulus K q L G k hq hL hG))).1

/-- The canonical bucket set contains no nontrivial three-term arithmetic progression. -/
theorem cw112SymmetricBuckets_threeAPFree
    (q L G k : ℕ) (hq : 0 < q) (hL : 0 < L) (hG : 0 < G) :
    ThreeAPFree
      (cw112SymmetricBuckets K q L G k hq hL hG :
        Set (ZMod (cw112SymmetricHashModulus K q L G k hq hL hG))) :=
  (Classical.choose_spec
    (exists_threeAPFree_zmod_half
      (cw112SymmetricHashModulus K q L G k hq hL hG))).2

/-- The canonical affine-hashing seed type at repetition `k`. -/
noncomputable abbrev CW112SymmetricCanonicalSeed
    (q L G k : ℕ) (hq : 0 < q) (hL : 0 < L) (hG : 0 < G) :=
  ProgressionHash.Seed
    (ZMod (cw112SymmetricHashModulus K q L G k hq hL hG))
    (Fin ((cw112SymmetricLeaf K q L G hq hL hG).proportionalDepth k + 1))

/-- The exact finite survivor type for the canonical prime and Behrend bucket choices. -/
noncomputable abbrev CW112SymmetricCanonicalSurvivor
    (q L G k : ℕ) (hq : 0 < q) (hL : 0 < L) (hG : 0 < G)
    (seed : CW112SymmetricCanonicalSeed K q L G k hq hL hG) :=
  CW112SymmetricSurvivor K q L G k
    (cw112SymmetricHashModulus K q L G k hq hL hG)
    hq hL hG
    (cw112SymmetricHashModulus_ge_twentySeven K q L G k hq hL hG)
    (cw112SymmetricBuckets K q L G k hq hL hG) seed

/-- Package one nonempty canonical survivor family as the exact finite cyclic degeneration-value
certificate used by the value calculus. -/
noncomputable def cw112SymmetricCanonicalDegenerationValueCertificate
    (τ : ℝ) (q L G k : ℕ) (hq : 0 < q) (hL : 0 < L) (hG : 0 < G)
    (hk : 0 < k)
    (seed : CW112SymmetricCanonicalSeed K q L G k hq hL hG)
    (hnonempty : Nonempty
      (CW112SymmetricCanonicalSurvivor K q L G k hq hL hG seed)) :
    CyclicDegenerationCertificate K (cw112PartitionedTensor K q).realize τ := by
  letI := hnonempty
  exact cw112SymmetricDegenerationValueCertificate K τ q L G k
    (cw112SymmetricHashModulus K q L G k hq hL hG)
    hq hL hG hk
    (cw112SymmetricHashModulus_ge_twentySeven K q L G k hq hL hG)
    (cw112SymmetricBuckets K q L G k hq hL hG)
    (cw112SymmetricBuckets_threeAPFree K q L G k hq hL hG) seed

/-- The canonical certificate's source power is the typed leaf's exact word length. -/
@[simp] theorem cw112SymmetricCanonicalDegenerationValueCertificate_power
    (τ : ℝ) (q L G k : ℕ) (hq : 0 < q) (hL : 0 < L) (hG : 0 < G)
    (hk : 0 < k)
    (seed : CW112SymmetricCanonicalSeed K q L G k hq hL hG)
    (hnonempty : Nonempty
      (CW112SymmetricCanonicalSurvivor K q L G k hq hL hG seed)) :
    (cw112SymmetricCanonicalDegenerationValueCertificate
      K τ q L G k hq hL hG hk seed hnonempty).power =
      (cw112SymmetricLeaf K q L G hq hL hG).proportionalDepth k + 1 := by
  rfl

/-- The canonical certificate records exactly the number of surviving hash addresses. -/
@[simp] theorem cw112SymmetricCanonicalDegenerationValueCertificate_copies
    (τ : ℝ) (q L G k : ℕ) (hq : 0 < q) (hL : 0 < L) (hG : 0 < G)
    (hk : 0 < k)
    (seed : CW112SymmetricCanonicalSeed K q L G k hq hL hG)
    (hnonempty : Nonempty
      (CW112SymmetricCanonicalSurvivor K q L G k hq hL hG seed)) :
    (cw112SymmetricCanonicalDegenerationValueCertificate
      K τ q L G k hq hL hG hk seed hnonempty).copies =
      Fintype.card
        (CW112SymmetricCanonicalSurvivor K q L G k hq hL hG seed) := by
  rfl

/-- Each `X` dimension in the canonical certificate is the typed-leaf product raised to `k`. -/
@[simp] theorem cw112SymmetricCanonicalDegenerationValueCertificate_xSize
    (τ : ℝ) (q L G k : ℕ) (hq : 0 < q) (hL : 0 < L) (hG : 0 < G)
    (hk : 0 < k)
    (seed : CW112SymmetricCanonicalSeed K q L G k hq hL hG)
    (hnonempty : Nonempty
      (CW112SymmetricCanonicalSurvivor K q L G k hq hL hG seed))
    (i : Fin (cw112SymmetricCanonicalDegenerationValueCertificate
      K τ q L G k hq hL hG hk seed hnonempty).copies) :
    (cw112SymmetricCanonicalDegenerationValueCertificate
      K τ q L G k hq hL hG hk seed hnonempty).xSize i =
      (cw112SymmetricLeaf K q L G hq hL hG).dimensionProduct .X ^ k := by
  rfl

/-- Each `Y` dimension in the canonical certificate is the typed-leaf product raised to `k`. -/
@[simp] theorem cw112SymmetricCanonicalDegenerationValueCertificate_ySize
    (τ : ℝ) (q L G k : ℕ) (hq : 0 < q) (hL : 0 < L) (hG : 0 < G)
    (hk : 0 < k)
    (seed : CW112SymmetricCanonicalSeed K q L G k hq hL hG)
    (hnonempty : Nonempty
      (CW112SymmetricCanonicalSurvivor K q L G k hq hL hG seed))
    (i : Fin (cw112SymmetricCanonicalDegenerationValueCertificate
      K τ q L G k hq hL hG hk seed hnonempty).copies) :
    (cw112SymmetricCanonicalDegenerationValueCertificate
      K τ q L G k hq hL hG hk seed hnonempty).ySize i =
      (cw112SymmetricLeaf K q L G hq hL hG).dimensionProduct .Y ^ k := by
  rfl

/-- Each `Z` dimension in the canonical certificate is the typed-leaf product raised to `k`. -/
@[simp] theorem cw112SymmetricCanonicalDegenerationValueCertificate_zSize
    (τ : ℝ) (q L G k : ℕ) (hq : 0 < q) (hL : 0 < L) (hG : 0 < G)
    (hk : 0 < k)
    (seed : CW112SymmetricCanonicalSeed K q L G k hq hL hG)
    (hnonempty : Nonempty
      (CW112SymmetricCanonicalSurvivor K q L G k hq hL hG seed))
    (i : Fin (cw112SymmetricCanonicalDegenerationValueCertificate
      K τ q L G k hq hL hG hk seed hnonempty).copies) :
    (cw112SymmetricCanonicalDegenerationValueCertificate
      K τ q L G k hq hL hG hk seed hnonempty).zSize i =
      (cw112SymmetricLeaf K q L G hq hL hG).dimensionProduct .Z ^ k := by
  rfl

/-- Exact normalized term of the canonical equal-dimension certificate.

The expression keeps the three dimension products separate so it remains valid without first
using the CW-specific proof that they agree.  Downstream numerical clients may rewrite all three
with `cw112SymmetricPartitionRationalTypedLeaf_dimensionProduct`. -/
theorem cw112SymmetricCanonicalDegenerationValueCertificate_term
    (τ : ℝ) (q L G k : ℕ) (hq : 0 < q) (hL : 0 < L) (hG : 0 < G)
    (hk : 0 < k)
    (seed : CW112SymmetricCanonicalSeed K q L G k hq hL hG)
    (hnonempty : Nonempty
      (CW112SymmetricCanonicalSurvivor K q L G k hq hL hG seed)) :
    (cw112SymmetricCanonicalDegenerationValueCertificate
      K τ q L G k hq hL hG hk seed hnonempty).term =
      ((Fintype.card
          (CW112SymmetricCanonicalSurvivor K q L G k hq hL hG seed) : ℝ) *
        (((cw112SymmetricLeaf K q L G hq hL hG).dimensionProduct .X ^ k *
            (cw112SymmetricLeaf K q L G hq hL hG).dimensionProduct .Y ^ k *
            (cw112SymmetricLeaf K q L G hq hL hG).dimensionProduct .Z ^ k : ℕ) : ℝ) ^ τ) ^
        (((3 * ((cw112SymmetricLeaf K q L G hq hL hG).proportionalDepth k + 1) : ℕ) : ℝ)⁻¹) := by
  unfold CyclicDegenerationCertificate.term CyclicExtractionCertificate.term cyclicValueTerm
  let certificate := cw112SymmetricCanonicalDegenerationValueCertificate
    K τ q L G k hq hL hG hk seed hnonempty
  have hpower : certificate.power =
      (cw112SymmetricLeaf K q L G hq hL hG).proportionalDepth k + 1 :=
    cw112SymmetricCanonicalDegenerationValueCertificate_power
      K τ q L G k hq hL hG hk seed hnonempty
  have hcopies : certificate.copies =
      Fintype.card
        (CW112SymmetricCanonicalSurvivor K q L G k hq hL hG seed) :=
    cw112SymmetricCanonicalDegenerationValueCertificate_copies
      K τ q L G k hq hL hG hk seed hnonempty
  have hx : certificate.xSize = fun _ ↦
      (cw112SymmetricLeaf K q L G hq hL hG).dimensionProduct .X ^ k := by
    funext i
    exact cw112SymmetricCanonicalDegenerationValueCertificate_xSize
      K τ q L G k hq hL hG hk seed hnonempty i
  have hy : certificate.ySize = fun _ ↦
      (cw112SymmetricLeaf K q L G hq hL hG).dimensionProduct .Y ^ k := by
    funext i
    exact cw112SymmetricCanonicalDegenerationValueCertificate_ySize
      K τ q L G k hq hL hG hk seed hnonempty i
  have hz : certificate.zSize = fun _ ↦
      (cw112SymmetricLeaf K q L G hq hL hG).dimensionProduct .Z ^ k := by
    funext i
    exact cw112SymmetricCanonicalDegenerationValueCertificate_zSize
      K τ q L G k hq hL hG hk seed hnonempty i
  change (matrixMultiplicationVolumePowerSum certificate.xSize certificate.ySize
      certificate.zSize τ) ^ (((3 * certificate.power : ℕ) : ℝ)⁻¹) = _
  rw [hpower, hx, hy, hz, matrixMultiplicationVolumePowerSum_const, hcopies]

/-- Explicit lower term obtained by replacing the exact survivor count with a certified base
`W^k`. -/
noncomputable def cw112SymmetricFiniteLowerTerm
    (W τ : ℝ) (q L G k : ℕ) (hq : 0 < q) (hL : 0 < L) (hG : 0 < G) : ℝ :=
  ((W ^ k) *
      (((cw112SymmetricLeaf K q L G hq hL hG).dimensionProduct .X ^ k *
          (cw112SymmetricLeaf K q L G hq hL hG).dimensionProduct .Y ^ k *
          (cw112SymmetricLeaf K q L G hq hL hG).dimensionProduct .Z ^ k : ℕ) : ℝ) ^ τ) ^
    (((3 * ((cw112SymmetricLeaf K q L G hq hL hG).proportionalDepth k + 1) : ℕ) : ℝ)⁻¹)

/-- Repetition-independent normalization of the symmetric finite lower term. -/
noncomputable def cw112SymmetricLimitLowerTerm
    (W τ : ℝ) (q L G : ℕ) (hq : 0 < q) (hL : 0 < L) (hG : 0 < G) : ℝ :=
  (W *
      (((cw112SymmetricLeaf K q L G hq hL hG).dimensionProduct .X *
          (cw112SymmetricLeaf K q L G hq hL hG).dimensionProduct .Y *
          (cw112SymmetricLeaf K q L G hq hL hG).dimensionProduct .Z : ℕ) : ℝ) ^ τ) ^
    (((3 * (cw112SymmetricLeaf K q L G hq hL hG).profile.mass : ℕ) : ℝ)⁻¹)

/-- The apparent dependence of `cw112SymmetricFiniteLowerTerm` on the repetition disappears after
normalization.

Proof sketch: the exact word length is `profile.mass * k`, all three dimensions are `k`th powers,
and the copy lower bound is `W^k`.  Thus the quantity under the outer real power is itself the
`k`th power of the one-repetition quantity; the factor `k` cancels from the normalizing exponent. -/
theorem cw112SymmetricFiniteLowerTerm_eq_limit
    (W τ : ℝ) (q L G k : ℕ) (hq : 0 < q) (hL : 0 < L) (hG : 0 < G)
    (hk : 0 < k) (hW : 0 < W) :
    cw112SymmetricFiniteLowerTerm K W τ q L G k hq hL hG =
      cw112SymmetricLimitLowerTerm K W τ q L G hq hL hG := by
  let leaf := cw112SymmetricLeaf K q L G hq hL hG
  unfold cw112SymmetricFiniteLowerTerm cw112SymmetricLimitLowerTerm
  change ((W ^ k) *
      (((leaf.dimensionProduct .X ^ k * leaf.dimensionProduct .Y ^ k *
          leaf.dimensionProduct .Z ^ k : ℕ) : ℝ) ^ τ)) ^
        (((3 * (leaf.proportionalDepth k + 1) : ℕ) : ℝ)⁻¹) =
      (W * (((leaf.dimensionProduct .X * leaf.dimensionProduct .Y *
          leaf.dimensionProduct .Z : ℕ) : ℝ) ^ τ)) ^
        (((3 * leaf.profile.mass : ℕ) : ℝ)⁻¹)
  rw [leaf.proportionalDepth_add_one hk]
  exact normalizedConstantVolumePower_eq W τ
    (leaf.dimensionProduct .X) (leaf.dimensionProduct .Y) (leaf.dimensionProduct .Z)
    leaf.profile.mass k hW (leaf.dimensionProduct_pos .X) (leaf.dimensionProduct_pos .Y)
    (leaf.dimensionProduct_pos .Z) leaf.profile.mass_pos hk

/-- A lower bound on the survivor count gives the corresponding lower bound on the actual finite
cyclic degeneration-value term.

Proof sketch: use the exact constant-family term formula above, multiply the copy-count inequality
by the nonnegative matrix-volume contribution, and apply monotonicity of real powers at the
positive normalizing exponent. -/
theorem cw112SymmetricFiniteLowerTerm_le_certificate
    (W τ : ℝ) (q L G k : ℕ) (hq : 0 < q) (hL : 0 < L) (hG : 0 < G)
    (hk : 0 < k) (hW : 0 ≤ W)
    (seed : CW112SymmetricCanonicalSeed K q L G k hq hL hG)
    (hnonempty : Nonempty
      (CW112SymmetricCanonicalSurvivor K q L G k hq hL hG seed))
    (hcopies : W ^ k ≤
      (Fintype.card
        (CW112SymmetricCanonicalSurvivor K q L G k hq hL hG seed) : ℝ)) :
    cw112SymmetricFiniteLowerTerm K W τ q L G k hq hL hG ≤
      (cw112SymmetricCanonicalDegenerationValueCertificate
        K τ q L G k hq hL hG hk seed hnonempty).term := by
  rw [cw112SymmetricCanonicalDegenerationValueCertificate_term]
  unfold cw112SymmetricFiniteLowerTerm
  apply Real.rpow_le_rpow
  · exact mul_nonneg (pow_nonneg hW k) (Real.rpow_nonneg (Nat.cast_nonneg _) τ)
  · exact mul_le_mul_of_nonneg_right hcopies (Real.rpow_nonneg (Nat.cast_nonneg _) τ)
  · exact inv_nonneg.mpr (Nat.cast_nonneg _)

/-- At every positive repetition, the canonical prime field and Behrend buckets have a seed
with the exact division-free survivor inequality.

This theorem is still finite.  Its conclusion also retains legwise injectivity, which is useful
for clients that want the raw direct-sum restriction rather than only its cardinality. -/
theorem exists_cw112SymmetricGoodSeed
    (q L G k : ℕ) (hq : 0 < q) (hL : 0 < L) (hG : 0 < G)
    (hk : 0 < k) :
    ∃ seed : ProgressionHash.Seed
        (ZMod (cw112SymmetricHashModulus K q L G k hq hL hG))
        (Fin ((cw112SymmetricLeaf K q L G hq hL hG).proportionalDepth k + 1)),
      3 * ((cw112SymmetricLeaf K q L G hq hL hG).markedWords k).card *
          (cw112SymmetricBuckets K q L G k hq hL hG).card ≤
        4 * (cw112SymmetricHashModulus K q L G k hq hL hG *
          cw112SymmetricHashModulus K q L G k hq hL hG) *
          ((cw112SymmetricPartitionHashEncoding K q
              (cw112SymmetricHashModulus K q L G k hq hL hG)
              (cw112SymmetricHashModulus_ge_twentySeven K q L G k hq hL hG)
            ).markedLegwiseIsolatedPowerAddresses
              ((cw112SymmetricLeaf K q L G hq hL hG).proportionalDepth k)
              ((cw112SymmetricLeaf K q L G hq hL hG).ambientWords k)
              ((cw112SymmetricLeaf K q L G hq hL hG).markedWords k)
              (cw112SymmetricBuckets K q L G k hq hL hG) seed).card := by
  let leaf := cw112SymmetricLeaf K q L G hq hL hG
  let requirement := cw112SymmetricHashingRequirement K q L G k hq hL hG
  let p := cw112SymmetricHashModulus K q L G k hq hL hG
  let hp := cw112SymmetricHashModulus_ge_twentySeven K q L G k hq hL hG
  let H := cw112SymmetricPartitionHashEncoding K q p hp
  let B := cw112SymmetricBuckets K q L G k hq hL hG
  letI : NeZero (2 : ZMod p) :=
    PrimeFieldSizing.neZeroTwo 27 requirement (by norm_num)
  have hfield : leaf.hashingRequirement k ≤ Fintype.card (ZMod p) := by
    simpa only [ZMod.card, leaf, requirement, p, cw112SymmetricHashingRequirement,
      cw112SymmetricHashModulus] using
      (Nat.le_of_lt (PrimeFieldSizing.requirement_lt_modulus 27 requirement))
  obtain ⟨seed, hcount, _hsubset, _hinjective⟩ :=
    leaf.exists_seed_many_markedIsolatedPowerAddresses
      (cw112SymmetricPartitionRationalTypedLeaf_isSupportCoordinate
        K q L G hq hL hG)
      H hk B (by
        simpa only [B, p] using
          cw112SymmetricBuckets_threeAPFree K q L G k hq hL hG) hfield
  refine ⟨seed, ?_⟩
  simpa only [leaf, p, hp, H, B, ZMod.card] using hcount

/-- At every positive repetition, some canonical hash seed satisfies the real-valued counting
inequality expected by the Behrend growth theorem.

The left side is the full joint entropy exponential times the exact progression-free-set size.
The right side contains the squared field modulus, the actual survivor count, and only the
explicit subexponential joint-type loss.

Proof sketch: multiply the standard multinomial lower bound for the marked joint type by the
Behrend bucket cardinality.  The finite good-seed theorem bounds this product, after division by
three, by `4/3` times the squared modulus and the survivor cardinality. -/
theorem exists_cw112SymmetricGoodSeed_count
    (q L G k : ℕ) (hq : 0 < q) (hL : 0 < L) (hG : 0 < G)
    (hk : 0 < k) :
    ∃ seed : CW112SymmetricCanonicalSeed K q L G k hq hL hG,
      cw112SymmetricJointEntropyBase K q L G hq hL hG ^ k *
          (rothNumberNat
            (cw112SymmetricHashModulus K q L G k hq hL hG / 2) : ℝ) ≤
        cw112SymmetricHashCountLoss K q L G hq hL hG k *
          ((cw112SymmetricHashModulus K q L G k hq hL hG : ℝ) *
            (cw112SymmetricHashModulus K q L G k hq hL hG : ℝ)) *
          (Fintype.card
            (CW112SymmetricCanonicalSurvivor K q L G k hq hL hG seed) : ℝ) := by
  let leaf := cw112SymmetricLeaf K q L G hq hL hG
  let p := cw112SymmetricHashModulus K q L G k hq hL hG
  let B := cw112SymmetricBuckets K q L G k hq hL hG
  let hp := cw112SymmetricHashModulus_ge_twentySeven K q L G k hq hL hG
  let H := cw112SymmetricPartitionHashEncoding K q p hp
  obtain ⟨seed, hcountNat⟩ :=
    exists_cw112SymmetricGoodSeed K q L G k hq hL hG hk
  refine ⟨seed, ?_⟩
  have hmarked : leaf.jointEntropyBase ^ k ≤
      leaf.jointTypeLoss k * (leaf.markedWords k).card :=
    leaf.jointEntropyBase_pow_le_jointTypeLoss_mul_card_markedWords hk
  have hcountReal :
      3 * ((leaf.markedWords k).card : ℝ) * (B.card : ℝ) ≤
        4 * ((p : ℝ) * (p : ℝ)) *
          (Fintype.card
            (CW112SymmetricCanonicalSurvivor K q L G k hq hL hG seed) : ℝ) := by
    exact_mod_cast (by
      simpa only [leaf, p, hp, H, B, CW112SymmetricCanonicalSurvivor,
        CW112SymmetricSurvivor, Fintype.card_coe] using hcountNat)
  have hbucket : (B.card : ℝ) =
      (rothNumberNat (p / 2) : ℝ) := by
    exact_mod_cast (by
      simpa only [B, p] using
        cw112SymmetricBuckets_card K q L G k hq hL hG)
  have hseed :
      ((leaf.markedWords k).card : ℝ) * (rothNumberNat (p / 2) : ℝ) ≤
        (4 / 3 : ℝ) * ((p : ℝ) * (p : ℝ)) *
          (Fintype.card
            (CW112SymmetricCanonicalSurvivor K q L G k hq hL hG seed) : ℝ) := by
    rw [← hbucket]
    nlinarith [hcountReal]
  calc
    cw112SymmetricJointEntropyBase K q L G hq hL hG ^ k *
          (rothNumberNat
            (cw112SymmetricHashModulus K q L G k hq hL hG / 2) : ℝ) =
        leaf.jointEntropyBase ^ k * (rothNumberNat (p / 2) : ℝ) := by
          rfl
    _ ≤ (leaf.jointTypeLoss k * (leaf.markedWords k).card) *
          (rothNumberNat (p / 2) : ℝ) :=
      mul_le_mul_of_nonneg_right hmarked (by positivity)
    _ = leaf.jointTypeLoss k *
          (((leaf.markedWords k).card : ℝ) * (rothNumberNat (p / 2) : ℝ)) := by
      ring
    _ ≤ leaf.jointTypeLoss k *
          ((4 / 3 : ℝ) * ((p : ℝ) * (p : ℝ)) *
            (Fintype.card
              (CW112SymmetricCanonicalSurvivor K q L G k hq hL hG seed) : ℝ)) :=
      mul_le_mul_of_nonneg_left hseed (leaf.jointTypeLoss_pos k).le
    _ = cw112SymmetricHashCountLoss K q L G hq hL hG k *
          ((cw112SymmetricHashModulus K q L G k hq hL hG : ℝ) *
            (cw112SymmetricHashModulus K q L G k hq hL hG : ℝ)) *
          (Fintype.card
            (CW112SymmetricCanonicalSurvivor K q L G k hq hL hG seed) : ℝ) := by
      unfold cw112SymmetricHashCountLoss
      ring

/-- **Every strict visible-marginal base is eventually attained by the canonical symmetric CW
survivor family.**

For any `W` below the common marginal entropy base, all sufficiently large proportional
repetitions have a canonical affine seed with at least `W^k` surviving blocks.  This is the
sequence-level counting statement consumed by the cyclic degeneration-value certificate.

Proof sketch: the canonical prime is bounded by a subexponential loss times the field entropy
base.  The previous good-seed theorem supplies the matching Behrend counting inequality.  The
generic Behrend rate theorem cancels the joint base by the field base, leaving every strict base
below the common marginal base. -/
theorem exists_eventually_cw112SymmetricSurvivorGrowth
    (q L G : ℕ) (hq : 0 < q) (hL : 0 < L) (hG : 0 < G)
    {W : ℝ} (hW : 0 < W)
    (hWlt : W < cw112SymmetricMarginalEntropyBase K q L G hq hL hG) :
    ∃ N : ℕ, ∀ k : ℕ, N ≤ k →
      ∃ seed : CW112SymmetricCanonicalSeed K q L G k hq hL hG,
        W ^ k ≤
          (Fintype.card
            (CW112SymmetricCanonicalSurvivor K q L G k hq hL hG seed) : ℝ) := by
  let leaf := cw112SymmetricLeaf K q L G hq hL hG
  let A := cw112SymmetricJointEntropyBase K q L G hq hL hG
  let M := cw112SymmetricMarginalEntropyBase K q L G hq hL hG
  let D := cw112SymmetricFieldEntropyBase K q L G hq hL hG
  have hA : 0 < A := cw112SymmetricJointEntropyBase_pos K q L G hq hL hG
  have hM : 0 < M := cw112SymmetricMarginalEntropyBase_pos K q L G hq hL hG
  have hD : 0 < D := cw112SymmetricFieldEntropyBase_pos K q L G hq hL hG
  have hcancel : A / (A / M) = M := by
    field_simp [hA.ne', hM.ne']
  have hWA : W < A / D := by
    change W < A / (A / M)
    rw [hcancel]
    exact hWlt
  obtain ⟨N₀, hgrowth⟩ :=
    Growth.exists_forall_pow_le_copies_of_subexponential_modulus
      (A := A) (D := D) (W := W)
      (modulusLoss := leaf.hashingModulusLoss)
      (poly := cw112SymmetricHashCountLoss K q L G hq hL hG)
      hD leaf.hashingModulusLoss_subexponential
      (cw112SymmetricHashCountLoss_subexponential K q L G hq hL hG)
      hW hWA
  refine ⟨max N₀ 1, fun k hk ↦ ?_⟩
  have hk₀ : N₀ ≤ k := (le_max_left N₀ 1).trans hk
  have hkone : 1 ≤ k := (le_max_right N₀ 1).trans hk
  have hkpos : 0 < k := by omega
  obtain ⟨seed, hcount⟩ :=
    exists_cw112SymmetricGoodSeed_count K q L G k hq hL hG hkpos
  refine ⟨seed, hgrowth k
    (cw112SymmetricHashModulus K q L G k hq hL hG)
    (Fintype.card (CW112SymmetricCanonicalSurvivor K q L G k hq hL hG seed))
    hk₀ ?_ ?_ ?_⟩
  · exact (by
      have hp := cw112SymmetricHashModulus_ge_twentySeven K q L G k hq hL hG
      omega)
  · simpa only [D, leaf] using
      cw112SymmetricHashModulus_cast_le K q L G hq hL hG hkpos
  · simpa only [A] using hcount

/-- **Certificate form of symmetric CW survivor growth.**

Every strict base below the common visible marginal entropy base is eventually realized by a
genuine finite polynomial-degeneration certificate.  Its `copies` field is at least `W^k`; the
preceding projection lemmas give its exact source power and square matrix dimensions.

Proof sketch: apply `exists_eventually_cw112SymmetricSurvivorGrowth`.  Positivity of `W^k` forces
the chosen survivor type to be nonempty, which is precisely the final hypothesis needed by the
finite semantic certificate constructor. -/
theorem exists_eventually_cw112SymmetricDegenerationValueCertificate
    (τ : ℝ) (q L G : ℕ) (hq : 0 < q) (hL : 0 < L) (hG : 0 < G)
    {W : ℝ} (hW : 0 < W)
    (hWlt : W < cw112SymmetricMarginalEntropyBase K q L G hq hL hG) :
    ∃ N : ℕ, ∀ k : ℕ, N ≤ k →
      ∃ hkpos : 0 < k,
        ∃ seed : CW112SymmetricCanonicalSeed K q L G k hq hL hG,
          ∃ hnonempty : Nonempty
              (CW112SymmetricCanonicalSurvivor K q L G k hq hL hG seed),
            W ^ k ≤
              ((cw112SymmetricCanonicalDegenerationValueCertificate
                K τ q L G k hq hL hG hkpos seed hnonempty).copies : ℝ) := by
  obtain ⟨N, hgrowth⟩ :=
    exists_eventually_cw112SymmetricSurvivorGrowth K q L G hq hL hG
      hW hWlt
  refine ⟨max N 1, fun k hk ↦ ?_⟩
  have hkN : N ≤ k := (le_max_left N 1).trans hk
  have hkone : 1 ≤ k := (le_max_right N 1).trans hk
  have hkpos : 0 < k := by omega
  obtain ⟨seed, hseed⟩ := hgrowth k hkN
  have hcardReal :
      0 < (Fintype.card
        (CW112SymmetricCanonicalSurvivor K q L G k hq hL hG seed) : ℝ) :=
    (pow_pos hW k).trans_le hseed
  have hcardNat :
      0 < Fintype.card
        (CW112SymmetricCanonicalSurvivor K q L G k hq hL hG seed) := by
    exact_mod_cast hcardReal
  let hnonempty : Nonempty
      (CW112SymmetricCanonicalSurvivor K q L G k hq hL hG seed) :=
    Fintype.card_pos_iff.mp hcardNat
  refine ⟨hkpos, seed, hnonempty, ?_⟩
  simpa only [cw112SymmetricCanonicalDegenerationValueCertificate_copies] using hseed

/-- **Finite value-term form of the modern symmetric CW `112` extraction.**

For every strict copy base below the common marginal entropy base, all sufficiently large
repetitions yield an actual degeneration certificate whose normalized term dominates the explicit
finite lower term `cw112SymmetricFiniteLowerTerm`.

This is the final tensor/counting interface.  Subsequent work only simplifies the displayed real
expression and compares it with a border-rank bound. -/
theorem exists_eventually_cw112SymmetricFiniteLowerTerm_le_certificate
    (τ : ℝ) (q L G : ℕ) (hq : 0 < q) (hL : 0 < L) (hG : 0 < G)
    {W : ℝ} (hW : 0 < W)
    (hWlt : W < cw112SymmetricMarginalEntropyBase K q L G hq hL hG) :
    ∃ N : ℕ, ∀ k : ℕ, N ≤ k →
      ∃ hkpos : 0 < k,
        ∃ seed : CW112SymmetricCanonicalSeed K q L G k hq hL hG,
          ∃ hnonempty : Nonempty
              (CW112SymmetricCanonicalSurvivor K q L G k hq hL hG seed),
            cw112SymmetricFiniteLowerTerm K W τ q L G k hq hL hG ≤
              (cw112SymmetricCanonicalDegenerationValueCertificate
                K τ q L G k hq hL hG hkpos seed hnonempty).term := by
  obtain ⟨N, hcertificates⟩ :=
    exists_eventually_cw112SymmetricDegenerationValueCertificate
      K τ q L G hq hL hG hW hWlt
  refine ⟨N, fun k hk ↦ ?_⟩
  obtain ⟨hkpos, seed, hnonempty, hcopies⟩ := hcertificates k hk
  exact ⟨hkpos, seed, hnonempty,
    cw112SymmetricFiniteLowerTerm_le_certificate
      K W τ q L G k hq hL hG hkpos hW.le seed hnonempty hcopies⟩

/-- **Stable value interface for the symmetric CW `112` extraction.**

For every positive `W` strictly below the common marginal entropy base, sufficiently large
finite cyclic degeneration certificates dominate the *same*, repetition-independent value term
`cw112SymmetricLimitLowerTerm`.  This is the preferred interface for the generic `V_τ` calculus:
all tensor restriction, hashing, and subexponential-loss details are hidden behind an actual
finite degeneration certificate, while the numerical lower bound no longer mentions the
repetition parameter.

Proof sketch: use the eventual finite-certificate theorem and rewrite its lower term with
`cw112SymmetricFiniteLowerTerm_eq_limit`. -/
theorem exists_eventually_cw112SymmetricLimitLowerTerm_le_certificate
    (τ : ℝ) (q L G : ℕ) (hq : 0 < q) (hL : 0 < L) (hG : 0 < G)
    {W : ℝ} (hW : 0 < W)
    (hWlt : W < cw112SymmetricMarginalEntropyBase K q L G hq hL hG) :
    ∃ N : ℕ, ∀ k : ℕ, N ≤ k →
      ∃ hkpos : 0 < k,
        ∃ seed : CW112SymmetricCanonicalSeed K q L G k hq hL hG,
          ∃ hnonempty : Nonempty
              (CW112SymmetricCanonicalSurvivor K q L G k hq hL hG seed),
            cw112SymmetricLimitLowerTerm K W τ q L G hq hL hG ≤
              (cw112SymmetricCanonicalDegenerationValueCertificate
                K τ q L G k hq hL hG hkpos seed hnonempty).term := by
  obtain ⟨N, hcertificates⟩ :=
    exists_eventually_cw112SymmetricFiniteLowerTerm_le_certificate
      K τ q L G hq hL hG hW hWlt
  refine ⟨N, fun k hk ↦ ?_⟩
  obtain ⟨hkpos, seed, hnonempty, hterm⟩ := hcertificates k hk
  refine ⟨hkpos, seed, hnonempty, ?_⟩
  rw [← cw112SymmetricFiniteLowerTerm_eq_limit
    K W τ q L G k hq hL hG hkpos hW]
  exact hterm

end AlgebraicComplexity.Examples
