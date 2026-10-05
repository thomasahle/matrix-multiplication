/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinograd112SymmetricProfile
import AlgebraicComplexity.Examples.CoppersmithWinograd112LeafInterface
import AlgebraicComplexity.MatrixMultiplication.CyclicTypedLeaf
import AlgebraicComplexity.MatrixMultiplication.RationalTypedLeafReindex

/-!
# The symmetric rational typed leaf of the CW `112` constituent

This file specializes the paper-independent cyclic typed-leaf construction to the primitive
four-address CW `112` leaf.  It packages the 64 source triples as one rational typed leaf and
derives its maximum entropy, visible entropy, and exact square dimension from generic product
theorems.

No hashing or asymptotic limit occurs here.  The output is the finite typed leaf consumed by the
modern three-leg value extraction.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor

universe u

/-- The cyclic product of the primitive rational CW `112` typed leaf. -/
def cw112SymmetricRationalTypedLeaf
    (q L G : ℕ) (hq : 0 < q) (hL : 0 < L) (hG : 0 < G) :=
  (cw112RationalTypedLeaf q L G hq hL hG).cyclicProduct

/-- Its exact integral denominator is `[2(L+G)]³`. -/
@[simp] theorem cw112SymmetricRationalTypedLeaf_mass
    (q L G : ℕ) (hq : 0 < q) (hL : 0 < L) (hG : 0 < G) :
    (cw112SymmetricRationalTypedLeaf q L G hq hL hG).profile.mass =
      (2 * (L + G)) ^ 3 := by
  unfold cw112SymmetricRationalTypedLeaf
  change (cw112IntegralProfile L G hL hG).cyclicProduct.mass = _
  rw [PositiveIntegralProfile.mass_cyclicProduct,
    cw112IntegralProfile_mass]

/-- Canonical equivalence from the generic cyclic coordinate alphabet to the transparent CW
compound alphabet.  The equivalence is mathematically the identity in every leg; spelling it out
avoids relying on definitional equality between dependent `Fintype` instances. -/
def cw112CyclicCoordinateEquiv :
    ∀ c, CyclicTypedLeafCoordinate CW112Block c ≃ CW112SymmetricVisibleBlock c
  | .X => Equiv.refl _
  | .Y => Equiv.refl _
  | .Z => Equiv.refl _

/-- After the canonical alphabet relabelling, the generic cyclic typed-leaf coordinate is the
transparent compound CW coordinate. -/
theorem cw112SymmetricRationalTypedLeaf_equivCoordinate
    (q L G : ℕ) (hq : 0 < q) (hL : 0 < L) (hG : 0 < G) :
    WordType.equivCoordinate
        (cw112SymmetricRationalTypedLeaf q L G hq hL hG).coordinate
        cw112CyclicCoordinateEquiv =
      cw112SymmetricVisibleSourceCoordinate := by
  funext c source
  cases c <;> rfl

/-- The cyclic leaf distribution is exactly the independent three-source law used by the
64-address profile. -/
theorem cw112SymmetricRationalTypedLeaf_distribution
    (q L G : ℕ) (hq : 0 < q) (hL : 0 < L) (hG : 0 < G) :
    (cw112SymmetricRationalTypedLeaf q L G hq hL hG).distribution =
      cw112SymmetricSourceProbability L G (Nat.add_pos_left hL G) := by
  unfold cw112SymmetricRationalTypedLeaf
  rw [RationalTypedLeaf.cyclicProduct_distribution]
  have hdistribution :
      (cw112RationalTypedLeaf q L G hq hL hG).distribution =
        (cw112RationalTypedLeaf 1 L G (by omega) hL hG).distribution := by
    rfl
  rw [hdistribution, ← cw112ProfileProbability_eq_typedLeafDistribution hL hG]
  rfl

/-- The symmetric CW typed leaf maximizes entropy in its three compound marginal fiber.

Proof sketch: the primitive four-address law is marginally rigid and hence maximum entropy.  The
generic cyclic-product theorem tensorizes that property to the independent 64-address law. -/
theorem cw112SymmetricRationalTypedLeaf_isMaximumEntropyBits
    (q L G : ℕ) (hq : 0 < q) (hL : 0 < L) (hG : 0 < G) :
    (cw112SymmetricRationalTypedLeaf q L G hq hL hG).IsMaximumEntropyBits
      (cw112SymmetricRationalTypedLeaf q L G hq hL hG).distribution :=
  (cw112RationalTypedLeaf_isMaximumEntropyBits q L G hq hL hG).cyclicProduct

/-- Every compound marginal of the symmetric typed leaf has exactly
`2 + H₂(mu,mu,1-2mu)` bits of entropy. -/
theorem cw112SymmetricRationalTypedLeaf_marginalEntropyBits
    (q L G : ℕ) (hq : 0 < q) (hL : 0 < L) (hG : 0 < G) (c : Leg) :
    (cw112SymmetricRationalTypedLeaf q L G hq hL hG).marginalEntropyBits c =
      2 + cw112MuEntropyBits L G := by
  unfold RationalTypedLeaf.marginalEntropyBits RationalTypedLeaf.marginal
  rw [cw112SymmetricRationalTypedLeaf_distribution]
  calc
    ((cw112SymmetricSourceProbability L G (Nat.add_pos_left hL G)).pushforward
        ((cw112SymmetricRationalTypedLeaf q L G hq hL hG).coordinate c)).entropyBits =
        ((cw112SymmetricSourceProbability L G (Nat.add_pos_left hL G)).pushforward
          (cw112CyclicCoordinateEquiv c ∘
            (cw112SymmetricRationalTypedLeaf q L G hq hL hG).coordinate c)).entropyBits :=
      (ProbabilityVector.entropyBits_pushforward_equiv
        ((cw112SymmetricRationalTypedLeaf q L G hq hL hG).coordinate c)
        (cw112CyclicCoordinateEquiv c)
        (cw112SymmetricSourceProbability L G (Nat.add_pos_left hL G))).symm
    _ = ((cw112SymmetricSourceProbability L G (Nat.add_pos_left hL G)).pushforward
          (cw112SymmetricVisibleSourceCoordinate c)).entropyBits := by
      rw [← cw112SymmetricRationalTypedLeaf_equivCoordinate q L G hq hL hG]
      rfl
    _ = 2 + cw112MuEntropyBits L G :=
      cw112SymmetricVisibleSourceProbability_marginalEntropyBits hL hG c

/-- Each of the three exact matrix dimensions of the symmetric typed leaf is the same square
side `cw112FiniteLeafSquareSide^(2(L+G))²`.

Proof sketch: the generic cyclic dimension theorem multiplies the primitive dimensions
`q^(2G), q^(2L), q^(2G)` and raises the result to the square of the primitive profile mass. -/
theorem cw112SymmetricRationalTypedLeaf_dimensionProduct
    (q L G : ℕ) (hq : 0 < q) (hL : 0 < L) (hG : 0 < G) (c : Leg) :
    (cw112SymmetricRationalTypedLeaf q L G hq hL hG).dimensionProduct c =
      cw112FiniteLeafSquareSide q L G ^ ((2 * (L + G)) ^ 2) := by
  unfold cw112SymmetricRationalTypedLeaf
  rw [RationalTypedLeaf.cyclicProduct_dimensionProduct]
  have hbase (c : Leg) :
      (cw112RationalTypedLeaf q L G hq hL hG).dimensionProduct c *
          (cw112RationalTypedLeaf q L G hq hL hG).dimensionProduct (cycle.symm c) *
          (cw112RationalTypedLeaf q L G hq hL hG).dimensionProduct (cycle c) =
        cw112FiniteLeafSquareSide q L G := by
    cases c <;>
      simp only [cycle_symm_X, cycle_X, cycle_symm_Y, cycle_Y,
        cycle_symm_Z, cycle_Z,
        cw112RationalTypedLeaf_dimensionProduct_X,
        cw112RationalTypedLeaf_dimensionProduct_Y,
        cw112RationalTypedLeaf_dimensionProduct_Z] <;>
      unfold cw112FiniteLeafSquareSide <;>
      rw [← pow_add, ← pow_add] <;>
      congr 1 <;>
      omega
  rw [hbase]
  change cw112FiniteLeafSquareSide q L G ^
      ((cw112IntegralProfile L G hL hG).mass ^ 2) = _
  rw [cw112IntegralProfile_mass]

/-! ## The same leaf on the actual partition-support subtype -/

/-- Reindex the Cartesian 64-address leaf onto the support subtype of the symmetric partitioned
tensor.  This is the tensor-facing leaf consumed by generic hashing. -/
noncomputable def cw112SymmetricSupportedRationalTypedLeaf
    (q L G : ℕ) (hq : 0 < q) (hL : 0 < L) (hG : 0 < G) :
    RationalTypedLeaf CW112SymmetricSupport (CyclicTypedLeafCoordinate CW112Block) :=
  (cw112SymmetricRationalTypedLeaf q L G hq hL hG).reindex
    cw112SymmetricSupportEquiv

/-- Source reindexing preserves the maximum-entropy certificate. -/
theorem cw112SymmetricSupportedRationalTypedLeaf_isMaximumEntropyBits
    (q L G : ℕ) (hq : 0 < q) (hL : 0 < L) (hG : 0 < G) :
    (cw112SymmetricSupportedRationalTypedLeaf q L G hq hL hG).IsMaximumEntropyBits
      (cw112SymmetricSupportedRationalTypedLeaf q L G hq hL hG).distribution :=
  (cw112SymmetricRationalTypedLeaf_isMaximumEntropyBits q L G hq hL hG).reindex
    cw112SymmetricSupportEquiv

/-- Every visible marginal of the support-indexed leaf retains the exact entropy
`2 + H₂(mu,mu,1-2mu)`. -/
theorem cw112SymmetricSupportedRationalTypedLeaf_marginalEntropyBits
    (q L G : ℕ) (hq : 0 < q) (hL : 0 < L) (hG : 0 < G) (c : Leg) :
    (cw112SymmetricSupportedRationalTypedLeaf q L G hq hL hG).marginalEntropyBits c =
      2 + cw112MuEntropyBits L G := by
  rw [cw112SymmetricSupportedRationalTypedLeaf,
    RationalTypedLeaf.marginalEntropyBits_reindex,
    cw112SymmetricRationalTypedLeaf_marginalEntropyBits]

/-- Every matrix dimension product of the support-indexed leaf is the same exact square side. -/
theorem cw112SymmetricSupportedRationalTypedLeaf_dimensionProduct
    (q L G : ℕ) (hq : 0 < q) (hL : 0 < L) (hG : 0 < G) (c : Leg) :
    (cw112SymmetricSupportedRationalTypedLeaf q L G hq hL hG).dimensionProduct c =
      cw112FiniteLeafSquareSide q L G ^ ((2 * (L + G)) ^ 2) := by
  rw [cw112SymmetricSupportedRationalTypedLeaf,
    RationalTypedLeaf.dimensionProduct_reindex,
    cw112SymmetricRationalTypedLeaf_dimensionProduct]

/-- Reindex the same Cartesian leaf directly onto the support subtype of the actual symmetric
partitioned tensor.  This is the exact input type expected by generic partition hashing. -/
noncomputable def cw112SymmetricPartitionRationalTypedLeaf
    (K : Type u) [CommRing K]
    (q L G : ℕ) (hq : 0 < q) (hL : 0 < L) (hG : 0 < G) :
    RationalTypedLeaf (cw112SymmetricPartitionedTensor K q).support
      (CyclicTypedLeafCoordinate CW112Block) :=
  (cw112SymmetricRationalTypedLeaf q L G hq hL hG).reindex
    (cw112SymmetricPartitionSupportEquiv K q)

/-- The actual-partition leaf inherits the symmetric maximum-entropy certificate. -/
theorem cw112SymmetricPartitionRationalTypedLeaf_isMaximumEntropyBits
    (K : Type u) [CommRing K]
    (q L G : ℕ) (hq : 0 < q) (hL : 0 < L) (hG : 0 < G) :
    (cw112SymmetricPartitionRationalTypedLeaf K q L G hq hL hG).IsMaximumEntropyBits
      (cw112SymmetricPartitionRationalTypedLeaf K q L G hq hL hG).distribution :=
  (cw112SymmetricRationalTypedLeaf_isMaximumEntropyBits q L G hq hL hG).reindex
    (cw112SymmetricPartitionSupportEquiv K q)

/-- All three dimension products of the actual-partition leaf are the same exact square side. -/
theorem cw112SymmetricPartitionRationalTypedLeaf_dimensionProduct
    (K : Type u) [CommRing K]
    (q L G : ℕ) (hq : 0 < q) (hL : 0 < L) (hG : 0 < G) (c : Leg) :
    (cw112SymmetricPartitionRationalTypedLeaf K q L G hq hL hG).dimensionProduct c =
      cw112FiniteLeafSquareSide q L G ^ ((2 * (L + G)) ^ 2) := by
  rw [cw112SymmetricPartitionRationalTypedLeaf,
    RationalTypedLeaf.dimensionProduct_reindex,
    cw112SymmetricRationalTypedLeaf_dimensionProduct]

end AlgebraicComplexity.Examples
