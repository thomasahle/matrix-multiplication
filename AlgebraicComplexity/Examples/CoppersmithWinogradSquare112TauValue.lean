/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinograd112SymmetricGrowth
import AlgebraicComplexity.Examples.CoppersmithWinogradSquareTauValueAssembly

/-!
# The modern symmetric `(112)` value inside the CW square

This client specializes the relation-neutral square value assembly to the modern symmetric
`(112)` extraction.  One repetition of the symmetric 64-address typed leaf has mass
`[2(L+G)]³`; choosing that number as the outer exceptional-orbit multiplicity makes the inner
cyclic certificate's power agree exactly with the three exceptional chunks of an outer square
word.

The file contains only finite semantic assembly and exact normalization identities.  Outer and
inner survivor-growth estimates remain separate inputs, and the eventual `q = 6` scalar
optimization is downstream.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor

universe u w

/-- Exceptional-orbit multiplicity required by one repetition of the modern symmetric `(112)`
profile. -/
def cwSquareSymmetric112Multiplicity (L G : ℕ) : ℕ :=
  (2 * (L + G)) ^ 3

/-- The modern symmetric exceptional multiplicity is positive for a positive `L`. -/
theorem cwSquareSymmetric112Multiplicity_pos
    {L G : ℕ} (hL : 0 < L) :
    0 < cwSquareSymmetric112Multiplicity L G := by
  unfold cwSquareSymmetric112Multiplicity
  positivity

noncomputable section

variable (K : Type u) [CommRing K]

/-- The canonical symmetric inner certificate has exactly the power required by an outer profile
whose exceptional multiplicity is `[2(L+G)]³`.

Proof sketch: the typed leaf has power `profile.mass*k`; its proved profile mass is
`[2(L+G)]³`. -/
theorem cw112SymmetricCanonical_power_eq_squareMultiplicity_mul
    (τ : ℝ) (q L G k : ℕ) (hq : 0 < q) (hL : 0 < L) (hG : 0 < G)
    (hk : 0 < k)
    (seed : CW112SymmetricCanonicalSeed K q L G k hq hL hG)
    (hnonempty : Nonempty
      (CW112SymmetricCanonicalSurvivor K q L G k hq hL hG seed)) :
    (cw112SymmetricCanonicalDegenerationValueCertificate
      K τ q L G k hq hL hG hk seed hnonempty).power =
      cwSquareSymmetric112Multiplicity L G * k := by
  let leaf := cw112SymmetricLeaf K q L G hq hL hG
  calc
    (cw112SymmetricCanonicalDegenerationValueCertificate
        K τ q L G k hq hL hG hk seed hnonempty).power =
        leaf.proportionalDepth k + 1 := rfl
    _ = leaf.profile.mass * k := leaf.proportionalDepth_add_one hk
    _ = cwSquareSymmetric112Multiplicity L G * k := by
      rw [cw112SymmetricLeaf_profile_mass]
      rfl

/-- Fully assembled finite value certificate for the CW square using the canonical modern
symmetric `(112)` inner extraction and one independently chosen outer hash seed. -/
noncomputable def cwSquareSymmetric112TauValueCertificate
    {R : Type w} [Field R] [NeZero (2 : R)]
    (H : PartitionHashEncoding (R := R) cwSquareSupport)
    (τ : ℝ) (q a b c L G k : ℕ)
    (hq : 0 < q) (hordinary : 0 < cwSquareStride a b c 0)
    (hL : 0 < L) (hG : 0 < G) (hk : 0 < k)
    (B : Finset R) (hB : ThreeAPFree (B : Set R))
    (outerSeed : ProgressionHash.Seed R
      (Fin (cwSquareDepth a b c (cwSquareSymmetric112Multiplicity L G) k + 1)))
    [Nonempty (CWSquareOuterSurvivor H a b c
      (cwSquareSymmetric112Multiplicity L G) k B outerSeed)]
    (innerSeed : CW112SymmetricCanonicalSeed K q L G k hq hL hG)
    (hinnerNonempty : Nonempty
      (CW112SymmetricCanonicalSurvivor K q L G k hq hL hG innerSeed)) :
    TauValueCertificate K (cwSquarePartitionedTensor K q).realize :=
  cwSquareTauValueCertificateOfCyclicInner
    K H τ q a b c (cwSquareSymmetric112Multiplicity L G) k
    hq hordinary (cwSquareSymmetric112Multiplicity_pos hL) hk
    B hB outerSeed
    (cw112SymmetricCanonicalDegenerationValueCertificate
      K τ q L G k hq hL hG hk innerSeed hinnerNonempty)
    (cw112SymmetricCanonical_power_eq_squareMultiplicity_mul
      K τ q L G k hq hL hG hk innerSeed hinnerNonempty)

/-- The assembled modern symmetric certificate records the exact outer word length. -/
@[simp] theorem cwSquareSymmetric112TauValueCertificate_power
    {R : Type w} [Field R] [NeZero (2 : R)]
    (H : PartitionHashEncoding (R := R) cwSquareSupport)
    (τ : ℝ) (q a b c L G k : ℕ)
    (hq : 0 < q) (hordinary : 0 < cwSquareStride a b c 0)
    (hL : 0 < L) (hG : 0 < G) (hk : 0 < k)
    (B : Finset R) (hB : ThreeAPFree (B : Set R))
    (outerSeed : ProgressionHash.Seed R
      (Fin (cwSquareDepth a b c (cwSquareSymmetric112Multiplicity L G) k + 1)))
    [Nonempty (CWSquareOuterSurvivor H a b c
      (cwSquareSymmetric112Multiplicity L G) k B outerSeed)]
    (innerSeed : CW112SymmetricCanonicalSeed K q L G k hq hL hG)
    (hinnerNonempty : Nonempty
      (CW112SymmetricCanonicalSurvivor K q L G k hq hL hG innerSeed)) :
    (cwSquareSymmetric112TauValueCertificate
      K H τ q a b c L G k hq hordinary hL hG hk B hB outerSeed
        innerSeed hinnerNonempty).power =
      cwSquareDepth a b c (cwSquareSymmetric112Multiplicity L G) k + 1 := by
  unfold cwSquareSymmetric112TauValueCertificate
  exact cwSquareTauValueCertificateOfCyclicInner_power
    K H τ q a b c (cwSquareSymmetric112Multiplicity L G) k
      hq hordinary (cwSquareSymmetric112Multiplicity_pos hL) hk B hB outerSeed _ _

/-- Exact finite term of the fully assembled modern symmetric square certificate.

The quantity below the outer `1 / (stride*k)` root is the product of three independently visible
factors: the number of surviving outer blocks, the ordinary cube-volume contribution, and the
unnormalized volume sum of the cyclic `(112)` certificate.

Proof sketch: unfold the specialization and apply the relation-neutral outer assembly formula.
-/
theorem cwSquareSymmetric112TauValueCertificate_term
    {R : Type w} [Field R] [NeZero (2 : R)]
    (H : PartitionHashEncoding (R := R) cwSquareSupport)
    (τ σ : ℝ) (q a b c L G k : ℕ)
    (hq : 0 < q) (hordinary : 0 < cwSquareStride a b c 0)
    (hL : 0 < L) (hG : 0 < G) (hk : 0 < k)
    (B : Finset R) (hB : ThreeAPFree (B : Set R))
    (outerSeed : ProgressionHash.Seed R
      (Fin (cwSquareDepth a b c (cwSquareSymmetric112Multiplicity L G) k + 1)))
    [Nonempty (CWSquareOuterSurvivor H a b c
      (cwSquareSymmetric112Multiplicity L G) k B outerSeed)]
    (innerSeed : CW112SymmetricCanonicalSeed K q L G k hq hL hG)
    (hinnerNonempty : Nonempty
      (CW112SymmetricCanonicalSurvivor K q L G k hq hL hG innerSeed)) :
    (cwSquareSymmetric112TauValueCertificate
      K H τ q a b c L G k hq hordinary hL hG hk B hB outerSeed
        innerSeed hinnerNonempty).term σ =
      (((Fintype.card (CWSquareOuterSurvivor H a b c
          (cwSquareSymmetric112Multiplicity L G) k B outerSeed) : ℕ) : ℝ) *
        ((((cwSquareOrdinaryDimension q b c k *
            cwSquareOrdinaryDimension q b c k *
            cwSquareOrdinaryDimension q b c k : ℕ) : ℝ) ^ σ) *
          matrixMultiplicationVolumePowerSum
            (cw112SymmetricCanonicalDegenerationValueCertificate
              K τ q L G k hq hL hG hk innerSeed hinnerNonempty).xSize
            (cw112SymmetricCanonicalDegenerationValueCertificate
              K τ q L G k hq hL hG hk innerSeed hinnerNonempty).ySize
            (cw112SymmetricCanonicalDegenerationValueCertificate
              K τ q L G k hq hL hG hk innerSeed hinnerNonempty).zSize σ)) ^
        (((cwSquareDepth a b c (cwSquareSymmetric112Multiplicity L G) k + 1 : ℕ) : ℝ)⁻¹) := by
  unfold cwSquareSymmetric112TauValueCertificate
  exact cwSquareTauValueCertificateOfCyclicInner_term
    K H τ σ q a b c (cwSquareSymmetric112Multiplicity L G) k
      hq hordinary (cwSquareSymmetric112Multiplicity_pos hL) hk B hB outerSeed _ _

end

end AlgebraicComplexity.Examples
