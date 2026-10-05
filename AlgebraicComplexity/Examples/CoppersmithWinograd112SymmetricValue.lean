/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinograd112SymmetricFiniteExtraction
import AlgebraicComplexity.MatrixMultiplication.CyclicValueTensor

/-!
# Finite cyclic-value certificates for the symmetric CW `112` leaf

This file is the semantic meeting point of the modern symmetric typed-leaf proof and the
relation-parametric value API.  A nonempty finite set of hash survivors gives a checked
polynomial-degeneration certificate for the conventional three-orientation source.  Its copy
count is the exact survivor cardinality and all three target dimensions are the exact products
computed by the rational typed leaf.

No asymptotic survivor estimate or numerical optimization is assumed here.  Those are separate
proof obligations: a later theorem must choose fields, progression-free sets, and seeds whose
survivor cardinalities have the required exponential growth, then evaluate the resulting finite
terms.  The present theorem ensures that such counting results enter the value through an actual
tensor degeneration rather than an unproved value axiom.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor

universe u

variable (K : Type u) [CommRing K]

/-- The structured finite survivor type selected by symmetric three-leg hashing. -/
noncomputable abbrev CW112SymmetricSurvivor
    (q L G k p : ℕ) (hq : 0 < q) (hL : 0 < L) (hG : 0 < G)
    [Fact p.Prime] (hp : 27 ≤ p)
    (B : Finset (ZMod p))
    (seed : ProgressionHash.Seed (ZMod p)
      (Fin ((cw112SymmetricPartitionRationalTypedLeaf K q L G hq hL hG).proportionalDepth k + 1))) :=
  (cw112SymmetricPartitionHashEncoding K q p hp).markedLegwiseIsolatedPowerAddresses
    ((cw112SymmetricPartitionRationalTypedLeaf K q L G hq hL hG).proportionalDepth k)
    ((cw112SymmetricPartitionRationalTypedLeaf K q L G hq hL hG).ambientWords k)
    ((cw112SymmetricPartitionRationalTypedLeaf K q L G hq hL hG).markedWords k)
    B seed

/-- Every nonempty finite symmetric survivor family produces a checked degeneration-value
certificate for the primitive CW `112` tensor.

The certificate has source power `profile.mass * k`, exact copy count equal to the survivor
cardinality, and constant square target side equal to the `k`th power of the symmetric typed
leaf's dimension product.

Proof sketch: use `cw112CyclicPowerProductFiniteExtraction` for the tensor degeneration, then
apply the generic constant-indexed-direct-sum adapter.  Positivity of the three dimensions comes
from the typed-leaf contract and positivity of finite products. -/
noncomputable def cw112SymmetricDegenerationValueCertificate
    (τ : ℝ)
    (q L G k p : ℕ) (hq : 0 < q) (hL : 0 < L) (hG : 0 < G)
    (hk : 0 < k) [Fact p.Prime] (hp : 27 ≤ p)
    (B : Finset (ZMod p)) (hB : ThreeAPFree (B : Set (ZMod p)))
    (seed : ProgressionHash.Seed (ZMod p)
      (Fin ((cw112SymmetricPartitionRationalTypedLeaf K q L G hq hL hG).proportionalDepth k + 1)))
    [Nonempty (CW112SymmetricSurvivor K q L G k p hq hL hG hp B seed)] :
    CyclicDegenerationCertificate K (cw112PartitionedTensor K q).realize τ := by
  let leaf := cw112SymmetricPartitionRationalTypedLeaf K q L G hq hL hG
  exact CyclicDegenerationCertificate.of_constantIndexedDirectSum (K := K)
    τ (cw112PartitionedTensor K q).realize (leaf.proportionalDepth k + 1)
    (leaf.dimensionProduct .X ^ k)
    (leaf.dimensionProduct .Y ^ k)
    (leaf.dimensionProduct .Z ^ k)
    (Nat.succ_pos _)
    (pow_pos (leaf.dimensionProduct_pos .X) k)
    (pow_pos (leaf.dimensionProduct_pos .Y) k)
    (pow_pos (leaf.dimensionProduct_pos .Z) k)
    (by
      simpa only [leaf, CW112SymmetricSurvivor] using
        cw112CyclicPowerProductFiniteExtraction K q L G k p hq hL hG hk hp B hB seed)

/-- The finite symmetric CW certificate contributes its exact numerical term to the intrinsic
polynomial-degeneration value set. -/
theorem cw112SymmetricDegenerationValueCertificate_mem
    (τ : ℝ)
    (q L G k p : ℕ) (hq : 0 < q) (hL : 0 < L) (hG : 0 < G)
    (hk : 0 < k) [Fact p.Prime] (hp : 27 ≤ p)
    (B : Finset (ZMod p)) (hB : ThreeAPFree (B : Set (ZMod p)))
    (seed : ProgressionHash.Seed (ZMod p)
      (Fin ((cw112SymmetricPartitionRationalTypedLeaf K q L G hq hL hG).proportionalDepth k + 1)))
    [Nonempty (CW112SymmetricSurvivor K q L G k p hq hL hG hp B seed)] :
    (cw112SymmetricDegenerationValueCertificate K τ q L G k p hq hL hG hk hp B hB seed).term
      ∈ degenerationValueValues K (cw112PartitionedTensor K q).realize τ :=
  CyclicDegenerationCertificate.mem_degenerationValueValues (K := K)
    (cw112SymmetricDegenerationValueCertificate K τ q L G k p hq hL hG hk hp B hB seed)

end AlgebraicComplexity.Examples
