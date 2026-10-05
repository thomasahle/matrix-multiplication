/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinograd112SymmetricMarginalHashing
import AlgebraicComplexity.Examples.CoppersmithWinograd112SymmetricConstituent
import AlgebraicComplexity.MatrixMultiplication.CyclicProductCoherence
import AlgebraicComplexity.MatrixMultiplication.RationalTypedLeafRelation
import AlgebraicComplexity.Combinatorics.ProgressionFree

/-!
# Finite ordinary three-leg extraction for the symmetric CW `112` product

This is the first tensor-facing client of the modern symmetric formulation.  The three cyclic
orientations are treated as one partitioned tensor with 64 supported addresses.  We retain the
complete three-marginal ambient family of a rational typed leaf, apply ordinary affine hashing,
and isolate the marked proportional joint type.  Every surviving constituent is then identified
with the same rectangular matrix-multiplication tensor by the reusable relation-parametric typed-
leaf theorem.

The theorem here is finite: it exposes the exact support, field, seed, and progression-free-set
hypotheses.  It does not hide an asymptotic value premise or claim the final CW exponent bound.
The subsequent value layer will apply the proportional type-counting estimates to this direct
sum. -/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor

universe u

variable (K : Type u) [CommRing K]

/-! ## The complete three-marginal zero-out -/

/-- The leg-local predicate which retains precisely the three prescribed marginal types of the
 symmetric rational typed leaf.  Keeping this as a named predicate, rather than baking the
 filter into the ambient definition, lets the generic support and restriction lemmas see the
 actual zero-out map. -/
noncomputable def cw112SymmetricKeepMarginal
    (q L G k : ℕ) (hq : 0 < q) (hL : 0 < L) (hG : 0 < G)
    (c : Leg)
    (word : PositiveWord (CW112SymmetricBlock c)
      ((cw112SymmetricPartitionRationalTypedLeaf K q L G hq hL hG).proportionalDepth k)) : Prop :=
  (cw112SymmetricPartitionRationalTypedLeaf K q L G hq hL hG).KeepsMarginal k c word

noncomputable instance cw112SymmetricKeepMarginal_decidable
    (q L G k : ℕ) (hq : 0 < q) (hL : 0 < L) (hG : 0 < G)
    (c : Leg)
    (word : PositiveWord (CW112SymmetricBlock c)
      ((cw112SymmetricPartitionRationalTypedLeaf K q L G hq hL hG).proportionalDepth k)) :
    Decidable (cw112SymmetricKeepMarginal K q L G k hq hL hG c word) := by
  unfold cw112SymmetricKeepMarginal
  infer_instance

/-- The ambient partition obtained by retaining the modeled addresses of the symmetric CW leaf's
complete three-marginal word family.  Its constituents are inherited from the positive power; the
support is replaced only after the support identity has been proved by the generic hashing API. -/
noncomputable def cw112SymmetricAmbientPartitionedPower
    (q L G k p : ℕ) (hq : 0 < q) (hL : 0 < L) (hG : 0 < G)
    [Fact p.Prime] (hp : 27 ≤ p) :
    PartitionedTensor (K := K)
      (A := fun c ↦ PositiveWord (CW112SymmetricBlock c)
        ((cw112SymmetricPartitionRationalTypedLeaf K q L G hq hL hG).proportionalDepth k))
      (PositivePowerBlockSpace K (CW112SymmetricBlockSpace K q)
        ((cw112SymmetricPartitionRationalTypedLeaf K q L G hq hL hG).proportionalDepth k)) := by
  let leaf := cw112SymmetricPartitionRationalTypedLeaf K q L G hq hL hG
  let H := cw112SymmetricPartitionHashEncoding K q p hp
  let r := leaf.proportionalDepth k
  exact ((cw112SymmetricPartitionedTensor K q).positivePower r).select
    (cw112SymmetricKeepMarginal K q L G k hq hL hG)

/-- The selected ambient partition has exactly the modeled legal-target support required by
ordinary three-leg hashing. -/
theorem cw112SymmetricAmbientPartitionedPower_support
    (q L G k p : ℕ) (hq : 0 < q) (hL : 0 < L) (hG : 0 < G)
    [Fact p.Prime] (hp : 27 ≤ p) :
    (cw112SymmetricAmbientPartitionedPower K q L G k p hq hL hG hp).support =
      (cw112SymmetricPartitionHashEncoding K q p hp).modeledAddresses
        ((cw112SymmetricPartitionRationalTypedLeaf K q L G hq hL hG).proportionalDepth k)
        ((cw112SymmetricPartitionHashEncoding K q p hp).legalTargets
          ((cw112SymmetricPartitionRationalTypedLeaf K q L G hq hL hG).proportionalDepth k)
          ((cw112SymmetricPartitionRationalTypedLeaf K q L G hq hL hG).ambientWords k)) := by
  classical
  unfold cw112SymmetricAmbientPartitionedPower
  change
    (((cw112SymmetricPartitionedTensor K q).positivePower
      ((cw112SymmetricPartitionRationalTypedLeaf K q L G hq hL hG).proportionalDepth k)).support.filter
        (fun s ↦ ∀ c, cw112SymmetricKeepMarginal K q L G k hq hL hG c (s c))) = _
  rw [(cw112SymmetricPartitionHashEncoding K q p hp).positivePower_support_eq_modeledLegalTargets
    (cw112SymmetricPartitionedTensor K q)
    ((cw112SymmetricPartitionRationalTypedLeaf K q L G hq hL hG).proportionalDepth k)]
  apply (cw112SymmetricPartitionHashEncoding K q p hp).filter_modeledLegalTargets_eq_of_mem_iff
    ((cw112SymmetricPartitionRationalTypedLeaf K q L G hq hL hG).proportionalDepth k)
    ((cw112SymmetricPartitionRationalTypedLeaf K q L G hq hL hG).ambientWords k)
    (cw112SymmetricKeepMarginal K q L G k hq hL hG)
  intro word
  exact (cw112SymmetricPartitionRationalTypedLeaf K q L G hq hL hG).mem_ambientWords_iff k word

/-- The full realized symmetric power restricts to the complete three-marginal ambient power.

This is the semantic bridge that turns the finite extraction theorem below into a theorem about
the actual source tensor.  It is just positive-power expansion followed by the generic legwise
selection zero-out; no hashing or asymptotic assumption is involved. -/
theorem cw112SymmetricPower_restricts_ambientPartitionedPower
    (q L G k p : ℕ) (hq : 0 < q) (hL : 0 < L) (hG : 0 < G)
    [Fact p.Prime] (hp : 27 ≤ p) :
    Restricts
      (Tensor.power (cw112SymmetricPartitionedTensor K q).realize
        ((cw112SymmetricPartitionRationalTypedLeaf K q L G hq hL hG).proportionalDepth k + 1))
      (cw112SymmetricAmbientPartitionedPower K q L G k p hq hL hG hp).realize := by
  exact (Tensor.Restricts.power_partitionedPositivePower
      (cw112SymmetricPartitionedTensor K q)
      ((cw112SymmetricPartitionRationalTypedLeaf K q L G hq hL hG).proportionalDepth k)).trans
    (Tensor.Restricts.partitionedSelect
      ((cw112SymmetricPartitionedTensor K q).positivePower
        ((cw112SymmetricPartitionRationalTypedLeaf K q L G hq hL hG).proportionalDepth k))
      (cw112SymmetricKeepMarginal K q L G k hq hL hG))

/-- Constituents of the selected ambient partition are the corresponding constituents of the
unfiltered positive power. -/
theorem cw112SymmetricAmbientPartitionedPower_constituent
    (q L G k p : ℕ) (hq : 0 < q) (hL : 0 < L) (hG : 0 < G)
    [Fact p.Prime] (hp : 27 ≤ p)
    (address : BlockAddress
      (fun c ↦ PositiveWord (CW112SymmetricBlock c)
        ((cw112SymmetricPartitionRationalTypedLeaf K q L G hq hL hG).proportionalDepth k))) :
    (cw112SymmetricAmbientPartitionedPower K q L G k p hq hL hG hp).constituent address =
      ((cw112SymmetricPartitionedTensor K q).positivePower
        ((cw112SymmetricPartitionRationalTypedLeaf K q L G hq hL hG).proportionalDepth k)).constituent
        address := by
  rfl

/-- Every marked word in the symmetric CW ambient family has the proportional joint type recorded
by the rational leaf. -/
theorem cw112SymmetricAmbient_markedType
    (q L G k : ℕ) (hq : 0 < q) (hL : 0 < L) (hG : 0 < G)
    {word : PositiveWord (cw112SymmetricPartitionedTensor K q).support
      ((cw112SymmetricPartitionRationalTypedLeaf K q L G hq hL hG).proportionalDepth k)}
    (hword : word ∈
      (cw112SymmetricPartitionRationalTypedLeaf K q L G hq hL hG).markedWords k) :
    WordType.multiplicity
        (positiveWordEquiv (cw112SymmetricPartitionedTensor K q).support
          ((cw112SymmetricPartitionRationalTypedLeaf K q L G hq hL hG).proportionalDepth k) word) =
      WordType.proportionalCounts
        (cw112SymmetricPartitionRationalTypedLeaf K q L G hq hL hG).profile.count k := by
  exact mem_positiveTypeClass.mp hword

/-- Finite symmetric CW extraction: after retaining the complete three-marginal ambient family and
hashing it, the selected tensor degenerates to a direct sum of identical rectangular matrix
multiplication tensors.  The number of summands is left as the exact finite survivor cardinality.

Proof sketch: instantiate the generic relation-parametric extraction theorem with the actual
symmetric support coordinate, the already-proved 64-address field encoding, and the constituent
restriction theorem.  The selected support is the exact three-marginal zero-out established
above; the marked-family inclusion is the symmetric marginal bridge. -/
theorem cw112SymmetricFiniteExtraction
    (q L G k p : ℕ) (hq : 0 < q) (hL : 0 < L) (hG : 0 < G)
    (hk : 0 < k) [Fact p.Prime] (hp : 27 ≤ p)
    (B : Finset (ZMod p)) (hB : ThreeAPFree (B : Set (ZMod p)))
    (seed : ProgressionHash.Seed (ZMod p)
      (Fin ((cw112SymmetricPartitionRationalTypedLeaf K q L G hq hL hG).proportionalDepth k + 1))) :
    PolynomialDegenerates
      (cw112SymmetricAmbientPartitionedPower K q L G k p hq hL hG hp).realize
      (Tensor.indexedDirectSum
        (fun _selected :
          (cw112SymmetricPartitionHashEncoding K q p hp).markedLegwiseIsolatedPowerAddresses
            ((cw112SymmetricPartitionRationalTypedLeaf K q L G hq hL hG).proportionalDepth k)
            ((cw112SymmetricPartitionRationalTypedLeaf K q L G hq hL hG).ambientWords k)
            ((cw112SymmetricPartitionRationalTypedLeaf K q L G hq hL hG).markedWords k)
            B seed ↦
          matrixMultiplication (K := K)
            ((cw112SymmetricPartitionRationalTypedLeaf K q L G hq hL hG).dimensionProduct .X ^ k)
            ((cw112SymmetricPartitionRationalTypedLeaf K q L G hq hL hG).dimensionProduct .Y ^ k)
            ((cw112SymmetricPartitionRationalTypedLeaf K q L G hq hL hG).dimensionProduct .Z ^ k))) := by
  letI : NeZero (2 : ZMod p) := neZero_two_zmod_of_three_le (by omega)
  let leaf := cw112SymmetricPartitionRationalTypedLeaf K q L G hq hL hG
  let H := cw112SymmetricPartitionHashEncoding K q p hp
  let r := leaf.proportionalDepth k
  let ambient := leaf.ambientWords k
  let marked := leaf.markedWords k
  let Q := cw112SymmetricAmbientPartitionedPower K q L G k p hq hL hG hp
  have hmarked : marked ⊆ ambient := by
    exact cw112SymmetricMarkedWords_subset_ambientWords K q L G k hq hL hG
  have htype : ∀ word ∈ marked,
    WordType.multiplicity
        (positiveWordEquiv (cw112SymmetricPartitionedTensor K q).support r word) =
        WordType.proportionalCounts leaf.profile.count k := by
    intro word hword
    exact mem_positiveTypeClass.mp hword
  have hconstituent : ∀ s : (cw112SymmetricPartitionedTensor K q).support,
      Restricts ((cw112SymmetricPartitionedTensor K q).constituent s.1)
        (matrixMultiplication (K := K)
          (leaf.dimension s .X) (leaf.dimension s .Y) (leaf.dimension s .Z)) := by
    intro s
    exact cw112SymmetricSupportedConstituent_restricts K q L G hq hL hG s
  let certificate :=
    RationalTypedLeaf.TypedLeafExtractionCertificate.of_restriction leaf hconstituent
  simpa [Q, H, r, ambient, marked] using
    RationalTypedLeaf.localizedAmbient_degenerates_markedLeafDirectSum_of_certificate
      (P := cw112SymmetricPartitionedTensor K q) leaf _ certificate H r k ambient marked hmarked
      htype Q
      (cw112SymmetricAmbientPartitionedPower_support K q L G k p hq hL hG hp)
      (by intro; rfl) B hB seed

/-- The finite symmetric extraction stated directly over the full realized source power. -/
theorem cw112SymmetricPowerFiniteExtraction
    (q L G k p : ℕ) (hq : 0 < q) (hL : 0 < L) (hG : 0 < G)
    (hk : 0 < k) [Fact p.Prime] (hp : 27 ≤ p)
    (B : Finset (ZMod p)) (hB : ThreeAPFree (B : Set (ZMod p)))
    (seed : ProgressionHash.Seed (ZMod p)
      (Fin ((cw112SymmetricPartitionRationalTypedLeaf K q L G hq hL hG).proportionalDepth k + 1))) :
    PolynomialDegenerates
      (Tensor.power (cw112SymmetricPartitionedTensor K q).realize
        ((cw112SymmetricPartitionRationalTypedLeaf K q L G hq hL hG).proportionalDepth k + 1))
      (Tensor.indexedDirectSum
        (fun _selected :
          (cw112SymmetricPartitionHashEncoding K q p hp).markedLegwiseIsolatedPowerAddresses
            ((cw112SymmetricPartitionRationalTypedLeaf K q L G hq hL hG).proportionalDepth k)
            ((cw112SymmetricPartitionRationalTypedLeaf K q L G hq hL hG).ambientWords k)
            ((cw112SymmetricPartitionRationalTypedLeaf K q L G hq hL hG).markedWords k)
            B seed ↦
          matrixMultiplication (K := K)
            ((cw112SymmetricPartitionRationalTypedLeaf K q L G hq hL hG).dimensionProduct .X ^ k)
            ((cw112SymmetricPartitionRationalTypedLeaf K q L G hq hL hG).dimensionProduct .Y ^ k)
            ((cw112SymmetricPartitionRationalTypedLeaf K q L G hq hL hG).dimensionProduct .Z ^ k))) := by
  exact (PolynomialDegenerates.of_restricts
      (cw112SymmetricPower_restricts_ambientPartitionedPower K q L G k p hq hL hG hp)).trans
    (cw112SymmetricFiniteExtraction K q L G k p hq hL hG hk hp B hB seed)

/-- The same finite extraction stated over the conventional cyclic value source.

In human terms, a positive power of the primitive `112` tensor together with the corresponding
powers of its two cyclic orientations degenerates to the direct sum selected by symmetric
three-leg hashing.  Thus the symmetric 64-address construction is not a new tensor assumption:
it is a structured representation of the source used by the modern value definition.

Proof sketch: `cyclicPowerProduct_partitioned_positive` identifies the cyclic product of the
primitive realized partition with the matching power of the realized symmetric partition.  An
isomorphism is an exact restriction and hence a degree-zero polynomial degeneration; compose it
with `cw112SymmetricPowerFiniteExtraction`. -/
theorem cw112CyclicPowerProductFiniteExtraction
    (q L G k p : ℕ) (hq : 0 < q) (hL : 0 < L) (hG : 0 < G)
    (hk : 0 < k) [Fact p.Prime] (hp : 27 ≤ p)
    (B : Finset (ZMod p)) (hB : ThreeAPFree (B : Set (ZMod p)))
    (seed : ProgressionHash.Seed (ZMod p)
      (Fin ((cw112SymmetricPartitionRationalTypedLeaf K q L G hq hL hG).proportionalDepth k + 1))) :
    PolynomialDegenerates
      (cyclicPowerProduct K (cw112PartitionedTensor K q).realize
        ((cw112SymmetricPartitionRationalTypedLeaf K q L G hq hL hG).proportionalDepth k + 1))
      (Tensor.indexedDirectSum
        (fun _selected :
          (cw112SymmetricPartitionHashEncoding K q p hp).markedLegwiseIsolatedPowerAddresses
            ((cw112SymmetricPartitionRationalTypedLeaf K q L G hq hL hG).proportionalDepth k)
            ((cw112SymmetricPartitionRationalTypedLeaf K q L G hq hL hG).ambientWords k)
            ((cw112SymmetricPartitionRationalTypedLeaf K q L G hq hL hG).markedWords k)
            B seed ↦
          matrixMultiplication (K := K)
            ((cw112SymmetricPartitionRationalTypedLeaf K q L G hq hL hG).dimensionProduct .X ^ k)
            ((cw112SymmetricPartitionRationalTypedLeaf K q L G hq hL hG).dimensionProduct .Y ^ k)
            ((cw112SymmetricPartitionRationalTypedLeaf K q L G hq hL hG).dimensionProduct .Z ^ k))) := by
  have hsource := Tensor.Isomorphic.cyclicPowerProduct_partitioned_positive
    (cw112PartitionedTensor K q)
    ((cw112SymmetricPartitionRationalTypedLeaf K q L G hq hL hG).proportionalDepth k)
  have hsource' : Restricts
      (cyclicPowerProduct K (cw112PartitionedTensor K q).realize
        ((cw112SymmetricPartitionRationalTypedLeaf K q L G hq hL hG).proportionalDepth k + 1))
      (Tensor.power (cw112SymmetricPartitionedTensor K q).realize
        ((cw112SymmetricPartitionRationalTypedLeaf K q L G hq hL hG).proportionalDepth k + 1)) := by
    simpa only [cw112SymmetricPartitionedTensor] using hsource.restricts
  exact (PolynomialDegenerates.of_restricts hsource').trans
    (cw112SymmetricPowerFiniteExtraction K q L G k p hq hL hG hk hp B hB seed)

end AlgebraicComplexity.Examples
