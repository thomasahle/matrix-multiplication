import AlgebraicComplexity.MatrixMultiplication.HashingExtraction
import AlgebraicComplexity.Tensor.CompatibilityZeroing

/-!
# Hashing stages from *More Asymmetry Yields Faster Matrix Multiplication*

The global and recursive constituent invocations use the same finite theorem.  This client module
names both interfaces explicitly while proving them through one reusable `FiniteHashingStage`.
It covers the affine hash, progression-free filtering, finite good-seed averaging, isolated
target extraction, and the ensuing exact `X`-variable zero-out.  Compatibility zeroing and hole
repair remain later stages of the paper pipeline.
-/

namespace MatrixMultiplication.MoreAsymmetry

open AlgebraicComplexity
open AlgebraicComplexity.ProgressionHash

universe u v w x

/-- Complete finite input to one invocation of the more-asymmetric hashing cleanup. -/
structure FiniteHashingStage (R : Type u) [Field R] [Fintype R]
    (ι : Type v) [Fintype ι] (target : R) where
  targets : Finset (LegalTriple R ι target)
  buckets : Finset R
  progressionFree : ThreeAPFree (buckets : Set R)
  degreeBound : ∀ triple ∈ targets,
    8 * (LegalTriple.xFiber targets triple).card ≤ Fintype.card R

namespace FiniteHashingStage

variable {R : Type u} [Field R] [Fintype R]
variable {ι : Type v} [Fintype ι]
variable {target : R}

noncomputable local instance : DecidableEq ι := Classical.decEq _
noncomputable local instance (c : AlgebraicComplexity.Tensor.Leg) :
    Fintype (WordBlockLabels R ι c) := inferInstance
noncomputable local instance (c : AlgebraicComplexity.Tensor.Leg) :
    DecidableEq (WordBlockLabels R ι c) := Classical.decEq _

/-- Paper-facing output proposition for a successful finite hashing invocation. -/
def HasGoodSeed (input : FiniteHashingStage R ι target) : Prop :=
  ∃ seed : Seed R ι,
    3 * input.targets.card * input.buckets.card ≤
        4 * (Fintype.card R * Fintype.card R) *
          (LegalTriple.xIsolatedAddresses input.targets input.buckets seed).card ∧
      LegalTriple.xIsolatedTargets input.targets input.buckets seed ⊆
        LegalTriple.filteredTargets input.targets input.buckets seed ∧
      AlgebraicComplexity.Tensor.HasUniqueLegFibers
        (LegalTriple.filteredAddresses input.targets input.buckets seed)
        (LegalTriple.xIsolatedAddresses input.targets input.buckets seed) .X

/-- One successful seed, with its exact finite count, survival property, and the full ambient
`X`-fiber uniqueness needed for tensor zeroing. -/
theorem exists_good_seed [NeZero (2 : R)] (input : FiniteHashingStage R ι target) :
    input.HasGoodSeed := by
  obtain ⟨seed, hcount, hsubset, _hinjective⟩ :=
    LegalTriple.exists_seed_many_xIsolatedTargets input.targets input.buckets
      (LegalTriple.competitor_quarter_of_eight_mul_xFiber_le input.targets input.degreeBound)
  refine ⟨seed, ?_, hsubset,
    LegalTriple.xIsolatedAddresses_hasUniqueXFibers input.targets input.buckets
      input.progressionFree seed⟩
  rwa [LegalTriple.card_xIsolatedAddresses]

section TensorZeroOut

variable {K : Type w} [CommSemiring K]
variable {V : ∀ c, WordBlockLabels R ι c → Type x}
variable [∀ c a, AddCommMonoid (V c a)] [∀ c a, Module K (V c a)]

/-- Fixed-seed tensor realization of the hashing cleanup. -/
theorem tensor_zeroOut [NeZero (2 : R)] (input : FiniteHashingStage R ι target)
    (seed : Seed R ι)
    (P : AlgebraicComplexity.Tensor.PartitionedTensor
      (K := K) (A := WordBlockLabels R ι) V)
    (hsupport : P.support =
      LegalTriple.filteredAddresses input.targets input.buckets seed) :
    AlgebraicComplexity.Tensor.Restricts P.realize
      (P.withSupport
        (LegalTriple.xIsolatedAddresses input.targets input.buckets seed)).realize :=
  Tensor.Restricts.hashFiltered_to_xIsolated input.targets input.buckets
    input.progressionFree seed P hsupport

/-- Full indexed-direct-sum interface after the later compatibility stages establish independence
on all three legs. -/
theorem tensor_directSum [NeZero (2 : R)] (input : FiniteHashingStage R ι target)
    (seed : Seed R ι)
    (P : AlgebraicComplexity.Tensor.PartitionedTensor
      (K := K) (A := WordBlockLabels R ι) V)
    (hsupport : P.support =
      LegalTriple.filteredAddresses input.targets input.buckets seed)
    (hlegwise : AlgebraicComplexity.Tensor.IsLegwiseInjective
      (LegalTriple.xIsolatedAddresses input.targets input.buckets seed)) :
    AlgebraicComplexity.Tensor.Restricts P.realize
      (AlgebraicComplexity.Tensor.indexedDirectSum
        (V := AlgebraicComplexity.Tensor.SelectedBlockFamily (V := V)
          (LegalTriple.xIsolatedAddresses input.targets input.buckets seed))
        (fun s : LegalTriple.xIsolatedAddresses input.targets input.buckets seed =>
          P.constituent s.1)) :=
  Tensor.Restricts.hashFiltered_to_xIsolatedIndexedDirectSum
    input.targets input.buckets input.progressionFree seed P hsupport hlegwise

/-- Hashing followed by the two paper compatibility cleanups.  The only stage-specific inputs
remaining are soundness of the concrete `Y`- and `Z`-compatibility predicates.  Unique-label
zeroing and final direct-sum assembly are consequences, not assumptions. -/
theorem tensor_compatibility_directSum [NeZero (2 : R)]
    (input : FiniteHashingStage R ι target) (seed : Seed R ι)
    (P : AlgebraicComplexity.Tensor.PartitionedTensor
      (K := K) (A := WordBlockLabels R ι) V)
    (hsupport : P.support =
      LegalTriple.filteredAddresses input.targets input.buckets seed)
    (compatibleY : WordBlockLabels R ι .Y →
      AlgebraicComplexity.Tensor.BlockAddress (WordBlockLabels R ι) → Prop)
    (hsoundY :
      let xSupport := LegalTriple.xIsolatedAddresses input.targets input.buckets seed
      AlgebraicComplexity.Tensor.IsCompatibilitySound xSupport .Y compatibleY)
    (compatibleZ : WordBlockLabels R ι .Z →
      AlgebraicComplexity.Tensor.BlockAddress (WordBlockLabels R ι) → Prop)
    (hsoundZ :
      let xSupport := LegalTriple.xIsolatedAddresses input.targets input.buckets seed
      let ySupport := AlgebraicComplexity.Tensor.compatibilityIsolatedSupport
        xSupport .Y compatibleY
      AlgebraicComplexity.Tensor.IsCompatibilitySound ySupport .Z compatibleZ) :
    let xSupport := LegalTriple.xIsolatedAddresses input.targets input.buckets seed
    let PX := P.withSupport xSupport
    let ySupport := AlgebraicComplexity.Tensor.compatibilityIsolatedSupport
      xSupport .Y compatibleY
    let zSupport := AlgebraicComplexity.Tensor.compatibilityIsolatedSupport
      ySupport .Z compatibleZ
    AlgebraicComplexity.Tensor.Restricts P.realize
      (AlgebraicComplexity.Tensor.indexedDirectSum
        (V := AlgebraicComplexity.Tensor.SelectedBlockFamily (V := V) zSupport)
        (fun address : zSupport ↦ PX.constituent address.1)) := by
  classical
  let xSupport := LegalTriple.xIsolatedAddresses input.targets input.buckets seed
  let PX := P.withSupport xSupport
  let ySupport := AlgebraicComplexity.Tensor.compatibilityIsolatedSupport
    xSupport .Y compatibleY
  let zSupport := AlgebraicComplexity.Tensor.compatibilityIsolatedSupport
    ySupport .Z compatibleZ
  have hxRestrict : AlgebraicComplexity.Tensor.Restricts P.realize PX.realize := by
    simpa [PX, xSupport] using tensor_zeroOut input seed P hsupport
  have hxFibers : AlgebraicComplexity.Tensor.HasUniqueLegFibers
      (LegalTriple.filteredAddresses input.targets input.buckets seed) xSupport .X := by
    simpa [xSupport] using LegalTriple.xIsolatedAddresses_hasUniqueXFibers
      input.targets input.buckets input.progressionFree seed
  have hxInjective : Set.InjOn
      (fun address : AlgebraicComplexity.Tensor.BlockAddress (WordBlockLabels R ι) ↦ address .X)
      xSupport := by
    intro left hleft right hright hlabel
    have hrightAmbient : right ∈
        LegalTriple.filteredAddresses input.targets input.buckets seed := hxFibers.1 hright
    exact (hxFibers.2 left hleft right hrightAmbient hlabel.symm).symm
  have hcleanup :=
    AlgebraicComplexity.Tensor.Restricts.partitionedYZCompatibilityCleanup_to_indexedDirectSum
      PX hxInjective compatibleY hsoundY compatibleZ hsoundZ
  exact hxRestrict.trans hcleanup

end TensorZeroOut

end FiniteHashingStage

/-- Global-stage input.  The alias documents the role without duplicating the theorem. -/
abbrev GlobalHashingStage := FiniteHashingStage

/-- Recursive constituent-stage input.  Its finite proof obligations are identical to the global
stage after replacing the concrete target family and coordinate-position type. -/
abbrev ConstituentHashingStage := FiniteHashingStage

/-- Global invocation of the shared finite extraction theorem. -/
theorem GlobalHashingStage.exists_good_seed
    {R : Type u} [Field R] [Fintype R] {ι : Type v} [Fintype ι] {target : R}
    [NeZero (2 : R)] (input : GlobalHashingStage R ι target) :
    FiniteHashingStage.HasGoodSeed input :=
  FiniteHashingStage.exists_good_seed input

/-- Recursive constituent invocation of the shared finite extraction theorem. -/
theorem ConstituentHashingStage.exists_good_seed
    {R : Type u} [Field R] [Fintype R] {ι : Type v} [Fintype ι] {target : R}
    [NeZero (2 : R)] (input : ConstituentHashingStage R ι target) :
    FiniteHashingStage.HasGoodSeed input :=
  FiniteHashingStage.exists_good_seed input

end MatrixMultiplication.MoreAsymmetry
