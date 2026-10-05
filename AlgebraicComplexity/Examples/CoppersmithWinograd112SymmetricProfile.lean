/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Analysis.MaximumEntropyProduct
import AlgebraicComplexity.Examples.CoppersmithWinograd112TypedLeaf
import AlgebraicComplexity.Probability.IntegralProfile
import AlgebraicComplexity.Tensor.PartitionedProduct
import AlgebraicComplexity.Tensor.PartitionedPermutation

/-!
# The symmetric product profile of the exceptional CW `112` constituent

The historical value bound for `T₁₁₂` must symmetrize before it isolates tensor blocks.  This
file constructs that three-orientation partition exactly.  Its support consists of 64 addresses,
one for each ordered triple of the four `112` source addresses.  For an integral source profile
`a`, the symmetric profile assigns the product multiplicity `aᵢ aⱼ aₖ` to the triple `(i,j,k)`.

The three labels visible on a fixed tensor leg come from three different source legs.  Thus the
corresponding marginal profile is the product of one X, one Y, and one Z marginal.  For the CW
profile `(L,L,G,G)`, its entropy is consequently `2 + H₂(μ,μ,1-2μ)`.  This positive Z-entropy is
the feature lost by the older flattened shared-Z route.

This module is finite and combinatorial.  It introduces no asymptotic value axiom and performs no
numerical optimization.  Later files use the profile as the marked family for ordinary symmetric
three-leg hashing, following the proof of the `T₁₁₂` value lemma in Coppersmith--Winograd (1990),
pp. 270--272.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor
open scoped BigOperators

universe u

/-- Block labels in the product of `T₁₁₂` with its two cyclic orientations. -/
abbrev CW112SymmetricBlock : Leg → Type :=
  ProductBlockIndex
    (ProductBlockIndex CW112Block (PermutedBlockIndex cycle CW112Block))
    (PermutedBlockIndex cycle.symm CW112Block)

/-- Block spaces in the product of `T₁₁₂` with its two cyclic orientations. -/
abbrev CW112SymmetricBlockSpace (K : Type u) [CommRing K] (q : ℕ) :=
  ProductBlockSpace K
    (ProductBlockSpace K (CW112PartitionBlockSpace K q)
      (PermutedBlockSpace cycle (CW112PartitionBlockSpace K q)))
    (PermutedBlockSpace cycle.symm (CW112PartitionBlockSpace K q))

/-- The structured three-orientation product of the exceptional partitioned tensor. -/
noncomputable def cw112SymmetricPartitionedTensor
    (K : Type u) [CommRing K] (q : ℕ) :
    PartitionedTensor (K := K) (A := CW112SymmetricBlock)
      (CW112SymmetricBlockSpace K q) :=
  ((cw112PartitionedTensor K q).external
      ((cw112PartitionedTensor K q).permute cycle)).external
    ((cw112PartitionedTensor K q).permute cycle.symm)

/-- Recover the address in the unpermuted first factor of a symmetric block address. -/
def cw112SymmetricFirstAddress
    (s : BlockAddress CW112SymmetricBlock) : BlockAddress CW112Block :=
  fun c ↦ (s c).1.1

/-- Recover the address in the unpermuted source of the second, cyclic factor. -/
def cw112SymmetricSecondAddress
    (s : BlockAddress CW112SymmetricBlock) : BlockAddress CW112Block :=
  (permuteBlockAddress cycle).symm (fun c ↦ (s c).1.2)

/-- Recover the address in the unpermuted source of the third, inverse-cyclic factor. -/
def cw112SymmetricThirdAddress
    (s : BlockAddress CW112SymmetricBlock) : BlockAddress CW112Block :=
  (permuteBlockAddress cycle.symm).symm (fun c ↦ (s c).2)

/-- Purely combinatorial support of the symmetric `112` product. -/
def cw112SymmetricSupport : Finset (BlockAddress CW112SymmetricBlock) :=
  Finset.univ.filter fun s ↦
    (cw112SymmetricFirstAddress s ∈ cw112BlockSupport ∧
      cw112SymmetricSecondAddress s ∈ cw112BlockSupport) ∧
        cw112SymmetricThirdAddress s ∈ cw112BlockSupport

/-- The tensor construction has exactly the advertised three-source support.

Proof sketch: membership in an external-product support is componentwise membership; membership
in a permuted support is membership of the inverse-transported source address.  These are exactly
the three conjuncts defining `cw112SymmetricSupport`. -/
theorem cw112SymmetricPartitionedTensor_support
    (K : Type u) [CommRing K] (q : ℕ) :
    (cw112SymmetricPartitionedTensor K q).support = cw112SymmetricSupport := by
  ext s
  simp only [cw112SymmetricPartitionedTensor,
    PartitionedTensor.mem_external_support, PartitionedTensor.mem_permute_support]
  rw [cw112SymmetricSupport, Finset.mem_filter]
  simp only [Finset.mem_univ, true_and]
  rfl

/-- Finite alphabet of supported addresses in the symmetric product. -/
abbrev CW112SymmetricSupport := {s // s ∈ cw112SymmetricSupport}

/-- Ordered triples of the four source addresses. -/
abbrev CW112SourceTriple :=
  (cw112BlockSupport × cw112BlockSupport) × cw112BlockSupport

/-- Assemble three source addresses into the corresponding symmetric-product address. -/
def cw112SymmetricAddress (source : CW112SourceTriple) :
    BlockAddress CW112SymmetricBlock :=
  blockAddressProductEquiv
    (blockAddressProductEquiv
      (source.1.1.1, permuteBlockAddress cycle source.1.2.1),
      permuteBlockAddress cycle.symm source.2.1)

/-- Reading the first source back from an assembled symmetric address is exact. -/
@[simp] theorem cw112SymmetricFirstAddress_address (source : CW112SourceTriple) :
    cw112SymmetricFirstAddress (cw112SymmetricAddress source) = source.1.1.1 := by
  rfl

/-- Reading the second source back from an assembled symmetric address is exact. -/
@[simp] theorem cw112SymmetricSecondAddress_address (source : CW112SourceTriple) :
    cw112SymmetricSecondAddress (cw112SymmetricAddress source) = source.1.2.1 := by
  unfold cw112SymmetricSecondAddress cw112SymmetricAddress
  exact (permuteBlockAddress cycle).symm_apply_apply source.1.2.1

/-- Reading the third source back from an assembled symmetric address is exact. -/
@[simp] theorem cw112SymmetricThirdAddress_address (source : CW112SourceTriple) :
    cw112SymmetricThirdAddress (cw112SymmetricAddress source) = source.2.1 := by
  unfold cw112SymmetricThirdAddress cw112SymmetricAddress
  exact (permuteBlockAddress cycle.symm).symm_apply_apply source.2.1

/-- Every assembled source triple lies in the symmetric-product support. -/
theorem cw112SymmetricAddress_mem (source : CW112SourceTriple) :
    cw112SymmetricAddress source ∈ cw112SymmetricSupport := by
  simp [cw112SymmetricSupport, source.1.1.2, source.1.2.2, source.2.2]

/-- Read the three original supported addresses from one symmetric-product address. -/
def cw112SymmetricSources (s : CW112SymmetricSupport) : CW112SourceTriple :=
  ((⟨cw112SymmetricFirstAddress s.1, (Finset.mem_filter.mp s.2).2.1.1⟩,
      ⟨cw112SymmetricSecondAddress s.1, (Finset.mem_filter.mp s.2).2.1.2⟩),
    ⟨cw112SymmetricThirdAddress s.1, (Finset.mem_filter.mp s.2).2.2⟩)

/-- The 64 supported symmetric addresses are canonically equivalent to ordered source triples. -/
def cw112SymmetricSupportEquiv : CW112SourceTriple ≃ CW112SymmetricSupport where
  toFun source := ⟨cw112SymmetricAddress source, cw112SymmetricAddress_mem source⟩
  invFun := cw112SymmetricSources
  left_inv source := by
    rcases source with ⟨⟨first, second⟩, third⟩
    apply Prod.ext
    · apply Prod.ext <;> apply Subtype.ext <;>
        simp [cw112SymmetricSources]
    · apply Subtype.ext
      simp [cw112SymmetricSources]
  right_inv s := by
    apply Subtype.ext
    funext c
    have hsecond :
        permuteBlockAddress cycle (cw112SymmetricSecondAddress s.1) =
          (fun c ↦ (s.1 c).1.2) := by
      exact (permuteBlockAddress cycle).apply_symm_apply _
    have hthird :
        permuteBlockAddress cycle.symm (cw112SymmetricThirdAddress s.1) =
          (fun c ↦ (s.1 c).2) := by
      exact (permuteBlockAddress cycle.symm).apply_symm_apply _
    change ((cw112SymmetricFirstAddress s.1 c,
      permuteBlockAddress cycle (cw112SymmetricSecondAddress s.1) c),
        permuteBlockAddress cycle.symm (cw112SymmetricThirdAddress s.1) c) = s.1 c
    rw [congrFun hsecond c, congrFun hthird c]
    rfl

/-- The symmetric support is inhabited (indeed it has 64 elements). -/
instance : Nonempty CW112SymmetricSupport :=
  cw112SymmetricSupportEquiv.nonempty_congr.mp inferInstance

/-- Identify the combinatorial symmetric support with the support subtype of the actual
partitioned tensor. -/
def cw112SymmetricSupportToPartitionSupportEquiv
    (K : Type u) [CommRing K] (q : ℕ) :
    CW112SymmetricSupport ≃ (cw112SymmetricPartitionedTensor K q).support :=
  Equiv.subtypeEquivRight fun address ↦ by
    rw [cw112SymmetricPartitionedTensor_support]

/-- Ordered source triples are canonically equivalent to the actual symmetric partition support. -/
def cw112SymmetricPartitionSupportEquiv
    (K : Type u) [CommRing K] (q : ℕ) :
    CW112SourceTriple ≃ (cw112SymmetricPartitionedTensor K q).support :=
  cw112SymmetricSupportEquiv.trans
    (cw112SymmetricSupportToPartitionSupportEquiv K q)

/-- The actual-support equivalence has the expected assembled underlying address. -/
@[simp] theorem cw112SymmetricPartitionSupportEquiv_val
    (K : Type u) [CommRing K] (q : ℕ) (source : CW112SourceTriple) :
    (cw112SymmetricPartitionSupportEquiv K q source).1 =
      cw112SymmetricAddress source :=
  rfl

/-- The actual symmetric partition support is inhabited. -/
instance (K : Type u) [CommRing K] (q : ℕ) :
    Nonempty (cw112SymmetricPartitionedTensor K q).support :=
  (cw112SymmetricPartitionSupportEquiv K q).nonempty_congr.mp inferInstance

/-- Decoding an address assembled from a source triple recovers that triple. -/
@[simp] theorem cw112SymmetricSources_supportEquiv (source : CW112SourceTriple) :
    cw112SymmetricSources (cw112SymmetricSupportEquiv source) = source :=
  cw112SymmetricSupportEquiv.left_inv source

/-- The symmetric support contains exactly `4³ = 64` addresses. -/
@[simp] theorem card_cw112SymmetricSupport : cw112SymmetricSupport.card = 64 := by
  rw [← Fintype.card_coe]
  calc
    Fintype.card CW112SymmetricSupport = Fintype.card CW112SourceTriple :=
      Fintype.card_congr cw112SymmetricSupportEquiv.symm
    _ = 64 := by simp

/-- Sum over the symmetric support as an iterated sum over its three source addresses. -/
theorem sum_cw112SymmetricSupport (f : CW112SymmetricSupport → ℕ) :
    ∑ s, f s =
      ∑ first : cw112BlockSupport, ∑ second : cw112BlockSupport,
        ∑ third : cw112BlockSupport,
          f (cw112SymmetricSupportEquiv ((first, second), third)) := by
  rw [← Fintype.sum_equiv cw112SymmetricSupportEquiv
    (fun source ↦ f (cw112SymmetricSupportEquiv source)) f]
  · rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
  · intro source
    rfl

/-- A triple sum of independent natural-valued factors is the product of the three sums. -/
private theorem sum_triple_product {I : Type*} [Fintype I]
    (f g h : I → ℕ) :
    (∑ i, ∑ j, ∑ k, f i * g j * h k) =
      (∑ i, f i) * (∑ j, g j) * (∑ k, h k) := by
  classical
  calc
    _ = ∑ i, ∑ j, (f i * g j) * (∑ k, h k) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.mul_sum]
    _ = ∑ i, f i * (∑ j, g j) * (∑ k, h k) := by
      apply Finset.sum_congr rfl
      intro i _
      calc
        (∑ j, (f i * g j) * (∑ k, h k)) =
            (∑ j, f i * g j) * (∑ k, h k) := by
          exact (Finset.sum_mul Finset.univ (fun j ↦ f i * g j)
            (∑ k, h k)).symm
        _ = f i * (∑ j, g j) * (∑ k, h k) := by
          congr 1
          exact (Finset.mul_sum Finset.univ g (f i)).symm
    _ = _ := by
      calc
        (∑ i, (f i * (∑ j, g j)) * (∑ k, h k)) =
            (∑ i, f i * (∑ j, g j)) * (∑ k, h k) := by
          exact (Finset.sum_mul Finset.univ
            (fun i ↦ f i * (∑ j, g j)) (∑ k, h k)).symm
        _ = (∑ i, f i) * (∑ j, g j) * (∑ k, h k) := by
          congr 1
          exact (Finset.sum_mul Finset.univ f (∑ j, g j)).symm

/-- Product integral profile on the 64 symmetric source triples. -/
def cw112SymmetricNaturalType (L G : ℕ) : CW112SymmetricSupport → ℕ :=
  fun s ↦
    cw112NaturalType L G (cw112SymmetricSources s).1.1 *
      cw112NaturalType L G (cw112SymmetricSources s).1.2 *
      cw112NaturalType L G (cw112SymmetricSources s).2

/-- The product profile has total mass `[2(L+G)]³`.

Proof sketch: transport the support sum to the Cartesian source-triple alphabet.  The summand is
a product of three independent copies of `cw112NaturalType`, so the triple sum factors as the
cube of the one-source mass. -/
theorem cw112SymmetricNaturalType_profileMass (L G : ℕ) :
    WordType.profileMass (cw112SymmetricNaturalType L G) =
      (2 * (L + G)) ^ 3 := by
  unfold WordType.profileMass
  rw [sum_cw112SymmetricSupport]
  simp only [cw112SymmetricNaturalType, cw112SymmetricSources_supportEquiv]
  rw [sum_triple_product]
  rw [sum_cw112BlockSupportSubtype]
  simp [cw112NaturalType, cw112DiagonalFirstAddress,
    cw112DiagonalSecondAddress, cw112CrossFirstAddress,
    cw112CrossSecondAddress, cw112BlockAddress]
  ring

/-- Explicit marginal profile on one compound leg of the symmetric product. -/
def cw112SymmetricMarginalType (L G : ℕ) (c : Leg) :
    CW112SymmetricBlock c → ℕ :=
  fun block ↦
    cw112MarginalType L G c block.1.1 *
      cw112MarginalType L G (cycle.symm c) block.1.2 *
      cw112MarginalType L G (cycle c) block.2

/-- Projecting the product joint profile to a compound tensor leg gives the product of the three
source marginals.

Proof sketch: transport the support sum to ordered source triples, expand the four-element source
alphabet in each coordinate, and inspect the finitely many compound block labels.  The remaining
identity is distributivity of three independent finite sums. -/
theorem cw112Symmetric_mappedType_eq_marginal (L G : ℕ) (c : Leg) :
    WordType.mappedType (fun s : CW112SymmetricSupport ↦ s.1 c)
      (cw112SymmetricNaturalType L G) = cw112SymmetricMarginalType L G c := by
  funext block
  unfold WordType.mappedType WordType.letterFiber
  simp only [Finset.sum_filter]
  change (∑ s : CW112SymmetricSupport,
      if s.1 c = block then cw112SymmetricNaturalType L G s else 0) = _
  rw [sum_cw112SymmetricSupport]
  simp only [cw112SymmetricNaturalType, cw112SymmetricSources_supportEquiv]
  let firstWeight : cw112BlockSupport → ℕ := fun source ↦
    if source.1 c = block.1.1 then cw112NaturalType L G source else 0
  let secondWeight : cw112BlockSupport → ℕ := fun source ↦
    if source.1 (cycle.symm c) = block.1.2 then cw112NaturalType L G source else 0
  let thirdWeight : cw112BlockSupport → ℕ := fun source ↦
    if source.1 (cycle c) = block.2 then cw112NaturalType L G source else 0
  have hterm (first second third : cw112BlockSupport) :
      (if (cw112SymmetricSupportEquiv ((first, second), third)).1 c = block then
          cw112NaturalType L G first * cw112NaturalType L G second *
            cw112NaturalType L G third
        else 0) = firstWeight first * secondWeight second * thirdWeight third := by
    rcases block with ⟨⟨blockFirst, blockSecond⟩, blockThird⟩
    dsimp [firstWeight, secondWeight, thirdWeight, cw112SymmetricSupportEquiv]
    change (if ((first.1 c, second.1 (cycle.symm c)), third.1 (cycle c)) =
        ((blockFirst, blockSecond), blockThird) then
        cw112NaturalType L G first * cw112NaturalType L G second *
          cw112NaturalType L G third else 0) = _
    by_cases hfirst : first.1 c = blockFirst <;>
      by_cases hsecond : second.1 (cycle.symm c) = blockSecond <;>
      by_cases hthird : third.1 (cycle c) = blockThird <;>
      simp_all
  simp_rw [hterm]
  rw [sum_triple_product]
  have hfirst := congrFun (cw112_mappedType_eq_marginal L G c) block.1.1
  have hsecond := congrFun
    (cw112_mappedType_eq_marginal L G (cycle.symm c)) block.1.2
  have hthird := congrFun
    (cw112_mappedType_eq_marginal L G (cycle c)) block.2
  unfold WordType.mappedType WordType.letterFiber at hfirst hsecond hthird
  simp only [Finset.sum_filter] at hfirst hsecond hthird
  change (∑ source : cw112BlockSupport,
      if source.1 c = block.1.1 then cw112NaturalType L G source else 0) =
        cw112MarginalType L G c block.1.1 at hfirst
  change (∑ source : cw112BlockSupport,
      if source.1 (cycle.symm c) = block.1.2 then cw112NaturalType L G source else 0) =
        cw112MarginalType L G (cycle.symm c) block.1.2 at hsecond
  change (∑ source : cw112BlockSupport,
      if source.1 (cycle c) = block.2 then cw112NaturalType L G source else 0) =
        cw112MarginalType L G (cycle c) block.2 at hthird
  change (∑ source, firstWeight source) * (∑ source, secondWeight source) *
      (∑ source, thirdWeight source) = _
  rw [show (∑ source, firstWeight source) =
      cw112MarginalType L G c block.1.1 by exact hfirst,
    show (∑ source, secondWeight source) =
      cw112MarginalType L G (cycle.symm c) block.1.2 by exact hsecond,
    show (∑ source, thirdWeight source) =
      cw112MarginalType L G (cycle c) block.2 by exact hthird]
  rfl

/-! ## Maximum entropy of the product profile -/

/-- The four-letter primitive profile has total mass `2(L+G)`. -/
@[simp] theorem cw112NaturalType_profileMass (L G : ℕ) :
    WordType.profileMass (cw112NaturalType L G) = 2 * (L + G) := by
  unfold WordType.profileMass
  rw [sum_cw112BlockSupportSubtype]
  simp [cw112NaturalType, cw112DiagonalFirstAddress,
    cw112DiagonalSecondAddress, cw112CrossFirstAddress,
    cw112CrossSecondAddress, cw112BlockAddress]
  omega

/-- The three visible block coordinates on one supported `112` address. -/
abbrev cw112SupportCoordinate : ∀ c, cw112BlockSupport → CW112Block c :=
  fun c s ↦ s.1 c

/-- Normalized probability law of the primitive integral profile. -/
noncomputable def cw112ProfileProbability
    (L G : ℕ) (hLG : 0 < L + G) : ProbabilityVector cw112BlockSupport :=
  WordType.normalizedProfileProbability (cw112NaturalType L G) (by
    rw [cw112NaturalType_profileMass]
    positivity)

/-- The primitive four-address law maximizes entropy in its three-coordinate marginal fiber.

Proof sketch: the three labelled marginals determine every law on the four-address support, as
proved by `cw112_coordinateMarginals_injective`.  Hence every competitor in the same mapped fiber
is the reference law itself. -/
theorem cw112ProfileProbability_isMaximumEntropy
    {L G : ℕ} (hLG : 0 < L + G) :
    WordType.IsMaximumEntropyInMappedFiber cw112SupportCoordinate
      (cw112ProfileProbability L G hLG) := by
  intro competitor hcompetitor
  have heq : competitor = cw112ProfileProbability L G hLG := by
    apply cw112_coordinateMarginals_injective
    intro c
    exact hcompetitor c
  rw [heq]

/-- Coordinate system on ordered source triples that exactly matches the three oriented factors
of `CW112SymmetricBlock`. -/
def cw112SymmetricSourceCoordinate :
    ∀ c, CW112SourceTriple → CW112SymmetricBlock c
  | .X => fun source ↦
      ((source.1.1.1 .X, source.1.2.1 .Z), source.2.1 .Y)
  | .Y => fun source ↦
      ((source.1.1.1 .Y, source.1.2.1 .X), source.2.1 .Z)
  | .Z => fun source ↦
      ((source.1.1.1 .Z, source.1.2.1 .Y), source.2.1 .X)

/-- A definitionally transparent presentation of the three visible compound alphabets.

The abstract partitioned tensor uses transported block families, whose synthesized `Fintype`
instances need not be definitionally identical to the obvious product instances.  This family
records the mathematically canonical product alphabets and crosses back through explicit
equivalences below. -/
abbrev CW112SymmetricVisibleBlock : Leg → Type
  | .X => (CW112Block .X × CW112Block .Z) × CW112Block .Y
  | .Y => (CW112Block .Y × CW112Block .X) × CW112Block .Z
  | .Z => (CW112Block .Z × CW112Block .Y) × CW112Block .X

instance (c : Leg) : Fintype (CW112SymmetricVisibleBlock c) := by
  cases c with
  | X => change Fintype ((CW112Block .X × CW112Block .Z) × CW112Block .Y); infer_instance
  | Y => change Fintype ((CW112Block .Y × CW112Block .X) × CW112Block .Z); infer_instance
  | Z => change Fintype ((CW112Block .Z × CW112Block .Y) × CW112Block .X); infer_instance

instance (c : Leg) : DecidableEq (CW112SymmetricVisibleBlock c) := by
  cases c with
  | X => change DecidableEq ((CW112Block .X × CW112Block .Z) × CW112Block .Y); infer_instance
  | Y => change DecidableEq ((CW112Block .Y × CW112Block .X) × CW112Block .Z); infer_instance
  | Z => change DecidableEq ((CW112Block .Z × CW112Block .Y) × CW112Block .X); infer_instance

/-- The transparent visible alphabet is equivalent to the transported partition block alphabet
on each tensor leg. -/
def cw112SymmetricVisibleEquiv :
    ∀ c, CW112SymmetricVisibleBlock c ≃ CW112SymmetricBlock c
  | .X => Equiv.refl _
  | .Y => Equiv.refl _
  | .Z => Equiv.refl _

/-- Compound visible coordinates valued in the transparent product alphabets. -/
def cw112SymmetricVisibleSourceCoordinate :
    ∀ c, CW112SourceTriple → CW112SymmetricVisibleBlock c
  | .X => fun source ↦
      ((source.1.1.1 .X, source.1.2.1 .Z), source.2.1 .Y)
  | .Y => fun source ↦
      ((source.1.1.1 .Y, source.1.2.1 .X), source.2.1 .Z)
  | .Z => fun source ↦
      ((source.1.1.1 .Z, source.1.2.1 .Y), source.2.1 .X)

/-- The tensor's transported block coordinate is obtained by equivalently relabelling the
transparent compound coordinate. -/
theorem cw112SymmetricSourceCoordinate_eq_equivCoordinate :
    cw112SymmetricSourceCoordinate =
      WordType.equivCoordinate cw112SymmetricVisibleSourceCoordinate
        cw112SymmetricVisibleEquiv := by
  funext c source
  cases c <;> rfl

/-- Independent product of the three primitive source laws. -/
noncomputable def cw112SymmetricSourceProbability
    (L G : ℕ) (hLG : 0 < L + G) : ProbabilityVector CW112SourceTriple :=
  ((cw112ProfileProbability L G hLG).product
      (cw112ProfileProbability L G hLG)).product
    (cw112ProfileProbability L G hLG)

/-- The independent three-source law maximizes entropy for the transparent oriented compound
coordinates.

Proof sketch: reorder the three visible features for the cyclic factors, then apply the generic
maximum-entropy product theorem twice.  Entropy subadditivity, rather than a 64-address case split,
is the only inequality used. -/
theorem cw112SymmetricSourceProbability_isMaximumEntropy_visible
    {L G : ℕ} (hLG : 0 < L + G) :
    WordType.IsMaximumEntropyInMappedFiber cw112SymmetricVisibleSourceCoordinate
      (cw112SymmetricSourceProbability L G hLG) := by
  let p := cw112ProfileProbability L G hLG
  have hbase : WordType.IsMaximumEntropyInMappedFiber cw112SupportCoordinate p :=
    cw112ProfileProbability_isMaximumEntropy hLG
  have hcycle : WordType.IsMaximumEntropyInMappedFiber
      (fun c ↦ cw112SupportCoordinate (cycle.symm c)) p := by
    intro competitor hcompetitor
    apply hbase competitor
    intro c
    have hc := hcompetitor (cycle c)
    change competitor.pushforward
        (cw112SupportCoordinate (cycle.symm (cycle c))) =
      p.pushforward (cw112SupportCoordinate (cycle.symm (cycle c))) at hc
    rw [Equiv.symm_apply_apply] at hc
    exact hc
  have hcycleInv : WordType.IsMaximumEntropyInMappedFiber
      (fun c ↦ cw112SupportCoordinate (cycle c)) p := by
    intro competitor hcompetitor
    apply hbase competitor
    intro c
    have hc := hcompetitor (cycle.symm c)
    change competitor.pushforward
        (cw112SupportCoordinate (cycle (cycle.symm c))) =
      p.pushforward (cw112SupportCoordinate (cycle (cycle.symm c))) at hc
    rw [Equiv.apply_symm_apply] at hc
    exact hc
  have hfirst := WordType.IsMaximumEntropyInMappedFiber.product
    cw112SupportCoordinate (fun c ↦ cw112SupportCoordinate (cycle.symm c))
    p p hbase hcycle
  have hall := WordType.IsMaximumEntropyInMappedFiber.product
    (WordType.productCoordinate cw112SupportCoordinate
      (fun c ↦ cw112SupportCoordinate (cycle.symm c)))
    (fun c ↦ cw112SupportCoordinate (cycle c))
    (p.product p) p hfirst hcycleInv
  intro competitor hcompetitor
  change competitor.entropy ≤ ((p.product p).product p).entropy
  apply hall competitor
  intro c
  cases c with
  | X => exact hcompetitor .X
  | Y => exact hcompetitor .Y
  | Z => exact hcompetitor .Z

/-- The independent three-source law maximizes entropy for the actual transported block labels.

Proof sketch: the transparent product labels maximize entropy by tensorization.  Postcomposing
each coordinate by the canonical equivalence does not change its mapped fiber. -/
theorem cw112SymmetricSourceProbability_isMaximumEntropy
    {L G : ℕ} (hLG : 0 < L + G) :
    WordType.IsMaximumEntropyInMappedFiber cw112SymmetricSourceCoordinate
      (cw112SymmetricSourceProbability L G hLG) := by
  have h := WordType.IsMaximumEntropyInMappedFiber.equivCoordinate
    cw112SymmetricVisibleSourceCoordinate cw112SymmetricVisibleEquiv
    (cw112SymmetricSourceProbability L G hLG)
    (cw112SymmetricSourceProbability_isMaximumEntropy_visible hLG)
  rw [← cw112SymmetricSourceCoordinate_eq_equivCoordinate] at h
  exact h

/-- Transporting the source-triple coordinate system through the 64-address equivalence gives
the actual block label on every compound tensor leg. -/
theorem cw112SymmetricSourceCoordinate_reindex :
    WordType.reindexCoordinate cw112SymmetricSourceCoordinate
      cw112SymmetricSupportEquiv =
        (fun c (s : CW112SymmetricSupport) ↦ s.1 c) := by
  funext c s
  have hs := congrArg Subtype.val
    (cw112SymmetricSupportEquiv.apply_symm_apply s)
  cases c with
  | X =>
      change (cw112SymmetricSupportEquiv
        (cw112SymmetricSupportEquiv.symm s)).1 .X = s.1 .X
      exact congrFun hs .X
  | Y =>
      change (cw112SymmetricSupportEquiv
        (cw112SymmetricSupportEquiv.symm s)).1 .Y = s.1 .Y
      exact congrFun hs .Y
  | Z =>
      change (cw112SymmetricSupportEquiv
        (cw112SymmetricSupportEquiv.symm s)).1 .Z = s.1 .Z
      exact congrFun hs .Z

/-- Normalized probability law represented by the 64-address product profile. -/
noncomputable def cw112SymmetricProfileProbability
    (L G : ℕ) (hLG : 0 < L + G) : ProbabilityVector CW112SymmetricSupport :=
  WordType.normalizedProfileProbability (cw112SymmetricNaturalType L G) (by
    rw [cw112SymmetricNaturalType_profileMass]
    positivity)

/-- The normalized integral product profile is exactly the independent three-source law,
transported to the supported symmetric addresses.

Proof sketch: both weights at an address are the product of its three primitive counts divided by
`[2(L+G)]³`.  The two exact profile-mass theorems identify the denominators. -/
theorem cw112SymmetricProfileProbability_eq_reindex
    {L G : ℕ} (hLG : 0 < L + G) :
    cw112SymmetricProfileProbability L G hLG =
      (cw112SymmetricSourceProbability L G hLG).reindex
        cw112SymmetricSupportEquiv := by
  apply ProbabilityVector.ext
  funext s
  rw [ProbabilityVector.reindex_weight]
  unfold cw112SymmetricProfileProbability cw112SymmetricSourceProbability
  simp only [WordType.normalizedProfileProbability_weight]
  rw [cw112SymmetricNaturalType_profileMass]
  change (cw112SymmetricNaturalType L G s : ℝ) /
      (((2 * (L + G)) ^ 3 : ℕ) : ℝ) =
    (cw112ProfileProbability L G hLG).weight
        (cw112SymmetricSupportEquiv.symm s).1.1 *
      (cw112ProfileProbability L G hLG).weight
        (cw112SymmetricSupportEquiv.symm s).1.2 *
      (cw112ProfileProbability L G hLG).weight
        (cw112SymmetricSupportEquiv.symm s).2
  rw [show cw112SymmetricSupportEquiv.symm s = cw112SymmetricSources s by rfl]
  unfold cw112SymmetricNaturalType cw112ProfileProbability
  simp only [WordType.normalizedProfileProbability_weight]
  rw [cw112NaturalType_profileMass]
  have hmassNat : 0 < 2 * (L + G) := by positivity
  have hmass : ((2 * (L + G) : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast hmassNat.ne'
  push_cast
  field_simp [hmass]

/-- The 64-address product profile is a maximum-entropy representative of its three compound
marginals.

Proof sketch: the ordered-source product law is maximum entropy by tensorization.  Reindex it
through the exact support equivalence, identify the transported coordinates with the actual block
labels, and identify the transported law with the normalized integral profile. -/
theorem cw112SymmetricProfileProbability_isMaximumEntropy
    {L G : ℕ} (hLG : 0 < L + G) :
    WordType.IsMaximumEntropyInMappedFiber
      (fun c (s : CW112SymmetricSupport) ↦ s.1 c)
      (cw112SymmetricProfileProbability L G hLG) := by
  have hsource := cw112SymmetricSourceProbability_isMaximumEntropy hLG
  have hreindexed := hsource.reindex cw112SymmetricSourceCoordinate
    cw112SymmetricSupportEquiv (cw112SymmetricSourceProbability L G hLG)
  rw [cw112SymmetricSourceCoordinate_reindex] at hreindexed
  rw [cw112SymmetricProfileProbability_eq_reindex hLG]
  exact hreindexed

/-! ## The visible `2 + H(Z)` entropy -/

/-- The elementary normalized-profile law agrees with the rational typed-leaf distribution.

This bridge lets the symmetric-value layer reuse the already checked one-leg entropy formulas
without depending on any matrix-dimension calculation. -/
theorem cw112ProfileProbability_eq_typedLeafDistribution
    {L G : ℕ} (hL : 0 < L) (hG : 0 < G) :
    cw112ProfileProbability L G (Nat.add_pos_left hL G) =
      (cw112RationalTypedLeaf 1 L G (by omega) hL hG).distribution := by
  apply ProbabilityVector.ext
  funext source
  unfold cw112ProfileProbability RationalTypedLeaf.distribution
  change (WordType.normalizedProfileProbability (cw112NaturalType L G) _).weight source =
    (cw112IntegralProfile L G hL hG).probability.weight source
  rw [WordType.normalizedProfileProbability_weight]
  rw [PositiveIntegralProfile.probability_weight]
  rw [cw112NaturalType_profileMass, cw112IntegralProfile_mass]
  rfl

/-- Entropy of each primitive coordinate marginal: the two side coordinates have one bit and the
Z coordinate has the ternary `mu` entropy. -/
theorem cw112ProfileProbability_marginalEntropyBits
    {L G : ℕ} (hL : 0 < L) (hG : 0 < G) (c : Leg) :
    ((cw112ProfileProbability L G (Nat.add_pos_left hL G)).pushforward
      (cw112SupportCoordinate c)).entropyBits =
      match c with
      | .X => 1
      | .Y => 1
      | .Z => cw112MuEntropyBits L G := by
  have hlaw := cw112ProfileProbability_eq_typedLeafDistribution hL hG
  cases c with
  | X =>
      have h := cw112RationalTypedLeaf_side_entropyBits
        1 L G (by omega) hL hG .X (Or.inl rfl)
      unfold RationalTypedLeaf.marginalEntropyBits RationalTypedLeaf.marginal at h
      rw [hlaw]
      exact h
  | Y =>
      have h := cw112RationalTypedLeaf_side_entropyBits
        1 L G (by omega) hL hG .Y (Or.inr rfl)
      unfold RationalTypedLeaf.marginalEntropyBits RationalTypedLeaf.marginal at h
      rw [hlaw]
      exact h
  | Z =>
      have h := cw112RationalTypedLeaf_z_entropyBits 1 L G (by omega) hL hG
      unfold RationalTypedLeaf.marginalEntropyBits RationalTypedLeaf.marginal at h
      rw [hlaw]
      exact h

/-- Independent product law of the three primitive marginals visible on a compound leg. -/
noncomputable def cw112SymmetricVisibleMarginalProbability
    (L G : ℕ) (hLG : 0 < L + G) :
    (c : Leg) → ProbabilityVector (CW112SymmetricVisibleBlock c)
  | .X => (((cw112ProfileProbability L G hLG).pushforward
      (cw112SupportCoordinate .X)).product
        ((cw112ProfileProbability L G hLG).pushforward
          (cw112SupportCoordinate .Z))).product
      ((cw112ProfileProbability L G hLG).pushforward
        (cw112SupportCoordinate .Y))
  | .Y => (((cw112ProfileProbability L G hLG).pushforward
      (cw112SupportCoordinate .Y)).product
        ((cw112ProfileProbability L G hLG).pushforward
          (cw112SupportCoordinate .X))).product
      ((cw112ProfileProbability L G hLG).pushforward
        (cw112SupportCoordinate .Z))
  | .Z => (((cw112ProfileProbability L G hLG).pushforward
      (cw112SupportCoordinate .Z)).product
        ((cw112ProfileProbability L G hLG).pushforward
          (cw112SupportCoordinate .Y))).product
      ((cw112ProfileProbability L G hLG).pushforward
        (cw112SupportCoordinate .X))

/-- A transparent compound source coordinate has the independent product of the three
corresponding primitive marginals. -/
theorem cw112SymmetricVisibleSourceProbability_pushforward
    {L G : ℕ} (hLG : 0 < L + G) (c : Leg) :
    (cw112SymmetricSourceProbability L G hLG).pushforward
        (cw112SymmetricVisibleSourceCoordinate c) =
      cw112SymmetricVisibleMarginalProbability L G hLG c := by
  cases c with
  | X =>
      unfold cw112SymmetricVisibleMarginalProbability
      change ((((cw112ProfileProbability L G hLG).product
          (cw112ProfileProbability L G hLG)).product
            (cw112ProfileProbability L G hLG)).pushforward
          (fun source ↦
            ((source.1.1.1 .X, source.1.2.1 .Z), source.2.1 .Y))) = _
      calc
        _ = (((cw112ProfileProbability L G hLG).product
              (cw112ProfileProbability L G hLG)).pushforward
                (fun source ↦ (source.1.1 .X, source.2.1 .Z))).product
              ((cw112ProfileProbability L G hLG).pushforward
                (cw112SupportCoordinate .Y)) :=
          ProbabilityVector.pushforward_product_prodMap _ _ _ _
        _ = (((cw112ProfileProbability L G hLG).pushforward
              (cw112SupportCoordinate .X)).product
                ((cw112ProfileProbability L G hLG).pushforward
                  (cw112SupportCoordinate .Z))).product
              ((cw112ProfileProbability L G hLG).pushforward
                (cw112SupportCoordinate .Y)) := by
          exact congrArg (fun law ↦ law.product
            ((cw112ProfileProbability L G hLG).pushforward
              (cw112SupportCoordinate .Y)))
            (ProbabilityVector.pushforward_product_prodMap
              (cw112ProfileProbability L G hLG) (cw112ProfileProbability L G hLG)
              (cw112SupportCoordinate .X) (cw112SupportCoordinate .Z))
        _ = _ := rfl
  | Y =>
      unfold cw112SymmetricVisibleMarginalProbability
      change ((((cw112ProfileProbability L G hLG).product
          (cw112ProfileProbability L G hLG)).product
            (cw112ProfileProbability L G hLG)).pushforward
          (fun source ↦
            ((source.1.1.1 .Y, source.1.2.1 .X), source.2.1 .Z))) = _
      calc
        _ = (((cw112ProfileProbability L G hLG).product
              (cw112ProfileProbability L G hLG)).pushforward
                (fun source ↦ (source.1.1 .Y, source.2.1 .X))).product
              ((cw112ProfileProbability L G hLG).pushforward
                (cw112SupportCoordinate .Z)) :=
          ProbabilityVector.pushforward_product_prodMap _ _ _ _
        _ = (((cw112ProfileProbability L G hLG).pushforward
              (cw112SupportCoordinate .Y)).product
                ((cw112ProfileProbability L G hLG).pushforward
                  (cw112SupportCoordinate .X))).product
              ((cw112ProfileProbability L G hLG).pushforward
                (cw112SupportCoordinate .Z)) := by
          exact congrArg (fun law ↦ law.product
            ((cw112ProfileProbability L G hLG).pushforward
              (cw112SupportCoordinate .Z)))
            (ProbabilityVector.pushforward_product_prodMap
              (cw112ProfileProbability L G hLG) (cw112ProfileProbability L G hLG)
              (cw112SupportCoordinate .Y) (cw112SupportCoordinate .X))
        _ = _ := rfl
  | Z =>
      unfold cw112SymmetricVisibleMarginalProbability
      change ((((cw112ProfileProbability L G hLG).product
          (cw112ProfileProbability L G hLG)).product
            (cw112ProfileProbability L G hLG)).pushforward
          (fun source ↦
            ((source.1.1.1 .Z, source.1.2.1 .Y), source.2.1 .X))) = _
      calc
        _ = (((cw112ProfileProbability L G hLG).product
              (cw112ProfileProbability L G hLG)).pushforward
                (fun source ↦ (source.1.1 .Z, source.2.1 .Y))).product
              ((cw112ProfileProbability L G hLG).pushforward
                (cw112SupportCoordinate .X)) :=
          ProbabilityVector.pushforward_product_prodMap _ _ _ _
        _ = (((cw112ProfileProbability L G hLG).pushforward
              (cw112SupportCoordinate .Z)).product
                ((cw112ProfileProbability L G hLG).pushforward
                  (cw112SupportCoordinate .Y))).product
              ((cw112ProfileProbability L G hLG).pushforward
                (cw112SupportCoordinate .X)) := by
          exact congrArg (fun law ↦ law.product
            ((cw112ProfileProbability L G hLG).pushforward
              (cw112SupportCoordinate .X)))
            (ProbabilityVector.pushforward_product_prodMap
              (cw112ProfileProbability L G hLG) (cw112ProfileProbability L G hLG)
              (cw112SupportCoordinate .Z) (cw112SupportCoordinate .Y))
        _ = _ := rfl

/-- Every transparent compound leg of the symmetric source product has entropy
`2 + H₂(mu,mu,1-2mu)` bits.

Proof sketch: its law is the independent product of one X, one Y, and one Z primitive marginal.
Entropy is additive on products; cyclic orientation merely changes their order. -/
theorem cw112SymmetricVisibleSourceProbability_marginalEntropyBits
    {L G : ℕ} (hL : 0 < L) (hG : 0 < G) (c : Leg) :
    ((cw112SymmetricSourceProbability L G (Nat.add_pos_left hL G)).pushforward
      (cw112SymmetricVisibleSourceCoordinate c)).entropyBits =
        2 + cw112MuEntropyBits L G := by
  rw [cw112SymmetricVisibleSourceProbability_pushforward]
  cases c with
  | X =>
      unfold cw112SymmetricVisibleMarginalProbability
      rw [ProbabilityVector.entropyBits_product,
        ProbabilityVector.entropyBits_product,
        cw112ProfileProbability_marginalEntropyBits hL hG,
        cw112ProfileProbability_marginalEntropyBits hL hG,
        cw112ProfileProbability_marginalEntropyBits hL hG]
      ring
  | Y =>
      unfold cw112SymmetricVisibleMarginalProbability
      rw [ProbabilityVector.entropyBits_product,
        ProbabilityVector.entropyBits_product,
        cw112ProfileProbability_marginalEntropyBits hL hG,
        cw112ProfileProbability_marginalEntropyBits hL hG,
        cw112ProfileProbability_marginalEntropyBits hL hG]
      ring
  | Z =>
      unfold cw112SymmetricVisibleMarginalProbability
      rw [ProbabilityVector.entropyBits_product,
        ProbabilityVector.entropyBits_product,
        cw112ProfileProbability_marginalEntropyBits hL hG,
        cw112ProfileProbability_marginalEntropyBits hL hG,
        cw112ProfileProbability_marginalEntropyBits hL hG]
      ring

/-- Every actual transported block leg of the symmetric source product has entropy
`2 + H₂(mu,mu,1-2mu)` bits.

Proof sketch: each transported block alphabet is equivalent to its transparent product
presentation.  Entropy is invariant under this relabelling, so the transparent product calculation
applies verbatim. -/
theorem cw112SymmetricSourceProbability_marginalEntropyBits
    {L G : ℕ} (hL : 0 < L) (hG : 0 < G) (c : Leg) :
    ((cw112SymmetricSourceProbability L G (Nat.add_pos_left hL G)).pushforward
      (cw112SymmetricSourceCoordinate c)).entropyBits =
        2 + cw112MuEntropyBits L G := by
  rw [cw112SymmetricSourceCoordinate_eq_equivCoordinate]
  exact (ProbabilityVector.entropyBits_pushforward_equiv
    (cw112SymmetricVisibleSourceCoordinate c) (cw112SymmetricVisibleEquiv c)
    (cw112SymmetricSourceProbability L G (Nat.add_pos_left hL G))).trans
      (cw112SymmetricVisibleSourceProbability_marginalEntropyBits hL hG c)

/-- **The positive shared-Z sign.**  Every actual block marginal of the normalized 64-address
profile has exactly `2 + H₂(mu,mu,1-2mu)` bits of entropy.

This is the finite entropy identity used by the modern value proof.  In particular, it replaces
the `2 - H₂(...)` retained rate of the weaker flattened shared-Z extraction. -/
theorem cw112SymmetricProfileProbability_marginalEntropyBits
    {L G : ℕ} (hL : 0 < L) (hG : 0 < G) (c : Leg) :
    ((cw112SymmetricProfileProbability L G (Nat.add_pos_left hL G)).pushforward
      (fun s : CW112SymmetricSupport ↦ s.1 c)).entropyBits =
        2 + cw112MuEntropyBits L G := by
  rw [cw112SymmetricProfileProbability_eq_reindex]
  rw [ProbabilityVector.pushforward_reindex]
  have hcoordinate :
      (fun s : CW112SymmetricSupport ↦ s.1 c) ∘ cw112SymmetricSupportEquiv =
        cw112SymmetricSourceCoordinate c := by
    funext source
    cases c <;> rfl
  rw [hcoordinate]
  exact cw112SymmetricSourceProbability_marginalEntropyBits hL hG c

end AlgebraicComplexity.Examples
