/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinograd112Counting
import AlgebraicComplexity.MatrixMultiplication.CTensorExtraction
import AlgebraicComplexity.MatrixMultiplication.CTensorMatrixMultiplication
import AlgebraicComplexity.MatrixMultiplication.PartitionedTypeExtraction

/-!
# Tensor extraction for the exceptional CW `112` type

This file connects the exact `L,L,G,G` counting and two-leg hashing theorem to the actual
partitioned power of the `112` constituent.  The three leg-local marginal constraints
`(L+G,L+G)`, `(L+G,L+G)`, and `(L,L,2G)` uniquely determine the four joint multiplicities, so
they can be implemented by independent block zeroing.

For every successful affine hash seed, the canonical positive tensor power therefore restricts
to the modeled X/Y-isolated subpartition.  X and Y block words are injective there, while repeated
Z words are deliberately retained.  Those repeated-Z fibers are precisely the C-tensor groups to
which `MatrixMultiplication/CTensor.lean` will be applied.

The construction follows journal pages 270--272 of Coppersmith and Winograd, "Matrix
Multiplication via Arithmetic Progressions" (1990), stored locally as `papers/MMult1987.pdf`.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor

/-- Leg-local predicate selecting the prescribed `112` marginal word type. -/
noncomputable def cw112TypeKeepBlock (L G : ℕ) (c : Leg)
    (word : PositiveWord (CW112Block c) (cw112TypeDepth L G)) : Prop :=
  WordType.multiplicity
    (positiveWordEquiv (CW112Block c) (cw112TypeDepth L G) word) =
      cw112MarginalType L G c

/-- The leg-local type predicate is decidable. -/
noncomputable instance cw112TypeKeepBlock_decidable (L G : ℕ) (c : Leg)
    (word : PositiveWord (CW112Block c) (cw112TypeDepth L G)) :
    Decidable (cw112TypeKeepBlock L G c word) := by
  classical
  unfold cw112TypeKeepBlock
  infer_instance

/-- Projecting the multiplicity of a supported-address word to one leg gives the multiplicity of
the corresponding transposed block word. -/
theorem cw112_mappedMultiplicity_eq_legMultiplicity
    (L G : ℕ) (word : PositiveWord cw112BlockSupport (cw112TypeDepth L G)) (c : Leg) :
    WordType.mappedType (fun s : cw112BlockSupport ↦ s.1 c)
        (WordType.multiplicity
          (positiveWordEquiv cw112BlockSupport (cw112TypeDepth L G) word)) =
      WordType.multiplicity
        (positiveWordEquiv (CW112Block c) (cw112TypeDepth L G)
          (PartitionHashEncoding.supportWordAddress
            (A := CW112Block) (support := cw112BlockSupport)
            (cw112TypeDepth L G) word c)) := by
  rw [← WordType.multiplicity_comp_eq_mappedType]
  congr 1
  funext i
  exact congrFun
    (PartitionHashEncoding.positiveWordEquiv_supportWordAddress
      (A := CW112Block) (support := cw112BlockSupport)
      (cw112TypeDepth L G) word c) i |>.symm

/-- The three prescribed marginal word types uniquely recover the joint `L,L,G,G` type.

Proof sketch: the two corner entries of the Z marginal directly recover the two diagonal
multiplicities.  The first X marginal then recovers the first cross multiplicity, and the first Y
marginal recovers the second. -/
theorem mem_cw112TypeWords_iff_keepBlocks (L G : ℕ)
    (word : PositiveWord cw112BlockSupport (cw112TypeDepth L G)) :
    word ∈ cw112TypeWords L G ↔
      ∀ c, cw112TypeKeepBlock L G c
        (PartitionHashEncoding.supportWordAddress
          (A := CW112Block) (support := cw112BlockSupport)
          (cw112TypeDepth L G) word c) := by
  rw [cw112TypeWords, mem_positiveTypeClass]
  let μ := WordType.multiplicity
    (positiveWordEquiv cw112BlockSupport (cw112TypeDepth L G) word)
  constructor
  · intro htype c
    unfold cw112TypeKeepBlock
    rw [← cw112_mappedMultiplicity_eq_legMultiplicity L G word c,
      htype, cw112_mappedType_eq_marginal]
  · intro hkeep
    have hmapped (c : Leg) :
        WordType.mappedType (fun s : cw112BlockSupport ↦ s.1 c) μ =
          cw112MarginalType L G c := by
      rw [cw112_mappedMultiplicity_eq_legMultiplicity L G word c]
      exact hkeep c
    have hZFirst := congrFun (hmapped .Z) CW112ZBlock.firstCorner
    have hZSecond := congrFun (hmapped .Z) CW112ZBlock.secondCorner
    have hXFirst := congrFun (hmapped .X) CW112Side.first
    have hYFirst := congrFun (hmapped .Y) CW112Side.first
    unfold WordType.mappedType WordType.letterFiber at hZFirst hZSecond hXFirst hYFirst
    simp only [Finset.sum_filter] at hZFirst hZSecond hXFirst hYFirst
    change (∑ s : cw112BlockSupport,
      if s.1 .Z = .firstCorner then μ s else 0) = L at hZFirst
    change (∑ s : cw112BlockSupport,
      if s.1 .Z = .secondCorner then μ s else 0) = L at hZSecond
    change (∑ s : cw112BlockSupport,
      if s.1 .X = .first then μ s else 0) = L + G at hXFirst
    change (∑ s : cw112BlockSupport,
      if s.1 .Y = .first then μ s else 0) = L + G at hYFirst
    rw [sum_cw112BlockSupportSubtype] at hZFirst hZSecond hXFirst hYFirst
    simp [cw112DiagonalFirstAddress, cw112DiagonalSecondAddress,
      cw112CrossFirstAddress, cw112CrossSecondAddress, cw112BlockAddress,
      ofLegs_X, ofLegs_Y, ofLegs_Z]
      at hZFirst hZSecond hXFirst hYFirst
    have hCrossFirst : μ cw112CrossFirstS = G := by omega
    have hCrossSecond : μ cw112CrossSecondS = G := by omega
    funext s
    have hs : s = cw112DiagonalFirstS ∨ s = cw112DiagonalSecondS ∨
        s = cw112CrossFirstS ∨ s = cw112CrossSecondS := by
      have hsValue : s.1 = cw112DiagonalFirstAddress ∨
          s.1 = cw112DiagonalSecondAddress ∨
          s.1 = cw112CrossFirstAddress ∨ s.1 = cw112CrossSecondAddress := by
        simpa only [cw112BlockSupport, Finset.mem_insert, Finset.mem_singleton]
          using s.property
      rcases hsValue with hs | hs | hs | hs
      · exact Or.inl (Subtype.ext hs)
      · exact Or.inr (Or.inl (Subtype.ext hs))
      · exact Or.inr (Or.inr (Or.inl (Subtype.ext hs)))
      · exact Or.inr (Or.inr (Or.inr (Subtype.ext hs)))
    rcases hs with rfl | rfl | rfl | rfl
    · simpa [μ, cw112NaturalType, cw112DiagonalFirstAddress, cw112BlockAddress] using hZFirst
    · simpa [μ, cw112NaturalType, cw112DiagonalSecondAddress, cw112BlockAddress] using hZSecond
    · simpa [μ, cw112NaturalType, cw112CrossFirstAddress, cw112BlockAddress]
        using hCrossFirst
    · simpa [μ, cw112NaturalType, cw112CrossSecondAddress, cw112BlockAddress]
        using hCrossSecond

section TensorPower

universe u

variable (K : Type u) [CommRing K]
variable (q L G : ℕ)

/-- Packaged constant side module.  Packaging the instances before recursion avoids asking type
class synthesis to unfold a symbolic word depth. -/
def cw112UniformSideFamily : LegModuleFamily K where
  Space _ := Fin q → K

/-- Word-independent iterated side space.  A word of depth `n` contains `n+1` copies of
`Fin q → K`, left-associated exactly as in `PositivePowerBlockSpace`. -/
abbrev CW112UniformSideSpace (n : ℕ) : Type u :=
  ((cw112UniformSideFamily K q).iterated n).Space .X

/-- First matrix-multiplication dimension of a supported base `112` constituent.  The two
cross constituents have dimension `q`; the diagonal constituents have dimension one. -/
abbrev cw112TensorConstituentM
    (s : (cw112PartitionedTensor K q).support) : ℕ :=
  match s.1 .Z with
  | .grid => q
  | _ => 1

/-- Middle matrix-multiplication dimension of a supported base `112` constituent.  This is
`q` on the two diagonal constituents and one on the two cross constituents. -/
abbrev cw112TensorConstituentN
    (s : (cw112PartitionedTensor K q).support) : ℕ :=
  match s.1 .Z with
  | .grid => 1
  | _ => q

/-- Third matrix-multiplication dimension of a supported base `112` constituent. -/
abbrev cw112TensorConstituentP
    (s : (cw112PartitionedTensor K q).support) : ℕ :=
  match s.1 .Z with
  | .grid => q
  | _ => 1

/-- Every supported base `112` constituent restricts to the rectangular tensor recorded by
`cw112TensorConstituentM/N/P`.

Proof sketch: enumerate the four supported addresses.  The two diagonal cases use the checked
`⟨1,q,1⟩` certificates, and the two cross cases use the checked `⟨q,1,q⟩` certificates. -/
theorem cw112SupportedConstituent_restricts
    (s : (cw112PartitionedTensor K q).support) :
    Restricts ((cw112PartitionedTensor K q).constituent s.1)
      (matrixMultiplication (K := K)
        (cw112TensorConstituentM K q s)
        (cw112TensorConstituentN K q s)
        (cw112TensorConstituentP K q s)) := by
  rcases s with ⟨s, hs⟩
  simp only [cw112PartitionedTensor_support, cw112BlockSupport,
    Finset.mem_insert, Finset.mem_singleton] at hs
  rcases hs with rfl | rfl | rfl | rfl
  · exact cw112DiagonalFirstConstituent_restricts K q
  · exact cw112DiagonalSecondConstituent_restricts K q
  · exact cw112CrossFirstConstituent_restricts K q
  · exact cw112CrossSecondConstituent_restricts K q

/-- A selected `L,L,G,G` word has first dimension `q^(2G)`. -/
theorem cw112Type_positiveWordProduct_m
    (word : PositiveWord (cw112PartitionedTensor K q).support (cw112TypeDepth L G))
    (hword : word ∈ positiveTypeClass (cw112PartitionedTensor K q).support
      (cw112TypeDepth L G) (cw112NaturalType L G)) :
    positiveWordProduct (cw112TensorConstituentM K q)
      (cw112TypeDepth L G) word = q ^ (2 * G) := by
  rw [positiveWordProduct_eq_prod_pow (a := cw112NaturalType L G)
    (cw112TensorConstituentM K q) hword]
  change (∏ s : cw112BlockSupport,
    cw112TensorConstituentM K q s ^ cw112NaturalType L G s) = _
  rw [prod_cw112BlockSupportSubtype]
  simp [cw112TensorConstituentM, cw112NaturalType, cw112DiagonalFirstAddress,
    cw112DiagonalSecondAddress, cw112CrossFirstAddress, cw112CrossSecondAddress,
    cw112BlockAddress, ← pow_add, two_mul]

/-- A selected `L,L,G,G` word has middle dimension `q^(2L)`. -/
theorem cw112Type_positiveWordProduct_n
    (word : PositiveWord (cw112PartitionedTensor K q).support (cw112TypeDepth L G))
    (hword : word ∈ positiveTypeClass (cw112PartitionedTensor K q).support
      (cw112TypeDepth L G) (cw112NaturalType L G)) :
    positiveWordProduct (cw112TensorConstituentN K q)
      (cw112TypeDepth L G) word = q ^ (2 * L) := by
  rw [positiveWordProduct_eq_prod_pow (a := cw112NaturalType L G)
    (cw112TensorConstituentN K q) hword]
  change (∏ s : cw112BlockSupport,
    cw112TensorConstituentN K q s ^ cw112NaturalType L G s) = _
  rw [prod_cw112BlockSupportSubtype]
  simp [cw112TensorConstituentN, cw112NaturalType, cw112DiagonalFirstAddress,
    cw112DiagonalSecondAddress, cw112CrossFirstAddress, cw112CrossSecondAddress,
    cw112BlockAddress, ← pow_add, two_mul]

/-- A selected `L,L,G,G` word has third dimension `q^(2G)`. -/
theorem cw112Type_positiveWordProduct_p
    (word : PositiveWord (cw112PartitionedTensor K q).support (cw112TypeDepth L G))
    (hword : word ∈ positiveTypeClass (cw112PartitionedTensor K q).support
      (cw112TypeDepth L G) (cw112NaturalType L G)) :
    positiveWordProduct (cw112TensorConstituentP K q)
      (cw112TypeDepth L G) word = q ^ (2 * G) := by
  rw [positiveWordProduct_eq_prod_pow (a := cw112NaturalType L G)
    (cw112TensorConstituentP K q) hword]
  change (∏ s : cw112BlockSupport,
    cw112TensorConstituentP K q s ^ cw112NaturalType L G s) = _
  rw [prod_cw112BlockSupportSubtype]
  simp [cw112TensorConstituentP, cw112NaturalType, cw112DiagonalFirstAddress,
    cw112DiagonalSecondAddress, cw112CrossFirstAddress, cw112CrossSecondAddress,
    cw112BlockAddress, ← pow_add, two_mul]

/-- One X side block is canonically the standard coordinate space, independently of its label. -/
def cw112XBlockEquiv (b : CW112Side) :
    CW112PartitionBlockSpace K q .X b ≃ₗ[K] (Fin q → K) :=
  LinearEquiv.refl K _

/-- One Y side block is canonically the standard coordinate space, independently of its label. -/
def cw112YBlockEquiv (b : CW112Side) :
    CW112PartitionBlockSpace K q .Y b ≃ₗ[K] (Fin q → K) :=
  LinearEquiv.refl K _

/-- Every positive X-block word is canonically equivalent to the word-independent side space. -/
noncomputable def cw112PositiveXEquiv : (n : ℕ) →
    (word : PositiveWord CW112Side n) →
      PositivePowerBlockSpace K (CW112PartitionBlockSpace K q) n .X word ≃ₗ[K]
        CW112UniformSideSpace K q n
  | 0, _ => LinearEquiv.refl K _
  | n + 1, word => TensorProduct.congr
      (cw112PositiveXEquiv n word.1) (cw112XBlockEquiv K q word.2)

/-- Every positive Y-block word is canonically equivalent to the same word-independent side
space. -/
noncomputable def cw112PositiveYEquiv : (n : ℕ) →
    (word : PositiveWord CW112Side n) →
      PositivePowerBlockSpace K (CW112PartitionBlockSpace K q) n .Y word ≃ₗ[K]
        CW112UniformSideSpace K q n
  | 0, _ => LinearEquiv.refl K _
  | n + 1, word => TensorProduct.congr
      (cw112PositiveYEquiv n word.1) (cw112YBlockEquiv K q word.2)

/-- Canonical uniform X-side space at the selected CW word depth. -/
abbrev CW112PositiveXSpace := CW112UniformSideSpace K q (cw112TypeDepth L G)

/-- Canonical uniform Y-side space at the selected CW word depth. -/
abbrev CW112PositiveYSpace := CW112UniformSideSpace K q (cw112TypeDepth L G)

/-- The joint-type subpartition of the `2(L+G)`-fold `112` tensor power. -/
noncomputable def cw112TypePartitionedPower :
    PartitionedTensor (K := K)
      (A := fun c ↦ PositiveWord (CW112Block c) (cw112TypeDepth L G))
      (PositivePowerBlockSpace K (CW112PartitionBlockSpace K q)
        (cw112TypeDepth L G)) :=
  ((cw112PartitionedTensor K q).positivePower (cw112TypeDepth L G)).select
    (cw112TypeKeepBlock L G)

/-- The selected power support is exactly the modeled legal-target family of joint-type words. -/
theorem cw112TypePartitionedPower_support
    {R : Type*} [Field R] [NeZero (2 : R)] :
    (cw112TypePartitionedPower K q L G).support =
      (cw112PartitionHashEncoding (R := R)).modeledAddresses
        (cw112TypeDepth L G) (cw112TypeTargets (R := R) L G) := by
  classical
  unfold cw112TypePartitionedPower cw112TypeTargets
  change ((cw112PartitionedTensor K q).positivePower (cw112TypeDepth L G)).support.filter
      (fun s ↦ ∀ c, cw112TypeKeepBlock L G c (s c)) = _
  rw [(cw112PartitionHashEncoding (R := R)).positivePower_support_eq_modeledLegalTargets
    (cw112PartitionedTensor K q) (cw112TypeDepth L G)]
  exact (cw112PartitionHashEncoding (R := R)).filter_modeledLegalTargets_eq_of_mem_iff
    (cw112TypeDepth L G) (cw112TypeWords L G) (cw112TypeKeepBlock L G)
      (mem_cw112TypeWords_iff_keepBlocks L G)

/-- The canonical power of the partitioned `112` realization restricts to its joint-type
subpartition before hashing. -/
theorem cw112Power_restricts_typePartitionedPower :
    Restricts
      (Tensor.power (cw112PartitionedTensor K q).realize (cw112TypeDepth L G + 1))
      (cw112TypePartitionedPower K q L G).realize := by
  exact (Tensor.Restricts.power_partitionedPositivePower
      (cw112PartitionedTensor K q) (cw112TypeDepth L G)).trans
    (Tensor.Restricts.partitionedSelect
      ((cw112PartitionedTensor K q).positivePower (cw112TypeDepth L G))
      (cw112TypeKeepBlock L G))

/-- For a fixed progression-free hash seed, the canonical `112` power restricts to the
X/Y-isolated subpartition while retaining every shared Z fiber. -/
theorem cw112Power_restricts_xyIsolated
    {R : Type*} [Field R] [NeZero (2 : R)]
    (B : Finset R) (hB : ThreeAPFree (B : Set R))
    (seed : ProgressionHash.Seed R (Fin (cw112TypeDepth L G + 1))) :
    Restricts
      (Tensor.power (cw112PartitionedTensor K q).realize (cw112TypeDepth L G + 1))
      ((cw112TypePartitionedPower K q L G).withSupport
        ((cw112PartitionHashEncoding (R := R)).xyIsolatedPowerAddresses
          (cw112TypeDepth L G) (cw112TypeWords L G) B seed)).realize := by
  apply (cw112Power_restricts_typePartitionedPower K q L G).trans
  apply Tensor.Restricts.modeledTargets_to_xyIsolated
    (cw112PartitionHashEncoding (R := R)) (cw112TypeWords L G) B hB seed
      (cw112TypePartitionedPower K q L G)
  exact cw112TypePartitionedPower_support K q L G

/-- The modeled X/Y-isolated support has exactly the number of isolated legal targets counted by
the finite hashing theorem. -/
theorem card_cw112XYIsolatedPowerAddresses
    {R : Type*} [Field R] [NeZero (2 : R)]
    (B : Finset R) (seed : ProgressionHash.Seed R (Fin (cw112TypeDepth L G + 1))) :
    ((cw112PartitionHashEncoding (R := R)).xyIsolatedPowerAddresses
      (cw112TypeDepth L G) (cw112TypeWords L G) B seed).card =
      (ProgressionHash.LegalTriple.xyIsolatedTargets
        (cw112TypeTargets (R := R) L G) B seed).card := by
  exact (cw112PartitionHashEncoding (R := R)).card_xyIsolatedPowerAddresses
    (cw112TypeDepth L G) (cw112TypeWords L G) B seed

/-- The retained modeled addresses are injective on X. -/
theorem cw112XYIsolatedPowerAddresses_xInjective
    {R : Type*} [Field R] [NeZero (2 : R)]
    (B : Finset R) (hB : ThreeAPFree (B : Set R))
    (seed : ProgressionHash.Seed R (Fin (cw112TypeDepth L G + 1))) :
    Set.InjOn
      (fun s : BlockAddress
        (fun c ↦ PositiveWord (CW112Block c) (cw112TypeDepth L G)) ↦ s .X)
      ((cw112PartitionHashEncoding (R := R)).xyIsolatedPowerAddresses
        (cw112TypeDepth L G) (cw112TypeWords L G) B seed : Set _) :=
  (cw112PartitionHashEncoding (R := R)).x_injectiveOn_xyIsolatedPowerAddresses
    (cw112TypeDepth L G) (cw112TypeWords L G) B hB seed

/-- The retained modeled addresses are injective on Y. -/
theorem cw112XYIsolatedPowerAddresses_yInjective
    {R : Type*} [Field R] [NeZero (2 : R)]
    (B : Finset R) (hB : ThreeAPFree (B : Set R))
    (seed : ProgressionHash.Seed R (Fin (cw112TypeDepth L G + 1))) :
    Set.InjOn
      (fun s : BlockAddress
        (fun c ↦ PositiveWord (CW112Block c) (cw112TypeDepth L G)) ↦ s .Y)
      ((cw112PartitionHashEncoding (R := R)).xyIsolatedPowerAddresses
        (cw112TypeDepth L G) (cw112TypeWords L G) B seed : Set _) :=
  (cw112PartitionHashEncoding (R := R)).y_injectiveOn_xyIsolatedPowerAddresses
    (cw112TypeDepth L G) (cw112TypeWords L G) B hB seed

/-! ## Fixed-Z fibers as genuine C-tensors -/

/-- The portion of the X/Y-isolated support sharing one prescribed Z block word. -/
noncomputable def cw112XYIsolatedZFiber
    {R : Type*} [Field R] [NeZero (2 : R)]
    (B : Finset R) (seed : ProgressionHash.Seed R (Fin (cw112TypeDepth L G + 1)))
    (z : PositiveWord CW112ZBlock (cw112TypeDepth L G)) :
    Finset (BlockAddress
      (fun c ↦ PositiveWord (CW112Block c) (cw112TypeDepth L G))) :=
  ((cw112PartitionHashEncoding (R := R)).xyIsolatedPowerAddresses
      (cw112TypeDepth L G) (cw112TypeWords L G) B seed).filter
    (fun s ↦ s .Z = z)

/-- Canonical enumeration of one finite shared-Z fiber. -/
noncomputable def cw112ZFiberEquiv
    {R : Type*} [Field R] [NeZero (2 : R)]
    (B : Finset R) (seed : ProgressionHash.Seed R (Fin (cw112TypeDepth L G + 1)))
    (z : PositiveWord CW112ZBlock (cw112TypeDepth L G)) :
    Fin (cw112XYIsolatedZFiber L G B seed z).card ≃ cw112XYIsolatedZFiber L G B seed z :=
  (cw112XYIsolatedZFiber L G B seed z).equivFin.symm

/-- X label attached to an enumerated address in one shared-Z fiber. -/
noncomputable def cw112ZFiberXLabel
    {R : Type*} [Field R] [NeZero (2 : R)]
    (B : Finset R) (seed : ProgressionHash.Seed R (Fin (cw112TypeDepth L G + 1)))
    (z : PositiveWord CW112ZBlock (cw112TypeDepth L G))
    (i : Fin (cw112XYIsolatedZFiber L G B seed z).card) :
    PositiveWord CW112Side (cw112TypeDepth L G) :=
  (cw112ZFiberEquiv L G B seed z i).1 .X

/-- Y label attached to an enumerated address in one shared-Z fiber. -/
noncomputable def cw112ZFiberYLabel
    {R : Type*} [Field R] [NeZero (2 : R)]
    (B : Finset R) (seed : ProgressionHash.Seed R (Fin (cw112TypeDepth L G + 1)))
    (z : PositiveWord CW112ZBlock (cw112TypeDepth L G))
    (i : Fin (cw112XYIsolatedZFiber L G B seed z).card) :
    PositiveWord CW112Side (cw112TypeDepth L G) :=
  (cw112ZFiberEquiv L G B seed z i).1 .Y

/-- Reconstructing an enumerated fiber address from its X/Y labels and the fixed Z word gives
the original address. -/
theorem cw112ZFiber_fiberAddress_eq
    {R : Type*} [Field R] [NeZero (2 : R)]
    (B : Finset R) (seed : ProgressionHash.Seed R (Fin (cw112TypeDepth L G + 1)))
    (z : PositiveWord CW112ZBlock (cw112TypeDepth L G))
    (i : Fin (cw112XYIsolatedZFiber L G B seed z).card) :
    CTensor.fiberAddress
        (cw112ZFiberXLabel L G B seed z) (cw112ZFiberYLabel L G B seed z) z i =
      (cw112ZFiberEquiv L G B seed z i).1 := by
  funext c
  cases c with
  | X => rfl
  | Y => rfl
  | Z =>
      exact (Finset.mem_filter.mp (cw112ZFiberEquiv L G B seed z i).2).2.symm

/-- The fixed-Z fiber is exactly the image of its canonical `Fin card` enumeration. -/
theorem cw112ZFiber_eq_univ_map
    {R : Type*} [Field R] [NeZero (2 : R)]
    (B : Finset R) (seed : ProgressionHash.Seed R (Fin (cw112TypeDepth L G + 1)))
    (z : PositiveWord CW112ZBlock (cw112TypeDepth L G))
    (hx : Function.Injective (cw112ZFiberXLabel L G B seed z)) :
    cw112XYIsolatedZFiber L G B seed z = Finset.univ.map
      (CTensor.fiberAddressEmbedding
        (cw112ZFiberXLabel L G B seed z) (cw112ZFiberYLabel L G B seed z) z hx) := by
  classical
  ext s
  constructor
  · intro hs
    let indexed : cw112XYIsolatedZFiber L G B seed z := ⟨s, hs⟩
    let i := (cw112XYIsolatedZFiber L G B seed z).equivFin indexed
    apply Finset.mem_map.mpr
    refine ⟨i, Finset.mem_univ i, ?_⟩
    change CTensor.fiberAddress
      (cw112ZFiberXLabel L G B seed z) (cw112ZFiberYLabel L G B seed z) z i = s
    rw [cw112ZFiber_fiberAddress_eq L G B seed z i]
    exact congrArg Subtype.val
      ((cw112XYIsolatedZFiber L G B seed z).equivFin.symm_apply_apply indexed)
  · intro hs
    rcases Finset.mem_map.mp hs with ⟨i, _hi, rfl⟩
    change CTensor.fiberAddress
      (cw112ZFiberXLabel L G B seed z) (cw112ZFiberYLabel L G B seed z) z i ∈
        cw112XYIsolatedZFiber L G B seed z
    rw [cw112ZFiber_fiberAddress_eq L G B seed z i]
    exact (cw112ZFiberEquiv L G B seed z i).2

/-- X labels of a fixed-Z fiber are injective, inherited from two-leg hashing isolation. -/
theorem cw112ZFiberXLabel_injective
    {R : Type*} [Field R] [NeZero (2 : R)]
    (B : Finset R) (hB : ThreeAPFree (B : Set R))
    (seed : ProgressionHash.Seed R (Fin (cw112TypeDepth L G + 1)))
    (z : PositiveWord CW112ZBlock (cw112TypeDepth L G)) :
    Function.Injective (cw112ZFiberXLabel L G B seed z) := by
  intro i j hij
  apply (cw112ZFiberEquiv L G B seed z).injective
  apply Subtype.ext
  apply cw112XYIsolatedPowerAddresses_xInjective L G B hB seed
  · exact (Finset.mem_filter.mp (cw112ZFiberEquiv L G B seed z i).2).1
  · exact (Finset.mem_filter.mp (cw112ZFiberEquiv L G B seed z j).2).1
  · exact hij

/-- Y labels of a fixed-Z fiber are injective, inherited from two-leg hashing isolation. -/
theorem cw112ZFiberYLabel_injective
    {R : Type*} [Field R] [NeZero (2 : R)]
    (B : Finset R) (hB : ThreeAPFree (B : Set R))
    (seed : ProgressionHash.Seed R (Fin (cw112TypeDepth L G + 1)))
    (z : PositiveWord CW112ZBlock (cw112TypeDepth L G)) :
    Function.Injective (cw112ZFiberYLabel L G B seed z) := by
  intro i j hij
  apply (cw112ZFiberEquiv L G B seed z).injective
  apply Subtype.ext
  apply cw112XYIsolatedPowerAddresses_yInjective L G B hB seed
  · exact (Finset.mem_filter.mp (cw112ZFiberEquiv L G B seed z i).2).1
  · exact (Finset.mem_filter.mp (cw112ZFiberEquiv L G B seed z j).2).1
  · exact hij

/-- Retyping certificate identifying one hashed shared-Z fiber with the reusable uniform
C-tensor interface.  All leg maps are identities after unfolding the constant side-block types;
in particular, the Z map is one common identity for the entire fiber. -/
noncomputable def cw112ZFiberRetyping
    {R : Type*} [Field R] [NeZero (2 : R)]
    (B : Finset R) (hB : ThreeAPFree (B : Set R))
    (seed : ProgressionHash.Seed R (Fin (cw112TypeDepth L G + 1)))
    (z : PositiveWord CW112ZBlock (cw112TypeDepth L G)) :
    CTensor.FiberRetyping
      (X := CW112PositiveXSpace K q L G) (Y := CW112PositiveYSpace K q L G)
      (Z := PositivePowerBlockSpace K (CW112PartitionBlockSpace K q)
        (cw112TypeDepth L G) .Z z)
      (cw112TypePartitionedPower K q L G)
      (cw112XYIsolatedZFiber L G B seed z)
      (cw112XYIsolatedZFiber L G B seed z).card where
  xLabel := cw112ZFiberXLabel L G B seed z
  yLabel := cw112ZFiberYLabel L G B seed z
  x_injective := cw112ZFiberXLabel_injective L G B hB seed z
  y_injective := cw112ZFiberYLabel_injective L G B hB seed z
  zLabel := z
  selected_eq := cw112ZFiber_eq_univ_map L G B seed z
    (cw112ZFiberXLabel_injective L G B hB seed z)
  xMap := fun i ↦ (cw112PositiveXEquiv K q (cw112TypeDepth L G)
    (cw112ZFiberXLabel L G B seed z i)).toLinearMap
  yMap := fun i ↦ (cw112PositiveYEquiv K q (cw112TypeDepth L G)
    (cw112ZFiberYLabel L G B seed z i)).toLinearMap
  zMap := LinearMap.id

/-- Every enumerated address in a hashed Z fiber comes from a selected supported-address word
of joint type `L,L,G,G`.

Proof sketch: the fiber lies inside the XY-isolated address family, which lies inside the
hash-filtered family and hence inside the original modeled legal-target family.  Unpacking a
modeled legal target recovers the required source word. -/
theorem exists_cw112TypeWord_of_ZFiberIndex
    {R : Type*} [Field R] [NeZero (2 : R)]
    (B : Finset R) (hB : ThreeAPFree (B : Set R))
    (seed : ProgressionHash.Seed R (Fin (cw112TypeDepth L G + 1)))
    (z : PositiveWord CW112ZBlock (cw112TypeDepth L G))
    (i : Fin (cw112XYIsolatedZFiber L G B seed z).card) :
    ∃ word ∈ cw112TypeWords L G,
      positiveSupportWordBlockAddress cw112BlockSupport (cw112TypeDepth L G) word =
        (cw112ZFiberRetyping (K := K) q L G B hB seed z).sourceAddress i := by
  let H := cw112PartitionHashEncoding (R := R)
  have hxy : (cw112ZFiberEquiv L G B seed z i).1 ∈
      H.xyIsolatedPowerAddresses (cw112TypeDepth L G) (cw112TypeWords L G) B seed :=
    (Finset.mem_filter.mp (cw112ZFiberEquiv L G B seed z i).2).1
  have hfiltered := H.xyIsolatedPowerAddresses_subset_filteredPowerAddresses
    (cw112TypeDepth L G) (cw112TypeWords L G) B seed hxy
  have hmodeled := H.filteredPowerAddresses_subset_modeledAddresses
    (cw112TypeDepth L G) (cw112TypeWords L G) B seed hfiltered
  obtain ⟨word, hword, haddress⟩ :=
    H.exists_sourceWord_of_mem_modeledAddresses_legalTargets
      (cw112TypeDepth L G) (cw112TypeWords L G) hmodeled
  refine ⟨word, hword, ?_⟩
  calc
    positiveSupportWordBlockAddress cw112BlockSupport (cw112TypeDepth L G) word =
        (cw112ZFiberEquiv L G B seed z i).1 := haddress
    _ = (cw112ZFiberRetyping (K := K) q L G B hB seed z).sourceAddress i :=
      (cw112ZFiber_fiberAddress_eq L G B seed z i).symm

/-- The source constituent represented by one hashed Z-fiber index restricts to
`⟨q^(2G),q^(2L),q^(2G)⟩`.

Proof sketch: recover its joint-type source word, apply the generic positive-power constituent
theorem to the four checked base restrictions, and substitute the three exact word products. -/
theorem cw112ZFiber_sourceConstituent_restricts
    {R : Type*} [Field R] [NeZero (2 : R)]
    (B : Finset R) (hB : ThreeAPFree (B : Set R))
    (seed : ProgressionHash.Seed R (Fin (cw112TypeDepth L G + 1)))
    (z : PositiveWord CW112ZBlock (cw112TypeDepth L G))
    (i : Fin (cw112XYIsolatedZFiber L G B seed z).card) :
    Restricts
      ((cw112TypePartitionedPower K q L G).constituent
        ((cw112ZFiberRetyping (K := K) q L G B hB seed z).sourceAddress i))
      (matrixMultiplication (K := K) (q ^ (2 * G)) (q ^ (2 * L)) (q ^ (2 * G))) := by
  obtain ⟨word, hword, haddress⟩ :=
    exists_cw112TypeWord_of_ZFiberIndex (K := K) q L G B hB seed z i
  change PositiveWord (cw112PartitionedTensor K q).support (cw112TypeDepth L G) at word
  change word ∈ positiveTypeClass (cw112PartitionedTensor K q).support
    (cw112TypeDepth L G) (cw112NaturalType L G) at hword
  change positiveSupportWordBlockAddress (cw112PartitionedTensor K q).support
    (cw112TypeDepth L G) word =
      (cw112ZFiberRetyping (K := K) q L G B hB seed z).sourceAddress i at haddress
  have hrestrict := Tensor.Restricts.positivePower_constituent_matrixMultiplication
    (cw112PartitionedTensor K q)
    (cw112TensorConstituentM K q) (cw112TensorConstituentN K q)
    (cw112TensorConstituentP K q)
    (cw112SupportedConstituent_restricts K q)
    (cw112TypeDepth L G) word
  have hm := cw112Type_positiveWordProduct_m K q L G word hword
  have hn := cw112Type_positiveWordProduct_n K q L G word hword
  rw [hm, hn] at hrestrict
  rw [haddress] at hrestrict
  simpa only [cw112TypePartitionedPower, PartitionedTensor.select] using hrestrict

/-- Leg equivalences underlying the CW fiber retyping at one constituent. -/
noncomputable def cw112ZFiberConstituentEquiv
    {R : Type*} [Field R] [NeZero (2 : R)]
    (B : Finset R) (hB : ThreeAPFree (B : Set R))
    (seed : ProgressionHash.Seed R (Fin (cw112TypeDepth L G + 1)))
    (z : PositiveWord CW112ZBlock (cw112TypeDepth L G))
    (i : Fin (cw112XYIsolatedZFiber L G B seed z).card) : ∀ c,
    PositivePowerBlockSpace K (CW112PartitionBlockSpace K q) (cw112TypeDepth L G) c
        ((cw112ZFiberRetyping (K := K) q L G B hB seed z).sourceAddress i c) ≃ₗ[K]
      CTensor.ConstituentSpace
        (CW112PositiveXSpace K q L G) (CW112PositiveYSpace K q L G)
        (PositivePowerBlockSpace K (CW112PartitionBlockSpace K q)
          (cw112TypeDepth L G) .Z z) c := by
  intro c
  cases c with
  | X =>
    change PositivePowerBlockSpace K (CW112PartitionBlockSpace K q)
        (cw112TypeDepth L G) .X (cw112ZFiberXLabel L G B seed z i) ≃ₗ[K]
      CW112UniformSideSpace K q (cw112TypeDepth L G)
    exact cw112PositiveXEquiv K q (cw112TypeDepth L G)
      (cw112ZFiberXLabel L G B seed z i)
  | Y =>
    change PositivePowerBlockSpace K (CW112PartitionBlockSpace K q)
        (cw112TypeDepth L G) .Y (cw112ZFiberYLabel L G B seed z i) ≃ₗ[K]
      CW112UniformSideSpace K q (cw112TypeDepth L G)
    exact cw112PositiveYEquiv K q (cw112TypeDepth L G)
      (cw112ZFiberYLabel L G B seed z i)
  | Z =>
    change PositivePowerBlockSpace K (CW112PartitionBlockSpace K q)
        (cw112TypeDepth L G) .Z z ≃ₗ[K]
      PositivePowerBlockSpace K (CW112PartitionBlockSpace K q)
        (cw112TypeDepth L G) .Z z
    exact LinearEquiv.refl K _

/-- Retyping one CW Z-fiber constituent is a legwise tensor isomorphism. -/
theorem cw112ZFiber_sourceConstituent_isomorphic
    {R : Type*} [Field R] [NeZero (2 : R)]
    (B : Finset R) (hB : ThreeAPFree (B : Set R))
    (seed : ProgressionHash.Seed R (Fin (cw112TypeDepth L G + 1)))
    (z : PositiveWord CW112ZBlock (cw112TypeDepth L G))
    (i : Fin (cw112XYIsolatedZFiber L G B seed z).card) :
    Isomorphic
      ((cw112TypePartitionedPower K q L G).constituent
        ((cw112ZFiberRetyping (K := K) q L G B hB seed z).sourceAddress i))
      ((cw112ZFiberRetyping (K := K) q L G B hB seed z).targetConstituent i) := by
  refine ⟨cw112ZFiberConstituentEquiv (K := K) q L G B hB seed z i, ?_⟩
  change Tensor.map
      (fun c ↦ (cw112ZFiberConstituentEquiv (K := K) q L G B hB seed z i c).toLinearMap)
      ((cw112TypePartitionedPower K q L G).constituent
        ((cw112ZFiberRetyping (K := K) q L G B hB seed z).sourceAddress i)) =
    Tensor.map
      ((cw112ZFiberRetyping (K := K) q L G B hB seed z).constituentMap i)
      ((cw112TypePartitionedPower K q L G).constituent
        ((cw112ZFiberRetyping (K := K) q L G B hB seed z).sourceAddress i))
  rw [show
    (fun c ↦ (cw112ZFiberConstituentEquiv (K := K) q L G B hB seed z i c).toLinearMap) =
      (cw112ZFiberRetyping (K := K) q L G B hB seed z).constituentMap i by
        funext c
        cases c <;> rfl]

/-- Every uniformly retyped constituent in a hashed Z fiber restricts to the same rectangular
matrix-multiplication tensor `⟨q^(2G),q^(2L),q^(2G)⟩`. -/
theorem cw112ZFiber_targetConstituent_restricts
    {R : Type*} [Field R] [NeZero (2 : R)]
    (B : Finset R) (hB : ThreeAPFree (B : Set R))
    (seed : ProgressionHash.Seed R (Fin (cw112TypeDepth L G + 1)))
    (z : PositiveWord CW112ZBlock (cw112TypeDepth L G))
    (i : Fin (cw112XYIsolatedZFiber L G B seed z).card) :
    Restricts
      ((cw112ZFiberRetyping (K := K) q L G B hB seed z).targetConstituent i)
      (matrixMultiplication (K := K) (q ^ (2 * G)) (q ^ (2 * L)) (q ^ (2 * G))) := by
  exact (cw112ZFiber_sourceConstituent_isomorphic (K := K) q L G B hB seed z i).symm.restricts.trans
    (cw112ZFiber_sourceConstituent_restricts (K := K) q L G B hB seed z i)

/-- A constituent of the three-orientation cyclic product of one hashed Z fiber restricts to a
square matrix-multiplication tensor of side `q^(4G+2L)`.

Proof sketch: the three orientations of `⟨q^(2G),q^(2L),q^(2G)⟩` have dimensions
`(a,b,a)`, `(a,a,b)`, and `(b,a,a)`.  Their external product is therefore square of side
`a²b = q^(4G+2L)`.  The generic C-tensor theorem identifies that product with the constituent
at `tripleAddress i j k`. -/
theorem cw112ZFiber_cyclicTriple_constituent_restricts_square
    {R : Type*} [Field R] [NeZero (2 : R)]
    (B : Finset R) (hB : ThreeAPFree (B : Set R))
    (seed : ProgressionHash.Seed R (Fin (cw112TypeDepth L G + 1)))
    (z : PositiveWord CW112ZBlock (cw112TypeDepth L G))
    (i j k : Fin (cw112XYIsolatedZFiber L G B seed z).card) :
    Restricts
      ((CTensor.cyclicTriple
        (cw112ZFiberRetyping (K := K) q L G B hB seed z).targetConstituent).constituent
          (CTensor.tripleAddress i j k))
      (matrixMultiplication (K := K)
        (q ^ (4 * G + 2 * L)) (q ^ (4 * G + 2 * L)) (q ^ (4 * G + 2 * L))) := by
  let T := (cw112ZFiberRetyping (K := K) q L G B hB seed z).targetConstituent
  let a := q ^ (2 * G)
  let b := q ^ (2 * L)
  let side := q ^ (4 * G + 2 * L)
  have hi : Restricts (T i) (matrixMultiplication (K := K) a b a) :=
    cw112ZFiber_targetConstituent_restricts (K := K) q L G B hB seed z i
  have hj : Restricts (Tensor.permute cycle (T j))
      (matrixMultiplication (K := K) a a b) :=
    ((cw112ZFiber_targetConstituent_restricts (K := K) q L G B hB seed z j).permute
      cycle).trans
        (Tensor.Isomorphic.matrixMultiplication_cycle (K := K) a b a).restricts
  have hk : Restricts (Tensor.permute cycle.symm (T k))
      (matrixMultiplication (K := K) b a a) :=
    ((cw112ZFiber_targetConstituent_restricts (K := K) q L G B hB seed z k).permute
      cycle.symm).trans
        (Tensor.Isomorphic.matrixMultiplication_cycle_symm (K := K) a b a).restricts
  have hfirst : Restricts
      (Tensor.external (T i) (Tensor.permute cycle (T j)))
      (matrixMultiplication (K := K) (a * a) (b * a) (a * b)) :=
    (hi.external hj).trans
      (Tensor.Isomorphic.matrixMultiplication_external (K := K) a b a a a b).restricts
  have hall : Restricts
      (Tensor.external
        (Tensor.external (T i) (Tensor.permute cycle (T j)))
        (Tensor.permute cycle.symm (T k)))
      (matrixMultiplication (K := K)
        ((a * a) * b) ((b * a) * a) ((a * b) * a)) :=
    (hfirst.external hk).trans
      (Tensor.Isomorphic.matrixMultiplication_external (K := K)
        (a * a) (b * a) (a * b) b a a).restricts
  have hX : (a * a) * b = side := by
    dsimp [a, b, side]
    rw [← pow_add, ← pow_add]
    congr 1
    omega
  have hY : (b * a) * a = side := by
    dsimp [a, b, side]
    rw [← pow_add, ← pow_add]
    congr 1
    omega
  have hZ : (a * b) * a = side := by
    dsimp [a, b, side]
    rw [← pow_add, ← pow_add]
    congr 1
    omega
  have hsquare := hall.trans
    (Tensor.Isomorphic.matrixMultiplication_congr (K := K) hX hY hZ).restricts
  exact
    (CTensor.cyclicTriple_constituent_tripleAddress_isomorphic T i j k).symm.restricts.trans
      hsquare

/-- Every minimum-weight antidiagonal constituent of a hashed CW Z fiber restricts to the same
square tensor of side `q^(4G+2L)`.

Proof sketch: membership in the antidiagonal support implies membership in the full cyclic
triple support, hence the address is `tripleAddress i j k` for some indices.  Selection does not
change the stored constituent, so the preceding square restriction applies. -/
theorem cw112ZFiber_antidiagonalConstituent_restricts_square
    {R : Type*} [Field R] [NeZero (2 : R)]
    (B : Finset R) (hB : ThreeAPFree (B : Set R))
    (seed : ProgressionHash.Seed R (Fin (cw112TypeDepth L G + 1)))
    (z : PositiveWord CW112ZBlock (cw112TypeDepth L G))
    (s : (CTensor.antidiagonal
      (cw112ZFiberRetyping (K := K) q L G B hB seed z).targetConstituent).support) :
    Restricts
      ((CTensor.antidiagonal
        (cw112ZFiberRetyping (K := K) q L G B hB seed z).targetConstituent).constituent s.1)
      (matrixMultiplication (K := K)
        (q ^ (4 * G + 2 * L)) (q ^ (4 * G + 2 * L)) (q ^ (4 * G + 2 * L))) := by
  let T := (cw112ZFiberRetyping (K := K) q L G B hB seed z).targetConstituent
  have hsCyclic : s.1 ∈ (CTensor.cyclicTriple T).support := by
    exact (PartitionedTensor.mem_selectAddresses_support
      (CTensor.cyclicTriple T)
      (fun address ↦ Tensor.blockAddressTotalWeight
        (CTensor.antidiagonalWeight (cw112XYIsolatedZFiber L G B seed z).card) address =
          CTensor.antidiagonalDegree (cw112XYIsolatedZFiber L G B seed z).card)
      s.1).mp s.2 |>.1
  obtain ⟨i, j, k, haddress⟩ :=
    (CTensor.mem_cyclicTriple_support_iff T s.1).mp hsCyclic
  rw [CTensor.antidiagonal_constituent, ← haddress]
  exact cw112ZFiber_cyclicTriple_constituent_restricts_square
    (K := K) q L G B hB seed z i j k

/-- Degree-aware finite C-tensor extraction for one hashed shared-Z fiber.  Its leading degree is
the explicit antidiagonal degree `3*h^2`. -/
theorem cw112ZFiber_cyclicTensor_degeneratesAt_squareDirectSum
    {R : Type*} [Field R] [NeZero (2 : R)]
    (B : Finset R) (hB : ThreeAPFree (B : Set R))
    (seed : ProgressionHash.Seed R (Fin (cw112TypeDepth L G + 1)))
    (z : PositiveWord CW112ZBlock (cw112TypeDepth L G)) :
    PolynomialDegeneratesAt
      (CTensor.antidiagonalDegree (cw112XYIsolatedZFiber L G B seed z).card)
      (CTensor.cyclicTensor
        (cw112ZFiberRetyping (K := K) q L G B hB seed z).targetConstituent)
      (Tensor.indexedDirectSum
        (fun _ : (CTensor.antidiagonal
          (cw112ZFiberRetyping (K := K) q L G B hB seed z).targetConstituent).support ↦
            matrixMultiplication (K := K)
              (q ^ (4 * G + 2 * L)) (q ^ (4 * G + 2 * L))
              (q ^ (4 * G + 2 * L)))) := by
  let T := (cw112ZFiberRetyping (K := K) q L G B hB seed z).targetConstituent
  simpa using CTensor.cyclicTensor_degeneratesAt_matrixMultiplicationDirectSum T
    (q ^ (4 * G + 2 * L)) (q ^ (4 * G + 2 * L)) (q ^ (4 * G + 2 * L))
    (fun s ↦ cw112ZFiber_antidiagonalConstituent_restricts_square
      (K := K) q L G B hB seed z s)

/-- Finite C-tensor extraction for one hashed shared-Z fiber.  Its three-orientation cyclic
product polynomially degenerates to an indexed direct sum of square tensors of side
`q^(4G+2L)`.

Combined with `CTensor.half_sq_le_card_antidiagonal`, the index type contains at least
`⌊h/2⌋²` copies, where `h` is the number of constituents in the original Z fiber. -/
theorem cw112ZFiber_cyclicTensor_degenerates_squareDirectSum
    {R : Type*} [Field R] [NeZero (2 : R)]
    (B : Finset R) (hB : ThreeAPFree (B : Set R))
    (seed : ProgressionHash.Seed R (Fin (cw112TypeDepth L G + 1)))
    (z : PositiveWord CW112ZBlock (cw112TypeDepth L G)) :
    PolynomialDegenerates
      (CTensor.cyclicTensor
        (cw112ZFiberRetyping (K := K) q L G B hB seed z).targetConstituent)
      (Tensor.indexedDirectSum
        (fun _ : (CTensor.antidiagonal
          (cw112ZFiberRetyping (K := K) q L G B hB seed z).targetConstituent).support ↦
            matrixMultiplication (K := K)
              (q ^ (4 * G + 2 * L)) (q ^ (4 * G + 2 * L))
              (q ^ (4 * G + 2 * L)))) := by
  exact (cw112ZFiber_cyclicTensor_degeneratesAt_squareDirectSum
    (K := K) q L G B hB seed z).toPolynomialDegenerates

/-- Every hashed fixed-Z fiber restricts to a genuine C-tensor with exactly `fiber.card`
constituents.

Proof sketch: enumerate the finite fiber, inherit injectivity of its X/Y labels from the hashing
theorem, and apply the generic `FiberRetyping.restricts_partitioned` global-map construction. -/
theorem cw112ZFiber_restricts_cTensor
    {R : Type*} [Field R] [NeZero (2 : R)]
    (B : Finset R) (hB : ThreeAPFree (B : Set R))
    (seed : ProgressionHash.Seed R (Fin (cw112TypeDepth L G + 1)))
    (z : PositiveWord CW112ZBlock (cw112TypeDepth L G)) :
    Restricts
      ((cw112TypePartitionedPower K q L G).withSupport
        (cw112XYIsolatedZFiber L G B seed z)).realize
      (CTensor.partitioned
        (cw112ZFiberRetyping (K := K) q L G B hB seed z).targetConstituent).realize :=
  (cw112ZFiberRetyping (K := K) q L G B hB seed z).restricts_partitioned

end TensorPower

end AlgebraicComplexity.Examples
