/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinogradTotalWeightOuterSequence
import AlgebraicComplexity.Tensor.CompatibilityZeroing

set_option autoImplicit false

/-!
# The depth-four total-weight outer sequence datum at stride `38`

`CWTotalWeightLocalizedOuterSequenceData.ofCombinedPrimeFullBucketCount` is already generic in the
recursion `depth`, but it takes the assembled restriction

`Restricts (Tensor.power T (stride * r)) (Tensor.indexedDirectSum …)`

as an *input* field `hsource`.  For the `ω < 2.36999` endpoint the source is the literal
`T = CW₅⁸`, the stride is `38` and the depth is `4`, so that field carries the whole
`8 · 38 · r` versus `16 · m` chunk-alignment obligation.  Handing it to the constructor as an
unconstrained hypothesis is exactly what the anti-laundering rule of `DESIGN.md` forbids: it is a
restriction from an assembled source power to an assembled family, which is the conclusion the
interface exists to prove.

This module derives it instead.

## The alignment chain

`cwFlatChunkPower_restricts` composes four *proved* structural facts and nothing else:

1. `Tensor.Isomorphic.power_power_mul_comm` flattens `(CW_q^e)^s` to `CW_q^(e·s)`;
2. `cwPartitionedTensor_isomorphic` (used backwards) replaces `CW_q` by the realization of its
   canonical three-block partition;
3. `power_power_mul_comm` again re-chunks `e·s = 2^depth · m` letters into `m` chunks of
   `2^depth`;
4. `cwChunkPartitionedTensor_isomorphic_power` identifies one chunk with the native depth-`depth`
   chunk partition.

At `q = 5`, `e = 8`, `depth = 4` and `stride = 38` this is `8 · (38 · r) = 304 · r = 16 · (19 · r)`,
so a stride block is exactly `19 · r` chunks of `16` CW letters, i.e. the positive-power exponent
is `n r = 19 · r - 1`.  The arithmetic closes by `omega` for every `r > 0`; nothing about the
number `38` beyond `8 · 38 ≡ 0 (mod 16)` is used.

`cwCoarsePower_restricts` continues through the two remaining canonical partition theorems,
`Tensor.Restricts.power_partitionedCoarsen` (total-weight coarsening of the chunk alphabet) and
`Tensor.Restricts.power_partitionedPositivePower` (word-block partition of a canonical power).

## What the client still supplies

`CWTotalWeightOuterCoarseCleanup` bundles exactly the finite, non-tensor inputs of the outer
cleanup at the coarse chunk alphabet: three compatibility predicates — one per leg — with their
soundness statements.  These are predicates on `Finset`s of block addresses; no tensor relation
occurs in them.  This is the same discipline as
`MatrixMultiplication/WholeConstituentExtraction.lean`, whose constructors derive
`WholeConstituentLaserVolumeStage.source_restricts` from the same kind of ingredients.

The `X` pass is a *third* compatibility isolation rather than an assumed injectivity hypothesis.
`Tensor.Restricts.partitionedYZCompatibilityCleanup_to_indexedDirectSum` demands
`Set.InjOn (· .X) P.support`, and on the full coarse power that statement is false — distinct
coarse addresses routinely share an `X` word — so taking it as a field would have made the record
vacuous.  Instead `xSupport_injOn` *derives* it from `soundX` through
`compatibilityIsolatedSupport_hasUniqueLegFibers`, and the extra restriction step is
`Tensor.Restricts.partitionedCompatibilityIsolated` at pivot `.X`.  A client that has already
performed hashing takes `compatibleX label address := (address .X = label)`, whose soundness is
`rfl` and whose isolated support is exactly the set of addresses using an `X` word no other
ambient address uses.

The surviving index type is **not** an input: it is definitionally the triply compatibility-
isolated support, whose cardinality is precisely the `Finset` cardinality that the full-bucket
counting layer bounds from below.  Its coarse words are recovered by the proved
`cwTotalWeightCoarseWordOfAddress`, and
`positiveSupportWordBlockAddress_cwTotalWeightCoarseWordOfAddress` puts them in the exact shape the
sequence structure demands.

Genuinely quantitative inputs — the target growth `htargetGrowth`, the two field requirements
`hxRequirement` / `hvisibleRequirement`, and the full-bucket survivor count `hfinite` — are kept as
named hypotheses, unchanged from `ofCombinedPrimeFullBucketCount`.

## Honest gaps

Nothing in this file discharges the numeric floor `outerRetainedFloor = 811/125`.  The
constructors are parametric in `outerBase`; `exists_cwTotalWeightLocalizedOuterSequenceData_levelFourCPrime`
only *names* the `C′` instantiation, leaving the identification of
`2 ^ (38 · 811/125)` with `targetBase / combinedFieldBase …` as the sole remaining real input.

The residual hypotheses of the level-four constructor are, in full:

* the three compatibility predicates and their soundness statements (`CWTotalWeightOuterCoarseCleanup`),
  finite and non-tensor; `ownLabelCompatible` discharges the `X` one for a hashing client;
* `hcountPos` and `hfinite`, the full-bucket survivor count at level `r` — the *only* genuinely
  combinatorial obligation left, and by construction a lower bound on the cardinality of a named
  `Finset`;
* `htargetGrowth`, `hxRequirement`, `hvisibleRequirement`, the three exponential-rate inequalities;
* `hbase`, the numeric identification of the copy base.

Nothing else is assumed.  In particular the two combined-prime field lemmas
`CWTotalWeightLocalizedOuterSequenceData.xQuarter_le_card_combinedPrimeField` and
`…visibleRequirement_lt_card_combinedPrimeField` carry no `depth` argument at all, so — unlike the
*inner* prime field, which needed the `…AtDepth` restatements — they apply verbatim at depth four
and are already discharged inside `ofCombinedPrimeFullBucketCount`.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor

universe u v w

/-! ## The total-weight coarse chunk power -/

/-- The total-weight-coarsened depth-`depth` CW chunk partition, raised to the positive word power
with exponent `n` (that is, `n + 1` chunks). -/
noncomputable abbrev cwTotalWeightCoarsePower
    (K : Type u) [CommRing K] (q depth n : ℕ) :=
  ((cwChunkPartitionedTensor K q depth).coarsen
    (cwTotalWeightChunkCoarsening depth)).positivePower n

/-! ## The chunk-alignment chain -/

/-- Flat-power chunk alignment.  Whenever a stride block of `e · s` CW letters splits evenly into
`m` chunks of `2 ^ depth` letters, the honest asymptotic source `(CW_q^e)^s` restricts to the
`m`-th canonical power of the native chunk partition.

Every step is a proved isomorphism; nothing is assumed. -/
theorem cwFlatChunkPower_restricts
    (K : Type u) [CommRing K] (q depth e s m : ℕ)
    (halign : e * s = 2 ^ depth * m) :
    Restricts (Tensor.power (Tensor.power (coppersmithWinograd K q) e) s)
      (Tensor.power (cwChunkPartitionedTensor K q depth).realize m) := by
  have hflat : Restricts
      (Tensor.power (Tensor.power (coppersmithWinograd K q) e) s)
      (Tensor.power (coppersmithWinograd K q) (e * s)) :=
    (Isomorphic.power_power_mul_comm (coppersmithWinograd K q) e s).restricts
  have hpartition : Restricts
      (Tensor.power (coppersmithWinograd K q) (e * s))
      (Tensor.power (cwPartitionedTensor K q).realize (2 ^ depth * m)) := by
    rw [halign]
    exact ((cwPartitionedTensor_isomorphic K q).symm.power (2 ^ depth * m)).restricts
  have hrechunk : Restricts
      (Tensor.power (cwPartitionedTensor K q).realize (2 ^ depth * m))
      (Tensor.power
        (Tensor.power (cwPartitionedTensor K q).realize (2 ^ depth)) m) :=
    (Isomorphic.power_power_mul_comm
      (cwPartitionedTensor K q).realize (2 ^ depth) m).symm.restricts
  have hchunk : Restricts
      (Tensor.power
        (Tensor.power (cwPartitionedTensor K q).realize (2 ^ depth)) m)
      (Tensor.power (cwChunkPartitionedTensor K q depth).realize m) :=
    (cwChunkPartitionedTensor_isomorphic_power K q depth).restricts.power m
  exact hflat.trans (hpartition.trans (hrechunk.trans hchunk))

/-- The same alignment, carried through the total-weight coarsening and the canonical word-block
partition of a positive power. -/
theorem cwCoarsePower_restricts
    (K : Type u) [CommRing K] (q depth e s n : ℕ)
    (halign : e * s = 2 ^ depth * (n + 1)) :
    Restricts (Tensor.power (Tensor.power (coppersmithWinograd K q) e) s)
      (cwTotalWeightCoarsePower K q depth n).realize := by
  have hcoarsen : Restricts
      (Tensor.power (cwChunkPartitionedTensor K q depth).realize (n + 1))
      (Tensor.power
        ((cwChunkPartitionedTensor K q depth).coarsen
          (cwTotalWeightChunkCoarsening depth)).realize (n + 1)) :=
    Restricts.power_partitionedCoarsen (cwChunkPartitionedTensor K q depth)
      (cwTotalWeightChunkCoarsening depth) (n + 1)
  have hword : Restricts
      (Tensor.power
        ((cwChunkPartitionedTensor K q depth).coarsen
          (cwTotalWeightChunkCoarsening depth)).realize (n + 1))
      (cwTotalWeightCoarsePower K q depth n).realize :=
    Restricts.power_partitionedPositivePower
      ((cwChunkPartitionedTensor K q depth).coarsen
        (cwTotalWeightChunkCoarsening depth)) n
  exact (cwFlatChunkPower_restricts K q depth e s (n + 1) halign).trans
    (hcoarsen.trans hword)

/-! ## The finite outer cleanup certificate -/

/-- The canonical `X`-isolation relation: an address is compatible with its own `X` label.

Its `compatibilityIsolatedSupport` is exactly the set of ambient addresses whose `X` word no other
ambient address uses, i.e. the survivors of the paper's `X` zero-out after hashing.  This is the
default instantiation of `CWTotalWeightOuterCoarseCleanup.compatibleX`, and it witnesses that the
record is not vacuous. -/
def ownLabelCompatible {A : Leg → Type w} (pivot : Leg)
    (label : A pivot) (address : BlockAddress A) : Prop :=
  address pivot = label

theorem isCompatibilitySound_ownLabelCompatible
    {A : Leg → Type w} [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]
    (ambient : Finset (BlockAddress A)) (pivot : Leg) :
    IsCompatibilitySound ambient pivot (ownLabelCompatible pivot) :=
  fun _address _hmem ↦ rfl

/-- The finite, non-tensor inputs of the outer total-weight cleanup at the coarse chunk alphabet.

Every field is a statement about a `Finset` of block addresses.  In particular no restriction or
degeneration appears, so this record cannot launder the assembled-source obligation. -/
structure CWTotalWeightOuterCoarseCleanup
    (K : Type u) [CommRing K] (q depth : ℕ) (n : ℕ → ℕ) where
  /-- The `X`-compatibility predicate that performs the `X`-isolation pass at level `r`.  A hashing
  client takes `compatibleX label address := (address .X = label)` here, whose soundness is
  `rfl`; a marked full-bucket client uses its bucket relation. -/
  compatibleX : ∀ r, PositiveWord (CWCoarseDigit depth) (n r) →
    BlockAddress (fun _c : Leg ↦ PositiveWord (CWCoarseDigit depth) (n r)) → Prop
  /-- The `Y`-compatibility predicate used by the second cleanup pass at level `r`. -/
  compatibleY : ∀ r, PositiveWord (CWCoarseDigit depth) (n r) →
    BlockAddress (fun _c : Leg ↦ PositiveWord (CWCoarseDigit depth) (n r)) → Prop
  /-- The `Z`-compatibility predicate used by the third cleanup pass at level `r`. -/
  compatibleZ : ∀ r, PositiveWord (CWCoarseDigit depth) (n r) →
    BlockAddress (fun _c : Leg ↦ PositiveWord (CWCoarseDigit depth) (n r)) → Prop
  /-- Every ambient coarse address is `X`-compatible with the label it actually uses. -/
  soundX : ∀ r, IsCompatibilitySound
    (cwTotalWeightCoarsePower K q depth (n r)).support .X (compatibleX r)
  /-- Every `X`-isolated address is `Y`-compatible with the label it actually uses. -/
  soundY : ∀ r, IsCompatibilitySound
    (compatibilityIsolatedSupport
      (cwTotalWeightCoarsePower K q depth (n r)).support .X (compatibleX r))
    .Y (compatibleY r)
  /-- Every `X`- and `Y`-isolated address is `Z`-compatible with the label it actually uses. -/
  soundZ : ∀ r, IsCompatibilitySound
    (compatibilityIsolatedSupport
      (compatibilityIsolatedSupport
        (cwTotalWeightCoarsePower K q depth (n r)).support .X (compatibleX r))
      .Y (compatibleY r))
    .Z (compatibleZ r)

namespace CWTotalWeightOuterCoarseCleanup

variable {K : Type u} [CommRing K] {q depth : ℕ} {n : ℕ → ℕ}

/-- The ambient coarse support left after the `X`-isolation pass. -/
noncomputable def xSupport
    (data : CWTotalWeightOuterCoarseCleanup K q depth n) (r : ℕ) :
    Finset (BlockAddress (fun _c : Leg ↦ PositiveWord (CWCoarseDigit depth) (n r))) :=
  compatibilityIsolatedSupport
    (cwTotalWeightCoarsePower K q depth (n r)).support .X (data.compatibleX r)

theorem xSupport_subset
    (data : CWTotalWeightOuterCoarseCleanup K q depth n) (r : ℕ) :
    data.xSupport r ⊆ (cwTotalWeightCoarsePower K q depth (n r)).support :=
  compatibilityIsolatedSupport_subset _ _ _

/-- `X`-isolation really does isolate: the surviving `X` labels are pairwise distinct.  This is the
`hX` premise of `Tensor.Restricts.partitionedYZCompatibilityCleanup_to_indexedDirectSum`, derived
rather than assumed — assuming it on the *full* coarse power would be vacuous, since distinct
coarse addresses routinely share an `X` word. -/
theorem xSupport_injOn
    (data : CWTotalWeightOuterCoarseCleanup K q depth n) (r : ℕ) :
    Set.InjOn
      (fun address : BlockAddress
        (fun _c : Leg ↦ PositiveWord (CWCoarseDigit depth) (n r)) ↦ address .X)
      (data.xSupport r) := by
  classical
  have hunique := compatibilityIsolatedSupport_hasUniqueLegFibers
    (cwTotalWeightCoarsePower K q depth (n r)).support .X (data.compatibleX r)
    (data.soundX r)
  intro left hleft right hright hlabel
  exact (hunique.2 left (Finset.mem_coe.mp hleft) right
    (hunique.1 (Finset.mem_coe.mp hright)) hlabel.symm).symm

/-- The exact surviving coarse support after all three cleanup passes.  This `Finset` — not an
assumed index type — is what the full-bucket counting layer bounds from below. -/
noncomputable def survivors
    (data : CWTotalWeightOuterCoarseCleanup K q depth n) (r : ℕ) :
    Finset (BlockAddress (fun _c : Leg ↦ PositiveWord (CWCoarseDigit depth) (n r))) :=
  compatibilityIsolatedSupport
    (compatibilityIsolatedSupport (data.xSupport r) .Y (data.compatibleY r))
    .Z (data.compatibleZ r)

theorem survivors_subset
    (data : CWTotalWeightOuterCoarseCleanup K q depth n) (r : ℕ) :
    data.survivors r ⊆ (cwTotalWeightCoarsePower K q depth (n r)).support :=
  ((compatibilityIsolatedSupport_subset _ _ _).trans
    (compatibilityIsolatedSupport_subset _ _ _)).trans (data.xSupport_subset r)

/-- The supported coarse word underlying one survivor, recovered by the proved choice principle
`cwTotalWeightCoarseWordOfAddress`. -/
noncomputable def coarseWord
    (data : CWTotalWeightOuterCoarseCleanup K q depth n) (r : ℕ)
    (i : data.survivors r) :
    PositiveWord (CWTotalWeightCoarseSupport K q depth) (n r) :=
  cwTotalWeightCoarseWordOfAddress K q depth (n r) i.1
    (data.survivors_subset r i.2)

@[simp] theorem coarseWord_address
    (data : CWTotalWeightOuterCoarseCleanup K q depth n) (r : ℕ)
    (i : data.survivors r) :
    positiveSupportWordBlockAddress (CWTotalWeightCoarseSupport K q depth) (n r)
        (data.coarseWord r i) = i.1 :=
  positiveSupportWordBlockAddress_cwTotalWeightCoarseWordOfAddress
    K q depth (n r) i.1 (data.survivors_subset r i.2)

/-- **The derived source bridge.**  From the finite cleanup inputs and the chunk-alignment
identity alone, the honest asymptotic source `(CW_q^e)^(stride · r)` restricts to the direct sum of
the whole localized fine type-selected families attached to the surviving coarse words.

This is exactly the `source_restricts` field of `CWTotalWeightLocalizedOuterSequenceData`, proved
rather than assumed. -/
theorem source_restricts
    (data : CWTotalWeightOuterCoarseCleanup K q depth n)
    (e stride : ℕ)
    (fineType : ℕ → ∀ _c : Leg, PositiveWord CWBlock (2 ^ depth - 1) → ℕ)
    (halign : ∀ r, 0 < r → e * (stride * r) = 2 ^ depth * (n r + 1))
    (r : ℕ) (hr : 0 < r) :
    Restricts
      (Tensor.power
        (Tensor.power (coppersmithWinograd K q) e) (stride * r))
      (Tensor.indexedDirectSum (fun i : data.survivors r ↦
        (cwTotalWeightLocalizedFineTypes K q depth (n r)
          (positiveSupportWordBlockAddress
            (CWTotalWeightCoarseSupport K q depth) (n r) (data.coarseWord r i))
          (fineType r)).realize)) := by
  classical
  have hpower := cwCoarsePower_restricts K q depth e (stride * r) (n r)
    (halign r hr)
  have hxIsolate : Restricts
      (cwTotalWeightCoarsePower K q depth (n r)).realize
      ((cwTotalWeightCoarsePower K q depth (n r)).withSupport
        (data.xSupport r)).realize :=
    Tensor.Restricts.partitionedCompatibilityIsolated
      (cwTotalWeightCoarsePower K q depth (n r)) .X (data.compatibleX r)
      (data.soundX r)
  have hclean := Tensor.Restricts.partitionedYZCompatibilityCleanup_to_indexedDirectSum
    ((cwTotalWeightCoarsePower K q depth (n r)).withSupport (data.xSupport r))
    (data.xSupport_injOn r)
    (data.compatibleY r) (data.soundY r) (data.compatibleZ r) (data.soundZ r)
  have hlocal := cwTotalWeight_indexedCoarseConstituents_to_localizedFineTypes
    K q depth (n r) (I := data.survivors r) (fun i ↦ i.1)
    (fun i ↦ data.survivors_subset r i.2) (fineType r)
  simpa only [coarseWord_address] using
    hpower.trans (hxIsolate.trans (hclean.trans hlocal))

end CWTotalWeightOuterCoarseCleanup

/-! ## The outer sequence datum -/

namespace CWTotalWeightLocalizedOuterSequenceData

/-- Build a localized outer total-weight sequence for the honest power source `CW_q^e` at any
depth, from the finite coarse cleanup certificate plus the arithmetic full-bucket inputs of
`ofCombinedPrimeFullBucketCount`.

The `source_restricts` field is discharged internally by
`CWTotalWeightOuterCoarseCleanup.source_restricts`; the only remaining premises are the genuinely
quantitative ones. -/
noncomputable def ofChunkAlignedCoarseCleanup
    (K : Type u) [CommRing K] (q depth e stride : ℕ)
    (targetBase xFieldBase outerBase : ℝ)
    (hstride : 0 < stride) (htargetBase : 0 < targetBase)
    (hxFieldBase : 0 ≤ xFieldBase)
    {Part : Type} [Fintype Part]
    (ySourceProfile zSourceProfile : CWCoarseDigit depth → ℕ)
    (yJointExponentPerRepetition zJointExponentPerRepetition : ℝ)
    (hbase : outerBase = targetBase /
      combinedFieldBase xFieldBase
        (cwTotalWeightVisibleFeatureFieldBase
          ySourceProfile zSourceProfile
          yJointExponentPerRepetition zJointExponentPerRepetition))
    (characteristicFloor : ℕ)
    (targetLoss xFieldLoss : ℕ → ℝ)
    (targetCount xRequirement visibleRequirement : ℕ → ℕ)
    (n : ℕ → ℕ)
    (fineType : ℕ → Leg → PositiveWord CWBlock (2 ^ depth - 1) → ℕ)
    (cleanup : CWTotalWeightOuterCoarseCleanup K q depth n)
    (halign : ∀ r, 0 < r → e * (stride * r) = 2 ^ depth * (n r + 1))
    (htargetLoss : Growth.Subexponential targetLoss)
    (hxFieldLoss : Growth.Subexponential xFieldLoss)
    (htargetLossPos : ∀ r, 0 < r → 0 < targetLoss r)
    (hxFieldLossPos : ∀ r, 0 < r → 0 < xFieldLoss r)
    (hcountPos : ∀ r, 0 < r → 0 < (cleanup.survivors r).card)
    (htargetGrowth : ∀ r, 0 < r →
      targetBase ^ r ≤ targetLoss r * (targetCount r : ℝ))
    (hxRequirement : ∀ r, 0 < r →
      (xRequirement r : ℝ) ≤ xFieldLoss r * xFieldBase ^ r)
    (hvisibleRequirement : ∀ r, 0 < r →
      (visibleRequirement r : ℝ) ≤
        cwTotalWeightVisibleFeatureFieldLoss
            depth Part ySourceProfile zSourceProfile r *
          cwTotalWeightVisibleFeatureFieldBase
            ySourceProfile zSourceProfile
            yJointExponentPerRepetition zJointExponentPerRepetition ^ r)
    (hfinite : ∀ r, 0 < r →
      xRequirement r < PrimeFieldSizing.modulus characteristicFloor
          (max (xRequirement r) (visibleRequirement r)) →
      visibleRequirement r < PrimeFieldSizing.modulus characteristicFloor
          (max (xRequirement r) (visibleRequirement r)) →
      3 * targetCount r ≤
        8 * PrimeFieldSizing.modulus characteristicFloor
            (max (xRequirement r) (visibleRequirement r)) *
          (cleanup.survivors r).card) :
    CWTotalWeightLocalizedOuterSequenceData K q depth
      (Tensor.power (coppersmithWinograd K q) e) stride outerBase := by
  classical
  refine ofCombinedPrimeFullBucketCount K q depth
    (Tensor.power (coppersmithWinograd K q) e) stride targetBase xFieldBase
    outerBase hstride htargetBase hxFieldBase
    ySourceProfile zSourceProfile
    yJointExponentPerRepetition zJointExponentPerRepetition hbase
    characteristicFloor targetLoss xFieldLoss targetCount xRequirement
    visibleRequirement n fineType (fun r ↦ (cleanup.survivors r))
    (fun r ↦ cleanup.coarseWord r) htargetLoss hxFieldLoss htargetLossPos
    hxFieldLossPos ?_ ?_ htargetGrowth hxRequirement hvisibleRequirement ?_
  · intro r hr
    simpa only [Fintype.card_coe] using hcountPos r hr
  · exact cleanup.source_restricts e stride fineType halign
  · intro r hr
    simpa only [Fintype.card_coe] using hfinite r hr

/-- The four fields of the produced datum that the *inner* level-four constructor has to match
(`hn`, `hfine` and `hcoarseWordType` of
`exists_cwTotalWeightCanonicalInnerSequenceData_levelFour` all read them).

They are exactly the inputs, with the copy count the survivor cardinality; nothing is repackaged.
Stating them through an equation hypothesis avoids spelling the long application twice. -/
theorem ofChunkAlignedCoarseCleanup_spec
    (K : Type u) [CommRing K] (q depth e stride : ℕ)
    (targetBase xFieldBase outerBase : ℝ)
    (hstride : 0 < stride) (htargetBase : 0 < targetBase)
    (hxFieldBase : 0 ≤ xFieldBase)
    {Part : Type} [Fintype Part]
    (ySourceProfile zSourceProfile : CWCoarseDigit depth → ℕ)
    (yJointExponentPerRepetition zJointExponentPerRepetition : ℝ)
    (hbase : outerBase = targetBase /
      combinedFieldBase xFieldBase
        (cwTotalWeightVisibleFeatureFieldBase
          ySourceProfile zSourceProfile
          yJointExponentPerRepetition zJointExponentPerRepetition))
    (characteristicFloor : ℕ)
    (targetLoss xFieldLoss : ℕ → ℝ)
    (targetCount xRequirement visibleRequirement : ℕ → ℕ)
    (n : ℕ → ℕ)
    (fineType : ℕ → Leg → PositiveWord CWBlock (2 ^ depth - 1) → ℕ)
    (cleanup : CWTotalWeightOuterCoarseCleanup K q depth n)
    (halign : ∀ r, 0 < r → e * (stride * r) = 2 ^ depth * (n r + 1))
    (htargetLoss : Growth.Subexponential targetLoss)
    (hxFieldLoss : Growth.Subexponential xFieldLoss)
    (htargetLossPos : ∀ r, 0 < r → 0 < targetLoss r)
    (hxFieldLossPos : ∀ r, 0 < r → 0 < xFieldLoss r)
    (hcountPos : ∀ r, 0 < r → 0 < (cleanup.survivors r).card)
    (htargetGrowth : ∀ r, 0 < r →
      targetBase ^ r ≤ targetLoss r * (targetCount r : ℝ))
    (hxRequirement : ∀ r, 0 < r →
      (xRequirement r : ℝ) ≤ xFieldLoss r * xFieldBase ^ r)
    (hvisibleRequirement : ∀ r, 0 < r →
      (visibleRequirement r : ℝ) ≤
        cwTotalWeightVisibleFeatureFieldLoss
            depth Part ySourceProfile zSourceProfile r *
          cwTotalWeightVisibleFeatureFieldBase
            ySourceProfile zSourceProfile
            yJointExponentPerRepetition zJointExponentPerRepetition ^ r)
    (hfinite : ∀ r, 0 < r →
      xRequirement r < PrimeFieldSizing.modulus characteristicFloor
          (max (xRequirement r) (visibleRequirement r)) →
      visibleRequirement r < PrimeFieldSizing.modulus characteristicFloor
          (max (xRequirement r) (visibleRequirement r)) →
      3 * targetCount r ≤
        8 * PrimeFieldSizing.modulus characteristicFloor
            (max (xRequirement r) (visibleRequirement r)) *
          (cleanup.survivors r).card)
    {data : CWTotalWeightLocalizedOuterSequenceData K q depth
      (Tensor.power (coppersmithWinograd K q) e) stride outerBase}
    (hdata : data = ofChunkAlignedCoarseCleanup K q depth e stride targetBase
      xFieldBase outerBase hstride htargetBase hxFieldBase ySourceProfile
      zSourceProfile yJointExponentPerRepetition zJointExponentPerRepetition
      hbase characteristicFloor targetLoss xFieldLoss targetCount xRequirement
      visibleRequirement n fineType cleanup halign htargetLoss hxFieldLoss
      htargetLossPos hxFieldLossPos hcountPos htargetGrowth hxRequirement
      hvisibleRequirement hfinite) :
    data.n = n ∧ data.fineType = fineType ∧
      (∀ r, data.count r = (cleanup.survivors r).card) ∧
      HEq data.coarseWord cleanup.coarseWord := by
  subst hdata
  exact ⟨rfl, rfl, fun r ↦ Fintype.card_coe _, HEq.rfl⟩

/-! ### The level-four instantiation -/

/-- The positive-power exponent forced by `8 · 38 · r = 16 · (19 · r)`. -/
def levelFourOuterExponent (r : ℕ) : ℕ := 19 * r - 1

theorem levelFour_align (r : ℕ) (hr : 0 < r) :
    8 * (38 * r) = 2 ^ 4 * (levelFourOuterExponent r + 1) := by
  unfold levelFourOuterExponent
  omega

/-- The depth-four outer total-weight sequence datum for the endpoint source `CW₅⁸` at stride
`38`, with the copy base left parametric. -/
noncomputable def ofLevelFourCoarseCleanup
    (K : Type u) [CommRing K]
    (targetBase xFieldBase outerBase : ℝ)
    (htargetBase : 0 < targetBase) (hxFieldBase : 0 ≤ xFieldBase)
    {Part : Type} [Fintype Part]
    (ySourceProfile zSourceProfile : CWCoarseDigit 4 → ℕ)
    (yJointExponentPerRepetition zJointExponentPerRepetition : ℝ)
    (hbase : outerBase = targetBase /
      combinedFieldBase xFieldBase
        (cwTotalWeightVisibleFeatureFieldBase
          ySourceProfile zSourceProfile
          yJointExponentPerRepetition zJointExponentPerRepetition))
    (characteristicFloor : ℕ)
    (targetLoss xFieldLoss : ℕ → ℝ)
    (targetCount xRequirement visibleRequirement : ℕ → ℕ)
    (fineType : ℕ → Leg → PositiveWord CWBlock (2 ^ 4 - 1) → ℕ)
    (cleanup : CWTotalWeightOuterCoarseCleanup K 5 4 levelFourOuterExponent)
    (htargetLoss : Growth.Subexponential targetLoss)
    (hxFieldLoss : Growth.Subexponential xFieldLoss)
    (htargetLossPos : ∀ r, 0 < r → 0 < targetLoss r)
    (hxFieldLossPos : ∀ r, 0 < r → 0 < xFieldLoss r)
    (hcountPos : ∀ r, 0 < r → 0 < (cleanup.survivors r).card)
    (htargetGrowth : ∀ r, 0 < r →
      targetBase ^ r ≤ targetLoss r * (targetCount r : ℝ))
    (hxRequirement : ∀ r, 0 < r →
      (xRequirement r : ℝ) ≤ xFieldLoss r * xFieldBase ^ r)
    (hvisibleRequirement : ∀ r, 0 < r →
      (visibleRequirement r : ℝ) ≤
        cwTotalWeightVisibleFeatureFieldLoss
            4 Part ySourceProfile zSourceProfile r *
          cwTotalWeightVisibleFeatureFieldBase
            ySourceProfile zSourceProfile
            yJointExponentPerRepetition zJointExponentPerRepetition ^ r)
    (hfinite : ∀ r, 0 < r →
      xRequirement r < PrimeFieldSizing.modulus characteristicFloor
          (max (xRequirement r) (visibleRequirement r)) →
      visibleRequirement r < PrimeFieldSizing.modulus characteristicFloor
          (max (xRequirement r) (visibleRequirement r)) →
      3 * targetCount r ≤
        8 * PrimeFieldSizing.modulus characteristicFloor
            (max (xRequirement r) (visibleRequirement r)) *
          (cleanup.survivors r).card) :
    CWTotalWeightLocalizedOuterSequenceData K 5 4
      (Tensor.power (coppersmithWinograd K 5) 8) 38 outerBase :=
  ofChunkAlignedCoarseCleanup K 5 4 8 38 targetBase xFieldBase outerBase
    (by norm_num) htargetBase hxFieldBase
    ySourceProfile zSourceProfile
    yJointExponentPerRepetition zJointExponentPerRepetition hbase
    characteristicFloor targetLoss xFieldLoss targetCount xRequirement
    visibleRequirement levelFourOuterExponent fineType cleanup
    levelFour_align htargetLoss hxFieldLoss htargetLossPos hxFieldLossPos
    hcountPos htargetGrowth hxRequirement hvisibleRequirement hfinite

end CWTotalWeightLocalizedOuterSequenceData

/-- Existence form of the depth-four outer datum, matching the shape consumed by
`exists_subexponentialLaserVolumeSequence_levelFourInner`.

`outerRetained` is left free; the `C′` acceptance floor is `811 / 125`, and instantiating it here
is a purely numerical step for the aggregation side: the single remaining obligation is `hbase`,
i.e. that the chosen target and field bases really quotient to `2 ^ (38 · 811/125)`. -/
theorem exists_cwTotalWeightLocalizedOuterSequenceData_levelFour
    (K : Type u) [CommRing K]
    {outerRetained targetBase xFieldBase : ℝ}
    (htargetBase : 0 < targetBase) (hxFieldBase : 0 ≤ xFieldBase)
    {Part : Type} [Fintype Part]
    (ySourceProfile zSourceProfile : CWCoarseDigit 4 → ℕ)
    (yJointExponentPerRepetition zJointExponentPerRepetition : ℝ)
    (hbase : (2 : ℝ) ^ (((38 : ℕ) : ℝ) * outerRetained) = targetBase /
      CWTotalWeightLocalizedOuterSequenceData.combinedFieldBase xFieldBase
        (cwTotalWeightVisibleFeatureFieldBase
          ySourceProfile zSourceProfile
          yJointExponentPerRepetition zJointExponentPerRepetition))
    (characteristicFloor : ℕ)
    (targetLoss xFieldLoss : ℕ → ℝ)
    (targetCount xRequirement visibleRequirement : ℕ → ℕ)
    (fineType : ℕ → Leg → PositiveWord CWBlock (2 ^ 4 - 1) → ℕ)
    (cleanup : CWTotalWeightOuterCoarseCleanup K 5 4
      CWTotalWeightLocalizedOuterSequenceData.levelFourOuterExponent)
    (htargetLoss : Growth.Subexponential targetLoss)
    (hxFieldLoss : Growth.Subexponential xFieldLoss)
    (htargetLossPos : ∀ r, 0 < r → 0 < targetLoss r)
    (hxFieldLossPos : ∀ r, 0 < r → 0 < xFieldLoss r)
    (hcountPos : ∀ r, 0 < r → 0 < (cleanup.survivors r).card)
    (htargetGrowth : ∀ r, 0 < r →
      targetBase ^ r ≤ targetLoss r * (targetCount r : ℝ))
    (hxRequirement : ∀ r, 0 < r →
      (xRequirement r : ℝ) ≤ xFieldLoss r * xFieldBase ^ r)
    (hvisibleRequirement : ∀ r, 0 < r →
      (visibleRequirement r : ℝ) ≤
        cwTotalWeightVisibleFeatureFieldLoss
            4 Part ySourceProfile zSourceProfile r *
          cwTotalWeightVisibleFeatureFieldBase
            ySourceProfile zSourceProfile
            yJointExponentPerRepetition zJointExponentPerRepetition ^ r)
    (hfinite : ∀ r, 0 < r →
      xRequirement r < PrimeFieldSizing.modulus characteristicFloor
          (max (xRequirement r) (visibleRequirement r)) →
      visibleRequirement r < PrimeFieldSizing.modulus characteristicFloor
          (max (xRequirement r) (visibleRequirement r)) →
      3 * targetCount r ≤
        8 * PrimeFieldSizing.modulus characteristicFloor
            (max (xRequirement r) (visibleRequirement r)) *
          (cleanup.survivors r).card) :
    Nonempty (CWTotalWeightLocalizedOuterSequenceData.{u, u, 0} K 5 4
      (Tensor.power (coppersmithWinograd K 5) 8) 38
      ((2 : ℝ) ^ (((38 : ℕ) : ℝ) * outerRetained))) :=
  ⟨CWTotalWeightLocalizedOuterSequenceData.ofLevelFourCoarseCleanup K
    targetBase xFieldBase _ htargetBase hxFieldBase
    ySourceProfile zSourceProfile
    yJointExponentPerRepetition zJointExponentPerRepetition hbase
    characteristicFloor targetLoss xFieldLoss targetCount xRequirement
    visibleRequirement fineType cleanup htargetLoss hxFieldLoss
    htargetLossPos hxFieldLossPos hcountPos htargetGrowth hxRequirement
    hvisibleRequirement hfinite⟩

/-- The `C′` instantiation: `outerRetainedFloor = 811 / 125`.

The value is stated literally so that this module stays below the `MatrixMultiplication/` layer;
`MatrixMultiplication/TotalWeightAcceptanceFloors.outerRetainedFloor` is definitionally the same
real number. -/
theorem exists_cwTotalWeightLocalizedOuterSequenceData_levelFourCPrime
    (K : Type u) [CommRing K]
    {targetBase xFieldBase : ℝ}
    (htargetBase : 0 < targetBase) (hxFieldBase : 0 ≤ xFieldBase)
    {Part : Type} [Fintype Part]
    (ySourceProfile zSourceProfile : CWCoarseDigit 4 → ℕ)
    (yJointExponentPerRepetition zJointExponentPerRepetition : ℝ)
    (hbase : (2 : ℝ) ^ (((38 : ℕ) : ℝ) * (811 / 125)) = targetBase /
      CWTotalWeightLocalizedOuterSequenceData.combinedFieldBase xFieldBase
        (cwTotalWeightVisibleFeatureFieldBase
          ySourceProfile zSourceProfile
          yJointExponentPerRepetition zJointExponentPerRepetition))
    (characteristicFloor : ℕ)
    (targetLoss xFieldLoss : ℕ → ℝ)
    (targetCount xRequirement visibleRequirement : ℕ → ℕ)
    (fineType : ℕ → Leg → PositiveWord CWBlock (2 ^ 4 - 1) → ℕ)
    (cleanup : CWTotalWeightOuterCoarseCleanup K 5 4
      CWTotalWeightLocalizedOuterSequenceData.levelFourOuterExponent)
    (htargetLoss : Growth.Subexponential targetLoss)
    (hxFieldLoss : Growth.Subexponential xFieldLoss)
    (htargetLossPos : ∀ r, 0 < r → 0 < targetLoss r)
    (hxFieldLossPos : ∀ r, 0 < r → 0 < xFieldLoss r)
    (hcountPos : ∀ r, 0 < r → 0 < (cleanup.survivors r).card)
    (htargetGrowth : ∀ r, 0 < r →
      targetBase ^ r ≤ targetLoss r * (targetCount r : ℝ))
    (hxRequirement : ∀ r, 0 < r →
      (xRequirement r : ℝ) ≤ xFieldLoss r * xFieldBase ^ r)
    (hvisibleRequirement : ∀ r, 0 < r →
      (visibleRequirement r : ℝ) ≤
        cwTotalWeightVisibleFeatureFieldLoss
            4 Part ySourceProfile zSourceProfile r *
          cwTotalWeightVisibleFeatureFieldBase
            ySourceProfile zSourceProfile
            yJointExponentPerRepetition zJointExponentPerRepetition ^ r)
    (hfinite : ∀ r, 0 < r →
      xRequirement r < PrimeFieldSizing.modulus characteristicFloor
          (max (xRequirement r) (visibleRequirement r)) →
      visibleRequirement r < PrimeFieldSizing.modulus characteristicFloor
          (max (xRequirement r) (visibleRequirement r)) →
      3 * targetCount r ≤
        8 * PrimeFieldSizing.modulus characteristicFloor
            (max (xRequirement r) (visibleRequirement r)) *
          (cleanup.survivors r).card) :
    Nonempty (CWTotalWeightLocalizedOuterSequenceData.{u, u, 0} K 5 4
      (Tensor.power (coppersmithWinograd K 5) 8) 38
      ((2 : ℝ) ^ (((38 : ℕ) : ℝ) * (811 / 125)))) :=
  exists_cwTotalWeightLocalizedOuterSequenceData_levelFour K htargetBase
    hxFieldBase ySourceProfile zSourceProfile
    yJointExponentPerRepetition zJointExponentPerRepetition hbase
    characteristicFloor targetLoss xFieldLoss targetCount xRequirement
    visibleRequirement fineType cleanup htargetLoss hxFieldLoss
    htargetLossPos hxFieldLossPos hcountPos htargetGrowth hxRequirement
    hvisibleRequirement hfinite

end AlgebraicComplexity.Examples
