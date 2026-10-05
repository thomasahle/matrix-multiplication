import AlgebraicComplexity.Examples.CoppersmithWinogradTotalWeightInnerGrowthDepthFour
import AlgebraicComplexity.Examples.CoppersmithWinogradTotalWeightOuterDepthFour
import MatrixMultiplication.TotalQuotientExponentLevelTwoRecurrence
import MatrixMultiplication.TotalWeightLeanEndpointLevelFourEmbeddedInner

set_option autoImplicit false

/-!
# Superseded provisional total-weight acceptance assembly

This module records the provisional stage `S7` interface that was considered for the volume-only
`2.36999` campaign.  It composes the depth-four total-weight chain into a conditional theorem over
four named hypotheses.  The hypotheses are now known to be jointly inconsistent: the requested
outer copy base exceeds the cardinality of the complete depth-four `X`-label space.  The formal
capacity obstruction is stated in `MatrixMultiplication/TotalWeightAcceptanceNoGo.lean`.

The failure is a rate-allocation error, not a failure of the generic constructors below.  The
interface assigns the root/level-4/level-3 retained subtotal entirely to the number of coarse
survivors and then applies only one level-two fine extraction.  A correct construction must retain
the complete conditional fine family through the recursive stages.  Accordingly this file is a
negative regression artifact and must not be used as evidence for an unconditional endpoint.

Conditionally, everything structural — the outer sequence
datum, the depth-four inner growth datum, the `n r = 19 · r − 1` handshake, the base-two
`2 ^ (38 · outer) · 2 ^ (38 · inner)` composition, the hash-loss factors and the rectangular volume
floor — is *discharged inside*, not assumed.

## The theorem

`omega_lt_236999_of_named_inputs` reads

```
(h1 : SparseInnerInput K letters dims)      -- the sparse depth-four leaf and its inner rate
(h2 : OuterFloorInput 4)                    -- the outer copy-base identity
(h3 : OuterCountInput K 5 4 CWTotalWeightLocalizedOuterSequenceData.levelFourOuterExponent
        Part h2 (embeddedCoarseReference h1))
                                            -- compatibility predicates + outer count exports
(h4 : LevelTwoTableInput h1.innerRate)      -- the level-two table instantiation
⊢ omega K < TotalWeightAcceptanceFloors.acceptanceTarget
```

Each residual is *factorwise, finite or numeric*: a rational typed leaf on a finite sparse
alphabet, comparisons of real numbers, predicates on `Finset`s of block addresses, and a decidable
branch-floor certificate over generated tables.  No hypothesis is a restriction or a degeneration
of an assembled family, so the anti-laundering rule of `DESIGN.md` is respected: the one assembled
restriction in the whole chain, `CWTotalWeightLocalizedOuterSequenceData.source_restricts`, is
*derived* by `CWTotalWeightOuterCoarseCleanup.source_restricts` (stage `S6`), and the inner
degeneration is derived by the embedded marked-hashing theorem.

## Ownership of the four residuals

| input | owner | board item |
| --- | --- | --- |
| `h1.maximumEntropy` | codex-2.36x | the rigidity / relativized criterion, handoff §S4.7.1 |
| `h1.rate`, `h4.realizes` | codex-2.36x | the segmented occurrence-family rate transfer |
| `h1.volume_ge`, `h1.oneTypeLetters_ge` | S4 / here | the letter-count volume floor, below |
| `h2.base` | S1 (numeric prep) | `2 ^ (38 · 811/125) = targetBase / combinedFieldBase …` |
| `h3.*` | S6 | the residual table of `…TotalWeightOuterDepthFour.lean`'s header |
| `h4.certificate` | S1 emission | `total_weight_level_two_emission/HANDOFF.md` §4 |

## Alignment premises: which discharged

The depth-four endpoint of stage `S3` takes three index-alignment premises.  Two of them are
discharged here outright.

* `hn` (`outer.n r = growth.exponent r`).  Discharged.  The outer datum has
  `n r = levelFourOuterExponent r = 19 · r − 1` by construction, and the zero-safe growth datum has
  `exponent r = profileMass · r − 1`; `h1.mass_eq` (mass `19`, the exact chunk count of one
  stride block, `8 · 38 = 16 · 19`) makes the two literally the same natural number.  This is
  `embeddedGrowthDatum_exponent`.
* `hfine` (`outer.fineType r = cwTotalWeightFineMarginalType …`).  Discharged.  `fineType` is a free
  input of `ofLevelFourCoarseCleanup`, so `outerData` supplies exactly the family the inner
  constructor reads back; the premise is read off S6's `ofChunkAlignedCoarseCleanup_spec`
  (`outerData_spec`), see the elaboration note at the end of this header.
* `hcoarseWordType` genuinely remains, as `h3.coarseWord_type`: it says that every surviving coarse
  address at level `r` carries the same coarse quotient type as the growth datum's canonical
  representative.  That is a property of the *cleanup's survivor set*, not something the assembly
  can choose, and it is finite (an equality of multiplicity functions on a finite alphabet).

The S4 obstruction `no_levelFour_leaf_growthData_matches_outerExponent` — no leaf over the *full*
`6 ^ 16`-letter depth-four chunk support can have mass `19` — is avoided because `h1` carries a
*sparse* leaf together with its embedding, in the shape of
`Examples.cwEmbeddedChunkProfile`, and only the zero-extended profile is asked to have mass `19`.

## The volume floor in letter-count form

`h1` states the rectangular volume obligation as

`oneTypeLetters ≥ 295` and `5 ^ oneTypeLetters ≤ dimX · dimY · dimZ`,

that is: at least `295` of the `8 · 38 = 304` `CW₅` letters of a stride block carry a volume-`5`
block.  The endpoint's `rpow` interface is restored internally by `two_rpow_le_five_pow_295`, the
`C′` analogue of `Examples.two_rpow_le_five_pow_304`; the certified margin at
`volumeFloor = 15021/2500` is `295 · log 5 − 3 · 38 · volumeFloor · log 2 ≥ 7.7e-3`, and `294` is
provably too small.

Stating the obligation by letters rather than by whole one-type *chunks* matters.  S4's
`cwChunkLevelFour_volumeFloor_of_oneTypeCount` asks for multiplicity `19` on the single all-`cw011`
chunk letter; combined with mass `19` that forces a **point mass**, whose inner entropy rate is
zero, so the resulting `hWrate` is unsatisfiable.  In the letter form the constraint leaves `9` of
the `304` letters completely free *and* leaves the remaining `295` free among the three volume-`5`
blocks `cw011`, `cw101`, `cw110`, which is where the inner rate has to come from.

## The entropy → count bridge

Both halves of the "retained exponent ⇒ copy count" bridge are already committed and are consumed
*inside* the constructors this module composes:

* outer: `AlgebraicComplexity.copy_growth_of_fullBucket_hashCount`
  (`MatrixMultiplication/WholeConstituentFullBucketSequence.lean`), used at
  `Examples/CoppersmithWinogradTotalWeightOuterSequence.lean:99` inside
  `ofCombinedPrimeFullBucketCount`, so the outer residual is only the *finite* count export
  `h3.targetGrowth` / `h3.fullBucket`;
* inner: `CWTotalWeightInnerGrowthDataAtDepth.exists_subexponentialLoss_pow_le_embeddedBehrendCopies`,
  used inside `exists_cwTotalWeightEmbeddedCanonicalInnerSequenceData_ofDepth`.

What was missing between them is only the monotone adapter from the aggregation stack's output
shape (`floor ≤ familyExponent`) to the rate premise of the inner constructor; that is
`two_rpow_lt_of_floor_le` below, and it is what lets `h4` be the level-two *table* certificate
rather than a restatement of `hWrate`.

## Why the former non-vacuity argument is insufficient

The final section exhibits inhabitants of several fields separately:
`witnessOuterFloor` inhabits `OuterFloorInput 4`, `trivialCoarseCleanup` inhabits the cleanup field
of `OuterCountInput`, `levelTwoTableInput_of_certificate` packages a certified level-two table,
and `levelFour_letterBudget` proves the volume-letter arithmetic.  These facts do **not** establish
a joint inhabitant of `OuterCountInput`.  In particular, `xSupport_injOn` bounds its survivor count
by `33^(19r)`, whereas `outerData.copy_growth` would require exponential base
`2^(38 * 811/125)`.  The former is strictly smaller.  This is precisely the vacuity caught by the
capacity obstruction cited above.

## Elaboration note

`OuterFloorInput` and `OuterCountInput` are parametric in `q`, `depth` and `n`, and the outer
datum's four exposed fields are read through S6's `ofChunkAlignedCoarseCleanup_spec` rather than by
`rfl`.  Both are necessary, not stylistic: at the literal parameters `q = 5`, `depth = 4` a direct
`rfl`/structure elaboration drives `whnf` into the decidability instances of the `3 ^ 16`-letter
depth-four chunk alphabet and does not terminate within any reasonable `maxRecDepth`.
-/

namespace MatrixMultiplication.TotalWeightAcceptanceAssembly

open AlgebraicComplexity
open AlgebraicComplexity.Examples
open AlgebraicComplexity.Tensor
open MatrixMultiplication.TotalWeightAcceptanceFloors

universe u

/-! ## The rectangular volume floor, in letter-count form -/

set_option exponentiation.threshold 512 in
/-- **The `C′` volume floor as a letter count.**  `295` volume-`5` letters in a stride block clear
`2 ^ (3 · 38 · volumeFloor)`.

This is the `C′` analogue of `Examples.two_rpow_le_five_pow_304`, which is stated at the older and
larger floor `3755689/625000` and therefore needs `304` letters.  At
`volumeFloor = 15021/2500 = 6.0084` the requirement is `3 · 38 · 6.0084 = 684.9576` bits, i.e.
`684.9576 · log 2 ≤ 474.7765` against `295 · log 5 ≥ 474.7842`. -/
theorem two_rpow_le_five_pow_295 :
    (2 : ℝ) ^ (3 * (((38 : ℕ) : ℝ)) * volumeFloor) ≤ ((5 : ℕ) ^ (295 : ℕ) : ℝ) := by
  have hcast : ((38 : ℕ) : ℝ) = (38 : ℝ) := by norm_num
  rw [hcast]
  have hrpow : (2 : ℝ) ^ (3 * (38 : ℝ) * volumeFloor) =
      Real.exp (Real.log 2 * (3 * (38 : ℝ) * volumeFloor)) :=
    Real.rpow_def_of_pos (by norm_num) _
  have hpow : ((5 : ℕ) ^ (295 : ℕ) : ℝ) = Real.exp (((295 : ℕ) : ℝ) * Real.log 5) := by
    rw [← Real.log_pow, Real.exp_log (by positivity)]
    push_cast
    ring
  rw [hrpow, hpow]
  refine Real.exp_le_exp.mpr ?_
  have hlogTwo := Analysis.log_two_le_sharp
  have hlogFive := Analysis.log_five_ge_sharp
  simp only [volumeFloor]
  push_cast
  nlinarith [hlogTwo, hlogFive]

set_option exponentiation.threshold 512 in
/-- The floor is sharp in the letter count: `294` volume-`5` letters do **not** clear the `C′`
volume floor.  Recorded so that `295` is not mistaken for a convenient slack value. -/
theorem five_pow_294_lt_two_rpow :
    ((5 : ℕ) ^ (294 : ℕ) : ℝ) < (2 : ℝ) ^ (3 * (((38 : ℕ) : ℝ)) * volumeFloor) := by
  have hcast : ((38 : ℕ) : ℝ) = (38 : ℝ) := by norm_num
  rw [hcast]
  have hrpow : (2 : ℝ) ^ (3 * (38 : ℝ) * volumeFloor) =
      Real.exp (Real.log 2 * (3 * (38 : ℝ) * volumeFloor)) :=
    Real.rpow_def_of_pos (by norm_num) _
  have hpow : ((5 : ℕ) ^ (294 : ℕ) : ℝ) = Real.exp (((294 : ℕ) : ℝ) * Real.log 5) := by
    rw [← Real.log_pow, Real.exp_log (by positivity)]
    push_cast
    ring
  rw [hrpow, hpow]
  refine Real.exp_lt_exp.mpr ?_
  have hlogTwo := Analysis.log_two_ge_sharp
  have hlogFive := Analysis.log_five_le_sharp
  simp only [volumeFloor]
  push_cast
  nlinarith [hlogTwo, hlogFive]

/-! ## The monotone bridge from an aggregated retained floor to a rate premise -/

/-- **Entropy → count adapter.**  The aggregation stack (`RetainedExponentAggregation`,
`TotalQuotientExponentStageAggregation`) emits lower bounds of the form `floor ≤ familyExponent`.
The hashing constructors consume strict upper bounds of the form
`2 ^ (stride · rate) < target / (δ · competitor)`.  This is the only adapter between the two
shapes; the actual "exponent ⇒ number of surviving hash buckets" content lives in
`copy_growth_of_fullBucket_hashCount` (outer) and
`exists_subexponentialLoss_pow_le_embeddedBehrendCopies` (inner), both already committed and both
consumed inside the constructors composed below. -/
theorem two_rpow_lt_of_floor_le {stride floor rate quotient : ℝ}
    (hstride : 0 ≤ stride) (hfloor : floor ≤ rate)
    (hrate : (2 : ℝ) ^ (stride * rate) < quotient) :
    (2 : ℝ) ^ (stride * floor) < quotient :=
  lt_of_le_of_lt
    (Real.rpow_le_rpow_of_exponent_le (by norm_num)
      (mul_le_mul_of_nonneg_left hfloor hstride))
    hrate

/-! ## `h1`: the sparse depth-four inner leaf and its rate -/

/-- The zero-extension of a sparse leaf profile along its letter embedding has positive mass. -/
theorem embeddedProfileMass_pos {K : Type u} [CommRing K] {q depth : ℕ}
    {I : Type} [Fintype I] [Nonempty I] {C : Leg → Type}
    (leaf : RationalTypedLeaf I C)
    (letter : I ↪ (cwChunkPartitionedTensor K q depth).support) :
    0 < WordType.profileMass (cwEmbeddedChunkProfile leaf letter) := by
  rw [profileMass_cwEmbeddedChunkProfile]
  exact leaf.profile.mass_pos

/-- **Residual `h1`.**  A rational typed leaf carried by its own sparse alphabet, embedded in the
depth-four chunk support, together with the two genuinely open scalar facts about it: the
conditional maximum-entropy certificate for its zero-extended profile, and the inner rate it
realizes.

Nothing here is a tensor relation.  `mass_eq` is the chunk-alignment handshake `8 · 38 = 16 · 19`;
`volume_ge` is the letter-count volume floor; `rate` is the inner extraction rate *at the level-two
family exponent* `innerRate`, which `h4` then places above the `C′` inner acceptance floor. -/
structure SparseInnerInput (K : Type u) [CommRing K]
    (letters : Type) [Fintype letters] [Nonempty letters]
    (dims : Leg → Type) [∀ c, Fintype (dims c)] [∀ c, DecidableEq (dims c)] where
  /-- The sparse rational typed leaf. -/
  leaf : RationalTypedLeaf letters dims
  /-- Its letters, as an embedding into the depth-four chunk support. -/
  embed : letters ↪ (cwChunkPartitionedTensor K 5 4).support
  /-- The leaf carries the canonical chunk constituent dimensions. -/
  dimension_eq : ∀ i c,
    leaf.dimension i c = cwChunkConstituentDimension K 5 4 (embed i) c
  /-- Chunk-alignment handshake: a stride block of `8 · 38 = 304` `CW₅` letters is `19` chunks of
  `2 ^ 4 = 16`, so the profile mass must be `19`. -/
  mass_eq : leaf.profile.mass = 19
  /-- Number of volume-`5` `CW₅` letters in one stride block of the leaf. -/
  oneTypeLetters : ℕ
  /-- The `C′` volume floor in letter-count form. -/
  oneTypeLetters_ge : 295 ≤ oneTypeLetters
  /-- Each volume-`5` letter contributes a factor `5` to the rectangular volume. -/
  volume_ge : (5 : ℕ) ^ oneTypeLetters ≤
    leaf.dimensionProduct .X * leaf.dimensionProduct .Y * leaf.dimensionProduct .Z
  /-- Conditional maximum-entropy certificate for the zero-extended profile.  Open; the natural
  closures are the rigidity criterion and the alphabet-relativized predicate named in
  `tmp/S3-S4-S6-handoff.md` §S4.7.1. -/
  maximumEntropy : WordType.IsMaximumEntropyInMappedFiber (cwChunkCoordinate K 5 4)
    (WordType.normalizedProfileProbability (cwEmbeddedChunkProfile leaf embed)
      (embeddedProfileMass_pos leaf embed))
  /-- The competitor slack `δ` of the marked hashing argument. -/
  slack : ℝ
  one_lt_slack : 1 < slack
  /-- The inner retained rate this leaf realizes, per stride block. -/
  innerRate : ℝ
  /-- The realized rate, in the exact shape the embedded inner constructor consumes. -/
  rate : (2 : ℝ) ^ (((38 : ℕ) : ℝ) * innerRate) <
    cwTotalWeightInnerTargetBase K 5 4 (cwEmbeddedChunkProfile leaf embed) /
      (slack * cwTotalWeightInnerCompetitorBase K 5 4 (cwEmbeddedChunkProfile leaf embed)
        (cwChunkAmbientEntropyBase (cwEmbeddedChunkProfile leaf embed)))

namespace SparseInnerInput

variable {K : Type u} [CommRing K]
variable {letters : Type} [Fintype letters] [Nonempty letters]
variable {dims : Leg → Type} [∀ c, Fintype (dims c)] [∀ c, DecidableEq (dims c)]

/-- The zero-extended profile of the sparse leaf has mass exactly `19`. -/
theorem embeddedMass (data : SparseInnerInput K letters dims) :
    WordType.profileMass (cwEmbeddedChunkProfile data.leaf data.embed) = 19 := by
  rw [profileMass_cwEmbeddedChunkProfile]
  exact data.mass_eq

end SparseInnerInput

/-- The depth-four inner growth datum of a sparse leaf: S4's zero-safe maximum-entropy constructor
at the zero-extended profile.  Its `ambient_upper` field is proved, not assumed. -/
noncomputable def embeddedGrowthDatum {K : Type u} [CommRing K]
    {letters : Type} [Fintype letters] [Nonempty letters]
    {dims : Leg → Type} [∀ c, Fintype (dims c)] [∀ c, DecidableEq (dims c)]
    (data : SparseInnerInput K letters dims) :
    CWTotalWeightInnerGrowthDataAtDepth K 5 4
      (cwEmbeddedChunkProfile data.leaf data.embed)
      (cwChunkAmbientEntropyBase (cwEmbeddedChunkProfile data.leaf data.embed))
      (cwChunkAmbientTypeLoss (cwEmbeddedChunkProfile data.leaf data.embed)) :=
  cwChunkInnerGrowthDataOfMaximumEntropyZeroSafe K 5 4
    (cwEmbeddedChunkProfile data.leaf data.embed)
    (embeddedProfileMass_pos data.leaf data.embed) data.maximumEntropy

/-- **The `hn` handshake, discharged.**  The growth datum's positive-power exponent is exactly the
outer datum's `19 · r − 1`. -/
theorem embeddedGrowthDatum_exponent {K : Type u} [CommRing K]
    {letters : Type} [Fintype letters] [Nonempty letters]
    {dims : Leg → Type} [∀ c, Fintype (dims c)] [∀ c, DecidableEq (dims c)]
    (data : SparseInnerInput K letters dims) (r : ℕ) :
    (embeddedGrowthDatum data).exponent r =
      CWTotalWeightLocalizedOuterSequenceData.levelFourOuterExponent r := by
  simp only [embeddedGrowthDatum, cwChunkInnerGrowthDataOfMaximumEntropyZeroSafe_exponent,
    data.embeddedMass, CWTotalWeightLocalizedOuterSequenceData.levelFourOuterExponent]

/-- The growth datum's canonical coarse representative, transported to the outer index length. -/
noncomputable def embeddedCoarseReference {K : Type u} [CommRing K]
    {letters : Type} [Fintype letters] [Nonempty letters]
    {dims : Leg → Type} [∀ c, Fintype (dims c)] [∀ c, DecidableEq (dims c)]
    (data : SparseInnerInput K letters dims) (r : ℕ) :
    PositiveWord (CWTotalWeightCoarseSupport K 5 4)
      (CWTotalWeightLocalizedOuterSequenceData.levelFourOuterExponent r) :=
  positiveWordCast (embeddedGrowthDatum_exponent data r)
    ((embeddedGrowthDatum data).coarseWord r)

/-! ## `h2`: the outer copy-base identity -/

/-- **Residual `h2`.**  The purely numeric outer input: a target base, an `X`-field base, the two
visible-feature source profiles and their joint exponents, and the single identity saying that
their quotient *is* the `C′` outer copy base `2 ^ (38 · 811/125)`.

This is the "sole remaining real input" that S6's module documentation names, restated at the `C′`
floor of `MatrixMultiplication/TotalWeightAcceptanceFloors.lean`. -/
structure OuterFloorInput (depth : ℕ) where
  targetBase : ℝ
  xFieldBase : ℝ
  targetBase_pos : 0 < targetBase
  xFieldBase_nonneg : 0 ≤ xFieldBase
  ySourceProfile : CWCoarseDigit depth → ℕ
  zSourceProfile : CWCoarseDigit depth → ℕ
  yJointExponentPerRepetition : ℝ
  zJointExponentPerRepetition : ℝ
  /-- The `C′` outer copy base is the target base divided by the combined field base. -/
  base : (2 : ℝ) ^ (((38 : ℕ) : ℝ) * outerRetainedFloor) =
    targetBase /
      CWTotalWeightLocalizedOuterSequenceData.combinedFieldBase xFieldBase
        (cwTotalWeightVisibleFeatureFieldBase ySourceProfile zSourceProfile
          yJointExponentPerRepetition zJointExponentPerRepetition)

/-! ## `h3`: the compatibility cleanup and the outer count exports -/

/-- **Residual `h3`.**  Exactly S6's residual table: the three compatibility predicates with their
soundness statements (bundled as `CWTotalWeightOuterCoarseCleanup`, all statements about `Finset`s
of block addresses), the four exponential-rate exports, the full-bucket survivor count, and the one
alignment premise that is *not* dischargeable by choice, `coarseWord_type`.

No field mentions a restriction or a degeneration. -/
structure OuterCountInput (K : Type u) [CommRing K] (q depth : ℕ) (n : ℕ → ℕ)
    (Part : Type) [Fintype Part] (floor : OuterFloorInput depth)
    (coarseRef : ∀ r, PositiveWord (CWTotalWeightCoarseSupport K q depth) (n r)) where
  characteristicFloor : ℕ
  targetLoss : ℕ → ℝ
  xFieldLoss : ℕ → ℝ
  targetCount : ℕ → ℕ
  xRequirement : ℕ → ℕ
  visibleRequirement : ℕ → ℕ
  /-- The finite, non-tensor cleanup certificate of stage S6. -/
  cleanup : CWTotalWeightOuterCoarseCleanup K q depth n
  targetLoss_subexponential : Growth.Subexponential targetLoss
  xFieldLoss_subexponential : Growth.Subexponential xFieldLoss
  targetLoss_pos : ∀ r, 0 < r → 0 < targetLoss r
  xFieldLoss_pos : ∀ r, 0 < r → 0 < xFieldLoss r
  count_pos : ∀ r, 0 < r → 0 < (cleanup.survivors r).card
  /-- Target growth export: the certificate's target base is realized by the target count. -/
  targetGrowth : ∀ r, 0 < r →
    floor.targetBase ^ r ≤ targetLoss r * (targetCount r : ℝ)
  xRequirement_le : ∀ r, 0 < r →
    (xRequirement r : ℝ) ≤ xFieldLoss r * floor.xFieldBase ^ r
  visibleRequirement_le : ∀ r, 0 < r →
    (visibleRequirement r : ℝ) ≤
      cwTotalWeightVisibleFeatureFieldLoss depth Part
          floor.ySourceProfile floor.zSourceProfile r *
        cwTotalWeightVisibleFeatureFieldBase floor.ySourceProfile floor.zSourceProfile
          floor.yJointExponentPerRepetition floor.zJointExponentPerRepetition ^ r
  /-- The full-bucket survivor count: a lower bound on the cardinality of a named `Finset`. -/
  fullBucket : ∀ r, 0 < r →
    xRequirement r < PrimeFieldSizing.modulus characteristicFloor
        (max (xRequirement r) (visibleRequirement r)) →
    visibleRequirement r < PrimeFieldSizing.modulus characteristicFloor
        (max (xRequirement r) (visibleRequirement r)) →
    3 * targetCount r ≤
      8 * PrimeFieldSizing.modulus characteristicFloor
          (max (xRequirement r) (visibleRequirement r)) *
        (cleanup.survivors r).card
  /-- The surviving coarse addresses all carry the growth datum's coarse quotient type.  This is
  the one alignment premise the assembly cannot choose away. -/
  coarseWord_type : ∀ r (i : cleanup.survivors r),
    WordType.multiplicity
        (positiveWordEquiv (CWTotalWeightCoarseSupport K q depth) (n r)
          (cleanup.coarseWord r i)) =
      WordType.multiplicity
        (positiveWordEquiv (CWTotalWeightCoarseSupport K q depth) (n r)
          (coarseRef r))

/-! ## `h4`: the level-two table instantiation -/

/-- **Residual `h4`.**  The level-two branch-floor certificate over the emitted primary tables,
together with the numeric statement that the inner rate of `h1` realizes the certified level-two
bottleneck.

`certificate` is the obligation of `better_bound/total_weight_level_two_emission/HANDOFF.md` §4 and
is discharged by `branchFloorCertified_of_normalizedForms` from generated data.  `realizes` is the
transfer codex-2.36x's segmented occurrence family targets; it is a comparison of two real
numbers, never a claim about an assembled tensor. -/
structure LevelTwoTableInput (innerRate : ℝ) where
  tables : SimplifiedVolumeReconstruction.PrimaryTables
  massThree : Array ℕ
  certificate : TotalQuotientExponentLevelTwoRecurrence.BranchFloorCertified tables massThree
  realizes :
    TotalQuotientExponentLevelTwoRecurrence.retainedExponent tables massThree ≤ innerRate

/-- The `C′` inner acceptance floor is below the rate `h1` realizes. -/
theorem innerRetainedFloor_le_innerRate {innerRate : ℝ}
    (data : LevelTwoTableInput innerRate) : innerRetainedFloor ≤ innerRate := by
  refine le_trans ?_ data.realizes
  have h := TotalQuotientExponentLevelTwoRecurrence.innerRetainedFloor_le_retainedExponent
    data.tables data.massThree data.certificate
  simpa only [innerRetainedFloor] using h

/-! ## The assembled outer datum -/

/-- The depth-four outer total-weight sequence at stride `38`, built from `h2` and `h3` through
S6's `ofLevelFourCoarseCleanup`.  The `fineType` family is *chosen* to be the one the inner
constructor reads back, which is what discharges `hfine`. -/
noncomputable def outerData {K : Type u} [CommRing K]
    {letters : Type} [Fintype letters] [Nonempty letters]
    {dims : Leg → Type} [∀ c, Fintype (dims c)] [∀ c, DecidableEq (dims c)]
    {Part : Type} [Fintype Part]
    (h1 : SparseInnerInput K letters dims) (h2 : OuterFloorInput 4)
    (h3 : OuterCountInput K 5 4 CWTotalWeightLocalizedOuterSequenceData.levelFourOuterExponent
      Part h2 (embeddedCoarseReference h1)) :
    CWTotalWeightLocalizedOuterSequenceData K 5 4
      (Tensor.power (coppersmithWinograd K 5) 8) 38
      ((2 : ℝ) ^ (((38 : ℕ) : ℝ) * outerRetainedFloor)) :=
  CWTotalWeightLocalizedOuterSequenceData.ofLevelFourCoarseCleanup K
    h2.targetBase h2.xFieldBase _ h2.targetBase_pos h2.xFieldBase_nonneg
    h2.ySourceProfile h2.zSourceProfile
    h2.yJointExponentPerRepetition h2.zJointExponentPerRepetition h2.base
    h3.characteristicFloor h3.targetLoss h3.xFieldLoss h3.targetCount
    h3.xRequirement h3.visibleRequirement
    (fun r ↦ cwTotalWeightFineMarginalType K 5 4
      (WordType.proportionalCounts (cwEmbeddedChunkProfile h1.leaf h1.embed) r))
    h3.cleanup h3.targetLoss_subexponential h3.xFieldLoss_subexponential
    h3.targetLoss_pos h3.xFieldLoss_pos h3.count_pos h3.targetGrowth
    h3.xRequirement_le h3.visibleRequirement_le h3.fullBucket

/-- The four fields of `outerData` that the inner constructor reads back, obtained from S6's
`ofChunkAlignedCoarseCleanup_spec` rather than by unfolding the constructor.

Going through the exported specification matters: the constructor is a tactic-mode definition, and
at the *literal* parameters `q = 5`, `depth = 4` a direct `rfl` sends `whnf` into the
`3 ^ 16`-letter chunk alphabet's decidability instances.  S6 proved the same equations once,
generically, which is exactly what this projection reuses. -/
theorem outerData_spec {K : Type u} [CommRing K]
    {letters : Type} [Fintype letters] [Nonempty letters]
    {dims : Leg → Type} [∀ c, Fintype (dims c)] [∀ c, DecidableEq (dims c)]
    {Part : Type} [Fintype Part]
    (h1 : SparseInnerInput K letters dims) (h2 : OuterFloorInput 4)
    (h3 : OuterCountInput K 5 4 CWTotalWeightLocalizedOuterSequenceData.levelFourOuterExponent
      Part h2 (embeddedCoarseReference h1)) :
    (outerData h1 h2 h3).n =
        CWTotalWeightLocalizedOuterSequenceData.levelFourOuterExponent ∧
      (outerData h1 h2 h3).fineType =
        (fun r ↦ cwTotalWeightFineMarginalType K 5 4
          (WordType.proportionalCounts (cwEmbeddedChunkProfile h1.leaf h1.embed) r)) ∧
      (∀ r, (outerData h1 h2 h3).count r = (h3.cleanup.survivors r).card) ∧
      HEq (outerData h1 h2 h3).coarseWord h3.cleanup.coarseWord :=
  CWTotalWeightLocalizedOuterSequenceData.ofChunkAlignedCoarseCleanup_spec K 5 4 8 38
    h2.targetBase h2.xFieldBase _ (by norm_num) h2.targetBase_pos h2.xFieldBase_nonneg
    h2.ySourceProfile h2.zSourceProfile h2.yJointExponentPerRepetition
    h2.zJointExponentPerRepetition h2.base h3.characteristicFloor h3.targetLoss h3.xFieldLoss
    h3.targetCount h3.xRequirement h3.visibleRequirement
    CWTotalWeightLocalizedOuterSequenceData.levelFourOuterExponent
    (fun r ↦ cwTotalWeightFineMarginalType K 5 4
      (WordType.proportionalCounts (cwEmbeddedChunkProfile h1.leaf h1.embed) r))
    h3.cleanup CWTotalWeightLocalizedOuterSequenceData.levelFour_align
    h3.targetLoss_subexponential h3.xFieldLoss_subexponential h3.targetLoss_pos
    h3.xFieldLoss_pos h3.count_pos h3.targetGrowth h3.xRequirement_le h3.visibleRequirement_le
    h3.fullBucket rfl

/-! ## The superseded conditional assembly theorem -/

set_option exponentiation.threshold 512 in
/-- **Superseded stage S7: a conditional theorem over jointly inconsistent residual inputs.**

Everything structural is discharged inside:

* the depth-four outer sequence datum, including the derived `source_restricts` chain
  `8 · (38 · r) = 16 · (19 · r)` (S6);
* the depth-four inner growth datum with `ambient_upper` proved (S4);
* the embedded marked-hashing inner extraction and its Behrend copy count (S3 + codex-2.36x's
  embedded route);
* the `hn` and `hfine` alignment premises;
* the base-two composition `2 ^ (38 · outer) · 2 ^ (38 · inner) = 2 ^ (38 · 8.22)` and the
  rectangular volume base, through
  `CanonicalInnerSequenceData.toSubexponentialLaserVolumeSequence_addRetained` and the
  `LaserVolumeMonotone` weakening used by
  `omega_lt_236999_of_levelFourEmbeddedCanonicalInner`;
* the volume floor, from the letter count of `h1`.

Only the four residuals remain syntactically, but the first three cannot be inhabited together;
see `TotalWeightAcceptanceNoGo`.  This theorem is retained as a regression test for the generic
composition plumbing, not as an endpoint. -/
theorem omega_lt_236999_of_named_inputs
    (K : Type u) [Field K]
    {letters : Type} [Fintype letters] [Nonempty letters]
    {dims : Leg → Type} [∀ c, Fintype (dims c)] [∀ c, DecidableEq (dims c)]
    {Part : Type} [Fintype Part]
    (h1 : SparseInnerInput K letters dims)
    (h2 : OuterFloorInput 4)
    (h3 : OuterCountInput K 5 4 CWTotalWeightLocalizedOuterSequenceData.levelFourOuterExponent
      Part h2 (embeddedCoarseReference h1))
    (h4 : LevelTwoTableInput h1.innerRate) :
    omega K < acceptanceTarget := by
  have hWrate : (2 : ℝ) ^ (((38 : ℕ) : ℝ) * innerRetainedFloor) <
      cwTotalWeightInnerTargetBase K 5 4 (cwEmbeddedChunkProfile h1.leaf h1.embed) /
        (h1.slack * cwTotalWeightInnerCompetitorBase K 5 4
          (cwEmbeddedChunkProfile h1.leaf h1.embed)
          (cwChunkAmbientEntropyBase (cwEmbeddedChunkProfile h1.leaf h1.embed))) :=
    two_rpow_lt_of_floor_le (by positivity) (innerRetainedFloor_le_innerRate h4) h1.rate
  have hvolume : (2 : ℝ) ^ (3 * (((38 : ℕ) : ℝ)) * volumeFloor) ≤
      ((h1.leaf.dimensionProduct .X * h1.leaf.dimensionProduct .Y *
        h1.leaf.dimensionProduct .Z : ℕ) : ℝ) := by
    refine two_rpow_le_five_pow_295.trans ?_
    have hstep : (5 : ℕ) ^ (295 : ℕ) ≤ (5 : ℕ) ^ h1.oneTypeLetters :=
      Nat.pow_le_pow_right (by norm_num) h1.oneTypeLetters_ge
    exact_mod_cast hstep.trans h1.volume_ge
  exact TotalWeightLeanEndpoint.omega_lt_236999_of_levelFourEmbeddedCanonicalInner
    K (outerData h1 h2 h3)
    h1.leaf h1.embed h1.dimension_eq (embeddedGrowthDatum h1)
    (fun r ↦ (embeddedGrowthDatum_exponent h1 r).symm)
    (fun r ↦ congrFun (outerData_spec h1 h2 h3).2.1 r)
    (fun r i ↦ h3.coarseWord_type r i)
    h1.one_lt_slack hWrate hvolume

/-! ## Separate field inhabitants (not joint non-vacuity) -/

/-- The `295` volume-`5` letters demanded by the `C′` volume floor fit inside the `8 · 38 = 304`
`CW₅` letters of a mass-`19` stride block, with `9` letters left completely free.

This single arithmetic fact is what makes `SparseInnerInput` satisfiable at all: it is the exact
place where the S4 obstruction (`19` whole all-`cw011` chunks, hence a point mass, hence zero inner
entropy) is avoided. -/
theorem levelFour_letterBudget : 295 ≤ 19 * 2 ^ 4 ∧ 19 * 2 ^ 4 = 8 * 38 := by
  constructor <;> norm_num

/-- The depth-four chunk support is inhabited, so a sparse letter embedding exists. -/
theorem nonempty_cwChunkSupport (K : Type u) [CommRing K] :
    Nonempty ((cwChunkPartitionedTensor K 5 4).support) :=
  ⟨cwChunkSupportWitness K 5 4⟩

/-- The `X`/`Y`/`Z` compatibility field of `OuterCountInput` is inhabited: the own-label relation
is sound on every ambient support.  S6 found that the naive `Set.InjOn` form of this field is
*false* on the full coarse power, which is exactly the vacuity trap this witness rules out. -/
noncomputable def trivialCoarseCleanup (K : Type u) [CommRing K] (q depth : ℕ) (n : ℕ → ℕ) :
    CWTotalWeightOuterCoarseCleanup K q depth n := by
  classical
  refine
    { compatibleX := fun r ↦ ownLabelCompatible
        (A := fun _c : Leg ↦ PositiveWord (CWCoarseDigit depth) (n r)) .X
      compatibleY := fun r ↦ ownLabelCompatible
        (A := fun _c : Leg ↦ PositiveWord (CWCoarseDigit depth) (n r)) .Y
      compatibleZ := fun r ↦ ownLabelCompatible
        (A := fun _c : Leg ↦ PositiveWord (CWCoarseDigit depth) (n r)) .Z
      soundX := ?_
      soundY := ?_
      soundZ := ?_ }
  · exact fun _r ↦ isCompatibilitySound_ownLabelCompatible _ .X
  · exact fun _r ↦ isCompatibilitySound_ownLabelCompatible _ .Y
  · exact fun _r ↦ isCompatibilitySound_ownLabelCompatible _ .Z

/-- `OuterFloorInput` is inhabited in isolation: the copy-base identity is a *definition* of the
target base once the field bases are fixed.  This does not imply that the same target base can
satisfy `h3.targetGrowth` and the finite survivor capacity simultaneously. -/
noncomputable def witnessOuterFloor : OuterFloorInput 4 where
  targetBase := (2 : ℝ) ^ (((38 : ℕ) : ℝ) * outerRetainedFloor) *
    CWTotalWeightLocalizedOuterSequenceData.combinedFieldBase 0
      (cwTotalWeightVisibleFeatureFieldBase (depth := 4) (fun _ ↦ 0) (fun _ ↦ 0) 0 0)
  xFieldBase := 0
  targetBase_pos :=
    mul_pos (Real.rpow_pos_of_pos (by norm_num) _)
      (CWTotalWeightLocalizedOuterSequenceData.combinedFieldBase_pos _ _)
  xFieldBase_nonneg := le_rfl
  ySourceProfile := fun _ ↦ 0
  zSourceProfile := fun _ ↦ 0
  yJointExponentPerRepetition := 0
  zJointExponentPerRepetition := 0
  base := by
    rw [eq_div_iff
      (CWTotalWeightLocalizedOuterSequenceData.combinedFieldBase_pos 0
        (cwTotalWeightVisibleFeatureFieldBase (depth := 4) (fun _ ↦ 0) (fun _ ↦ 0) 0 0)).ne']

/-- `LevelTwoTableInput` is inhabited by any certified table pair, at its own exact bottleneck. -/
def levelTwoTableInput_of_certificate
    (tables : SimplifiedVolumeReconstruction.PrimaryTables) (massThree : Array ℕ)
    (certificate :
      TotalQuotientExponentLevelTwoRecurrence.BranchFloorCertified tables massThree) :
    LevelTwoTableInput
      (TotalQuotientExponentLevelTwoRecurrence.retainedExponent tables massThree) where
  tables := tables
  massThree := massThree
  certificate := certificate
  realizes := le_rfl

end MatrixMultiplication.TotalWeightAcceptanceAssembly
