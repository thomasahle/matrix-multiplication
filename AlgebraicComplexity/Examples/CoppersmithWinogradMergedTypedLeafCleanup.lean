/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinogradTotalWeightQuotientCompatibility
import AlgebraicComplexity.MatrixMultiplication.MergedRationalTypedLeaf

set_option autoImplicit false

/-!
# The total-weight cleanup at a merged leaf

`Examples/CoppersmithWinogradTotalWeightQuotientCompatibility.lean` ends with the committed
end-to-end bridge
`cwTotalWeightFeatureYZCompatibilityCleanup_to_matrixMultiplicationDirectSum_of_shapeType`
(`:643`, conclusion `:711-714`).  Its leaf premise is

```
hdimension : ∀ support c, leaf.dimension support c = cwChunkConstituentDimension K q depth support c
```

— the *fine* chunk dimension table, a pure product of per-letter `q`-powers.  Experiment **E2**
identified that premise as the binding obstruction of the whole volume side: at the certificate's
own letter census a pure-`q` leaf carries `637.586` bits per `38`-word stride block against the
`683.852` the `ω < 2.36999` milestone needs, a shortfall of `46.414` bits per block that no amount
of counting work can recover (`better_bound/r4_scoping/E2_LATTICE.md` §1, §4).

## What this module does, and what it does not touch

**No committed file is modified.**  The committed cleanup stays exactly as it is; this module
states the generalization beside it, in a new module that consumes it.

The relaxation is possible with no new tensor algebra because `hdimension` is used in exactly one
place downstream — `Examples.cwChunk_constituent_restricts_of_leaf_dimension_eq`, which turns it
into the per-letter degeneration

```
hconstituent : ∀ s, Restricts (P.constituent s)
  ⟨leaf.dimension s .X, leaf.dimension s .Y, leaf.dimension s .Z⟩
```

— and the generic coarse-to-fine bridge
`RationalTypedLeaf.coarsenedPositivePower_constituent_matrixMultiplication_of_mappedType` already
takes `hconstituent` itself.  So the cleanup's real premise is the per-letter degeneration, and
`hdimension` is one way of discharging it.  Every theorem below simply hands that premise through:

* `cwTotalWeight_coarsenedConstituent_matrixMultiplication_of_shapeType_of_degeneration`
  — the constituent bridge with `hconstituent` in place of `hdimension`;
* `cwTotalWeightFeatureYZCompatibilityCleanup_to_matrixMultiplicationDirectSum_of_degeneration`
  — the end-to-end cleanup with the same substitution.  The committed theorem is its special case,
  recovered by `cwChunk_constituent_restricts_of_leaf_dimension_eq`, and
  `cwChunk_constituentDegeneration_of_dimension_eq` records that identification;
* `cwTotalWeightFeatureYZCompatibilityCleanup_to_matrixMultiplicationDirectSum_of_mergedLeaf`
  — the same statement for a `MergedRationalTypedLeaf`, whose designated leg carries a merged
  zero-coordinate class dimension;
* `cwTotalWeightMergedCleanupStage` — the output as a `WholeConstituentLaserVolumeStage`, the form
  `SimplifiedSequencePackaging.RetainedExtractionValid.of_stageFamily` consumes;
* `cwTotalWeightFeatureYZCompatibilityCleanup_to_matrixMultiplicationDirectSum_of_zeroClasses`
  — the merged `N` made visible: the `Y` leg of every retained leaf is
  `(residual.dimensionProduct .Y * mergedFactorProduct) ^ k`, with the other two legs unchanged.

## Leg convention

Statements are in Lean's `(X, Y, Z)` matrix-shape leg order and the merged dimension is on `Y`,
matching `ZeroCoordinateMerge.mergeY` and the committed one-slice fusion.  The certificate's volume
coordinate `c` is the leg `(c + 2) % 3` (`OBLIGATIONS.md` §9.1/§9.8); the rotation is applied by the
certificate client `MatrixMultiplication/MergedLeafBudget.lean`, not here.

## The honest gap, precisely

Relaxing the premise does **not** prove it.  `hmerged` — the per-letter degeneration at merged
dimensions — is a named hypothesis of every theorem below, and it is not available from the chunk
dimension table by construction: `cwChunkConstituentDimension` is a product over the chunk's
individual `CW₅` letters and knows nothing about a zero class.  It must come from the
zero-coordinate one-slice fusion
(`UniformPowerFusion.restricts_matrixMultiplication_mergedDimension` composed with
`cwSelectedExactInterfaceTerm_zeroZ_restricts_mergedOneSlice_of_labelMaps`), which in turn still
rests on the shared-`Z` map coherence recorded in `OBLIGATIONS.md` §9.9 and owned by codex-2.36x's
zero-dimension tranche.  What this module removes is the *interface* obstruction — that the
committed cleanup could not accept a merged leaf at all — not the semantic one.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor MoreAsymmetryCompatibility

universe u v

/-! ## The constituent bridge with the per-letter degeneration as the premise -/

/-- **The alpha-facing constituent bridge, at an arbitrary per-letter degeneration.**

This is `cwTotalWeight_coarsenedPositivePower_constituent_matrixMultiplication_of_shapeType` with
its `hdimension` premise replaced by the weaker `hconstituent` that the committed proof actually
consumes.  Nothing else changes: the joint-type recovery is still
`cwTotalWeight_jointType_eq_of_shapeType`, and the coarse-to-fine step is still the committed
`RationalTypedLeaf.coarsenedPositivePower_constituent_matrixMultiplication_of_mappedType`. -/
theorem cwTotalWeight_coarsenedConstituent_matrixMultiplication_of_shapeType_of_degeneration
    (K : Type u) [CommRing K] (q depth : ℕ)
    {C : Leg → Type v} [∀ c, Fintype (C c)] [∀ c, DecidableEq (C c)]
    (leaf : RationalTypedLeaf (cwChunkPartitionedTensor K q depth).support C)
    (hconstituent : ∀ support : (cwChunkPartitionedTensor K q depth).support,
      Restricts ((cwChunkPartitionedTensor K q depth).constituent support.1)
        (matrixMultiplication (K := K)
          (leaf.dimension support .X) (leaf.dimension support .Y)
          (leaf.dimension support .Z)))
    {r k : ℕ}
    (coarseWord : PositiveWord (CWTotalWeightCoarseSupport K q depth) r)
    (hlegal : WordType.proportionalCounts leaf.profile.count k ∈
      WordType.types (cwChunkPartitionedTensor K q depth).support (r + 1))
    (hshape : WordType.mappedType (cwTotalWeightSupportedShape K q depth)
        (WordType.multiplicity
          (positiveWordEquiv (CWTotalWeightCoarseSupport K q depth) r coarseWord)) =
      WordType.mappedType (cwTotalWeightSupportedShape K q depth)
        (WordType.mappedType
          ((cwChunkPartitionedTensor K q depth).coarsenSupportMap
            (cwTotalWeightChunkCoarsening depth))
          (WordType.proportionalCounts leaf.profile.count k))) :
    Restricts
      (((cwChunkPartitionedTensor K q depth).coarsenedPositivePower
          (cwTotalWeightChunkCoarsening depth) r).constituent
        (positiveSupportWordBlockAddress
          (CWTotalWeightCoarseSupport K q depth) r coarseWord))
      (matrixMultiplication (K := K)
        (leaf.dimensionProduct .X ^ k)
        (leaf.dimensionProduct .Y ^ k)
        (leaf.dimensionProduct .Z ^ k)) := by
  letI : Nonempty (cwChunkPartitionedTensor K q depth).support :=
    ⟨cwChunkSupportWitness K q depth⟩
  apply RationalTypedLeaf.coarsenedPositivePower_constituent_matrixMultiplication_of_mappedType
    (cwChunkPartitionedTensor K q depth)
      (cwTotalWeightChunkCoarsening depth) leaf hconstituent coarseWord hlegal
  rw [mem_positiveTypeClass]
  exact cwTotalWeight_jointType_eq_of_shapeType K q depth _ _ hshape

/-- The committed fine premise really is a special case: a leaf whose dimension table is the
canonical chunk table satisfies the per-letter degeneration.  This is the identification that makes
the generalized cleanup below strictly weaker in hypotheses than the committed one. -/
theorem cwChunk_constituentDegeneration_of_dimension_eq
    (K : Type u) [CommRing K] (q depth : ℕ)
    {C : Leg → Type v} [∀ c, Fintype (C c)] [∀ c, DecidableEq (C c)]
    (leaf : RationalTypedLeaf (cwChunkPartitionedTensor K q depth).support C)
    (hdimension : ∀ support c,
      leaf.dimension support c = cwChunkConstituentDimension K q depth support c) :
    ∀ support : (cwChunkPartitionedTensor K q depth).support,
      Restricts ((cwChunkPartitionedTensor K q depth).constituent support.1)
        (matrixMultiplication (K := K)
          (leaf.dimension support .X) (leaf.dimension support .Y)
          (leaf.dimension support .Z)) :=
  cwChunk_constituent_restricts_of_leaf_dimension_eq K q depth leaf hdimension

/-! ## The end-to-end cleanup at an arbitrary per-letter degeneration -/

/-- **The relaxed end-to-end bridge — this is C1b item 9.**

Verbatim the committed
`cwTotalWeightFeatureYZCompatibilityCleanup_to_matrixMultiplicationDirectSum_of_shapeType`, except
that the leaf premise is the per-letter degeneration `hconstituent` rather than the fine dimension
identity `hdimension`.  Compatibility counting, the two isolation passes and the shape-type
rigidity are untouched and are cited from the committed module.

A leaf whose designated leg carries a merged zero-coordinate class dimension is admitted by this
statement and rejected by the committed one; that is the entire content of the relaxation. -/
theorem cwTotalWeightFeatureYZCompatibilityCleanup_to_matrixMultiplicationDirectSum_of_degeneration
    (K : Type u) [CommRing K] (q depth n : ℕ)
    {Part : Type*} [DecidableEq Part]
    (partAt : Fin (n + 1) → Part)
    (rawTargets : CompatibilityTargets Part depth)
    (ambient : Finset
      (BlockAddress (fun _c ↦ PositiveWord (CWCoarseDigit depth) n)))
    (hambient : ambient ⊆
      (((cwChunkPartitionedTensor K q depth).coarsen
        (cwTotalWeightChunkCoarsening depth)).positivePower n).support)
    (hX : Set.InjOn
      (fun address : BlockAddress
        (fun _c ↦ PositiveWord (CWCoarseDigit depth) n) ↦ address .X) ambient)
    (hpassesY : ∀ address ∈ ambient,
      let model := cwTotalWeightFeatureCompatibilityModel depth n partAt
      let targets := cwTotalWeightPushforwardTargets rawTargets
      model.MatchesExact address .X targets.xExact ∧
        ∀ part y symbol,
          cellMultiplicity
              (fun sample ↦ yCompatibilityCell (model.coarse address sample))
              (model.symbols .Y (address .Y)) (.pooled part y) symbol =
            targets.yPooled part y symbol)
    (hpassesZ : ∀ address ∈ compatibilityIsolatedSupport ambient .Y
        ((cwTotalWeightFeatureCompatibilityModel depth n partAt).FeatureCompatibleY
          (cwTotalWeightPushforwardTargets rawTargets)),
      let model := cwTotalWeightFeatureCompatibilityModel depth n partAt
      let targets := cwTotalWeightPushforwardTargets rawTargets
      model.MatchesExact address .X targets.xExact ∧
        model.MatchesExact address .Y targets.yExact ∧
        ∀ part z symbol,
          cellMultiplicity
              (fun sample ↦ zCompatibilityCell (model.coarse address sample))
              (model.symbols .Z (address .Z)) (.pooled part z) symbol =
            targets.zPooled part z symbol)
    {C : Leg → Type v} [∀ c, Fintype (C c)] [∀ c, DecidableEq (C c)]
    (leaf : RationalTypedLeaf
      (cwChunkPartitionedTensor K q depth).support C)
    (hconstituent : ∀ support : (cwChunkPartitionedTensor K q depth).support,
      Restricts ((cwChunkPartitionedTensor K q depth).constituent support.1)
        (matrixMultiplication (K := K)
          (leaf.dimension support .X) (leaf.dimension support .Y)
          (leaf.dimension support .Z)))
    {k : ℕ}
    (hlegal : WordType.proportionalCounts leaf.profile.count k ∈
      WordType.types (cwChunkPartitionedTensor K q depth).support (n + 1))
    (hshape : ∀ address : cwTotalWeightYZIsolatedSupport
        depth n partAt rawTargets ambient,
      ∃ coarseWord : PositiveWord (CWTotalWeightCoarseSupport K q depth) n,
        positiveSupportWordBlockAddress
            (CWTotalWeightCoarseSupport K q depth) n coarseWord = address.1 ∧
          WordType.mappedType (cwTotalWeightSupportedShape K q depth)
              (WordType.multiplicity
                (positiveWordEquiv
                  (CWTotalWeightCoarseSupport K q depth) n coarseWord)) =
            WordType.mappedType (cwTotalWeightSupportedShape K q depth)
              (WordType.mappedType
                ((cwChunkPartitionedTensor K q depth).coarsenSupportMap
                  (cwTotalWeightChunkCoarsening depth))
                (WordType.proportionalCounts leaf.profile.count k))) :
    let Q := (cwChunkPartitionedTensor K q depth).coarsen
      (cwTotalWeightChunkCoarsening depth)
    let P := (Q.positivePower n).withSupport ambient
    let model := cwTotalWeightFeatureCompatibilityModel depth n partAt
    let targets := cwTotalWeightPushforwardTargets rawTargets
    let ySupport := compatibilityIsolatedSupport ambient .Y
      (model.FeatureCompatibleY targets)
    let zSupport := compatibilityIsolatedSupport ySupport .Z
      (model.FeatureCompatibleZ targets)
    Restricts P.realize
      (Tensor.indexedDirectSum (fun _address : zSupport ↦
        matrixMultiplication (K := K)
          (leaf.dimensionProduct .X ^ k)
          (leaf.dimensionProduct .Y ^ k)
          (leaf.dimensionProduct .Z ^ k))) := by
  classical
  let Q := (cwChunkPartitionedTensor K q depth).coarsen
    (cwTotalWeightChunkCoarsening depth)
  let P := (Q.positivePower n).withSupport ambient
  let model := cwTotalWeightFeatureCompatibilityModel depth n partAt
  let targets := cwTotalWeightPushforwardTargets rawTargets
  let ySupport := compatibilityIsolatedSupport ambient .Y
    (model.FeatureCompatibleY targets)
  let zSupport := compatibilityIsolatedSupport ySupport .Z
    (model.FeatureCompatibleZ targets)
  have hcleanup : Restricts P.realize
      (Tensor.indexedDirectSum
        (fun address : zSupport ↦ P.constituent address.1)) := by
    simpa [Q, P, model, targets, ySupport, zSupport,
      cwTotalWeightYZIsolatedSupport, cwTotalWeightYIsolatedSupport,
      cwTotalWeightCompatibilityY, cwTotalWeightCompatibilityZ] using
      cwTotalWeightFeatureYZCompatibilityCleanup_to_indexedDirectSum
        K q depth n partAt rawTargets ambient hambient hX hpassesY hpassesZ
  apply hcleanup.trans
  apply Restricts.indexedDirectSum
  intro address
  obtain ⟨coarseWord, hword, hwordShape⟩ := hshape address
  have hleaf :=
    cwTotalWeight_coarsenedConstituent_matrixMultiplication_of_shapeType_of_degeneration
      K q depth leaf hconstituent coarseWord hlegal hwordShape
  change Restricts ((Q.positivePower n).constituent address.1) _
  rw [← hword]
  exact hleaf

/-! ## The merged leaf -/

/-- **The cleanup at a merged rational typed leaf.**

A `MergedRationalTypedLeaf` is a rational typed leaf whose designated leg carries a merged
zero-coordinate class dimension on top of its **residual** one, so this is the previous theorem at
`leaf.toRationalTypedLeaf`.  Its premise `hmerged` is the per-letter degeneration *at the merged
dimensions* — the named obligation of the zero-coordinate one-slice fusion, not of this module.

The residual convention matters here: `leaf.residual` must not be instantiated with the committed
fine leaf, whose designated dimension already carries each zero class's own `q`-power.  See
`MergedRationalTypedLeaf`'s module doc, and
`MergedRationalTypedLeaf.dimensionProduct_mergeLeg_eq_classCardProduct_mul_representative` for the
exact relation to the fine reading. -/
theorem cwTotalWeightFeatureYZCompatibilityCleanup_to_matrixMultiplicationDirectSum_of_mergedLeaf
    (K : Type u) [CommRing K] (q depth n : ℕ)
    {Part : Type*} [DecidableEq Part]
    (partAt : Fin (n + 1) → Part)
    (rawTargets : CompatibilityTargets Part depth)
    (ambient : Finset
      (BlockAddress (fun _c ↦ PositiveWord (CWCoarseDigit depth) n)))
    (hambient : ambient ⊆
      (((cwChunkPartitionedTensor K q depth).coarsen
        (cwTotalWeightChunkCoarsening depth)).positivePower n).support)
    (hX : Set.InjOn
      (fun address : BlockAddress
        (fun _c ↦ PositiveWord (CWCoarseDigit depth) n) ↦ address .X) ambient)
    (hpassesY : ∀ address ∈ ambient,
      let model := cwTotalWeightFeatureCompatibilityModel depth n partAt
      let targets := cwTotalWeightPushforwardTargets rawTargets
      model.MatchesExact address .X targets.xExact ∧
        ∀ part y symbol,
          cellMultiplicity
              (fun sample ↦ yCompatibilityCell (model.coarse address sample))
              (model.symbols .Y (address .Y)) (.pooled part y) symbol =
            targets.yPooled part y symbol)
    (hpassesZ : ∀ address ∈ compatibilityIsolatedSupport ambient .Y
        ((cwTotalWeightFeatureCompatibilityModel depth n partAt).FeatureCompatibleY
          (cwTotalWeightPushforwardTargets rawTargets)),
      let model := cwTotalWeightFeatureCompatibilityModel depth n partAt
      let targets := cwTotalWeightPushforwardTargets rawTargets
      model.MatchesExact address .X targets.xExact ∧
        model.MatchesExact address .Y targets.yExact ∧
        ∀ part z symbol,
          cellMultiplicity
              (fun sample ↦ zCompatibilityCell (model.coarse address sample))
              (model.symbols .Z (address .Z)) (.pooled part z) symbol =
            targets.zPooled part z symbol)
    {C : Leg → Type v} [∀ c, Fintype (C c)] [∀ c, DecidableEq (C c)]
    (leaf : MergedRationalTypedLeaf
      (cwChunkPartitionedTensor K q depth).support C)
    (hmerged : ∀ support : (cwChunkPartitionedTensor K q depth).support,
      Restricts ((cwChunkPartitionedTensor K q depth).constituent support.1)
        (matrixMultiplication (K := K)
          (leaf.toRationalTypedLeaf.dimension support .X)
          (leaf.toRationalTypedLeaf.dimension support .Y)
          (leaf.toRationalTypedLeaf.dimension support .Z)))
    {k : ℕ}
    (hlegal : WordType.proportionalCounts leaf.residual.profile.count k ∈
      WordType.types (cwChunkPartitionedTensor K q depth).support (n + 1))
    (hshape : ∀ address : cwTotalWeightYZIsolatedSupport
        depth n partAt rawTargets ambient,
      ∃ coarseWord : PositiveWord (CWTotalWeightCoarseSupport K q depth) n,
        positiveSupportWordBlockAddress
            (CWTotalWeightCoarseSupport K q depth) n coarseWord = address.1 ∧
          WordType.mappedType (cwTotalWeightSupportedShape K q depth)
              (WordType.multiplicity
                (positiveWordEquiv
                  (CWTotalWeightCoarseSupport K q depth) n coarseWord)) =
            WordType.mappedType (cwTotalWeightSupportedShape K q depth)
              (WordType.mappedType
                ((cwChunkPartitionedTensor K q depth).coarsenSupportMap
                  (cwTotalWeightChunkCoarsening depth))
                (WordType.proportionalCounts leaf.residual.profile.count k))) :
    let Q := (cwChunkPartitionedTensor K q depth).coarsen
      (cwTotalWeightChunkCoarsening depth)
    let P := (Q.positivePower n).withSupport ambient
    let model := cwTotalWeightFeatureCompatibilityModel depth n partAt
    let targets := cwTotalWeightPushforwardTargets rawTargets
    let ySupport := compatibilityIsolatedSupport ambient .Y
      (model.FeatureCompatibleY targets)
    let zSupport := compatibilityIsolatedSupport ySupport .Z
      (model.FeatureCompatibleZ targets)
    Restricts P.realize
      (Tensor.indexedDirectSum (fun _address : zSupport ↦
        matrixMultiplication (K := K)
          (leaf.toRationalTypedLeaf.dimensionProduct .X ^ k)
          (leaf.toRationalTypedLeaf.dimensionProduct .Y ^ k)
          (leaf.toRationalTypedLeaf.dimensionProduct .Z ^ k))) :=
  cwTotalWeightFeatureYZCompatibilityCleanup_to_matrixMultiplicationDirectSum_of_degeneration
    K q depth n partAt rawTargets ambient hambient hX hpassesY hpassesZ
    leaf.toRationalTypedLeaf hmerged hlegal hshape

/-- **The merged cleanup output as a whole-constituent stage.**

`SimplifiedSequencePackaging.RetainedExtractionValid.of_stageFamily` consumes exactly this shape.
The copy count is the cardinality of the doubly isolated support — the same `Finset` the
compatibility-incidence estimates bound from below — and the three rectangular dimensions are the
merged leaf's own dimension products. -/
noncomputable def cwTotalWeightMergedCleanupStage
    (K : Type u) [CommRing K] (q depth n : ℕ)
    {Part : Type*} [DecidableEq Part]
    (partAt : Fin (n + 1) → Part)
    (rawTargets : CompatibilityTargets Part depth)
    (ambient : Finset
      (BlockAddress (fun _c ↦ PositiveWord (CWCoarseDigit depth) n)))
    {C : Leg → Type v} [∀ c, Fintype (C c)] [∀ c, DecidableEq (C c)]
    (leaf : MergedRationalTypedLeaf
      (cwChunkPartitionedTensor K q depth).support C)
    {k : ℕ}
    (hcleanup :
      Restricts
        ((((cwChunkPartitionedTensor K q depth).coarsen
          (cwTotalWeightChunkCoarsening depth)).positivePower n).withSupport ambient).realize
        (Tensor.indexedDirectSum (fun _address :
            cwTotalWeightYZIsolatedSupport depth n partAt rawTargets ambient ↦
          matrixMultiplication (K := K)
            (leaf.toRationalTypedLeaf.dimensionProduct .X ^ k)
            (leaf.toRationalTypedLeaf.dimensionProduct .Y ^ k)
            (leaf.toRationalTypedLeaf.dimensionProduct .Z ^ k)))) :
    WholeConstituentLaserVolumeStage K
      ((((cwChunkPartitionedTensor K q depth).coarsen
        (cwTotalWeightChunkCoarsening depth)).positivePower n).withSupport ambient).realize
      (cwTotalWeightYZIsolatedSupport depth n partAt rawTargets ambient).card
      (leaf.toRationalTypedLeaf.dimensionProduct .X ^ k)
      (leaf.toRationalTypedLeaf.dimensionProduct .Y ^ k)
      (leaf.toRationalTypedLeaf.dimensionProduct .Z ^ k) where
  I := cwTotalWeightYZIsolatedSupport depth n partAt rawTargets ambient
  card_I := Fintype.card_coe _
  source_restricts := by
    simpa only [matrixMultiplicationDirectSum] using hcleanup

/-! ## The merged `N` on the designated leg -/

/-- **The zero-coordinate merge, visible in the cleanup's own conclusion.**

Specializing the merged cleanup to a leaf built by `MergedRationalTypedLeaf.ofZeroClasses` on the
`Y` leg — the orientation the committed one-slice fusion produces — every retained leaf is

```
⟨ residual.dimensionProduct .X ^ k ,
  (residual.dimensionProduct .Y * mergedFactorProduct) ^ k ,
  residual.dimensionProduct .Z ^ k ⟩
```

with `mergedFactorProduct = ∏ i, (∑ s ∈ cls i, q ^ ones i s) ^ count i`.  The two undesignated legs
are the residual dimensions unchanged; the whole difference from the committed cleanup is the single
factor `mergedFactorProduct ^ k` on the designated leg.

**Against the committed fine reading**, at uniform local powers that factor is exactly
`(∏ i, (cls i).card ^ count i) ^ k` times the fine leaf's own `Y` product — the zero blocks' support
multiplicity, E1's zero-coordinate entropy term and E2's missing `46.414` bits per stride block.
That comparison is
`MergedRationalTypedLeaf.dimensionProduct_mergeLeg_eq_classCardProduct_mul_representative`;
the residual-side bound `classCardProduct_le_mergedFactorProduct` is strictly weaker and is not the
statement to cite against E2. -/
theorem cwTotalWeightFeatureYZCompatibilityCleanup_to_matrixMultiplicationDirectSum_of_zeroClasses
    (K : Type u) [CommRing K] (q depth n : ℕ)
    {Part : Type*} [DecidableEq Part]
    (partAt : Fin (n + 1) → Part)
    (rawTargets : CompatibilityTargets Part depth)
    (ambient : Finset
      (BlockAddress (fun _c ↦ PositiveWord (CWCoarseDigit depth) n)))
    {C : Leg → Type v} [∀ c, Fintype (C c)] [∀ c, DecidableEq (C c)]
    {ι : Type*}
    (residual : RationalTypedLeaf (cwChunkPartitionedTensor K q depth).support C)
    (hq : 0 < q)
    (ones : (cwChunkPartitionedTensor K q depth).support → ι → ℕ)
    (cls : (cwChunkPartitionedTensor K q depth).support → Finset ι)
    (hne : ∀ i, (cls i).Nonempty)
    {k : ℕ}
    (hcleanup :
      Restricts
        ((((cwChunkPartitionedTensor K q depth).coarsen
          (cwTotalWeightChunkCoarsening depth)).positivePower n).withSupport ambient).realize
        (Tensor.indexedDirectSum (fun _address :
            cwTotalWeightYZIsolatedSupport depth n partAt rawTargets ambient ↦
          matrixMultiplication (K := K)
            ((MergedRationalTypedLeaf.ofZeroClasses residual .Y q hq ones cls
              hne).toRationalTypedLeaf.dimensionProduct .X ^ k)
            ((MergedRationalTypedLeaf.ofZeroClasses residual .Y q hq ones cls
              hne).toRationalTypedLeaf.dimensionProduct .Y ^ k)
            ((MergedRationalTypedLeaf.ofZeroClasses residual .Y q hq ones cls
              hne).toRationalTypedLeaf.dimensionProduct .Z ^ k)))) :
    Restricts
      ((((cwChunkPartitionedTensor K q depth).coarsen
        (cwTotalWeightChunkCoarsening depth)).positivePower n).withSupport ambient).realize
      (Tensor.indexedDirectSum (fun _address :
          cwTotalWeightYZIsolatedSupport depth n partAt rawTargets ambient ↦
        matrixMultiplication (K := K)
          (residual.dimensionProduct .X ^ k)
          ((residual.dimensionProduct .Y *
            (MergedRationalTypedLeaf.ofZeroClasses residual .Y q hq ones cls
              hne).mergedFactorProduct) ^ k)
          (residual.dimensionProduct .Z ^ k))) := by
  have hmerge : (MergedRationalTypedLeaf.ofZeroClasses residual .Y q hq ones cls hne).mergeLeg =
      Leg.Y := rfl
  have hY := (MergedRationalTypedLeaf.ofZeroClasses residual .Y q hq ones cls
    hne).dimensionProduct_mergeLeg
  rw [hmerge, MergedRationalTypedLeaf.ofZeroClasses_residual] at hY
  have hX := (MergedRationalTypedLeaf.ofZeroClasses residual .Y q hq ones cls
    hne).dimensionProduct_of_ne (c := Leg.X) (by rw [hmerge]; exact Leg.noConfusion)
  have hZ := (MergedRationalTypedLeaf.ofZeroClasses residual .Y q hq ones cls
    hne).dimensionProduct_of_ne (c := Leg.Z) (by rw [hmerge]; exact Leg.noConfusion)
  rw [MergedRationalTypedLeaf.ofZeroClasses_residual] at hX hZ
  rw [← hX, ← hY, ← hZ]
  exact hcleanup

end AlgebraicComplexity.Examples
