/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinogradSortedPairHashingEndpoint
import AlgebraicComplexity.Examples.CoppersmithWinogradChunkTypedLeaf
import AlgebraicComplexity.MatrixMultiplication.WholeConstituentLaserVolumeAssembly

/-!
# Certificate-defined support for the sorted-pair hashing endpoint

The finite endpoint should not ask a numerical certificate to re-prove semantic facts about
every retained address.  This module defines the pre-hash family by the exact profile equations
that the certificate already stores.  Membership then supplies, by projection:

* the exact and pooled equations needed by the `Y/Z` compatibility zero-outs;
* the three shape-conditional profiles determining the full joint quotient type; and
* support in the upstream `X`-isolated family.

Consequently all of those facts survive affine hashing and subsequent zero-outs automatically.
The only remaining certificate obligations in the main corollary are the genuinely quantitative
incidence-density inequality and the upstream `X`-isolation theorem.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor MoreAsymmetryCompatibility

universe u v w x

/-- Exact semantic data imposed on one supported sorted-pair power address before affine
hashing.  `targetType` is the desired full quotient support type, normally the pushforward of a
fine rational typed-leaf type. -/
structure CWSortedPairCertificateProfiles
    (K : Type u) [CommRing K] (q n : ℕ)
    {Part : Type v} [DecidableEq Part]
    (partAt : Fin (n + 1) → Part)
    (rawTargets : CompatibilityTargets Part 1)
    (targetType : CWSortedPairCoarseSupport K q → ℕ)
    (source : CWSortedPairPowerSupport K q n) : Prop where
  matchesX :
    (cwSortedPairFeatureCompatibilityModel n partAt).MatchesExact source.1 .X
      (cwSortedPairPushforwardTargets rawTargets).xExact
  matchesY :
    (cwSortedPairFeatureCompatibilityModel n partAt).MatchesExact source.1 .Y
      (cwSortedPairPushforwardTargets rawTargets).yExact
  matchesZ :
    (cwSortedPairFeatureCompatibilityModel n partAt).MatchesExact source.1 .Z
      (cwSortedPairPushforwardTargets rawTargets).zExact
  pooledY : ∀ part y symbol,
    cellMultiplicity
        (fun sample ↦ yCompatibilityCell
          ((cwSortedPairFeatureCompatibilityModel n partAt).coarse source.1 sample))
        ((cwSortedPairFeatureCompatibilityModel n partAt).symbols .Y (source.1 .Y))
        (.pooled part y) symbol =
      (cwSortedPairPushforwardTargets rawTargets).yPooled part y symbol
  pooledZ : ∀ part z symbol,
    cellMultiplicity
        (fun sample ↦ zCompatibilityCell
          ((cwSortedPairFeatureCompatibilityModel n partAt).coarse source.1 sample))
        ((cwSortedPairFeatureCompatibilityModel n partAt).symbols .Z (source.1 .Z))
        (.pooled part z) symbol =
      (cwSortedPairPushforwardTargets rawTargets).zPooled part z symbol
  shapeConditional : ∀ c,
    cwSortedPairShapeConditionalProfile K q
        (WordType.multiplicity
          (positiveWordEquiv (CWSortedPairCoarseSupport K q) n
            (cwSortedPairSupportedWordOfAddress K q n source.1 source.2))) c =
      cwSortedPairShapeConditionalProfile K q targetType c

/-- Filter an already `X`-isolated upstream family by all exact profile equations used later in
the sorted-pair proof. -/
noncomputable def cwSortedPairCertificateTargets
    (K : Type u) [CommRing K] (q n : ℕ)
    {Part : Type v} [DecidableEq Part]
    (partAt : Fin (n + 1) → Part)
    (rawTargets : CompatibilityTargets Part 1)
    (targetType : CWSortedPairCoarseSupport K q → ℕ)
    (upstream : Finset (CWSortedPairPowerSupport K q n)) :
    Finset (CWSortedPairPowerSupport K q n) := by
  classical
  exact upstream.filter
    (CWSortedPairCertificateProfiles K q n partAt rawTargets targetType)

@[simp] theorem mem_cwSortedPairCertificateTargets
    (K : Type u) [CommRing K] (q n : ℕ)
    {Part : Type v} [DecidableEq Part]
    (partAt : Fin (n + 1) → Part)
    (rawTargets : CompatibilityTargets Part 1)
    (targetType : CWSortedPairCoarseSupport K q → ℕ)
    (upstream : Finset (CWSortedPairPowerSupport K q n))
    (source : CWSortedPairPowerSupport K q n) :
    source ∈ cwSortedPairCertificateTargets K q n partAt rawTargets targetType upstream ↔
      source ∈ upstream ∧
        CWSortedPairCertificateProfiles K q n partAt rawTargets targetType source := by
  classical
  simp [cwSortedPairCertificateTargets]

theorem cwSortedPairCertificateTargets_subset_upstream
    (K : Type u) [CommRing K] (q n : ℕ)
    {Part : Type v} [DecidableEq Part]
    (partAt : Fin (n + 1) → Part)
    (rawTargets : CompatibilityTargets Part 1)
    (targetType : CWSortedPairCoarseSupport K q → ℕ)
    (upstream : Finset (CWSortedPairPowerSupport K q n)) :
    cwSortedPairCertificateTargets K q n partAt rawTargets targetType upstream ⊆ upstream := by
  intro source hsource
  exact (mem_cwSortedPairCertificateTargets K q n partAt rawTargets
    targetType upstream source).mp hsource |>.1

/-- Forgetting support proofs is monotone in the selected family. -/
theorem cwSortedPairSelectedAddressSupport_mono
    (K : Type u) [CommRing K] (q n : ℕ)
    {left right : Finset (CWSortedPairPowerSupport K q n)}
    (h : left ⊆ right) :
    cwSortedPairSelectedAddressSupport K q n left ⊆
      cwSortedPairSelectedAddressSupport K q n right := by
  classical
  exact Finset.image_subset_image h

/-- Upstream injectivity of `X` labels survives every subsequent finite selection. -/
theorem cwSortedPairSelectedAddressSupport_injOn_of_subset
    (K : Type u) [CommRing K] (q n : ℕ)
    {left right : Finset (CWSortedPairPowerSupport K q n)}
    (h : left ⊆ right)
    (hX : Set.InjOn
      (fun address : BlockAddress (fun _c ↦ PositiveWord (SplitWord 1) n) ↦
        address .X) (cwSortedPairSelectedAddressSupport K q n right)) :
    Set.InjOn
      (fun address : BlockAddress (fun _c ↦ PositiveWord (SplitWord 1) n) ↦
        address .X) (cwSortedPairSelectedAddressSupport K q n left) :=
  hX.mono (cwSortedPairSelectedAddressSupport_mono K q n h)

/-- An address selected from a subfamily of the certificate family carries all certificate
profiles, with its positive-power support proof reconstructed canonically. -/
theorem cwSortedPairCertificateProfiles_of_mem_selectedAddressSupport
    (K : Type u) [CommRing K] (q n : ℕ)
    {Part : Type v} [DecidableEq Part]
    (partAt : Fin (n + 1) → Part)
    (rawTargets : CompatibilityTargets Part 1)
    (targetType : CWSortedPairCoarseSupport K q → ℕ)
    (upstream selected : Finset (CWSortedPairPowerSupport K q n))
    (hselected : selected ⊆
      cwSortedPairCertificateTargets K q n partAt rawTargets targetType upstream)
    {address : BlockAddress (fun _c ↦ PositiveWord (SplitWord 1) n)}
    (haddress : address ∈ cwSortedPairSelectedAddressSupport K q n selected) :
    ∃ hsupport : address ∈
        (((cwChunkPartitionedTensor K q 1).coarsen
          cwSortedPairChunkCoarsening).positivePower n).support,
      CWSortedPairCertificateProfiles K q n partAt rawTargets targetType
        ⟨address, hsupport⟩ := by
  classical
  obtain ⟨source, hsource, hvalue⟩ := Finset.mem_image.mp haddress
  subst address
  refine ⟨source.2, ?_⟩
  have hprofiles := (mem_cwSortedPairCertificateTargets K q n partAt rawTargets
    targetType upstream source).mp (hselected hsource) |>.2
  simpa only using hprofiles

/-- The exact `X` and pooled-`Y` equations needed by the first compatibility zero-out are
definitional consequences of certificate-family membership. -/
theorem cwSortedPairCertificateTargets_passesY
    (K : Type u) [CommRing K] (q n : ℕ)
    {Part : Type v} [DecidableEq Part]
    (partAt : Fin (n + 1) → Part)
    (rawTargets : CompatibilityTargets Part 1)
    (targetType : CWSortedPairCoarseSupport K q → ℕ)
    (upstream selected : Finset (CWSortedPairPowerSupport K q n))
    (hselected : selected ⊆
      cwSortedPairCertificateTargets K q n partAt rawTargets targetType upstream) :
    ∀ address ∈ cwSortedPairSelectedAddressSupport K q n selected,
      let model := cwSortedPairFeatureCompatibilityModel n partAt
      let targets := cwSortedPairPushforwardTargets rawTargets
      model.MatchesExact address .X targets.xExact ∧
        ∀ part y symbol,
          cellMultiplicity
              (fun sample ↦ yCompatibilityCell (model.coarse address sample))
              (model.symbols .Y (address .Y)) (.pooled part y) symbol =
            targets.yPooled part y symbol := by
  intro address haddress
  obtain ⟨hsupport, hprofiles⟩ :=
    cwSortedPairCertificateProfiles_of_mem_selectedAddressSupport K q n partAt
      rawTargets targetType upstream selected hselected haddress
  exact ⟨hprofiles.matchesX, hprofiles.pooledY⟩

/-- The exact `X/Y` and pooled-`Z` equations needed by the second zero-out survive the first
zero-out automatically. -/
theorem cwSortedPairCertificateTargets_passesZ
    (K : Type u) [CommRing K] (q n : ℕ)
    {Part : Type v} [DecidableEq Part]
    (partAt : Fin (n + 1) → Part)
    (rawTargets : CompatibilityTargets Part 1)
    (targetType : CWSortedPairCoarseSupport K q → ℕ)
    (upstream selected : Finset (CWSortedPairPowerSupport K q n))
    (hselected : selected ⊆
      cwSortedPairCertificateTargets K q n partAt rawTargets targetType upstream) :
    ∀ address ∈ cwSortedPairYIsolatedSupport n partAt rawTargets
        (cwSortedPairSelectedAddressSupport K q n selected),
      let model := cwSortedPairFeatureCompatibilityModel n partAt
      let targets := cwSortedPairPushforwardTargets rawTargets
      model.MatchesExact address .X targets.xExact ∧
        model.MatchesExact address .Y targets.yExact ∧
        ∀ part z symbol,
          cellMultiplicity
              (fun sample ↦ zCompatibilityCell (model.coarse address sample))
              (model.symbols .Z (address .Z)) (.pooled part z) symbol =
            targets.zPooled part z symbol := by
  intro address haddress
  have hambient : address ∈ cwSortedPairSelectedAddressSupport K q n selected :=
    by
      simpa only [cwSortedPairYIsolatedSupport] using
        (compatibilityIsolatedSupport_subset
          (cwSortedPairSelectedAddressSupport K q n selected) .Y
          (cwSortedPairCompatibilityY n partAt rawTargets) haddress)
  obtain ⟨hsupport, hprofiles⟩ :=
    cwSortedPairCertificateProfiles_of_mem_selectedAddressSupport K q n partAt
      rawTargets targetType upstream selected hselected hambient
  exact ⟨hprofiles.matchesX, hprofiles.matchesY, hprofiles.pooledZ⟩

/-- The final isolated family has the prescribed full quotient type because every retained
address inherits the three shape-conditional profiles imposed before hashing. -/
theorem cwSortedPairCertificateTargets_jointProfiles
    (K : Type u) [CommRing K] (q n : ℕ)
    {Part : Type v} [DecidableEq Part]
    (partAt : Fin (n + 1) → Part)
    (rawTargets : CompatibilityTargets Part 1)
    (targetType : CWSortedPairCoarseSupport K q → ℕ)
    (upstream selected : Finset (CWSortedPairPowerSupport K q n))
    (hselected : selected ⊆
      cwSortedPairCertificateTargets K q n partAt rawTargets targetType upstream) :
    ∀ address : cwSortedPairYZIsolatedSupport n partAt rawTargets
        (cwSortedPairSelectedAddressSupport K q n selected),
      ∃ coarseWord : PositiveWord (CWSortedPairCoarseSupport K q) n,
        positiveSupportWordBlockAddress
            (CWSortedPairCoarseSupport K q) n coarseWord = address.1 ∧
          ∀ c,
            cwSortedPairShapeConditionalProfile K q
                (WordType.multiplicity
                  (positiveWordEquiv
                    (CWSortedPairCoarseSupport K q) n coarseWord)) c =
              cwSortedPairShapeConditionalProfile K q targetType c := by
  intro address
  have hy : address.1 ∈ cwSortedPairYIsolatedSupport n partAt rawTargets
      (cwSortedPairSelectedAddressSupport K q n selected) :=
    by
      simpa only [cwSortedPairYZIsolatedSupport] using
        (compatibilityIsolatedSupport_subset
          (cwSortedPairYIsolatedSupport n partAt rawTargets
            (cwSortedPairSelectedAddressSupport K q n selected)) .Z
          (cwSortedPairCompatibilityZ n partAt rawTargets) address.2)
  have hambient : address.1 ∈ cwSortedPairSelectedAddressSupport K q n selected :=
    by
      simpa only [cwSortedPairYIsolatedSupport] using
        (compatibilityIsolatedSupport_subset
          (cwSortedPairSelectedAddressSupport K q n selected) .Y
          (cwSortedPairCompatibilityY n partAt rawTargets) hy)
  obtain ⟨hsupport, hprofiles⟩ :=
    cwSortedPairCertificateProfiles_of_mem_selectedAddressSupport K q n partAt
      rawTargets targetType upstream selected hselected hambient
  let coarseWord := cwSortedPairSupportedWordOfAddress K q n address.1 hsupport
  refine ⟨coarseWord,
    positiveSupportWordBlockAddress_cwSortedPairSupportedWordOfAddress
      K q n address.1 hsupport, ?_⟩
  exact hprofiles.shapeConditional

/-- Exact proportional counts have the required word length whenever the stride equation holds.
This removes a redundant `WordType.types` premise from every rational typed-leaf client. -/
theorem proportionalCounts_mem_types_of_profileMass_mul_eq
    {I : Type u} [Fintype I] (count : I → ℕ) (k length : ℕ)
    (hstride : WordType.profileMass count * k = length) :
    WordType.proportionalCounts count k ∈ WordType.types I length := by
  rw [WordType.mem_types]
  simpa [WordType.profileMass, WordType.proportionalCounts, Finset.sum_mul] using hstride

/-- Cancel a positive common finite hash-loss factor.  This is the exact arithmetic bridge from
a scaled residual-incidence bound and the good-seed count to half density of the selected
family. -/
theorem residualHalfDensity_of_scaled_count
    (scale incidence hashCount selected : ℕ) (hscale : 0 < scale)
    (hincidence : scale * (2 * incidence) ≤ hashCount)
    (hhash : hashCount ≤ scale * selected) :
    2 * incidence ≤ selected := by
  exact Nat.le_of_mul_le_mul_left (hincidence.trans hhash) hscale

/-- With every field element used as a bucket, cancel one positive field-cardinality factor from
the composed hash count.  Thus the finite loss is linear, not quadratic, in `|R|`. -/
theorem fullBucket_hashCount_cancel
    {R : Type u} [Fintype R] [Nonempty R]
    (targets finalSupport : ℕ)
    (hcount : 3 * targets * (Finset.univ : Finset R).card ≤
      8 * (Fintype.card R * Fintype.card R) * finalSupport) :
    3 * targets ≤ 8 * Fintype.card R * finalSupport := by
  have hcount' : (3 * targets) * Fintype.card R ≤
      (8 * Fintype.card R * finalSupport) * Fintype.card R := by
    simpa only [Finset.card_univ] using hcount.trans_eq (by ring)
  exact Nat.le_of_mul_le_mul_right hcount' Fintype.card_pos

/-- Certificate-facing fixed-family endpoint.  Exact/pooled profile equations, the joint
quotient type, legality of proportional counts, exact incidence budgets, and inherited `X`
injectivity are all discharged internally. -/
theorem cwSortedPairCertificateHashSelected_to_matrixMultiplicationDirectSum
    (K : Type u) [CommRing K] (q n : ℕ)
    {Part : Type v} [DecidableEq Part]
    (partAt : Fin (n + 1) → Part)
    (rawTargets : CompatibilityTargets Part 1)
    {C : Leg → Type w} [∀ c, Fintype (C c)] [∀ c, DecidableEq (C c)]
    (leaf : RationalTypedLeaf
      (cwChunkPartitionedTensor K q 1).support C)
    (hdimension : ∀ support c,
      leaf.dimension support c = cwChunkConstituentDimension K q 1 support c)
    (k : ℕ)
    (upstream selected : Finset (CWSortedPairPowerSupport K q n))
    (hselected : selected ⊆
      cwSortedPairCertificateTargets K q n partAt rawTargets
        (WordType.mappedType
          ((cwChunkPartitionedTensor K q 1).coarsenSupportMap
            cwSortedPairChunkCoarsening)
          (WordType.proportionalCounts leaf.profile.count k)) upstream)
    (hX : Set.InjOn
      (fun address : BlockAddress (fun _c ↦ PositiveWord (SplitWord 1) n) ↦
        address .X) (cwSortedPairSelectedAddressSupport K q n upstream))
    (hstride : WordType.profileMass leaf.profile.count * k = n + 1)
    (hhalf : 2 *
      (cwSortedPairYCompetitorIncidence n partAt rawTargets
          (cwSortedPairSelectedAddressSupport K q n selected) +
        cwSortedPairZCompetitorIncidence n partAt rawTargets
          (cwSortedPairSelectedAddressSupport K q n selected)) ≤ selected.card)
    (hashCount hashLoss : ℕ)
    (hhash : hashCount ≤ hashLoss * selected.card) :
    let ambient := cwSortedPairSelectedAddressSupport K q n selected
    let finalSupport := cwSortedPairYZIsolatedSupport n partAt rawTargets ambient
    Restricts
        (((((cwChunkPartitionedTensor K q 1).coarsen
          cwSortedPairChunkCoarsening).positivePower n).withSupport ambient).realize)
        (Tensor.indexedDirectSum (fun _address : finalSupport ↦
          matrixMultiplication (K := K)
            (leaf.dimensionProduct .X ^ k)
            (leaf.dimensionProduct .Y ^ k)
            (leaf.dimensionProduct .Z ^ k))) ∧
      selected.card ≤ finalSupport.card +
        cwSortedPairYCompetitorIncidence n partAt rawTargets ambient +
        cwSortedPairZCompetitorIncidence n partAt rawTargets ambient ∧
      selected.card ≤ 2 * finalSupport.card ∧
      hashCount ≤ (2 * hashLoss) * finalSupport.card := by
  let targetType := WordType.mappedType
    ((cwChunkPartitionedTensor K q 1).coarsenSupportMap
      cwSortedPairChunkCoarsening)
    (WordType.proportionalCounts leaf.profile.count k)
  have hselected' : selected ⊆
      cwSortedPairCertificateTargets K q n partAt rawTargets targetType upstream := by
    simpa only [targetType] using hselected
  have hselectedUpstream : selected ⊆ upstream :=
    hselected'.trans
      (cwSortedPairCertificateTargets_subset_upstream K q n partAt rawTargets
        targetType upstream)
  have hXSelected := cwSortedPairSelectedAddressSupport_injOn_of_subset
    K q n hselectedUpstream hX
  have hpassesY := cwSortedPairCertificateTargets_passesY
    K q n partAt rawTargets targetType upstream selected hselected'
  have hpassesZ := cwSortedPairCertificateTargets_passesZ
    K q n partAt rawTargets targetType upstream selected hselected'
  have hjoint := cwSortedPairCertificateTargets_jointProfiles
    K q n partAt rawTargets targetType upstream selected hselected'
  have hlegal : WordType.proportionalCounts leaf.profile.count k ∈
      WordType.types (cwChunkPartitionedTensor K q 1).support (n + 1) :=
    proportionalCounts_mem_types_of_profileMass_mul_eq leaf.profile.count k (n + 1) hstride
  have hconstituent :=
    cwChunk_constituent_restricts_of_leaf_dimension_eq K q 1 leaf hdimension
  exact cwSortedPairHashSelected_to_matrixMultiplicationDirectSum
    K q n partAt rawTargets selected hXSelected hpassesY hpassesZ
      leaf hconstituent hlegal hjoint
      (cwSortedPairYCompetitorIncidence n partAt rawTargets
        (cwSortedPairSelectedAddressSupport K q n selected))
      (cwSortedPairZCompetitorIncidence n partAt rawTargets
        (cwSortedPairSelectedAddressSupport K q n selected))
      (by rfl) (by rfl) hhalf hashCount hashLoss hhash

/-- Package a fixed certificate-selected restriction as a whole-constituent stage and precompose
it with any available upstream `X`-isolation/support-selection restriction.  Counts and all
three matrix dimensions are unchanged. -/
noncomputable def cwSortedPairCertificateWholeStage_precompose
    (K : Type u) [CommRing K] (q n : ℕ)
    {Part : Type*} [DecidableEq Part]
    (partAt : Fin (n + 1) → Part)
    (rawTargets : CompatibilityTargets Part 1)
    (selected : Finset (CWSortedPairPowerSupport K q n))
    {C : Leg → Type w} [∀ c, Fintype (C c)] [∀ c, DecidableEq (C c)]
    (leaf : RationalTypedLeaf (cwChunkPartitionedTensor K q 1).support C)
    (k : ℕ)
    (hrestricts :
      let ambient := cwSortedPairSelectedAddressSupport K q n selected
      let finalSupport := cwSortedPairYZIsolatedSupport n partAt rawTargets ambient
      Restricts
        (((((cwChunkPartitionedTensor K q 1).coarsen
          cwSortedPairChunkCoarsening).positivePower n).withSupport ambient).realize)
        (Tensor.indexedDirectSum (fun _address : finalSupport ↦
          matrixMultiplication (K := K)
            (leaf.dimensionProduct .X ^ k)
            (leaf.dimensionProduct .Y ^ k)
            (leaf.dimensionProduct .Z ^ k))))
    {V : Leg → Type x} [∀ c, AddCommMonoid (V c)] [∀ c, Module K (V c)]
    (upstreamSource : Tensor3 K V)
    (hupstream :
      let ambient := cwSortedPairSelectedAddressSupport K q n selected
      Restricts upstreamSource
        (((((cwChunkPartitionedTensor K q 1).coarsen
          cwSortedPairChunkCoarsening).positivePower n).withSupport ambient).realize)) :
    let ambient := cwSortedPairSelectedAddressSupport K q n selected
    let finalSupport := cwSortedPairYZIsolatedSupport n partAt rawTargets ambient
    WholeConstituentLaserVolumeStage K upstreamSource finalSupport.card
      (leaf.dimensionProduct .X ^ k)
      (leaf.dimensionProduct .Y ^ k)
      (leaf.dimensionProduct .Z ^ k) := by
  let stage := cwSortedPairHashSelectedWholeConstituentLaserVolumeStage
    K q n partAt rawTargets selected leaf k hrestricts
  exact WholeConstituentLaserVolumeStage.precompose (K := K) hupstream stage

/-- End-to-end finite seed theorem.  Exact reconstructed compatibility profiles provide the
support condition for affine collision hashing; all semantic profile premises of the tensor
cleanup are inherited from `cwSortedPairCertificateTargets`.  The residual premise is required
only for a seed satisfying the good-count inequality, and supplies a scaled incidence bound from
which half density is proved by cancellation. -/
theorem exists_seed_cwSortedPairCertificate_to_matrixMultiplicationDirectSum
    {R : Type v} [Field R] [Fintype R] [NeZero (2 : R)]
    (encoding : CWCoarseFieldEncoding R 1)
    (K : Type u) [CommRing K] (q n : ℕ)
    {Part : Type*} [Fintype Part] [DecidableEq Part]
    (partAt : Fin (n + 1) → Part)
    (rawTargets : CompatibilityTargets Part 1)
    (data : ExactCompatibilityProfileFamily Part 1)
    (pooled : ExactSplitAvgFamily Part 1)
    (hdata : data.RealizesTargets rawTargets)
    (hpooled : pooled.RealizesTargets rawTargets)
    {C : Leg → Type w} [∀ c, Fintype (C c)] [∀ c, DecidableEq (C c)]
    (leaf : RationalTypedLeaf
      (cwChunkPartitionedTensor K q 1).support C)
    (hdimension : ∀ support c,
      leaf.dimension support c = cwChunkConstituentDimension K q 1 support c)
    (k : ℕ)
    (upstream : Finset (CWSortedPairPowerSupport K q n))
    (hX : Set.InjOn
      (fun address : BlockAddress (fun _c ↦ PositiveWord (SplitWord 1) n) ↦
        address .X) (cwSortedPairSelectedAddressSupport K q n upstream))
    (hstride : WordType.profileMass leaf.profile.count * k = n + 1)
    (buckets : Finset R)
    (hquarter : ∀ target ∈
      cwSortedPairCertificateTargets K q n partAt rawTargets
        (WordType.mappedType
          ((cwChunkPartitionedTensor K q 1).coarsenSupportMap
            cwSortedPairChunkCoarsening)
          (WordType.proportionalCounts leaf.profile.count k)) upstream,
      4 * ((cwSortedPairYCompetitorTypeClass K q n rawTargets
          (target.1 .Y)).card +
        (cwSortedPairZCompetitorTypeClass K q n rawTargets
          (target.1 .Z)).card) ≤ Fintype.card R)
    (hresidualCount : ∀ seed : ProgressionHash.Seed R (Fin (n + 1)),
      let targets := cwSortedPairCertificateTargets K q n partAt rawTargets
        (WordType.mappedType
          ((cwChunkPartitionedTensor K q 1).coarsenSupportMap
            cwSortedPairChunkCoarsening)
          (WordType.proportionalCounts leaf.profile.count k)) upstream
      let selected := cwSortedPairYZHashIsolatedTargets encoding K q n partAt rawTargets
        targets buckets seed
      let ambient := cwSortedPairSelectedAddressSupport K q n selected
      3 * targets.card * buckets.card ≤
          8 * (Fintype.card R * Fintype.card R) * selected.card →
        16 * (Fintype.card R * Fintype.card R) *
            (cwSortedPairYCompetitorIncidence n partAt rawTargets ambient +
              cwSortedPairZCompetitorIncidence n partAt rawTargets ambient) ≤
          3 * targets.card * buckets.card) :
    ∃ seed : ProgressionHash.Seed R (Fin (n + 1)),
      let targets := cwSortedPairCertificateTargets K q n partAt rawTargets
        (WordType.mappedType
          ((cwChunkPartitionedTensor K q 1).coarsenSupportMap
            cwSortedPairChunkCoarsening)
          (WordType.proportionalCounts leaf.profile.count k)) upstream
      let selected := cwSortedPairYZHashIsolatedTargets encoding K q n partAt rawTargets
        targets buckets seed
      let ambient := cwSortedPairSelectedAddressSupport K q n selected
      let finalSupport := cwSortedPairYZIsolatedSupport n partAt rawTargets ambient
      Restricts
          (((((cwChunkPartitionedTensor K q 1).coarsen
            cwSortedPairChunkCoarsening).positivePower n).withSupport ambient).realize)
          (Tensor.indexedDirectSum (fun _address : finalSupport ↦
            matrixMultiplication (K := K)
              (leaf.dimensionProduct .X ^ k)
              (leaf.dimensionProduct .Y ^ k)
              (leaf.dimensionProduct .Z ^ k))) ∧
        Nonempty (WholeConstituentLaserVolumeStage.{u, u, 0} K
          (((((cwChunkPartitionedTensor K q 1).coarsen
            cwSortedPairChunkCoarsening).positivePower n).withSupport ambient).realize)
          finalSupport.card
          (leaf.dimensionProduct .X ^ k)
          (leaf.dimensionProduct .Y ^ k)
          (leaf.dimensionProduct .Z ^ k)) ∧
        3 * targets.card * buckets.card ≤
          8 * (Fintype.card R * Fintype.card R) * finalSupport.card := by
  classical
  let targetType := WordType.mappedType
    ((cwChunkPartitionedTensor K q 1).coarsenSupportMap
      cwSortedPairChunkCoarsening)
    (WordType.proportionalCounts leaf.profile.count k)
  let targets := cwSortedPairCertificateTargets K q n partAt rawTargets
    targetType upstream
  have hsupported : rawTargets.IsWeightSupported :=
    data.isWeightSupported_of_realizesTargets pooled rawTargets hdata hpooled
  obtain ⟨seed, hcount, hcommon, _hisolated⟩ :=
    exists_seed_many_cwSortedPairYZHashIsolatedTargets encoding K q n partAt
      rawTargets hsupported targets buckets (by
        intro target htarget
        simpa only [targets, targetType] using hquarter target htarget)
  let selected := cwSortedPairYZHashIsolatedTargets encoding K q n partAt rawTargets
    targets buckets seed
  have hcountEight : 3 * targets.card * buckets.card ≤
      8 * (Fintype.card R * Fintype.card R) * selected.card := by
    exact hcount.trans (by
      dsimp only [selected]
      gcongr
      norm_num)
  have hselected : selected ⊆ targets := by
    intro target htarget
    have hcommonTarget : target ∈
        cwSortedPairCommonBucketTargets encoding K q n targets buckets seed := by
      exact hcommon htarget
    exact (ProgressionHash.Seed.mem_commonBucketFilteredTargets targets buckets
      (cwSortedPairXHashIndex encoding K q n)
      (cwSortedPairYHashIndex encoding K q n) seed target).mp hcommonTarget |>.1
  have hhalf : 2 *
      (cwSortedPairYCompetitorIncidence n partAt rawTargets
          (cwSortedPairSelectedAddressSupport K q n selected) +
        cwSortedPairZCompetitorIncidence n partAt rawTargets
          (cwSortedPairSelectedAddressSupport K q n selected)) ≤ selected.card := by
    let incidence :=
      cwSortedPairYCompetitorIncidence n partAt rawTargets
          (cwSortedPairSelectedAddressSupport K q n selected) +
        cwSortedPairZCompetitorIncidence n partAt rawTargets
          (cwSortedPairSelectedAddressSupport K q n selected)
    let scale := 8 * (Fintype.card R * Fintype.card R)
    have hscaled : scale * (2 * incidence) ≤ 3 * targets.card * buckets.card := by
      have hcertificate := hresidualCount seed (by
        simpa only [targets, targetType, selected] using hcountEight)
      dsimp only [scale, incidence]
      calc
        8 * (Fintype.card R * Fintype.card R) *
            (2 * (cwSortedPairYCompetitorIncidence n partAt rawTargets
                (cwSortedPairSelectedAddressSupport K q n selected) +
              cwSortedPairZCompetitorIncidence n partAt rawTargets
                (cwSortedPairSelectedAddressSupport K q n selected))) =
            16 * (Fintype.card R * Fintype.card R) *
              (cwSortedPairYCompetitorIncidence n partAt rawTargets
                  (cwSortedPairSelectedAddressSupport K q n selected) +
                cwSortedPairZCompetitorIncidence n partAt rawTargets
                  (cwSortedPairSelectedAddressSupport K q n selected)) := by ring
        _ ≤ 3 * targets.card * buckets.card := by
          simpa only [targets, targetType, selected] using hcertificate
    have hscale : 0 < scale := by
      dsimp only [scale]
      positivity
    exact residualHalfDensity_of_scaled_count scale incidence
      (3 * targets.card * buckets.card) selected.card hscale hscaled hcountEight
  have hendpoint :=
    cwSortedPairCertificateHashSelected_to_matrixMultiplicationDirectSum
      K q n partAt rawTargets leaf hdimension k upstream selected
      (by simpa only [targets, targetType] using hselected) hX hstride hhalf
      (3 * targets.card * buckets.card)
      (4 * (Fintype.card R * Fintype.card R)) hcount
  refine ⟨seed, ?_⟩
  rcases hendpoint with ⟨hrestricts, _hadd, _hhalfFinal, hfinal⟩
  have hstage := cwSortedPairHashSelectedWholeConstituentLaserVolumeStage
    K q n partAt rawTargets selected leaf k hrestricts
  refine ⟨?_, ?_, ?_⟩
  · simpa only [targets, targetType, selected] using hrestricts
  · exact ⟨by simpa only [targets, targetType, selected] using hstage⟩
  · simp only [targets, targetType, selected] at hfinal ⊢
    exact hfinal.trans_eq (by ring)

end AlgebraicComplexity.Examples
