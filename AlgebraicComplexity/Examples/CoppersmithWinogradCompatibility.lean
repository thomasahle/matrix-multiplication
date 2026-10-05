/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinogradInterface
import AlgebraicComplexity.MatrixMultiplication.MoreAsymmetryCompatibilityInterface
import AlgebraicComplexity.MatrixMultiplication.MoreAsymmetryCompatibilityTransport

/-!
# Complete-split compatibility for concrete CW interface tensors

This file instantiates the reusable positive-power compatibility model with the native recursive
block representation of `CW_q`.  A depth-`d` native chunk is a positive word of `2^d` base CW
blocks; `cwChunkSplitWord` is exactly its complete-split encoding.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor MoreAsymmetryCompatibility

universe u v

/-- Every supported depth-`d` CW chunk address is coordinatewise fine-legal under its native
complete-split encoding. -/
theorem cwChunkPartitionedTensor_isEncodedFineLegalOnSupport
    (K : Type u) [CommRing K] (q depth : ℕ) :
    IsEncodedFineLegalOnSupport (cwChunkPartitionedTensor K q depth).support
      (fun _c ↦ cwChunkSplitWord depth) := by
  intro address haddress position
  change address ∈
    ((cwPartitionedTensor K q).positivePower (2 ^ depth - 1)).support at haddress
  obtain ⟨source, hsource⟩ :=
    (cwPartitionedTensor K q).exists_positiveSupportWord_of_mem_positivePower_support
      (2 ^ depth - 1) haddress
  rw [← hsource]
  let sample : Fin (2 ^ depth - 1 + 1) := (cwChunkPositionEquiv depth).symm position
  change
    (cwBlockDigit
          (positiveWordEquiv CWBlock (2 ^ depth - 1)
            (positiveSupportWordBlockAddress (cwPartitionedTensor K q).support
              (2 ^ depth - 1) source .X) sample) : ℕ) +
        (cwBlockDigit
          (positiveWordEquiv CWBlock (2 ^ depth - 1)
            (positiveSupportWordBlockAddress (cwPartitionedTensor K q).support
              (2 ^ depth - 1) source .Y) sample) : ℕ) +
        (cwBlockDigit
          (positiveWordEquiv CWBlock (2 ^ depth - 1)
            (positiveSupportWordBlockAddress (cwPartitionedTensor K q).support
              (2 ^ depth - 1) source .Z) sample) : ℕ) = 2
  rw [congrFun
      (positiveWordEquiv_positiveSupportWordBlockAddress
        (cwPartitionedTensor K q).support (2 ^ depth - 1) source .X) sample,
    congrFun
      (positiveWordEquiv_positiveSupportWordBlockAddress
        (cwPartitionedTensor K q).support (2 ^ depth - 1) source .Y) sample,
    congrFun
      (positiveWordEquiv_positiveSupportWordBlockAddress
        (cwPartitionedTensor K q).support (2 ^ depth - 1) source .Z) sample]
  have hsupported := (positiveWordEquiv (cwPartitionedTensor K q).support
    (2 ^ depth - 1) source sample).2
  change
    (cwBlockDigit
          ((positiveWordEquiv (cwPartitionedTensor K q).support
            (2 ^ depth - 1) source sample).1 .X) : ℕ) +
        (cwBlockDigit
          ((positiveWordEquiv (cwPartitionedTensor K q).support
            (2 ^ depth - 1) source sample).1 .Y) : ℕ) +
        (cwBlockDigit
          ((positiveWordEquiv (cwPartitionedTensor K q).support
            (2 ^ depth - 1) source sample).1 .Z) : ℕ) = 2
  change
    (positiveWordEquiv (cwPartitionedTensor K q).support
      (2 ^ depth - 1) source sample).1 ∈ cwBlockSupport at hsupported
  simpa [sum_leg] using cwBlockSupport_digit_sum
    (positiveWordEquiv (cwPartitionedTensor K q).support
      (2 ^ depth - 1) source sample).1 hsupported

/-- The concrete compatibility model on `n+1` selected level-`depth+1` CW chunks. -/
def cwExactInterfaceCompatibilityModel {Part : Type v} (depth n : ℕ)
    (partAt : Fin (n + 1) → Part) :=
  encodedPositiveWordCompatibilityModel
    (A := fun _c ↦ PositiveWord CWBlock (2 ^ depth - 1))
    (fun _c ↦ cwChunkSplitWord depth) partAt

@[simp] theorem cwExactInterfaceCompatibilityModel_chunks {Part : Type v}
    (depth n : ℕ) (partAt : Fin (n + 1) → Part) (c : Leg)
    (word : PositiveWord (PositiveWord CWBlock (2 ^ depth - 1)) n)
    (sample : Fin (n + 1)) :
    (cwExactInterfaceCompatibilityModel depth n partAt).chunks c word sample =
      cwChunkSplitWord depth
        (positiveWordEquiv (PositiveWord CWBlock (2 ^ depth - 1)) n word sample) :=
  rfl

/-- The concrete recursive CW model records exactly the three complete-split weights. -/
theorem cwExactInterfaceCompatibilityModel_hasCoarseWeights {Part : Type v}
    (depth n : ℕ) (partAt : Fin (n + 1) → Part)
    (address : BlockAddress (fun _c ↦
      PositiveWord (PositiveWord CWBlock (2 ^ depth - 1)) n)) :
    (cwExactInterfaceCompatibilityModel depth n partAt).HasCoarseWeights address :=
  encodedPositiveWordCompatibilityModel_hasCoarseWeights _ _ _

/-- Any block surviving an exact recursive CW interface-term selection is fine-legal. -/
theorem cwExactInterfaceCompatibilityModel_isFineLegal_of_mem_selected_support
    (K : Type u) [CommRing K] (q : ℕ) {Part : Type v} {depth n : ℕ}
    (partAt : Fin (n + 1) → Part) (term : ExactInterfaceTermParameters depth)
    (hmultiplicity : term.multiplicity = n + 1)
    (address : BlockAddress (fun _c ↦
      PositiveWord (PositiveWord CWBlock (2 ^ depth - 1)) n))
    (haddress : address ∈ (cwSelectedExactInterfaceTerm K q term hmultiplicity).support) :
    (cwExactInterfaceCompatibilityModel depth n partAt).IsFineLegal address := by
  exact
    encodedPositiveWordCompatibilityModel_isFineLegal_of_mem_exactInterfaceTerm_support
      (cwChunkPartitionedTensor K q depth) (fun _c ↦ cwChunkSplitWord depth) partAt
      (cwChunkPartitionedTensor_isEncodedFineLegalOnSupport K q depth)
      term hmultiplicity address haddress

/-! ## Paper compatibility profiles and oriented cleanup -/

/-- Fine legality of a selected CW interface address is invariant under an arbitrary region
orientation.  This is not an additional symmetry assumption on the selected profile: it follows
because the three physical leg digits are merely permuted inside their sum. -/
theorem cwExactInterfaceCompatibilityModel_isFineLegal_logicalAddress_of_mem_selected_support
    (K : Type u) [CommRing K] (q : ℕ) {Part : Type v} {depth n : ℕ}
    (partAt : Fin (n + 1) → Part) (term : ExactInterfaceTermParameters depth)
    (hmultiplicity : term.multiplicity = n + 1) (sigma : Orientation)
    (address : BlockAddress (fun _c ↦
      PositiveWord (PositiveWord CWBlock (2 ^ depth - 1)) n))
    (haddress : address ∈ (cwSelectedExactInterfaceTerm K q term hmultiplicity).support) :
    (cwExactInterfaceCompatibilityModel depth n partAt).IsFineLegal
      (logicalAddress sigma address) := by
  let model := cwExactInterfaceCompatibilityModel depth n partAt
  have hphysical : model.IsFineLegal address :=
    cwExactInterfaceCompatibilityModel_isFineLegal_of_mem_selected_support
      K q partAt term hmultiplicity address haddress
  intro sample position
  have hsum :
      (∑ c : Leg,
        ((model.chunks c (address c) sample position : SplitDigit) : ℕ)) = 2 := by
    simpa [Tensor.sum_leg] using hphysical sample position
  have hperm :
      (∑ c : Leg,
        ((model.chunks c (address (sigma c)) sample position : SplitDigit) : ℕ)) =
      ∑ c : Leg,
        ((model.chunks c (address c) sample position : SplitDigit) : ℕ) := by
    change
      (∑ c : Leg,
        ((cwChunkSplitWord depth
          (positiveWordEquiv (PositiveWord CWBlock (2 ^ depth - 1)) n
            (address (sigma c)) sample) position : SplitDigit) : ℕ)) =
      ∑ c : Leg,
        ((cwChunkSplitWord depth
          (positiveWordEquiv (PositiveWord CWBlock (2 ^ depth - 1)) n
            (address c) sample) position : SplitDigit) : ℕ)
    exact Equiv.sum_comp sigma
      (fun c : Leg ↦
        ((cwChunkSplitWord depth
          (positiveWordEquiv (PositiveWord CWBlock (2 ^ depth - 1)) n
            (address c) sample) position : SplitDigit) : ℕ))
  have hlogicalSum :
      (∑ c : Leg,
        ((model.chunks c ((logicalAddress sigma address) c) sample position :
          SplitDigit) : ℕ)) = 2 := by
    simpa only [logicalAddress_apply] using hperm.trans hsum
  change
    ((model.chunks .X ((logicalAddress sigma address) .X) sample position :
          SplitDigit) : ℕ) +
        ((model.chunks .Y ((logicalAddress sigma address) .Y) sample position :
          SplitDigit) : ℕ) +
      ((model.chunks .Z ((logicalAddress sigma address) .Z) sample position :
        SplitDigit) : ℕ) = 2
  simpa only [Tensor.sum_leg] using hlogicalSum

/-- The profile equations supplied at the paper's first `Y` compatibility zero-out.  Semantic
fine legality and coarse-weight correctness are intentionally absent: for selected CW interface
terms they are theorems, not certificate obligations. -/
def CWPooledAllYProfileMatches {Part : Type v} [DecidableEq Part] {depth n : ℕ}
    (sigma : Orientation) (partAt : Fin (n + 1) → Part)
    (targets : CompatibilityTargets Part depth) (pooled : PooledAllTargets targets)
    (address : BlockAddress (fun _c ↦
      PositiveWord (PositiveWord CWBlock (2 ^ depth - 1)) n)) : Prop :=
  let model := cwExactInterfaceCompatibilityModel depth n partAt
  let logical := logicalAddress sigma address
  model.MatchesExact logical .X targets.xExact ∧
    model.MatchesYPooledAll logical pooled.yAll

/-- The profile equations supplied at the later paper `Z` compatibility zero-out, after useful
`Y` blocks have their exact constituent profiles. -/
def CWPooledAllZProfileMatches {Part : Type v} [DecidableEq Part] {depth n : ℕ}
    (sigma : Orientation) (partAt : Fin (n + 1) → Part)
    (targets : CompatibilityTargets Part depth) (pooled : PooledAllTargets targets)
    (address : BlockAddress (fun _c ↦
      PositiveWord (PositiveWord CWBlock (2 ^ depth - 1)) n)) : Prop :=
  let model := cwExactInterfaceCompatibilityModel depth n partAt
  let logical := logicalAddress sigma address
  model.MatchesExact logical .X targets.xExact ∧
    model.MatchesExact logical .Y targets.yExact ∧
    model.MatchesZPooledAll logical pooled.zAll

/-- The concrete selected CW representation turns the paper's `Y` profile equations into the
complete pooled-all zero-out invariant. -/
theorem cwExactInterfaceCompatibilityModel_passesYPooledAllZeroOut
    (K : Type u) [CommRing K] (q : ℕ) {Part : Type v} [DecidableEq Part]
    {depth n : ℕ} (partAt : Fin (n + 1) → Part)
    (term : ExactInterfaceTermParameters depth)
    (hmultiplicity : term.multiplicity = n + 1)
    (sigma : Orientation) (targets : CompatibilityTargets Part depth)
    (pooled : PooledAllTargets targets)
    (address : BlockAddress (fun _c ↦
      PositiveWord (PositiveWord CWBlock (2 ^ depth - 1)) n))
    (haddress : address ∈ (cwSelectedExactInterfaceTerm K q term hmultiplicity).support)
    (hprofiles : CWPooledAllYProfileMatches sigma partAt targets pooled address) :
    (cwExactInterfaceCompatibilityModel depth n partAt).PassesYPooledAllZeroOut
      targets pooled (logicalAddress sigma address) := by
  rcases hprofiles with ⟨hX, hYAll⟩
  exact
    ⟨cwExactInterfaceCompatibilityModel_isFineLegal_logicalAddress_of_mem_selected_support
        K q partAt term hmultiplicity sigma address haddress,
      cwExactInterfaceCompatibilityModel_hasCoarseWeights depth n partAt _, hX, hYAll⟩

/-- The analogous concrete bridge for the paper's `Z` profile equations. -/
theorem cwExactInterfaceCompatibilityModel_passesZPooledAllZeroOut
    (K : Type u) [CommRing K] (q : ℕ) {Part : Type v} [DecidableEq Part]
    {depth n : ℕ} (partAt : Fin (n + 1) → Part)
    (term : ExactInterfaceTermParameters depth)
    (hmultiplicity : term.multiplicity = n + 1)
    (sigma : Orientation) (targets : CompatibilityTargets Part depth)
    (pooled : PooledAllTargets targets)
    (address : BlockAddress (fun _c ↦
      PositiveWord (PositiveWord CWBlock (2 ^ depth - 1)) n))
    (haddress : address ∈ (cwSelectedExactInterfaceTerm K q term hmultiplicity).support)
    (hprofiles : CWPooledAllZProfileMatches sigma partAt targets pooled address) :
    (cwExactInterfaceCompatibilityModel depth n partAt).PassesZPooledAllZeroOut
      targets pooled (logicalAddress sigma address) := by
  rcases hprofiles with ⟨hX, hY, hZAll⟩
  exact
    ⟨cwExactInterfaceCompatibilityModel_isFineLegal_logicalAddress_of_mem_selected_support
        K q partAt term hmultiplicity sigma address haddress,
      cwExactInterfaceCompatibilityModel_hasCoarseWeights depth n partAt _, hX, hY, hZAll⟩

/-- Concrete arbitrary-orientation form of the paper's `Y` compatibility claim on any support
contained in a selected exact CW interface term. -/
theorem cwSelectedExactInterfaceTerm_orientedYCompatibility_sound
    (K : Type u) [CommRing K] (q : ℕ) {Part : Type v} [DecidableEq Part]
    {depth n : ℕ} (partAt : Fin (n + 1) → Part)
    (term : ExactInterfaceTermParameters depth)
    (hmultiplicity : term.multiplicity = n + 1)
    (sigma : Orientation) (targets : CompatibilityTargets Part depth)
    (pooled : PooledAllTargets targets)
    (ambient : Finset (BlockAddress (fun _c ↦
      PositiveWord (PositiveWord CWBlock (2 ^ depth - 1)) n)))
    (hambient : ambient ⊆
      (cwSelectedExactInterfaceTerm K q term hmultiplicity).support)
    (hprofiles : ∀ address ∈ ambient,
      CWPooledAllYProfileMatches sigma partAt targets pooled address) :
    IsCompatibilitySound ambient (sigma .Y)
      (OrientedCompatibleY
        (A := fun _c ↦ PositiveWord (PositiveWord CWBlock (2 ^ depth - 1)) n)
        sigma (cwExactInterfaceCompatibilityModel depth n partAt) targets) := by
  apply CompatibilityModel.orientedYCompatibility_sound
    (A := fun _c ↦ PositiveWord (PositiveWord CWBlock (2 ^ depth - 1)) n)
    sigma (cwExactInterfaceCompatibilityModel depth n partAt) targets
  intro address haddress
  apply CompatibilityModel.passesYFirstZeroOut_of_pooledAll
  exact cwExactInterfaceCompatibilityModel_passesYPooledAllZeroOut
    K q partAt term hmultiplicity sigma targets pooled address
      (hambient haddress) (hprofiles address haddress)

/-- Concrete arbitrary-orientation form of the later paper `Z` compatibility claim. -/
theorem cwSelectedExactInterfaceTerm_orientedZCompatibility_sound
    (K : Type u) [CommRing K] (q : ℕ) {Part : Type v} [DecidableEq Part]
    {depth n : ℕ} (partAt : Fin (n + 1) → Part)
    (term : ExactInterfaceTermParameters depth)
    (hmultiplicity : term.multiplicity = n + 1)
    (sigma : Orientation) (targets : CompatibilityTargets Part depth)
    (pooled : PooledAllTargets targets)
    (ambient : Finset (BlockAddress (fun _c ↦
      PositiveWord (PositiveWord CWBlock (2 ^ depth - 1)) n)))
    (hambient : ambient ⊆
      (cwSelectedExactInterfaceTerm K q term hmultiplicity).support)
    (hprofiles : ∀ address ∈ ambient,
      CWPooledAllZProfileMatches sigma partAt targets pooled address) :
    IsCompatibilitySound ambient (sigma .Z)
      (OrientedCompatibleZ
        (A := fun _c ↦ PositiveWord (PositiveWord CWBlock (2 ^ depth - 1)) n)
        sigma (cwExactInterfaceCompatibilityModel depth n partAt) targets) := by
  apply CompatibilityModel.orientedZCompatibility_sound
    (A := fun _c ↦ PositiveWord (PositiveWord CWBlock (2 ^ depth - 1)) n)
    sigma (cwExactInterfaceCompatibilityModel depth n partAt) targets
  intro address haddress
  apply CompatibilityModel.passesZFirstZeroOut_of_pooledAll
  exact cwExactInterfaceCompatibilityModel_passesZPooledAllZeroOut
    K q partAt term hmultiplicity sigma targets pooled address
      (hambient haddress) (hprofiles address haddress)

/-- End-to-end exact compatibility cleanup for an arbitrary hash-isolated subset of one selected
CW interface term.  The `Y` profile equations are required on that ambient support, while the
later `Z` equations are required only on the support left by `Y` compatibility isolation.  The
output is a genuine indexed tensor direct sum. -/
theorem cwSelectedExactInterfaceTerm_orientedCompatibilityCleanup_to_indexedDirectSum
    (K : Type u) [CommRing K] (q : ℕ) {Part : Type v} [DecidableEq Part]
    {depth n : ℕ} (partAt : Fin (n + 1) → Part)
    (term : ExactInterfaceTermParameters depth)
    (hmultiplicity : term.multiplicity = n + 1)
    (sigma : Orientation) (targets : CompatibilityTargets Part depth)
    (pooled : PooledAllTargets targets)
    (ambient : Finset (BlockAddress (fun _c ↦
      PositiveWord (PositiveWord CWBlock (2 ^ depth - 1)) n)))
    (hambient : ambient ⊆
      (cwSelectedExactInterfaceTerm K q term hmultiplicity).support)
    (hX : Set.InjOn
      (fun address : BlockAddress (fun _c ↦
        PositiveWord (PositiveWord CWBlock (2 ^ depth - 1)) n) ↦
          address (sigma .X))
      ambient)
    (hYProfiles : ∀ address ∈ ambient,
        CWPooledAllYProfileMatches sigma partAt targets pooled address)
    (hZProfiles : ∀ address ∈
      compatibilityIsolatedSupport
        ambient (sigma .Y)
        (OrientedCompatibleY
          (A := fun _c ↦ PositiveWord (PositiveWord CWBlock (2 ^ depth - 1)) n)
          sigma (cwExactInterfaceCompatibilityModel depth n partAt) targets),
        CWPooledAllZProfileMatches sigma partAt targets pooled address) :
    let selected := cwSelectedExactInterfaceTerm K q term hmultiplicity
    let hashed := selected.withSupport ambient
    let model := cwExactInterfaceCompatibilityModel depth n partAt
    let ySupport := compatibilityIsolatedSupport ambient (sigma .Y)
      (OrientedCompatibleY
        (A := fun _c ↦ PositiveWord (PositiveWord CWBlock (2 ^ depth - 1)) n)
        sigma model targets)
    let zSupport := compatibilityIsolatedSupport ySupport (sigma .Z)
      (OrientedCompatibleZ
        (A := fun _c ↦ PositiveWord (PositiveWord CWBlock (2 ^ depth - 1)) n)
        sigma model targets)
    Restricts hashed.realize
      (indexedDirectSum (fun address : zSupport ↦ hashed.constituent address.1)) := by
  let selected := cwSelectedExactInterfaceTerm K q term hmultiplicity
  let hashed := selected.withSupport ambient
  let model := cwExactInterfaceCompatibilityModel depth n partAt
  let compatibleY := OrientedCompatibleY
    (A := fun _c ↦ PositiveWord (PositiveWord CWBlock (2 ^ depth - 1)) n)
    sigma model targets
  let compatibleZ := OrientedCompatibleZ
    (A := fun _c ↦ PositiveWord (PositiveWord CWBlock (2 ^ depth - 1)) n)
    sigma model targets
  let ySupport := compatibilityIsolatedSupport ambient (sigma .Y) compatibleY
  have hsoundY : IsCompatibilitySound ambient (sigma .Y) compatibleY := by
    exact cwSelectedExactInterfaceTerm_orientedYCompatibility_sound
      K q partAt term hmultiplicity sigma targets pooled ambient hambient hYProfiles
  have hsoundZ : IsCompatibilitySound ySupport (sigma .Z) compatibleZ := by
    exact cwSelectedExactInterfaceTerm_orientedZCompatibility_sound
      K q partAt term hmultiplicity sigma targets pooled ySupport
        (fun _ haddress ↦ hambient
          (compatibilityIsolatedSupport_subset ambient (sigma .Y) compatibleY haddress))
        hZProfiles
  exact partitionedOrientedYZCompatibilityCleanup_to_indexedDirectSum
    sigma hashed hX compatibleY hsoundY compatibleZ hsoundZ

end AlgebraicComplexity.Examples
