/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinogradCompatibilityTargetRepair
import AlgebraicComplexity.Examples.CoppersmithWinogradTotalWeightIsolatedSupport
import AlgebraicComplexity.Examples.CoppersmithWinogradTotalWeightQuotientCompatibility

/-!
# Total-weight extraction clients for one full tagged cell type

The total-weight quotient cleanup deliberately takes its semantic pass equations from a client.
This module supplies those equations for the family selected by one full tagged empirical cell
type.  Equality of full cell multiplicities gives a concrete common position permutation; the
proof uses that permutation to transport exact and pooled cell counts from the reference address
to every selected address.

The only remaining semantic datum is `CWTotalWeightReferenceProfiles`: the four profile equations
at the chosen reference itself.  Later occurrence clients identify those empirical profiles with
the committed recursive target tables.  No count, entropy estimate, hashing rate, or generated
certificate datum is used here.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor MoreAsymmetryCompatibility

universe u v w

/-- Applying any deterministic cell projection to a full tagged cell type preserves its joint
multiplicity with one total-weight leg word.

The position permutation is the explicit decoder witnessing the transport: it simultaneously
reindexes the full coarse cell and the chosen leg symbol. -/
theorem cwTotalWeightCellMultiplicity_eq_of_fullCellType
    {Part : Type v} [Fintype Part] [DecidableEq Part]
    {Cell : Type w} [DecidableEq Cell]
    (depth n : ℕ) (partAt : Fin (n + 1) → Part)
    (reference address : BlockAddress
      (fun _c ↦ PositiveWord (CWCoarseDigit depth) n))
    (hsame : WordType.multiplicity
        (cwOrientedFiniteCellSequence depth n partAt (Equiv.refl Leg) reference) =
      WordType.multiplicity
        (cwOrientedFiniteCellSequence depth n partAt (Equiv.refl Leg) address))
    (cellOf : CoarseIndex Part → Cell) (c : Leg) (cell : Cell)
    (symbol : CWCoarseDigit depth) :
    let model := cwTotalWeightFeatureCompatibilityModel depth n partAt
    cellMultiplicity (fun sample ↦ cellOf (model.coarse address sample))
        (model.symbols c (address c)) cell symbol =
      cellMultiplicity (fun sample ↦ cellOf (model.coarse reference sample))
        (model.symbols c (reference c)) cell symbol := by
  classical
  let model := cwTotalWeightFeatureCompatibilityModel depth n partAt
  let tau := cwOrientedCellPositionPermOfSameMultiplicity
    depth n partAt (Equiv.refl Leg) reference address hsame
  have hfull :
      cwOrientedFiniteCellSequence depth n partAt (Equiv.refl Leg) address ∘ tau =
        cwOrientedFiniteCellSequence depth n partAt (Equiv.refl Leg) reference :=
    cwOrientedCoarseIndexSequence_positionPermOfSameMultiplicity
      depth n partAt (Equiv.refl Leg) reference address hsame
  have hcoarse : model.coarse address ∘ tau = model.coarse reference := by
    funext sample
    have hsample := congrArg cwOrientedCoarseCellToIndex (congrFun hfull sample)
    simpa [model, cwTotalWeightFeatureCompatibilityModel,
      cwOrientedFiniteCellSequence, cwOrientedCoarseCellToIndex,
      Function.comp_apply] using hsample
  have hsymbols :
      model.symbols c (address c) ∘ tau = model.symbols c (reference c) := by
    funext sample
    have hsample := congrArg (fun q ↦ q.2 c) (congrFun hfull sample)
    simpa [model, cwTotalWeightFeatureCompatibilityModel,
      cwOrientedFiniteCellSequence, Function.comp_apply] using hsample
  have hcells :
      (fun sample ↦ cellOf (model.coarse address sample)) ∘ tau =
        fun sample ↦ cellOf (model.coarse reference sample) := by
    funext sample
    exact congrArg cellOf (congrFun hcoarse sample)
  calc
    cellMultiplicity (fun sample ↦ cellOf (model.coarse address sample))
        (model.symbols c (address c)) cell symbol =
      cellMultiplicity
          ((fun sample ↦ cellOf (model.coarse address sample)) ∘ tau)
          ((model.symbols c (address c)) ∘ tau) cell symbol :=
        (cellMultiplicity_comp_perm
          (fun sample ↦ cellOf (model.coarse address sample))
          (model.symbols c (address c)) tau cell symbol).symm
    _ = cellMultiplicity (fun sample ↦ cellOf (model.coarse reference sample))
          (model.symbols c (reference c)) cell symbol := by
        rw [hcells, hsymbols]

/-- Exact profiles are constant on one full tagged empirical cell type. -/
theorem cwTotalWeightMatchesExact_of_fullCellType
    {Part : Type v} [Fintype Part] [DecidableEq Part]
    (depth n : ℕ) (partAt : Fin (n + 1) → Part)
    (reference address : BlockAddress
      (fun _c ↦ PositiveWord (CWCoarseDigit depth) n))
    (hsame : WordType.multiplicity
        (cwOrientedFiniteCellSequence depth n partAt (Equiv.refl Leg) reference) =
      WordType.multiplicity
        (cwOrientedFiniteCellSequence depth n partAt (Equiv.refl Leg) address))
    (c : Leg) (profile : CoarseIndex Part → CWCoarseDigit depth → ℕ)
    (hreference :
      (cwTotalWeightFeatureCompatibilityModel depth n partAt).MatchesExact
        reference c profile) :
    (cwTotalWeightFeatureCompatibilityModel depth n partAt).MatchesExact
      address c profile := by
  intro cell symbol
  exact (cwTotalWeightCellMultiplicity_eq_of_fullCellType
    depth n partAt reference address hsame (fun q ↦ q) c cell symbol).trans
      (hreference cell symbol)

/-- The pooled `Y` profile is constant on one full tagged empirical cell type. -/
theorem cwTotalWeightYPooled_of_fullCellType
    {Part : Type v} [Fintype Part] [DecidableEq Part]
    (depth n : ℕ) (partAt : Fin (n + 1) → Part)
    (reference address : BlockAddress
      (fun _c ↦ PositiveWord (CWCoarseDigit depth) n))
    (hsame : WordType.multiplicity
        (cwOrientedFiniteCellSequence depth n partAt (Equiv.refl Leg) reference) =
      WordType.multiplicity
        (cwOrientedFiniteCellSequence depth n partAt (Equiv.refl Leg) address))
    (profile : Part → ℕ → CWCoarseDigit depth → ℕ)
    (hreference : ∀ part y symbol,
      let model := cwTotalWeightFeatureCompatibilityModel depth n partAt
      cellMultiplicity
          (fun sample ↦ yCompatibilityCell (model.coarse reference sample))
          (model.symbols .Y (reference .Y)) (.pooled part y) symbol =
        profile part y symbol) :
    ∀ part y symbol,
      let model := cwTotalWeightFeatureCompatibilityModel depth n partAt
      cellMultiplicity
          (fun sample ↦ yCompatibilityCell (model.coarse address sample))
          (model.symbols .Y (address .Y)) (.pooled part y) symbol =
        profile part y symbol := by
  intro part y symbol
  exact (cwTotalWeightCellMultiplicity_eq_of_fullCellType
    depth n partAt reference address hsame yCompatibilityCell .Y
      (.pooled part y) symbol).trans (hreference part y symbol)

/-- The pooled `Z` profile is constant on one full tagged empirical cell type. -/
theorem cwTotalWeightZPooled_of_fullCellType
    {Part : Type v} [Fintype Part] [DecidableEq Part]
    (depth n : ℕ) (partAt : Fin (n + 1) → Part)
    (reference address : BlockAddress
      (fun _c ↦ PositiveWord (CWCoarseDigit depth) n))
    (hsame : WordType.multiplicity
        (cwOrientedFiniteCellSequence depth n partAt (Equiv.refl Leg) reference) =
      WordType.multiplicity
        (cwOrientedFiniteCellSequence depth n partAt (Equiv.refl Leg) address))
    (profile : Part → ℕ → CWCoarseDigit depth → ℕ)
    (hreference : ∀ part z symbol,
      let model := cwTotalWeightFeatureCompatibilityModel depth n partAt
      cellMultiplicity
          (fun sample ↦ zCompatibilityCell (model.coarse reference sample))
          (model.symbols .Z (reference .Z)) (.pooled part z) symbol =
        profile part z symbol) :
    ∀ part z symbol,
      let model := cwTotalWeightFeatureCompatibilityModel depth n partAt
      cellMultiplicity
          (fun sample ↦ zCompatibilityCell (model.coarse address sample))
          (model.symbols .Z (address .Z)) (.pooled part z) symbol =
        profile part z symbol := by
  intro part z symbol
  exact (cwTotalWeightCellMultiplicity_eq_of_fullCellType
    depth n partAt reference address hsame zCompatibilityCell .Z
      (.pooled part z) symbol).trans (hreference part z symbol)

/-- The exact reference-address equations that a recursive occurrence client must identify with
the pushed total-weight target tables.  This single predicate is the honest semantic seam between
the occurrence cone and the generic fixed-cell transport proved in this module. -/
structure CWTotalWeightReferenceProfiles
    {Part : Type v} [DecidableEq Part]
    (depth n : ℕ) (partAt : Fin (n + 1) → Part)
    (rawTargets : CompatibilityTargets Part depth)
    (reference : BlockAddress
      (fun _c ↦ PositiveWord (CWCoarseDigit depth) n)) : Prop where
  matchesX :
    (cwTotalWeightFeatureCompatibilityModel depth n partAt).MatchesExact reference .X
      (cwTotalWeightPushforwardTargets rawTargets).xExact
  matchesY :
    (cwTotalWeightFeatureCompatibilityModel depth n partAt).MatchesExact reference .Y
      (cwTotalWeightPushforwardTargets rawTargets).yExact
  pooledY : ∀ part y symbol,
    let model := cwTotalWeightFeatureCompatibilityModel depth n partAt
    cellMultiplicity
        (fun sample ↦ yCompatibilityCell (model.coarse reference sample))
        (model.symbols .Y (reference .Y)) (.pooled part y) symbol =
      (cwTotalWeightPushforwardTargets rawTargets).yPooled part y symbol
  pooledZ : ∀ part z symbol,
    let model := cwTotalWeightFeatureCompatibilityModel depth n partAt
    cellMultiplicity
        (fun sample ↦ zCompatibilityCell (model.coarse reference sample))
        (model.symbols .Z (reference .Z)) (.pooled part z) symbol =
      (cwTotalWeightPushforwardTargets rawTargets).zPooled part z symbol

/-- Selecting one full tagged type only removes addresses from the upstream family. -/
theorem cwFixedTargetCellTypeCoarseSupport_subset
    {Part : Type v} [Fintype Part] [DecidableEq Part]
    (depth n : ℕ) (partAt : Fin (n + 1) → Part)
    (coarseKept : Finset (BlockAddress
      (fun _c ↦ PositiveWord (CWCoarseDigit depth) n)))
    (reference : BlockAddress
      (fun _c ↦ PositiveWord (CWCoarseDigit depth) n)) :
    cwFixedTargetCellTypeCoarseSupport
        depth n partAt (Equiv.refl Leg) coarseKept reference ⊆ coarseKept := by
  intro address haddress
  exact ((mem_cwFixedTargetCellTypeCoarseSupport_iff
    depth n partAt (Equiv.refl Leg) coarseKept reference address).mp haddress).1

/-- A reference belonging to the upstream family belongs to its own selected full tagged type. -/
theorem cwReference_mem_fixedTargetCellTypeCoarseSupport
    {Part : Type v} [Fintype Part] [DecidableEq Part]
    (depth n : ℕ) (partAt : Fin (n + 1) → Part)
    (coarseKept : Finset (BlockAddress
      (fun _c ↦ PositiveWord (CWCoarseDigit depth) n)))
    (reference : BlockAddress
      (fun _c ↦ PositiveWord (CWCoarseDigit depth) n))
    (hreference : reference ∈ coarseKept) :
    reference ∈ cwFixedTargetCellTypeCoarseSupport
      depth n partAt (Equiv.refl Leg) coarseKept reference := by
  rw [mem_cwFixedTargetCellTypeCoarseSupport_iff]
  exact ⟨hreference, rfl⟩

/-- Reference profiles supply the exact `X` and pooled-`Y` equations on the entire selected full
cell type. -/
theorem cwTotalWeightFixedTargetCellType_passesY
    {Part : Type v} [Fintype Part] [DecidableEq Part]
    (depth n : ℕ) (partAt : Fin (n + 1) → Part)
    (rawTargets : CompatibilityTargets Part depth)
    (coarseKept : Finset (BlockAddress
      (fun _c ↦ PositiveWord (CWCoarseDigit depth) n)))
    (reference : BlockAddress
      (fun _c ↦ PositiveWord (CWCoarseDigit depth) n))
    (hreference : CWTotalWeightReferenceProfiles
      depth n partAt rawTargets reference) :
    ∀ address ∈ cwFixedTargetCellTypeCoarseSupport
        depth n partAt (Equiv.refl Leg) coarseKept reference,
      let model := cwTotalWeightFeatureCompatibilityModel depth n partAt
      let targets := cwTotalWeightPushforwardTargets rawTargets
      model.MatchesExact address .X targets.xExact ∧
        ∀ part y symbol,
          cellMultiplicity
              (fun sample ↦ yCompatibilityCell (model.coarse address sample))
              (model.symbols .Y (address .Y)) (.pooled part y) symbol =
            targets.yPooled part y symbol := by
  intro address haddress
  have hsame := ((mem_cwFixedTargetCellTypeCoarseSupport_iff
    depth n partAt (Equiv.refl Leg) coarseKept reference address).mp haddress).2
  exact ⟨
    cwTotalWeightMatchesExact_of_fullCellType
      depth n partAt reference address hsame .X _ hreference.matchesX,
    cwTotalWeightYPooled_of_fullCellType
      depth n partAt reference address hsame _ hreference.pooledY⟩

/-- The same full-cell membership survives the `Y` isolation, so reference profiles also supply
the exact `X/Y` and pooled-`Z` equations needed by the second pass. -/
theorem cwTotalWeightFixedTargetCellType_passesZ
    {Part : Type v} [Fintype Part] [DecidableEq Part]
    (depth n : ℕ) (partAt : Fin (n + 1) → Part)
    (rawTargets : CompatibilityTargets Part depth)
    (coarseKept : Finset (BlockAddress
      (fun _c ↦ PositiveWord (CWCoarseDigit depth) n)))
    (reference : BlockAddress
      (fun _c ↦ PositiveWord (CWCoarseDigit depth) n))
    (hreference : CWTotalWeightReferenceProfiles
      depth n partAt rawTargets reference) :
    ∀ address ∈ compatibilityIsolatedSupport
        (cwFixedTargetCellTypeCoarseSupport
          depth n partAt (Equiv.refl Leg) coarseKept reference)
        .Y (cwTotalWeightCompatibilityY depth n partAt rawTargets),
      let model := cwTotalWeightFeatureCompatibilityModel depth n partAt
      let targets := cwTotalWeightPushforwardTargets rawTargets
      model.MatchesExact address .X targets.xExact ∧
        model.MatchesExact address .Y targets.yExact ∧
        ∀ part z symbol,
          cellMultiplicity
              (fun sample ↦ zCompatibilityCell (model.coarse address sample))
              (model.symbols .Z (address .Z)) (.pooled part z) symbol =
            targets.zPooled part z symbol := by
  intro address haddress
  have hselected : address ∈ cwFixedTargetCellTypeCoarseSupport
      depth n partAt (Equiv.refl Leg) coarseKept reference :=
    compatibilityIsolatedSupport_subset _ .Y _ haddress
  have hsame := ((mem_cwFixedTargetCellTypeCoarseSupport_iff
    depth n partAt (Equiv.refl Leg) coarseKept reference address).mp hselected).2
  exact ⟨
    cwTotalWeightMatchesExact_of_fullCellType
      depth n partAt reference address hsame .X _ hreference.matchesX,
    cwTotalWeightMatchesExact_of_fullCellType
      depth n partAt reference address hsame .Y _ hreference.matchesY,
    cwTotalWeightZPooled_of_fullCellType
      depth n partAt reference address hsame _ hreference.pooledZ⟩

/-- A supported, `X`-injective upstream family remains supported and `X`-injective after selecting
one full tagged type. -/
theorem cwTotalWeightFixedTargetCellType_clientSupport
    (K : Type u) [CommRing K] (q depth n : ℕ)
    {Part : Type v} [Fintype Part] [DecidableEq Part]
    (partAt : Fin (n + 1) → Part)
    (coarseKept : Finset (BlockAddress
      (fun _c ↦ PositiveWord (CWCoarseDigit depth) n)))
    (hcoarseKept : coarseKept ⊆
      (((cwChunkPartitionedTensor K q depth).coarsen
        (cwTotalWeightChunkCoarsening depth)).positivePower n).support)
    (hX : Set.InjOn
      (fun address : BlockAddress
        (fun _c ↦ PositiveWord (CWCoarseDigit depth) n) ↦ address .X) coarseKept)
    (reference : BlockAddress
      (fun _c ↦ PositiveWord (CWCoarseDigit depth) n)) :
    let selected := cwFixedTargetCellTypeCoarseSupport
      depth n partAt (Equiv.refl Leg) coarseKept reference
    selected ⊆
        (((cwChunkPartitionedTensor K q depth).coarsen
          (cwTotalWeightChunkCoarsening depth)).positivePower n).support ∧
      Set.InjOn
        (fun address : BlockAddress
          (fun _c ↦ PositiveWord (CWCoarseDigit depth) n) ↦ address .X) selected := by
  let selected := cwFixedTargetCellTypeCoarseSupport
    depth n partAt (Equiv.refl Leg) coarseKept reference
  have hsubset : selected ⊆ coarseKept :=
    cwFixedTargetCellTypeCoarseSupport_subset
      depth n partAt coarseKept reference
  exact ⟨hsubset.trans hcoarseKept, hX.mono hsubset⟩

/-- **C2 local monotone-transfer client.**  On a supported, `X`-injective upstream family,
selecting the full tagged type of a reference address transports support and `X`-injectivity and
supplies the two profile-pass equations for the total-weight quotient cleanup.  This theorem starts
at the selected tensor; the full-support `X` pass is composed by the stronger client below. -/
theorem cwTotalWeightFixedTargetCellTypeYZCompatibilityCleanup_to_indexedDirectSum
    (K : Type u) [CommRing K] (q depth n : ℕ)
    {Part : Type v} [Fintype Part] [DecidableEq Part]
    (partAt : Fin (n + 1) → Part)
    (rawTargets : CompatibilityTargets Part depth)
    (coarseKept : Finset (BlockAddress
      (fun _c ↦ PositiveWord (CWCoarseDigit depth) n)))
    (hcoarseKept : coarseKept ⊆
      (((cwChunkPartitionedTensor K q depth).coarsen
        (cwTotalWeightChunkCoarsening depth)).positivePower n).support)
    (hX : Set.InjOn
      (fun address : BlockAddress
        (fun _c ↦ PositiveWord (CWCoarseDigit depth) n) ↦ address .X) coarseKept)
    (reference : BlockAddress
      (fun _c ↦ PositiveWord (CWCoarseDigit depth) n))
    (hreference : CWTotalWeightReferenceProfiles
      depth n partAt rawTargets reference) :
    let ambient := cwFixedTargetCellTypeCoarseSupport
      depth n partAt (Equiv.refl Leg) coarseKept reference
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
      (Tensor.indexedDirectSum
        (fun address : zSupport ↦ P.constituent address.1)) := by
  let ambient := cwFixedTargetCellTypeCoarseSupport
    depth n partAt (Equiv.refl Leg) coarseKept reference
  have hclient := cwTotalWeightFixedTargetCellType_clientSupport
    K q depth n partAt coarseKept hcoarseKept hX reference
  exact cwTotalWeightFeatureYZCompatibilityCleanup_to_indexedDirectSum
    K q depth n partAt rawTargets ambient hclient.1 hclient.2
      (cwTotalWeightFixedTargetCellType_passesY
        depth n partAt rawTargets coarseKept reference hreference)
      (cwTotalWeightFixedTargetCellType_passesZ
        depth n partAt rawTargets coarseKept reference hreference)

/-- **C2 nonvacuous full-power client.**  Compose an explicit upstream `X`-pass restriction with
full-cell selection and the two total-weight compatibility passes.  Supported targets plus
`Y`/`Z` injectivity make both compatibility isolations lossless, so the reference itself survives
and the resulting direct sum is nonempty.

The `hfull` premise is the exact boundary with the hash/counting construction: this module does not
claim that an arbitrary subset of the unrestricted positive power is a tensor restriction. -/
theorem cwTotalWeightFixedTargetCellTypeYZCompatibilityCleanup_from_fullPower
    (K : Type u) [CommRing K] (q depth n : ℕ)
    {Part : Type v} [Fintype Part] [DecidableEq Part]
    (partAt : Fin (n + 1) → Part)
    (rawTargets : CompatibilityTargets Part depth)
    (coarseKept : Finset (BlockAddress
      (fun _c ↦ PositiveWord (CWCoarseDigit depth) n)))
    (hcoarseKept : coarseKept ⊆
      (((cwChunkPartitionedTensor K q depth).coarsen
        (cwTotalWeightChunkCoarsening depth)).positivePower n).support)
    (hfull :
      let Q := (cwChunkPartitionedTensor K q depth).coarsen
        (cwTotalWeightChunkCoarsening depth)
      Restricts (Q.positivePower n).realize
        ((Q.positivePower n).withSupport coarseKept).realize)
    (hX : Set.InjOn
      (fun address : BlockAddress
        (fun _c ↦ PositiveWord (CWCoarseDigit depth) n) ↦ address .X) coarseKept)
    (hY : Set.InjOn
      (fun address : BlockAddress
        (fun _c ↦ PositiveWord (CWCoarseDigit depth) n) ↦ address .Y) coarseKept)
    (hZ : Set.InjOn
      (fun address : BlockAddress
        (fun _c ↦ PositiveWord (CWCoarseDigit depth) n) ↦ address .Z) coarseKept)
    (reference : BlockAddress
      (fun _c ↦ PositiveWord (CWCoarseDigit depth) n))
    (hreferenceMem : reference ∈ coarseKept)
    (hsupported : rawTargets.IsWeightSupported)
    (hreference : CWTotalWeightReferenceProfiles
      depth n partAt rawTargets reference) :
    let ambient := cwFixedTargetCellTypeCoarseSupport
      depth n partAt (Equiv.refl Leg) coarseKept reference
    let Q := (cwChunkPartitionedTensor K q depth).coarsen
      (cwTotalWeightChunkCoarsening depth)
    let P := (Q.positivePower n).withSupport ambient
    let model := cwTotalWeightFeatureCompatibilityModel depth n partAt
    let targets := cwTotalWeightPushforwardTargets rawTargets
    let ySupport := compatibilityIsolatedSupport ambient .Y
      (model.FeatureCompatibleY targets)
    let zSupport := compatibilityIsolatedSupport ySupport .Z
      (model.FeatureCompatibleZ targets)
    reference ∈ zSupport ∧
      Restricts (Q.positivePower n).realize
        (Tensor.indexedDirectSum
          (fun address : zSupport ↦ P.constituent address.1)) := by
  classical
  let ambient := cwFixedTargetCellTypeCoarseSupport
    depth n partAt (Equiv.refl Leg) coarseKept reference
  let Q := (cwChunkPartitionedTensor K q depth).coarsen
    (cwTotalWeightChunkCoarsening depth)
  let P := (Q.positivePower n).withSupport ambient
  let model := cwTotalWeightFeatureCompatibilityModel depth n partAt
  let targets := cwTotalWeightPushforwardTargets rawTargets
  let ySupport := compatibilityIsolatedSupport ambient .Y
    (model.FeatureCompatibleY targets)
  let zSupport := compatibilityIsolatedSupport ySupport .Z
    (model.FeatureCompatibleZ targets)
  have hambient : ambient ⊆ coarseKept :=
    cwFixedTargetCellTypeCoarseSupport_subset
      depth n partAt coarseKept reference
  have hYambient := hY.mono hambient
  have hZambient := hZ.mono hambient
  have hisolated : cwTotalWeightYZIsolatedSupport
      depth n partAt rawTargets ambient = ambient :=
    cwTotalWeightYZIsolatedSupport_eq_ambient_of_injOn
      depth n partAt rawTargets hsupported ambient hYambient hZambient
  have hreferenceAmbient : reference ∈ ambient :=
    cwReference_mem_fixedTargetCellTypeCoarseSupport
      depth n partAt coarseKept reference hreferenceMem
  have hreferenceFinal : reference ∈ zSupport := by
    change reference ∈ cwTotalWeightYZIsolatedSupport
      depth n partAt rawTargets ambient
    rw [hisolated]
    exact hreferenceAmbient
  have hselected : Restricts
      ((Q.positivePower n).withSupport coarseKept).realize P.realize := by
    apply Restricts.partitionedProjectionClosed
      ((Q.positivePower n).withSupport coarseKept) ambient {Leg.X}
    refine ⟨hambient, ?_⟩
    intro address haddress hlabels
    obtain ⟨selected, hselected, hlabel⟩ :=
      hlabels .X (Finset.mem_singleton_self _)
    have haddressEq : address = selected :=
      hX (Finset.mem_coe.mpr haddress)
        (Finset.mem_coe.mpr (hambient hselected)) hlabel
    rw [haddressEq]
    exact hselected
  have hcleanup : Restricts P.realize
      (Tensor.indexedDirectSum
        (fun address : zSupport ↦ P.constituent address.1)) := by
    simpa [ambient, Q, P, model, targets, ySupport, zSupport] using
      (cwTotalWeightFixedTargetCellTypeYZCompatibilityCleanup_to_indexedDirectSum
        K q depth n partAt rawTargets coarseKept hcoarseKept hX reference hreference)
  refine ⟨hreferenceFinal, ?_⟩
  exact hfull.trans (hselected.trans hcleanup)

end AlgebraicComplexity.Examples
