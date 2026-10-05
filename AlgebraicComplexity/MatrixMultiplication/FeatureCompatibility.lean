/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.MoreAsymmetryCompatibility

/-!
# Compatibility cleanup for quotient features

The ordinary complete-split compatibility theorem derives its boundary identities from
coordinatewise legality of raw split words.  A noninjective but globally consistent quotient need
not preserve that coordinatewise legality on chosen representatives.  What survives is the exact
relation that compatibility actually uses: on a boundary cell, the two quotient labels are
related by an induced involution.

This file isolates that weaker, reusable hypothesis.  The feature alphabet is arbitrary and the
three boundary relations are stated directly.  The resulting soundness theorems feed the existing
generic compatibility-zeroing and indexed-direct-sum machinery without changing it.
-/

namespace AlgebraicComplexity
namespace MoreAsymmetryCompatibility

open Tensor

universe u v w

/-- A compatibility model whose local symbols may be quotient features rather than raw
complete-split words. -/
structure FeatureCompatibilityModel (A : Leg → Type v) (Part : Type u)
    (Symbol : Type w) (samples : ℕ) where
  symbols : ∀ c, A c → Fin samples → Symbol
  coarse : BlockAddress A → Fin samples → CoarseIndex Part

/-- Exact target profiles for an arbitrary feature alphabet equipped with the induced boundary
involution. -/
structure FeatureCompatibilityTargets (Part : Type u) (Symbol : Type w) where
  complement : Equiv.Perm Symbol
  complement_symm : complement.symm = complement
  xExact : CoarseIndex Part → Symbol → ℕ
  yExact : CoarseIndex Part → Symbol → ℕ
  zExact : CoarseIndex Part → Symbol → ℕ
  yPooled : Part → ℕ → Symbol → ℕ
  zPooled : Part → ℕ → Symbol → ℕ
  yBoundary : ∀ q, q.z = 0 → ∀ symbol,
    yExact q symbol = xExact q (complement symbol)
  zBoundaryOfX : ∀ q, q.y = 0 → ∀ symbol,
    zExact q symbol = xExact q (complement symbol)
  zBoundaryOfY : ∀ q, q.x = 0 → ∀ symbol,
    zExact q symbol = yExact q (complement symbol)

namespace FeatureCompatibilityTargets

variable {Part : Type u} {Symbol : Type w}

/-- Prescribed profile of one concrete `Y` compatibility cell. -/
def yCellProfile (targets : FeatureCompatibilityTargets Part Symbol) :
    YCompatibilityCell Part → Symbol → ℕ
  | .boundary q => targets.yExact q.1
  | .pooled part y => targets.yPooled part y

/-- Prescribed profile of one concrete `Z` compatibility cell. -/
def zCellProfile (targets : FeatureCompatibilityTargets Part Symbol) :
    ZCompatibilityCell Part → Symbol → ℕ
  | .boundary q => targets.zExact q.1
  | .pooled part z => targets.zPooled part z

end FeatureCompatibilityTargets

/-- A pointwise equivalence on one cell transports exact empirical multiplicities. -/
theorem cellMultiplicity_equiv_on_cell
    {I Cell Left Right : Type*} [Fintype I]
    [DecidableEq Cell] [DecidableEq Left] [DecidableEq Right]
    (cellOf : I → Cell) (left : I → Left) (right : I → Right)
    (equiv : Left ≃ Right) (cell : Cell)
    (hrelation : ∀ position, cellOf position = cell →
      right position = equiv (left position))
    (symbol : Right) :
    cellMultiplicity cellOf right cell symbol =
      cellMultiplicity cellOf left cell (equiv.symm symbol) := by
  classical
  unfold cellMultiplicity
  congr 1
  ext position
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hcell, hsymbol⟩
    refine ⟨hcell, ?_⟩
    have h := hrelation position hcell
    rw [h] at hsymbol
    simpa using congrArg equiv.symm hsymbol
  · rintro ⟨hcell, hsymbol⟩
    refine ⟨hcell, ?_⟩
    rw [hrelation position hcell, hsymbol]
    simp

namespace FeatureCompatibilityModel

variable {A : Leg → Type v} {Part : Type u} {Symbol : Type w}
variable {samples : ℕ}

/-- On every cell with coarse `Z = 0`, the feature on `Y` is the induced complement of the
feature on `X`. -/
def HasYBoundaryRelation
    (model : FeatureCompatibilityModel A Part Symbol samples)
    (complement : Equiv.Perm Symbol) (address : BlockAddress A) : Prop :=
  ∀ sample, (model.coarse address sample).z = 0 →
    model.symbols .Y (address .Y) sample =
      complement (model.symbols .X (address .X) sample)

/-- The two boundary relations needed by the `Z` compatibility cleanup. -/
def HasZBoundaryRelations
    (model : FeatureCompatibilityModel A Part Symbol samples)
    (complement : Equiv.Perm Symbol) (address : BlockAddress A) : Prop :=
  (∀ sample, (model.coarse address sample).x = 0 →
    model.symbols .Z (address .Z) sample =
      complement (model.symbols .Y (address .Y) sample)) ∧
  (∀ sample, (model.coarse address sample).y = 0 →
    model.symbols .Z (address .Z) sample =
      complement (model.symbols .X (address .X) sample))

/-- Exact profile match on every individual coarse constituent cell. -/
def MatchesExact [DecidableEq Part] [DecidableEq Symbol]
    (model : FeatureCompatibilityModel A Part Symbol samples)
    (address : BlockAddress A) (c : Leg)
    (profile : CoarseIndex Part → Symbol → ℕ) : Prop :=
  ∀ q symbol,
    cellMultiplicity (model.coarse address) (model.symbols c (address c)) q symbol =
      profile q symbol

/-- Concrete `Y` compatibility on a quotient-feature alphabet. -/
def FeatureCompatibleY [DecidableEq Part] [DecidableEq Symbol]
    (model : FeatureCompatibilityModel A Part Symbol samples)
    (targets : FeatureCompatibilityTargets Part Symbol)
    (label : A .Y) (address : BlockAddress A) : Prop :=
  ∀ cell symbol,
    cellMultiplicity (fun sample ↦ yCompatibilityCell (model.coarse address sample))
        (model.symbols .Y label) cell symbol =
      targets.yCellProfile cell symbol

/-- Concrete `Z` compatibility on a quotient-feature alphabet. -/
def FeatureCompatibleZ [DecidableEq Part] [DecidableEq Symbol]
    (model : FeatureCompatibilityModel A Part Symbol samples)
    (targets : FeatureCompatibilityTargets Part Symbol)
    (label : A .Z) (address : BlockAddress A) : Prop :=
  ∀ cell symbol,
    cellMultiplicity (fun sample ↦ zCompatibilityCell (model.coarse address sample))
        (model.symbols .Z label) cell symbol =
      targets.zCellProfile cell symbol

/-- Exact invariants supplied before quotient-feature `Y` compatibility isolation. -/
def PassesFeatureYFirstZeroOut [DecidableEq Part] [DecidableEq Symbol]
    (model : FeatureCompatibilityModel A Part Symbol samples)
    (targets : FeatureCompatibilityTargets Part Symbol)
    (address : BlockAddress A) : Prop :=
  model.HasYBoundaryRelation targets.complement address ∧
    model.MatchesExact address .X targets.xExact ∧
    ∀ part y symbol,
      cellMultiplicity (fun sample ↦ yCompatibilityCell (model.coarse address sample))
          (model.symbols .Y (address .Y)) (.pooled part y) symbol =
        targets.yPooled part y symbol

/-- Exact invariants supplied before quotient-feature `Z` compatibility isolation. -/
def PassesFeatureZFirstZeroOut [DecidableEq Part] [DecidableEq Symbol]
    (model : FeatureCompatibilityModel A Part Symbol samples)
    (targets : FeatureCompatibilityTargets Part Symbol)
    (address : BlockAddress A) : Prop :=
  model.HasZBoundaryRelations targets.complement address ∧
    model.MatchesExact address .X targets.xExact ∧
    model.MatchesExact address .Y targets.yExact ∧
    ∀ part z symbol,
      cellMultiplicity (fun sample ↦ zCompatibilityCell (model.coarse address sample))
          (model.symbols .Z (address .Z)) (.pooled part z) symbol =
        targets.zPooled part z symbol

private theorem y_cellMultiplicity_boundary [DecidableEq Part] [DecidableEq Symbol]
    (model : FeatureCompatibilityModel A Part Symbol samples)
    (address : BlockAddress A) (sequence : Fin samples → Symbol)
    (q : {q : CoarseIndex Part // q.z = 0}) (symbol : Symbol) :
    cellMultiplicity (fun sample ↦ yCompatibilityCell (model.coarse address sample))
        sequence (.boundary q) symbol =
      cellMultiplicity (model.coarse address) sequence q.1 symbol := by
  classical
  unfold cellMultiplicity
  congr 1
  ext sample
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hcell, hsymbol⟩
    refine ⟨?_, hsymbol⟩
    unfold yCompatibilityCell at hcell
    split at hcell
    · exact congrArg Subtype.val (YCompatibilityCell.boundary.inj hcell)
    · cases hcell
  · rintro ⟨hcoarse, hsymbol⟩
    refine ⟨?_, hsymbol⟩
    rw [hcoarse]
    simp [yCompatibilityCell, q.2]

private theorem z_cellMultiplicity_boundary [DecidableEq Part] [DecidableEq Symbol]
    (model : FeatureCompatibilityModel A Part Symbol samples)
    (address : BlockAddress A) (sequence : Fin samples → Symbol)
    (q : {q : CoarseIndex Part // q.x = 0 ∨ q.y = 0}) (symbol : Symbol) :
    cellMultiplicity (fun sample ↦ zCompatibilityCell (model.coarse address sample))
        sequence (.boundary q) symbol =
      cellMultiplicity (model.coarse address) sequence q.1 symbol := by
  classical
  unfold cellMultiplicity
  congr 1
  ext sample
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hcell, hsymbol⟩
    refine ⟨?_, hsymbol⟩
    unfold zCompatibilityCell at hcell
    split at hcell
    · exact congrArg Subtype.val (ZCompatibilityCell.boundary.inj hcell)
    · cases hcell
  · rintro ⟨hcoarse, hsymbol⟩
    refine ⟨?_, hsymbol⟩
    rw [hcoarse]
    simp [zCompatibilityCell, q.2]

/-- Quotient-feature analogue of Claim 6.8: direct boundary relations and the first-zero-out
profile equations imply sound `Y` compatibility. -/
theorem featureCompatibleY_of_passesFirstZeroOut
    [DecidableEq Part] [DecidableEq Symbol]
    (model : FeatureCompatibilityModel A Part Symbol samples)
    (targets : FeatureCompatibilityTargets Part Symbol)
    (address : BlockAddress A)
    (hpasses : model.PassesFeatureYFirstZeroOut targets address) :
    model.FeatureCompatibleY targets (address .Y) address := by
  rcases hpasses with ⟨hboundary, hX, hpooled⟩
  intro cell symbol
  cases cell with
  | pooled part y => exact hpooled part y symbol
  | boundary q =>
      rw [y_cellMultiplicity_boundary]
      calc
        cellMultiplicity (model.coarse address)
            (model.symbols .Y (address .Y)) q.1 symbol =
            cellMultiplicity (model.coarse address)
              (model.symbols .X (address .X)) q.1
                (targets.complement.symm symbol) := by
          apply cellMultiplicity_equiv_on_cell
          intro sample hsample
          exact hboundary sample (by simpa [hsample] using q.2)
        _ = targets.xExact q.1 (targets.complement symbol) := by
          rw [targets.complement_symm]
          exact hX q.1 _
        _ = targets.yExact q.1 symbol :=
          (targets.yBoundary q.1 q.2 symbol).symm

/-- Quotient-feature analogue of Claim 6.12 for `Z`. -/
theorem featureCompatibleZ_of_passesFirstZeroOut
    [DecidableEq Part] [DecidableEq Symbol]
    (model : FeatureCompatibilityModel A Part Symbol samples)
    (targets : FeatureCompatibilityTargets Part Symbol)
    (address : BlockAddress A)
    (hpasses : model.PassesFeatureZFirstZeroOut targets address) :
    model.FeatureCompatibleZ targets (address .Z) address := by
  rcases hpasses with ⟨hboundary, hX, hY, hpooled⟩
  intro cell symbol
  cases cell with
  | pooled part z => exact hpooled part z symbol
  | boundary q =>
      rw [z_cellMultiplicity_boundary]
      rcases q.2 with hx | hy
      · calc
          cellMultiplicity (model.coarse address)
              (model.symbols .Z (address .Z)) q.1 symbol =
              cellMultiplicity (model.coarse address)
                (model.symbols .Y (address .Y)) q.1
                  (targets.complement.symm symbol) := by
            apply cellMultiplicity_equiv_on_cell
            intro sample hsample
            exact hboundary.1 sample (by simpa [hsample] using hx)
          _ = targets.yExact q.1 (targets.complement symbol) := by
            rw [targets.complement_symm]
            exact hY q.1 _
          _ = targets.zExact q.1 symbol :=
            (targets.zBoundaryOfY q.1 hx symbol).symm
      · calc
          cellMultiplicity (model.coarse address)
              (model.symbols .Z (address .Z)) q.1 symbol =
              cellMultiplicity (model.coarse address)
                (model.symbols .X (address .X)) q.1
                  (targets.complement.symm symbol) := by
            apply cellMultiplicity_equiv_on_cell
            intro sample hsample
            exact hboundary.2 sample (by simpa [hsample] using hy)
          _ = targets.xExact q.1 (targets.complement symbol) := by
            rw [targets.complement_symm]
            exact hX q.1 _
          _ = targets.zExact q.1 symbol :=
            (targets.zBoundaryOfX q.1 hy symbol).symm

/-- The exact soundness certificate consumed by generic `Y` compatibility zeroing. -/
theorem featureYCompatibility_sound
    [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]
    [DecidableEq Part] [DecidableEq Symbol]
    (model : FeatureCompatibilityModel A Part Symbol samples)
    (targets : FeatureCompatibilityTargets Part Symbol)
    (ambient : Finset (BlockAddress A))
    (hpasses : ∀ address ∈ ambient,
      model.PassesFeatureYFirstZeroOut targets address) :
    IsCompatibilitySound ambient .Y (model.FeatureCompatibleY targets) := by
  intro address haddress
  exact model.featureCompatibleY_of_passesFirstZeroOut targets address
    (hpasses address haddress)

/-- The exact soundness certificate consumed by generic `Z` compatibility zeroing. -/
theorem featureZCompatibility_sound
    [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]
    [DecidableEq Part] [DecidableEq Symbol]
    (model : FeatureCompatibilityModel A Part Symbol samples)
    (targets : FeatureCompatibilityTargets Part Symbol)
    (ambient : Finset (BlockAddress A))
    (hpasses : ∀ address ∈ ambient,
      model.PassesFeatureZFirstZeroOut targets address) :
    IsCompatibilitySound ambient .Z (model.FeatureCompatibleZ targets) := by
  intro address haddress
  exact model.featureCompatibleZ_of_passesFirstZeroOut targets address
    (hpasses address haddress)

end FeatureCompatibilityModel

section Cleanup

variable {K : Type*} [CommSemiring K]
variable {A : Leg → Type v} [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]
variable {V : ∀ c, A c → Type*}
variable [∀ c a, AddCommMonoid (V c a)] [∀ c a, Module K (V c a)]
variable {Part : Type u} {Symbol : Type w} [DecidableEq Part] [DecidableEq Symbol]
variable {samples : ℕ}

/-- Complete exact compatibility cleanup for an arbitrary quotient-feature alphabet.  This is a
thin semantic composition: feature boundary soundness feeds the existing generic two-stage
variable zeroing and indexed-direct-sum theorem. -/
theorem Tensor.Restricts.partitionedFeatureYZCompatibilityCleanup_to_indexedDirectSum
    (P : PartitionedTensor (K := K) (A := A) V)
    (hX : Set.InjOn (fun address : BlockAddress A ↦ address .X) P.support)
    (model : FeatureCompatibilityModel A Part Symbol samples)
    (targets : FeatureCompatibilityTargets Part Symbol)
    (hpassesY : ∀ address ∈ P.support,
      model.PassesFeatureYFirstZeroOut targets address)
    (hpassesZ : ∀ address ∈ compatibilityIsolatedSupport P.support .Y
        (model.FeatureCompatibleY targets),
      model.PassesFeatureZFirstZeroOut targets address) :
    let ySupport := compatibilityIsolatedSupport P.support .Y
      (model.FeatureCompatibleY targets)
    let zSupport := compatibilityIsolatedSupport ySupport .Z
      (model.FeatureCompatibleZ targets)
    Restricts P.realize
      (Tensor.indexedDirectSum
        (V := SelectedBlockFamily (V := V) zSupport)
        (fun address : zSupport ↦ P.constituent address.1)) := by
  exact Tensor.Restricts.partitionedYZCompatibilityCleanup_to_indexedDirectSum
    P hX (model.FeatureCompatibleY targets)
    (model.featureYCompatibility_sound targets P.support hpassesY)
    (model.FeatureCompatibleZ targets)
    (model.featureZCompatibility_sound targets _ hpassesZ)

end Cleanup

end MoreAsymmetryCompatibility
end AlgebraicComplexity
