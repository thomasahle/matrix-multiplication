/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.CompatibilityTargetCore
import AlgebraicComplexity.MatrixMultiplication.MoreAsymmetryCompatibility

/-!
# Aggregating the paper's compatibility profiles

The first compatibility zero-outs in *More Asymmetry Yields Faster Matrix
Multiplication* prescribe complete-split profiles on the pooled sets
`S_{t,*,j,*}` and `S_{t,*,*,k}`.  The disjoint cells used in the counting
argument remove the already-determined boundary constituents.  This file
proves the finite cancellation step connecting those two formulations.

The generic first section makes the required disjointness explicit.  The
specialized section then proves that the CW coarse boundary has one `Y` cell
and at most two `Z` cells and derives the positive-cell clauses used by
`PassesYFirstZeroOut` and `PassesZFirstZeroOut`.
-/

open scoped BigOperators

namespace AlgebraicComplexity
namespace MoreAsymmetryCompatibility

open Tensor

universe u v w

/-! ## Generic finite disjoint aggregation -/

section FiniteAggregation

variable {ι Cell Symbol : Type*}
variable [DecidableEq Cell] [DecidableEq Symbol]

/-- The finite fiber contributing to one cell/symbol aggregate. -/
noncomputable def cellFiber [Fintype ι]
    (cellOf : ι → Cell) (symbolOf : ι → Symbol) (cell : Cell) (symbol : Symbol) :
    Finset ι := by
  classical
  exact Finset.univ.filter fun occurrence ↦
    cellOf occurrence = cell ∧ symbolOf occurrence = symbol

/-- The portion of a cell/symbol fiber selected by a predicate. -/
noncomputable def restrictedCellFiber [Fintype ι]
    (keep : ι → Prop) (cellOf : ι → Cell) (symbolOf : ι → Symbol)
    (cell : Cell) (symbol : Symbol) : Finset ι := by
  classical
  exact Finset.univ.filter fun occurrence ↦
    keep occurrence ∧ cellOf occurrence = cell ∧ symbolOf occurrence = symbol

@[simp] theorem mem_cellFiber [Fintype ι]
    (cellOf : ι → Cell) (symbolOf : ι → Symbol) (cell : Cell) (symbol : Symbol)
    (occurrence : ι) :
    occurrence ∈ cellFiber cellOf symbolOf cell symbol ↔
      cellOf occurrence = cell ∧ symbolOf occurrence = symbol := by
  classical
  simp [cellFiber]

@[simp] theorem mem_restrictedCellFiber [Fintype ι]
    (keep : ι → Prop) (cellOf : ι → Cell) (symbolOf : ι → Symbol)
    (cell : Cell) (symbol : Symbol) (occurrence : ι) :
    occurrence ∈ restrictedCellFiber keep cellOf symbolOf cell symbol ↔
      keep occurrence ∧ cellOf occurrence = cell ∧ symbolOf occurrence = symbol := by
  classical
  simp [restrictedCellFiber]

/-- A predicate and its complement select disjoint portions of every fiber. -/
theorem restrictedCellFiber_disjoint_compl [Fintype ι] [DecidableEq ι]
    (keep : ι → Prop) (cellOf : ι → Cell) (symbolOf : ι → Symbol)
    (cell : Cell) (symbol : Symbol) :
    Disjoint
      (restrictedCellFiber keep cellOf symbolOf cell symbol)
      (restrictedCellFiber (fun occurrence ↦ ¬ keep occurrence)
        cellOf symbolOf cell symbol) := by
  classical
  rw [Finset.disjoint_left]
  intro occurrence hkeep hnot
  exact (mem_restrictedCellFiber _ _ _ _ _ _).mp hnot |>.1
    ((mem_restrictedCellFiber _ _ _ _ _ _).mp hkeep).1

/-- A predicate and its complement exhaust every fiber. -/
theorem cellFiber_eq_restricted_union_compl [Fintype ι] [DecidableEq ι]
    (keep : ι → Prop) (cellOf : ι → Cell) (symbolOf : ι → Symbol)
    (cell : Cell) (symbol : Symbol) :
    cellFiber cellOf symbolOf cell symbol =
      restrictedCellFiber keep cellOf symbolOf cell symbol ∪
        restrictedCellFiber (fun occurrence ↦ ¬ keep occurrence)
          cellOf symbolOf cell symbol := by
  classical
  ext occurrence
  by_cases hkeep : keep occurrence <;> simp [hkeep]

/-- Restriction to a disjunction is the union of the two restricted fibers.
The separate theorem below records the extra pointwise hypothesis required
for that union to be disjoint. -/
theorem restrictedCellFiber_or_eq_union [Fintype ι] [DecidableEq ι]
    (left right : ι → Prop)
    (cellOf : ι → Cell) (symbolOf : ι → Symbol)
    (cell : Cell) (symbol : Symbol) :
    restrictedCellFiber (fun occurrence ↦ left occurrence ∨ right occurrence)
        cellOf symbolOf cell symbol =
      restrictedCellFiber left cellOf symbolOf cell symbol ∪
        restrictedCellFiber right cellOf symbolOf cell symbol := by
  classical
  ext occurrence
  simp only [mem_restrictedCellFiber, Finset.mem_union]
  constructor
  · rintro ⟨hleft | hright, hcell, hsymbol⟩
    · exact Or.inl ⟨hleft, hcell, hsymbol⟩
    · exact Or.inr ⟨hright, hcell, hsymbol⟩
  · rintro (⟨hleft, hcell, hsymbol⟩ | ⟨hright, hcell, hsymbol⟩)
    · exact ⟨Or.inl hleft, hcell, hsymbol⟩
    · exact ⟨Or.inr hright, hcell, hsymbol⟩

/-- The two restricted fibers in `restrictedCellFiber_or_eq_union` are
disjoint precisely under the exposed pointwise-disjointness hypothesis. -/
theorem restrictedCellFiber_disjoint_of_pointwise [Fintype ι] [DecidableEq ι]
    (left right : ι → Prop)
    (hdisjoint : ∀ occurrence, ¬ (left occurrence ∧ right occurrence))
    (cellOf : ι → Cell) (symbolOf : ι → Symbol)
    (cell : Cell) (symbol : Symbol) :
    Disjoint
      (restrictedCellFiber left cellOf symbolOf cell symbol)
      (restrictedCellFiber right cellOf symbolOf cell symbol) := by
  classical
  rw [Finset.disjoint_left]
  intro occurrence hleft hright
  exact hdisjoint occurrence
    ⟨(mem_restrictedCellFiber _ _ _ _ _ _).mp hleft |>.1,
      (mem_restrictedCellFiber _ _ _ _ _ _).mp hright |>.1⟩

/-- Sum arbitrary weights over one cell/symbol fiber. -/
noncomputable def weightedCellMass [Fintype ι] [AddCommMonoid W]
    (weight : ι → W) (cellOf : ι → Cell) (symbolOf : ι → Symbol)
    (cell : Cell) (symbol : Symbol) : W :=
  ∑ occurrence ∈ cellFiber cellOf symbolOf cell symbol, weight occurrence

/-- Sum arbitrary weights over the selected portion of one fiber. -/
noncomputable def restrictedWeightedCellMass [Fintype ι] [AddCommMonoid W]
    (weight : ι → W) (keep : ι → Prop)
    (cellOf : ι → Cell) (symbolOf : ι → Symbol)
    (cell : Cell) (symbol : Symbol) : W :=
  ∑ occurrence ∈ restrictedCellFiber keep cellOf symbolOf cell symbol,
    weight occurrence

/-- Exact weighted decomposition over a proved disjoint partition. -/
theorem weightedCellMass_eq_restricted_add_compl [Fintype ι] [AddCommMonoid W]
    (weight : ι → W) (keep : ι → Prop)
    (cellOf : ι → Cell) (symbolOf : ι → Symbol)
    (cell : Cell) (symbol : Symbol) :
    weightedCellMass weight cellOf symbolOf cell symbol =
      restrictedWeightedCellMass weight keep cellOf symbolOf cell symbol +
        restrictedWeightedCellMass weight (fun occurrence ↦ ¬ keep occurrence)
          cellOf symbolOf cell symbol := by
  classical
  unfold weightedCellMass restrictedWeightedCellMass
  rw [cellFiber_eq_restricted_union_compl keep]
  exact Finset.sum_union
    (restrictedCellFiber_disjoint_compl keep cellOf symbolOf cell symbol)

/-- Weighted aggregation over the union of two explicitly disjoint classes. -/
theorem restrictedWeightedCellMass_or [Fintype ι] [AddCommMonoid W]
    (weight : ι → W) (left right : ι → Prop)
    (hdisjoint : ∀ occurrence, ¬ (left occurrence ∧ right occurrence))
    (cellOf : ι → Cell) (symbolOf : ι → Symbol)
    (cell : Cell) (symbol : Symbol) :
    restrictedWeightedCellMass weight (fun occurrence ↦ left occurrence ∨ right occurrence)
        cellOf symbolOf cell symbol =
      restrictedWeightedCellMass weight left cellOf symbolOf cell symbol +
        restrictedWeightedCellMass weight right cellOf symbolOf cell symbol := by
  classical
  unfold restrictedWeightedCellMass
  rw [restrictedCellFiber_or_eq_union left right]
  exact Finset.sum_union
    (restrictedCellFiber_disjoint_of_pointwise left right hdisjoint
      cellOf symbolOf cell symbol)

/-- Nonnegative occurrence weights give nonnegative restricted aggregates. -/
theorem restrictedWeightedCellMass_nonneg [Fintype ι]
    (weight : ι → ℝ) (keep : ι → Prop)
    (cellOf : ι → Cell) (symbolOf : ι → Symbol)
    (cell : Cell) (symbol : Symbol)
    (hweight : ∀ occurrence, 0 ≤ weight occurrence) :
    0 ≤ restrictedWeightedCellMass weight keep cellOf symbolOf cell symbol := by
  classical
  exact Finset.sum_nonneg fun occurrence _ ↦ hweight occurrence

/-- Cardinality version of a restricted fiber. -/
noncomputable def restrictedCellMultiplicity [Fintype ι]
    (keep : ι → Prop) (cellOf : ι → Cell) (symbolOf : ι → Symbol)
    (cell : Cell) (symbol : Symbol) : ℕ :=
  (restrictedCellFiber keep cellOf symbolOf cell symbol).card

/-- Ordinary multiplicity is the sum of the two nonnegative cardinalities of a
disjoint predicate partition. -/
theorem cellMultiplicity_eq_restricted_add_compl [Fintype ι]
    (keep : ι → Prop) (cellOf : ι → Cell) (symbolOf : ι → Symbol)
    (cell : Cell) (symbol : Symbol) :
    cellMultiplicity cellOf symbolOf cell symbol =
      restrictedCellMultiplicity keep cellOf symbolOf cell symbol +
        restrictedCellMultiplicity (fun occurrence ↦ ¬ keep occurrence)
          cellOf symbolOf cell symbol := by
  classical
  unfold cellMultiplicity restrictedCellMultiplicity
  change (cellFiber cellOf symbolOf cell symbol).card = _
  rw [cellFiber_eq_restricted_union_compl keep,
    Finset.card_union_of_disjoint
      (restrictedCellFiber_disjoint_compl keep cellOf symbolOf cell symbol)]

/-- Generic finite cancellation across a disjoint predicate/complement
partition.  Counts are natural numbers (hence nonnegative), and the required
disjointness is supplied by `restrictedCellFiber_disjoint_compl`, rather than
being inferred from an equality of aggregate sums. -/
theorem restrictedComplementMultiplicity_eq_of_total_and_part [Fintype ι]
    (keep : ι → Prop) (cellOf : ι → Cell) (symbolOf : ι → Symbol)
    (cell : Cell) (symbol : Symbol)
    (totalTarget partTarget complementTarget : ℕ)
    (htarget : totalTarget = partTarget + complementTarget)
    (htotal : cellMultiplicity cellOf symbolOf cell symbol = totalTarget)
    (hpart : restrictedCellMultiplicity keep cellOf symbolOf cell symbol = partTarget) :
    restrictedCellMultiplicity (fun occurrence ↦ ¬ keep occurrence)
        cellOf symbolOf cell symbol = complementTarget := by
  have hdecompose := cellMultiplicity_eq_restricted_add_compl
    keep cellOf symbolOf cell symbol
  rw [htotal, htarget, hpart] at hdecompose
  exact (Nat.add_left_cancel hdecompose).symm

/-- Cardinality aggregation over the union of two explicitly disjoint classes. -/
theorem restrictedCellMultiplicity_or [Fintype ι]
    (left right : ι → Prop)
    (hdisjoint : ∀ occurrence, ¬ (left occurrence ∧ right occurrence))
    (cellOf : ι → Cell) (symbolOf : ι → Symbol)
    (cell : Cell) (symbol : Symbol) :
    restrictedCellMultiplicity (fun occurrence ↦ left occurrence ∨ right occurrence)
        cellOf symbolOf cell symbol =
      restrictedCellMultiplicity left cellOf symbolOf cell symbol +
        restrictedCellMultiplicity right cellOf symbolOf cell symbol := by
  classical
  unfold restrictedCellMultiplicity
  rw [restrictedCellFiber_or_eq_union left right,
    Finset.card_union_of_disjoint
      (restrictedCellFiber_disjoint_of_pointwise left right hdisjoint
        cellOf symbolOf cell symbol)]

/-- Restricted multiplicity depends only on the selected subset, not on the
syntactic presentation of its predicate. -/
theorem restrictedCellMultiplicity_congr [Fintype ι]
    {left right : ι → Prop} (hiff : ∀ occurrence, left occurrence ↔ right occurrence)
    (cellOf : ι → Cell) (symbolOf : ι → Symbol)
    (cell : Cell) (symbol : Symbol) :
    restrictedCellMultiplicity left cellOf symbolOf cell symbol =
      restrictedCellMultiplicity right cellOf symbolOf cell symbol := by
  classical
  unfold restrictedCellMultiplicity
  congr 1
  ext occurrence
  simp only [mem_restrictedCellFiber]
  rw [hiff occurrence]

end FiniteAggregation

/-! ## Paper pooled cells and exact target decomposition -/

/-- The paper's `S_{t,*,j,*}` cell. -/
def yPooledAllCell {Part : Type u} (q : CoarseIndex Part) : Part × ℕ :=
  (q.part, q.y)

/-- The paper's `S_{t,*,*,k}` cell. -/
def zPooledAllCell {Part : Type u} (q : CoarseIndex Part) : Part × ℕ :=
  (q.part, q.z)

/-- Canonical `k=0` boundary constituent inside `S_{t,*,j,*}`. -/
def yBoundaryIndex {Part : Type u} (depth : ℕ) (part : Part) (y : ℕ) : CoarseIndex Part where
  part := part
  x := coarseTotal depth - y
  y := y
  z := 0

/-- Canonical `i=0` boundary constituent inside `S_{t,*,*,k}`. -/
def zXBoundaryIndex {Part : Type u} (depth : ℕ) (part : Part) (z : ℕ) : CoarseIndex Part where
  part := part
  x := 0
  y := coarseTotal depth - z
  z := z

/-- Canonical `j=0`, `i>0` boundary constituent inside `S_{t,*,*,k}`. -/
def zYBoundaryIndex {Part : Type u} (depth : ℕ) (part : Part) (z : ℕ) : CoarseIndex Part where
  part := part
  x := coarseTotal depth - z
  y := 0
  z := z

namespace CompatibilityTargets

variable {Part : Type u} {depth : ℕ}

/-- Boundary contribution removed from the paper's `S_{t,*,j,*}` profile.
Legality makes this a single coarse constituent. -/
def yBoundaryAggregate (targets : CompatibilityTargets Part depth)
    (part : Part) (y : ℕ) (word : SplitWord depth) : ℕ :=
  targets.yExact (yBoundaryIndex depth part y) word

/-- Boundary contribution removed from the paper's `S_{t,*,*,k}` profile.
The `i=0` cell is always the first summand.  The `j=0` cell is distinct
exactly when `k < 2^(depth+1)`, so the conditional prevents double counting
the all-zero `X,Y` boundary. -/
def zBoundaryAggregate (targets : CompatibilityTargets Part depth)
    (part : Part) (z : ℕ) (word : SplitWord depth) : ℕ :=
  targets.zExact (zXBoundaryIndex depth part z) word +
    if z < coarseTotal depth then
      targets.zExact (zYBoundaryIndex depth part z) word
    else 0

end CompatibilityTargets

/-- Exact count tables prescribed by the paper on the pooled-all sets,
together with the two disjoint target decompositions needed to pass to the
positive compatibility cells.  These equations are the finite, unnormalized
form of the weighted-average definitions of the paper's `Split_avg` tables. -/
structure PooledAllTargets {Part : Type u} {depth : ℕ}
    (targets : CompatibilityTargets Part depth) where
  yAll : Part → ℕ → SplitWord depth → ℕ
  zAll : Part → ℕ → SplitWord depth → ℕ
  y_decompose : ∀ part y word,
    yAll part y word =
      targets.yBoundaryAggregate part y word + targets.yPooled part y word
  z_decompose : ∀ part z word,
    zAll part z word =
      targets.zBoundaryAggregate part z word + targets.zPooled part z word

namespace CompatibilityTargets

/-- Canonical pooled-all count tables obtained by adjoining the already fixed
boundary counts to the positive-cell targets.  This is the exact finite
counterpart of defining the paper's averaged complete-split distributions by
their weighted mixtures. -/
def canonicalPooledAll {Part : Type u} {depth : ℕ}
    (targets : CompatibilityTargets Part depth) : PooledAllTargets targets where
  yAll part y word :=
    targets.yBoundaryAggregate part y word + targets.yPooled part y word
  zAll part z word :=
    targets.zBoundaryAggregate part z word + targets.zPooled part z word
  y_decompose _ _ _ := rfl
  z_decompose _ _ _ := rfl

end CompatibilityTargets

namespace CompatibilityModel

variable {A : Leg → Type v} {Part : Type u} {depth samples : ℕ}

/-- Exact finite form of the paper's first `Y` zero-out on every
`S_{t,*,j,*}` cell. -/
def MatchesYPooledAll [DecidableEq Part]
    (model : CompatibilityModel A Part depth samples)
    (address : BlockAddress A)
    (profile : Part → ℕ → SplitWord depth → ℕ) : Prop :=
  ∀ part y word,
    cellMultiplicity (fun sample ↦ yPooledAllCell (model.coarse address sample))
        (model.chunks .Y (address .Y)) (part, y) word =
      profile part y word

/-- Exact finite form of the paper's first `Z` zero-out on every
`S_{t,*,*,k}` cell. -/
def MatchesZPooledAll [DecidableEq Part]
    (model : CompatibilityModel A Part depth samples)
    (address : BlockAddress A)
    (profile : Part → ℕ → SplitWord depth → ℕ) : Prop :=
  ∀ part z word,
    cellMultiplicity (fun sample ↦ zPooledAllCell (model.coarse address sample))
        (model.chunks .Z (address .Z)) (part, z) word =
      profile part z word

/-- Every coarse triple realized by a legal fine CW triple has total weight
`2^(depth+1)`. -/
theorem coarse_sum_eq_coarseTotal
    (model : CompatibilityModel A Part depth samples)
    (address : BlockAddress A) (hlegal : model.IsFineLegal address)
    (hweights : model.HasCoarseWeights address) (sample : Fin samples) :
    (model.coarse address sample).x + (model.coarse address sample).y +
        (model.coarse address sample).z = coarseTotal depth := by
  have hX := hweights .X sample
  have hY := hweights .Y sample
  have hZ := hweights .Z sample
  simp only [CoarseIndex.get] at hX hY hZ
  rw [← hX, ← hY, ← hZ]
  unfold splitWordWeight coarseTotal
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  calc
    (∑ position,
        ((model.chunks .X (address .X) sample position : ℕ) +
          (model.chunks .Y (address .Y) sample position : ℕ) +
          (model.chunks .Z (address .Z) sample position : ℕ))) =
        ∑ _position : Fin (2 ^ depth), 2 := by
          apply Finset.sum_congr rfl
          intro position _
          exact hlegal sample position
    _ = coarseTotal depth := by
      simp [coarseTotal, pow_succ, Nat.mul_comm]

/-- Inside a legal pooled `Y` cell, a boundary sample has the unique canonical
coarse index. -/
theorem coarse_eq_yBoundaryIndex
    (model : CompatibilityModel A Part depth samples)
    (address : BlockAddress A) (hlegal : model.IsFineLegal address)
    (hweights : model.HasCoarseWeights address) (sample : Fin samples)
    (part : Part) (y : ℕ)
    (hcell : yPooledAllCell (model.coarse address sample) = (part, y))
    (hboundary : (model.coarse address sample).z = 0) :
    model.coarse address sample = yBoundaryIndex depth part y := by
  have htotal := model.coarse_sum_eq_coarseTotal address hlegal hweights sample
  have hpart : (model.coarse address sample).part = part := congrArg Prod.fst hcell
  have hy : (model.coarse address sample).y = y := congrArg Prod.snd hcell
  cases hq : model.coarse address sample with
  | mk p x' y' z' =>
      simp only [hq] at htotal hpart hy hboundary ⊢
      subst p
      subst y'
      subst z'
      simp only [yBoundaryIndex, CoarseIndex.mk.injEq, true_and]
      have hy_le : y ≤ coarseTotal depth := by omega
      exact ⟨by omega, trivial⟩

/-- Inside a legal pooled `Z` cell, an `x=0` boundary sample has the canonical
`i=0` coarse index. -/
theorem coarse_eq_zXBoundaryIndex
    (model : CompatibilityModel A Part depth samples)
    (address : BlockAddress A) (hlegal : model.IsFineLegal address)
    (hweights : model.HasCoarseWeights address) (sample : Fin samples)
    (part : Part) (z : ℕ)
    (hcell : zPooledAllCell (model.coarse address sample) = (part, z))
    (hx : (model.coarse address sample).x = 0) :
    model.coarse address sample = zXBoundaryIndex depth part z := by
  have htotal := model.coarse_sum_eq_coarseTotal address hlegal hweights sample
  have hpart : (model.coarse address sample).part = part := congrArg Prod.fst hcell
  have hz : (model.coarse address sample).z = z := congrArg Prod.snd hcell
  cases hq : model.coarse address sample with
  | mk p x' y' z' =>
      simp only [hq] at htotal hpart hz hx ⊢
      subst p
      subst z'
      subst x'
      simp only [zXBoundaryIndex, CoarseIndex.mk.injEq, true_and]
      have hz_le : z ≤ coarseTotal depth := by omega
      exact ⟨by omega, trivial⟩

/-- Inside a legal pooled `Z` cell, a boundary sample with `x>0` and `y=0`
has the second canonical boundary index. -/
theorem coarse_eq_zYBoundaryIndex
    (model : CompatibilityModel A Part depth samples)
    (address : BlockAddress A) (hlegal : model.IsFineLegal address)
    (hweights : model.HasCoarseWeights address) (sample : Fin samples)
    (part : Part) (z : ℕ)
    (hcell : zPooledAllCell (model.coarse address sample) = (part, z))
    (hy : (model.coarse address sample).y = 0) :
    model.coarse address sample = zYBoundaryIndex depth part z := by
  have htotal := model.coarse_sum_eq_coarseTotal address hlegal hweights sample
  have hpart : (model.coarse address sample).part = part := congrArg Prod.fst hcell
  have hz : (model.coarse address sample).z = z := congrArg Prod.snd hcell
  cases hq : model.coarse address sample with
  | mk p x' y' z' =>
      simp only [hq] at htotal hpart hz hy ⊢
      subst p
      subst z'
      subst y'
      simp only [zYBoundaryIndex, CoarseIndex.mk.injEq, and_self, true_and]
      have hz_le : z ≤ coarseTotal depth := by omega
      exact ⟨by omega, trivial⟩

section CellDecompositions

variable [DecidableEq Part]

/-- The positive part of a pooled-all `Y` fiber is exactly the pooled
`YCompatibilityCell`. -/
theorem restricted_yPositive_eq_compatibilityPooled
    (model : CompatibilityModel A Part depth samples)
    (address : BlockAddress A) (sequence : Fin samples → SplitWord depth)
    (part : Part) (y : ℕ) (word : SplitWord depth) :
    restrictedCellMultiplicity
        (fun sample ↦ (model.coarse address sample).z ≠ 0)
        (fun sample ↦ yPooledAllCell (model.coarse address sample))
        sequence (part, y) word =
      cellMultiplicity
        (fun sample ↦ yCompatibilityCell (model.coarse address sample))
        sequence (.pooled part y) word := by
  classical
  unfold restrictedCellMultiplicity cellMultiplicity
  congr 1
  ext sample
  simp only [mem_restrictedCellFiber, Finset.mem_filter, Finset.mem_univ, true_and]
  by_cases hz : (model.coarse address sample).z = 0
  · simp [hz, yCompatibilityCell]
  · simp [hz, yCompatibilityCell, yPooledAllCell]

/-- The positive part of a pooled-all `Z` fiber is exactly the pooled
`ZCompatibilityCell`. -/
theorem restricted_zPositive_eq_compatibilityPooled
    (model : CompatibilityModel A Part depth samples)
    (address : BlockAddress A) (sequence : Fin samples → SplitWord depth)
    (part : Part) (z : ℕ) (word : SplitWord depth) :
    restrictedCellMultiplicity
        (fun sample ↦ ¬ ((model.coarse address sample).x = 0 ∨
          (model.coarse address sample).y = 0))
        (fun sample ↦ zPooledAllCell (model.coarse address sample))
        sequence (part, z) word =
      cellMultiplicity
        (fun sample ↦ zCompatibilityCell (model.coarse address sample))
        sequence (.pooled part z) word := by
  classical
  unfold restrictedCellMultiplicity cellMultiplicity
  congr 1
  ext sample
  simp only [mem_restrictedCellFiber, Finset.mem_filter, Finset.mem_univ, true_and]
  by_cases hboundary : (model.coarse address sample).x = 0 ∨
      (model.coarse address sample).y = 0
  · simp [hboundary, zCompatibilityCell]
  · simp [hboundary, zCompatibilityCell, zPooledAllCell]

/-- Exact disjoint decomposition of `S_{t,*,j,*}` into its `k=0` boundary
and `k>0` compatibility cell. -/
theorem yPooledAllMultiplicity_decompose
    (model : CompatibilityModel A Part depth samples)
    (address : BlockAddress A) (sequence : Fin samples → SplitWord depth)
    (part : Part) (y : ℕ) (word : SplitWord depth) :
    cellMultiplicity
        (fun sample ↦ yPooledAllCell (model.coarse address sample))
        sequence (part, y) word =
      restrictedCellMultiplicity
          (fun sample ↦ (model.coarse address sample).z = 0)
          (fun sample ↦ yPooledAllCell (model.coarse address sample))
          sequence (part, y) word +
        cellMultiplicity
          (fun sample ↦ yCompatibilityCell (model.coarse address sample))
          sequence (.pooled part y) word := by
  rw [cellMultiplicity_eq_restricted_add_compl
    (fun sample ↦ (model.coarse address sample).z = 0)]
  congr 1
  exact model.restricted_yPositive_eq_compatibilityPooled address sequence part y word

/-- Exact disjoint decomposition of `S_{t,*,*,k}` into its boundary and
`i,j>0` compatibility cell. -/
theorem zPooledAllMultiplicity_decompose
    (model : CompatibilityModel A Part depth samples)
    (address : BlockAddress A) (sequence : Fin samples → SplitWord depth)
    (part : Part) (z : ℕ) (word : SplitWord depth) :
    cellMultiplicity
        (fun sample ↦ zPooledAllCell (model.coarse address sample))
        sequence (part, z) word =
      restrictedCellMultiplicity
          (fun sample ↦ (model.coarse address sample).x = 0 ∨
            (model.coarse address sample).y = 0)
          (fun sample ↦ zPooledAllCell (model.coarse address sample))
          sequence (part, z) word +
        cellMultiplicity
          (fun sample ↦ zCompatibilityCell (model.coarse address sample))
          sequence (.pooled part z) word := by
  rw [cellMultiplicity_eq_restricted_add_compl
    (fun sample ↦ (model.coarse address sample).x = 0 ∨
      (model.coarse address sample).y = 0)]
  congr 1
  exact model.restricted_zPositive_eq_compatibilityPooled address sequence part z word

/-- A legal pooled `Y` boundary fiber is the exact canonical coarse fiber. -/
theorem restricted_yBoundary_eq_exact
    (model : CompatibilityModel A Part depth samples)
    (address : BlockAddress A) (hlegal : model.IsFineLegal address)
    (hweights : model.HasCoarseWeights address)
    (sequence : Fin samples → SplitWord depth)
    (part : Part) (y : ℕ) (word : SplitWord depth) :
    restrictedCellMultiplicity
        (fun sample ↦ (model.coarse address sample).z = 0)
        (fun sample ↦ yPooledAllCell (model.coarse address sample))
        sequence (part, y) word =
      cellMultiplicity (model.coarse address) sequence
        (yBoundaryIndex depth part y) word := by
  classical
  unfold restrictedCellMultiplicity cellMultiplicity
  congr 1
  ext sample
  simp only [mem_restrictedCellFiber, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hboundary, hcell, hword⟩
    exact ⟨model.coarse_eq_yBoundaryIndex address hlegal hweights sample part y
      hcell hboundary, hword⟩
  · rintro ⟨hcoarse, hword⟩
    refine ⟨?_, ?_, hword⟩
    · simp [hcoarse, yBoundaryIndex]
    · simp [hcoarse, yPooledAllCell, yBoundaryIndex]

/-- The `i=0` portion of a legal pooled `Z` boundary fiber is its exact
canonical coarse fiber. -/
theorem restricted_zXBoundary_eq_exact
    (model : CompatibilityModel A Part depth samples)
    (address : BlockAddress A) (hlegal : model.IsFineLegal address)
    (hweights : model.HasCoarseWeights address)
    (sequence : Fin samples → SplitWord depth)
    (part : Part) (z : ℕ) (word : SplitWord depth) :
    restrictedCellMultiplicity
        (fun sample ↦ (model.coarse address sample).x = 0)
        (fun sample ↦ zPooledAllCell (model.coarse address sample))
        sequence (part, z) word =
      cellMultiplicity (model.coarse address) sequence
        (zXBoundaryIndex depth part z) word := by
  classical
  unfold restrictedCellMultiplicity cellMultiplicity
  congr 1
  ext sample
  simp only [mem_restrictedCellFiber, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hx, hcell, hword⟩
    exact ⟨model.coarse_eq_zXBoundaryIndex address hlegal hweights sample part z hcell hx,
      hword⟩
  · rintro ⟨hcoarse, hword⟩
    refine ⟨?_, ?_, hword⟩
    · simp [hcoarse, zXBoundaryIndex]
    · simp [hcoarse, zPooledAllCell, zXBoundaryIndex]

/-- When `z` is below the total, the distinct `j=0`, `i>0` portion of a
legal pooled `Z` boundary fiber is its exact canonical coarse fiber. -/
theorem restricted_zYBoundary_eq_exact
    (model : CompatibilityModel A Part depth samples)
    (address : BlockAddress A) (hlegal : model.IsFineLegal address)
    (hweights : model.HasCoarseWeights address)
    (sequence : Fin samples → SplitWord depth)
    (part : Part) (z : ℕ) (word : SplitWord depth)
    (hz : z < coarseTotal depth) :
    restrictedCellMultiplicity
        (fun sample ↦ (model.coarse address sample).x ≠ 0 ∧
          (model.coarse address sample).y = 0)
        (fun sample ↦ zPooledAllCell (model.coarse address sample))
        sequence (part, z) word =
      cellMultiplicity (model.coarse address) sequence
        (zYBoundaryIndex depth part z) word := by
  classical
  unfold restrictedCellMultiplicity cellMultiplicity
  congr 1
  ext sample
  simp only [mem_restrictedCellFiber, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨⟨_hx, hy⟩, hcell, hword⟩
    exact ⟨model.coarse_eq_zYBoundaryIndex address hlegal hweights sample part z hcell hy,
      hword⟩
  · rintro ⟨hcoarse, hword⟩
    refine ⟨⟨?_, ?_⟩, ?_, hword⟩
    · simp only [hcoarse, zYBoundaryIndex]
      omega
    · simp [hcoarse, zYBoundaryIndex]
    · simp [hcoarse, zPooledAllCell, zYBoundaryIndex]

/-- At and above the total weight, the distinct `j=0`, `i>0` boundary
portion is empty. -/
theorem restricted_zYBoundary_eq_zero
    (model : CompatibilityModel A Part depth samples)
    (address : BlockAddress A) (hlegal : model.IsFineLegal address)
    (hweights : model.HasCoarseWeights address)
    (sequence : Fin samples → SplitWord depth)
    (part : Part) (z : ℕ) (word : SplitWord depth)
    (hz : ¬ z < coarseTotal depth) :
    restrictedCellMultiplicity
        (fun sample ↦ (model.coarse address sample).x ≠ 0 ∧
          (model.coarse address sample).y = 0)
        (fun sample ↦ zPooledAllCell (model.coarse address sample))
        sequence (part, z) word = 0 := by
  classical
  unfold restrictedCellMultiplicity
  apply Finset.card_eq_zero.mpr
  ext sample
  constructor
  · intro hsample
    rcases (mem_restrictedCellFiber _ _ _ _ _ _).mp hsample with
      ⟨⟨hx, hy⟩, hcell, _hword⟩
    have hcoarse := model.coarse_eq_zYBoundaryIndex address hlegal hweights sample
      part z hcell hy
    exfalso
    apply hx
    rw [hcoarse]
    simp [zYBoundaryIndex, Nat.sub_eq_zero_of_le (Nat.le_of_not_gt hz)]
  · intro hsample
    simp at hsample

/-- The actual `Y` boundary aggregate equals the boundary table determined by
the exact `X` profile and the CW complementation identity. -/
theorem yBoundaryMultiplicity_eq_target
    (model : CompatibilityModel A Part depth samples)
    (targets : CompatibilityTargets Part depth)
    (address : BlockAddress A) (hlegal : model.IsFineLegal address)
    (hweights : model.HasCoarseWeights address)
    (hX : model.MatchesExact address .X targets.xExact)
    (part : Part) (y : ℕ) (word : SplitWord depth) :
    restrictedCellMultiplicity
        (fun sample ↦ (model.coarse address sample).z = 0)
        (fun sample ↦ yPooledAllCell (model.coarse address sample))
        (model.chunks .Y (address .Y)) (part, y) word =
      targets.yBoundaryAggregate part y word := by
  rw [model.restricted_yBoundary_eq_exact address hlegal hweights]
  let q := yBoundaryIndex depth part y
  calc
    cellMultiplicity (model.coarse address)
        (model.chunks .Y (address .Y)) q word =
        cellMultiplicity (model.coarse address)
          (model.chunks .X (address .X)) q (complementSplitWord word) := by
      apply cellMultiplicity_complement
      intro sample hsample
      exact model.y_eq_complement_x_of_z_eq_zero address hlegal hweights sample
        (by rw [hsample]; rfl)
    _ = targets.xExact q (complementSplitWord word) := hX q _
    _ = targets.yExact q word := (targets.yBoundary q (by rfl) word).symm
    _ = targets.yBoundaryAggregate part y word := rfl

/-- The actual `i=0` part of the `Z` boundary equals its exact target table. -/
theorem zXBoundaryMultiplicity_eq_target
    (model : CompatibilityModel A Part depth samples)
    (targets : CompatibilityTargets Part depth)
    (address : BlockAddress A) (hlegal : model.IsFineLegal address)
    (hweights : model.HasCoarseWeights address)
    (hY : model.MatchesExact address .Y targets.yExact)
    (part : Part) (z : ℕ) (word : SplitWord depth) :
    restrictedCellMultiplicity
        (fun sample ↦ (model.coarse address sample).x = 0)
        (fun sample ↦ zPooledAllCell (model.coarse address sample))
        (model.chunks .Z (address .Z)) (part, z) word =
      targets.zExact (zXBoundaryIndex depth part z) word := by
  rw [model.restricted_zXBoundary_eq_exact address hlegal hweights]
  let q := zXBoundaryIndex depth part z
  calc
    cellMultiplicity (model.coarse address)
        (model.chunks .Z (address .Z)) q word =
        cellMultiplicity (model.coarse address)
          (model.chunks .Y (address .Y)) q (complementSplitWord word) := by
      apply cellMultiplicity_complement
      intro sample hsample
      exact model.z_eq_complement_y_of_x_eq_zero address hlegal hweights sample
        (by rw [hsample]; rfl)
    _ = targets.yExact q (complementSplitWord word) := hY q _
    _ = targets.zExact q word := (targets.zBoundaryOfY q (by rfl) word).symm

/-- The actual distinct `j=0`, `i>0` part of the `Z` boundary equals its
exact target table whenever that cell exists. -/
theorem zYBoundaryMultiplicity_eq_target
    (model : CompatibilityModel A Part depth samples)
    (targets : CompatibilityTargets Part depth)
    (address : BlockAddress A) (hlegal : model.IsFineLegal address)
    (hweights : model.HasCoarseWeights address)
    (hX : model.MatchesExact address .X targets.xExact)
    (part : Part) (z : ℕ) (word : SplitWord depth)
    (hz : z < coarseTotal depth) :
    restrictedCellMultiplicity
        (fun sample ↦ (model.coarse address sample).x ≠ 0 ∧
          (model.coarse address sample).y = 0)
        (fun sample ↦ zPooledAllCell (model.coarse address sample))
        (model.chunks .Z (address .Z)) (part, z) word =
      targets.zExact (zYBoundaryIndex depth part z) word := by
  rw [model.restricted_zYBoundary_eq_exact address hlegal hweights _ _ _ _ hz]
  let q := zYBoundaryIndex depth part z
  calc
    cellMultiplicity (model.coarse address)
        (model.chunks .Z (address .Z)) q word =
        cellMultiplicity (model.coarse address)
          (model.chunks .X (address .X)) q (complementSplitWord word) := by
      apply cellMultiplicity_complement
      intro sample hsample
      exact model.z_eq_complement_x_of_y_eq_zero address hlegal hweights sample
        (by rw [hsample]; rfl)
    _ = targets.xExact q (complementSplitWord word) := hX q _
    _ = targets.zExact q word := (targets.zBoundaryOfX q (by rfl) word).symm

/-- The whole actual `Z` boundary aggregate equals the target boundary sum.
The proof explicitly partitions it into the disjoint classes `x=0` and
`x≠0 ∧ y=0`, so the endpoint is not double counted. -/
theorem zBoundaryMultiplicity_eq_target
    (model : CompatibilityModel A Part depth samples)
    (targets : CompatibilityTargets Part depth)
    (address : BlockAddress A) (hlegal : model.IsFineLegal address)
    (hweights : model.HasCoarseWeights address)
    (hX : model.MatchesExact address .X targets.xExact)
    (hY : model.MatchesExact address .Y targets.yExact)
    (part : Part) (z : ℕ) (word : SplitWord depth) :
    restrictedCellMultiplicity
        (fun sample ↦ (model.coarse address sample).x = 0 ∨
          (model.coarse address sample).y = 0)
        (fun sample ↦ zPooledAllCell (model.coarse address sample))
        (model.chunks .Z (address .Z)) (part, z) word =
      targets.zBoundaryAggregate part z word := by
  let left : Fin samples → Prop :=
    fun sample ↦ (model.coarse address sample).x = 0
  let right : Fin samples → Prop :=
    fun sample ↦ (model.coarse address sample).x ≠ 0 ∧
      (model.coarse address sample).y = 0
  have hpredicate : ∀ sample,
      ((model.coarse address sample).x = 0 ∨
        (model.coarse address sample).y = 0) ↔ left sample ∨ right sample := by
    intro sample
    simp only [left, right]
    tauto
  rw [restrictedCellMultiplicity_congr hpredicate]
  rw [restrictedCellMultiplicity_or left right (by
    intro sample
    simp only [left, right]
    tauto)]
  rw [model.zXBoundaryMultiplicity_eq_target targets address hlegal hweights hY]
  by_cases hz : z < coarseTotal depth
  · rw [model.zYBoundaryMultiplicity_eq_target targets address hlegal hweights hX
      part z word hz]
    simp [CompatibilityTargets.zBoundaryAggregate, hz]
  · rw [model.restricted_zYBoundary_eq_zero address hlegal hweights
      (model.chunks .Z (address .Z)) part z word hz]
    simp [CompatibilityTargets.zBoundaryAggregate, hz]

/-! ## Adapter from the paper's pooled-all zero-outs -/

/-- The hypotheses literally enforced before the paper's first `Y`
compatibility cleanup. -/
def PassesYPooledAllZeroOut
    (model : CompatibilityModel A Part depth samples)
    (targets : CompatibilityTargets Part depth)
    (pooled : PooledAllTargets targets) (address : BlockAddress A) : Prop :=
  model.IsFineLegal address ∧
    model.HasCoarseWeights address ∧
    model.MatchesExact address .X targets.xExact ∧
    model.MatchesYPooledAll address pooled.yAll

/-- The analogous pooled-all hypotheses for the paper's first `Z`
compatibility cleanup. -/
def PassesZPooledAllZeroOut
    (model : CompatibilityModel A Part depth samples)
    (targets : CompatibilityTargets Part depth)
    (pooled : PooledAllTargets targets) (address : BlockAddress A) : Prop :=
  model.IsFineLegal address ∧
    model.HasCoarseWeights address ∧
    model.MatchesExact address .X targets.xExact ∧
    model.MatchesExact address .Y targets.yExact ∧
    model.MatchesZPooledAll address pooled.zAll

/-- Pooled-all `Y` data imply the positive-cell profile.  Cancellation occurs
only after the same explicitly identified boundary summand appears on both
sides. -/
theorem yPositiveProfile_of_matchesPooledAll
    (model : CompatibilityModel A Part depth samples)
    (targets : CompatibilityTargets Part depth)
    (pooled : PooledAllTargets targets) (address : BlockAddress A)
    (hlegal : model.IsFineLegal address)
    (hweights : model.HasCoarseWeights address)
    (hX : model.MatchesExact address .X targets.xExact)
    (hAll : model.MatchesYPooledAll address pooled.yAll) :
    ∀ part y word,
      cellMultiplicity
          (fun sample ↦ yCompatibilityCell (model.coarse address sample))
          (model.chunks .Y (address .Y)) (.pooled part y) word =
        targets.yPooled part y word := by
  intro part y word
  have hdecompose := model.yPooledAllMultiplicity_decompose address
    (model.chunks .Y (address .Y)) part y word
  rw [hAll part y word, pooled.y_decompose part y word,
    model.yBoundaryMultiplicity_eq_target targets address hlegal hweights hX]
      at hdecompose
  exact (Nat.add_left_cancel hdecompose).symm

/-- Pooled-all `Z` data imply the positive-cell profile, with the overlapping
boundary endpoint removed exactly once. -/
theorem zPositiveProfile_of_matchesPooledAll
    (model : CompatibilityModel A Part depth samples)
    (targets : CompatibilityTargets Part depth)
    (pooled : PooledAllTargets targets) (address : BlockAddress A)
    (hlegal : model.IsFineLegal address)
    (hweights : model.HasCoarseWeights address)
    (hX : model.MatchesExact address .X targets.xExact)
    (hY : model.MatchesExact address .Y targets.yExact)
    (hAll : model.MatchesZPooledAll address pooled.zAll) :
    ∀ part z word,
      cellMultiplicity
          (fun sample ↦ zCompatibilityCell (model.coarse address sample))
          (model.chunks .Z (address .Z)) (.pooled part z) word =
        targets.zPooled part z word := by
  intro part z word
  have hdecompose := model.zPooledAllMultiplicity_decompose address
    (model.chunks .Z (address .Z)) part z word
  rw [hAll part z word, pooled.z_decompose part z word,
    model.zBoundaryMultiplicity_eq_target targets address hlegal hweights hX hY]
      at hdecompose
  exact (Nat.add_left_cancel hdecompose).symm

/-- Exact adapter from the paper's pooled-all `Y` zero-out to the
partition-friendly `PassesYFirstZeroOut` interface. -/
theorem passesYFirstZeroOut_of_pooledAll
    (model : CompatibilityModel A Part depth samples)
    (targets : CompatibilityTargets Part depth)
    (pooled : PooledAllTargets targets) (address : BlockAddress A)
    (hpasses : model.PassesYPooledAllZeroOut targets pooled address) :
    model.PassesYFirstZeroOut targets address := by
  rcases hpasses with ⟨hlegal, hweights, hX, hAll⟩
  exact ⟨hlegal, hweights, hX,
    model.yPositiveProfile_of_matchesPooledAll targets pooled address
      hlegal hweights hX hAll⟩

/-- Exact adapter from the paper's pooled-all `Z` zero-out to the
partition-friendly `PassesZFirstZeroOut` interface. -/
theorem passesZFirstZeroOut_of_pooledAll
    (model : CompatibilityModel A Part depth samples)
    (targets : CompatibilityTargets Part depth)
    (pooled : PooledAllTargets targets) (address : BlockAddress A)
    (hpasses : model.PassesZPooledAllZeroOut targets pooled address) :
    model.PassesZFirstZeroOut targets address := by
  rcases hpasses with ⟨hlegal, hweights, hX, hY, hAll⟩
  exact ⟨hlegal, hweights, hX, hY,
    model.zPositiveProfile_of_matchesPooledAll targets pooled address
      hlegal hweights hX hY hAll⟩

/-- The complete finite compatibility-soundness interface follows from the
paper's literal pooled-all first-zero-out conditions. -/
theorem yzCompatibility_sound_of_pooledAll
    [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]
    (model : CompatibilityModel A Part depth samples)
    (targets : CompatibilityTargets Part depth)
    (pooled : PooledAllTargets targets)
    (ambient : Finset (BlockAddress A))
    (hpassesY : ∀ address ∈ ambient,
      model.PassesYPooledAllZeroOut targets pooled address)
    (hpassesZ : ∀ address ∈ ambient,
      model.PassesZPooledAllZeroOut targets pooled address) :
    IsCompatibilitySound ambient .Y (model.CompatibleY targets) ∧
      IsCompatibilitySound
        (compatibilityIsolatedSupport ambient .Y (model.CompatibleY targets))
        .Z (model.CompatibleZ targets) := by
  apply model.yzCompatibility_sound targets ambient
  · intro address haddress
    exact model.passesYFirstZeroOut_of_pooledAll targets pooled address
      (hpassesY address haddress)
  · intro address haddress
    exact model.passesZFirstZeroOut_of_pooledAll targets pooled address
      (hpassesZ address haddress)

end CellDecompositions

end CompatibilityModel


end MoreAsymmetryCompatibility
end AlgebraicComplexity
