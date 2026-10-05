/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.InterfaceTensor
import AlgebraicComplexity.MatrixMultiplication.CompatibilityTargetCore
import AlgebraicComplexity.Tensor.CompatibilityZeroing

/-!
# Complete-split compatibility cells for asymmetric CW extraction

This file gives an exact finite formulation of the two compatibility predicates used in the
global and recursive constituent stages of *More Asymmetry Yields Faster Matrix
Multiplication*.  A coarse position is tagged by a part and a triple `(i,j,k)`.  The `Y` cleanup
keeps the cells

* the individual triples with `k = 0`; and
* one pooled cell `(part, j, *)` for all triples with `k > 0`.

The `Z` cleanup analogously keeps the individual triples with `i = 0` or `j = 0`, and pools the
remaining triples into `(part, *, *, k)` cells.  Taking the part type to be `PUnit` gives the
global stage; taking it to be the finite term index gives the recursive constituent stage.

The principal results `CompatibilityModel.yCompatibility_sound` and
`CompatibilityModel.zCompatibility_sound` prove the paper's compatibility-soundness claims.
The nontrivial ingredient is proved here: coordinatewise CW legality together with a zero coarse
coordinate transports the exact complete-split multiplicity by digitwise complementation.  The
results are denominator-free and therefore apply directly to finite type classes.
-/

open scoped BigOperators

namespace AlgebraicComplexity
namespace MoreAsymmetryCompatibility

open Tensor

universe u v

/-- If three split digits form a legal CW monomial and the third is zero, the second is the
complement of the first. -/
theorem splitDigit_eq_rev_of_legal_of_right_eq_zero
    (left middle right : SplitDigit)
    (hlegal : (left : ℕ) + (middle : ℕ) + (right : ℕ) = 2)
    (hright : right = 0) :
    middle = Fin.rev left := by
  apply Fin.ext
  simp only [Fin.val_rev]
  have hleft := left.isLt
  have hmiddle := middle.isLt
  have hrightBound := right.isLt
  simp only [hright, Fin.val_zero, add_zero] at hlegal
  omega

/-- Pointwise complementation on one cell transports its exact empirical multiplicities. -/
theorem cellMultiplicity_complement {ι Cell : Type*} [Fintype ι] [DecidableEq Cell]
    {depth : ℕ} (cellOf : ι → Cell) (left right : ι → SplitWord depth) (cell : Cell)
    (hcomplement : ∀ position, cellOf position = cell →
      right position = complementSplitWord (left position))
    (word : SplitWord depth) :
    cellMultiplicity cellOf right cell word =
      cellMultiplicity cellOf left cell (complementSplitWord word) := by
  classical
  unfold cellMultiplicity
  congr 1
  ext position
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hcell, hright⟩
    refine ⟨hcell, ?_⟩
    have h := hcomplement position hcell
    rw [hright] at h
    simpa using congrArg complementSplitWord h.symm
  · rintro ⟨hcell, hleft⟩
    refine ⟨hcell, ?_⟩
    rw [hcomplement position hcell, hleft,
      complementSplitWord_complementSplitWord]

/-- One fine realization of coarse block labels.  `chunks c label sample` is the level-1 split
word used by `label` in that sample, while `coarse address sample` is the tagged coarse triple
containing it. -/
structure CompatibilityModel (A : Leg → Type v) (Part : Type u)
    (depth samples : ℕ) where
  chunks : ∀ c, A c → Fin samples → SplitWord depth
  coarse : BlockAddress A → Fin samples → CoarseIndex Part

namespace CompatibilityModel

variable {A : Leg → Type v} {Part : Type u} {depth samples : ℕ}

/-- The three fine words at every sample form coordinatewise legal CW monomials. -/
def IsFineLegal (model : CompatibilityModel A Part depth samples)
    (address : BlockAddress A) : Prop :=
  ∀ sample position,
    (model.chunks .X (address .X) sample position : ℕ) +
      (model.chunks .Y (address .Y) sample position : ℕ) +
      (model.chunks .Z (address .Z) sample position : ℕ) = 2

/-- Each coarse coordinate is the digit sum of the corresponding fine split word. -/
def HasCoarseWeights (model : CompatibilityModel A Part depth samples)
    (address : BlockAddress A) : Prop :=
  ∀ c sample,
    splitWordWeight (model.chunks c (address c) sample) =
      (model.coarse address sample).get c

/-- A split word of weight zero is the all-zero word. -/
theorem splitWord_eq_zero_of_weight_eq_zero (word : SplitWord depth)
    (hweight : splitWordWeight word = 0) :
    word = 0 := by
  funext position
  apply Fin.ext
  have hzero : ∀ p, (word p : ℕ) = 0 := by
    have hsum : (∑ p, (word p : ℕ)) = 0 := hweight
    exact fun p ↦ (Finset.sum_eq_zero_iff.mp hsum) p (Finset.mem_univ p)
  simpa using hzero position

/-- On a coarse cell with zero `Z` coordinate, the fine `Y` word is the complement of the fine
`X` word. -/
theorem y_eq_complement_x_of_z_eq_zero
    (model : CompatibilityModel A Part depth samples)
    (address : BlockAddress A) (hlegal : model.IsFineLegal address)
    (hweights : model.HasCoarseWeights address) (sample : Fin samples)
    (hz : (model.coarse address sample).z = 0) :
    model.chunks .Y (address .Y) sample =
      complementSplitWord (model.chunks .X (address .X) sample) := by
  have hzWeight : splitWordWeight (model.chunks .Z (address .Z) sample) = 0 := by
    simpa [CoarseIndex.get, hz] using hweights .Z sample
  have hzWord : model.chunks .Z (address .Z) sample = 0 :=
    splitWord_eq_zero_of_weight_eq_zero _ hzWeight
  funext position
  exact splitDigit_eq_rev_of_legal_of_right_eq_zero
    (model.chunks .X (address .X) sample position)
    (model.chunks .Y (address .Y) sample position)
    (model.chunks .Z (address .Z) sample position)
    (hlegal sample position) (congrFun hzWord position)

/-- On a coarse cell with zero `Y` coordinate, the fine `Z` word is the complement of the fine
`X` word. -/
theorem z_eq_complement_x_of_y_eq_zero
    (model : CompatibilityModel A Part depth samples)
    (address : BlockAddress A) (hlegal : model.IsFineLegal address)
    (hweights : model.HasCoarseWeights address) (sample : Fin samples)
    (hy : (model.coarse address sample).y = 0) :
    model.chunks .Z (address .Z) sample =
      complementSplitWord (model.chunks .X (address .X) sample) := by
  have hyWeight : splitWordWeight (model.chunks .Y (address .Y) sample) = 0 := by
    simpa [CoarseIndex.get, hy] using hweights .Y sample
  have hyWord : model.chunks .Y (address .Y) sample = 0 :=
    splitWord_eq_zero_of_weight_eq_zero _ hyWeight
  funext position
  have h := splitDigit_eq_rev_of_legal_of_right_eq_zero
    (model.chunks .X (address .X) sample position)
    (model.chunks .Z (address .Z) sample position)
    (model.chunks .Y (address .Y) sample position)
    (by simpa [add_assoc, add_left_comm, add_comm] using hlegal sample position)
    (congrFun hyWord position)
  exact h

/-- On a coarse cell with zero `X` coordinate, the fine `Z` word is the complement of the fine
`Y` word. -/
theorem z_eq_complement_y_of_x_eq_zero
    (model : CompatibilityModel A Part depth samples)
    (address : BlockAddress A) (hlegal : model.IsFineLegal address)
    (hweights : model.HasCoarseWeights address) (sample : Fin samples)
    (hx : (model.coarse address sample).x = 0) :
    model.chunks .Z (address .Z) sample =
      complementSplitWord (model.chunks .Y (address .Y) sample) := by
  have hxWeight : splitWordWeight (model.chunks .X (address .X) sample) = 0 := by
    simpa [CoarseIndex.get, hx] using hweights .X sample
  have hxWord : model.chunks .X (address .X) sample = 0 :=
    splitWord_eq_zero_of_weight_eq_zero _ hxWeight
  funext position
  have h := splitDigit_eq_rev_of_legal_of_right_eq_zero
    (model.chunks .Y (address .Y) sample position)
    (model.chunks .Z (address .Z) sample position)
    (model.chunks .X (address .X) sample position)
    (by simpa [add_assoc, add_left_comm, add_comm] using hlegal sample position)
    (congrFun hxWord position)
  exact h

end CompatibilityModel

/-- Compatibility cells for the `Y` cleanup: exact boundary triples with `k=0`, and pooled
`(part,*,j,+)` cells for `k>0`. -/
inductive YCompatibilityCell (Part : Type u) where
  | boundary (q : {q : CoarseIndex Part // q.z = 0})
  | pooled (part : Part) (y : ℕ)
  deriving DecidableEq

/-- The concrete partition-friendly `Y` compatibility-cell map used in the paper's constituent
compatibility-counting claim. -/
def yCompatibilityCell {Part : Type u} [DecidableEq Part] (q : CoarseIndex Part) :
    YCompatibilityCell Part :=
  if hz : q.z = 0 then .boundary ⟨q, hz⟩ else .pooled q.part q.y

/-- Compatibility cells for the `Z` cleanup: exact boundary triples with `i=0` or `j=0`, and
pooled `(part,+,+,k)` cells for `i,j>0`. -/
inductive ZCompatibilityCell (Part : Type u) where
  | boundary (q : {q : CoarseIndex Part // q.x = 0 ∨ q.y = 0})
  | pooled (part : Part) (z : ℕ)
  deriving DecidableEq

/-- The concrete partition-friendly `Z` compatibility-cell map used in the paper's constituent
compatibility-counting claim. -/
def zCompatibilityCell {Part : Type u} [DecidableEq Part] (q : CoarseIndex Part) :
    ZCompatibilityCell Part :=
  if hboundary : q.x = 0 ∨ q.y = 0 then
    .boundary ⟨q, hboundary⟩
  else
    .pooled q.part q.z

/-! ## Ordered child occurrences and pooled weights -/

/-- The two logical coordinates on which the paper performs compatibility cleanup. -/
inductive LogicalCoordinate where
  | Y
  | Z
  deriving DecidableEq

instance : Fintype LogicalCoordinate where
  elems := {.Y, .Z}
  complete coordinate := by cases coordinate <;> simp

/-- An ordered parent split has one occurrence on each child side.  Keeping these constructors
distinct is essential when the split is self-complementary. -/
inductive ChildSide where
  | left
  | right
  deriving DecidableEq

instance : Fintype ChildSide where
  elems := {.left, .right}
  complete side := by cases side <;> simp

/-- A compatibility occurrence records its logical coordinate as a type index, together with the
ordered parent split and one of its two child sides.  This is deliberately a product, not a set
of child splits: when `u = complement u`, the left and right occurrences remain distinct. -/
abbrev SplitOccurrence (_coordinate : LogicalCoordinate) (U : Type*) := U × ChildSide

namespace SplitOccurrence

variable {U : Type*} {coordinate : LogicalCoordinate}

/-- Ordered split which generated an occurrence. -/
def orderedSplit (occurrence : SplitOccurrence coordinate U) : U := occurrence.1

/-- Child side of an occurrence. -/
def side (occurrence : SplitOccurrence coordinate U) : ChildSide := occurrence.2

/-- Child split seen at an occurrence. -/
def childSplit (complement : Equiv.Perm U)
    (occurrence : SplitOccurrence coordinate U) : U :=
  match occurrence.side with
  | .left => occurrence.orderedSplit
  | .right => complement occurrence.orderedSplit

/-- Unnormalized occurrence mass.  Each ordered split contributes its full `alpha` mass once on
the left and once on the right. -/
def mass [Fintype U] (alpha : ProbabilityVector U)
    (occurrence : SplitOccurrence coordinate U) : ℝ :=
  alpha.weight occurrence.orderedSplit

private theorem sum_childSide {M : Type*} [AddCommMonoid M] (f : ChildSide → M) :
    (∑ side, f side) = f .left + f .right := by
  change (∑ side ∈ ({.left, .right} : Finset ChildSide), f side) = _
  simp

/-- For either fixed logical coordinate, the total child-occurrence mass is exactly two. -/
theorem sum_mass_for_logical_eq_two [Fintype U]
    (alpha : ProbabilityVector U) (coordinate : LogicalCoordinate) :
    (∑ occurrence : SplitOccurrence coordinate U, occurrence.mass alpha) = 2 := by
  classical
  rw [Fintype.sum_prod_type]
  simp_rw [sum_childSide]
  change (∑ (u : U), (alpha.weight u + alpha.weight u)) = 2
  calc
    (∑ (u : U), (alpha.weight u + alpha.weight u)) =
        (∑ (u : U), alpha.weight u) + ∑ (u : U), alpha.weight u := Finset.sum_add_distrib
    _ = 2 := by rw [alpha.total]; norm_num

end SplitOccurrence

/-- A logical compatibility cell is tagged by whether it belongs to the `Y` or `Z` cleanup. -/
inductive LogicalCompatibilityCell (Part : Type u) where
  | y (cell : YCompatibilityCell Part)
  | z (cell : ZCompatibilityCell Part)
  deriving DecidableEq

/-- Push a child occurrence to its unique concrete `Y`/`Z` compatibility cell. -/
def occurrenceCell {Part : Type u} [DecidableEq Part]
    (coordinate : LogicalCoordinate)
    (complement : Equiv.Perm (CoarseIndex Part))
    (occurrence : SplitOccurrence coordinate (CoarseIndex Part)) :
    LogicalCompatibilityCell Part :=
  match coordinate with
  | .Y => .y (yCompatibilityCell (occurrence.childSplit complement))
  | .Z => .z (zCompatibilityCell (occurrence.childSplit complement))

/-- Every ordered occurrence belongs to exactly one logical compatibility cell. -/
theorem existsUnique_occurrenceCell {Part : Type u} [DecidableEq Part]
    (coordinate : LogicalCoordinate)
    (complement : Equiv.Perm (CoarseIndex Part))
    (occurrence : SplitOccurrence coordinate (CoarseIndex Part)) :
    ∃! cell, occurrenceCell coordinate complement occurrence = cell := by
  exact ⟨occurrenceCell coordinate complement occurrence, rfl, fun cell hcell ↦ hcell.symm⟩

section OccurrenceWeights

variable {U Cell Symbol : Type*} [Fintype U] [DecidableEq Cell]

/-- Occurrence mass pushed to one cell at one fixed logical coordinate. -/
noncomputable def occurrenceCellMass (alpha : ProbabilityVector U)
    (complement : Equiv.Perm U) (coordinate : LogicalCoordinate)
    (cellOf : U → Cell) (cell : Cell) : ℝ :=
  ∑ occurrence : SplitOccurrence coordinate U,
    if cellOf (occurrence.childSplit complement) = cell then
      occurrence.mass alpha
    else 0

/-- The evaluator's cell mass: a child split `v` receives occurrence weight
`alpha(v) + alpha(complement(v))`. -/
noncomputable def evaluatorCellMass (alpha : ProbabilityVector U)
    (complement : Equiv.Perm U) (cellOf : U → Cell) (cell : Cell) : ℝ :=
  ∑ child,
    if cellOf child = cell then
      alpha.weight child + alpha.weight (complement.symm child)
    else 0

/-- Pushing the two explicitly labelled occurrences through the cell map gives exactly the
evaluator formula.  In particular, a self-complementary split contributes `2 * alpha(u)`, rather
than being deduplicated. -/
theorem occurrenceCellMass_eq_evaluatorCellMass (alpha : ProbabilityVector U)
    (complement : Equiv.Perm U) (coordinate : LogicalCoordinate)
    (cellOf : U → Cell) (cell : Cell) :
    occurrenceCellMass alpha complement coordinate cellOf cell =
      evaluatorCellMass alpha complement cellOf cell := by
  classical
  unfold occurrenceCellMass evaluatorCellMass
  have hreindex :
      (∑ u, if cellOf (complement u) = cell then alpha.weight u else 0) =
        ∑ v, if cellOf v = cell then alpha.weight (complement.symm v) else 0 := by
    simpa using
      (Equiv.sum_comp complement
        (fun v ↦ if cellOf v = cell then alpha.weight (complement.symm v) else 0))
  rw [Fintype.sum_prod_type]
  simp_rw [SplitOccurrence.sum_childSide]
  change
    (∑ (u : U), ((if cellOf u = cell then alpha.weight u else 0) +
      (if cellOf (complement u) = cell then alpha.weight u else 0))) = _
  rw [Finset.sum_add_distrib, hreindex]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro child _
  by_cases hcell : cellOf child = cell <;> simp [hcell]

/-- With the self-inverse complement used by recursive CW splits, the evaluator formula has the
paper's literal occurrence weight `alpha(v) + alpha(complement(v))`. -/
theorem occurrenceCellMass_eq_paper_sum (alpha : ProbabilityVector U)
    (complement : Equiv.Perm U) (hselfInverse : complement.symm = complement)
    (coordinate : LogicalCoordinate) (cellOf : U → Cell) (cell : Cell) :
    occurrenceCellMass alpha complement coordinate cellOf cell =
      ∑ child,
        if cellOf child = cell then
          alpha.weight child + alpha.weight (complement child)
        else 0 := by
  rw [occurrenceCellMass_eq_evaluatorCellMass]
  simp [evaluatorCellMass, hselfInverse]

/-- A self-complementary child split retains two labelled occurrences, hence weight
`2 * alpha(u)`. -/
theorem selfComplementary_occurrenceWeight (alpha : ProbabilityVector U)
    (complement : Equiv.Perm U) (hselfInverse : complement.symm = complement)
    (u : U) (hfixed : complement u = u) :
    alpha.weight u + alpha.weight (complement.symm u) = 2 * alpha.weight u := by
  rw [hselfInverse, hfixed]
  ring

/-- `Y`-cell specialization of the ordered-occurrence pushforward identity. -/
theorem yOccurrenceCellMass_eq_paper_sum {Part : Type u} [DecidableEq Part]
    (alpha : ProbabilityVector U) (complement : Equiv.Perm U)
    (hselfInverse : complement.symm = complement)
    (splitValue : U → CoarseIndex Part) (cell : YCompatibilityCell Part) :
    occurrenceCellMass alpha complement .Y
        (fun u ↦ yCompatibilityCell (splitValue u)) cell =
      ∑ child,
        if yCompatibilityCell (splitValue child) = cell then
          alpha.weight child + alpha.weight (complement child)
        else 0 :=
  occurrenceCellMass_eq_paper_sum alpha complement hselfInverse .Y
    (fun u ↦ yCompatibilityCell (splitValue u)) cell

/-- `Z`-cell specialization of the ordered-occurrence pushforward identity. -/
theorem zOccurrenceCellMass_eq_paper_sum {Part : Type u} [DecidableEq Part]
    (alpha : ProbabilityVector U) (complement : Equiv.Perm U)
    (hselfInverse : complement.symm = complement)
    (splitValue : U → CoarseIndex Part) (cell : ZCompatibilityCell Part) :
    occurrenceCellMass alpha complement .Z
        (fun u ↦ zCompatibilityCell (splitValue u)) cell =
      ∑ child,
        if zCompatibilityCell (splitValue child) = cell then
          alpha.weight child + alpha.weight (complement child)
        else 0 :=
  occurrenceCellMass_eq_paper_sum alpha complement hselfInverse .Z
    (fun u ↦ zCompatibilityCell (splitValue u)) cell

/-- Occurrence mass of one child symbol pushed to one cell. -/
noncomputable def occurrenceCellSymbolMass [Fintype Symbol]
    (alpha : ProbabilityVector U) (complement : Equiv.Perm U)
    (coordinate : LogicalCoordinate) (cellOf : U → Cell)
    (childLaw : U → ProbabilityVector Symbol) (cell : Cell) (symbol : Symbol) : ℝ :=
  ∑ occurrence : SplitOccurrence coordinate U,
    if cellOf (occurrence.childSplit complement) = cell then
      occurrence.mass alpha *
        (childLaw (occurrence.childSplit complement)).weight symbol
    else 0

/-- The evaluator's unnormalized pooled symbol mass. -/
noncomputable def evaluatorCellSymbolMass [Fintype Symbol]
    (alpha : ProbabilityVector U) (complement : Equiv.Perm U)
    (cellOf : U → Cell) (childLaw : U → ProbabilityVector Symbol)
    (cell : Cell) (symbol : Symbol) : ℝ :=
  ∑ child,
    if cellOf child = cell then
      (alpha.weight child + alpha.weight (complement.symm child)) *
        (childLaw child).weight symbol
    else 0

/-- The occurrence pushforward produces exactly the unnormalized pooled law used by the
certificate evaluator. -/
theorem occurrenceCellSymbolMass_eq_evaluatorCellSymbolMass [Fintype Symbol]
    (alpha : ProbabilityVector U) (complement : Equiv.Perm U)
    (coordinate : LogicalCoordinate) (cellOf : U → Cell)
    (childLaw : U → ProbabilityVector Symbol) (cell : Cell) (symbol : Symbol) :
    occurrenceCellSymbolMass alpha complement coordinate cellOf childLaw cell symbol =
      evaluatorCellSymbolMass alpha complement cellOf childLaw cell symbol := by
  classical
  unfold occurrenceCellSymbolMass evaluatorCellSymbolMass
  have hreindex :
      (∑ u, if cellOf (complement u) = cell then
          alpha.weight u * (childLaw (complement u)).weight symbol else 0) =
        ∑ v, if cellOf v = cell then
          alpha.weight (complement.symm v) * (childLaw v).weight symbol else 0 := by
    simpa using
      (Equiv.sum_comp complement
        (fun v ↦ if cellOf v = cell then
          alpha.weight (complement.symm v) * (childLaw v).weight symbol else 0))
  rw [Fintype.sum_prod_type]
  simp_rw [SplitOccurrence.sum_childSide]
  change
    (∑ (u : U),
      ((if cellOf u = cell then alpha.weight u * (childLaw u).weight symbol else 0) +
      (if cellOf (complement u) = cell then
        alpha.weight u * (childLaw (complement u)).weight symbol else 0))) = _
  rw [Finset.sum_add_distrib, hreindex]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro child _
  by_cases hcell : cellOf child = cell <;> simp [hcell, add_mul]

/-- Literal paper/evaluator form of the pooled symbol numerator for a self-inverse complement. -/
theorem occurrenceCellSymbolMass_eq_paper_sum [Fintype Symbol]
    (alpha : ProbabilityVector U) (complement : Equiv.Perm U)
    (hselfInverse : complement.symm = complement)
    (coordinate : LogicalCoordinate) (cellOf : U → Cell)
    (childLaw : U → ProbabilityVector Symbol) (cell : Cell) (symbol : Symbol) :
    occurrenceCellSymbolMass alpha complement coordinate cellOf childLaw cell symbol =
      ∑ child,
        if cellOf child = cell then
          (alpha.weight child + alpha.weight (complement child)) *
            (childLaw child).weight symbol
        else 0 := by
  rw [occurrenceCellSymbolMass_eq_evaluatorCellSymbolMass]
  simp [evaluatorCellSymbolMass, hselfInverse]

/-- Normalized pooled symbol weight, in the same division form as the numerical evaluator. -/
noncomputable def evaluatorPooledWeight [Fintype Symbol]
    (alpha : ProbabilityVector U) (complement : Equiv.Perm U)
    (cellOf : U → Cell) (childLaw : U → ProbabilityVector Symbol)
    (cell : Cell) (symbol : Symbol) : ℝ :=
  evaluatorCellSymbolMass alpha complement cellOf childLaw cell symbol /
    evaluatorCellMass alpha complement cellOf cell

/-- Normalizing the occurrence pushforward agrees definitionally with the evaluator's pooled
law after the two exact pushforward identities above. -/
theorem occurrencePooledWeight_eq_evaluatorPooledWeight [Fintype Symbol]
    (alpha : ProbabilityVector U) (complement : Equiv.Perm U)
    (coordinate : LogicalCoordinate) (cellOf : U → Cell)
    (childLaw : U → ProbabilityVector Symbol) (cell : Cell) (symbol : Symbol) :
    occurrenceCellSymbolMass alpha complement coordinate cellOf childLaw cell symbol /
        occurrenceCellMass alpha complement coordinate cellOf cell =
      evaluatorPooledWeight alpha complement cellOf childLaw cell symbol := by
  rw [occurrenceCellSymbolMass_eq_evaluatorCellSymbolMass,
    occurrenceCellMass_eq_evaluatorCellMass]
  rfl

end OccurrenceWeights

namespace CompatibilityTargets

variable {Part : Type u} {depth : ℕ}

/-- Prescribed profile of one concrete `Y` compatibility cell. -/
def yCellProfile (targets : CompatibilityTargets Part depth) :
    YCompatibilityCell Part → SplitWord depth → ℕ
  | .boundary q => targets.yExact q.1
  | .pooled part y => targets.yPooled part y

/-- Prescribed profile of one concrete `Z` compatibility cell. -/
def zCellProfile (targets : CompatibilityTargets Part depth) :
    ZCompatibilityCell Part → SplitWord depth → ℕ
  | .boundary q => targets.zExact q.1
  | .pooled part z => targets.zPooled part z

end CompatibilityTargets

namespace CompatibilityModel

variable {A : Leg → Type v} {Part : Type u} [DecidableEq Part]
variable {depth samples : ℕ}

/-- Exact profile match on every individual coarse constituent cell for one tensor leg. -/
def MatchesExact (model : CompatibilityModel A Part depth samples)
    (address : BlockAddress A) (c : Leg)
    (profile : CoarseIndex Part → SplitWord depth → ℕ) : Prop :=
  ∀ q word,
    cellMultiplicity (model.coarse address) (model.chunks c (address c)) q word =
      profile q word

/-- The partition-friendly concrete `Y` compatibility predicate (`Compatibility'` in the
counting proof). -/
def CompatibleY (model : CompatibilityModel A Part depth samples)
    (targets : CompatibilityTargets Part depth) (label : A .Y)
    (address : BlockAddress A) : Prop :=
  ∀ cell word,
    cellMultiplicity (fun sample ↦ yCompatibilityCell (model.coarse address sample))
        (model.chunks .Y label) cell word =
      targets.yCellProfile cell word

/-- The partition-friendly concrete `Z` compatibility predicate (`Compatibility'` in the
counting proof). -/
def CompatibleZ (model : CompatibilityModel A Part depth samples)
    (targets : CompatibilityTargets Part depth) (label : A .Z)
    (address : BlockAddress A) : Prop :=
  ∀ cell word,
    cellMultiplicity (fun sample ↦ zCompatibilityCell (model.coarse address sample))
        (model.chunks .Z label) cell word =
      targets.zCellProfile cell word

/-- Conditions enforced before `Y` compatibility zero-out II.  The pooled clause is zero-out I;
the exact `X` clause is available because hashing made the coarse `X` block unique. -/
def PassesYFirstZeroOut (model : CompatibilityModel A Part depth samples)
    (targets : CompatibilityTargets Part depth) (address : BlockAddress A) : Prop :=
  model.IsFineLegal address ∧
    model.HasCoarseWeights address ∧
    model.MatchesExact address .X targets.xExact ∧
    ∀ part y word,
      cellMultiplicity (fun sample ↦ yCompatibilityCell (model.coarse address sample))
          (model.chunks .Y (address .Y)) (.pooled part y) word =
        targets.yPooled part y word

/-- Conditions enforced before `Z` compatibility zero-out II.  At this point both `X` and `Y`
have exact constituent profiles, while zero-out I enforces the pooled `Z` profiles. -/
def PassesZFirstZeroOut (model : CompatibilityModel A Part depth samples)
    (targets : CompatibilityTargets Part depth) (address : BlockAddress A) : Prop :=
  model.IsFineLegal address ∧
    model.HasCoarseWeights address ∧
    model.MatchesExact address .X targets.xExact ∧
    model.MatchesExact address .Y targets.yExact ∧
    ∀ part z word,
      cellMultiplicity (fun sample ↦ zCompatibilityCell (model.coarse address sample))
          (model.chunks .Z (address .Z)) (.pooled part z) word =
        targets.zPooled part z word

private theorem y_cellMultiplicity_boundary
    (model : CompatibilityModel A Part depth samples) (address : BlockAddress A)
    (sequence : Fin samples → SplitWord depth)
    (q : {q : CoarseIndex Part // q.z = 0}) (word : SplitWord depth) :
    cellMultiplicity (fun sample ↦ yCompatibilityCell (model.coarse address sample))
        sequence (.boundary q) word =
      cellMultiplicity (model.coarse address) sequence q.1 word := by
  classical
  unfold cellMultiplicity
  congr 1
  ext sample
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hcell, hword⟩
    refine ⟨?_, hword⟩
    unfold yCompatibilityCell at hcell
    split at hcell
    · exact congrArg Subtype.val (YCompatibilityCell.boundary.inj hcell)
    · cases hcell
  · rintro ⟨hcoarse, hword⟩
    refine ⟨?_, hword⟩
    rw [hcoarse]
    simp [yCompatibilityCell, q.2]

private theorem z_cellMultiplicity_boundary
    (model : CompatibilityModel A Part depth samples) (address : BlockAddress A)
    (sequence : Fin samples → SplitWord depth)
    (q : {q : CoarseIndex Part // q.x = 0 ∨ q.y = 0}) (word : SplitWord depth) :
    cellMultiplicity (fun sample ↦ zCompatibilityCell (model.coarse address sample))
        sequence (.boundary q) word =
      cellMultiplicity (model.coarse address) sequence q.1 word := by
  classical
  unfold cellMultiplicity
  congr 1
  ext sample
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hcell, hword⟩
    refine ⟨?_, hword⟩
    unfold zCompatibilityCell at hcell
    split at hcell
    · exact congrArg Subtype.val (ZCompatibilityCell.boundary.inj hcell)
    · cases hcell
  · rintro ⟨hcoarse, hword⟩
    refine ⟨?_, hword⟩
    rw [hcoarse]
    simp [zCompatibilityCell, q.2]

/-- Claim 6.8, in exact finite form: every address surviving the first `Y` zero-out is compatible
with the coarse triple that contains it. -/
theorem compatibleY_of_passesYFirstZeroOut
    (model : CompatibilityModel A Part depth samples)
    (targets : CompatibilityTargets Part depth) (address : BlockAddress A)
    (hpasses : model.PassesYFirstZeroOut targets address) :
    model.CompatibleY targets (address .Y) address := by
  rcases hpasses with ⟨hlegal, hweights, hX, hpooled⟩
  intro cell word
  cases cell with
  | pooled part y => exact hpooled part y word
  | boundary q =>
      rw [y_cellMultiplicity_boundary]
      calc
        cellMultiplicity (model.coarse address)
            (model.chunks .Y (address .Y)) q.1 word =
            cellMultiplicity (model.coarse address)
              (model.chunks .X (address .X)) q.1 (complementSplitWord word) := by
          apply cellMultiplicity_complement
          intro sample hsample
          exact model.y_eq_complement_x_of_z_eq_zero address hlegal hweights sample
            (by simpa [hsample] using q.2)
        _ = targets.xExact q.1 (complementSplitWord word) := hX q.1 _
        _ = targets.yExact q.1 word := (targets.yBoundary q.1 q.2 word).symm

/-- Claim 6.12, in exact finite form: every address surviving the first `Z` zero-out is compatible
with the coarse triple that contains it. -/
theorem compatibleZ_of_passesZFirstZeroOut
    (model : CompatibilityModel A Part depth samples)
    (targets : CompatibilityTargets Part depth) (address : BlockAddress A)
    (hpasses : model.PassesZFirstZeroOut targets address) :
    model.CompatibleZ targets (address .Z) address := by
  rcases hpasses with ⟨hlegal, hweights, hX, hY, hpooled⟩
  intro cell word
  cases cell with
  | pooled part z => exact hpooled part z word
  | boundary q =>
      rw [z_cellMultiplicity_boundary]
      rcases q.2 with hx | hy
      · calc
          cellMultiplicity (model.coarse address)
              (model.chunks .Z (address .Z)) q.1 word =
              cellMultiplicity (model.coarse address)
                (model.chunks .Y (address .Y)) q.1 (complementSplitWord word) := by
            apply cellMultiplicity_complement
            intro sample hsample
            exact model.z_eq_complement_y_of_x_eq_zero address hlegal hweights sample
              (by simpa [hsample] using hx)
          _ = targets.yExact q.1 (complementSplitWord word) := hY q.1 _
          _ = targets.zExact q.1 word := (targets.zBoundaryOfY q.1 hx word).symm
      · calc
          cellMultiplicity (model.coarse address)
              (model.chunks .Z (address .Z)) q.1 word =
              cellMultiplicity (model.coarse address)
                (model.chunks .X (address .X)) q.1 (complementSplitWord word) := by
            apply cellMultiplicity_complement
            intro sample hsample
            exact model.z_eq_complement_x_of_y_eq_zero address hlegal hweights sample
              (by simpa [hsample] using hy)
          _ = targets.xExact q.1 (complementSplitWord word) := hX q.1 _
          _ = targets.zExact q.1 word := (targets.zBoundaryOfX q.1 hy word).symm

/-- The finite soundness hypothesis consumed by compatibility zeroing follows solely from the
paper's first-`Y`-zero-out invariants. -/
theorem yCompatibility_sound [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]
    (model : CompatibilityModel A Part depth samples)
    (targets : CompatibilityTargets Part depth)
    (ambient : Finset (BlockAddress A))
    (hpasses : ∀ address ∈ ambient, model.PassesYFirstZeroOut targets address) :
    IsCompatibilitySound ambient .Y (model.CompatibleY targets) := by
  intro address haddress
  exact model.compatibleY_of_passesYFirstZeroOut targets address (hpasses address haddress)

/-- The finite soundness hypothesis consumed by the second compatibility cleanup follows from
the first-`Z`-zero-out invariants. -/
theorem zCompatibility_sound [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]
    (model : CompatibilityModel A Part depth samples)
    (targets : CompatibilityTargets Part depth)
    (ambient : Finset (BlockAddress A))
    (hpasses : ∀ address ∈ ambient, model.PassesZFirstZeroOut targets address) :
    IsCompatibilitySound ambient .Z (model.CompatibleZ targets) := by
  intro address haddress
  exact model.compatibleZ_of_passesZFirstZeroOut targets address (hpasses address haddress)

/-- Direct adapter for the paper's sequential cleanup: if the `Z` first-zero-out invariants hold
on the hash-isolated support, they also give soundness on the smaller support left by `Y`
compatibility isolation. -/
theorem zCompatibility_sound_afterY [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]
    (model : CompatibilityModel A Part depth samples)
    (targets : CompatibilityTargets Part depth)
    (ambient : Finset (BlockAddress A))
    (hpasses : ∀ address ∈ ambient, model.PassesZFirstZeroOut targets address) :
    IsCompatibilitySound
      (compatibilityIsolatedSupport ambient .Y (model.CompatibleY targets))
      .Z (model.CompatibleZ targets) := by
  apply model.zCompatibility_sound targets
  intro address haddress
  exact hpasses address
    (compatibilityIsolatedSupport_subset ambient .Y (model.CompatibleY targets) haddress)

/-- The two soundness witnesses, packaged in exactly the sequential shape consumed by the finite
hashing theorem's `tensor_compatibility_directSum` interface. -/
theorem yzCompatibility_sound [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]
    (model : CompatibilityModel A Part depth samples)
    (targets : CompatibilityTargets Part depth)
    (ambient : Finset (BlockAddress A))
    (hpassesY : ∀ address ∈ ambient, model.PassesYFirstZeroOut targets address)
    (hpassesZ : ∀ address ∈ ambient, model.PassesZFirstZeroOut targets address) :
    IsCompatibilitySound ambient .Y (model.CompatibleY targets) ∧
      IsCompatibilitySound
        (compatibilityIsolatedSupport ambient .Y (model.CompatibleY targets))
        .Z (model.CompatibleZ targets) :=
  ⟨model.yCompatibility_sound targets ambient hpassesY,
    model.zCompatibility_sound_afterY targets ambient hpassesZ⟩

end CompatibilityModel

end MoreAsymmetryCompatibility
end AlgebraicComplexity
