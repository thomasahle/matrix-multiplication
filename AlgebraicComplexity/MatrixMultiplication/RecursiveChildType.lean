/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.RecursiveChildCompatibilityModel

set_option autoImplicit false

/-!
# Exact integral types for recursive child splits

The recursive constituent theorem prescribes an ordered split distribution `alpha` for the
left child of every parent occurrence.  At finite block length this is an integral multiplicity
table on the bounded child-shape alphabet.  Structural-zero shapes are allowed.  The labelled
right occurrences are not an independent input: they are the coordinatewise complements of the
left occurrences.

This module packages that finite interface without mentioning a tensor construction, optimizer,
or asymptotic estimate.  Its main theorem says that selecting the left-child type forces the
literal paper occurrence table

`alphaCounts u + alphaCounts (parent - u)`.
-/

open scoped BigOperators

namespace AlgebraicComplexity
namespace MoreAsymmetryCompatibility

open Tensor

universe u v

/-- A finite ordered recursive-split type.  Unlike `PositiveIntegralProfile`, zero counts are
permitted because a certificate split distribution normally has structural zeros. -/
structure ExactRecursiveSplitType (parent : Leg → ℕ) (childTotal samples : ℕ) where
  count : RecursiveChildShape parent childTotal → ℕ
  total : ∑ child, count child = samples

namespace ExactRecursiveSplitType

variable {parent : Leg → ℕ} {childTotal samples : ℕ}

/-- One visible coordinate of a recursive child shape.  Every coordinate is at most the
common child total because the other two coordinates are nonnegative. -/
def coordinate (c : Leg) (child : RecursiveChildShape parent childTotal) :
    Fin (childTotal + 1) :=
  ⟨child.get c, by
    have htotal := child.total_eq
    cases c <;> simp only [RecursiveChildShape.get_X,
      RecursiveChildShape.get_Y, RecursiveChildShape.get_Z] at * <;> omega⟩

@[simp] theorem coordinate_val (c : Leg)
    (child : RecursiveChildShape parent childTotal) :
    ((coordinate c child : Fin (childTotal + 1)) : ℕ) = child.get c :=
  rfl

/-- The visible three-coordinate tuple of one ordered child shape. -/
abbrev CoordinateTriple (childTotal : ℕ) :=
  Fin (childTotal + 1) × Fin (childTotal + 1) × Fin (childTotal + 1)

/-- Forget the parent bounds of a child shape while retaining all three visible coordinates. -/
def coordinateTriple (child : RecursiveChildShape parent childTotal) :
    CoordinateTriple childTotal :=
  (coordinate .X child, coordinate .Y child, coordinate .Z child)

/-- The three-coordinate observation loses no child-shape information. -/
theorem coordinateTriple_injective :
    Function.Injective
      (coordinateTriple : RecursiveChildShape parent childTotal → CoordinateTriple childTotal) := by
  intro left right heq
  apply RecursiveChildShape.ext
  intro c
  cases c with
  | X => exact congrArg (fun value ↦ (value.1 : ℕ)) heq
  | Y => exact congrArg (fun value ↦ (value.2.1 : ℕ)) heq
  | Z => exact congrArg (fun value ↦ (value.2.2 : ℕ)) heq

/-- Pushing an integral child-shape profile through all three visible coordinates loses no
information.  This is the exact finite counterpart of the fact that the three recursive split
coordinates determine the split state. -/
theorem mappedType_coordinateTriple_injective :
    Function.Injective
      (WordType.mappedType
        (coordinateTriple :
          RecursiveChildShape parent childTotal → CoordinateTriple childTotal)) := by
  classical
  intro left right heq
  funext child
  have hchild := congrFun heq (coordinateTriple child)
  have hfiber :
      WordType.letterFiber
          (coordinateTriple :
            RecursiveChildShape parent childTotal → CoordinateTriple childTotal)
          (coordinateTriple child) = {child} := by
    ext other
    simp only [WordType.mem_letterFiber, Finset.mem_singleton]
    exact coordinateTriple_injective.eq_iff
  unfold WordType.mappedType at hchild
  rw [hfiber] at hchild
  simpa using hchild

/-- Exact marginal count table seen on one tensor leg.  This is a pushforward rather than a
separate certificate field, so the three marginal selectors cannot drift from `alpha`. -/
noncomputable def marginalCount
    (alpha : ExactRecursiveSplitType parent childTotal samples) (c : Leg) :
    Fin (childTotal + 1) → ℕ :=
  WordType.mappedType (coordinate c) alpha.count

/-- Joint visible count table of the ordered split law.  It is stored as a pushforward so that
the marked hashing family and all three marginal selectors share one source of truth. -/
noncomputable def coordinateTripleCount
    (alpha : ExactRecursiveSplitType parent childTotal samples) :
    CoordinateTriple childTotal → ℕ :=
  WordType.mappedType coordinateTriple alpha.count

/-- Equality of visible joint count tables is equivalent to equality of the underlying ordered
child-shape count tables. -/
theorem coordinateTripleCount_eq_iff
    (alpha : ExactRecursiveSplitType parent childTotal samples)
    (profile : RecursiveChildShape parent childTotal → ℕ) :
    WordType.mappedType coordinateTriple profile = alpha.coordinateTripleCount ↔
      profile = alpha.count := by
  rw [coordinateTripleCount]
  exact mappedType_coordinateTriple_injective.eq_iff

/-- A finite ordered child-shape word has type `alpha` exactly when its visible coordinate-triple
word has the marked joint type stored by `alpha`. -/
theorem multiplicity_coordinateTriple_comp_eq_coordinateTripleCount_iff
    (alpha : ExactRecursiveSplitType parent childTotal samples)
    (word : Fin samples → RecursiveChildShape parent childTotal) :
    WordType.multiplicity (coordinateTriple ∘ word) = alpha.coordinateTripleCount ↔
      WordType.multiplicity word = alpha.count := by
  rw [WordType.multiplicity_comp_eq_mappedType, coordinateTripleCount_eq_iff]

/-- The joint visible count table has the prescribed sample mass. -/
theorem coordinateTripleCount_total
    (alpha : ExactRecursiveSplitType parent childTotal samples) :
    ∑ triple, alpha.coordinateTripleCount triple = samples := by
  rw [coordinateTripleCount, WordType.sum_mappedType, alpha.total]

/-- The marked visible joint table is a legal word type. -/
theorem coordinateTripleCount_mem_types
    (alpha : ExactRecursiveSplitType parent childTotal samples) :
    alpha.coordinateTripleCount ∈ WordType.types (CoordinateTriple childTotal) samples := by
  rw [WordType.mem_types]
  exact alpha.coordinateTripleCount_total

/-- Projecting the visible joint table to a leg gives the corresponding stored marginal table. -/
theorem mappedType_coordinateTripleCount_fst
    (alpha : ExactRecursiveSplitType parent childTotal samples) :
    WordType.mappedType Prod.fst alpha.coordinateTripleCount = alpha.marginalCount .X := by
  rw [coordinateTripleCount, marginalCount,
    WordType.mappedType_comp]
  rfl

/-- `Y`-coordinate analogue of `mappedType_coordinateTripleCount_fst`. -/
theorem mappedType_coordinateTripleCount_snd_fst
    (alpha : ExactRecursiveSplitType parent childTotal samples) :
    WordType.mappedType (fun triple : CoordinateTriple childTotal ↦ triple.2.1)
        alpha.coordinateTripleCount =
      alpha.marginalCount .Y := by
  rw [coordinateTripleCount, marginalCount,
    WordType.mappedType_comp]
  rfl

/-- `Z`-coordinate analogue of `mappedType_coordinateTripleCount_fst`. -/
theorem mappedType_coordinateTripleCount_snd_snd
    (alpha : ExactRecursiveSplitType parent childTotal samples) :
    WordType.mappedType (fun triple : CoordinateTriple childTotal ↦ triple.2.2)
        alpha.coordinateTripleCount =
      alpha.marginalCount .Z := by
  rw [coordinateTripleCount, marginalCount,
    WordType.mappedType_comp]
  rfl

/-- Each coordinate marginal has the same total mass as the ordered joint split type. -/
theorem marginalCount_total
    (alpha : ExactRecursiveSplitType parent childTotal samples) (c : Leg) :
    ∑ digit, alpha.marginalCount c digit = samples := by
  rw [marginalCount, WordType.sum_mappedType, alpha.total]

/-- The induced coordinate marginal is a legal method-of-types profile. -/
theorem marginalCount_mem_types
    (alpha : ExactRecursiveSplitType parent childTotal samples) (c : Leg) :
    alpha.marginalCount c ∈ WordType.types (Fin (childTotal + 1)) samples := by
  rw [WordType.mem_types]
  exact alpha.marginalCount_total c

/-- Build a recursive split type by pushing an integral profile on any finite certificate
alphabet to child shapes.  Duplicate source labels are combined automatically. -/
noncomputable def ofMappedCounts {I : Type u} [Fintype I]
    (shape : I → RecursiveChildShape parent childTotal)
    (sourceCount : I → ℕ) (htotal : ∑ i, sourceCount i = samples) :
    ExactRecursiveSplitType parent childTotal samples where
  count := WordType.mappedType shape sourceCount
  total := by
    rw [WordType.sum_mappedType]
    exact htotal

@[simp] theorem ofMappedCounts_count {I : Type u} [Fintype I]
    (shape : I → RecursiveChildShape parent childTotal)
    (sourceCount : I → ℕ) (htotal : ∑ i, sourceCount i = samples)
    (child : RecursiveChildShape parent childTotal) :
    (ofMappedCounts shape sourceCount htotal).count child =
      WordType.mappedType shape sourceCount child :=
  rfl

/-- The count table is a valid method-of-types profile of length `samples`. -/
theorem count_mem_types (alpha : ExactRecursiveSplitType parent childTotal samples) :
    alpha.count ∈ WordType.types (RecursiveChildShape parent childTotal) samples := by
  rw [WordType.mem_types]
  exact alpha.total

/-- Every exact recursive split type is realized by at least one abstract child-shape word. -/
theorem typeClass_nonempty (alpha : ExactRecursiveSplitType parent childTotal samples) :
    (WordType.typeClass samples alpha.count).Nonempty :=
  WordType.typeClass_nonempty alpha.count alpha.count_mem_types

/-- Repeat every count in an exact split type by the same block factor. -/
def scale (alpha : ExactRecursiveSplitType parent childTotal samples) (k : ℕ) :
    ExactRecursiveSplitType parent childTotal (samples * k) where
  count child := alpha.count child * k
  total := by
    simpa [Finset.sum_mul] using congrArg (· * k) alpha.total

@[simp] theorem scale_count
    (alpha : ExactRecursiveSplitType parent childTotal samples) (k : ℕ)
    (child : RecursiveChildShape parent childTotal) :
    (alpha.scale k).count child = alpha.count child * k :=
  rfl

/-- Full labelled occurrence counts induced by the ordered left-child type. -/
def occurrenceCount
    (hparent : parent .X + parent .Y + parent .Z = 2 * childTotal)
    (alpha : ExactRecursiveSplitType parent childTotal samples) :
    RecursiveChildShape parent childTotal → ℕ :=
  fun child ↦ alpha.count child +
    alpha.count ((RecursiveChildShape.complementPerm hparent).symm child)

@[simp] theorem occurrenceCount_apply
    (hparent : parent .X + parent .Y + parent .Z = 2 * childTotal)
    (alpha : ExactRecursiveSplitType parent childTotal samples)
    (child : RecursiveChildShape parent childTotal) :
    alpha.occurrenceCount hparent child =
      alpha.count child +
        alpha.count ((RecursiveChildShape.complementPerm hparent).symm child) :=
  rfl

/-- The labelled occurrence table has twice the mass of the ordered left-child table.  A
self-complementary shape contributes once in each summand and is therefore counted twice. -/
theorem occurrenceCount_total
    (hparent : parent .X + parent .Y + parent .Z = 2 * childTotal)
    (alpha : ExactRecursiveSplitType parent childTotal samples) :
    ∑ child, alpha.occurrenceCount hparent child = 2 * samples := by
  have hperm :
      (∑ child, alpha.count
        ((RecursiveChildShape.complementPerm hparent).symm child)) =
        ∑ child, alpha.count child :=
    Equiv.sum_comp (RecursiveChildShape.complementPerm hparent).symm alpha.count
  rw [show (∑ child, alpha.occurrenceCount hparent child) =
      (∑ child, alpha.count child) +
        ∑ child, alpha.count ((RecursiveChildShape.complementPerm hparent).symm child) by
    simp only [occurrenceCount, Finset.sum_add_distrib]]
  rw [hperm, alpha.total]
  omega

/-- Scaling the ordered split type scales its full labelled occurrence profile pointwise. -/
theorem occurrenceCount_scale
    (hparent : parent .X + parent .Y + parent .Z = 2 * childTotal)
    (alpha : ExactRecursiveSplitType parent childTotal samples) (k : ℕ) :
    (alpha.scale k).occurrenceCount hparent =
      fun child ↦ alpha.occurrenceCount hparent child * k := by
  funext child
  simp only [occurrenceCount, scale_count]
  exact (Nat.add_mul _ _ _).symm

/-- A concrete parent address has type `alpha` when its ordered left-child shape word has exactly
the stored multiplicities. -/
def MatchesLeftChildType
    {A : Leg → Type u} {Part : Type v} {depth n : ℕ}
    (encode : ∀ c, A c → SplitWord (depth + 1))
    (part : Part)
    (address : BlockAddress (fun c ↦ PositiveWord (A c) n))
    (parent : Leg → ℕ)
    (hparent : ∀ c sample,
      splitWordWeight (encode c (positiveWordEquiv (A c) n (address c) sample)) =
        parent c)
    (hlegal : IsParentFineLegal encode address)
    (alpha : ExactRecursiveSplitType parent (coarseTotal depth) (n + 1)) : Prop :=
  WordType.multiplicity
    (recursiveLeftChildShape encode part address parent hparent hlegal) = alpha.count

/-- Exact left-child type selection forces the full labelled occurrence type. -/
theorem multiplicity_recursiveChildShapeWord_eq_occurrenceCount
    {A : Leg → Type u} {Part : Type v} {depth n : ℕ}
    (encode : ∀ c, A c → SplitWord (depth + 1))
    (part : Part)
    (address : BlockAddress (fun c ↦ PositiveWord (A c) n))
    (parent : Leg → ℕ)
    (hparentTotal : parent .X + parent .Y + parent .Z = 2 * coarseTotal depth)
    (hparent : ∀ c sample,
      splitWordWeight (encode c (positiveWordEquiv (A c) n (address c) sample)) =
        parent c)
    (hlegal : IsParentFineLegal encode address)
    (alpha : ExactRecursiveSplitType parent (coarseTotal depth) (n + 1))
    (hmatches : alpha.MatchesLeftChildType encode part address parent hparent hlegal) :
    WordType.multiplicity
        (recursiveChildShapeWord encode part address parent hparentTotal hparent hlegal) =
      alpha.occurrenceCount hparentTotal := by
  exact multiplicity_recursiveChildShapeWord_eq_of_leftType
    encode part address parent hparentTotal hparent hlegal alpha.count hmatches

end ExactRecursiveSplitType
end MoreAsymmetryCompatibility
end AlgebraicComplexity
