/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Combinatorics.IntegralProfileCounts
import AlgebraicComplexity.Probability.RationalCore
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.NormNum

/-!
# Finite laws and ordered profile data for asymmetric laser certificates

This is the finite-data slice of [duan2023faster], `prelim.tex:294-309,342-366`:
ordered split letters and predetermined physical-leg profiles are different objects.
The natural-number counts retain every declared letter, including legal letters of zero mass.
Their interpretation uses `RationalProbabilityData` and `WordType.profileMass`, not a new
probability or value engine. `LegProfile.countAt` extends an aligned profile by zero.

`ProfileDescriptor.Valid` checks record shape only. Native alphabet completeness is a separate
check; `LegProfile.IsOrderedSplitFor` supplies the ordered-pair check for this first slice.
The complete-word view has three separate physical-leg laws, never a joint three-leg law.
No tensor extraction, native descriptor, producing-rule DAG or final semantic `Checks` is defined.

`SplitChildren` records both labelled occurrences in a binary split, as in
`component_value.tex:205-225`. It must not represent a global coarse mixture, which has one
child per state. Occurrence counting retains the physical-leg transport as part of its key.
-/

set_option autoImplicit false

namespace AlgebraicComplexity.AsymmetricLaserData

open scoped BigOperators

/-- A finite law with an arbitrary common denominator and one count per declared symbol. -/
structure FiniteLaw where
  denominator : Nat
  counts : List Nat

/-- A law is normalized when its denominator is positive and equals the sum of its counts. -/
def FiniteLaw.Valid (law : FiniteLaw) : Prop :=
  0 < law.denominator ∧ law.counts.sum = law.denominator

/-- The aligned count function on all list positions, without discarding zero-count positions. -/
def FiniteLaw.profile (law : FiniteLaw) : Fin law.counts.length → Nat :=
  fun i => law.counts[i.val]

/-- The existing integral-profile mass of the decoded list is its list sum. -/
theorem FiniteLaw.profileMass_profile (law : FiniteLaw) :
    WordType.profileMass law.profile = law.counts.sum := by
  simpa only [WordType.profileMass, FiniteLaw.profile] using Fin.sum_univ_getElem law.counts

/-- Interpret a finite count list as existing exact rational probability data. -/
def FiniteLaw.toRational (law : FiniteLaw) :
    RationalProbabilityData (Fin law.counts.length) where
  weight i := (law.profile i : ℚ) / (law.denominator : ℚ)

/-- A normalized finite law decodes to an exact rational probability vector. -/
theorem FiniteLaw.toRational_isProbability (law : FiniteLaw) (h : law.Valid) :
    law.toRational.IsProbability := by
  constructor
  · intro i
    exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  · change (∑ i, (law.profile i : ℚ) / (law.denominator : ℚ)) = 1
    rw [← Finset.sum_div]
    have hsumNat : (∑ i, law.profile i) = law.denominator :=
      law.profileMass_profile.trans h.2
    have hsum : (∑ i, (law.profile i : ℚ)) = (law.denominator : ℚ) := by
      exact_mod_cast hsumNat
    rw [hsum]
    exact div_self (Nat.cast_ne_zero.mpr (Nat.ne_of_gt h.1))

/-- The interface views have independent per-leg laws; a view does not carry an extraction rule. -/
inductive ProfileView where
  | unrestricted
  | orderedSplit
  | completeWord

/-- One physical leg's complete ordered word alphabet and its aligned law. -/
structure LegProfile where
  physicalLeg : Nat
  alphabet : List (List Nat)
  law : FiniteLaw

/-- Structural profile validity: a physical leg, distinct letters, alignment and normalization.
Native word lengths, weights and alphabet completeness are deliberately checked separately. -/
def LegProfile.Valid (profile : LegProfile) : Prop :=
  profile.physicalLeg < 3 ∧ profile.alphabet.Nodup ∧
    profile.law.counts.length = profile.alphabet.length ∧ profile.law.Valid

/-- Decode an aligned count by letter, with zero outside the declared alphabet.
On invalid data a missing aligned count also returns zero; consumers must check `Valid`. -/
def LegProfile.countAt (profile : LegProfile) (word : List Nat) : Nat :=
  ((profile.alphabet.zip profile.law.counts).lookup word).getD 0

/-- A letter outside the declared alphabet always has zero decoded count. -/
theorem LegProfile.countAt_eq_zero_of_not_mem (profile : LegProfile) (word : List Nat)
    (hword : word ∉ profile.alphabet) : profile.countAt word = 0 := by
  have hlookup : (profile.alphabet.zip profile.law.counts).lookup word = none := by
    apply List.lookup_eq_none_iff.mpr
    intro entry hentry
    have hne : word ≠ entry.1 := by
      intro heq
      apply hword
      rw [heq]
      exact (List.of_mem_zip hentry).1
    simpa using hne
  simp only [LegProfile.countAt, hlookup, Option.getD_none]

/-- The canonical ordered pairs with digits at most `digitBound` and total `degree`.
The left digit orders the list; a legal pair is retained regardless of its primal count. -/
def orderedSplitAlphabet (digitBound degree : Nat) : List (List Nat) :=
  ((List.range (digitBound + 1)).filter fun left =>
    decide (left ≤ degree ∧ degree - left ≤ digitBound)).map fun left => [left, degree - left]

/-- A valid leg profile has exactly the full ordered-pair alphabet at the specified degree. -/
def LegProfile.IsOrderedSplitFor (profile : LegProfile) (digitBound degree : Nat) : Prop :=
  profile.Valid ∧ profile.alphabet = orderedSplitAlphabet digitBound degree

/-- An interface view with separate laws for its constrained physical legs. -/
structure ProfileDescriptor where
  view : ProfileView
  legs : List LegProfile

/-- Structural view validity only: no laws, one law, or three laws in physical-leg order.
This does not replace a native alphabet check or prove that the leg laws are jointly attainable. -/
def ProfileDescriptor.Valid (profile : ProfileDescriptor) : Prop :=
  (∀ leg ∈ profile.legs, leg.Valid) ∧
    match profile.view with
    | .unrestricted => profile.legs = []
    | .orderedSplit => profile.legs.length = 1
    | .completeWord => profile.legs.map LegProfile.physicalLeg = [0, 1, 2]

/-- A reference to a prior value-pair node with an output-to-input physical-leg permutation. -/
structure ChildRef where
  nodeId : Nat
  physicalLegs : List Nat

/-- A reference points backward and its physical-leg table is a permutation of the three legs.
Native/profile transport and matrix-dimension retyping are additional, distinct checks. -/
def ChildRef.ValidBefore (child : ChildRef) (parentId : Nat) : Prop :=
  child.nodeId < parentId ∧ child.physicalLegs.Perm [0, 1, 2]

/-- The two labelled child occurrences of one binary split state, even when they coincide. -/
structure SplitChildren where
  left : ChildRef
  right : ChildRef

/-- Both labelled occurrences have valid backward references. -/
def SplitChildren.ValidBefore (children : SplitChildren) (parentId : Nat) : Prop :=
  children.left.ValidBefore parentId ∧ children.right.ValidBefore parentId

/-- Count both occurrences of one transported child at an integral parent-state count.
Different physical-leg transports are not identified merely because their node IDs agree. -/
def SplitChildren.occurrenceCount (children : SplitChildren) (child : ChildRef)
    (parentCount : Nat) : Nat :=
  (if children.left.nodeId = child.nodeId ∧ children.left.physicalLegs = child.physicalLegs
    then parentCount else 0) +
  (if children.right.nodeId = child.nodeId ∧ children.right.physicalLegs = child.physicalLegs
    then parentCount else 0)

/-- A repeated transported child contributes twice the parent-state count, not once. -/
theorem SplitChildren.occurrenceCount_self (child : ChildRef) (parentCount : Nat) :
    (SplitChildren.mk child child).occurrenceCount child parentCount =
      parentCount + parentCount := by
  simp [SplitChildren.occurrenceCount]

end AlgebraicComplexity.AsymmetricLaserData
