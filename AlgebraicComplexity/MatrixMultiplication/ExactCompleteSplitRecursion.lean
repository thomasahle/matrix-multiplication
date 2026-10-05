/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.InterfaceTensor

/-!
# Exact finite complete-split recursion

The published recursive interface theorem is phrased using probability distributions and an
approximation parameter.  Rational certificate points have a stronger finite formulation:
integer child profiles can be independently concatenated, scaled, and mixed with integer ordered
split counts.  Every resulting row total is then an identity, not an asymptotic hypothesis.

This module implements that denominator-free algebra.  It is independent of Coppersmith--Winograd
tensors, certificate arrays, compatibility cells, and entropy estimates.
-/

open scoped BigOperators

namespace AlgebraicComplexity

namespace CompleteSplitProfile

variable {depth total samples : ℕ}

/-- Repeat every entry of an exact complete-split profile by an integral factor. -/
def scale (profile : CompleteSplitProfile depth total samples) (factor : ℕ) :
    CompleteSplitProfile depth total (samples * factor) where
  counts word := profile.counts word * factor
  isType := by
    rw [WordType.mem_types]
    rw [← Finset.sum_mul, profile.sum_counts]
  supported := by
    intro word hcount
    apply profile.supported word
    intro hzero
    exact hcount (by simp [hzero])

@[simp] theorem scale_counts
    (profile : CompleteSplitProfile depth total samples) (factor : ℕ)
    (word : SplitWord depth) :
    (profile.scale factor).counts word = profile.counts word * factor :=
  rfl

/-- Retype only the aggregate coordinate carried by an exact profile. -/
def castTotal {newTotal : ℕ} (profile : CompleteSplitProfile depth total samples)
    (h : total = newTotal) : CompleteSplitProfile depth newTotal samples :=
  h ▸ profile

@[simp] theorem castTotal_counts {newTotal : ℕ}
    (profile : CompleteSplitProfile depth total samples) (h : total = newTotal)
    (word : SplitWord depth) :
    (profile.castTotal h).counts word = profile.counts word := by
  subst newTotal
  rfl

/-- Independently concatenate two exact child profiles.  The resulting sample count is the
Cartesian product of the two child sample sets. -/
def independentConcat {leftTotal rightTotal leftSamples rightSamples : ℕ}
    (left : CompleteSplitProfile depth leftTotal leftSamples)
    (right : CompleteSplitProfile depth rightTotal rightSamples) :
    CompleteSplitProfile (depth + 1) (leftTotal + rightTotal)
      (leftSamples * rightSamples) where
  counts word :=
    left.counts (splitWordSuccEquiv depth word).1 *
      right.counts (splitWordSuccEquiv depth word).2
  isType := by
    rw [WordType.mem_types]
    calc
      (∑ word,
          left.counts (splitWordSuccEquiv depth word).1 *
            right.counts (splitWordSuccEquiv depth word).2) =
          ∑ pair : SplitWord depth × SplitWord depth,
            left.counts pair.1 * right.counts pair.2 :=
        (splitWordSuccEquiv depth).sum_comp
          (fun pair : SplitWord depth × SplitWord depth ↦
            left.counts pair.1 * right.counts pair.2)
      _ = leftSamples * rightSamples := by
        rw [Fintype.sum_prod_type]
        simp_rw [← Finset.mul_sum]
        rw [right.sum_counts, ← Finset.sum_mul, left.sum_counts]
  supported := by
    intro word hcount
    have hproduct :
        left.counts (splitWordSuccEquiv depth word).1 ≠ 0 ∧
          right.counts (splitWordSuccEquiv depth word).2 ≠ 0 :=
      mul_ne_zero_iff.mp hcount
    rw [splitWordWeight_succ,
      left.supported _ hproduct.1, right.supported _ hproduct.2]

@[simp] theorem independentConcat_counts
    {leftTotal rightTotal leftSamples rightSamples : ℕ}
    (left : CompleteSplitProfile depth leftTotal leftSamples)
    (right : CompleteSplitProfile depth rightTotal rightSamples)
    (word : SplitWord (depth + 1)) :
    (left.independentConcat right).counts word =
      left.counts (splitWordSuccEquiv depth word).1 *
        right.counts (splitWordSuccEquiv depth word).2 :=
  rfl

/-- Integral weighted sum of a finite family of exact profiles with a common interface. -/
def weightedSum {κ : Type*} [Fintype κ]
    {componentSamples alphaSamples : ℕ}
    (alphaCount : κ → ℕ) (halpha : ∑ k, alphaCount k = alphaSamples)
    (component : κ → CompleteSplitProfile depth total componentSamples) :
    CompleteSplitProfile depth total (alphaSamples * componentSamples) where
  counts word := ∑ k, alphaCount k * (component k).counts word
  isType := by
    rw [WordType.mem_types]
    calc
      (∑ word, ∑ k, alphaCount k * (component k).counts word) =
          ∑ k, ∑ word, alphaCount k * (component k).counts word := by
        rw [Finset.sum_comm]
      _ = ∑ k, alphaCount k * componentSamples := by
        apply Finset.sum_congr rfl
        intro k _
        rw [← Finset.mul_sum, (component k).sum_counts]
      _ = alphaSamples * componentSamples := by
        rw [← Finset.sum_mul, halpha]
  supported := by
    intro word hcount
    by_contra hweight
    apply hcount
    apply Finset.sum_eq_zero
    intro k _
    have hcomponent : (component k).counts word = 0 := by
      by_contra hnonzero
      exact hweight ((component k).supported word hnonzero)
    simp [hcomponent]

@[simp] theorem weightedSum_counts {κ : Type*} [Fintype κ]
    {componentSamples alphaSamples : ℕ}
    (alphaCount : κ → ℕ) (halpha : ∑ k, alphaCount k = alphaSamples)
    (component : κ → CompleteSplitProfile depth total componentSamples)
    (word : SplitWord depth) :
    (weightedSum alphaCount halpha component).counts word =
      ∑ k, alphaCount k * (component k).counts word :=
  rfl

end CompleteSplitProfile

/-- One exact product component in a recursive parent profile. -/
structure RecursiveSplitProfileComponent
    (depth parentTotal leftSamples rightSamples : ℕ) where
  leftTotal : ℕ
  rightTotal : ℕ
  total_eq : leftTotal + rightTotal = parentTotal
  left : CompleteSplitProfile depth leftTotal leftSamples
  right : CompleteSplitProfile depth rightTotal rightSamples

namespace RecursiveSplitProfileComponent

/-- Exact independently concatenated parent profile of one recursive split component. -/
def toParent {depth parentTotal leftSamples rightSamples : ℕ}
    (component : RecursiveSplitProfileComponent
      depth parentTotal leftSamples rightSamples) :
    CompleteSplitProfile (depth + 1) parentTotal (leftSamples * rightSamples) :=
  (component.left.independentConcat component.right).castTotal component.total_eq

@[simp] theorem toParent_counts {depth parentTotal leftSamples rightSamples : ℕ}
    (component : RecursiveSplitProfileComponent
      depth parentTotal leftSamples rightSamples)
    (word : SplitWord (depth + 1)) :
    component.toParent.counts word =
      component.left.counts (splitWordSuccEquiv depth word).1 *
        component.right.counts (splitWordSuccEquiv depth word).2 := by
  simp [toParent]

end RecursiveSplitProfileComponent

/-- Exact finite counterpart of a recursive mixture of independently concatenated child
complete-split laws. -/
def recursiveSplitProfile
    {κ : Type*} [Fintype κ]
    {depth parentTotal leftSamples rightSamples alphaSamples : ℕ}
    (alphaCount : κ → ℕ) (halpha : ∑ k, alphaCount k = alphaSamples)
    (component : κ → RecursiveSplitProfileComponent
      depth parentTotal leftSamples rightSamples) :
    CompleteSplitProfile (depth + 1) parentTotal
      (alphaSamples * (leftSamples * rightSamples)) :=
  CompleteSplitProfile.weightedSum alphaCount halpha
    (fun k ↦ (component k).toParent)

@[simp] theorem recursiveSplitProfile_counts
    {κ : Type*} [Fintype κ]
    {depth parentTotal leftSamples rightSamples alphaSamples : ℕ}
    (alphaCount : κ → ℕ) (halpha : ∑ k, alphaCount k = alphaSamples)
    (component : κ → RecursiveSplitProfileComponent
      depth parentTotal leftSamples rightSamples)
    (word : SplitWord (depth + 1)) :
    (recursiveSplitProfile alphaCount halpha component).counts word =
      ∑ k, alphaCount k *
        ((component k).left.counts (splitWordSuccEquiv depth word).1 *
          (component k).right.counts (splitWordSuccEquiv depth word).2) := by
  simp [recursiveSplitProfile]

namespace ExactInterfaceTermParameters

/-- Construct an exact parent interface term from a common ordered split table and, for each
tensor leg and ordered split, a pair of exact child profiles.  All parent normalization and
support obligations are discharged by `recursiveSplitProfile`; clients do not supply a
separately asserted parent row-total theorem. -/
def ofRecursiveProfiles
    {κ : Type*} [Fintype κ]
    {depth alphaSamples leftSamples rightSamples : ℕ}
    (index : LevelConstituentIndex (depth + 1))
    (alphaCount : κ → ℕ) (halpha : ∑ k, alphaCount k = alphaSamples)
    (component : ∀ c, κ → RecursiveSplitProfileComponent
      depth (index.count c) leftSamples rightSamples) :
    ExactInterfaceTermParameters (depth + 1) where
  multiplicity := alphaSamples * (leftSamples * rightSamples)
  index := index
  split c := recursiveSplitProfile alphaCount halpha (component c)

@[simp] theorem ofRecursiveProfiles_multiplicity
    {κ : Type*} [Fintype κ]
    {depth alphaSamples leftSamples rightSamples : ℕ}
    (index : LevelConstituentIndex (depth + 1))
    (alphaCount : κ → ℕ) (halpha : ∑ k, alphaCount k = alphaSamples)
    (component : ∀ c, κ → RecursiveSplitProfileComponent
      depth (index.count c) leftSamples rightSamples) :
    (ofRecursiveProfiles index alphaCount halpha component).multiplicity =
      alphaSamples * (leftSamples * rightSamples) :=
  rfl

@[simp] theorem ofRecursiveProfiles_index
    {κ : Type*} [Fintype κ]
    {depth alphaSamples leftSamples rightSamples : ℕ}
    (index : LevelConstituentIndex (depth + 1))
    (alphaCount : κ → ℕ) (halpha : ∑ k, alphaCount k = alphaSamples)
    (component : ∀ c, κ → RecursiveSplitProfileComponent
      depth (index.count c) leftSamples rightSamples) :
    (ofRecursiveProfiles index alphaCount halpha component).index = index :=
  rfl

@[simp] theorem ofRecursiveProfiles_split_counts
    {κ : Type*} [Fintype κ]
    {depth alphaSamples leftSamples rightSamples : ℕ}
    (index : LevelConstituentIndex (depth + 1))
    (alphaCount : κ → ℕ) (halpha : ∑ k, alphaCount k = alphaSamples)
    (component : ∀ c, κ → RecursiveSplitProfileComponent
      depth (index.count c) leftSamples rightSamples)
    (c : Tensor.Leg) (word : SplitWord (depth + 1)) :
    ((ofRecursiveProfiles index alphaCount halpha component).split c).counts word =
      ∑ k, alphaCount k *
        ((component c k).left.counts (splitWordSuccEquiv depth word).1 *
          (component c k).right.counts (splitWordSuccEquiv depth word).2) := by
  simp [ofRecursiveProfiles]

end ExactInterfaceTermParameters

end AlgebraicComplexity
