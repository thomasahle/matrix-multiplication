/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinogradSortedPairCompatibility
import AlgebraicComplexity.MatrixMultiplication.FeatureCompatibilityContainment

/-!
# Coarse containment forced by sorted-pair compatibility

The affine hash in the recursive Coppersmith--Winograd extraction is applied to coarse total
words.  A compatibility profile therefore has to imply that its candidate label lies over the
same coarse leg as the constituent being tested.  This implication is not true for arbitrary
profile tables: it follows from the support invariant of the reconstructed complete-split
profiles.

This file transports that raw support invariant through the pair-sorting quotient and proves the
samplewise containment equalities needed by the hashing argument.  Pair sorting may identify
`01` with `10`, but it preserves their total exactly, so no representative choice is involved.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor MoreAsymmetryCompatibility

/-- Pushing supported raw complete-split targets through pair sorting preserves the `Y` support
invariant. -/
theorem cwSortedPairPushforwardTargets_isYWeightSupported
    {Part : Type*} (rawTargets : CompatibilityTargets Part 1)
    (hsupported : rawTargets.IsYWeightSupported) :
    (cwSortedPairPushforwardTargets rawTargets).IsYWeightSupported
      splitWordWeight := by
  intro cell symbol hpositive
  cases cell with
  | boundary q =>
      change 0 < WordType.mappedType cwSortedPairSplitWord
        (rawTargets.yExact q.1) symbol at hpositive
      obtain ⟨raw, hrawSymbol, hrawPositive⟩ :=
        WordType.exists_positive_of_mappedType_pos
          cwSortedPairSplitWord (rawTargets.yExact q.1) symbol hpositive
      rw [← hrawSymbol, splitWordWeight_cwSortedPairSplitWord]
      exact hsupported.1 q.1 raw hrawPositive
  | pooled part total =>
      change 0 < WordType.mappedType cwSortedPairSplitWord
        (rawTargets.yPooled part total) symbol at hpositive
      obtain ⟨raw, hrawSymbol, hrawPositive⟩ :=
        WordType.exists_positive_of_mappedType_pos
          cwSortedPairSplitWord (rawTargets.yPooled part total) symbol hpositive
      rw [← hrawSymbol, splitWordWeight_cwSortedPairSplitWord]
      exact hsupported.2 part total raw hrawPositive

/-- Pushing supported raw complete-split targets through pair sorting preserves the `Z` support
invariant. -/
theorem cwSortedPairPushforwardTargets_isZWeightSupported
    {Part : Type*} (rawTargets : CompatibilityTargets Part 1)
    (hsupported : rawTargets.IsZWeightSupported) :
    (cwSortedPairPushforwardTargets rawTargets).IsZWeightSupported
      splitWordWeight := by
  intro cell symbol hpositive
  cases cell with
  | boundary q =>
      change 0 < WordType.mappedType cwSortedPairSplitWord
        (rawTargets.zExact q.1) symbol at hpositive
      obtain ⟨raw, hrawSymbol, hrawPositive⟩ :=
        WordType.exists_positive_of_mappedType_pos
          cwSortedPairSplitWord (rawTargets.zExact q.1) symbol hpositive
      rw [← hrawSymbol, splitWordWeight_cwSortedPairSplitWord]
      exact hsupported.1 q.1 raw hrawPositive
  | pooled part total =>
      change 0 < WordType.mappedType cwSortedPairSplitWord
        (rawTargets.zPooled part total) symbol at hpositive
      obtain ⟨raw, hrawSymbol, hrawPositive⟩ :=
        WordType.exists_positive_of_mappedType_pos
          cwSortedPairSplitWord (rawTargets.zPooled part total) symbol hpositive
      rw [← hrawSymbol, splitWordWeight_cwSortedPairSplitWord]
      exact hsupported.2 part total raw hrawPositive

/-- The full raw support invariant descends through the pair-sorting quotient. -/
theorem cwSortedPairPushforwardTargets_isWeightSupported
    {Part : Type*} (rawTargets : CompatibilityTargets Part 1)
    (hsupported : rawTargets.IsWeightSupported) :
    (cwSortedPairPushforwardTargets rawTargets).IsWeightSupported
      splitWordWeight :=
  ⟨cwSortedPairPushforwardTargets_isYWeightSupported rawTargets hsupported.2.1,
    cwSortedPairPushforwardTargets_isZWeightSupported rawTargets hsupported.2.2⟩

/-- A sorted-pair `Y` label compatible with an address has the same coarse total at every
sample. -/
theorem cwSortedPair_splitWordWeight_eq_Y_of_featureCompatibleY
    {Part : Type*} [DecidableEq Part] (n : ℕ)
    (partAt : Fin (n + 1) → Part)
    (rawTargets : CompatibilityTargets Part 1)
    (hsupported : rawTargets.IsYWeightSupported)
    (label : PositiveWord (SplitWord 1) n)
    (address : BlockAddress (fun _c ↦ PositiveWord (SplitWord 1) n))
    (hcompatible :
      (cwSortedPairFeatureCompatibilityModel n partAt).FeatureCompatibleY
        (cwSortedPairPushforwardTargets rawTargets) label address)
    (sample : Fin (n + 1)) :
    splitWordWeight
        (positiveWordEquiv (SplitWord 1) n label sample) =
      splitWordWeight
        (positiveWordEquiv (SplitWord 1) n (address .Y) sample) := by
  have h := FeatureCompatibilityModel.symbolWeight_eq_coarseY_of_featureCompatibleY
    (cwSortedPairFeatureCompatibilityModel n partAt)
    (cwSortedPairPushforwardTargets rawTargets) splitWordWeight
    (cwSortedPairPushforwardTargets_isYWeightSupported rawTargets hsupported)
    label address hcompatible sample
  exact h

/-- A sorted-pair `Z` label compatible with an address has the same coarse total at every
sample. -/
theorem cwSortedPair_splitWordWeight_eq_Z_of_featureCompatibleZ
    {Part : Type*} [DecidableEq Part] (n : ℕ)
    (partAt : Fin (n + 1) → Part)
    (rawTargets : CompatibilityTargets Part 1)
    (hsupported : rawTargets.IsZWeightSupported)
    (label : PositiveWord (SplitWord 1) n)
    (address : BlockAddress (fun _c ↦ PositiveWord (SplitWord 1) n))
    (hcompatible :
      (cwSortedPairFeatureCompatibilityModel n partAt).FeatureCompatibleZ
        (cwSortedPairPushforwardTargets rawTargets) label address)
    (sample : Fin (n + 1)) :
    splitWordWeight
        (positiveWordEquiv (SplitWord 1) n label sample) =
      splitWordWeight
        (positiveWordEquiv (SplitWord 1) n (address .Z) sample) := by
  have h := FeatureCompatibilityModel.symbolWeight_eq_coarseZ_of_featureCompatibleZ
    (cwSortedPairFeatureCompatibilityModel n partAt)
    (cwSortedPairPushforwardTargets rawTargets) splitWordWeight
    (cwSortedPairPushforwardTargets_isZWeightSupported rawTargets hsupported)
    label address hcompatible sample
  exact h

end AlgebraicComplexity.Examples
