/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinogradCompatibility

/-!
# Exact CW compatibility and usefulness zero-outs

This module realizes the ordinary one-letter cleanup order used after asymmetric hashing:

1. keep the exact logical-`X` profiles;
2. enforce the paper's pooled-all logical-`Y` profiles;
3. isolate uniquely compatible `Y` labels;
4. keep useful labels with exact logical-`Y` profiles;
5. enforce the pooled-all logical-`Z` profiles;
6. isolate uniquely compatible `Z` labels; and
7. keep useful labels with exact logical-`Z` profiles.

The pooled-all conditions are genuinely single-label predicates for the native CW encoding, so
their first zero-outs are ordinary `PartitionedTensor.select` restrictions.  The usefulness
conditions may depend on the containing address, but compatibility isolation has already made
the relevant leg injective, so arbitrary exact-profile selection is then a valid variable
zero-out on that leg.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor MoreAsymmetryCompatibility

universe u v w

/-- A pooled-all complete-split profile is a predicate of one native CW block label.  The same
definition serves logical `Y` and logical `Z`; the chosen physical label supplies the coordinate
weight used in the pooled cell. -/
def CWPooledAllLabelMatches {Part : Type v} [DecidableEq Part] {depth n : ℕ}
    (partAt : Fin (n + 1) → Part)
    (profile : Part → ℕ → SplitWord depth → ℕ)
    (label : PositiveWord (PositiveWord CWBlock (2 ^ depth - 1)) n) : Prop :=
  ∀ part coordinate word,
    cellMultiplicity
      (fun sample ↦
        (partAt sample,
          splitWordWeight
            (cwChunkSplitWord depth
              (positiveWordEquiv (PositiveWord CWBlock (2 ^ depth - 1)) n
                label sample))))
      (fun sample ↦
        cwChunkSplitWord depth
          (positiveWordEquiv (PositiveWord CWBlock (2 ^ depth - 1)) n label sample))
      (part, coordinate) word = profile part coordinate word

/-- The semantic pooled-`Y` address predicate is definitionally the corresponding predicate of
the physical `sigma Y` label alone. -/
theorem cw_matchesYPooledAll_iff_labelMatches
    {Part : Type v} [DecidableEq Part] {depth n : ℕ}
    (sigma : Orientation) (partAt : Fin (n + 1) → Part)
    (profile : Part → ℕ → SplitWord depth → ℕ)
    (address : BlockAddress (fun _c ↦
      PositiveWord (PositiveWord CWBlock (2 ^ depth - 1)) n)) :
    (cwExactInterfaceCompatibilityModel depth n partAt).MatchesYPooledAll
        (logicalAddress sigma address) profile ↔
      CWPooledAllLabelMatches partAt profile (address (sigma .Y)) :=
  Iff.rfl

/-- The analogous literal identification for the physical `sigma Z` label. -/
theorem cw_matchesZPooledAll_iff_labelMatches
    {Part : Type v} [DecidableEq Part] {depth n : ℕ}
    (sigma : Orientation) (partAt : Fin (n + 1) → Part)
    (profile : Part → ℕ → SplitWord depth → ℕ)
    (address : BlockAddress (fun _c ↦
      PositiveWord (PositiveWord CWBlock (2 ^ depth - 1)) n)) :
    (cwExactInterfaceCompatibilityModel depth n partAt).MatchesZPooledAll
        (logicalAddress sigma address) profile ↔
      CWPooledAllLabelMatches partAt profile (address (sigma .Z)) :=
  Iff.rfl

section FirstZeroOut

variable {K : Type u} [CommSemiring K]
variable {Part : Type v} [DecidableEq Part] {depth n : ℕ}
variable {V : ∀ _c,
  PositiveWord (PositiveWord CWBlock (2 ^ depth - 1)) n → Type w}
variable [∀ c a, AddCommMonoid (V c a)] [∀ c a, Module K (V c a)]

/-- Enforce the pooled-all `Y` profile by selecting only matching labels on physical leg
`sigma Y`; the other two legs are untouched. -/
noncomputable def cwPooledYFirstZeroOut
    (P : PartitionedTensor
      (K := K) (A := fun _c ↦
        PositiveWord (PositiveWord CWBlock (2 ^ depth - 1)) n) V)
    (sigma : Orientation) (partAt : Fin (n + 1) → Part)
    (profile : Part → ℕ → SplitWord depth → ℕ) :
    PartitionedTensor
      (K := K) (A := fun _c ↦
        PositiveWord (PositiveWord CWBlock (2 ^ depth - 1)) n) V := by
  classical
  exact P.select fun c label ↦
    c ≠ sigma .Y ∨ CWPooledAllLabelMatches partAt profile label

/-- Enforce the pooled-all `Z` profile on physical leg `sigma Z`. -/
noncomputable def cwPooledZFirstZeroOut
    (P : PartitionedTensor
      (K := K) (A := fun _c ↦
        PositiveWord (PositiveWord CWBlock (2 ^ depth - 1)) n) V)
    (sigma : Orientation) (partAt : Fin (n + 1) → Part)
    (profile : Part → ℕ → SplitWord depth → ℕ) :
    PartitionedTensor
      (K := K) (A := fun _c ↦
        PositiveWord (PositiveWord CWBlock (2 ^ depth - 1)) n) V := by
  classical
  exact P.select fun c label ↦
    c ≠ sigma .Z ∨ CWPooledAllLabelMatches partAt profile label

@[simp] theorem mem_cwPooledYFirstZeroOut_support
    (P : PartitionedTensor
      (K := K) (A := fun _c ↦
        PositiveWord (PositiveWord CWBlock (2 ^ depth - 1)) n) V)
    (sigma : Orientation) (partAt : Fin (n + 1) → Part)
    (profile : Part → ℕ → SplitWord depth → ℕ)
    (address : BlockAddress (fun _c ↦
      PositiveWord (PositiveWord CWBlock (2 ^ depth - 1)) n)) :
    address ∈ (cwPooledYFirstZeroOut P sigma partAt profile).support ↔
      address ∈ P.support ∧
        CWPooledAllLabelMatches partAt profile (address (sigma .Y)) := by
  classical
  rw [cwPooledYFirstZeroOut, PartitionedTensor.mem_select_support]
  constructor
  · rintro ⟨haddress, hkeep⟩
    exact ⟨haddress, by simpa using hkeep (sigma .Y)⟩
  · rintro ⟨haddress, hlabel⟩
    refine ⟨haddress, ?_⟩
    intro c
    by_cases hc : c = sigma .Y
    · subst c
      exact Or.inr hlabel
    · exact Or.inl hc

@[simp] theorem mem_cwPooledZFirstZeroOut_support
    (P : PartitionedTensor
      (K := K) (A := fun _c ↦
        PositiveWord (PositiveWord CWBlock (2 ^ depth - 1)) n) V)
    (sigma : Orientation) (partAt : Fin (n + 1) → Part)
    (profile : Part → ℕ → SplitWord depth → ℕ)
    (address : BlockAddress (fun _c ↦
      PositiveWord (PositiveWord CWBlock (2 ^ depth - 1)) n)) :
    address ∈ (cwPooledZFirstZeroOut P sigma partAt profile).support ↔
      address ∈ P.support ∧
        CWPooledAllLabelMatches partAt profile (address (sigma .Z)) := by
  classical
  rw [cwPooledZFirstZeroOut, PartitionedTensor.mem_select_support]
  constructor
  · rintro ⟨haddress, hkeep⟩
    exact ⟨haddress, by simpa using hkeep (sigma .Z)⟩
  · rintro ⟨haddress, hlabel⟩
    refine ⟨haddress, ?_⟩
    intro c
    by_cases hc : c = sigma .Z
    · subst c
      exact Or.inr hlabel
    · exact Or.inl hc

/-- The paper's pooled-all `Y` first zero-out is an exact variable restriction. -/
theorem cwPooledYFirstZeroOut_restricts
    (P : PartitionedTensor
      (K := K) (A := fun _c ↦
        PositiveWord (PositiveWord CWBlock (2 ^ depth - 1)) n) V)
    (sigma : Orientation) (partAt : Fin (n + 1) → Part)
    (profile : Part → ℕ → SplitWord depth → ℕ) :
    Restricts P.realize (cwPooledYFirstZeroOut P sigma partAt profile).realize := by
  classical
  exact Tensor.Restricts.partitionedSelect P fun c label ↦
    c ≠ sigma .Y ∨ CWPooledAllLabelMatches partAt profile label

/-- The pooled-all `Z` first zero-out is likewise an exact variable restriction. -/
theorem cwPooledZFirstZeroOut_restricts
    (P : PartitionedTensor
      (K := K) (A := fun _c ↦
        PositiveWord (PositiveWord CWBlock (2 ^ depth - 1)) n) V)
    (sigma : Orientation) (partAt : Fin (n + 1) → Part)
    (profile : Part → ℕ → SplitWord depth → ℕ) :
    Restricts P.realize (cwPooledZFirstZeroOut P sigma partAt profile).realize := by
  classical
  exact Tensor.Restricts.partitionedSelect P fun c label ↦
    c ≠ sigma .Z ∨ CWPooledAllLabelMatches partAt profile label

end FirstZeroOut

/-! ## Exact-profile usefulness selection -/

/-- Select the addresses having the prescribed exact complete-split profile on one logical leg. -/
noncomputable def cwExactProfileSupport
    {Part : Type v} [DecidableEq Part] {depth n : ℕ}
    (sigma : Orientation)
    (model : CompatibilityModel
      (fun _c ↦ PositiveWord (PositiveWord CWBlock (2 ^ depth - 1)) n)
      Part depth (n + 1))
    (ambient : Finset (BlockAddress (fun _c ↦
      PositiveWord (PositiveWord CWBlock (2 ^ depth - 1)) n)))
    (logicalLeg : Leg) (profile : CoarseIndex Part → SplitWord depth → ℕ) :
    Finset (BlockAddress (fun _c ↦
      PositiveWord (PositiveWord CWBlock (2 ^ depth - 1)) n)) := by
  classical
  exact ambient.filter fun address ↦
    model.MatchesExact (logicalAddress sigma address) logicalLeg profile

@[simp] theorem mem_cwExactProfileSupport
    {Part : Type v} [DecidableEq Part] {depth n : ℕ}
    (sigma : Orientation)
    (model : CompatibilityModel
      (fun _c ↦ PositiveWord (PositiveWord CWBlock (2 ^ depth - 1)) n)
      Part depth (n + 1))
    (ambient : Finset (BlockAddress (fun _c ↦
      PositiveWord (PositiveWord CWBlock (2 ^ depth - 1)) n)))
    (logicalLeg : Leg) (profile : CoarseIndex Part → SplitWord depth → ℕ)
    (address : BlockAddress (fun _c ↦
      PositiveWord (PositiveWord CWBlock (2 ^ depth - 1)) n)) :
    address ∈ cwExactProfileSupport sigma model ambient logicalLeg profile ↔
      address ∈ ambient ∧
        model.MatchesExact (logicalAddress sigma address) logicalLeg profile := by
  classical
  simp [cwExactProfileSupport]

theorem cwExactProfileSupport_subset
    {Part : Type v} [DecidableEq Part] {depth n : ℕ}
    (sigma : Orientation)
    (model : CompatibilityModel
      (fun _c ↦ PositiveWord (PositiveWord CWBlock (2 ^ depth - 1)) n)
      Part depth (n + 1))
    (ambient : Finset (BlockAddress (fun _c ↦
      PositiveWord (PositiveWord CWBlock (2 ^ depth - 1)) n)))
    (logicalLeg : Leg) (profile : CoarseIndex Part → SplitWord depth → ℕ) :
    cwExactProfileSupport sigma model ambient logicalLeg profile ⊆ ambient := by
  intro address haddress
  exact (mem_cwExactProfileSupport
    sigma model ambient logicalLeg profile address).mp haddress |>.1

/-- Once a physical leg is injective on the ambient support, selecting an arbitrary exact
logical profile on that leg is an exact variable zero-out.  This is the formal usefulness step. -/
theorem cwExactProfileSupport_restricts_of_injective
    {K : Type u} [CommSemiring K]
    {Part : Type v} [DecidableEq Part] {depth n : ℕ}
    {V : ∀ _c,
      PositiveWord (PositiveWord CWBlock (2 ^ depth - 1)) n → Type w}
    [∀ c a, AddCommMonoid (V c a)] [∀ c a, Module K (V c a)]
    (P : PartitionedTensor
      (K := K) (A := fun _c ↦
        PositiveWord (PositiveWord CWBlock (2 ^ depth - 1)) n) V)
    (sigma : Orientation)
    (model : CompatibilityModel
      (fun _c ↦ PositiveWord (PositiveWord CWBlock (2 ^ depth - 1)) n)
      Part depth (n + 1))
    (logicalLeg : Leg) (profile : CoarseIndex Part → SplitWord depth → ℕ)
    (hinjective : Set.InjOn
      (fun address : BlockAddress (fun _c ↦
        PositiveWord (PositiveWord CWBlock (2 ^ depth - 1)) n) ↦
          address (sigma logicalLeg)) P.support) :
    Restricts P.realize
      (P.withSupport
        (cwExactProfileSupport sigma model P.support logicalLeg profile)).realize := by
  apply Tensor.Restricts.partitionedUniqueLegFibers P _ (sigma logicalLeg)
  refine ⟨cwExactProfileSupport_subset sigma model P.support logicalLeg profile, ?_⟩
  intro selected hselected other hother hlabel
  exact hinjective hother
    (cwExactProfileSupport_subset sigma model P.support logicalLeg profile hselected)
    hlabel

end AlgebraicComplexity.Examples
