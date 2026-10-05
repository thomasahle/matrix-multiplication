/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinogradRecursiveHashing
import AlgebraicComplexity.Tensor.GroupedCompatibilityZeroing
import AlgebraicComplexity.Tensor.PartitionedGroupingBoxes

/-!
# Compatibility cleanup inside recursive child-word hashing fibers

The recursive constituent theorem hashes the weights of the two labelled children of each
parent chunk.  Compatibility and usefulness, however, are predicates of the children's full
complete-split words.  Consequently the cleanup must run on the fine parent labels while grouping
them by the labelled-child weight word; quotienting the tensor down to the weight word first would
discard precisely the data used by Claims 6.18--6.21.

This file supplies that semantic adapter.  It proves that

* the labelled-child hash group is readable on a hash-isolated leg;
* the pooled-all first zero-outs are genuine one-leg variable restrictions;
* exact complete-split usefulness is stable under a fine label together with its hash group; and
* the generic compatibility predicates are sound on every selected recursive CW parent term.

The finite competitor estimate, survivor count, sparse-hole bound, and target-box degeneration
remain separate quantitative obligations.  No assembled restriction is accepted as a hypothesis.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor MoreAsymmetryCompatibility

universe u v w

/-! ## Fine fibers over the recursive hash quotient -/

/-- Fine parent addresses lying over a retained recursive child-word family. -/
noncomputable def cwRecursiveFineSupportOverCoarseSupport {depth n : ℕ}
    (fine : Finset (BlockAddress (fun _c ↦
      PositiveWord (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n)))
    (coarse : Finset (CWRecursiveCoarseAddress depth n)) :
    Finset (BlockAddress (fun _c ↦
      PositiveWord (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n)) := by
  classical
  exact fine.filter fun address ↦ cwRecursiveChildGroup depth n address ∈ coarse

@[simp] theorem mem_cwRecursiveFineSupportOverCoarseSupport {depth n : ℕ}
    (fine : Finset (BlockAddress (fun _c ↦
      PositiveWord (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n)))
    (coarse : Finset (CWRecursiveCoarseAddress depth n))
    (address : BlockAddress (fun _c ↦
      PositiveWord (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n)) :
    address ∈ cwRecursiveFineSupportOverCoarseSupport fine coarse ↔
      address ∈ fine ∧ cwRecursiveChildGroup depth n address ∈ coarse := by
  classical
  simp [cwRecursiveFineSupportOverCoarseSupport]

/-- Hash isolation of recursive coarse addresses makes the hash group readable from the
corresponding fine parent label. -/
theorem cwRecursiveFineSupportOverCoarseSupport_hasGroupUniqueLegFibers
    {depth n : ℕ}
    (fine : Finset (BlockAddress (fun _c ↦
      PositiveWord (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n)))
    (coarse : Finset (CWRecursiveCoarseAddress depth n)) (pivot : Leg)
    (hinjective : Set.InjOn
      (fun address : CWRecursiveCoarseAddress depth n ↦ address pivot) coarse) :
    HasGroupUniqueLegFibers
      (cwRecursiveFineSupportOverCoarseSupport fine coarse)
      (cwRecursiveFineSupportOverCoarseSupport fine coarse)
      (cwRecursiveChildGroup depth n) pivot := by
  refine ⟨Finset.Subset.rfl, ?_⟩
  intro selected hselected other hother hlabel
  have hselectedCoarse :=
    (mem_cwRecursiveFineSupportOverCoarseSupport fine coarse selected).mp hselected |>.2
  have hotherCoarse :=
    (mem_cwRecursiveFineSupportOverCoarseSupport fine coarse other).mp hother |>.2
  apply hinjective hotherCoarse hselectedCoarse
  change cwRecursiveLabelledChildWord depth n (other pivot) =
    cwRecursiveLabelledChildWord depth n (selected pivot)
  rw [hlabel]

/-! ## The compatibility model sees exactly the recursive hash group -/

/-- The model's logical coarse coordinate is the corresponding physical recursive hash digit. -/
theorem cwRecursiveChildCompatibilityModel_coarse_get_eq_group
    {Part : Type v} {depth n : ℕ} (partAt : Fin (n + 1) → Part)
    (sigma : Orientation)
    (address : BlockAddress (fun _c ↦
      PositiveWord (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n))
    (occurrence : Fin ((n + 1) + (n + 1))) (logicalLeg : Leg) :
    ((cwRecursiveChildCompatibilityModel depth n partAt).coarse
        (logicalAddress sigma address) occurrence).get logicalLeg =
      ((cwRecursiveChildGroup depth n address (sigma logicalLeg) occurrence :
        CWRecursiveChildDigit depth) : ℕ) := by
  have hword := congrArg Fin.val <| congrFun
    (cwRecursiveLabelledChildWord_eq_model_get
      depth n partAt (logicalAddress sigma address) logicalLeg) occurrence
  simpa only [cwRecursiveChildGroup_apply, logicalAddress_apply] using hword.symm

/-- The recursive child model records the exact weights of its exposed complete-split chunks. -/
theorem cwRecursiveChildCompatibilityModel_hasCoarseWeights
    {Part : Type v} (depth n : ℕ) (partAt : Fin (n + 1) → Part)
    (address : BlockAddress (fun _c ↦
      PositiveWord (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n)) :
    (cwRecursiveChildCompatibilityModel depth n partAt).HasCoarseWeights address :=
  recursiveChildCompatibilityModel_hasCoarseWeights
    (fun _c ↦ cwChunkSplitWord (depth + 1)) partAt address

private theorem recursiveCoarseIndex_eq_of_part_eq_of_get_eq {Part : Type v}
    {left right : CoarseIndex Part} (hpart : left.part = right.part)
    (hget : ∀ c, left.get c = right.get c) : left = right := by
  cases left with
  | mk leftPart leftX leftY leftZ =>
      cases right with
      | mk rightPart rightX rightY rightZ =>
          have hx := hget .X
          have hy := hget .Y
          have hz := hget .Z
          simp only [CoarseIndex.get] at hx hy hz
          simp_all

/-- Exact complete-split usefulness depends only on one fine parent label and its recursive hash
group.  It can therefore be imposed by an honest variable zero-out once that group is readable. -/
theorem cwRecursiveMatchesExact_isGroupLabelStable
    {Part : Type v} [DecidableEq Part] {depth n : ℕ}
    (partAt : Fin (n + 1) → Part) (sigma : Orientation)
    (ambient : Finset (BlockAddress (fun _c ↦
      PositiveWord (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n)))
    (logicalLeg : Leg) (profile : CoarseIndex Part → SplitWord depth → ℕ) :
    IsGroupLabelStable ambient (cwRecursiveChildGroup depth n)
      (sigma logicalLeg)
      (fun address ↦
        (cwRecursiveChildCompatibilityModel depth n partAt).MatchesExact
          (logicalAddress sigma address) logicalLeg profile) := by
  intro left _hleft right _hright hlabel hgroup
  let model := cwRecursiveChildCompatibilityModel depth n partAt
  have hcoarse : model.coarse (logicalAddress sigma left) =
      model.coarse (logicalAddress sigma right) := by
    funext occurrence
    apply recursiveCoarseIndex_eq_of_part_eq_of_get_eq
    · rfl
    · intro c
      change
        ((cwRecursiveChildCompatibilityModel depth n partAt).coarse
          (logicalAddress sigma left) occurrence).get c =
        ((cwRecursiveChildCompatibilityModel depth n partAt).coarse
          (logicalAddress sigma right) occurrence).get c
      rw [cwRecursiveChildCompatibilityModel_coarse_get_eq_group,
        cwRecursiveChildCompatibilityModel_coarse_get_eq_group]
      exact congrArg
        (fun grouped : CWRecursiveCoarseAddress depth n ↦
          ((grouped (sigma c) occurrence : CWRecursiveChildDigit depth) : ℕ))
        hgroup
  have hchunks : model.chunks logicalLeg
      (logicalAddress sigma left logicalLeg) =
      model.chunks logicalLeg (logicalAddress sigma right logicalLeg) := by
    funext occurrence
    change positiveWordLabelledChildren (cwChunkSplitWord (depth + 1))
        (left (sigma logicalLeg)) occurrence =
      positiveWordLabelledChildren (cwChunkSplitWord (depth + 1))
        (right (sigma logicalLeg)) occurrence
    rw [hlabel]
  unfold CompatibilityModel.MatchesExact
  constructor <;> intro h q word
  · rw [← hcoarse, ← hchunks]
    exact h q word
  · rw [hcoarse, hchunks]
    exact h q word

/-! ## Pooled-all first zero-outs on labelled children -/

/-- The pooled-all profile of a recursive child sequence is a predicate of its parent label
alone.  Both labelled halves carry the part tag of their common parent occurrence. -/
def CWRecursivePooledAllLabelMatches
    {Part : Type v} [DecidableEq Part] {depth n : ℕ}
    (partAt : Fin (n + 1) → Part)
    (profile : Part → ℕ → SplitWord depth → ℕ)
    (label : PositiveWord (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n) : Prop :=
  ∀ part coordinate word,
    cellMultiplicity
      (fun occurrence ↦
        (labelledChildParts partAt occurrence,
          splitWordWeight
            (positiveWordLabelledChildren (cwChunkSplitWord (depth + 1))
              label occurrence)))
      (positiveWordLabelledChildren (cwChunkSplitWord (depth + 1)) label)
      (part, coordinate) word = profile part coordinate word

/-- Semantic pooled-`Y` matching is definitionally the parent-label predicate on physical
`sigma Y`. -/
theorem cwRecursive_matchesYPooledAll_iff_labelMatches
    {Part : Type v} [DecidableEq Part] {depth n : ℕ}
    (sigma : Orientation) (partAt : Fin (n + 1) → Part)
    (profile : Part → ℕ → SplitWord depth → ℕ)
    (address : BlockAddress (fun _c ↦
      PositiveWord (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n)) :
    (cwRecursiveChildCompatibilityModel depth n partAt).MatchesYPooledAll
        (logicalAddress sigma address) profile ↔
      CWRecursivePooledAllLabelMatches partAt profile (address (sigma .Y)) :=
  Iff.rfl

/-- Logical-`Z` analogue of `cwRecursive_matchesYPooledAll_iff_labelMatches`. -/
theorem cwRecursive_matchesZPooledAll_iff_labelMatches
    {Part : Type v} [DecidableEq Part] {depth n : ℕ}
    (sigma : Orientation) (partAt : Fin (n + 1) → Part)
    (profile : Part → ℕ → SplitWord depth → ℕ)
    (address : BlockAddress (fun _c ↦
      PositiveWord (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n)) :
    (cwRecursiveChildCompatibilityModel depth n partAt).MatchesZPooledAll
        (logicalAddress sigma address) profile ↔
      CWRecursivePooledAllLabelMatches partAt profile (address (sigma .Z)) :=
  Iff.rfl

section FirstZeroOut

variable {K : Type u} [CommSemiring K]
variable {Part : Type v} [DecidableEq Part] {depth n : ℕ}
variable {V : ∀ _c,
  PositiveWord (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n → Type w}
variable [∀ c a, AddCommMonoid (V c a)] [∀ c a, Module K (V c a)]

/-- Enforce the recursive pooled-all `Y` profile on physical leg `sigma Y`. -/
noncomputable def cwRecursivePooledYFirstZeroOut
    (P : PartitionedTensor
      (K := K) (A := fun _c ↦
        PositiveWord (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n) V)
    (sigma : Orientation) (partAt : Fin (n + 1) → Part)
    (profile : Part → ℕ → SplitWord depth → ℕ) := by
  classical
  exact P.select fun c label ↦
    c ≠ sigma .Y ∨ CWRecursivePooledAllLabelMatches partAt profile label

/-- Enforce the recursive pooled-all `Z` profile on physical leg `sigma Z`. -/
noncomputable def cwRecursivePooledZFirstZeroOut
    (P : PartitionedTensor
      (K := K) (A := fun _c ↦
        PositiveWord (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n) V)
    (sigma : Orientation) (partAt : Fin (n + 1) → Part)
    (profile : Part → ℕ → SplitWord depth → ℕ) := by
  classical
  exact P.select fun c label ↦
    c ≠ sigma .Z ∨ CWRecursivePooledAllLabelMatches partAt profile label

@[simp] theorem mem_cwRecursivePooledYFirstZeroOut_support
    (P : PartitionedTensor
      (K := K) (A := fun _c ↦
        PositiveWord (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n) V)
    (sigma : Orientation) (partAt : Fin (n + 1) → Part)
    (profile : Part → ℕ → SplitWord depth → ℕ)
    (address : BlockAddress (fun _c ↦
      PositiveWord (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n)) :
    address ∈ (cwRecursivePooledYFirstZeroOut P sigma partAt profile).support ↔
      address ∈ P.support ∧
        CWRecursivePooledAllLabelMatches partAt profile (address (sigma .Y)) := by
  classical
  rw [cwRecursivePooledYFirstZeroOut, PartitionedTensor.mem_select_support]
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

@[simp] theorem mem_cwRecursivePooledZFirstZeroOut_support
    (P : PartitionedTensor
      (K := K) (A := fun _c ↦
        PositiveWord (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n) V)
    (sigma : Orientation) (partAt : Fin (n + 1) → Part)
    (profile : Part → ℕ → SplitWord depth → ℕ)
    (address : BlockAddress (fun _c ↦
      PositiveWord (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n)) :
    address ∈ (cwRecursivePooledZFirstZeroOut P sigma partAt profile).support ↔
      address ∈ P.support ∧
        CWRecursivePooledAllLabelMatches partAt profile (address (sigma .Z)) := by
  classical
  rw [cwRecursivePooledZFirstZeroOut, PartitionedTensor.mem_select_support]
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

/-- The recursive pooled-all `Y` first zero-out is an exact variable restriction. -/
theorem cwRecursivePooledYFirstZeroOut_restricts
    (P : PartitionedTensor
      (K := K) (A := fun _c ↦
        PositiveWord (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n) V)
    (sigma : Orientation) (partAt : Fin (n + 1) → Part)
    (profile : Part → ℕ → SplitWord depth → ℕ) :
    Restricts P.realize
      (cwRecursivePooledYFirstZeroOut P sigma partAt profile).realize := by
  classical
  exact Tensor.Restricts.partitionedSelect P fun c label ↦
    c ≠ sigma .Y ∨ CWRecursivePooledAllLabelMatches partAt profile label

/-- The recursive pooled-all `Z` first zero-out is an exact variable restriction. -/
theorem cwRecursivePooledZFirstZeroOut_restricts
    (P : PartitionedTensor
      (K := K) (A := fun _c ↦
        PositiveWord (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n) V)
    (sigma : Orientation) (partAt : Fin (n + 1) → Part)
    (profile : Part → ℕ → SplitWord depth → ℕ) :
    Restricts P.realize
      (cwRecursivePooledZFirstZeroOut P sigma partAt profile).realize := by
  classical
  exact Tensor.Restricts.partitionedSelect P fun c label ↦
    c ≠ sigma .Z ∨ CWRecursivePooledAllLabelMatches partAt profile label

end FirstZeroOut

/-! ## Concrete soundness on selected recursive parent terms -/

/-- Exact and pooled profile equations present before recursive logical-`Y` compatibility
isolation. -/
def CWRecursivePooledAllYProfileMatches
    {Part : Type v} [DecidableEq Part] {depth n : ℕ}
    (sigma : Orientation) (partAt : Fin (n + 1) → Part)
    (targets : CompatibilityTargets Part depth) (pooled : PooledAllTargets targets)
    (address : BlockAddress (fun _c ↦
      PositiveWord (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n)) : Prop :=
  let model := cwRecursiveChildCompatibilityModel depth n partAt
  let logical := logicalAddress sigma address
  model.MatchesExact logical .X targets.xExact ∧
    model.MatchesYPooledAll logical pooled.yAll

/-- Exact and pooled profile equations present before recursive logical-`Z` compatibility
isolation. -/
def CWRecursivePooledAllZProfileMatches
    {Part : Type v} [DecidableEq Part] {depth n : ℕ}
    (sigma : Orientation) (partAt : Fin (n + 1) → Part)
    (targets : CompatibilityTargets Part depth) (pooled : PooledAllTargets targets)
    (address : BlockAddress (fun _c ↦
      PositiveWord (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n)) : Prop :=
  let model := cwRecursiveChildCompatibilityModel depth n partAt
  let logical := logicalAddress sigma address
  model.MatchesExact logical .X targets.xExact ∧
    model.MatchesExact logical .Y targets.yExact ∧
    model.MatchesZPooledAll logical pooled.zAll

/-- The recursive selected-parent semantics turn the `Y` profile equations into the complete
pooled-all invariant consumed by generic compatibility soundness. -/
theorem cwRecursiveChildCompatibilityModel_passesYPooledAllZeroOut
    (K : Type u) [CommRing K] (q : ℕ)
    {Part : Type v} [DecidableEq Part] {depth n : ℕ}
    (partAt : Fin (n + 1) → Part)
    (term : ExactInterfaceTermParameters (depth + 1))
    (hmultiplicity : term.multiplicity = n + 1)
    (sigma : Orientation) (targets : CompatibilityTargets Part depth)
    (pooled : PooledAllTargets targets)
    (address : BlockAddress (fun _c ↦
      PositiveWord (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n))
    (haddress : address ∈
      (cwSelectedExactInterfaceTerm K q term hmultiplicity).support)
    (hprofiles : CWRecursivePooledAllYProfileMatches
      sigma partAt targets pooled address) :
    (cwRecursiveChildCompatibilityModel depth n partAt).PassesYPooledAllZeroOut
      targets pooled (logicalAddress sigma address) := by
  rcases hprofiles with ⟨hX, hYAll⟩
  exact
    ⟨cwRecursiveChildCompatibilityModel_isFineLegal_logicalAddress_of_mem_selected_support
        K q partAt term hmultiplicity sigma address haddress,
      cwRecursiveChildCompatibilityModel_hasCoarseWeights
        depth n partAt (logicalAddress sigma address), hX, hYAll⟩

/-- Logical-`Z` analogue of
`cwRecursiveChildCompatibilityModel_passesYPooledAllZeroOut`. -/
theorem cwRecursiveChildCompatibilityModel_passesZPooledAllZeroOut
    (K : Type u) [CommRing K] (q : ℕ)
    {Part : Type v} [DecidableEq Part] {depth n : ℕ}
    (partAt : Fin (n + 1) → Part)
    (term : ExactInterfaceTermParameters (depth + 1))
    (hmultiplicity : term.multiplicity = n + 1)
    (sigma : Orientation) (targets : CompatibilityTargets Part depth)
    (pooled : PooledAllTargets targets)
    (address : BlockAddress (fun _c ↦
      PositiveWord (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n))
    (haddress : address ∈
      (cwSelectedExactInterfaceTerm K q term hmultiplicity).support)
    (hprofiles : CWRecursivePooledAllZProfileMatches
      sigma partAt targets pooled address) :
    (cwRecursiveChildCompatibilityModel depth n partAt).PassesZPooledAllZeroOut
      targets pooled (logicalAddress sigma address) := by
  rcases hprofiles with ⟨hX, hY, hZAll⟩
  exact
    ⟨cwRecursiveChildCompatibilityModel_isFineLegal_logicalAddress_of_mem_selected_support
        K q partAt term hmultiplicity sigma address haddress,
      cwRecursiveChildCompatibilityModel_hasCoarseWeights
        depth n partAt (logicalAddress sigma address), hX, hY, hZAll⟩

/-- Recursive arbitrary-orientation form of the paper's `Y` compatibility-soundness claim. -/
theorem cwRecursiveSelectedTerm_orientedYCompatibility_sound
    (K : Type u) [CommRing K] (q : ℕ)
    {Part : Type v} [DecidableEq Part] {depth n : ℕ}
    (partAt : Fin (n + 1) → Part)
    (term : ExactInterfaceTermParameters (depth + 1))
    (hmultiplicity : term.multiplicity = n + 1)
    (sigma : Orientation) (targets : CompatibilityTargets Part depth)
    (pooled : PooledAllTargets targets)
    (ambient : Finset (BlockAddress (fun _c ↦
      PositiveWord (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n)))
    (hambient : ambient ⊆
      (cwSelectedExactInterfaceTerm K q term hmultiplicity).support)
    (hprofiles : ∀ address ∈ ambient,
      CWRecursivePooledAllYProfileMatches sigma partAt targets pooled address) :
    IsCompatibilitySound ambient (sigma .Y)
      (OrientedCompatibleY
        (A := fun _c ↦
          PositiveWord (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n)
        sigma (cwRecursiveChildCompatibilityModel depth n partAt) targets) := by
  apply CompatibilityModel.orientedYCompatibility_sound
    (A := fun _c ↦
      PositiveWord (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n)
    sigma (cwRecursiveChildCompatibilityModel depth n partAt) targets
  intro address haddress
  apply CompatibilityModel.passesYFirstZeroOut_of_pooledAll
  exact cwRecursiveChildCompatibilityModel_passesYPooledAllZeroOut
    K q partAt term hmultiplicity sigma targets pooled address
      (hambient haddress) (hprofiles address haddress)

/-- Recursive arbitrary-orientation form of the paper's later `Z` compatibility-soundness
claim. -/
theorem cwRecursiveSelectedTerm_orientedZCompatibility_sound
    (K : Type u) [CommRing K] (q : ℕ)
    {Part : Type v} [DecidableEq Part] {depth n : ℕ}
    (partAt : Fin (n + 1) → Part)
    (term : ExactInterfaceTermParameters (depth + 1))
    (hmultiplicity : term.multiplicity = n + 1)
    (sigma : Orientation) (targets : CompatibilityTargets Part depth)
    (pooled : PooledAllTargets targets)
    (ambient : Finset (BlockAddress (fun _c ↦
      PositiveWord (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n)))
    (hambient : ambient ⊆
      (cwSelectedExactInterfaceTerm K q term hmultiplicity).support)
    (hprofiles : ∀ address ∈ ambient,
      CWRecursivePooledAllZProfileMatches sigma partAt targets pooled address) :
    IsCompatibilitySound ambient (sigma .Z)
      (OrientedCompatibleZ
        (A := fun _c ↦
          PositiveWord (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n)
        sigma (cwRecursiveChildCompatibilityModel depth n partAt) targets) := by
  apply CompatibilityModel.orientedZCompatibility_sound
    (A := fun _c ↦
      PositiveWord (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n)
    sigma (cwRecursiveChildCompatibilityModel depth n partAt) targets
  intro address haddress
  apply CompatibilityModel.passesZFirstZeroOut_of_pooledAll
  exact cwRecursiveChildCompatibilityModel_passesZPooledAllZeroOut
    K q partAt term hmultiplicity sigma targets pooled address
      (hambient haddress) (hprofiles address haddress)

/-! ## Complete grouped recursive cleanup -/

/-- Explicit final support of the recursive exact/compatibility/usefulness cleanup. -/
noncomputable def cwRecursiveOrientedGroupedCleanupFinalSupport
    (K : Type u) [CommRing K] (q : ℕ)
    {Part : Type v} [DecidableEq Part] {depth n : ℕ}
    (partAt : Fin (n + 1) → Part)
    (term : ExactInterfaceTermParameters (depth + 1))
    (hmultiplicity : term.multiplicity = n + 1)
    (sigma : Orientation)
    (alpha : ExactRecursiveSplitType
      (cwRecursiveLogicalParent term sigma) (coarseTotal depth) (n + 1))
    (targets : CompatibilityTargets Part depth)
    (pooled : PooledAllTargets targets)
    (coarseKept : Finset (CWRecursiveCoarseAddress depth n)) :=
  let alphaSelected := cwRecursiveAlphaMarginalSelectedTerm
    K q term hmultiplicity sigma alpha
  let group := cwRecursiveChildGroup depth n
  let fineAmbient := cwRecursiveFineSupportOverCoarseSupport
    alphaSelected.support coarseKept
  let hashed := alphaSelected.withSupport fineAmbient
  let model := cwRecursiveChildCompatibilityModel depth n partAt
  let xSupport := groupStableSupport hashed.support (fun address ↦
    model.MatchesExact (logicalAddress sigma address) .X targets.xExact)
  let xUseful := hashed.withSupport xSupport
  let yFirst := cwRecursivePooledYFirstZeroOut xUseful sigma partAt pooled.yAll
  let compatibleY := OrientedCompatibleY
    (A := fun _c ↦
      PositiveWord (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n)
    sigma model targets
  let ySupport := groupCompatibilityIsolatedSupport
    yFirst.support group (sigma .Y) compatibleY
  let yIsolated := yFirst.withSupport ySupport
  let yUsefulSupport := groupStableSupport yIsolated.support (fun address ↦
    model.MatchesExact (logicalAddress sigma address) .Y targets.yExact)
  let yUseful := yIsolated.withSupport yUsefulSupport
  let zFirst := cwRecursivePooledZFirstZeroOut yUseful sigma partAt pooled.zAll
  let compatibleZ := OrientedCompatibleZ
    (A := fun _c ↦
      PositiveWord (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n)
    sigma model targets
  let zSupport := groupCompatibilityIsolatedSupport
    zFirst.support group (sigma .Z) compatibleZ
  let zIsolated := zFirst.withSupport zSupport
  groupStableSupport zIsolated.support (fun address ↦
    model.MatchesExact (logicalAddress sigma address) .Z targets.zExact)

/-- Every address of the explicitly cleaned support realizes all three exact target tables. -/
theorem mem_cwRecursiveOrientedGroupedCleanupFinalSupport_matchesExact
    (K : Type u) [CommRing K] (q : ℕ)
    {Part : Type v} [DecidableEq Part] {depth n : ℕ}
    (partAt : Fin (n + 1) → Part)
    (term : ExactInterfaceTermParameters (depth + 1))
    (hmultiplicity : term.multiplicity = n + 1)
    (sigma : Orientation)
    (alpha : ExactRecursiveSplitType
      (cwRecursiveLogicalParent term sigma) (coarseTotal depth) (n + 1))
    (targets : CompatibilityTargets Part depth)
    (pooled : PooledAllTargets targets)
    (coarseKept : Finset (CWRecursiveCoarseAddress depth n))
    (address : BlockAddress (fun _c ↦
      PositiveWord (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n))
    (haddress : address ∈ cwRecursiveOrientedGroupedCleanupFinalSupport
      K q partAt term hmultiplicity sigma alpha targets pooled coarseKept)
    (logicalLeg : Leg) :
    (cwRecursiveChildCompatibilityModel depth n partAt).MatchesExact
      (logicalAddress sigma address) logicalLeg
      (match logicalLeg with
        | .X => targets.xExact
        | .Y => targets.yExact
        | .Z => targets.zExact) := by
  classical
  let alphaSelected := cwRecursiveAlphaMarginalSelectedTerm
    K q term hmultiplicity sigma alpha
  let group := cwRecursiveChildGroup depth n
  let fineAmbient := cwRecursiveFineSupportOverCoarseSupport
    alphaSelected.support coarseKept
  let hashed := alphaSelected.withSupport fineAmbient
  let model := cwRecursiveChildCompatibilityModel depth n partAt
  let xKeep := fun candidate : BlockAddress (fun _c ↦
      PositiveWord (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n) ↦
    model.MatchesExact (logicalAddress sigma candidate) .X targets.xExact
  let xSupport := groupStableSupport hashed.support xKeep
  let xUseful := hashed.withSupport xSupport
  let yFirst := cwRecursivePooledYFirstZeroOut xUseful sigma partAt pooled.yAll
  let compatibleY := OrientedCompatibleY
    (A := fun _c ↦
      PositiveWord (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n)
    sigma model targets
  let ySupport := groupCompatibilityIsolatedSupport
    yFirst.support group (sigma .Y) compatibleY
  let yIsolated := yFirst.withSupport ySupport
  let yKeep := fun candidate : BlockAddress (fun _c ↦
      PositiveWord (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n) ↦
    model.MatchesExact (logicalAddress sigma candidate) .Y targets.yExact
  let yUsefulSupport := groupStableSupport yIsolated.support yKeep
  let yUseful := yIsolated.withSupport yUsefulSupport
  let zFirst := cwRecursivePooledZFirstZeroOut yUseful sigma partAt pooled.zAll
  let compatibleZ := OrientedCompatibleZ
    (A := fun _c ↦
      PositiveWord (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n)
    sigma model targets
  let zSupport := groupCompatibilityIsolatedSupport
    zFirst.support group (sigma .Z) compatibleZ
  let zIsolated := zFirst.withSupport zSupport
  let zKeep := fun candidate : BlockAddress (fun _c ↦
      PositiveWord (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n) ↦
    model.MatchesExact (logicalAddress sigma candidate) .Z targets.zExact
  let zUsefulSupport := groupStableSupport zIsolated.support zKeep
  change address ∈ zUsefulSupport at haddress
  have hzData : address ∈ zSupport ∧ zKeep address := by
    simpa [zUsefulSupport, zIsolated, groupStableSupport] using haddress
  have hzFirstMem : address ∈ zFirst.support :=
    groupCompatibilityIsolatedSupport_subset
      zFirst.support group (sigma .Z) compatibleZ hzData.1
  have hyUsefulMem : address ∈ yUsefulSupport := by
    exact (mem_cwRecursivePooledZFirstZeroOut_support
      yUseful sigma partAt pooled.zAll address).mp hzFirstMem |>.1
  have hyData : address ∈ ySupport ∧ yKeep address := by
    simpa [yUsefulSupport, yIsolated, groupStableSupport] using hyUsefulMem
  have hyFirstMem : address ∈ yFirst.support :=
    groupCompatibilityIsolatedSupport_subset
      yFirst.support group (sigma .Y) compatibleY hyData.1
  have hxMem : address ∈ xSupport := by
    exact (mem_cwRecursivePooledYFirstZeroOut_support
      xUseful sigma partAt pooled.yAll address).mp hyFirstMem |>.1
  have hxData : address ∈ hashed.support ∧ xKeep address := by
    simpa [xSupport, groupStableSupport] using hxMem
  cases logicalLeg with
  | X => simpa [model, xKeep] using hxData.2
  | Y => simpa [model, yKeep] using hyData.2
  | Z => simpa [model, zKeep] using hzData.2

/-- Paper-faithful compatibility and usefulness cleanup inside an already hash-retained recursive
child-word family.

The source of this theorem is the entire fine preimage of `coarseKept` inside the exact marginal
type.  The construction itself performs the exact-`X`, pooled-`Y`, compatible-`Y`, exact-`Y`,
pooled-`Z`, compatible-`Z`, and exact-`Z` zero-outs.  It returns the whole surviving fine fiber of
every coarse group, together with projection closure of the final support relative to the hashed
fine preimage.  In particular, neither an assembled degeneration nor a selected target box is a
hypothesis. -/
theorem cwRecursiveSelectedTerm_orientedGroupedCleanup_withCoarseGroup
    (K : Type u) [CommRing K] (q : ℕ)
    {Part : Type v} [DecidableEq Part] {depth n : ℕ}
    (partAt : Fin (n + 1) → Part)
    (term : ExactInterfaceTermParameters (depth + 1))
    (hmultiplicity : term.multiplicity = n + 1)
    (sigma : Orientation)
    (alpha : ExactRecursiveSplitType
      (cwRecursiveLogicalParent term sigma) (coarseTotal depth) (n + 1))
    (targets : CompatibilityTargets Part depth)
    (pooled : PooledAllTargets targets)
    (coarseKept : Finset (CWRecursiveCoarseAddress depth n))
    (hcoarseX : Set.InjOn
      (fun address : CWRecursiveCoarseAddress depth n ↦ address (sigma .X)) coarseKept) :
    let alphaSelected := cwRecursiveAlphaMarginalSelectedTerm
      K q term hmultiplicity sigma alpha
    let group := cwRecursiveChildGroup depth n
    let fineAmbient := cwRecursiveFineSupportOverCoarseSupport
      alphaSelected.support coarseKept
    let hashed := alphaSelected.withSupport fineAmbient
    let model := cwRecursiveChildCompatibilityModel depth n partAt
    let xSupport := groupStableSupport hashed.support (fun address ↦
      model.MatchesExact (logicalAddress sigma address) .X targets.xExact)
    let xUseful := hashed.withSupport xSupport
    let yFirst := cwRecursivePooledYFirstZeroOut xUseful sigma partAt pooled.yAll
    let compatibleY := OrientedCompatibleY
      (A := fun _c ↦
        PositiveWord (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n)
      sigma model targets
    let ySupport := groupCompatibilityIsolatedSupport
      yFirst.support group (sigma .Y) compatibleY
    let yIsolated := yFirst.withSupport ySupport
    let yUsefulSupport := groupStableSupport yIsolated.support (fun address ↦
      model.MatchesExact (logicalAddress sigma address) .Y targets.yExact)
    let yUseful := yIsolated.withSupport yUsefulSupport
    let zFirst := cwRecursivePooledZFirstZeroOut yUseful sigma partAt pooled.zAll
    let compatibleZ := OrientedCompatibleZ
      (A := fun _c ↦
        PositiveWord (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n)
      sigma model targets
    let zSupport := groupCompatibilityIsolatedSupport
      zFirst.support group (sigma .Z) compatibleZ
    let zIsolated := zFirst.withSupport zSupport
    let zUsefulSupport := groupStableSupport zIsolated.support (fun address ↦
      model.MatchesExact (logicalAddress sigma address) .Z targets.zExact)
    let zUseful := zIsolated.withSupport zUsefulSupport
    ∃ G : zUseful.LegGrouping (CWRecursiveCoarseAddress depth n),
      (∀ address, G.group address = cwRecursiveChildGroup depth n address) ∧
        IsProjectionClosed hashed.support zUsefulSupport Finset.univ ∧
          Restricts hashed.realize
            (Tensor.indexedDirectSum (fun coarse ↦ (G.fiber coarse).realize)) := by
  classical
  let selected := cwSelectedExactInterfaceTerm K q term hmultiplicity
  let alphaSelected := cwRecursiveAlphaMarginalSelectedTerm
    K q term hmultiplicity sigma alpha
  let group := cwRecursiveChildGroup depth n
  let fineAmbient := cwRecursiveFineSupportOverCoarseSupport
    alphaSelected.support coarseKept
  let hashed := alphaSelected.withSupport fineAmbient
  let model := cwRecursiveChildCompatibilityModel depth n partAt
  let xKeep := fun address : BlockAddress (fun _c ↦
      PositiveWord (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n) ↦
    model.MatchesExact (logicalAddress sigma address) .X targets.xExact
  let xSupport := groupStableSupport hashed.support xKeep
  let xUseful := hashed.withSupport xSupport
  let yFirst := cwRecursivePooledYFirstZeroOut xUseful sigma partAt pooled.yAll
  let compatibleY := OrientedCompatibleY
    (A := fun _c ↦
      PositiveWord (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n)
    sigma model targets
  let ySupport := groupCompatibilityIsolatedSupport
    yFirst.support group (sigma .Y) compatibleY
  let yIsolated := yFirst.withSupport ySupport
  let yKeep := fun address : BlockAddress (fun _c ↦
      PositiveWord (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n) ↦
    model.MatchesExact (logicalAddress sigma address) .Y targets.yExact
  let yUsefulSupport := groupStableSupport yIsolated.support yKeep
  let yUseful := yIsolated.withSupport yUsefulSupport
  let zFirst := cwRecursivePooledZFirstZeroOut yUseful sigma partAt pooled.zAll
  let compatibleZ := OrientedCompatibleZ
    (A := fun _c ↦
      PositiveWord (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n)
    sigma model targets
  let zSupport := groupCompatibilityIsolatedSupport
    zFirst.support group (sigma .Z) compatibleZ
  let zIsolated := zFirst.withSupport zSupport
  let zKeep := fun address : BlockAddress (fun _c ↦
      PositiveWord (PositiveWord CWBlock (2 ^ (depth + 1) - 1)) n) ↦
    model.MatchesExact (logicalAddress sigma address) .Z targets.zExact
  let zUsefulSupport := groupStableSupport zIsolated.support zKeep
  let zUseful := zIsolated.withSupport zUsefulSupport

  have hXHashed : HasGroupUniqueLegFibers hashed.support hashed.support
      group (sigma .X) := by
    simpa [hashed, fineAmbient, group] using
      cwRecursiveFineSupportOverCoarseSupport_hasGroupUniqueLegFibers
        alphaSelected.support coarseKept (sigma .X) hcoarseX
  have hxSubset : xSupport ⊆ hashed.support :=
    groupStableSupport_subset hashed.support xKeep
  have hXYFirstSubset : yFirst.support ⊆ xSupport := by
    intro address haddress
    exact (mem_cwRecursivePooledYFirstZeroOut_support
      xUseful sigma partAt pooled.yAll address).mp haddress |>.1
  have hYSubset : ySupport ⊆ yFirst.support :=
    groupCompatibilityIsolatedSupport_subset
      yFirst.support group (sigma .Y) compatibleY
  have hYUsefulSubset : yUsefulSupport ⊆ ySupport := by
    change groupStableSupport ySupport yKeep ⊆ ySupport
    exact groupStableSupport_subset ySupport yKeep
  have hZFirstSubset : zFirst.support ⊆ yUsefulSupport := by
    intro address haddress
    exact (mem_cwRecursivePooledZFirstZeroOut_support
      yUseful sigma partAt pooled.zAll address).mp haddress |>.1
  have hZSubset : zSupport ⊆ zFirst.support :=
    groupCompatibilityIsolatedSupport_subset
      zFirst.support group (sigma .Z) compatibleZ
  have hZUsefulSubset : zUsefulSupport ⊆ zSupport := by
    change groupStableSupport zSupport zKeep ⊆ zSupport
    exact groupStableSupport_subset zSupport zKeep

  have hAlphaSelectedSubsetSelected : alphaSelected.support ⊆ selected.support := by
    intro address haddress
    exact (mem_cwRecursiveAlphaMarginalSelectedTerm_support
      K q term hmultiplicity sigma alpha address).mp haddress |>.1
  have hYFirstSubsetSelected : yFirst.support ⊆ selected.support := by
    intro address haddress
    have hx := hXYFirstSubset haddress
    have hhash := hxSubset hx
    have halpha :=
      (mem_cwRecursiveFineSupportOverCoarseSupport
        alphaSelected.support coarseKept address).mp hhash |>.1
    exact hAlphaSelectedSubsetSelected halpha
  have hYProfiles : ∀ address ∈ yFirst.support,
      CWRecursivePooledAllYProfileMatches sigma partAt targets pooled address := by
    intro address haddress
    have hfirst := (mem_cwRecursivePooledYFirstZeroOut_support
      xUseful sigma partAt pooled.yAll address).mp haddress
    have hxData : address ∈ hashed.support ∧ xKeep address := by
      simpa [xUseful, xSupport, groupStableSupport] using hfirst.1
    refine ⟨hxData.2, ?_⟩
    exact (cwRecursive_matchesYPooledAll_iff_labelMatches
      sigma partAt pooled.yAll address).mpr hfirst.2
  have hSoundY : IsCompatibilitySound yFirst.support (sigma .Y) compatibleY := by
    exact cwRecursiveSelectedTerm_orientedYCompatibility_sound
      K q partAt term hmultiplicity sigma targets pooled yFirst.support
        hYFirstSubsetSelected hYProfiles
  have hYGroup : HasGroupUniqueLegFibers yFirst.support ySupport
      group (sigma .Y) :=
    groupCompatibilityIsolatedSupport_hasGroupUniqueLegFibers
      yFirst.support group (sigma .Y) compatibleY hSoundY
  have hYGroupSelf : HasGroupUniqueLegFibers ySupport ySupport
      group (sigma .Y) := hYGroup.toSelf

  have hZFirstSubsetSelected : zFirst.support ⊆ selected.support := by
    intro address haddress
    exact hYFirstSubsetSelected
      (hYSubset (hYUsefulSubset (hZFirstSubset haddress)))
  have hZProfiles : ∀ address ∈ zFirst.support,
      CWRecursivePooledAllZProfileMatches sigma partAt targets pooled address := by
    intro address haddress
    have hfirst := (mem_cwRecursivePooledZFirstZeroOut_support
      yUseful sigma partAt pooled.zAll address).mp haddress
    have hyData : address ∈ ySupport ∧ yKeep address := by
      simpa [yUseful, yUsefulSupport, yIsolated, groupStableSupport] using hfirst.1
    have hyFirstMem := hYSubset hyData.1
    have hyFirstData := (mem_cwRecursivePooledYFirstZeroOut_support
      xUseful sigma partAt pooled.yAll address).mp hyFirstMem
    have hxData : address ∈ hashed.support ∧ xKeep address := by
      simpa [xUseful, xSupport, groupStableSupport] using hyFirstData.1
    refine ⟨hxData.2, hyData.2, ?_⟩
    exact (cwRecursive_matchesZPooledAll_iff_labelMatches
      sigma partAt pooled.zAll address).mpr hfirst.2
  have hSoundZ : IsCompatibilitySound zFirst.support (sigma .Z) compatibleZ := by
    exact cwRecursiveSelectedTerm_orientedZCompatibility_sound
      K q partAt term hmultiplicity sigma targets pooled zFirst.support
        hZFirstSubsetSelected hZProfiles
  have hZGroup : HasGroupUniqueLegFibers zFirst.support zSupport
      group (sigma .Z) :=
    groupCompatibilityIsolatedSupport_hasGroupUniqueLegFibers
      zFirst.support group (sigma .Z) compatibleZ hSoundZ
  have hZGroupSelf : HasGroupUniqueLegFibers zSupport zSupport
      group (sigma .Z) := hZGroup.toSelf

  have hxRestrict : Restricts hashed.realize xUseful.realize := by
    simpa [xUseful, xSupport, xKeep, model] using
      Tensor.Restricts.partitionedGroupStableFilter hashed group (sigma .X) xKeep
        hXHashed (cwRecursiveMatchesExact_isGroupLabelStable
          partAt sigma hashed.support .X targets.xExact)
  have hyFirstRestrict : Restricts xUseful.realize yFirst.realize :=
    cwRecursivePooledYFirstZeroOut_restricts xUseful sigma partAt pooled.yAll
  have hyCompatibilityRestrict : Restricts yFirst.realize yIsolated.realize := by
    simpa [yIsolated, ySupport] using
      Tensor.Restricts.partitionedGroupCompatibilityIsolated
        yFirst group (sigma .Y) compatibleY hSoundY
  have hyUsefulRestrict : Restricts yIsolated.realize yUseful.realize := by
    simpa [yUseful, yUsefulSupport, yKeep, model] using
      Tensor.Restricts.partitionedGroupStableFilter yIsolated group (sigma .Y) yKeep
        (by simpa [yIsolated] using hYGroupSelf)
        (cwRecursiveMatchesExact_isGroupLabelStable
          partAt sigma yIsolated.support .Y targets.yExact)
  have hzFirstRestrict : Restricts yUseful.realize zFirst.realize :=
    cwRecursivePooledZFirstZeroOut_restricts yUseful sigma partAt pooled.zAll
  have hzCompatibilityRestrict : Restricts zFirst.realize zIsolated.realize := by
    simpa [zIsolated, zSupport] using
      Tensor.Restricts.partitionedGroupCompatibilityIsolated
        zFirst group (sigma .Z) compatibleZ hSoundZ
  have hzUsefulRestrict : Restricts zIsolated.realize zUseful.realize := by
    simpa [zUseful, zUsefulSupport, zKeep, model] using
      Tensor.Restricts.partitionedGroupStableFilter zIsolated group (sigma .Z) zKeep
        (by simpa [zIsolated] using hZGroupSelf)
        (cwRecursiveMatchesExact_isGroupLabelStable
          partAt sigma zIsolated.support .Z targets.zExact)

  have hXFinal : HasGroupUniqueLegFibers zUsefulSupport zUsefulSupport
      group (sigma .X) := by
    have hXAtX := hXHashed.restrictToSubset hxSubset
    have hXAtYFirst := hXAtX.restrictToSubset hXYFirstSubset
    have hXAtY := hXAtYFirst.restrictToSubset hYSubset
    have hXAtYUseful := hXAtY.restrictToSubset hYUsefulSubset
    have hXAtZFirst := hXAtYUseful.restrictToSubset hZFirstSubset
    have hXAtZ := hXAtZFirst.restrictToSubset hZSubset
    exact (hXAtZ.restrictToSubset hZUsefulSubset).toSelf
  have hYFinal : HasGroupUniqueLegFibers zUsefulSupport zUsefulSupport
      group (sigma .Y) := by
    have hYAtUseful := hYGroup.restrictToSubset hYUsefulSubset
    have hYAtZFirst := hYAtUseful.restrictToSubset hZFirstSubset
    have hYAtZ := hYAtZFirst.restrictToSubset hZSubset
    exact (hYAtZ.restrictToSubset hZUsefulSubset).toSelf
  have hZFinal : HasGroupUniqueLegFibers zUsefulSupport zUsefulSupport
      group (sigma .Z) := (hZGroup.restrictToSubset hZUsefulSubset).toSelf
  have hfinal : ∀ pivot,
      HasGroupUniqueLegFibers zUseful.support zUseful.support group pivot := by
    intro pivot
    have hpivot : sigma (sigma.symm pivot) = pivot := sigma.apply_symm_apply pivot
    generalize hlogical : sigma.symm pivot = logical at hpivot
    cases logical with
    | X =>
        have : sigma .X = pivot := by simpa [hlogical] using hpivot
        simpa [zUseful, this] using hXFinal
    | Y =>
        have : sigma .Y = pivot := by simpa [hlogical] using hpivot
        simpa [zUseful, this] using hYFinal
    | Z =>
        have : sigma .Z = pivot := by simpa [hlogical] using hpivot
        simpa [zUseful, this] using hZFinal
  let zeroWord : Fin ((n + 1) + (n + 1)) → CWRecursiveChildDigit depth :=
    fun _ ↦ 0
  let fallback : CWRecursiveCoarseAddress depth n := fun _c ↦ zeroWord
  let G : zUseful.LegGrouping (CWRecursiveCoarseAddress depth n) :=
    PartitionedTensor.LegGrouping.ofGroupUnique zUseful group fallback hfinal
  have hxClosed : IsProjectionClosed hashed.support xSupport {sigma .X} := by
    exact groupStableSupport_isProjectionClosed hashed.support group (sigma .X) xKeep
      hXHashed (cwRecursiveMatchesExact_isGroupLabelStable
        partAt sigma hashed.support .X targets.xExact)
  have hyFirstClosed : IsProjectionClosed xUseful.support yFirst.support Finset.univ := by
    simpa [yFirst, cwRecursivePooledYFirstZeroOut] using
      PartitionedTensor.select_support_isProjectionClosed_univ xUseful
        (fun c label ↦ c ≠ sigma .Y ∨
          CWRecursivePooledAllLabelMatches partAt pooled.yAll label)
  have hyCompatibilityClosed : IsProjectionClosed yFirst.support ySupport {sigma .Y} :=
    groupCompatibilityIsolatedSupport_isProjectionClosed
      yFirst.support group (sigma .Y) compatibleY hSoundY
  have hyUsefulClosed : IsProjectionClosed yIsolated.support yUsefulSupport {sigma .Y} := by
    exact groupStableSupport_isProjectionClosed yIsolated.support group (sigma .Y) yKeep
      (by simpa [yIsolated] using hYGroupSelf)
      (cwRecursiveMatchesExact_isGroupLabelStable
        partAt sigma yIsolated.support .Y targets.yExact)
  have hzFirstClosed : IsProjectionClosed yUseful.support zFirst.support Finset.univ := by
    simpa [zFirst, cwRecursivePooledZFirstZeroOut] using
      PartitionedTensor.select_support_isProjectionClosed_univ yUseful
        (fun c label ↦ c ≠ sigma .Z ∨
          CWRecursivePooledAllLabelMatches partAt pooled.zAll label)
  have hzCompatibilityClosed : IsProjectionClosed zFirst.support zSupport {sigma .Z} :=
    groupCompatibilityIsolatedSupport_isProjectionClosed
      zFirst.support group (sigma .Z) compatibleZ hSoundZ
  have hzUsefulClosed : IsProjectionClosed zIsolated.support zUsefulSupport {sigma .Z} := by
    exact groupStableSupport_isProjectionClosed zIsolated.support group (sigma .Z) zKeep
      (by simpa [zIsolated] using hZGroupSelf)
      (cwRecursiveMatchesExact_isGroupLabelStable
        partAt sigma zIsolated.support .Z targets.zExact)
  have hclosed : IsProjectionClosed hashed.support zUsefulSupport Finset.univ := by
    have hchain := (((((hxClosed.trans_union hyFirstClosed).trans_union
      hyCompatibilityClosed).trans_union hyUsefulClosed).trans_union
      hzFirstClosed).trans_union hzCompatibilityClosed).trans_union hzUsefulClosed
    simpa using hchain
  refine ⟨G, (fun _address ↦ rfl), hclosed,
    hxRestrict.trans (hyFirstRestrict.trans
      (hyCompatibilityRestrict.trans (hyUsefulRestrict.trans
        (hzFirstRestrict.trans (hzCompatibilityRestrict.trans
          (hzUsefulRestrict.trans ?_))))))⟩
  exact G.restricts_groupedIndexedDirectSum

end AlgebraicComplexity.Examples
