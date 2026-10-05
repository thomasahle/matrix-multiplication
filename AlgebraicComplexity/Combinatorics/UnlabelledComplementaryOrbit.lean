/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Combinatorics.ComplementaryPairFiber

/-!
# Unlabelled complementary-orbit sums

These lemmas concern set-valued fibers of an involution. A fixed point occurs once. They are
deliberately separate from `ComplementaryOccurrence`, where left and right child occurrences are
labelled and a self-complementary state therefore occurs twice.

The literal two-point case is provided by the lightweight imported module
`ComplementaryPairFiber`; this file adds the more general decomposition over an arbitrary set of
orbit representatives.
-/

open scoped BigOperators

namespace AlgebraicComplexity.WordType

universe u v

variable {Split : Type u} [Fintype Split] [DecidableEq Split] {Cell : Type v}

omit [Fintype Split] in
/-- An unlabelled profile summed over a complementation-closed finite set equals the sum over
orbit representatives, with a fixed point contributing once. -/
theorem sum_dualInvariant_eq_sum_representatives
    (dual : Split → Split) (hdual : Function.Involutive dual)
    (S region : Finset Split) (p : Split → ℕ)
    (hsub : region ⊆ S)
    (hclosed : ∀ u ∈ region, dual u ∈ S)
    (hcover : ∀ u ∈ S, u ∈ region ∨ dual u ∈ region)
    (hrep : ∀ u ∈ region, dual u ∈ region → dual u = u) :
    ∑ u ∈ S, p u =
      ∑ u ∈ region, (if dual u = u then p u else p u + p (dual u)) := by
  classical
  set tail : Finset Split := (region.filter fun u ↦ dual u ≠ u).image dual with htail
  have hdisjoint : Disjoint region tail := by
    rw [Finset.disjoint_right]
    intro v hv hvregion
    rw [htail, Finset.mem_image] at hv
    obtain ⟨u, hu, rfl⟩ := hv
    rw [Finset.mem_filter] at hu
    exact hu.2 (hrep u hu.1 hvregion)
  have hunion : S = region ∪ tail := by
    apply Finset.Subset.antisymm
    · intro v hv
      rcases hcover v hv with h | h
      · exact Finset.mem_union_left _ h
      · by_cases hvregion : v ∈ region
        · exact Finset.mem_union_left _ hvregion
        · refine Finset.mem_union_right _ ?_
          rw [htail, Finset.mem_image]
          refine ⟨dual v, ?_, hdual v⟩
          rw [Finset.mem_filter]
          refine ⟨h, ?_⟩
          intro hfix
          have hvfix : v = dual v := (hdual v).symm.trans hfix
          exact hvregion (by rw [hvfix]; exact h)
    · intro v hv
      rcases Finset.mem_union.mp hv with h | h
      · exact hsub h
      · rw [htail, Finset.mem_image] at h
        obtain ⟨u, hu, rfl⟩ := h
        exact hclosed u (Finset.mem_filter.mp hu).1
  have hsumTail : ∑ v ∈ tail, p v =
      ∑ u ∈ region.filter (fun u ↦ dual u ≠ u), p (dual u) := by
    rw [htail]
    exact Finset.sum_image fun a _ b _ h ↦ hdual.injective h
  calc
    ∑ u ∈ S, p u = ∑ u ∈ region ∪ tail, p u := by rw [hunion]
    _ = (∑ u ∈ region, p u) + ∑ v ∈ tail, p v := Finset.sum_union hdisjoint
    _ = (∑ u ∈ region, p u) +
          ∑ u ∈ region.filter (fun u ↦ dual u ≠ u), p (dual u) := by rw [hsumTail]
    _ = (∑ u ∈ region, p u) +
          ∑ u ∈ region, (if dual u = u then 0 else p (dual u)) := by
        refine congrArg (_ + ·) ?_
        rw [Finset.sum_filter]
        refine Finset.sum_congr rfl fun u _ ↦ ?_
        by_cases h : dual u = u <;> simp [h]
    _ = ∑ u ∈ region, (if dual u = u then p u else p u + p (dual u)) := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun u _ ↦ ?_
        by_cases h : dual u = u <;> simp [h]

/-- Cell mass of an unlabelled dual-closed fiber, written as a sum over representatives. -/
theorem mappedType_apply_eq_sum_representatives
    (cellMap : Split → Cell) (dual : Split → Split) (hdual : Function.Involutive dual)
    (hinv : ∀ u, cellMap (dual u) = cellMap u)
    (p : Split → ℕ) (c : Cell) (region : Finset Split)
    (hregion : ∀ u ∈ region, cellMap u = c)
    (hcover : ∀ u, cellMap u = c → (u ∈ region ∨ dual u ∈ region))
    (hrep : ∀ u ∈ region, dual u ∈ region → dual u = u) :
    mappedType cellMap p c =
      ∑ u ∈ region, (if dual u = u then p u else p u + p (dual u)) := by
  classical
  show ∑ u ∈ letterFiber cellMap c, p u = _
  refine sum_dualInvariant_eq_sum_representatives dual hdual _ region p ?_ ?_ ?_ hrep
  · intro u hu
    exact mem_letterFiber.mpr (hregion u hu)
  · intro u hu
    exact mem_letterFiber.mpr (by rw [hinv u]; exact hregion u hu)
  · intro u hu
    exact hcover u (mem_letterFiber.mp hu)

end AlgebraicComplexity.WordType
