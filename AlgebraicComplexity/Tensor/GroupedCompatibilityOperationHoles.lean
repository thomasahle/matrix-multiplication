/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Tensor.GroupedCompatibilityZeroing

set_option autoImplicit false

/-!
# Operation-level holes for grouped compatibility cleanup

Grouped compatibility isolation is a genuine zero-out on its pivot leg.  This file records the
stronger fiberwise form of that fact: inside one fixed coarse group, the surviving support is
exactly the ambient group fiber with the pivot labels deleted by that operation removed.

This formulation is useful for sequential cleanup.  A logical-`Y` pass contributes only its
directly deleted `Y` labels, and a later logical-`Z` pass contributes only its directly deleted
`Z` labels in the actual post-`Y` ambient.  Labels on the other legs which cease to occur need not
be misclassified as direct compatibility holes; their incident constituents have already been
removed by one of those two honest variable zero-outs.

Everything here is finite support algebra.  It mentions no hashing model, tensor client, or
repair estimate.  The motivating cleanup order is Claim 6.18 of [alman2025more].

## Reference

- [alman2025more] Josh Alman, Ran Duan, Virginia Vassilevska Williams, Yinzhan Xu, Zixuan Xu,
  and Renfei Zhou, *More Asymmetry Yields Faster Matrix Multiplication*, Claim 6.18,
  Sections 6.3.2 and 6.4.2; the `Unique Triple` deletion steps adjacent to
  `def:constituent:Y-compatibility` and `def:constituent:compatibility` in
  `papers/sources/2404.16349/constituent.tex:274-276,324-326`.
-/

namespace AlgebraicComplexity.Tensor

universe u v

variable {A : Leg → Type u} [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]
variable {Γ : Type v} [DecidableEq Γ]

/-- Pivot labels in one coarse group which are removed by a grouped compatibility isolation.

The group restriction is important: the same pivot label may occur in several coarse groups
before cleanup.  The definition records the operation performed on the fiber named by `γ`, not
the projection of every deletion in the global ambient support. -/
noncomputable def groupCompatibilityDeletedLabels
    (ambient : Finset (BlockAddress A)) (group : BlockAddress A → Γ)
    (pivot : Leg) (compatible : A pivot → BlockAddress A → Prop)
    (γ : Γ) : Finset (A pivot) := by
  classical
  exact (ambient.filter fun address ↦
    group address = γ ∧
      address ∉ groupCompatibilityIsolatedSupport ambient group pivot compatible).image
        (fun address ↦ address pivot)

omit [∀ c, Fintype (A c)] in
/-- A label is an operation hole precisely when some ambient address in the advertised group
uses that label and is deleted by grouped compatibility isolation. -/
theorem mem_groupCompatibilityDeletedLabels_iff
    (ambient : Finset (BlockAddress A)) (group : BlockAddress A → Γ)
    (pivot : Leg) (compatible : A pivot → BlockAddress A → Prop)
    (γ : Γ) (label : A pivot) :
    label ∈ groupCompatibilityDeletedLabels ambient group pivot compatible γ ↔
      ∃ address ∈ ambient,
        group address = γ ∧
          address ∉ groupCompatibilityIsolatedSupport ambient group pivot compatible ∧
            address pivot = label := by
  classical
  simp only [groupCompatibilityDeletedLabels, Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro ⟨address, ⟨hambient, hgroup, hdeleted⟩, hlabel⟩
    exact ⟨address, hambient, hgroup, hdeleted, hlabel⟩
  · rintro ⟨address, hambient, hgroup, hdeleted, hlabel⟩
    exact ⟨address, ⟨hambient, hgroup, hdeleted⟩, hlabel⟩

/-- **A grouped compatibility pass is exactly pivot-label deletion inside each group.**

For a fixed coarse group `γ`, filter the isolated support to that group.  The result is the
ambient `γ`-fiber filtered by the complement of the operation's deleted pivot labels.

Proof sketch: a deleted address itself witnesses that its pivot label is deleted.  Conversely,
suppose a surviving address and a deleted address in the same group have the same pivot label.
The survivor's uniqueness condition then also proves the deleted address's uniqueness condition,
because compatibility reads only that common label and both addresses have the same group.  This
contradicts deletion.  No compatibility-soundness hypothesis is needed. -/
theorem groupCompatibilityIsolatedFiberSupport_eq_filter_not_mem_deletedLabels
    (ambient : Finset (BlockAddress A)) (group : BlockAddress A → Γ)
    (pivot : Leg) (compatible : A pivot → BlockAddress A → Prop)
    (γ : Γ) :
    (groupCompatibilityIsolatedSupport ambient group pivot compatible).filter
        (fun address ↦ group address = γ) =
      (ambient.filter fun address ↦ group address = γ).filter
        (fun address ↦
          address pivot ∉
            groupCompatibilityDeletedLabels ambient group pivot compatible γ) := by
  classical
  ext address
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hisolated, hgroup⟩
    have hambient := groupCompatibilityIsolatedSupport_subset
      ambient group pivot compatible hisolated
    refine ⟨⟨hambient, hgroup⟩, ?_⟩
    intro hdeletedLabel
    obtain ⟨deleted, hdeletedAmbient, hdeletedGroup, hdeleted, hlabel⟩ :=
      (mem_groupCompatibilityDeletedLabels_iff
        ambient group pivot compatible γ (address pivot)).mp hdeletedLabel
    apply hdeleted
    apply (mem_groupCompatibilityIsolatedSupport
      ambient group pivot compatible deleted).mpr
    refine ⟨hdeletedAmbient, ?_⟩
    have hunique := (mem_groupCompatibilityIsolatedSupport
      ambient group pivot compatible address).mp hisolated |>.2
    intro other hother hcompatible
    have hcompatibleAddress : compatible (address pivot) other := by
      simpa only [hlabel] using hcompatible
    exact (hunique other hother hcompatibleAddress).trans
      (hgroup.trans hdeletedGroup.symm)
  · rintro ⟨⟨hambient, hgroup⟩, hnotDeletedLabel⟩
    refine ⟨?_, hgroup⟩
    by_contra hnotIsolated
    apply hnotDeletedLabel
    apply (mem_groupCompatibilityDeletedLabels_iff
      ambient group pivot compatible γ (address pivot)).mpr
    exact ⟨address, hambient, hgroup, hnotIsolated, rfl⟩

end AlgebraicComplexity.Tensor
