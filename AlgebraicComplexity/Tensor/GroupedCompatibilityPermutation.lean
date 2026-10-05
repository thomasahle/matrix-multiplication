/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Tensor.GroupedCompatibilityOperationHoles
import AlgebraicComplexity.Tensor.PartitionedPermutation

set_option autoImplicit false

/-!
# Grouped-compatibility operation holes under leg permutations

The constituent cleanup of [alman2025more] is described for one region and then reused in the
other five regions by permuting the roles of the tensor legs.  This file records the finite
support identity needed at that orientation seam: transporting an ambient support, its coarse
group map, and its compatibility predicate through a leg permutation transports the set of
directly deleted pivot labels exactly.  An equivalence may simultaneously rename the coarse
groups.

The theorem is a generic transport law, not a new cleanup or counting argument.  It formalizes
the paper's statement in Section 6.6 that the algorithms in the other regions differ only by
permuting `X`, `Y`, and `Z` (`papers/sources/2404.16349/constituent.tex:497`).  Its motivating
application is the `Unique Triple` cleanup used in Claim 6.18: the `Y` and `Z` deletions are
stated in Sections 6.3.2 and 6.4.2 at lines `274-276` and `324-326`, while their hole counts enter
`cl:constituent:prob-of-holes` in Section 6.5 at lines `461-479`.

## Reference

- [alman2025more] Josh Alman, Ran Duan, Virginia Vassilevska Williams, Yinzhan Xu, Zixuan Xu,
  and Renfei Zhou, *More Asymmetry Yields Faster Matrix Multiplication*, Claim 6.18 and
  Sections 6.3.2, 6.4.2, 6.5, and 6.6.
-/

namespace AlgebraicComplexity.Tensor

universe u v w

variable {A : Leg → Type u} [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]
variable {Γ : Type v} {Δ : Type w} [DecidableEq Γ] [DecidableEq Δ]

omit [∀ c, Fintype (A c)] in
/-- **Direct grouped-compatibility holes commute with a permutation of tensor legs.**

The source pivot corresponding to target leg `pivot` is `e.symm pivot`.  On the target side,
addresses are sent forward by `permuteBlockAddress e`, while the group and compatibility maps
read an address by transporting it back.  Renaming groups by `groupEquiv` therefore changes
neither which source pivot labels are deleted nor their finite set.

Proof sketch: expand membership in the two deleted-label sets.  A target witness has a unique
source preimage because the transported ambient is a `Finset.map` along an equivalence.  Expand
membership in the isolated supports as well; inverse address transport preserves ambient
membership and compatibility, and `groupEquiv.injective` reflects the equality of coarse groups.
The two directions then send a deletion witness forward or backward along
`permuteBlockAddress e`. -/
theorem groupCompatibilityDeletedLabels_permuteBlockAddress
    (e : Orientation) (ambient : Finset (BlockAddress A))
    (group : BlockAddress A → Γ) (groupEquiv : Γ ≃ Δ) (pivot : Leg)
    (compatible : A (e.symm pivot) → BlockAddress A → Prop) (γ : Γ) :
    groupCompatibilityDeletedLabels
        (ambient.map (permuteBlockAddress e).toEmbedding)
        (fun address ↦ groupEquiv (group ((permuteBlockAddress e).symm address)))
        pivot
        (fun label address ↦ compatible label ((permuteBlockAddress e).symm address))
        (groupEquiv γ) =
      groupCompatibilityDeletedLabels ambient group (e.symm pivot) compatible γ := by
  classical
  ext label
  rw [mem_groupCompatibilityDeletedLabels_iff,
    mem_groupCompatibilityDeletedLabels_iff]
  constructor
  · rintro ⟨address, haddress, hgroup, hdeleted, hlabel⟩
    obtain ⟨source, hsource, rfl⟩ := Finset.mem_map.mp haddress
    refine ⟨source, hsource, ?_, ?_, ?_⟩
    · apply groupEquiv.injective
      simpa only [Equiv.toEmbedding_apply, Equiv.symm_apply_apply] using hgroup
    · intro hsourceIsolated
      apply hdeleted
      rw [mem_groupCompatibilityIsolatedSupport] at hsourceIsolated ⊢
      refine ⟨Finset.mem_map.mpr ⟨source, hsource, rfl⟩, ?_⟩
      intro other hother hcompatible
      obtain ⟨otherSource, hotherSource, rfl⟩ := Finset.mem_map.mp hother
      have hcompatibleSource :
          compatible (source (e.symm pivot)) otherSource := by
        simpa only [Equiv.toEmbedding_apply, permuteBlockAddress_apply,
          Equiv.symm_apply_apply] using hcompatible
      simpa only [Equiv.toEmbedding_apply, Equiv.symm_apply_apply] using
        congrArg groupEquiv
          (hsourceIsolated.2 otherSource hotherSource hcompatibleSource)
    · simpa only [Equiv.toEmbedding_apply, permuteBlockAddress_apply] using hlabel
  · rintro ⟨source, hsource, hgroup, hdeleted, hlabel⟩
    refine ⟨permuteBlockAddress e source,
      Finset.mem_map.mpr ⟨source, hsource, rfl⟩, ?_, ?_, ?_⟩
    · simpa only [Equiv.symm_apply_apply] using congrArg groupEquiv hgroup
    · intro htargetIsolated
      apply hdeleted
      rw [mem_groupCompatibilityIsolatedSupport] at htargetIsolated ⊢
      refine ⟨hsource, ?_⟩
      intro otherSource hotherSource hcompatibleSource
      have hcompatibleTarget :
          compatible
            (permuteBlockAddress e source pivot)
            ((permuteBlockAddress e).symm (permuteBlockAddress e otherSource)) := by
        simpa only [permuteBlockAddress_apply, Equiv.symm_apply_apply] using hcompatibleSource
      have htargetGroup := htargetIsolated.2
        (permuteBlockAddress e otherSource)
        (Finset.mem_map.mpr ⟨otherSource, hotherSource, rfl⟩)
        hcompatibleTarget
      apply groupEquiv.injective
      simpa only [Equiv.symm_apply_apply] using htargetGroup
    · simpa only [permuteBlockAddress_apply] using hlabel

end AlgebraicComplexity.Tensor
