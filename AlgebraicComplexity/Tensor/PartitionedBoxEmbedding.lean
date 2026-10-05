/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Tensor.PartitionedBoxRetyping
import AlgebraicComplexity.Tensor.PartitionedBlockMap

set_option autoImplicit false

/-!
# Embedding a compact box in its ambient partitioned spaces

The compact representation removes unused block labels from the leg spaces, not from the tensor
inside the box. Including its summands back into the ambient direct sums therefore recovers the
same box exactly. Together with `Restricts.box_to_compactBox`, this makes the two representations
mutually restricting; it does not assert an isomorphism of their differently sized leg spaces.

This is the representation step used before splitting the intact box in the Total-Weight manuscript,
`better_bound/paper.tex`, hypothesis `hyp:intact-box` (lines 1219–1229). The result is generic:
it supplies neither that hypothesis's child-product factorization nor any hole or counting bound.
The existing block-dictionary map supplies the inclusion, so no second direct-sum map API is needed.
The selected child-product terminology follows [alman2025more],
`papers/sources/2404.16349/constituent.tex:488–495`; no extraction theorem from that paper
is assumed.
-/

namespace AlgebraicComplexity.Tensor

universe u v w

variable {K : Type u} [CommSemiring K]
variable {A : Leg → Type w} [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]
variable {V : ∀ c, A c → Type v}
variable [∀ c a, AddCommMonoid (V c a)] [∀ c a, Module K (V c a)]

/-- The compact box restricts to the same box in the original ambient leg spaces.

Proof sketch: the dictionary forgets each label's membership proof and uses the identity on its
block space. It is injective, its support image is exactly the ambient box support, and it keeps
every constituent unchanged. This only pads unused coordinates by zero; it does not reconstruct
any term removed when the box was selected.
-/
theorem Restricts.compactBox_to_box
    (P : PartitionedTensor (K := K) (A := A) V)
    (parts : ∀ c, Finset (A c)) :
    Restricts (compactBox P parts).realize (P.box parts).realize := by
  classical
  apply Restricts.partitionedBlockMap (compactBox P parts) (P.box parts)
    (fun _ a ↦ a.1) (fun _ _ ↦ LinearMap.id)
  · intro s _ t _ h
    funext c
    exact Subtype.ext (congrFun h c)
  · ext address
    simp only [PartitionedTensor.mem_box_support, Finset.mem_image]
    constructor
    · rintro ⟨hsource, hparts⟩
      refine ⟨fun c ↦ ⟨address c, hparts c⟩, ?_, rfl⟩
      exact (mem_compactBox_support_iff P parts _).2 hsource
    · rintro ⟨source, hsource, rfl⟩
      exact ⟨(mem_compactBox_support_iff P parts source).1 hsource,
        fun c ↦ (source c).2⟩
  · intro source _ target htarget
    subst target
    rw [map_partitionedBlockMap_block]
    simp only [map_id, LinearMap.id_apply]
    rfl

end AlgebraicComplexity.Tensor
