/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Tensor.HoleRepair

set_option autoImplicit false

/-!
# Restriction between partitioned boxes

This file records a support-level form of variable zeroing for partitioned tensors.  A target
box need not use legwise smaller part sets than a source box: it is enough that every supported
target address already occurs in the source box.  Ordinary block zeroing then extracts the target
realization exactly.

The result is useful when the source support was produced by several sequential cleanup
operations while the target is specified by a single conservative tuple of surviving labels.
It is pure tensor infrastructure and contains no client-specific compatibility or repair data.

The motivating application is the compatibility-cleanup and hole-repair step in Claim 6.18 of
[alman2025more].  More precisely, it abstracts the final Cartesian-support step of Proposition
`prop:grouped-cleanup` in the Total-Weight manuscript,
`better_bound/paper.tex:859-898`, especially lines `890-895`.

## Reference

- [alman2025more] Josh Alman, Ran Duan, Virginia Vassilevska Williams, Yinzhan Xu, Zixuan Xu,
  and Renfei Zhou, *More Asymmetry Yields Faster Matrix Multiplication*, Claim 6.18.
- *Total-Weight Hashing and Rectangular Volume in the Coppersmith--Winograd Method*,
  Proposition `prop:grouped-cleanup`.
-/

namespace AlgebraicComplexity.Tensor

universe u v w

variable {K : Type u} [CommSemiring K]
variable {A : Leg → Type w} [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]
variable {V : ∀ c, A c → Type v}
variable [∀ c a, AddCommMonoid (V c a)] [∀ c a, Module K (V c a)]

namespace Restricts

/-- **A supported target box can be extracted from any source box containing its support.**

The hypothesis concerns supported addresses, rather than requiring the target part set to be a
subset of the source part set on every leg.  This is strictly more flexible when some nominal
parts do not occur in the ambient partitioned tensor.

Proof sketch: zero the source box again using the target part sets.  Its resulting support is the
intersection of the two boxes.  The assumed support inclusion identifies that intersection with
the target box, while the constituent families agree definitionally. -/
theorem partitionedBox_of_support_subset
    (P : PartitionedTensor (K := K) (A := A) V)
    (source target : ∀ c, Finset (A c))
    (hsubset : (P.box target).support ⊆ (P.box source).support) :
    Restricts (P.box source).realize (P.box target).realize := by
  have hzero := partitionedBox (P.box source) target
  have hrealize : ((P.box source).box target).realize = (P.box target).realize := by
    apply PartitionedTensor.realize_eq_of_support_eq
    · ext address
      constructor
      · intro haddress
        have houter := (PartitionedTensor.mem_box_support
          (P.box source) target address).mp haddress
        have hsource := (PartitionedTensor.mem_box_support
          P source address).mp houter.1
        exact (PartitionedTensor.mem_box_support P target address).mpr
          ⟨hsource.1, houter.2⟩
      · intro htarget
        have htargetParts :=
          (PartitionedTensor.mem_box_support P target address).mp htarget |>.2
        exact (PartitionedTensor.mem_box_support
          (P.box source) target address).mpr ⟨hsubset htarget, htargetParts⟩
    · intro _address _haddress
      rfl
  rw [hrealize] at hzero
  exact hzero

end Restricts

end AlgebraicComplexity.Tensor
