/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Tensor.Partitioned

set_option autoImplicit false

/-!
# Blockwise maps between partitioned tensors

Layer 1 (`AlgebraicComplexity/Tensor/`).  Two partitioned tensors over *different* block alphabets
are compared here by a **block dictionary** `dict c : A c → B c` together with one linear map per
source block.  The induced legwise map on the ambient direct sums carries the first realization
onto the second whenever the dictionary is injective on the source support, the target support is
its image, and every source constituent is carried to the corresponding target constituent.

## Why this and not `reindex`

`PartitionedTensor.reindex` (`Tensor/PartitionedReindex.lean`) transports a partitioned tensor
along a legwise *equivalence* of block alphabets with *equivalences* of block spaces.  That is the
wrong instrument whenever the two alphabets have different sizes — the motivating case is a
selected block of a tensor square, whose alphabet is a word alphabet with many labels, against a
coordinate presentation of the same tensor with only the few labels it actually uses.  No alphabet
equivalence exists, and none is needed: the ambient map is built from `DirectSum.toModule`, which
accepts an arbitrary family of maps out of the summands, so unused source blocks are simply sent to
zero and the two alphabets may even live in different universes.

`Restricts.partitionedSelect` (`Tensor/Partitioned.lean`) is the special case `A = B`,
`dict = id`, `φ = id`, with the target support a subset of the source support.

Primary source: none; this is partitioned-tensor infrastructure.
-/

namespace AlgebraicComplexity.Tensor

open scoped DirectSum

universe u v v' w x

section BlockMap

variable {K : Type u} [CommSemiring K]
variable {A : Leg → Type w} [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]
variable {B : Leg → Type x} [∀ c, Fintype (B c)] [∀ c, DecidableEq (B c)]
variable {V : ∀ c, A c → Type v} [∀ c a, AddCommMonoid (V c a)] [∀ c a, Module K (V c a)]
variable {W : ∀ c, B c → Type v'} [∀ c b, AddCommMonoid (W c b)] [∀ c b, Module K (W c b)]

/-- **The legwise ambient map determined by a block dictionary and blockwise linear maps.**

On the summand of the source block `a` it is the map `φ c a` followed by the inclusion of the
target block `dict c a`. -/
noncomputable def partitionedBlockMap (dict : ∀ c, A c → B c)
    (φ : ∀ c a, V c a →ₗ[K] W c (dict c a)) (c : Leg) :
    PartitionedSpace K V c →ₗ[K] PartitionedSpace K W c :=
  DirectSum.toModule K (A c) _
    (fun a ↦ (DirectSum.lof K (B c) (W c) (dict c a)).comp (φ c a))

omit [∀ c, Fintype (A c)] [∀ c, Fintype (B c)] in
/-- On one block, the ambient map is the block map followed by the target block inclusion. -/
theorem partitionedBlockMap_comp_blockInclude (dict : ∀ c, A c → B c)
    (φ : ∀ c a, V c a →ₗ[K] W c (dict c a)) (s : BlockAddress A) (c : Leg) :
    partitionedBlockMap (K := K) (V := V) (W := W) dict φ c ∘ₗ
        blockInclude (K := K) (V := V) s c =
      blockInclude (K := K) (V := W) (fun c ↦ dict c (s c)) c ∘ₗ φ c (s c) := by
  ext x
  simp [partitionedBlockMap, blockInclude, DirectSum.toModule_lof]

omit [∀ c, Fintype (A c)] [∀ c, Fintype (B c)] in
/-- One embedded constituent is carried to the embedded image of its blockwise image. -/
theorem map_partitionedBlockMap_block (dict : ∀ c, A c → B c)
    (φ : ∀ c a, V c a →ₗ[K] W c (dict c a)) (s : BlockAddress A)
    (T : Tensor3 K (fun c ↦ V c (s c))) :
    map (partitionedBlockMap (K := K) (V := V) (W := W) dict φ)
        (map (blockInclude (K := K) (V := V) s) T) =
      map (blockInclude (K := K) (V := W) (fun c ↦ dict c (s c)))
        (map (fun c ↦ φ c (s c)) T) := by
  have hcomp : (fun c ↦ partitionedBlockMap (K := K) (V := V) (W := W) dict φ c ∘ₗ
        blockInclude (K := K) (V := V) s c) =
      (fun c ↦ blockInclude (K := K) (V := W) (fun c ↦ dict c (s c)) c ∘ₗ φ c (s c)) :=
    funext fun c ↦ partitionedBlockMap_comp_blockInclude dict φ s c
  rw [map_map_comp, map_map_comp, hcomp]

namespace Restricts

/-- **A blockwise map along a block dictionary is an exact tensor restriction.**

The three hypotheses are exactly what makes the ambient map identify the two realizations term by
term: `hinj` lets the source sum be reindexed along the dictionary, `hsupport` says the target sum
runs over precisely the image, and `hconstituent` matches the summands.

`hconstituent` is stated **after** embedding both sides into the ambient spaces, and with the image
address as a bound variable carrying its defining equation.  That is not decoration: the
unembedded equation
`map (fun c ↦ φ c (s c)) (P.constituent s) = Q.constituent (fun c ↦ dict c (s c))`
is stated in a block-space family indexed by the composite `fun c ↦ dict c (s c)`, and a client
that knows this composite to be some named address cannot rewrite it there — the rewrite motive
would have to retype the left-hand side as well, and it is not type-correct.  Both sides here live
in the ambient spaces, which do not mention an address at all, so a client substitutes the equation
for the bound `t` and then works with a named address on the right.

Proof sketch: apply the ambient map to the source sum, discharge each summand by `hconstituent` at
the reflexivity witness, and reindex the sum by `Finset.sum_image`. -/
theorem partitionedBlockMap
    (P : PartitionedTensor (K := K) (A := A) V)
    (Q : PartitionedTensor (K := K) (A := B) W)
    (dict : ∀ c, A c → B c)
    (φ : ∀ c a, V c a →ₗ[K] W c (dict c a))
    (hinj : ∀ s ∈ P.support, ∀ t ∈ P.support,
      (fun c ↦ dict c (s c)) = (fun c ↦ dict c (t c)) → s = t)
    (hsupport : Q.support = P.support.image (fun s ↦ (fun c ↦ dict c (s c))))
    (hconstituent : ∀ s ∈ P.support, ∀ t : BlockAddress B,
      (fun c ↦ dict c (s c)) = t →
      map (AlgebraicComplexity.Tensor.partitionedBlockMap (K := K) (V := V) (W := W) dict φ)
          (map (blockInclude (K := K) (V := V) s) (P.constituent s)) =
        map (blockInclude (K := K) (V := W) t) (Q.constituent t)) :
    Restricts P.realize Q.realize := by
  classical
  refine ⟨AlgebraicComplexity.Tensor.partitionedBlockMap (K := K) (V := V) (W := W) dict φ, ?_⟩
  unfold PartitionedTensor.realize realizePartition
  rw [map_sum, hsupport, Finset.sum_image hinj]
  exact Finset.sum_congr rfl fun s hs ↦ hconstituent s hs _ rfl

end Restricts

end BlockMap

end AlgebraicComplexity.Tensor
