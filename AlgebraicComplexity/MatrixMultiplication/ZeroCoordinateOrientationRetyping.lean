/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.CTensorFiberEnumeration
import AlgebraicComplexity.MatrixMultiplication.ZeroCoordinateOrientation
import AlgebraicComplexity.Tensor.PartitionedPermutation

/-!
# C-tensor retyping of a shared fibre on an arbitrary leg

`CTensor.FiberRetyping` is hard-wired to a shared **`Z`** block with injective `X` and `Y` labels,
because that is the shape the one-slice fusion consumes.  A zero-coordinate family whose shared
block sits on `X` or on `Y` therefore cannot be fed to `ofSharedSupportAmbient` directly.

This module supplies the transport, once, for an arbitrary orientation `e`: the leg-permuted
partition certificate `P.permute e` of `Tensor/PartitionedPermutation.lean` has shared block
`e.symm .Z` and injective labels `e.symm .X`, `e.symm .Y` read off the *source* addresses, so the
committed enumerator applies to it verbatim.  Realization commutes with the permutation exactly
(`PartitionedTensor.permute_realize`), so the restriction obtained downstream is a restriction of
`Tensor.permute e P.realize`.

## Why the conclusion stays in the permuted frame

`Tensor.permute e.symm (Tensor.permute e T)` is only *isomorphic* to `T`, not equal — the two
ambient leg families differ by a dependent reindexing, which is exactly what
`Tensor.Isomorphic.permute_cycle_cycle` isolates for the cyclic case.  Rotating back is therefore a
separate, deliberate step and belongs with the leaf packaging, where the leg convention of
`better_bound/r4_scoping/OBLIGATIONS.md` §9.1 is applied anyway (and where
`ZeroCoordinateMerge.mergeX` / `mergeY` / `mergeZ` name the three cells).  Keeping the conclusion in
the permuted frame here means a client cannot silently pair a rotated tensor with an unrotated
dimension: the orientation is written in the statement.

## What is generic and what is not

Everything below is generic in `e`.  The three zero orientations are the instances
`e = zeroOrientation .X = Tensor.cycle.symm`, `e = zeroOrientation .Y = Tensor.cycle` and
`e = zeroOrientation .Z = 1` of `MoreAsymmetryCompatibility.zeroOrientation`, whose bridge lemmas
`zeroOrientation_symm_X/Y/Z` identify `e.symm .X`, `e.symm .Y`, `e.symm .Z` with
`firstLiveLeg zero`, `secondLiveLeg zero` and `zero`.  At a *concrete* zero leg those identities
hold definitionally, so an instantiation costs a statement and no proof.

No Coppersmith--Winograd constant and no certificate datum occurs here.
-/

namespace AlgebraicComplexity

open Tensor

universe u v w

namespace CTensor.FiberRetyping

variable {K : Type u} [CommSemiring K]
variable {A : Leg → Type w} [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]
variable {V : ∀ c, A c → Type (max u v w)}
variable [∀ c a, AddCommMonoid (V c a)] [∀ c a, Module K (V c a)]

/-! ## Transporting the two support hypotheses through a leg permutation -/

omit [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)] in
/-- Injectivity of the block label at leg `e.symm c` on a selected support is injectivity of the
block label at leg `c` on its leg-permuted image. -/
theorem injOn_map_permuteBlockAddress (e : Orientation)
    (selected : Finset (BlockAddress A)) (c : Leg)
    (h : Set.InjOn (fun address ↦ address (e.symm c)) (selected : Set (BlockAddress A))) :
    Set.InjOn (fun address ↦ address c)
      ((selected.map (permuteBlockAddress e).toEmbedding :
          Finset (BlockAddress (PermutedBlockIndex e A))) :
        Set (BlockAddress (PermutedBlockIndex e A))) := by
  intro left hleft right hright hlabel
  simp only [Finset.mem_coe, Finset.mem_map, Equiv.coe_toEmbedding] at hleft hright
  obtain ⟨source, hsource, rfl⟩ := hleft
  obtain ⟨target, htarget, rfl⟩ := hright
  have hsourceTarget : source = target :=
    h (Finset.mem_coe.mpr hsource) (Finset.mem_coe.mpr htarget) (by simpa using hlabel)
  rw [hsourceTarget]

omit [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)] in
/-- A block label that is constant at leg `e.symm c` on a selected support is constant at leg `c`
on its leg-permuted image. -/
theorem forall_map_permuteBlockAddress_eq (e : Orientation)
    (selected : Finset (BlockAddress A)) (c : Leg) (label : A (e.symm c))
    (h : ∀ address ∈ selected, address (e.symm c) = label) :
    ∀ address ∈ selected.map (permuteBlockAddress e).toEmbedding, address c = label := by
  intro address haddress
  simp only [Finset.mem_map, Equiv.coe_toEmbedding] at haddress
  obtain ⟨source, hsource, rfl⟩ := haddress
  simpa using h source hsource

/-! ## The retyping, and the restriction it certifies -/

/-- **Ambient C-tensor retyping of a fibre shared on an arbitrary leg.**  The shared block sits at
leg `e.symm .Z` of the source addresses and the two injective labels at `e.symm .X`, `e.symm .Y`;
the result is a retyping of the leg-permuted certificate `P.permute e`, whose shared block is on
`Z` as the one-slice fusion requires.

At `e = 1` this is exactly `ofSharedSupportAmbient P P.support`. -/
noncomputable def ofSharedSupportPermutedAmbient
    (P : PartitionedTensor (K := K) (A := A) V) (e : Orientation)
    (hx : Set.InjOn (fun address ↦ address (e.symm .X)) (P.support : Set (BlockAddress A)))
    (hy : Set.InjOn (fun address ↦ address (e.symm .Y)) (P.support : Set (BlockAddress A)))
    (zLabel : A (e.symm .Z))
    (hz : ∀ address ∈ P.support, address (e.symm .Z) = zLabel) :
    FiberRetyping
      (X := PartitionedSpace K (PermutedBlockSpace e V) .X)
      (Y := PartitionedSpace K (PermutedBlockSpace e V) .Y)
      (Z := PartitionedSpace K (PermutedBlockSpace e V) .Z)
      (P.permute e) (P.permute e).support (P.permute e).support.card :=
  ofSharedSupportAmbient.{u, v, w} (P.permute e) (P.permute e).support
    (injOn_map_permuteBlockAddress e P.support .X hx)
    (injOn_map_permuteBlockAddress e P.support .Y hy)
    zLabel (forall_map_permuteBlockAddress_eq e P.support .Z zLabel hz)

/-- **The whole shared-fibre tensor, permuted, restricts to its canonically enumerated C-tensor.**

The C-tensor has `(P.permute e).support.card = P.support.card` constituents and no representative
selection occurs.  This is the orientation-free form of
`Examples.cwSelectedExactInterfaceTerm_zeroZ_restricts_ambientCTensor`. -/
theorem restricts_permute_ofSharedSupportPermutedAmbient
    (P : PartitionedTensor (K := K) (A := A) V) (e : Orientation)
    (hx : Set.InjOn (fun address ↦ address (e.symm .X)) (P.support : Set (BlockAddress A)))
    (hy : Set.InjOn (fun address ↦ address (e.symm .Y)) (P.support : Set (BlockAddress A)))
    (zLabel : A (e.symm .Z))
    (hz : ∀ address ∈ P.support, address (e.symm .Z) = zLabel) :
    Restricts (Tensor.permute e P.realize)
      (CTensor.partitioned
        (ofSharedSupportPermutedAmbient.{u, v, w} P e hx hy zLabel hz).targetConstituent).realize
      := by
  have hrestricts :=
    (ofSharedSupportPermutedAmbient.{u, v, w} P e hx hy zLabel hz).restricts_partitioned
  have hself : (P.permute e).withSupport (P.permute e).support = P.permute e := rfl
  rw [hself, PartitionedTensor.permute_realize] at hrestricts
  exact hrestricts

/-- The permuted retyping has exactly as many constituents as the source support. -/
@[simp] theorem permute_support_card
    (P : PartitionedTensor (K := K) (A := A) V) (e : Orientation) :
    (P.permute e).support.card = P.support.card :=
  Finset.card_map _

end CTensor.FiberRetyping

end AlgebraicComplexity
