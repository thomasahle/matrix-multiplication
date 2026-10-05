/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Tensor.PartitionedPermutation

/-!
# Transporting isolated block-label families through leg permutations

Hashing theorems often produce a finite family whose block addresses are injective on two named
legs.  A later tensor construction may use a different orientation.  This file records the exact
finite transport: mapping the family by `permuteBlockAddress e` sends injectivity on source leg
`e⁻¹(c)` to injectivity on target leg `c`.

The cyclic specialization is the one needed by asymmetric CW extraction.  Since
`cycle⁻¹(Y)=X` and `cycle⁻¹(Z)=Y`, an X/Y-isolated family becomes Y/Z-isolated after one
cycle.  No tensor restriction or cardinality estimate is involved.
-/

namespace AlgebraicComplexity

open Tensor

universe w

variable {A : Leg → Type w}

/-- Pointwise leg permutation of a finite block-address family. -/
def permutedAddressFamily (e : Orientation) (family : Finset (BlockAddress A)) :
    Finset (BlockAddress (PermutedBlockIndex e A)) :=
  family.map (permuteBlockAddress e).toEmbedding

/-- Leg permutation preserves the number of addresses in a finite family. -/
@[simp] theorem card_permutedAddressFamily
    (e : Orientation) (family : Finset (BlockAddress A)) :
    (permutedAddressFamily e family).card = family.card := by
  exact Finset.card_map _

/-- Injectivity of one source block label transports to its corresponding target leg. -/
theorem injOn_leg_permutedAddressFamily
    (e : Orientation) (family : Finset (BlockAddress A))
    (sourceLeg targetLeg : Leg) (hleg : e.symm targetLeg = sourceLeg)
    (hinjective : Set.InjOn
      (fun address : BlockAddress A ↦ address sourceLeg) family) :
    Set.InjOn
      (fun address : BlockAddress (PermutedBlockIndex e A) ↦ address targetLeg)
      (permutedAddressFamily e family) := by
  classical
  subst sourceLeg
  intro left hleft right hright hcoordinate
  have hleft' : left ∈ permutedAddressFamily e family := hleft
  have hright' : right ∈ permutedAddressFamily e family := hright
  obtain ⟨leftSource, hleftSource, hleftEq⟩ :=
    Finset.mem_map.mp hleft'
  obtain ⟨rightSource, hrightSource, hrightEq⟩ :=
    Finset.mem_map.mp hright'
  have hleftEq' : permuteBlockAddress e leftSource = left := hleftEq
  have hrightEq' : permuteBlockAddress e rightSource = right := hrightEq
  have hsourceCoordinate :
      leftSource (e.symm targetLeg) = rightSource (e.symm targetLeg) := by
    have htargetCoordinate :
        permuteBlockAddress e leftSource targetLeg =
          permuteBlockAddress e rightSource targetLeg := by
      exact (congrFun hleftEq' targetLeg).trans
        (hcoordinate.trans (congrFun hrightEq' targetLeg).symm)
    simpa only [permuteBlockAddress_apply] using htargetCoordinate
  have hsource : leftSource = rightSource :=
    hinjective hleftSource hrightSource hsourceCoordinate
  calc
    left = permuteBlockAddress e leftSource := hleftEq'.symm
    _ = permuteBlockAddress e rightSource := congrArg (permuteBlockAddress e) hsource
    _ = right := hrightEq'

/-- A cyclic relabelling sends simultaneous X/Y isolation to simultaneous Y/Z isolation. -/
theorem yz_injectiveOn_cycle_permutedAddressFamily_of_xy
    (family : Finset (BlockAddress A))
    (hX : Set.InjOn (fun address : BlockAddress A ↦ address .X) family)
    (hY : Set.InjOn (fun address : BlockAddress A ↦ address .Y) family) :
    Set.InjOn
        (fun address : BlockAddress (PermutedBlockIndex cycle A) ↦ address .Y)
        (permutedAddressFamily cycle family) ∧
      Set.InjOn
        (fun address : BlockAddress (PermutedBlockIndex cycle A) ↦ address .Z)
        (permutedAddressFamily cycle family) :=
  ⟨injOn_leg_permutedAddressFamily cycle family .X .Y rfl hX,
    injOn_leg_permutedAddressFamily cycle family .Y .Z rfl hY⟩

end AlgebraicComplexity
