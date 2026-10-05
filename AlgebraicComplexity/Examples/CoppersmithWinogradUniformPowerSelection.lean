/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.UniformPowerFusion
import AlgebraicComplexity.Examples.CoppersmithWinogradZeroCTensor

/-!
# The uniform local `q`-power of a Coppersmith--Winograd zero-`Z` interface

A supported Coppersmith--Winograd chunk whose `Z` block is the all-zero word has matrix
dimensions `⟨1, q ^ k, 1⟩`, with `k` the number of middle digits of its encoded `X` split word.
Along one selected outer address the local `q`-power is therefore `q` raised to the *total*
middle-digit count of the encoded `X` word, `cwInterfaceMiddleCount`.

This module instantiates `MatrixMultiplication/UniformPowerSelection.lean` and
`MatrixMultiplication/UniformPowerFusion.lean` at that statistic, on the zero-`Z` fiber whose
shared-leg support law is the committed
`cwSelectedExactInterfaceTerm_zeroZ_support_isSharedFiber`.

## The two routes, concretely

* **Loss free.**  `cwInterfaceMiddleCount_eq_of_mem_support` — an exact interface term stores a
  complete-split *profile* on every leg, and its selection retains exactly the addresses whose
  encoded chunk sequence realizes that profile.  So the total middle count, and hence the local
  `q`-power, is the same for every retained address, read off `term.split .X`.  No pigeonhole and
  no subexponential loss are spent.  This corrects the caveat recorded at
  `better_bound/r4_scoping/OBLIGATIONS.md` §9.4: the chunk *weight* indeed does not determine the
  middle count, but the stored *profile* does, and it is the profile the selection uses.
* **With the pigeonhole.**  `cwSelectedExactInterfaceTerm_zeroZ_exists_uniform_power_fibre` keeps
  the general route available for a family selected by weight alone: its loss is the named
  polynomial `UniformPowerSelection.uniformPowerLoss (2 ^ depth) n`, spent once over the outer
  power and *not* once per chunk.

## Leg convention

Every statement below is in Lean's `(X, Y, Z)` leg order, and the merged type-class dimension is
the **`Y`** dimension of the fused leaf `⟨1, mergedDimension, 1⟩`.  The certificate's own volume
coordinate `c` is the Coppersmith--Winograd matrix-shape slot `(c + 2) mod 3`
(`better_bound/r4_scoping/OBLIGATIONS.md` §9.1); a client pairing these statements with a
certificate row must apply that rotation.

## The remaining input

The tensor-algebraic input is an explicit hypothesis in every statement below, in two equivalent
shapes.  The abstract shape is a `CTensor.FiberRetyping` into the canonical one-slice spaces
together with the pointwise identification `htarget` of its constituents.  The concrete shape is
`hone` of `cwSelectedExactInterfaceTerm_zeroZ_restricts_oneSlice_of_labelMaps`: leg maps indexed
by the address's own `X` and `Y` block labels, plus **one** map shared by every retained address
on the common all-zero `Z` block, carrying each retained constituent onto
`CTensor.oneSliceConstituent K d`.

That hypothesis is exactly the shared-`Z` *map* coherence.  The committed per-chunk zero-`Z`
one-slice restrictions (`cwZeroChunkOneSliceRestriction`) expose their leg maps, but they are
built by `Classical.choice` from a `Nonempty`, so nothing in the committed chain proves that two
retained addresses with different base letters use one common map on their shared `Z` block.  The
coherence *is* available one level down — `cwZeroBaseOneSliceMap_Z_coherent` is `rfl` for the
explicit `200`/`020`/`110` maps — and is lost exactly at that `Classical.choice` wrapper.  It is
named in the release note and is not proved here.

The `X` and `Y` maps are indexed by the block label rather than by the selected subtype, because
that is what makes the pointwise identity dischargeable from a hypothesis quantified over
*addresses*: `ofSharedSupport` enumerates the selected support by an equivalence that it does not
expose, so a subtype-indexed map cannot be evaluated at a named address.  Only the values at
labels that actually occur in the selected support are used; a client may take any junk value —
`0`, say — at every other label.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor MoreAsymmetryCompatibility
open scoped BigOperators

universe u

/-- Outer block addresses of one exact Coppersmith--Winograd interface term. -/
abbrev CWInterfaceAddress (depth n : ℕ) :=
  BlockAddress fun _c : Leg ↦ PositiveWord (PositiveWord CWBlock (2 ^ depth - 1)) n

/-- **The local `q`-power exponent of one selected outer address.**  The total number of middle
digits in the encoded `X` word: on the zero-`Z` fiber the constituent's `Y` dimension is exactly
`q` raised to this count. -/
def cwInterfaceMiddleCount (depth n : ℕ) (address : CWInterfaceAddress depth n) : ℕ :=
  UniformPowerSelection.outerChunkStatistic
    (A := fun _c : Leg ↦ PositiveWord CWBlock (2 ^ depth - 1)) (n := n)
    (fun _c ↦ cwChunkSplitWord depth) splitWordMiddleCount .X address

/-- **The exact exponent stored by an interface term on one leg.**  The profile-weighted total
middle count; it depends only on the term's recorded complete-split profile. -/
def cwInterfaceQExponent {depth : ℕ} (term : ExactInterfaceTermParameters depth) (c : Leg) : ℕ :=
  ∑ word, (term.split c).counts word * splitWordMiddleCount word

/-- Each of the `n + 1` chunks contributes at most `2 ^ depth` middle digits, so the outer
exponent is at most `2 ^ depth * (n + 1)`.  This is the bound the outer-power pigeonhole is
applied at — polynomial in `n`. -/
theorem cwInterfaceMiddleCount_le (depth n : ℕ) (address : CWInterfaceAddress depth n) :
    cwInterfaceMiddleCount depth n address ≤ 2 ^ depth * (n + 1) :=
  UniformPowerSelection.outerChunkStatistic_le
    (A := fun _c : Leg ↦ PositiveWord CWBlock (2 ^ depth - 1)) (n := n)
    (fun _c ↦ cwChunkSplitWord depth) splitWordMiddleCount (2 ^ depth)
    UniformPowerSelection.splitWordMiddleCount_le_two_pow .X address

/-- **The selected family already has a uniform local `q`-power.**  Every address retained by an
exact Coppersmith--Winograd interface term carries the same total middle count, namely the
profile-weighted exponent `cwInterfaceQExponent term .X`.  The refinement to a uniform local
`q`-power is therefore *free* for this family: no pigeonhole is spent. -/
theorem cwInterfaceMiddleCount_eq_of_mem_support
    (K : Type u) [CommRing K] (q : ℕ) {depth n : ℕ}
    (term : ExactInterfaceTermParameters depth)
    (hmultiplicity : term.multiplicity = n + 1)
    (address : CWInterfaceAddress depth n)
    (haddress : address ∈ (cwSelectedExactInterfaceTerm K q term hmultiplicity).support) :
    cwInterfaceMiddleCount depth n address = cwInterfaceQExponent term .X :=
  UniformPowerSelection.outerChunkStatistic_eq_of_mem_selectEncodedExactInterfaceTerm_support
    (cwChunkPartitionedTensor K q depth) (fun _c ↦ cwChunkSplitWord depth) term hmultiplicity
    splitWordMiddleCount .X address haddress

/-- **The merged dimension of the whole retained class.**  Taking the exact zero-`Z` class whole
contributes `card * q ^ e` to one matrix dimension — the type-class reading `h · q ^ k` of the
paper's blueprint, not a single representative's `q ^ k` and not a maximum over addresses. -/
theorem cwSelectedExactInterfaceTerm_mergedDimension_eq
    (K : Type u) [CommRing K] (q : ℕ) {depth n : ℕ}
    (term : ExactInterfaceTermParameters depth)
    (hmultiplicity : term.multiplicity = n + 1) :
    ZeroCoordinateMerge.mergedDimension q (cwInterfaceMiddleCount depth n)
        (cwSelectedExactInterfaceTerm K q term hmultiplicity).support =
      (cwSelectedExactInterfaceTerm K q term hmultiplicity).support.card *
        q ^ cwInterfaceQExponent term .X :=
  ZeroCoordinateMerge.mergedDimension_of_uniform q _ _
    (fun address haddress ↦
      cwInterfaceMiddleCount_eq_of_mem_support K q term hmultiplicity address haddress)

/-- **The fused zero-`Z` leaf.**  Given the shared-`Z` C-tensor retyping of the selected support
into the canonical one-slice spaces, the whole exact interface term restricts to the single
matrix-multiplication tensor `⟨1, mergedDimension, 1⟩` (Lean leg order), whose middle dimension is
the merged dimension of the entire retained type class.  No representative is chosen and no loss
is paid. -/
theorem cwSelectedExactInterfaceTerm_restricts_mergedOneSlice
    (K : Type u) [CommRing K] (q : ℕ) {depth n : ℕ}
    (term : ExactInterfaceTermParameters depth)
    (hmultiplicity : term.multiplicity = n + 1)
    (C : CTensor.FiberRetyping
      (X := MMSpace K 1 (q ^ cwInterfaceQExponent term .X) 1 .X)
      (Y := MMSpace K 1 (q ^ cwInterfaceQExponent term .X) 1 .Y)
      (Z := MMSpace K 1 (q ^ cwInterfaceQExponent term .X) 1 .Z)
      (cwSelectedExactInterfaceTerm K q term hmultiplicity)
      (cwSelectedExactInterfaceTerm K q term hmultiplicity).support
      (cwSelectedExactInterfaceTerm K q term hmultiplicity).support.card)
    (htarget : ∀ i, C.targetConstituent i =
      CTensor.oneSliceConstituent K (q ^ cwInterfaceQExponent term .X)) :
    Restricts (cwSelectedExactInterfaceTerm K q term hmultiplicity).realize
      (matrixMultiplication (K := K) 1
        (ZeroCoordinateMerge.mergedDimension q (cwInterfaceMiddleCount depth n)
          (cwSelectedExactInterfaceTerm K q term hmultiplicity).support) 1) :=
  UniformPowerSelection.restricts_matrixMultiplication_mergedDimension_of_support
    (fun address haddress ↦
      cwInterfaceMiddleCount_eq_of_mem_support K q term hmultiplicity address haddress)
    C htarget

section LabelMaps

variable (K : Type u) [CommRing K] (q : ℕ) {depth n : ℕ}
  (term : ExactInterfaceTermParameters depth)
  (hmultiplicity : term.multiplicity = n + 1)
  (hz : term.index.count .Z = 0) (d : ℕ)
  (xMap : ∀ a : PositiveWord (PositiveWord CWBlock (2 ^ depth - 1)) n,
    CWExactInterfaceBlockSpace K q depth n .X a →ₗ[K] MMSpace K 1 d 1 .X)
  (yMap : ∀ a : PositiveWord (PositiveWord CWBlock (2 ^ depth - 1)) n,
    CWExactInterfaceBlockSpace K q depth n .Y a →ₗ[K] MMSpace K 1 d 1 .Y)
  (zMap : CWExactInterfaceBlockSpace K q depth n .Z (cwZeroInterfaceLegWord depth n) →ₗ[K]
    MMSpace K 1 d 1 .Z)

include hz in
/-- **The zero-`Z` fibre retyped as a one-slice C-tensor from label-indexed leg maps.**  The `X`
and `Y` maps may depend on the address's own block label; the `Z` map is one map, shared by every
retained address, on the common all-zero `Z` block.  The shared-leg support law consumed here is
the committed `cwSelectedExactInterfaceTerm_zeroZ_support_isSharedFiber`; nothing else about the
family is used. -/
noncomputable def cwZeroZOneSliceFiberRetyping :
    CTensor.FiberRetyping
      (X := MMSpace K 1 d 1 .X) (Y := MMSpace K 1 d 1 .Y) (Z := MMSpace K 1 d 1 .Z)
      (cwSelectedExactInterfaceTerm K q term hmultiplicity)
      (cwSelectedExactInterfaceTerm K q term hmultiplicity).support
      (cwSelectedExactInterfaceTerm K q term hmultiplicity).support.card :=
  CTensor.FiberRetyping.ofSharedSupport
    (cwSelectedExactInterfaceTerm K q term hmultiplicity) _
    (cwSelectedExactInterfaceTerm_zeroZ_support_isSharedFiber K q term hmultiplicity hz).2.1
    (cwSelectedExactInterfaceTerm_zeroZ_support_isSharedFiber K q term hmultiplicity hz).2.2
    (cwZeroInterfaceLegWord depth n)
    (cwSelectedExactInterfaceTerm_zeroZ_support_isSharedFiber K q term hmultiplicity hz).1
    (fun address ↦ xMap (address.1 .X)) (fun address ↦ yMap (address.1 .Y)) zMap

/-- Every constituent of the label-map retyping is a genuinely selected address's constituent,
mapped by that address's own leg maps.  This is what lets a client discharge the pointwise
one-slice identity by a hypothesis quantified over addresses. -/
theorem cwZeroZOneSliceFiberRetyping_targetConstituent
    (i : Fin (cwSelectedExactInterfaceTerm K q term hmultiplicity).support.card) :
    ∃ address ∈ (cwSelectedExactInterfaceTerm K q term hmultiplicity).support,
      (cwZeroZOneSliceFiberRetyping K q term hmultiplicity hz d
          xMap yMap zMap).targetConstituent i =
        Tensor.map
          (CTensor.FiberRetyping.oneSliceLabelConstituentMap
            (A := fun _c : Leg ↦ PositiveWord (PositiveWord CWBlock (2 ^ depth - 1)) n)
            (V := CWExactInterfaceBlockSpace K q depth n)
            (zLabel := cwZeroInterfaceLegWord depth n) xMap yMap zMap
            (address .X) (address .Y))
          ((cwSelectedExactInterfaceTerm K q term hmultiplicity).constituent
            (Tensor.ofLegs (address .X) (address .Y) (cwZeroInterfaceLegWord depth n))) := by
  refine ⟨_, CTensor.FiberRetyping.sourceAddress_mem
    (cwZeroZOneSliceFiberRetyping K q term hmultiplicity hz d xMap yMap zMap) i, ?_⟩
  have hmap :
      (cwZeroZOneSliceFiberRetyping K q term hmultiplicity hz d
          xMap yMap zMap).constituentMap i =
        CTensor.FiberRetyping.oneSliceLabelConstituentMap
          (A := fun _c : Leg ↦ PositiveWord (PositiveWord CWBlock (2 ^ depth - 1)) n)
          (V := CWExactInterfaceBlockSpace K q depth n)
          (zLabel := cwZeroInterfaceLegWord depth n) xMap yMap zMap
          ((cwZeroZOneSliceFiberRetyping K q term hmultiplicity hz d
            xMap yMap zMap).sourceAddress i .X)
          ((cwZeroZOneSliceFiberRetyping K q term hmultiplicity hz d
            xMap yMap zMap).sourceAddress i .Y) := by
    funext c
    cases c <;> rfl
  show Tensor.map _ _ = _
  rw [hmap]
  rfl

include hz in
/-- **The fused zero-`Z` leaf, from per-address leg maps.**  If every retained address's
constituent is carried onto the canonical one-slice tensor `⟨1, d, 1⟩` by leg maps that depend
only on its `X` and `Y` block labels and share one common map on the all-zero `Z` block, then the
whole exact interface term restricts to `⟨1, card * d, 1⟩` — the *entire* retained type class,
cardinality included, in one matrix dimension (Lean leg order: the `Y` dimension).

This is item 4 with its input reduced to the shared-`Z` **map** coherence: the committed
per-chunk zero-`Z` one-slice restrictions expose their leg maps
(`cwZeroChunkOneSliceRestriction`), but nothing yet proves that different retained addresses use
one common map on their shared `Z` block.  That is the named residual; it is not proved here. -/
theorem cwSelectedExactInterfaceTerm_zeroZ_restricts_oneSlice_of_labelMaps
    (hone : ∀ address ∈ (cwSelectedExactInterfaceTerm K q term hmultiplicity).support,
      Tensor.map
          (CTensor.FiberRetyping.oneSliceLabelConstituentMap
            (A := fun _c : Leg ↦ PositiveWord (PositiveWord CWBlock (2 ^ depth - 1)) n)
            (V := CWExactInterfaceBlockSpace K q depth n)
            (zLabel := cwZeroInterfaceLegWord depth n) xMap yMap zMap
            (address .X) (address .Y))
          ((cwSelectedExactInterfaceTerm K q term hmultiplicity).constituent
            (Tensor.ofLegs (address .X) (address .Y) (cwZeroInterfaceLegWord depth n))) =
        CTensor.oneSliceConstituent K d) :
    Restricts (cwSelectedExactInterfaceTerm K q term hmultiplicity).realize
      (matrixMultiplication (K := K) 1
        ((cwSelectedExactInterfaceTerm K q term hmultiplicity).support.card * d) 1) := by
  refine CTensor.FiberRetyping.restricts_oneSliceMatrixMultiplication_of_support
    (cwZeroZOneSliceFiberRetyping K q term hmultiplicity hz d xMap yMap zMap) ?_
  intro i
  obtain ⟨address, haddress, heq⟩ := cwZeroZOneSliceFiberRetyping_targetConstituent
    K q term hmultiplicity hz d xMap yMap zMap i
  rw [heq]
  exact hone address haddress

end LabelMaps

/-- **Item 4 for the CW zero-`Z` leaf.**  At the exact local power `q ^ e` fixed by the stored
complete-split profile, the leaf of the previous theorem is `⟨1, mergedDimension, 1⟩`: the merged
dimension of the entire retained type class.  Nothing is lost — no representative is chosen and no
subexponential factor is spent. -/
theorem cwSelectedExactInterfaceTerm_zeroZ_restricts_mergedOneSlice_of_labelMaps
    (K : Type u) [CommRing K] (q : ℕ) {depth n : ℕ}
    (term : ExactInterfaceTermParameters depth)
    (hmultiplicity : term.multiplicity = n + 1)
    (hz : term.index.count .Z = 0)
    (xMap : ∀ a : PositiveWord (PositiveWord CWBlock (2 ^ depth - 1)) n,
      CWExactInterfaceBlockSpace K q depth n .X a →ₗ[K]
        MMSpace K 1 (q ^ cwInterfaceQExponent term .X) 1 .X)
    (yMap : ∀ a : PositiveWord (PositiveWord CWBlock (2 ^ depth - 1)) n,
      CWExactInterfaceBlockSpace K q depth n .Y a →ₗ[K]
        MMSpace K 1 (q ^ cwInterfaceQExponent term .X) 1 .Y)
    (zMap : CWExactInterfaceBlockSpace K q depth n .Z (cwZeroInterfaceLegWord depth n) →ₗ[K]
      MMSpace K 1 (q ^ cwInterfaceQExponent term .X) 1 .Z)
    (hone : ∀ address ∈ (cwSelectedExactInterfaceTerm K q term hmultiplicity).support,
      Tensor.map
          (CTensor.FiberRetyping.oneSliceLabelConstituentMap
            (A := fun _c : Leg ↦ PositiveWord (PositiveWord CWBlock (2 ^ depth - 1)) n)
            (V := CWExactInterfaceBlockSpace K q depth n)
            (zLabel := cwZeroInterfaceLegWord depth n) xMap yMap zMap
            (address .X) (address .Y))
          ((cwSelectedExactInterfaceTerm K q term hmultiplicity).constituent
            (Tensor.ofLegs (address .X) (address .Y) (cwZeroInterfaceLegWord depth n))) =
        CTensor.oneSliceConstituent K (q ^ cwInterfaceQExponent term .X)) :
    Restricts (cwSelectedExactInterfaceTerm K q term hmultiplicity).realize
      (matrixMultiplication (K := K) 1
        (ZeroCoordinateMerge.mergedDimension q (cwInterfaceMiddleCount depth n)
          (cwSelectedExactInterfaceTerm K q term hmultiplicity).support) 1) := by
  rw [cwSelectedExactInterfaceTerm_mergedDimension_eq K q term hmultiplicity]
  exact cwSelectedExactInterfaceTerm_zeroZ_restricts_oneSlice_of_labelMaps
    K q term hmultiplicity hz (q ^ cwInterfaceQExponent term .X) xMap yMap zMap hone

/-- **The pigeonhole route, kept available.**  Without using exactness of the stored profile, the
zero-`Z` shared-leg support law alone yields a uniform-power sub-family at the named
subexponential cost `UniformPowerSelection.uniformPowerLoss (2 ^ depth) n`, together with the
degeneration of the whole term onto the sub-family's merged leaf.  The `X`-injectivity that makes
the sub-family a degeneration rather than a deletion is the committed
`cwSelectedExactInterfaceTerm_zeroZ_support_isSharedFiber`. -/
theorem cwSelectedExactInterfaceTerm_zeroZ_exists_uniform_power_fibre
    (K : Type u) [CommRing K] (q : ℕ) {depth n : ℕ}
    (term : ExactInterfaceTermParameters depth)
    (hmultiplicity : term.multiplicity = n + 1)
    (hz : term.index.count .Z = 0)
    (retyping : ∀ k : ℕ, CTensor.FiberRetyping
      (X := MMSpace K 1 (q ^ k) 1 .X)
      (Y := MMSpace K 1 (q ^ k) 1 .Y)
      (Z := MMSpace K 1 (q ^ k) 1 .Z)
      (cwSelectedExactInterfaceTerm K q term hmultiplicity)
      ((cwSelectedExactInterfaceTerm K q term hmultiplicity).support.filter
        fun address ↦ cwInterfaceMiddleCount depth n address = k)
      ((cwSelectedExactInterfaceTerm K q term hmultiplicity).support.filter
        fun address ↦ cwInterfaceMiddleCount depth n address = k).card)
    (htarget : ∀ k i,
      (retyping k).targetConstituent i = CTensor.oneSliceConstituent K (q ^ k)) :
    ∃ k ≤ 2 ^ depth * (n + 1),
      ((ZeroCoordinateMerge.mergedDimension q (cwInterfaceMiddleCount depth n)
            (cwSelectedExactInterfaceTerm K q term hmultiplicity).support : ℕ) : ℝ) ≤
          UniformPowerSelection.uniformPowerLoss (2 ^ depth) n *
            ((ZeroCoordinateMerge.mergedDimension q (cwInterfaceMiddleCount depth n)
              ((cwSelectedExactInterfaceTerm K q term hmultiplicity).support.filter
                fun address ↦ cwInterfaceMiddleCount depth n address = k) : ℕ) : ℝ) ∧
        Restricts (cwSelectedExactInterfaceTerm K q term hmultiplicity).realize
          (matrixMultiplication (K := K) 1
            (ZeroCoordinateMerge.mergedDimension q (cwInterfaceMiddleCount depth n)
              ((cwSelectedExactInterfaceTerm K q term hmultiplicity).support.filter
                fun address ↦ cwInterfaceMiddleCount depth n address = k)) 1) :=
  UniformPowerSelection.exists_uniform_power_fibre_restricts_mergedDimension
    (cwSelectedExactInterfaceTerm K q term hmultiplicity)
    (cwInterfaceMiddleCount depth n) q (2 ^ depth) n
    (fun address _ ↦ cwInterfaceMiddleCount_le depth n address)
    (cwSelectedExactInterfaceTerm_zeroZ_support_isSharedFiber K q term hmultiplicity hz).2.1
    retyping htarget

end AlgebraicComplexity.Examples
