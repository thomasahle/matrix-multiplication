/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinogradCompatibility
import AlgebraicComplexity.Examples.CoppersmithWinogradZeroWord
import AlgebraicComplexity.MatrixMultiplication.ZeroCoordinateOrientation

/-!
# Exact zero-coordinate Coppersmith--Winograd interfaces, in every orientation

`CoppersmithWinogradZeroInterface` discharges the shared-leg support law for an exact CW interface
term whose **`Z`** coordinate is zero.  The certificate's active zero blocks are spread over all
three orientations with comparable mass at every depth — mass-weighted, level two carries
`0.476869995` on `X`, `0.437464549` on `Y` and `0.454193503` on `Z`, and levels three and four are
similarly balanced (orientation census of the certificate) — so roughly two thirds of
the zero mass is out of reach of the zero-`Z` statement alone.

This module closes that gap by instantiating the orientation-indexed generic law
`MoreAsymmetryCompatibility.selectedExactInterfaceTerm_zero_support_isSharedFiber` at the native
CW chunk encoding.  The instantiation is done **once**, with the zero leg free; the zero-`X` and
zero-`Y` statements are specializations of it, not copies of a proof.

## What is reused

Every side condition is the same one the committed zero-`Z` file supplies, and none of them
mentions a leg:

| hypothesis | discharged by |
|---|---|
| `hencode` | `cwChunkSplitWord_injective depth` |
| `hlegalSupport` | `cwChunkPartitionedTensor_isEncodedFineLegalOnSupport` |
| `zeroLabel`, `hzeroLabel` | `cwZeroChunkWord depth`, `cwChunkSplitWord_zeroChunkWord depth` |

That is the content of the orientation claim: the CW-specific inputs to the zero-coordinate law
are orientation-free, so the leg permutation costs nothing beyond naming it.  The shared block word
is `cwZeroInterfaceLegWord depth n` on whichever leg is zero, exactly as in the `Z` orientation.

## Leg convention

Statements are in Lean's `(X, Y, Z)` order and carry their zero leg in the name (or, for the
generic form, as an explicit argument), with the two live legs computed by
`MoreAsymmetryCompatibility.firstLiveLeg` / `secondLiveLeg`.  A certificate client must still
apply the volume-coordinate rotation `c ↦ (c + 2) % 3` of
`better_bound/r4_scoping/OBLIGATIONS.md` §9.1; nothing here depends on it.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor MoreAsymmetryCompatibility

universe u

/-- **Shared-leg C-tensor support law, in every orientation.**  On an exact CW interface term whose
weight at leg `zero` vanishes, the block word at that leg is the constant all-zero word and either
of the two live block words is injective on the entire selected support.

No representative selection occurs, and the zero leg is a free variable. -/
theorem cwSelectedExactInterfaceTerm_zero_support_isSharedFiber
    (K : Type u) [CommRing K] (q : ℕ) {depth n : ℕ}
    (term : ExactInterfaceTermParameters depth)
    (hmultiplicity : term.multiplicity = n + 1)
    (zero : Leg) (hzero : term.index.count zero = 0) :
    (∀ address ∈ (cwSelectedExactInterfaceTerm K q term hmultiplicity).support,
        address zero = cwZeroInterfaceLegWord depth n) ∧
      Set.InjOn (fun address ↦ address (firstLiveLeg zero))
        ((cwSelectedExactInterfaceTerm K q term hmultiplicity).support :
          Set (BlockAddress fun _c ↦ PositiveWord (PositiveWord CWBlock (2 ^ depth - 1)) n)) ∧
      Set.InjOn (fun address ↦ address (secondLiveLeg zero))
        ((cwSelectedExactInterfaceTerm K q term hmultiplicity).support :
          Set (BlockAddress fun _c ↦ PositiveWord (PositiveWord CWBlock (2 ^ depth - 1)) n)) := by
  simpa [cwSelectedExactInterfaceTerm, cwZeroInterfaceLegWord] using
    (selectedExactInterfaceTerm_zero_support_isSharedFiber
      (P := cwChunkPartitionedTensor K q depth)
      (encode := fun _c ↦ cwChunkSplitWord depth)
      (hencode := fun _c ↦ cwChunkSplitWord_injective depth)
      (hlegalSupport := cwChunkPartitionedTensor_isEncodedFineLegalOnSupport K q depth)
      (term := term) (hmultiplicity := hmultiplicity) (zero := zero) (hzero := hzero)
      (zeroLabel := cwZeroChunkWord depth)
      (hzeroLabel := cwChunkSplitWord_zeroChunkWord depth))

/-- **Zero-`X` shared-leg support law.**  The `X` block word is the constant all-zero word and
either of `Y`, `Z` determines the whole selected address. -/
theorem cwSelectedExactInterfaceTerm_zeroX_support_isSharedFiber
    (K : Type u) [CommRing K] (q : ℕ) {depth n : ℕ}
    (term : ExactInterfaceTermParameters depth)
    (hmultiplicity : term.multiplicity = n + 1)
    (hx : term.index.count .X = 0) :
    (∀ address ∈ (cwSelectedExactInterfaceTerm K q term hmultiplicity).support,
        address .X = cwZeroInterfaceLegWord depth n) ∧
      Set.InjOn (fun address ↦ address .Y)
        ((cwSelectedExactInterfaceTerm K q term hmultiplicity).support :
          Set (BlockAddress fun _c ↦ PositiveWord (PositiveWord CWBlock (2 ^ depth - 1)) n)) ∧
      Set.InjOn (fun address ↦ address .Z)
        ((cwSelectedExactInterfaceTerm K q term hmultiplicity).support :
          Set (BlockAddress fun _c ↦ PositiveWord (PositiveWord CWBlock (2 ^ depth - 1)) n)) :=
  cwSelectedExactInterfaceTerm_zero_support_isSharedFiber K q term hmultiplicity .X hx

/-- **Zero-`Y` shared-leg support law.**  The `Y` block word is the constant all-zero word and
either of `X`, `Z` determines the whole selected address.  The two injectivity conjuncts are in leg
order; the generic form lists them in the cyclic order `(Z, X)`. -/
theorem cwSelectedExactInterfaceTerm_zeroY_support_isSharedFiber
    (K : Type u) [CommRing K] (q : ℕ) {depth n : ℕ}
    (term : ExactInterfaceTermParameters depth)
    (hmultiplicity : term.multiplicity = n + 1)
    (hy : term.index.count .Y = 0) :
    (∀ address ∈ (cwSelectedExactInterfaceTerm K q term hmultiplicity).support,
        address .Y = cwZeroInterfaceLegWord depth n) ∧
      Set.InjOn (fun address ↦ address .X)
        ((cwSelectedExactInterfaceTerm K q term hmultiplicity).support :
          Set (BlockAddress fun _c ↦ PositiveWord (PositiveWord CWBlock (2 ^ depth - 1)) n)) ∧
      Set.InjOn (fun address ↦ address .Z)
        ((cwSelectedExactInterfaceTerm K q term hmultiplicity).support :
          Set (BlockAddress fun _c ↦ PositiveWord (PositiveWord CWBlock (2 ^ depth - 1)) n)) := by
  obtain ⟨hconst, hfirst, hsecond⟩ :=
    cwSelectedExactInterfaceTerm_zero_support_isSharedFiber K q term hmultiplicity .Y hy
  exact ⟨hconst, hsecond, hfirst⟩

/-- **Zero-`Z` shared-leg support law, re-derived.**  The committed
`cwSelectedExactInterfaceTerm_zeroZ_support_isSharedFiber` as the instance `zero = .Z`.  The
committed theorem is untouched; this one exists to certify that the orientation-indexed law really
does subsume it, and a later consolidation pass should keep only one of the two. -/
theorem cwSelectedExactInterfaceTerm_zeroZ_support_isSharedFiber'
    (K : Type u) [CommRing K] (q : ℕ) {depth n : ℕ}
    (term : ExactInterfaceTermParameters depth)
    (hmultiplicity : term.multiplicity = n + 1)
    (hz : term.index.count .Z = 0) :
    (∀ address ∈ (cwSelectedExactInterfaceTerm K q term hmultiplicity).support,
        address .Z = cwZeroInterfaceLegWord depth n) ∧
      Set.InjOn (fun address ↦ address .X)
        ((cwSelectedExactInterfaceTerm K q term hmultiplicity).support :
          Set (BlockAddress fun _c ↦ PositiveWord (PositiveWord CWBlock (2 ^ depth - 1)) n)) ∧
      Set.InjOn (fun address ↦ address .Y)
        ((cwSelectedExactInterfaceTerm K q term hmultiplicity).support :
          Set (BlockAddress fun _c ↦ PositiveWord (PositiveWord CWBlock (2 ^ depth - 1)) n)) :=
  cwSelectedExactInterfaceTerm_zero_support_isSharedFiber K q term hmultiplicity .Z hz

end AlgebraicComplexity.Examples
