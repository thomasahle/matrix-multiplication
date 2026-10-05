/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.ZeroCoordinateInterface

/-!
# Exact zero-coordinate interface supports, in every orientation

`ZeroCoordinateInterface` proves the shared-leg support law for an exact interface term whose
**`Z`** coordinate is zero.  A laser-method certificate meets zero blocks in all three
orientations, so the same law is needed with the zero on `X` and on `Y`.

This module states the law **once**, indexed by the zero leg, and derives the three orientations
from that single theorem.  Nothing is triplicated: the two live legs are named by an explicit
cyclic rotation of the zero leg, the underlying complement law is stated in the same rotated form,
and the committed zero-`Z` statement is recovered verbatim as the instance `zero = .Z`.

## The two live legs, and the orientation that normalizes them

If leg `zero` carries zero weight, the other two legs are `firstLiveLeg zero = cycle zero` and
`secondLiveLeg zero = cycle (cycle zero)`.  In the three orientations that reads

| `zero` | `firstLiveLeg` | `secondLiveLeg` |
|---|---|---|
| `X` | `Y` | `Z` |
| `Y` | `Z` | `X` |
| `Z` | `X` | `Y` |

so the committed zero-`Z` pair `(X, Y)` is the instance `zero = .Z`, in that order.

`zeroOrientation zero` is the leg permutation that rotates this back to the canonical picture: it
sends `zero ↦ .Z`, `firstLiveLeg zero ↦ .X` and `secondLiveLeg zero ↦ .Y`, i.e. it is `1`,
`Tensor.cycle` and `Tensor.cycle.symm` for `zero = .Z`, `.Y` and `.X` respectively.  It is supplied
here with its three bridge lemmas and their inverses so that a downstream C-tensor client can move
a zero-`X` or zero-`Y` family into the shared-`Z` normal form the committed enumerator expects,
**without** guessing the rotation.

## Why the statements are indexed by a leg rather than duplicated

Certificate volume coordinates and Lean leg names differ by a rotation
(`better_bound/r4_scoping/OBLIGATIONS.md` §9.1), so a zero-orientation statement that only names
`X`, `Y` and `Z` is easy to instantiate at the wrong cell.  Every theorem below carries its zero
leg as an explicit argument, and the live legs are *computed* from it, so a client cannot pair a
zero-`X` support law with a zero-`Y` dimension by accident.  The three specializations at the end
are the convenience forms, stated in Lean's `(X, Y, Z)` order.

No Coppersmith--Winograd constant, no certificate datum and no tensor algebra occurs here; this is
purely the support half.
-/

namespace AlgebraicComplexity
namespace MoreAsymmetryCompatibility

open Tensor

universe u v w

/-! ## Leg-named orientation constants -/

/-- The first of the two legs left live by a zero at leg `zero`, in cyclic order. -/
def firstLiveLeg (zero : Leg) : Leg := cycle zero

/-- The second of the two legs left live by a zero at leg `zero`, in cyclic order. -/
def secondLiveLeg (zero : Leg) : Leg := cycle (cycle zero)

@[simp] theorem firstLiveLeg_X : firstLiveLeg .X = .Y := rfl
@[simp] theorem firstLiveLeg_Y : firstLiveLeg .Y = .Z := rfl
@[simp] theorem firstLiveLeg_Z : firstLiveLeg .Z = .X := rfl

@[simp] theorem secondLiveLeg_X : secondLiveLeg .X = .Z := rfl
@[simp] theorem secondLiveLeg_Y : secondLiveLeg .Y = .X := rfl
@[simp] theorem secondLiveLeg_Z : secondLiveLeg .Z = .Y := rfl

/-- The zero leg and its two live legs are pairwise distinct: the three names below really do
enumerate the three legs. -/
theorem firstLiveLeg_ne_self (zero : Leg) : firstLiveLeg zero ≠ zero := by
  cases zero <;> simp

theorem secondLiveLeg_ne_self (zero : Leg) : secondLiveLeg zero ≠ zero := by
  cases zero <;> simp

theorem secondLiveLeg_ne_firstLiveLeg (zero : Leg) : secondLiveLeg zero ≠ firstLiveLeg zero := by
  cases zero <;> simp

/-- **Leg trichotomy.**  Every leg is the zero leg or one of its two live legs.  This is the case
split that replaces the committed `cases c with | X | Y | Z` once the zero leg is a variable. -/
theorem leg_eq_or_eq_firstLiveLeg_or_eq_secondLiveLeg (zero c : Leg) :
    c = zero ∨ c = firstLiveLeg zero ∨ c = secondLiveLeg zero := by
  cases zero <;> cases c <;> simp

/-- The leg permutation that rotates a zero at leg `zero` into the canonical zero-`Z` picture.

It sends `zero` to `.Z`, `firstLiveLeg zero` to `.X` and `secondLiveLeg zero` to `.Y`. -/
def zeroOrientation : Leg → Orientation
  | .X => cycle.symm
  | .Y => cycle
  | .Z => 1

@[simp] theorem zeroOrientation_zero (zero : Leg) : zeroOrientation zero zero = .Z := by
  cases zero <;> rfl

@[simp] theorem zeroOrientation_firstLiveLeg (zero : Leg) :
    zeroOrientation zero (firstLiveLeg zero) = .X := by
  cases zero <;> rfl

@[simp] theorem zeroOrientation_secondLiveLeg (zero : Leg) :
    zeroOrientation zero (secondLiveLeg zero) = .Y := by
  cases zero <;> rfl

@[simp] theorem zeroOrientation_symm_Z (zero : Leg) : (zeroOrientation zero).symm .Z = zero := by
  cases zero <;> rfl

@[simp] theorem zeroOrientation_symm_X (zero : Leg) :
    (zeroOrientation zero).symm .X = firstLiveLeg zero := by
  cases zero <;> rfl

@[simp] theorem zeroOrientation_symm_Y (zero : Leg) :
    (zeroOrientation zero).symm .Y = secondLiveLeg zero := by
  cases zero <;> rfl

/-- The zero-`Z` orientation is the identity, so the whole rotation layer is inert on the
committed orientation. -/
@[simp] theorem zeroOrientation_Z : zeroOrientation .Z = 1 := rfl

/-! ## The complement law, in rotated form -/

/-- **The three committed complement laws are one law.**  On a coarse cell whose `zero` coordinate
vanishes, the fine word at `secondLiveLeg zero` is the complement of the fine word at
`firstLiveLeg zero`.

Specializing `zero := .Z` gives `y_eq_complement_x_of_z_eq_zero`, `zero := .X` gives
`z_eq_complement_y_of_x_eq_zero`, and `zero := .Y` gives the involution flip of
`z_eq_complement_x_of_y_eq_zero`. -/
theorem CompatibilityModel.secondLiveChunk_eq_complement_firstLiveChunk_of_get_eq_zero
    {A : Leg → Type v} {Part : Type u} {depth samples : ℕ}
    (model : CompatibilityModel A Part depth samples)
    (address : BlockAddress A) (hlegal : model.IsFineLegal address)
    (hweights : model.HasCoarseWeights address) (sample : Fin samples)
    (zero : Leg) (hzero : (model.coarse address sample).get zero = 0) :
    model.chunks (secondLiveLeg zero) (address (secondLiveLeg zero)) sample =
      complementSplitWord
        (model.chunks (firstLiveLeg zero) (address (firstLiveLeg zero)) sample) := by
  cases zero with
  | X =>
      exact model.z_eq_complement_y_of_x_eq_zero address hlegal hweights sample hzero
  | Y =>
      have h := model.z_eq_complement_x_of_y_eq_zero address hlegal hweights sample hzero
      simpa using congrArg complementSplitWord h.symm
  | Z =>
      exact model.y_eq_complement_x_of_z_eq_zero address hlegal hweights sample hzero

/-! ## The selected-interface support law -/

section

variable {K : Type u} [CommSemiring K]
variable {A : Leg → Type w} [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]
variable {V : ∀ c, A c → Type (max u v)}
variable [∀ c a, AddCommMonoid (V c a)] [∀ c a, Module K (V c a)]
variable {depth n : ℕ}

/-- On a selected interface with zero weight at leg `zero`, the encoded chunk at
`secondLiveLeg zero` is the digitwise complement of the encoded chunk at `firstLiveLeg zero`. -/
theorem selectedExactInterfaceTerm_secondLiveChunk_eq_complement_firstLiveChunk
    (P : PartitionedTensor (K := K) (A := A) V)
    (encode : ∀ c, A c → SplitWord depth)
    (hlegalSupport : IsEncodedFineLegalOnSupport P.support encode)
    (term : ExactInterfaceTermParameters depth)
    (hmultiplicity : term.multiplicity = n + 1)
    (zero : Leg) (hzero : term.index.count zero = 0)
    (address : BlockAddress (fun c ↦ PositiveWord (A c) n))
    (haddress : address ∈
      (P.selectEncodedExactInterfaceTerm encode term hmultiplicity).support)
    (sample : Fin (n + 1)) :
    encode (secondLiveLeg zero)
        (positiveWordEquiv (A (secondLiveLeg zero)) n (address (secondLiveLeg zero)) sample) =
      complementSplitWord
        (encode (firstLiveLeg zero)
          (positiveWordEquiv (A (firstLiveLeg zero)) n
            (address (firstLiveLeg zero)) sample)) := by
  let partAt : Fin (n + 1) → Unit := fun _ ↦ ()
  let model := encodedPositiveWordCompatibilityModel encode partAt
  have hlegal : model.IsFineLegal address :=
    encodedPositiveWordCompatibilityModel_isFineLegal_of_mem_exactInterfaceTerm_support
      P encode partAt hlegalSupport term hmultiplicity address haddress
  have hweights : model.HasCoarseWeights address :=
    encodedPositiveWordCompatibilityModel_hasCoarseWeights encode partAt address
  have hcoarse : (model.coarse address sample).get zero = 0 := by
    rw [← hweights zero sample]
    exact (selectedExactInterfaceTerm_chunkWeight P encode term hmultiplicity
      address haddress zero sample).trans hzero
  exact model.secondLiveChunk_eq_complement_firstLiveChunk_of_get_eq_zero
    address hlegal hweights sample zero hcoarse

/-- Equality of the `firstLiveLeg` block words forces equality of the `secondLiveLeg` ones. -/
theorem selectedExactInterfaceTerm_secondLiveLeg_eq_of_firstLiveLeg_eq
    (P : PartitionedTensor (K := K) (A := A) V)
    (encode : ∀ c, A c → SplitWord depth)
    (hlegalSupport : IsEncodedFineLegalOnSupport P.support encode)
    (term : ExactInterfaceTermParameters depth)
    (hmultiplicity : term.multiplicity = n + 1)
    (zero : Leg) (hzero : term.index.count zero = 0)
    (hencodeSecond : Function.Injective (encode (secondLiveLeg zero)))
    (left right : BlockAddress (fun c ↦ PositiveWord (A c) n))
    (hleft : left ∈ (P.selectEncodedExactInterfaceTerm encode term hmultiplicity).support)
    (hright : right ∈ (P.selectEncodedExactInterfaceTerm encode term hmultiplicity).support)
    (hfirst : left (firstLiveLeg zero) = right (firstLiveLeg zero)) :
    left (secondLiveLeg zero) = right (secondLiveLeg zero) := by
  apply (positiveWordEquiv (A (secondLiveLeg zero)) n).injective
  funext sample
  apply hencodeSecond
  rw [selectedExactInterfaceTerm_secondLiveChunk_eq_complement_firstLiveChunk
      P encode hlegalSupport term hmultiplicity zero hzero left hleft sample,
    selectedExactInterfaceTerm_secondLiveChunk_eq_complement_firstLiveChunk
      P encode hlegalSupport term hmultiplicity zero hzero right hright sample,
    hfirst]

/-- Equality of the `secondLiveLeg` block words forces equality of the `firstLiveLeg` ones. -/
theorem selectedExactInterfaceTerm_firstLiveLeg_eq_of_secondLiveLeg_eq
    (P : PartitionedTensor (K := K) (A := A) V)
    (encode : ∀ c, A c → SplitWord depth)
    (hlegalSupport : IsEncodedFineLegalOnSupport P.support encode)
    (term : ExactInterfaceTermParameters depth)
    (hmultiplicity : term.multiplicity = n + 1)
    (zero : Leg) (hzero : term.index.count zero = 0)
    (hencodeFirst : Function.Injective (encode (firstLiveLeg zero)))
    (left right : BlockAddress (fun c ↦ PositiveWord (A c) n))
    (hleft : left ∈ (P.selectEncodedExactInterfaceTerm encode term hmultiplicity).support)
    (hright : right ∈ (P.selectEncodedExactInterfaceTerm encode term hmultiplicity).support)
    (hsecond : left (secondLiveLeg zero) = right (secondLiveLeg zero)) :
    left (firstLiveLeg zero) = right (firstLiveLeg zero) := by
  apply (positiveWordEquiv (A (firstLiveLeg zero)) n).injective
  funext sample
  apply hencodeFirst
  have hleftComplement := congrArg complementSplitWord
    (selectedExactInterfaceTerm_secondLiveChunk_eq_complement_firstLiveChunk
      P encode hlegalSupport term hmultiplicity zero hzero left hleft sample)
  have hrightComplement := congrArg complementSplitWord
    (selectedExactInterfaceTerm_secondLiveChunk_eq_complement_firstLiveChunk
      P encode hlegalSupport term hmultiplicity zero hzero right hright sample)
  rw [hsecond] at hleftComplement
  simpa using hleftComplement.symm.trans hrightComplement

/-- **Generic shared-leg support law, in every orientation.**  On an exact interface term whose
weight at leg `zero` vanishes, the native `zero` positive word is constant and *either* live block
word is injective on the entire selected support.

The committed `selectedExactInterfaceTerm_zeroZ_support_isSharedFiber` is the instance
`zero = .Z`; see `selectedExactInterfaceTerm_zeroZ_support_isSharedFiber'` below. -/
theorem selectedExactInterfaceTerm_zero_support_isSharedFiber
    (P : PartitionedTensor (K := K) (A := A) V)
    (encode : ∀ c, A c → SplitWord depth)
    (hencode : ∀ c, Function.Injective (encode c))
    (hlegalSupport : IsEncodedFineLegalOnSupport P.support encode)
    (term : ExactInterfaceTermParameters depth)
    (hmultiplicity : term.multiplicity = n + 1)
    (zero : Leg) (hzero : term.index.count zero = 0)
    (zeroLabel : A zero) (hzeroLabel : encode zero zeroLabel = 0) :
    (∀ address ∈ (P.selectEncodedExactInterfaceTerm encode term hmultiplicity).support,
        address zero = positiveWordConst zeroLabel n) ∧
      Set.InjOn (fun address ↦ address (firstLiveLeg zero))
        (↑(P.selectEncodedExactInterfaceTerm encode term hmultiplicity).support :
          Set (BlockAddress fun c ↦ PositiveWord (A c) n)) ∧
      Set.InjOn (fun address ↦ address (secondLiveLeg zero))
        (↑(P.selectEncodedExactInterfaceTerm encode term hmultiplicity).support :
          Set (BlockAddress fun c ↦ PositiveWord (A c) n)) := by
  have hconst : ∀ address ∈
      (P.selectEncodedExactInterfaceTerm encode term hmultiplicity).support,
      address zero = positiveWordConst zeroLabel n := fun address haddress ↦
    selectedExactInterfaceTerm_leg_eq_const_of_count_eq_zero
      P encode term hmultiplicity zero hzero zeroLabel hzeroLabel (hencode zero) address haddress
  refine ⟨hconst, ?_, ?_⟩
  · intro left hleft right hright hfirst
    simp only [Finset.mem_coe] at hleft hright
    funext c
    rcases leg_eq_or_eq_firstLiveLeg_or_eq_secondLiveLeg zero c with rfl | rfl | rfl
    · exact (hconst left hleft).trans (hconst right hright).symm
    · exact hfirst
    · exact selectedExactInterfaceTerm_secondLiveLeg_eq_of_firstLiveLeg_eq
        P encode hlegalSupport term hmultiplicity zero hzero (hencode _)
        left right hleft hright hfirst
  · intro left hleft right hright hsecond
    simp only [Finset.mem_coe] at hleft hright
    funext c
    rcases leg_eq_or_eq_firstLiveLeg_or_eq_secondLiveLeg zero c with rfl | rfl | rfl
    · exact (hconst left hleft).trans (hconst right hright).symm
    · exact selectedExactInterfaceTerm_firstLiveLeg_eq_of_secondLiveLeg_eq
        P encode hlegalSupport term hmultiplicity zero hzero (hencode _)
        left right hleft hright hsecond
    · exact hsecond

/-! ## The three orientations, in Lean's `(X, Y, Z)` order

Each specialization names its zero leg in its own name, and lists the two live legs in leg order.
-/

/-- **Zero-`X` shared-leg support law.**  The `X` block is constant, and either of `Y`, `Z`
determines the whole selected address. -/
theorem selectedExactInterfaceTerm_zeroX_support_isSharedFiber
    (P : PartitionedTensor (K := K) (A := A) V)
    (encode : ∀ c, A c → SplitWord depth)
    (hencode : ∀ c, Function.Injective (encode c))
    (hlegalSupport : IsEncodedFineLegalOnSupport P.support encode)
    (term : ExactInterfaceTermParameters depth)
    (hmultiplicity : term.multiplicity = n + 1)
    (hx : term.index.count .X = 0)
    (zeroX : A .X) (hzeroX : encode .X zeroX = 0) :
    (∀ address ∈ (P.selectEncodedExactInterfaceTerm encode term hmultiplicity).support,
        address .X = positiveWordConst zeroX n) ∧
      Set.InjOn (fun address ↦ address .Y)
        (↑(P.selectEncodedExactInterfaceTerm encode term hmultiplicity).support :
          Set (BlockAddress fun c ↦ PositiveWord (A c) n)) ∧
      Set.InjOn (fun address ↦ address .Z)
        (↑(P.selectEncodedExactInterfaceTerm encode term hmultiplicity).support :
          Set (BlockAddress fun c ↦ PositiveWord (A c) n)) :=
  selectedExactInterfaceTerm_zero_support_isSharedFiber
    P encode hencode hlegalSupport term hmultiplicity .X hx zeroX hzeroX

/-- **Zero-`Y` shared-leg support law.**  The `Y` block is constant, and either of `X`, `Z`
determines the whole selected address.  The conjuncts are in leg order; the generic statement
lists them in the cyclic order `(Z, X)`. -/
theorem selectedExactInterfaceTerm_zeroY_support_isSharedFiber
    (P : PartitionedTensor (K := K) (A := A) V)
    (encode : ∀ c, A c → SplitWord depth)
    (hencode : ∀ c, Function.Injective (encode c))
    (hlegalSupport : IsEncodedFineLegalOnSupport P.support encode)
    (term : ExactInterfaceTermParameters depth)
    (hmultiplicity : term.multiplicity = n + 1)
    (hy : term.index.count .Y = 0)
    (zeroY : A .Y) (hzeroY : encode .Y zeroY = 0) :
    (∀ address ∈ (P.selectEncodedExactInterfaceTerm encode term hmultiplicity).support,
        address .Y = positiveWordConst zeroY n) ∧
      Set.InjOn (fun address ↦ address .X)
        (↑(P.selectEncodedExactInterfaceTerm encode term hmultiplicity).support :
          Set (BlockAddress fun c ↦ PositiveWord (A c) n)) ∧
      Set.InjOn (fun address ↦ address .Z)
        (↑(P.selectEncodedExactInterfaceTerm encode term hmultiplicity).support :
          Set (BlockAddress fun c ↦ PositiveWord (A c) n)) := by
  obtain ⟨hconst, hfirst, hsecond⟩ :=
    selectedExactInterfaceTerm_zero_support_isSharedFiber
      P encode hencode hlegalSupport term hmultiplicity .Y hy zeroY hzeroY
  exact ⟨hconst, hsecond, hfirst⟩

/-- **Zero-`Z` shared-leg support law, re-derived.**  This is the committed
`selectedExactInterfaceTerm_zeroZ_support_isSharedFiber` obtained as the instance `zero = .Z` of
the orientation-indexed law, with no separate proof.  The committed theorem is left untouched; the
two are kept apart only so that this module adds nothing to a file it does not own. -/
theorem selectedExactInterfaceTerm_zeroZ_support_isSharedFiber'
    (P : PartitionedTensor (K := K) (A := A) V)
    (encode : ∀ c, A c → SplitWord depth)
    (hencode : ∀ c, Function.Injective (encode c))
    (hlegalSupport : IsEncodedFineLegalOnSupport P.support encode)
    (term : ExactInterfaceTermParameters depth)
    (hmultiplicity : term.multiplicity = n + 1)
    (hz : term.index.count .Z = 0)
    (zeroZ : A .Z) (hzeroZ : encode .Z zeroZ = 0) :
    (∀ address ∈ (P.selectEncodedExactInterfaceTerm encode term hmultiplicity).support,
        address .Z = positiveWordConst zeroZ n) ∧
      Set.InjOn (fun address ↦ address .X)
        (↑(P.selectEncodedExactInterfaceTerm encode term hmultiplicity).support :
          Set (BlockAddress fun c ↦ PositiveWord (A c) n)) ∧
      Set.InjOn (fun address ↦ address .Y)
        (↑(P.selectEncodedExactInterfaceTerm encode term hmultiplicity).support :
          Set (BlockAddress fun c ↦ PositiveWord (A c) n)) :=
  selectedExactInterfaceTerm_zero_support_isSharedFiber
    P encode hencode hlegalSupport term hmultiplicity .Z hz zeroZ hzeroZ

end

end MoreAsymmetryCompatibility
end AlgebraicComplexity
