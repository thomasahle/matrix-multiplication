/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.OneSliceRestrictionTransport
import AlgebraicComplexity.Tensor.IteratedProduct

/-!
# Coherent one-slice word certificates in a rotated frame

`CTensor.SharedOneSliceFiberData` fuses a whole selected family of constituents into one
matrix-multiplication tensor, but only if every constituent certificate uses **one common map** on
the block they share.  On a zero-coordinate fibre that shared block is the zero block, and the
certificates are built by iterating letterwise certificates along a supported word.  So the
coherence has to survive the iteration, and — when the zero coordinate sits on `X` or on `Y` — it
has to survive it in the rotated frame of `OneSliceRestrictionTransport`.

This module supplies both halves generically.

## The shared map of a word

`constWordZMap zero zMap r` is the canonical shared map of a **constant** word of blocks: the
`r`-fold one-slice coordinate product of the letter map `zMap` with itself.  It is the only map a
supported word on a shared fibre can carry, because `OneSliceRestriction.external` computes the
product `Z` map from the two factors' `Z` maps and from nothing else
(`OneSliceRestriction.external_legMap_Z`).

## The iteration

`permutedCoherentWord` is the rotated word recursion of `OneSliceRestrictionTransport` carrying its
coherence: from letterwise certificates that all use `zMap` on the shared block, it returns a
certificate for the rotated word tensor that uses `constWordZMap zero zMap r`.  The returned datum
is a subtype rather than a structure so it plugs straight into the shape the committed zero-`Z`
instantiation already uses.

Like the underlying recursion it only asks for certificates of the letters that **occur** with a
shared block on `zero`; on a zero-coordinate fibre the remaining letters are not one-slice tensors
in any frame.

## Why the dependent bookkeeping is three lemmas rather than one `congr`

The two maps compared by the coherence live over *different block labels* — the word's own
transposed label and the constant one — so their domains are different types and the comparison is
a `HEq`.  Splitting that `HEq` with `congr` leaves the block space, its `AddCommMonoid` and its
`Module` instance as separate dependent side goals.  `coordinateProductMapAfter_heq` does the whole
step once by substituting the two label equalities, which is available precisely because the labels
are *variables* of a generic lemma.  The three uses of the `congr` pattern in the committed
zero-`Z` chain are instances of it.

This module is reusable semantic infrastructure: no Coppersmith--Winograd constant, no certificate
datum, no support enumeration, no asymptotics.
-/

namespace AlgebraicComplexity

open Tensor

universe u v w

namespace OneSliceProduct

/-- **Dependent congruence for the one-slice coordinate product.**  Two coordinate product maps
whose factors are heterogeneously equal — over *equal* block labels in two dependent families —
are heterogeneously equal.

This is the dependent bookkeeping that a shared-leg word recursion needs at every step, done once.
Both label equalities are substituted, so no instance-level side goal survives. -/
theorem coordinateProductMapAfter_heq {K : Type u} [CommSemiring K]
    {I J L : Type*} (equiv : I × J ≃ L)
    {ι : Type*} {M : ι → Type v} [∀ i, AddCommMonoid (M i)] [∀ i, Module K (M i)]
    {κ : Type*} {N : κ → Type w} [∀ j, AddCommMonoid (N j)] [∀ j, Module K (N j)]
    {a a' : ι} (ha : a = a') {b b' : κ} (hb : b = b')
    {left : M a →ₗ[K] (I → K)} {left' : M a' →ₗ[K] (I → K)} (hleft : HEq left left')
    {right : N b →ₗ[K] (J → K)} {right' : N b' →ₗ[K] (J → K)} (hright : HEq right right') :
    HEq (coordinateProductMapAfter (K := K) equiv left right)
      (coordinateProductMapAfter (K := K) equiv left' right') := by
  subst ha
  subst hb
  rw [eq_of_heq hleft, eq_of_heq hright]

end OneSliceProduct

namespace OneSliceRestriction

/-! ## Reading the maps of a transported certificate -/

section Legwise

variable {K : Type u} [CommSemiring K]
variable {V : Leg → Type v} [∀ c, AddCommMonoid (V c)] [∀ c, Module K (V c)]
variable {W : Leg → Type w} [∀ c, AddCommMonoid (W c)] [∀ c, Module K (W c)]
variable {T : Tensor3 K V} {d : ℕ}

/-- Transporting a certificate along an equality of its source tensor leaves its three maps
untouched.  The maps do not mention the source, so this is the statement that
`congrTensor` really is a retyping and not a change of witness. -/
@[simp] theorem congrTensor_legMap {T' : Tensor3 K V} (C : OneSliceRestriction T d)
    (h : T = T') (c : Leg) :
    (C.congrTensor h).legMap c = C.legMap c := by
  subst h
  rfl

/-- The maps of a rotated external product are the maps of the unrotated one: the rotation is
carried entirely by the source. -/
@[simp] theorem permuteExternal_legMap (e : Orientation) {S : Tensor3 K W} {f : ℕ}
    (left : OneSliceRestriction (Tensor.permute e T) d)
    (right : OneSliceRestriction (Tensor.permute e S) f) (c : Leg) :
    (permuteExternal e left right).legMap c = (left.external right).legMap c :=
  congrTensor_legMap _ _ c

/-- **The shared map of a rotated product.**  It is the one-slice coordinate product of the two
factors' shared maps, and — as in the unrotated case — it does not depend on the two middle
dimensions. -/
theorem permuteExternal_legMap_Z (e : Orientation) {S : Tensor3 K W} {f : ℕ}
    (left : OneSliceRestriction (Tensor.permute e T) d)
    (right : OneSliceRestriction (Tensor.permute e S) f) :
    (permuteExternal e left right).legMap .Z =
      OneSliceProduct.coordinateProductMapAfter
        (OneSliceProduct.indexProductEquiv 1 1 .Z)
        (left.legMap .Z) (right.legMap .Z) := by
  rw [permuteExternal_legMap]
  rfl

end Legwise

/-! ## The canonical shared map of a constant word -/

section Word

variable {K : Type u} [CommSemiring K]
variable {A : Leg → Type w} [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]
variable {V : ∀ c, A c → Type (max u v)}
variable [∀ c a, AddCommMonoid (V c a)] [∀ c a, Module K (V c a)]

/-- The shared map carried by a word all of whose letters carry the block `zLabel` on leg `zero`:
the iterated one-slice coordinate product of the letter map with itself.

The committed zero-`Z` canonical maps of the Coppersmith--Winograd chain are the instances
`zero = .Z` of this definition at the base and at the chunk letter. -/
def constWordZMap (zero : Leg) {zLabel : A zero}
    (zMap : V zero zLabel →ₗ[K] MMSpace K 1 1 1 .Z) :
    (r : ℕ) →
      PositivePowerBlockSpace K V r zero (positiveWordConst zLabel r) →ₗ[K]
        MMSpace K 1 1 1 .Z
  | 0 => zMap
  | r + 1 => OneSliceProduct.coordinateProductMapAfter
      (OneSliceProduct.indexProductEquiv 1 1 .Z)
      (constWordZMap zero zMap r) zMap

omit [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)] in
@[simp] theorem constWordZMap_zero (zero : Leg) {zLabel : A zero}
    (zMap : V zero zLabel →ₗ[K] MMSpace K 1 1 1 .Z) :
    constWordZMap (V := V) zero zMap 0 = zMap := rfl

omit [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)] in
@[simp] theorem constWordZMap_succ (zero : Leg) {zLabel : A zero}
    (zMap : V zero zLabel →ₗ[K] MMSpace K 1 1 1 .Z) (r : ℕ) :
    constWordZMap (V := V) zero zMap (r + 1) =
      OneSliceProduct.coordinateProductMapAfter
        (OneSliceProduct.indexProductEquiv 1 1 .Z)
        (constWordZMap (V := V) zero zMap r) zMap := rfl

/-! ## The coherent rotated word recursion -/

/-- **Letterwise coherent certificates iterate to a coherent word certificate, in a rotated
frame.**

Every letter of the supported word carries the block `zLabel` on the leg `e.symm .Z` that the
rotation `e` puts on `Z`, and its rotated certificate uses `zMap` there.  The resulting certificate
for the rotated word tensor then uses `constWordZMap (e.symm .Z) zMap r`, so a whole family of
words on the shared fibre uses **one** map on the shared block — which is exactly the hypothesis
`CTensor.SharedOneSliceFiberData` takes.

At `e = 1` this is the unrotated statement; the committed zero-`Z` Coppersmith--Winograd chain runs
this recursion twice, at the base letter and at the chunk letter. -/
noncomputable def permutedCoherentWord
    (P : PartitionedTensor (K := K) (A := A) V)
    (dimension : P.support → ℕ) (e : Orientation)
    {zLabel : A (e.symm .Z)}
    (zMap : V (e.symm .Z) zLabel →ₗ[K] MMSpace K 1 1 1 .Z)
    (base : ∀ support : P.support, support.1 (e.symm .Z) = zLabel →
      { C : OneSliceRestriction (Tensor.permute e (P.constituent support.1))
          (dimension support) // HEq (C.legMap .Z) zMap }) :
    (r : ℕ) → (word : PositiveWord P.support r) →
      positiveSupportWordBlockAddress P.support r word (e.symm .Z) =
        positiveWordConst zLabel r →
      { C : OneSliceRestriction (Tensor.permute e (P.positiveSupportWordTensor r word))
          (positiveWordProduct dimension r word) //
        HEq (C.legMap .Z) (constWordZMap (V := V) (e.symm .Z) zMap r) }
  | 0, word, hzero => base word hzero
  | r + 1, word, hzero => by
      have hleft : positiveSupportWordBlockAddress P.support r word.1 (e.symm .Z) =
          positiveWordConst zLabel r := congrArg Prod.fst hzero
      have hright : word.2.1 (e.symm .Z) = zLabel := congrArg Prod.snd hzero
      refine ⟨permuteExternal e
        (permutedCoherentWord P dimension e zMap base r word.1 hleft).1
        (base word.2 hright).1, ?_⟩
      refine HEq.trans (heq_of_eq (permuteExternal_legMap_Z e _ _)) ?_
      exact OneSliceProduct.coordinateProductMapAfter_heq _ hleft hright
        (permutedCoherentWord P dimension e zMap base r word.1 hleft).2
        (base word.2 hright).2

/-- Constituent form of `permutedCoherentWord`: the source is the rotation of the block of the
canonical partitioned positive power sitting at the word's transposed address. -/
noncomputable def permutedCoherentPositivePowerConstituent
    (P : PartitionedTensor (K := K) (A := A) V)
    (dimension : P.support → ℕ) (e : Orientation)
    {zLabel : A (e.symm .Z)}
    (zMap : V (e.symm .Z) zLabel →ₗ[K] MMSpace K 1 1 1 .Z)
    (base : ∀ support : P.support, support.1 (e.symm .Z) = zLabel →
      { C : OneSliceRestriction (Tensor.permute e (P.constituent support.1))
          (dimension support) // HEq (C.legMap .Z) zMap })
    (r : ℕ) (word : PositiveWord P.support r)
    (hzero : positiveSupportWordBlockAddress P.support r word (e.symm .Z) =
      positiveWordConst zLabel r) :
    { C : OneSliceRestriction
        (Tensor.permute e
          ((P.positivePower r).constituent
            (positiveSupportWordBlockAddress P.support r word)))
        (positiveWordProduct dimension r word) //
      HEq (C.legMap .Z) (constWordZMap (V := V) (e.symm .Z) zMap r) } := by
  rw [P.positivePower_constituent_positiveSupportWordBlockAddress r word]
  exact permutedCoherentWord P dimension e zMap base r word hzero

end Word

end OneSliceRestriction

end AlgebraicComplexity
