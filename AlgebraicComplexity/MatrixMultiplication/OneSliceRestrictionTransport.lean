/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.OneSlicePartitionedPower
import AlgebraicComplexity.Tensor.Product

/-!
# Transporting explicit one-slice restrictions along legwise maps and leg permutations

`OneSliceRestriction T d` keeps the three witnessing maps as data, so a client can prove that
several constituents use one common map on a shared leg.  Two transports are missing from the
core module, and both are needed the moment a zero-coordinate family sits on `X` or on `Y`
rather than on `Z`.

## The two transports

* **Along a legwise map.**  If `Tensor.map f T = S` and `S` has an explicit certificate, then so
  does `T`, with `legMap` the composite `S.legMap ∘ₗ f`.  This is `precompose`, and it is the
  reason nothing has to be re-proved in coordinates when a source tensor is only *retyped*.
* **Along a leg permutation.**  A one-slice target `⟨1, d, 1⟩` is **not** preserved by
  `Tensor.permute`: rotating it gives `⟨1, 1, d⟩`, a different matrix shape.  So a certificate
  cannot be pushed forward along a rotation.  What *can* be done — and what a rotated
  zero-coordinate family needs — is to certify the **rotated source** against the *unrotated*
  one-slice target.  That is the content of `permuteExternal` and of the word iteration below:
  the leg permutation is applied to the source and named in every statement, exactly as the
  zero-orientation design convention requires (rotate the source, never the target), while the
  target stays in the canonical `⟨1, d, 1⟩` normal form that every downstream C-tensor client
  expects.

## Why the word iteration is re-run rather than transported

`Tensor.permute_external` says a rotation of an external product is the external product of the
rotations, with *definitionally equal* leg-space families.  So the whole `OneSliceRestriction`
word recursion of `OneSlicePartitionedPower` goes through verbatim in the rotated frame; only
the base certificates change.  `PermutedPositiveSupportWordData` mirrors
`OneSliceRestriction.PositiveSupportWordData` letter for letter, keeping the same essential
feature: only the letters that actually occur in the word need a certificate, because on a
zero-coordinate fibre the remaining Coppersmith--Winograd letters are not one-slice tensors.

This module is reusable semantic infrastructure.  It contains no Coppersmith--Winograd constant,
no certificate datum, no support enumeration and no asymptotic argument.

The only import beyond `OneSlicePartitionedPower` is `Tensor.Product`, for the single committed
law `Tensor.permute_external`.
-/

namespace AlgebraicComplexity

open Tensor

universe u v w

/-- Permuting by the identity of the orientation group is the identity map on tensors.  Stated
for `(1 : Orientation)` rather than `Equiv.refl Leg` because that is the value
`MoreAsymmetryCompatibility.zeroOrientation` takes at the already-canonical zero leg. -/
theorem Tensor.permute_one {K : Type u} [CommSemiring K] {V : Leg → Type v}
    [∀ c, AddCommMonoid (V c)] [∀ c, Module K (V c)] (T : Tensor3 K V) :
    Tensor.permute (K := K) (V := V) (1 : Orientation) T = T := by
  change Tensor.permute (K := K) (V := V) (Equiv.refl Leg) T = T
  rw [Tensor.permute_refl]
  rfl

namespace OneSliceRestriction

/-! ## Transport along a legwise map -/

section Precompose

variable {K : Type u} [CommSemiring K]
variable {V : Leg → Type v} [∀ c, AddCommMonoid (V c)] [∀ c, Module K (V c)]
variable {W : Leg → Type w} [∀ c, AddCommMonoid (W c)] [∀ c, Module K (W c)]
variable {T : Tensor3 K V} {S : Tensor3 K W} {d : ℕ}

/-- **Transport along a legwise map.**  If the legwise map `f` carries `T` onto a tensor that has
an explicit one-slice certificate, then `T` has one too, with the maps composed.

Keeping this as a definition rather than an existential is the whole point of
`OneSliceRestriction`: a client that later needs the shared-leg coherence
`external_legMap_Z_congr` can still read off the `Z` map of the transported certificate. -/
noncomputable def precompose (C : OneSliceRestriction S d) (f : ∀ c, V c →ₗ[K] W c)
    (h : Tensor.map f T = S) : OneSliceRestriction T d where
  legMap := fun c ↦ C.legMap c ∘ₗ f c
  map_eq := by
    have hcomp : Tensor.map (fun c ↦ C.legMap c ∘ₗ f c) T =
        Tensor.map C.legMap (Tensor.map f T) := by
      rw [Tensor.map_comp]
      rfl
    rw [hcomp, h, C.map_eq]

@[simp] theorem precompose_legMap (C : OneSliceRestriction S d) (f : ∀ c, V c →ₗ[K] W c)
    (h : Tensor.map f T = S) (c : Leg) :
    (C.precompose f h).legMap c = C.legMap c ∘ₗ f c :=
  rfl

/-- Transport a certificate along an equality of its source tensor. -/
def congrTensor {T' : Tensor3 K V} (C : OneSliceRestriction T d) (h : T = T') :
    OneSliceRestriction T' d := by
  subst h
  exact C

@[simp] theorem congrTensor_rfl (C : OneSliceRestriction T d) :
    C.congrTensor rfl = C :=
  rfl

/-- A certificate in the identity rotation is the certificate itself.  This is the degenerate
instance that lets a leg-indexed statement cover the already-canonical orientation without a
separate proof. -/
noncomputable def ofPermuteOne (C : OneSliceRestriction T d) :
    OneSliceRestriction (Tensor.permute (K := K) (V := V) (1 : Orientation) T) d :=
  C.congrTensor (Tensor.permute_one T).symm

end Precompose

/-! ## The rotated frame -/

section Permuted

variable {K : Type u} [CommSemiring K]
variable {V : Leg → Type v} [∀ c, AddCommMonoid (V c)] [∀ c, Module K (V c)]
variable {W : Leg → Type w} [∀ c, AddCommMonoid (W c)] [∀ c, Module K (W c)]

/-- **The external product in a rotated frame.**  Two certificates for rotated factors compose
into one certificate for the rotated product, because `Tensor.permute` distributes over
`Tensor.external` with definitionally equal leg spaces.

The middle dimensions multiply exactly as in the unrotated `external`; the rotation is carried
only by the source. -/
noncomputable def permuteExternal (e : Orientation) {T : Tensor3 K V} {S : Tensor3 K W}
    {d f : ℕ} (left : OneSliceRestriction (Tensor.permute e T) d)
    (right : OneSliceRestriction (Tensor.permute e S) f) :
    OneSliceRestriction (Tensor.permute e (Tensor.external T S)) (d * f) :=
  (left.external right).congrTensor (Tensor.permute_external e T S).symm

end Permuted

/-! ## Word iteration in a rotated frame -/

section Word

variable {K : Type u} [CommSemiring K]
variable {A : Leg → Type w} [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]
variable {V : ∀ c, A c → Type (max u v)}
variable [∀ c a, AddCommMonoid (V c a)] [∀ c a, Module K (V c a)]

/-- Letterwise certificates for the **rotated** constituents occurring in one supported word.

This mirrors `OneSliceRestriction.PositiveSupportWordData` exactly, with `Tensor.permute e`
applied to every source constituent.  As there, the dependent record lets a client certify only
the letters that actually occur: on a zero-coordinate fibre the other Coppersmith--Winograd
letters are not one-slice tensors in any frame. -/
def PermutedPositiveSupportWordData
    (P : PartitionedTensor (K := K) (A := A) V)
    (dimension : P.support → ℕ) (e : Orientation) :
    (r : ℕ) → (word : PositiveWord P.support r) → Type (max u v)
  | 0, word => OneSliceRestriction (Tensor.permute e (P.constituent word.1)) (dimension word)
  | r + 1, word =>
      PermutedPositiveSupportWordData P dimension e r word.1 ×
        OneSliceRestriction (Tensor.permute e (P.constituent word.2.1)) (dimension word.2)

/-- Assemble rotated letterwise certificates into one certificate for the rotated external
product constituent.  The target dimension is the same `positiveWordProduct` as in the unrotated
iteration. -/
noncomputable def ofPermutedPositiveSupportWordData
    (P : PartitionedTensor (K := K) (A := A) V)
    (dimension : P.support → ℕ) (e : Orientation) :
    (r : ℕ) → (word : PositiveWord P.support r) →
      PermutedPositiveSupportWordData P dimension e r word →
      OneSliceRestriction (Tensor.permute e (P.positiveSupportWordTensor r word))
        (positiveWordProduct dimension r word)
  | 0, _word, data => data
  | r + 1, word, data =>
      permuteExternal e
        (ofPermutedPositiveSupportWordData P dimension e r word.1 data.1) data.2

/-- Constituent form of `ofPermutedPositiveSupportWordData`: the source is the rotation of the
block of the canonical partitioned positive power sitting at the word's address. -/
noncomputable def ofPermutedPositivePowerConstituentData
    (P : PartitionedTensor (K := K) (A := A) V)
    (dimension : P.support → ℕ) (e : Orientation)
    (r : ℕ) (word : PositiveWord P.support r)
    (data : PermutedPositiveSupportWordData P dimension e r word) :
    OneSliceRestriction
      (Tensor.permute e
        ((P.positivePower r).constituent
          (positiveSupportWordBlockAddress P.support r word)))
      (positiveWordProduct dimension r word) := by
  rw [P.positivePower_constituent_positiveSupportWordBlockAddress r word]
  exact ofPermutedPositiveSupportWordData P dimension e r word data

/-- Iterate rotated constituent certificates along a supported word, when *every* supported letter
carries one.  This is the rotated analogue of `OneSliceRestriction.positiveSupportWord`. -/
noncomputable def permutedPositiveSupportWord
    (P : PartitionedTensor (K := K) (A := A) V)
    (dimension : P.support → ℕ) (e : Orientation)
    (base : ∀ support : P.support,
      OneSliceRestriction (Tensor.permute e (P.constituent support.1)) (dimension support)) :
    (r : ℕ) → (word : PositiveWord P.support r) →
      OneSliceRestriction (Tensor.permute e (P.positiveSupportWordTensor r word))
        (positiveWordProduct dimension r word)
  | 0, word => base word
  | r + 1, word =>
      permuteExternal e (permutedPositiveSupportWord P dimension e base r word.1)
        (base word.2)

@[simp] theorem permutedPositiveSupportWord_zero
    (P : PartitionedTensor (K := K) (A := A) V)
    (dimension : P.support → ℕ) (e : Orientation)
    (base : ∀ support : P.support,
      OneSliceRestriction (Tensor.permute e (P.constituent support.1)) (dimension support))
    (word : PositiveWord P.support 0) :
    permutedPositiveSupportWord P dimension e base 0 word = base word :=
  rfl

@[simp] theorem permutedPositiveSupportWord_succ
    (P : PartitionedTensor (K := K) (A := A) V)
    (dimension : P.support → ℕ) (e : Orientation)
    (base : ∀ support : P.support,
      OneSliceRestriction (Tensor.permute e (P.constituent support.1)) (dimension support))
    (r : ℕ) (word : PositiveWord P.support (r + 1)) :
    permutedPositiveSupportWord P dimension e base (r + 1) word =
      permuteExternal e (permutedPositiveSupportWord P dimension e base r word.1)
        (base word.2) :=
  rfl

end Word

end OneSliceRestriction

end AlgebraicComplexity
