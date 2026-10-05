/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Tensor.LocalizedCoarsenedSelection

set_option autoImplicit false

/-!
# Whole coarsening fibers of positive partitioned powers

This layer-1 module identifies a complete coarsening fiber in a positive partitioned power with
the heterogeneous external product of the corresponding one-letter fibers.  The intermediate
partition identity is literal; after realization, distributivity of tensor products over finite
direct sums supplies a canonical tensor isomorphism.

This is the product/fiber step used when Coppersmith and Winograd retain all exceptional
`(1,1,2)` summands sharing a grouped variable [CoppersmithWinograd1990, pp. 270--272], transcribed
in `papers/notes/MMult1987.tex:174-285`.  It is also the complete-fiber clause of Theorem
`thm:exact-nested-total-weight-leaf` in `better_bound/paper.tex:1684-1718`.  The theorem deliberately
preserves every fine address in the fiber: no representative choice, hashing, entropy estimate,
or paper-specific alphabet appears here.

## Reference

- [CoppersmithWinograd1990] Don Coppersmith and Shmuel Winograd, *Matrix Multiplication via
  Arithmetic Progressions*.
-/

namespace AlgebraicComplexity.Tensor

universe u v w x y z t

variable {K : Type u} [CommSemiring K]
variable {A : Leg → Type w} {B : Leg → Type x}
variable {C : Leg → Type y} {D : Leg → Type z}
variable [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]
variable [∀ c, Fintype (B c)] [∀ c, DecidableEq (B c)]
variable [∀ c, Fintype (C c)] [∀ c, DecidableEq (C c)]
variable [∀ c, Fintype (D c)] [∀ c, DecidableEq (D c)]
variable {V : ∀ c, A c → Type (max u v)}
variable {W : ∀ c, C c → Type (max u t)}
variable [∀ c a, AddCommMonoid (V c a)] [∀ c a, Module K (V c a)]
variable [∀ c a, AddCommMonoid (W c a)] [∀ c a, Module K (W c a)]

namespace PartitionedTensor

/-- The whole fiber of an external product is the external product of the two whole fibers.

In human-readable terms, fixing a coarse pair `(b,d)` retains exactly the pairs of fine addresses
whose left image is `b` and whose right image is `d`.

Proof sketch: the existing support theorem identifies the filtered support with the Cartesian
product of the separately filtered supports.  Constituents on the two sides are definitionally
the same external products. -/
theorem coarseningFiber_external
    (P : PartitionedTensor (K := K) (A := A) V)
    (Q : PartitionedTensor (K := K) (A := C) W)
    (f : ∀ c, A c → B c) (g : ∀ c, C c → D c)
    (target : BlockAddress (ProductBlockIndex B D)) :
    PartitionedTensor.coarseningFiber.{u, max v t, max w y, max x z}
        (P.external Q) (productCoarseningMap f g) target =
      PartitionedTensor.external.{u, max u v, w, y, max u t}
        (PartitionedTensor.coarseningFiber.{u, v, w, x}
          P f (fun c ↦ (target c).1))
        (PartitionedTensor.coarseningFiber.{u, t, y, z}
          Q g (fun c ↦ (target c).2)) := by
  apply PartitionedTensor.ext.{u, max (max u v) t, max w y}
    (K := K) (A := ProductBlockIndex A C) (V := ProductBlockSpace K V W)
  · exact P.external_support_filter_productCoarseningMap_eq Q f g target
  · rfl

end PartitionedTensor

namespace Isomorphic

/-- A complete coarsening fiber selected by a coarse joint-address word is canonically the
positive-word tensor of its complete one-letter fibers.

In human-readable terms, first taking a positive power and then retaining every fine word over a
fixed coarse word gives the same tensor, up to canonical distributivity isomorphisms, as tensoring
the full one-letter fiber chosen at each position of that word.

Proof sketch: induct on the nonempty word.  The one-letter case is reflexivity.  At a successor,
`PartitionedTensor.coarseningFiber_external` splits the fiber into the prefix fiber and final
one-letter fiber.  The realization of that partitioned external product is canonically isomorphic
to the external product of the realizations; combine this with the induction hypothesis. -/
theorem positivePower_coarseningFiber_positiveWordTensor_of_word
    (P : PartitionedTensor (K := K) (A := A) V)
    (f : ∀ c, A c → B c) (n : ℕ)
    (word : PositiveWord (BlockAddress B) n) :
    Isomorphic
      (((P.positivePower n).coarseningFiber
        (fun c ↦ positiveWordMap (f c) n)
        (positiveWordBlockAddressEquiv B n word)).realize)
      (positiveWordTensor
        (fun _target : BlockAddress B ↦
          LegModuleFamily.of.{u, max v w} (K := K) (PartitionedSpace K V))
        (fun target ↦ (P.coarseningFiber f target).realize)
        n word) := by
  induction n with
  | zero =>
      change Isomorphic ((P.coarseningFiber f word).realize)
        ((P.coarseningFiber f word).realize)
      exact Isomorphic.refl _
  | succ n ih =>
      rcases word with ⟨wordPrefix, last⟩
      let prefixFiber := (P.positivePower n).coarseningFiber
        (fun c ↦ positiveWordMap (f c) n)
        (positiveWordBlockAddressEquiv B n wordPrefix)
      let lastFiber := P.coarseningFiber f last
      have hsplit :
          (P.positivePower (n + 1)).coarseningFiber
              (fun c ↦ positiveWordMap (f c) (n + 1))
              (positiveWordBlockAddressEquiv B (n + 1) (wordPrefix, last)) =
            prefixFiber.external lastFiber := by
        change ((P.positivePower n).external P).coarseningFiber
            (productCoarseningMap (fun c ↦ positiveWordMap (f c) n) f)
            (fun c ↦ (positiveWordBlockAddressEquiv B n wordPrefix c, last c)) = _
        simpa only [prefixFiber, lastFiber] using
          PartitionedTensor.coarseningFiber_external
            (P := P.positivePower n) (Q := P)
            (f := fun c ↦ positiveWordMap (f c) n) (g := f)
            (target := fun c ↦
              (positiveWordBlockAddressEquiv B n wordPrefix c, last c))
      rw [hsplit]
      change Isomorphic
        (prefixFiber.external lastFiber).realize
        (Tensor.external
          (positiveWordTensor
            (fun _target : BlockAddress B ↦
              LegModuleFamily.of.{u, max v w} (K := K) (PartitionedSpace K V))
            (fun target ↦ (P.coarseningFiber f target).realize)
            n wordPrefix)
          lastFiber.realize)
      exact (Isomorphic.partitionedExternal prefixFiber lastFiber).symm.trans
        (Isomorphic.external (ih wordPrefix) (Isomorphic.refl lastFiber.realize))

/-- Arbitrary-address form of
`Isomorphic.positivePower_coarseningFiber_positiveWordTensor_of_word`.

In human-readable terms, a triple of coarse leg words determines a unique word of coarse joint
addresses.  The whole fine fiber over the triple is the positive-word tensor of the one-letter
fibers selected by that joint-address word.

Proof sketch: transpose the three leg words back to their joint-address word with
`positiveWordBlockAddressEquiv`, then apply the preceding theorem. -/
theorem positivePower_coarseningFiber_positiveWordTensor
    (P : PartitionedTensor (K := K) (A := A) V)
    (f : ∀ c, A c → B c) (n : ℕ)
    (target : BlockAddress (fun c ↦ PositiveWord (B c) n)) :
    Isomorphic
      (((P.positivePower n).coarseningFiber
        (fun c ↦ positiveWordMap (f c) n) target).realize)
      (positiveWordTensor
        (fun _target : BlockAddress B ↦
          LegModuleFamily.of.{u, max v w} (K := K) (PartitionedSpace K V))
        (fun address ↦ (P.coarseningFiber f address).realize)
        n ((positiveWordBlockAddressEquiv B n).symm target)) := by
  simpa only [Equiv.apply_symm_apply] using
    positivePower_coarseningFiber_positiveWordTensor_of_word
      P f n ((positiveWordBlockAddressEquiv B n).symm target)

end Isomorphic

end AlgebraicComplexity.Tensor
