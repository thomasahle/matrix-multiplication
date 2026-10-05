/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.SixSymmetrizedValue
import AlgebraicComplexity.Tensor.PartitionedPermutation
import AlgebraicComplexity.Tensor.PartitionedPower
import AlgebraicComplexity.Tensor.PartitionedProductRealization

set_option autoImplicit false

/-!
# `sym₃` and `sym₆` of a partitioned tensor

Layer 3 (`AlgebraicComplexity/MatrixMultiplication/`).
`MatrixMultiplication/SixSymmetrizedValue.lean` defines
the three- and six-orientation symmetrizations

`sym₃(T) = T ⊗ T^c ⊗ T^{c²}` and `sym₆(T) = sym₃(T) ⊗ sym₃(T)^s`

as iterated `Tensor.external`s of leg permutations.  Every laser-method tool in this repository ---
marked two-leg hashing, the compatibility zero-outs, the batched Hole Lemma --- instead consumes a
`PartitionedTensor`, i.e. a finite typed block decomposition.  Until now there was no way to view
`sym₆` of a partitioned realization as a partitioned tensor, so none of that machinery could be
pointed at `sym₆` at all.

This module supplies the missing structure.  `PartitionedTensor.permute` transports a partition
certificate through a leg permutation --- and `permute_realize` is an *equality*, not merely an
isomorphism --- while `PartitionedTensor.external` multiplies two certificates.  Composing them in
the association of `symSix_eq_sixOrientationProduct` gives `symSixPartition`, whose block labels
are the six-tuples of source labels, one per element of `Perm Leg`.

## Principal results

* `symThreePartition`, `swapSymThreePartition`, `symSixPartition` --- the certificates;
* `isomorphic_symSixPartition` --- `sym₆` of the realization *is* the realization of the
  certificate.  This is an isomorphism, so no information is lost in either direction;
* `card_symSixPartition_support` --- the certificate has exactly `P.support.card ^ 6` blocks, so
  the construction collapses nothing;
* `restricts_power_symSixPartition` --- the stage bridge
  `Restricts (Tensor.power (sym₆ P.realize) (n+1)) ((symSixPartition P).positivePower n).realize`,
  which carries **no hypothesis at all** and therefore cannot be vacuous;
* `restricts_power_symSix_of_partitionedStage` --- its client form: any restriction of the
  six-orientation positive power onto a constant family of leaves is a restriction of the `sym₆`
  power onto that family.

## Why this is the object an asymmetric laser argument needs

A single joint hash over all six orientations is expressible only if the six orientations live in
one block-label family.  Hashing them separately and multiplying the six stages is also possible
--- `Isomorphic.external_indexedDirectSum` distributes a constant direct sum through `external`
--- but it pays the *product of six* per-orientation moduli, whereas a joint hash pays one
maximum, and product-of-maxima exceeds maximum-of-products exactly when different orientations
select different branches.  That is the situation an asymmetric distribution creates, and it is
the whole source of the gain in `[DuanWuZhou2022]`.

## Non-goals

Nothing here mentions a distribution, a hashing seed, a compatibility predicate, a numerical
parameter, or any named tensor.  Clients supplying those live in
`AlgebraicComplexity/Examples/`.
-/

namespace AlgebraicComplexity.Tensor

universe u v w

namespace PartitionedTensor

section Symmetrization

variable {K : Type u} [CommSemiring K]
variable {A : Leg → Type w} [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]
variable {V : ∀ c, A c → Type (max u v)}
variable [∀ c a, AddCommMonoid (V c a)] [∀ c a, Module K (V c a)]

/-- **The three-orientation partitioned product** `T ⊗ T^c ⊗ T^{c²}`, as a partition certificate.
Its block labels are the triples of source labels, one per orientation. -/
noncomputable def symThreePartition (P : PartitionedTensor (K := K) (A := A) V) :=
  (P.external (P.permute cycle)).external (P.permute cycle.symm)

/-- **The swapped three-orientation partitioned product** `T^s ⊗ T^{cs} ⊗ T^{c²s}`. -/
noncomputable def swapSymThreePartition (P : PartitionedTensor (K := K) (A := A) V) :=
  ((P.permute swapXY).external (P.permute (cycle.trans swapXY))).external
    (P.permute (cycle.symm.trans swapXY))

/-- **The six-orientation partitioned product**, a partition certificate for `sym₆` of the
realization.  The association matches `symSix_eq_sixOrientationProduct` exactly. -/
noncomputable def symSixPartition (P : PartitionedTensor (K := K) (A := A) V) :=
  P.symThreePartition.external P.swapSymThreePartition

/-- **The six-orientation partition has the sixth power of the source's block count.**  Nothing
is collapsed by the construction: the block labels really are the six-tuples of source labels, one
per leg permutation.  This is the non-vacuity witness for `symSixPartition`. -/
@[simp] theorem card_symSixPartition_support (P : PartitionedTensor (K := K) (A := A) V) :
    P.symSixPartition.support.card = P.support.card ^ 6 := by
  simp only [symSixPartition, symThreePartition, swapSymThreePartition,
    PartitionedTensor.card_external_support, PartitionedTensor.permute_support,
    Finset.card_map]
  ring

/-- The partitioned three-orientation product realizes `sym₃` of the realization.

Proof sketch: `PartitionedTensor.permute_realize` is an equality, so the two permuted factors of
`sym₃` are literally the realizations of the permuted certificates; two applications of
`Isomorphic.partitionedExternal` then assemble the left-associated product. -/
theorem isomorphic_symThreePartition (P : PartitionedTensor (K := K) (A := A) V) :
    Isomorphic (symThree K P.realize) P.symThreePartition.realize := by
  show Isomorphic
    (Tensor.external (Tensor.external P.realize (Tensor.permute cycle P.realize))
      (Tensor.permute cycle.symm P.realize)) _
  rw [← P.permute_realize cycle, ← P.permute_realize cycle.symm]
  exact ((Isomorphic.partitionedExternal P (P.permute cycle)).external
      (Isomorphic.refl _)).trans
    (Isomorphic.partitionedExternal (P.external (P.permute cycle)) (P.permute cycle.symm))

/-- The swapped partitioned three-orientation product realizes the corresponding product of the
three swapped leg permutations. -/
theorem isomorphic_swapSymThreePartition (P : PartitionedTensor (K := K) (A := A) V) :
    Isomorphic
      (Tensor.external
        (Tensor.external (Tensor.permute swapXY P.realize)
          (Tensor.permute (cycle.trans swapXY) P.realize))
        (Tensor.permute (cycle.symm.trans swapXY) P.realize))
      P.swapSymThreePartition.realize := by
  rw [← P.permute_realize swapXY, ← P.permute_realize (cycle.trans swapXY),
    ← P.permute_realize (cycle.symm.trans swapXY)]
  exact ((Isomorphic.partitionedExternal (P.permute swapXY)
      (P.permute (cycle.trans swapXY))).external (Isomorphic.refl _)).trans
    (Isomorphic.partitionedExternal
      ((P.permute swapXY).external (P.permute (cycle.trans swapXY)))
      (P.permute (cycle.symm.trans swapXY)))

/-- **`sym₆` of a partitioned realization is the realization of a partition certificate.**

This is the structural fact `[DuanWuZhou2022]` section 6 needs and that the repository did not
have: every laser-method tool -- marked two-leg hashing, compatibility cleanup, the Hole Lemma --
consumes a `PartitionedTensor`, and until now `sym₆` of one was only an iterated
`Tensor.external`. -/
theorem isomorphic_symSixPartition (P : PartitionedTensor (K := K) (A := A) V) :
    Isomorphic (symSix K P.realize) P.symSixPartition.realize := by
  rw [symSix_eq_sixOrientationProduct]
  exact ((isomorphic_symThreePartition P).external
      (isomorphic_swapSymThreePartition P)).trans
    (Isomorphic.partitionedExternal P.symThreePartition P.swapSymThreePartition)

/-- **The `sym₆` stage bridge.**  A positive power of `sym₆` of a partitioned realization restricts
onto the realization of the positive power of its six-orientation partition certificate.

Everything downstream of this line -- hashing, the two compatibility zero-outs, batching and hole
repair -- is the existing generic pipeline, applied to a single `PartitionedTensor` whose block
labels already record all six orientations.  That is what makes the *joint* hash of
`[DuanWuZhou2022]` section 6 expressible. -/
theorem restricts_power_symSixPartition
    (P : PartitionedTensor (K := K) (A := A) V) (n : ℕ) :
    Restricts (Tensor.power (symSix K P.realize) (n + 1))
      (P.symSixPartition.positivePower n).realize :=
  ((isomorphic_symSixPartition P).power (n + 1)).restricts.trans
    (Restricts.power_partitionedPositivePower P.symSixPartition n)

/-- **The transport half of `[DuanWuZhou2022]`'s `hstage`, discharged.**

Given any restriction of the partitioned `sym₆` power onto a constant family of leaves, the
`sym₆` power itself restricts onto that family.  This is the exact shape
`AsymmetricGlobal.omega_lt_three_mul_of_repairedStage` and
`Examples.exists_value_of_repairedStage_true` consume. -/
theorem restricts_power_symSix_of_partitionedStage
    (P : PartitionedTensor (K := K) (A := A) V) (n : ℕ)
    {W : Leg → Type _} [∀ c, AddCommMonoid (W c)] [∀ c, Module K (W c)]
    {leaf : Tensor3 K W} {β : Type _} [Fintype β] [DecidableEq β]
    (hstage : Restricts (P.symSixPartition.positivePower n).realize
      (Tensor.indexedDirectSum (V := fun _ : β ↦ W) fun _ ↦ leaf)) :
    Restricts (Tensor.power (symSix K P.realize) (n + 1))
      (Tensor.indexedDirectSum (V := fun _ : β ↦ W) fun _ ↦ leaf) :=
  (restricts_power_symSixPartition P n).trans hstage

end Symmetrization

end PartitionedTensor

end AlgebraicComplexity.Tensor
