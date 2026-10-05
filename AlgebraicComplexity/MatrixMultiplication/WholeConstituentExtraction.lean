/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.WholeConstituentLaserVolume
import AlgebraicComplexity.Tensor.CompatibilityZeroing
import AlgebraicComplexity.Tensor.PartitionedPower

/-!
# Deriving whole-constituent stages from compatibility cleanup

`MatrixMultiplication/WholeConstituentLaserVolume.lean` stores the semantic content of a
no-hole cleanup in the field `WholeConstituentLaserVolumeStage.source_restricts`.  Populating
that field with an *assumed* restriction from the assembled source power to the assembled
matrix-multiplication direct sum is exactly the situation the anti-laundering rule of `DESIGN.md`
forbids: it is the conclusion the interface exists to prove.

This module supplies the missing derivation.  Its premises are finite and factorwise:

* `hX`, a finite injectivity statement for the `X` block labels of the ambient support (in laser
  clients this is the output of the preceding hashing or `X`-isolation step);
* `compatibleY` / `compatibleZ` together with their **soundness** statements, i.e. the paper's
  "every surviving address is compatible with the label it actually uses"; these are predicates
  on finite address families, never tensor relations;
* one exact restriction per *retained constituent* to the common rectangular
  matrix-multiplication tensor.

Everything tensor-semantic is then *derived*: the two exact variable zero-outs come from
`Tensor.Restricts.partitionedCompatibilityIsolated` through the committed cleanup theorem
`Tensor.Restricts.partitionedYZCompatibilityCleanup_to_indexedDirectSum`, the direct sum is
assembled by `Tensor.Restricts.indexedDirectSum`, and the passage from a canonical tensor power
`T ^ (m + 1)` to its word-block partition is the canonical structural theorem
`Tensor.Restricts.power_partitionedPositivePower`.  This mirrors the compliant pattern of
`AggregateMarkedHashingLaserVolume.toSubexponentialLaserVolumeSequence`, whose `extract` field is
derived the same way.

## Residual client obligations

The constructors below leave exactly four inputs to the paper client, all of them finite,
factorwise, or already proved in the combinatorial layer:

1. `hX : Set.InjOn (fun address ↦ address .X) ambient` — a statement about a `Finset` of block
   addresses.  For hashing clients it is the legwise-injectivity output of marked isolation; for
   word-type clients it is injectivity of the `X` word on the retained type class.
2. `hsoundY` / `hsoundZ` — `Tensor.IsCompatibilitySound`, again pure predicates on finite address
   families.  No tensor appears in them.
3. `hleaf` — one exact restriction `P.constituent address ⊒ ⟨xSize, ySize, zSize⟩` per retained
   address.  This is the *factorwise* premise permitted by the anti-laundering rule and is what
   the segmented-leaf / typed-leaf machinery discharges.
4. `hsupport : P.support = ambient` — a structural support identity, not a semantic relation.

The **copy count is not an input**: it is definitionally the cardinality of the final isolated
support `Tensor.compatibilityIsolatedSupport (Tensor.compatibilityIsolatedSupport ambient .Y _)
.Z _`, which is precisely the `Finset` whose cardinality the counting layer bounds from below.
Nothing here assumes a restriction or degeneration whose source is an assembled power and whose
target is an assembled family.

## What is deliberately not derived here

* The **lower bound** on the copy count.  This module hands the client the exact `Finset` whose
  cardinality is the copy count; bounding that cardinality from below is the business of the
  compatibility-incidence and hashing estimates, which are already finite counting theorems.
* The **paper instantiation** of `hX` and of the compatibility predicates.  Those depend on which
  alphabet quotient and which hashing scheme a client uses and cannot be stated generically.
* Cleanups that damage constituents.  By construction, a whole-constituent stage exists only when
  the cleanup zeroes complete partition variables; a hole-repair client must keep using the
  damaged-copy interfaces instead.

No step of the derivation needed new mathematics: every tensor-semantic ingredient
(`Tensor.Restricts.partitionedCompatibilityIsolated`,
`Tensor.Restricts.partitionedLegwiseInjective_to_indexedDirectSum`,
`Tensor.Restricts.indexedDirectSum`, `Tensor.Restricts.power_partitionedPositivePower`) was
already proved; only the composition into the stage interface was missing.
-/

namespace AlgebraicComplexity

open Tensor

universe u v w

section Cleanup

variable {K : Type u} [CommSemiring K]
variable {A : Leg → Type w} [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]
variable {V : ∀ c, A c → Type v}
variable [∀ c a, AddCommMonoid (V c a)] [∀ c a, Module K (V c a)]

/-- Two sound compatibility zero-outs, on top of an `X`-isolated ambient family, restrict a
partitioned tensor to a direct sum of equal rectangular matrix-multiplication tensors indexed by
the surviving support.

The only tensor-semantic input is the per-constituent restriction `hleaf`.  The assembled
restriction is constructed, not assumed. -/
theorem Tensor.Restricts.partitionedYZCompatibilityCleanup_to_matrixMultiplicationDirectSum
    (P : PartitionedTensor (K := K) (A := A) V)
    (hX : Set.InjOn (fun address : BlockAddress A ↦ address .X) P.support)
    (compatibleY : A .Y → BlockAddress A → Prop)
    (hsoundY : IsCompatibilitySound P.support .Y compatibleY)
    (compatibleZ : A .Z → BlockAddress A → Prop)
    (hsoundZ : IsCompatibilitySound
      (compatibilityIsolatedSupport P.support .Y compatibleY) .Z compatibleZ)
    (xSize ySize zSize : ℕ)
    (hleaf : ∀ address : compatibilityIsolatedSupport
        (compatibilityIsolatedSupport P.support .Y compatibleY) .Z compatibleZ,
      Restricts (P.constituent address.1)
        (matrixMultiplication (K := K) xSize ySize zSize)) :
    Restricts P.realize
      (matrixMultiplicationDirectSum
        (ι := compatibilityIsolatedSupport
          (compatibilityIsolatedSupport P.support .Y compatibleY) .Z compatibleZ)
        K (fun _ ↦ xSize) (fun _ ↦ ySize) (fun _ ↦ zSize)) := by
  have hdirect :=
    Tensor.Restricts.partitionedYZCompatibilityCleanup_to_indexedDirectSum
      P hX compatibleY hsoundY compatibleZ hsoundZ
  exact hdirect.trans (by
    simpa only [matrixMultiplicationDirectSum] using
      Tensor.Restricts.indexedDirectSum hleaf)

/-- Whole-constituent laser-volume stage derived from an `X`-isolated ambient family and two
sound compatibility zero-outs.

The copy count is the cardinality of the final isolated support, which is exactly the `Finset`
counted by the compatibility-incidence estimates.  No restriction of the assembled source is
assumed. -/
noncomputable def WholeConstituentLaserVolumeStage.ofYZCompatibilityCleanup
    (K : Type u) [CommSemiring K]
    {A : Leg → Type w} [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]
    {V : ∀ c, A c → Type v}
    [∀ c a, AddCommMonoid (V c a)] [∀ c a, Module K (V c a)]
    (P : PartitionedTensor (K := K) (A := A) V)
    (hX : Set.InjOn (fun address : BlockAddress A ↦ address .X) P.support)
    (compatibleY : A .Y → BlockAddress A → Prop)
    (hsoundY : IsCompatibilitySound P.support .Y compatibleY)
    (compatibleZ : A .Z → BlockAddress A → Prop)
    (hsoundZ : IsCompatibilitySound
      (compatibilityIsolatedSupport P.support .Y compatibleY) .Z compatibleZ)
    (xSize ySize zSize : ℕ)
    (hleaf : ∀ address : compatibilityIsolatedSupport
        (compatibilityIsolatedSupport P.support .Y compatibleY) .Z compatibleZ,
      Restricts (P.constituent address.1)
        (matrixMultiplication (K := K) xSize ySize zSize)) :
    WholeConstituentLaserVolumeStage K P.realize
      (compatibilityIsolatedSupport
        (compatibilityIsolatedSupport P.support .Y compatibleY) .Z compatibleZ).card
      xSize ySize zSize where
  I := compatibilityIsolatedSupport
    (compatibilityIsolatedSupport P.support .Y compatibleY) .Z compatibleZ
  card_I := Fintype.card_coe _
  source_restricts :=
    Tensor.Restricts.partitionedYZCompatibilityCleanup_to_matrixMultiplicationDirectSum
      P hX compatibleY hsoundY compatibleZ hsoundZ xSize ySize zSize hleaf

/-- Ambient-indexed form of `WholeConstituentLaserVolumeStage.ofYZCompatibilityCleanup`.

Clients usually name their retained family as a `Finset` `ambient` of block addresses and prove a
structural support identity for the partitioned tensor.  Stating the isolated supports in terms of
`ambient` lets the finite counting theorems and this constructor share literally the same
`Finset`. -/
noncomputable def WholeConstituentLaserVolumeStage.ofAmbientYZCompatibilityCleanup
    (K : Type u) [CommSemiring K]
    {A : Leg → Type w} [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]
    {V : ∀ c, A c → Type v}
    [∀ c a, AddCommMonoid (V c a)] [∀ c a, Module K (V c a)]
    (P : PartitionedTensor (K := K) (A := A) V)
    (ambient : Finset (BlockAddress A)) (hsupport : P.support = ambient)
    (hX : Set.InjOn (fun address : BlockAddress A ↦ address .X) ambient)
    (compatibleY : A .Y → BlockAddress A → Prop)
    (hsoundY : IsCompatibilitySound ambient .Y compatibleY)
    (compatibleZ : A .Z → BlockAddress A → Prop)
    (hsoundZ : IsCompatibilitySound
      (compatibilityIsolatedSupport ambient .Y compatibleY) .Z compatibleZ)
    (xSize ySize zSize : ℕ)
    (hleaf : ∀ address : compatibilityIsolatedSupport
        (compatibilityIsolatedSupport ambient .Y compatibleY) .Z compatibleZ,
      Restricts (P.constituent address.1)
        (matrixMultiplication (K := K) xSize ySize zSize)) :
    WholeConstituentLaserVolumeStage K P.realize
      (compatibilityIsolatedSupport
        (compatibilityIsolatedSupport ambient .Y compatibleY) .Z compatibleZ).card
      xSize ySize zSize := by
  subst hsupport
  exact WholeConstituentLaserVolumeStage.ofYZCompatibilityCleanup K P hX
    compatibleY hsoundY compatibleZ hsoundZ xSize ySize zSize hleaf

end Cleanup

section PositivePower

variable {K : Type u} [CommSemiring K]
variable {A : Leg → Type w} [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]
variable {V : ∀ c, A c → Type (max u v)}
variable [∀ c a, AddCommMonoid (V c a)] [∀ c a, Module K (V c a)]

/-- The same derivation for a canonical tensor power.

The source is the honest `Tensor.power P.realize (m + 1)` used by asymptotic rank; the passage to
the word-block partition `P.positivePower m` is the canonical structural theorem
`Tensor.Restricts.power_partitionedPositivePower`, invoked here rather than stored as a
certificate field. -/
noncomputable def WholeConstituentLaserVolumeStage.ofPositivePowerYZCompatibilityCleanup
    (K : Type u) [CommSemiring K]
    {A : Leg → Type w} [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]
    {V : ∀ c, A c → Type (max u v)}
    [∀ c a, AddCommMonoid (V c a)] [∀ c a, Module K (V c a)]
    (P : PartitionedTensor (K := K) (A := A) V) (m : ℕ)
    (hX : Set.InjOn
      (fun address : BlockAddress (fun c ↦ PositiveWord (A c) m) ↦ address .X)
      (P.positivePower m).support)
    (compatibleY : PositiveWord (A .Y) m →
      BlockAddress (fun c ↦ PositiveWord (A c) m) → Prop)
    (hsoundY : IsCompatibilitySound (P.positivePower m).support .Y compatibleY)
    (compatibleZ : PositiveWord (A .Z) m →
      BlockAddress (fun c ↦ PositiveWord (A c) m) → Prop)
    (hsoundZ : IsCompatibilitySound
      (compatibilityIsolatedSupport (P.positivePower m).support .Y compatibleY)
      .Z compatibleZ)
    (xSize ySize zSize : ℕ)
    (hleaf : ∀ address : compatibilityIsolatedSupport
        (compatibilityIsolatedSupport (P.positivePower m).support .Y compatibleY)
        .Z compatibleZ,
      Restricts ((P.positivePower m).constituent address.1)
        (matrixMultiplication (K := K) xSize ySize zSize)) :
    WholeConstituentLaserVolumeStage K (Tensor.power P.realize (m + 1))
      (compatibilityIsolatedSupport
        (compatibilityIsolatedSupport (P.positivePower m).support .Y compatibleY)
        .Z compatibleZ).card
      xSize ySize zSize where
  I := compatibilityIsolatedSupport
    (compatibilityIsolatedSupport (P.positivePower m).support .Y compatibleY)
    .Z compatibleZ
  card_I := Fintype.card_coe _
  source_restricts :=
    (Tensor.Restricts.power_partitionedPositivePower P m).trans
      (Tensor.Restricts.partitionedYZCompatibilityCleanup_to_matrixMultiplicationDirectSum
        (P.positivePower m) hX compatibleY hsoundY compatibleZ hsoundZ
        xSize ySize zSize hleaf)

/-- Positive-exponent repackaging of
`WholeConstituentLaserVolumeStage.ofPositivePowerYZCompatibilityCleanup`.

`WholeConstituentLaserVolumeSequenceData.stage` is indexed by `stride * r` with `0 < r`, so its
source is `Tensor.power T (stride * r)` rather than a literal successor.  This form absorbs the
predecessor bookkeeping once, exactly as the aggregate marked-hashing sequence does inside its
`extract` field. -/
noncomputable def WholeConstituentLaserVolumeStage.ofPositiveExponentYZCompatibilityCleanup
    (K : Type u) [CommSemiring K]
    {A : Leg → Type w} [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]
    {V : ∀ c, A c → Type (max u v)}
    [∀ c a, AddCommMonoid (V c a)] [∀ c a, Module K (V c a)]
    (P : PartitionedTensor (K := K) (A := A) V) (exponent : ℕ) (hexponent : 0 < exponent)
    (hX : Set.InjOn
      (fun address : BlockAddress (fun c ↦ PositiveWord (A c) (exponent - 1)) ↦ address .X)
      (P.positivePower (exponent - 1)).support)
    (compatibleY : PositiveWord (A .Y) (exponent - 1) →
      BlockAddress (fun c ↦ PositiveWord (A c) (exponent - 1)) → Prop)
    (hsoundY : IsCompatibilitySound
      (P.positivePower (exponent - 1)).support .Y compatibleY)
    (compatibleZ : PositiveWord (A .Z) (exponent - 1) →
      BlockAddress (fun c ↦ PositiveWord (A c) (exponent - 1)) → Prop)
    (hsoundZ : IsCompatibilitySound
      (compatibilityIsolatedSupport
        (P.positivePower (exponent - 1)).support .Y compatibleY) .Z compatibleZ)
    (xSize ySize zSize : ℕ)
    (hleaf : ∀ address : compatibilityIsolatedSupport
        (compatibilityIsolatedSupport
          (P.positivePower (exponent - 1)).support .Y compatibleY) .Z compatibleZ,
      Restricts ((P.positivePower (exponent - 1)).constituent address.1)
        (matrixMultiplication (K := K) xSize ySize zSize)) :
    WholeConstituentLaserVolumeStage K (Tensor.power P.realize exponent)
      (compatibilityIsolatedSupport
        (compatibilityIsolatedSupport
          (P.positivePower (exponent - 1)).support .Y compatibleY) .Z compatibleZ).card
      xSize ySize zSize := by
  match exponent, hexponent with
  | m + 1, _ =>
    exact WholeConstituentLaserVolumeStage.ofPositivePowerYZCompatibilityCleanup
      K P m hX compatibleY hsoundY compatibleZ hsoundZ xSize ySize zSize hleaf

end PositivePower

end AlgebraicComplexity
