/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Tensor.CompatibilityZeroing
import AlgebraicComplexity.MatrixMultiplication.PartitionedSymmetrization

set_option autoImplicit false

/-!
# Compatibility predicates for external, permuted and six-symmetrized partitions

Layer 3 (`AlgebraicComplexity/MatrixMultiplication/`).  `Tensor/CompatibilityZeroing.lean`'s
zero-out step is
parameterized by a predicate `compatible : A pivot -> BlockAddress A -> Prop` and one hypothesis
about it,

`IsCompatibilitySound ambient pivot compatible := forall address in ambient,
  compatible (address pivot) address`,

i.e. *reflexivity on the ambient support*.  All the mathematical content of a laser argument's
compatibility step sits in the other half --- `compatibilityIsolatedSupport`, the addresses that
are the **sole** ambient address compatible with their own pivot label --- which is a counting
statement, not a soundness statement.

This module builds compatibility predicates for `PartitionedTensor.external`,
`PartitionedTensor.permute`, `PartitionedTensor.positivePower` and
`PartitionedTensor.symSixPartition` out of predicates for the factors, and proves each of them
sound.  Consequently the six-orientation compatibility of an asymmetric laser argument **is** the
componentwise product of source-leg compatibilities, and its soundness is an instantiation rather
than new mathematics.

## The leg twist, which is the whole asymmetry

A `pivot`-label of `P.permute e` is a `(e.symm pivot)`-label of `P`
(`PermutedBlockIndex e A pivot` is by definition `A (e.symm pivot)`).  So a *single* compatibility
condition on the `Y` leg of `symSixPartition P` is six conditions on the source, one per leg
permutation `pi`, each about the source leg `pi.symm Y` --- and as `pi` ranges over `Perm Leg`
that hits `X`, `Y` and `Z` twice each.  `orientedCompatible` and
`isCompatibilitySound_orientedCompatible` are exactly that bookkeeping.  A client therefore owes
one compatibility predicate **per source leg**, not one per orientation, which is the
marginal-per-orientation form an asymmetric distribution produces.

## Soundness descends, so the two zero-outs do not interact

`Tensor.Restricts.partitionedYZCompatibilityCleanup_to_indexedDirectSum` asks for `Z`-soundness on
the *`Y`-isolated* support, a subset of the ambient.  `IsCompatibilitySound.mono` plus
`compatibilityIsolatedSupport_subset` reduce that to `Z`-soundness on the ambient itself
(`isCompatibilitySound_compatibilityIsolatedSupport`), so a client proves the two conditions
independently.

## What this does *not* supply

Nothing here makes `compatibilityIsolatedSupport` large; a constantly-true predicate is sound and
isolates almost nothing.  Choosing predicates whose isolated support carries the retained-copy
count is the counting obligation, and it is untouched by this module.
-/

namespace AlgebraicComplexity.Tensor

universe u v w

variable {K : Type u} [CommSemiring K]
variable {A : Leg → Type w} [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]
variable {V : ∀ c, A c → Type (max u v)}
variable [∀ c a, AddCommMonoid (V c a)] [∀ c a, Module K (V c a)]

/-! ## Soundness is monotone -/

omit [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)] in
/-- Soundness constrains only the addresses actually present, so it descends to sub-supports. -/
theorem IsCompatibilitySound.mono {ambient ambient' : Finset (BlockAddress A)} {pivot : Leg}
    {compatible : A pivot → BlockAddress A → Prop}
    (hsub : ambient ⊆ ambient') (h : IsCompatibilitySound ambient' pivot compatible) :
    IsCompatibilitySound ambient pivot compatible :=
  fun address haddress ↦ h address (hsub haddress)

omit [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)] in
/-- **The second zero-out inherits soundness from the first's ambient.**  A predicate sound on the
ambient support is sound on the support isolated by any earlier compatibility pass, so the `Y` and
`Z` obligations of the cleanup are proved independently. -/
theorem isCompatibilitySound_compatibilityIsolatedSupport
    {ambient : Finset (BlockAddress A)} {first pivot : Leg}
    {firstCompatible : A first → BlockAddress A → Prop}
    {compatible : A pivot → BlockAddress A → Prop}
    (h : IsCompatibilitySound ambient pivot compatible) :
    IsCompatibilitySound
      (compatibilityIsolatedSupport ambient first firstCompatible) pivot compatible :=
  h.mono (compatibilityIsolatedSupport_subset ambient first firstCompatible)

/-! ## External products -/

/-- Componentwise compatibility for an external product of partitions. -/
def externalCompatible {B : Leg → Type w} {pivot : Leg}
    (cA : A pivot → BlockAddress A → Prop) (cB : B pivot → BlockAddress B → Prop) :
    ProductBlockIndex A B pivot → BlockAddress (ProductBlockIndex A B) → Prop :=
  fun label address ↦
    cA label.1 (fun c ↦ (address c).1) ∧ cB label.2 (fun c ↦ (address c).2)

/-- **Componentwise compatibility of an external product is sound.**

Proof sketch: `PartitionedTensor.mem_external_support` says membership in a product support *is*
componentwise membership of the two projected addresses, and the `pivot` label of the product
address projects to the two `pivot` labels; apply the two factor hypotheses. -/
theorem isCompatibilitySound_external
    {B : Leg → Type w} [∀ c, Fintype (B c)] [∀ c, DecidableEq (B c)]
    {W : ∀ c, B c → Type (max u v)}
    [∀ c b, AddCommMonoid (W c b)] [∀ c b, Module K (W c b)]
    (P : PartitionedTensor (K := K) (A := A) V)
    (Q : PartitionedTensor (K := K) (A := B) W) {pivot : Leg}
    {cA : A pivot → BlockAddress A → Prop} {cB : B pivot → BlockAddress B → Prop}
    (hA : IsCompatibilitySound P.support pivot cA)
    (hB : IsCompatibilitySound Q.support pivot cB) :
    IsCompatibilitySound (P.external Q).support pivot (externalCompatible cA cB) := by
  intro address haddress
  rw [PartitionedTensor.mem_external_support] at haddress
  exact ⟨hA _ haddress.1, hB _ haddress.2⟩

/-! ## Leg permutations -/

/-- Compatibility transported through a leg permutation.  A `pivot` label of `P.permute e` is a
`(e.symm pivot)` label of `P`, so the source predicate is the one for that source leg. -/
def permuteCompatible {pivot : Leg} (e : Orientation)
    (c : A (e.symm pivot) → BlockAddress A → Prop) :
    PermutedBlockIndex e A pivot → BlockAddress (PermutedBlockIndex e A) → Prop :=
  fun label address ↦ c label ((permuteBlockAddress e).symm address)

/-- **Transported compatibility is sound**, from soundness at the source leg `e.symm pivot`. -/
theorem isCompatibilitySound_permute
    (P : PartitionedTensor (K := K) (A := A) V) (e : Orientation) {pivot : Leg}
    {c : A (e.symm pivot) → BlockAddress A → Prop}
    (h : IsCompatibilitySound P.support (e.symm pivot) c) :
    IsCompatibilitySound (P.permute e).support pivot (permuteCompatible e c) := by
  intro address haddress
  have hsource : (permuteBlockAddress e).symm address ∈ P.support :=
    (P.mem_permute_support e address).mp haddress
  show c (address pivot) ((permuteBlockAddress e).symm address)
  simpa using h _ hsource

/-- One orientation's contribution, read off a legwise family of source predicates. -/
def orientedCompatible (e : Orientation)
    (c : ∀ leg : Leg, A leg → BlockAddress A → Prop) (pivot : Leg) :
    PermutedBlockIndex e A pivot → BlockAddress (PermutedBlockIndex e A) → Prop :=
  permuteCompatible e (c (e.symm pivot))

/-- **One orientation's contribution is sound**, given soundness at every source leg. -/
theorem isCompatibilitySound_orientedCompatible
    (P : PartitionedTensor (K := K) (A := A) V) (e : Orientation)
    (c : ∀ leg : Leg, A leg → BlockAddress A → Prop) (pivot : Leg)
    (h : ∀ leg : Leg, IsCompatibilitySound P.support leg (c leg)) :
    IsCompatibilitySound (P.permute e).support pivot (orientedCompatible e c pivot) :=
  isCompatibilitySound_permute P e (h (e.symm pivot))

/-! ## The three- and six-orientation products -/

/-- Compatibility of `symThreePartition`, as the product of the identity, `cycle` and
`cycle.symm` orientations. -/
def symThreeCompatible (c : ∀ leg : Leg, A leg → BlockAddress A → Prop) (pivot : Leg) :
    ProductBlockIndex (ProductBlockIndex A (PermutedBlockIndex cycle A))
        (PermutedBlockIndex cycle.symm A) pivot →
      BlockAddress (ProductBlockIndex (ProductBlockIndex A (PermutedBlockIndex cycle A))
        (PermutedBlockIndex cycle.symm A)) → Prop :=
  externalCompatible (externalCompatible (c pivot) (orientedCompatible cycle c pivot))
    (orientedCompatible cycle.symm c pivot)

/-- Compatibility of `swapSymThreePartition`, the three swapped orientations. -/
def swapSymThreeCompatible (c : ∀ leg : Leg, A leg → BlockAddress A → Prop) (pivot : Leg) :
    ProductBlockIndex
        (ProductBlockIndex (PermutedBlockIndex swapXY A)
          (PermutedBlockIndex (cycle.trans swapXY) A))
        (PermutedBlockIndex (cycle.symm.trans swapXY) A) pivot →
      BlockAddress (ProductBlockIndex
        (ProductBlockIndex (PermutedBlockIndex swapXY A)
          (PermutedBlockIndex (cycle.trans swapXY) A))
        (PermutedBlockIndex (cycle.symm.trans swapXY) A)) → Prop :=
  externalCompatible
    (externalCompatible (orientedCompatible swapXY c pivot)
      (orientedCompatible (cycle.trans swapXY) c pivot))
    (orientedCompatible (cycle.symm.trans swapXY) c pivot)

/-- **The six-orientation compatibility predicate**, from one predicate per source leg.  Its six
factors are the same legwise family read at the six legs `pi.symm pivot`, `pi` ranging over
`Perm Leg`. -/
def symSixCompatible (c : ∀ leg : Leg, A leg → BlockAddress A → Prop) (pivot : Leg) :=
  externalCompatible (symThreeCompatible (A := A) c pivot) (swapSymThreeCompatible (A := A) c pivot)

/-- Soundness of the three-orientation compatibility. -/
theorem isCompatibilitySound_symThreeCompatible
    (P : PartitionedTensor (K := K) (A := A) V)
    (c : ∀ leg : Leg, A leg → BlockAddress A → Prop) (pivot : Leg)
    (h : ∀ leg : Leg, IsCompatibilitySound P.support leg (c leg)) :
    IsCompatibilitySound (P.symThreePartition).support pivot
      (symThreeCompatible (A := A) c pivot) :=
  isCompatibilitySound_external _ _
    (isCompatibilitySound_external P _ (h pivot)
      (isCompatibilitySound_orientedCompatible P cycle c pivot h))
    (isCompatibilitySound_orientedCompatible P cycle.symm c pivot h)

/-- Soundness of the swapped three-orientation compatibility. -/
theorem isCompatibilitySound_swapSymThreeCompatible
    (P : PartitionedTensor (K := K) (A := A) V)
    (c : ∀ leg : Leg, A leg → BlockAddress A → Prop) (pivot : Leg)
    (h : ∀ leg : Leg, IsCompatibilitySound P.support leg (c leg)) :
    IsCompatibilitySound (P.swapSymThreePartition).support pivot
      (swapSymThreeCompatible (A := A) c pivot) :=
  isCompatibilitySound_external _ _
    (isCompatibilitySound_external _ _
      (isCompatibilitySound_orientedCompatible P swapXY c pivot h)
      (isCompatibilitySound_orientedCompatible P (cycle.trans swapXY) c pivot h))
    (isCompatibilitySound_orientedCompatible P (cycle.symm.trans swapXY) c pivot h)

/-- **The six-orientation compatibility is sound**, from soundness at every source leg.

This is the whole answer to "is the six-tuple compatibility the componentwise product of the
plain source model?": it is, and its soundness is a product argument with no coordinate coupling.
The coupling in `[DuanWuZhou2022]` section 6.3 lives in the *isolation* count, not here. -/
theorem isCompatibilitySound_symSixCompatible
    (P : PartitionedTensor (K := K) (A := A) V)
    (c : ∀ leg : Leg, A leg → BlockAddress A → Prop) (pivot : Leg)
    (h : ∀ leg : Leg, IsCompatibilitySound P.support leg (c leg)) :
    IsCompatibilitySound (P.symSixPartition).support pivot
      (symSixCompatible (A := A) c pivot) :=
  isCompatibilitySound_external _ _
    (isCompatibilitySound_symThreeCompatible P c pivot h)
    (isCompatibilitySound_swapSymThreeCompatible P c pivot h)

/-! ## Positive powers -/

/-- Letterwise compatibility of a positive power: every letter of the word must be compatible with
the corresponding letter of the address. -/
def positivePowerCompatible {pivot : Leg} (c : A pivot → BlockAddress A → Prop) :
    (n : ℕ) → PositiveWord (A pivot) n →
      BlockAddress (fun leg ↦ PositiveWord (A leg) n) → Prop
  | 0 => c
  | n + 1 =>
      externalCompatible (A := fun leg ↦ PositiveWord (A leg) n) (B := A)
        (positivePowerCompatible c n) c

/-- **Letterwise compatibility of a positive power is sound.** -/
theorem isCompatibilitySound_positivePower
    (P : PartitionedTensor (K := K) (A := A) V) {pivot : Leg}
    {c : A pivot → BlockAddress A → Prop}
    (h : IsCompatibilitySound P.support pivot c) :
    ∀ n : ℕ, IsCompatibilitySound (P.positivePower n).support pivot
      (positivePowerCompatible c n)
  | 0 => by
      intro address haddress
      exact h address haddress
  | n + 1 => by
      simp only [PartitionedTensor.positivePower_succ, positivePowerCompatible]
      exact isCompatibilitySound_external _ _
        (isCompatibilitySound_positivePower P h n) h

/-! ## The predicate an asymmetric six-symmetrized laser stage consumes -/

/-- **The compatibility predicate of the six-orientation positive power**, from one predicate per
source leg: six orientations, then letterwise along the word. -/
def symSixPowerCompatible (c : ∀ leg : Leg, A leg → BlockAddress A → Prop)
    (pivot : Leg) (n : ℕ) :=
  positivePowerCompatible (symSixCompatible (A := A) c pivot) n

/-- **It is sound.**  Together with `IsCompatibilitySound.mono` this discharges both `hsoundY` and
`hsoundZ` of `[DuanWuZhou2022]` section 6's assembly for *any* legwise source model, on the
six-orientation positive power and on every sub-support of it --- in particular on the support
retained by a hashing seed. -/
theorem isCompatibilitySound_symSixPowerCompatible
    (P : PartitionedTensor (K := K) (A := A) V)
    (c : ∀ leg : Leg, A leg → BlockAddress A → Prop) (pivot : Leg) (n : ℕ)
    (h : ∀ leg : Leg, IsCompatibilitySound P.support leg (c leg)) :
    IsCompatibilitySound (P.symSixPartition.positivePower n).support pivot
      (symSixPowerCompatible (A := A) c pivot n) :=
  isCompatibilitySound_positivePower P.symSixPartition
    (isCompatibilitySound_symSixCompatible P c pivot h) n

/-- **The form a client of the section 6 assembly uses.**  On any retained sub-support of the
six-orientation positive power, both compatibility obligations hold for the letterwise product of
a legwise source model.  Only the isolation count remains. -/
theorem isCompatibilitySound_symSixPowerCompatible_of_subset
    (P : PartitionedTensor (K := K) (A := A) V)
    (c : ∀ leg : Leg, A leg → BlockAddress A → Prop) (pivot : Leg) (n : ℕ)
    {retained : Finset (BlockAddress (fun _leg ↦ PositiveWord _ n))}
    (hretained : retained ⊆ (P.symSixPartition.positivePower n).support)
    (h : ∀ leg : Leg, IsCompatibilitySound P.support leg (c leg)) :
    IsCompatibilitySound retained pivot (symSixPowerCompatible (A := A) c pivot n) :=
  (isCompatibilitySound_symSixPowerCompatible P c pivot n h).mono hretained

end AlgebraicComplexity.Tensor
