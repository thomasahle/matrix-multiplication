/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.CoarsenedRationalTypedLeaf
import AlgebraicComplexity.MatrixMultiplication.PartitionedSymmetrization
import AlgebraicComplexity.Tensor.PartitionedSelectStructure

set_option autoImplicit false

/-!
# `sym₃` of a block cut is a block cut of `sym₃`

Layer 3 (`AlgebraicComplexity/MatrixMultiplication/`).
`MatrixMultiplication/PartitionedSymmetrization.lean` builds the three-orientation partition
certificate `symThreePartition P = P ⊗ P^c ⊗ P^{c²}` and shows that its realization *is*
`sym₃` of the realization (`isomorphic_symThreePartition`).  This module records what happens when
the source certificate is first cut by a leg-local block predicate: the symmetrization of the cut is
a single cut of the symmetrization, by the induced three-orientation predicate `symThreeKeep`.

## Why a laser client needs exactly this

`[duan2023faster]`'s fine leaf cuts a partitioned power by a per-leg word-type condition and only
then symmetrizes, whereas the value certificate attached to a level-two component symmetrizes first
and cuts the symmetrized power by its marginal types.  Comparing the two therefore means comparing
two cuts, and selection monotonicity (`select_select_realize_of_imp`, `Restricts.partitionedSelect`)
only applies once both are cuts of *one* parent certificate.  `symThreePartition_select` supplies
exactly that normal form; the remaining discrepancy between the two parents is the regrouping of a
word of triples into a triple of words, which is a partition reindex and is treated separately.

## The shape of the induced predicate

The three factors of `symThreePartition` sit over the legs `c`, `c⁻¹(c)` and `c⁻²(c)` of the
source, so the induced predicate reads its three components at those three legs.  The third
component is written at `cycle.symm.symm c` rather than at `cycle c`: that is the leg the type of
the component mentions, so writing it this way keeps the statement free of a transport.

The published step these serve.  `[duan2023faster]`, proof of `lem:non-rot-values` (d),
`papers/sources/2210.10173/second_power_appendix.tex:26-45`, especially lines `:31-37`: the paper
first zeroes out the blocks inconsistent with the marginal distributions of `alpha^{(1,1,2)}`, and
only then forms `sym_3(T) = T (x) T^rot (x) T^{rot rot}`, using its inclusion in the symmetrized
marginally restricted component.  The general reason for cutting before symmetrizing is stated at
`global_value.tex:98-121`, Step 4 at line `:104` and the implicit symmetrization at line `:121`.

These Lean results are reusable algebraic infrastructure, not published claims: the theorem
statements below are general facts about partitioned tensors, and what they formalize is the
commutation/restriction bridge the paper needs at line `:37` in order to write that inclusion at
all.  The paper never states them, because in its notation cutting and symmetrizing commute
silently.

Primary source: Ran Duan, Hongxun Wu and Renfei Zhou, *Faster Matrix Multiplication via
Asymmetric Hashing*, `[duan2023faster]`, `second_power_appendix.tex:26-45` (lines `:31-37`),
`global_value.tex:98-121` (lines `:104`, `:121`).
-/

namespace AlgebraicComplexity.Tensor

universe u v w

namespace PartitionedTensor

variable {K : Type u} [CommSemiring K]
variable {A : Leg → Type w} [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]
variable {V : ∀ c, A c → Type (max u v)}
variable [∀ c a, AddCommMonoid (V c a)] [∀ c a, Module K (V c a)]

/-- **The three-orientation keep predicate induced by a source keep predicate.**  Each of the
three components is tested at the leg its own factor was permuted from. -/
def symThreeKeep (keep : ∀ c, A c → Prop) :
    ∀ c, ProductBlockIndex (ProductBlockIndex A (PermutedBlockIndex cycle A))
      (PermutedBlockIndex cycle.symm A) c → Prop :=
  fun c q ↦ (keep c q.1.1 ∧ keep (cycle.symm c) q.1.2) ∧ keep (cycle.symm.symm c) q.2

instance symThreeKeepDecidable (keep : ∀ c, A c → Prop) [∀ c a, Decidable (keep c a)]
    (c : Leg) (q : ProductBlockIndex (ProductBlockIndex A (PermutedBlockIndex cycle A))
      (PermutedBlockIndex cycle.symm A) c) :
    Decidable (symThreeKeep keep c q) :=
  inferInstanceAs (Decidable ((keep c q.1.1 ∧ keep (cycle.symm c) q.1.2) ∧
    keep (cycle.symm.symm c) q.2))

/-- **Symmetrizing a cut certificate cuts the symmetrized certificate.**

Proof sketch: `permute_select` moves the cut through each of the two permuted factors, and
`external_select` merges the three cuts into one, in the association of `symThreePartition`; the
resulting predicate is `symThreeKeep` after beta reduction, and the two `Decidable` instances agree
because `Decidable` is a subsingleton. -/
theorem symThreePartition_select
    (P : PartitionedTensor (K := K) (A := A) V)
    (keep : ∀ c, A c → Prop) [∀ c a, Decidable (keep c a)] :
    (P.select keep).symThreePartition =
      P.symThreePartition.select (symThreeKeep keep) := by
  classical
  unfold PartitionedTensor.symThreePartition
  rw [PartitionedTensor.permute_select, PartitionedTensor.permute_select,
    PartitionedTensor.external_select, PartitionedTensor.external_select]
  rfl

/-- **`sym₃` of the realization of a cut certificate is the realization of a single cut of the
three-orientation certificate.**  The client form: it composes
`isomorphic_symThreePartition` at the cut with the structural identity above. -/
theorem isomorphic_symThreePartition_select
    (P : PartitionedTensor (K := K) (A := A) V)
    (keep : ∀ c, A c → Prop) [∀ c a, Decidable (keep c a)] :
    Isomorphic (symThree K (P.select keep).realize)
      (P.symThreePartition.select (symThreeKeep keep)).realize := by
  rw [← symThreePartition_select P keep]
  exact isomorphic_symThreePartition (P.select keep)

end PartitionedTensor

/-- **Selection monotonicity, as a restriction.**  A cut by a weaker leg-local predicate restricts
onto the cut by any stronger one.

Proof sketch: cutting the weaker cut again by the stronger predicate is an exact zeroing
(`Restricts.partitionedSelect`), and by `PartitionedTensor.select_select_realize_of_imp` the
doubly cut certificate realizes the same tensor as the single stronger cut. -/
theorem Restricts.select_of_imp
    {K : Type u} [CommSemiring K]
    {A : Leg → Type w} [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]
    {V : ∀ c, A c → Type (max u v)}
    [∀ c a, AddCommMonoid (V c a)] [∀ c a, Module K (V c a)]
    (P : PartitionedTensor (K := K) (A := A) V)
    (outer inner : ∀ c, A c → Prop)
    [∀ c a, Decidable (outer c a)] [∀ c a, Decidable (inner c a)]
    (himp : ∀ c a, inner c a → outer c a) :
    Restricts (P.select outer).realize (P.select inner).realize := by
  have h := Restricts.partitionedSelect (P.select outer) inner
  rwa [PartitionedTensor.select_select_realize_of_imp P outer inner himp] at h

end AlgebraicComplexity.Tensor
