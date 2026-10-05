/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.PartitionedSymmetrizationSelect
import AlgebraicComplexity.Tensor.PartitionedPermutePower

set_option autoImplicit false

/-!
# `sym₃` of a positive power is a positive power of `sym₃`, up to the word transpose

Layer 3 (`AlgebraicComplexity/MatrixMultiplication/`).  The three-orientation partition of a
positive partitioned power and the positive power of the three-orientation partition carry the same
tensor; their block labels differ by the transpose of a triple of words into a word of triples.
This module states that as a `PartitionedTensor.ReindexEquiv` and draws the consequence a
symmetrized laser client needs: `sym₃` of a *cut* of a positive power is the realization of a cut
of the positive power of the three-orientation partition.

## What paper step this serves

`[duan2023faster]`, `second_power_appendix.tex:26-45` (proof of `lem:non-rot-values` (d)) forms
`\T ⊆ T_{1,1,2}^{⊗m}` by zeroing out the blocks inconsistent with the marginals of
`α^{(1,1,2)}`, then takes `sym₃(\T) = \T ⊗ \T^{rot} ⊗ \T^{rot rot}` and applies symmetric
hashing to it.  The paper's `sym₃(T_{1,1,2}^{⊗m})` and the formalization's
`(sym₃ T_{1,1,2})^{⊗m}` --- the object the committed `T_{1,1,2}` value certificate is attached
to --- are literally the same product of `3m` factors in the paper's notation, read in a
different order.  Here they are two partitioned tensors over different block alphabets, and
this module is the reindex that identifies them.  It is a Lean-side bridge, not a step of the
paper: it pays for the
reordering the paper performs silently.

The `sym₃` (rather than `sym₆`) level is forced by the same passage: `T_{1,1,2}` is the one
level-two component that is not a matrix multiplication tensor, so the paper has no non-rotational
value for
it and must symmetrize (`second_power.tex:235`, footnote `note:T112`; `second_power.tex:145-156`,
`lem:non-rot-values` (d)).

Primary source: Ran Duan, Hongxun Wu and Renfei Zhou, *Faster Matrix Multiplication via Asymmetric
Hashing*, arXiv:2210.10173, `second_power_appendix.tex:26-45`, `second_power.tex:142-158`
(`lem:non-rot-values`), `second_power.tex:235` (`note:T112`).
-/

namespace AlgebraicComplexity.Tensor

namespace PartitionedTensor

universe u v w

variable {K : Type u} [CommSemiring K]
variable {A : Leg → Type w} [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]
variable {V : ∀ c, A c → Type (max u v)}
variable [∀ c a, AddCommMonoid (V c a)] [∀ c a, Module K (V c a)]

/-- **The label transpose of the three-orientation product of a positive power.**  A triple of
words, one per orientation, read as a word of triples. -/
def symThreeWordEquiv (n : ℕ) : ∀ c : Leg,
    ProductBlockIndex (ProductBlockIndex (fun c ↦ PositiveWord (A c) n)
        (PermutedBlockIndex cycle (fun c ↦ PositiveWord (A c) n)))
      (PermutedBlockIndex cycle.symm (fun c ↦ PositiveWord (A c) n)) c ≃
      PositiveWord (ProductBlockIndex (ProductBlockIndex A (PermutedBlockIndex cycle A))
        (PermutedBlockIndex cycle.symm A) c) n :=
  fun c ↦
    (Equiv.prodCongr (positiveWordProdEquiv (A c) (A (cycle.symm c)) n)
      (Equiv.refl (PositiveWord (A (cycle.symm.symm c)) n))).trans
      (positiveWordProdEquiv (A c × A (cycle.symm c)) (A (cycle.symm.symm c)) n)

/-- **The three-orientation partition of a positive power is a reindex of the positive power of the
three-orientation partition**, along the label transpose.

Proof sketch: the two rotated factors are moved across the power by
`reindexEquiv_permute_positivePower`, and the two external products are then merged into the power
by the committed `reindexEquiv_positivePower_external`, applied twice in the association of
`symThreePartition`; the composite label equivalence is `symThreeWordEquiv`. -/
theorem reindexEquiv_symThreePartition_positivePower
    (P : PartitionedTensor (K := K) (A := A) V) (n : ℕ) :
    ((P.positivePower n).symThreePartition).ReindexEquiv
      ((P.symThreePartition).positivePower n) (symThreeWordEquiv (A := A) n) := by
  have h1 := (PartitionedTensor.ReindexEquiv.refl (P.positivePower n)).external
    (reindexEquiv_permute_positivePower P cycle n)
  have h2 := PartitionedTensor.reindexEquiv_positivePower_external P (P.permute cycle) n
  have h3 := (h1.trans h2).external (reindexEquiv_permute_positivePower P cycle.symm n)
  have h4 := PartitionedTensor.reindexEquiv_positivePower_external
    (P.external (P.permute cycle)) (P.permute cycle.symm) n
  refine PartitionedTensor.ReindexEquiv.congr_equiv ?_ (h3.trans h4)
  funext c
  apply Equiv.ext
  rintro ⟨⟨u, v⟩, x⟩
  rfl

/-- **`sym₃` of a cut of a positive power is a cut of the positive power of the three-orientation
partition.**

This is the normal form a symmetrized laser client needs: the leaf's cut and the value
certificate's marginal cut become two cuts of one parent, so that ordinary selection monotonicity
(`Restricts.select_of_imp`) compares them. -/
theorem isomorphic_symThreePartition_positivePower_select
    (P : PartitionedTensor (K := K) (A := A) V) (n : ℕ)
    (keep : ∀ c, PositiveWord (A c) n → Prop) [∀ c a, Decidable (keep c a)] :
    Isomorphic (symThree K ((P.positivePower n).select keep).realize)
      (((P.symThreePartition).positivePower n).select
        (fun c b ↦ symThreeKeep keep c ((symThreeWordEquiv (A := A) n c).symm b))).realize :=
  (isomorphic_symThreePartition_select (P.positivePower n) keep).trans
    ((reindexEquiv_symThreePartition_positivePower P n).isomorphic_select _)

end PartitionedTensor

end AlgebraicComplexity.Tensor
