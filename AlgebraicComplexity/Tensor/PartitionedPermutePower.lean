/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Tensor.PartitionedBlockMapPower
import AlgebraicComplexity.Tensor.PartitionedPowerExternalInterchange
import AlgebraicComplexity.Tensor.PartitionedProductRealization
import AlgebraicComplexity.Tensor.PartitionedSelectStructure

set_option autoImplicit false

/-!
# Leg permutation commutes with the external product and with positive powers

Layer 1 (`AlgebraicComplexity/Tensor/`).  Two structural facts a symmetrized laser client needs:
permuting the legs of a partitioned external product is the external product of the permuted
factors (an equality of certificates), and consequently a leg permutation may be moved across a
positive partitioned power (a reindex equivalence with the *identity* label equivalence).

## What paper step this serves

`[duan2023faster]`, `second_power_appendix.tex:26-45` (proof of `lem:non-rot-values` (d), the
`T_{1,1,2}` restricted-splitting value; the defining cut-then-`sym₃` sentence is at `:37`) writes:
"*Let `T` be the tensor obtained from
`T_{1,1,2}^{⊗m}` by zeroing out all blocks inconsistent with the marginal distributions of
`α^{(1,1,2)}` ... Then, we take the 3-symmetrization of `T`, denoted by
`sym₃(T) = T ⊗ T^rot ⊗ T^{rot rot}`*", and then applies symmetric hashing to `sym₃(T)`.  The
paper forms `sym₃` **after** the `m`-th power and treats `sym₃(A^{⊗m})` and `(sym₃
A)^{⊗m}` as the same tensor, because in its notation both are the same product of `3m` factors
read in a different order.  In a partitioned formalization they are not the same object: their
block-label alphabets differ by the transpose of a word of triples into a triple of words.  This
module supplies the half of that identification that concerns the two rotated factors; the word
transpose itself is the committed `PartitionedTensor.reindexEquiv_positivePower_external`
(`Tensor/PartitionedPowerExternalInterchange.lean`).  Nothing here is a mathematical step of the
paper: it is the bookkeeping the paper's silent reordering costs in Lean.

## How the address transport is avoided

`PartitionedTensor.permute` transports block addresses along `permuteBlockAddress`, an
`Equiv.piCongrLeft'` whose inverse carries a genuine transport at `e (e⁻¹ c)`; the projections of
a transported product address therefore agree with the transports of its projections only
propositionally (`permuteBlockAddress_symm_fst`/`_snd`), and rewriting by that inside a constituent
fails, because the address occurs in the constituent's own type.  The proof below never rewrites
there.  It compares the two constituents **after embedding them into the ambient partitioned
spaces**, where the value lives in a space that mentions no address at all, so the correction is an
ordinary `congrArg` of `fun a ↦ map (blockInclude a) (P.constituent a)`; the unembedded equality
is then recovered by `Tensor.map_blockInclude_injective`.  This is the address-free discipline
recorded as the design finding of the block-dictionary comparison, and it removes the need to
specialise to a concrete orientation.

INTEGRATION WINDOW: the same discipline would let `Tensor/PartitionedSelectStructure.lean`'s two
projection lemmas be stated once for a general `Equiv.piCongrLeft'` rather than for
`permuteBlockAddress`.

Primary source: Ran Duan, Hongxun Wu and Renfei Zhou, *Faster Matrix Multiplication via Asymmetric
Hashing*, arXiv:2210.10173, `second_power_appendix.tex:26-45` (`lem:non-rot-values` (d)); this
module is the Lean-side bookkeeping for the symmetrization/power reordering used silently there.
-/

namespace AlgebraicComplexity.Tensor

namespace PartitionedTensor

universe u v w

variable {K : Type u} [CommSemiring K]
variable {A : Leg → Type w} [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]
variable {B : Leg → Type w} [∀ c, Fintype (B c)] [∀ c, DecidableEq (B c)]
variable {V : ∀ c, A c → Type (max u v)}
variable [∀ c a, AddCommMonoid (V c a)] [∀ c a, Module K (V c a)]
variable {W : ∀ c, B c → Type (max u v)}
variable [∀ c b, AddCommMonoid (W c b)] [∀ c b, Module K (W c b)]

/-! ## Permuting an external product -/

/-- **Permuting the legs of a partitioned external product is the external product of the permuted
factors.**  An equality of certificates: the two block alphabets and the two block-space families
are definitionally equal, since both read the source data at the leg `e⁻¹ c`.

Proof sketch: the supports agree by the two projection lemmas for inverse address transport.  For
the constituents, embed both sides into the ambient partitioned spaces --- where no address occurs
in the type --- using `Tensor.map_blockInclude_injective`; there
`map_blockInclude_permute_constituent_target` turns each embedded permuted constituent into the leg
permutation of an embedded source constituent, `map_partitionExternalEquiv_external_blocks` splits
each embedded product constituent into the two embedded factors, the two source addresses are
corrected by `congrArg` of the address-free embedding map, and `PiTensorProduct.map_reindex` and
`Tensor.permute_external` move the leg permutation across the remaining legwise map and product.
The two distribution equivalences then agree definitionally, because the ambient space of a
permuted block family at leg `c` is the ambient space of the source family at `e⁻¹ c`. -/
theorem external_permute
    (P : PartitionedTensor (K := K) (A := A) V)
    (Q : PartitionedTensor (K := K) (A := B) W) (e : Orientation) :
    (P.external Q).permute e = (P.permute e).external (Q.permute e) := by
  classical
  apply PartitionedTensor.ext
  · ext s
    simp only [PartitionedTensor.mem_permute_support, PartitionedTensor.mem_external_support,
      permuteBlockAddress_symm_fst, permuteBlockAddress_symm_snd]
  · funext s
    refine map_blockInclude_injective
      (K := K) (V := PermutedBlockSpace e (ProductBlockSpace K V W)) s ?_
    have hL := PartitionedTensor.map_blockInclude_permute_constituent_target
      (P.external Q) e s
    have hR₁ := PartitionedTensor.map_blockInclude_permute_constituent_target
      P e (fun c ↦ (s c).1)
    have hR₂ := PartitionedTensor.map_blockInclude_permute_constituent_target
      Q e (fun c ↦ (s c).2)
    have hLE : map (blockInclude (K := K) (V := ProductBlockSpace K V W)
          ((permuteBlockAddress e).symm s))
          ((P.external Q).constituent ((permuteBlockAddress e).symm s)) =
        map (fun c ↦ (partitionExternalEquiv (K := K) (V := V) (W := W) c).toLinearMap)
          (Tensor.external
            (map (blockInclude (K := K) (V := V)
                (fun c ↦ (((permuteBlockAddress e).symm s) c).1))
              (P.constituent (fun c ↦ (((permuteBlockAddress e).symm s) c).1)))
            (map (blockInclude (K := K) (V := W)
                (fun c ↦ (((permuteBlockAddress e).symm s) c).2))
              (Q.constituent (fun c ↦ (((permuteBlockAddress e).symm s) c).2)))) :=
      (map_partitionExternalEquiv_external_blocks (K := K) (V := V) (W := W)
        (fun c ↦ (((permuteBlockAddress e).symm s) c).1)
        (fun c ↦ (((permuteBlockAddress e).symm s) c).2)
        (P.constituent (fun c ↦ (((permuteBlockAddress e).symm s) c).1))
        (Q.constituent (fun c ↦ (((permuteBlockAddress e).symm s) c).2))).symm
    have hRE : map (blockInclude
          (K := K) (V := ProductBlockSpace K (PermutedBlockSpace e V) (PermutedBlockSpace e W)) s)
          (((P.permute e).external (Q.permute e)).constituent s) =
        map (fun c ↦ (partitionExternalEquiv (K := K)
            (V := PermutedBlockSpace e V) (W := PermutedBlockSpace e W) c).toLinearMap)
          (Tensor.external
            (map (blockInclude (K := K) (V := PermutedBlockSpace e V) (fun c ↦ (s c).1))
              ((P.permute e).constituent (fun c ↦ (s c).1)))
            (map (blockInclude (K := K) (V := PermutedBlockSpace e W) (fun c ↦ (s c).2))
              ((Q.permute e).constituent (fun c ↦ (s c).2)))) :=
      (map_partitionExternalEquiv_external_blocks (K := K)
        (V := PermutedBlockSpace e V) (W := PermutedBlockSpace e W)
        (fun c ↦ (s c).1) (fun c ↦ (s c).2)
        ((P.permute e).constituent (fun c ↦ (s c).1))
        ((Q.permute e).constituent (fun c ↦ (s c).2))).symm
    have hfixP := congrArg
      (fun a ↦ map (blockInclude (K := K) (V := V) a) (P.constituent a))
      (permuteBlockAddress_symm_fst (A := A) (B := B) e s)
    have hfixQ := congrArg
      (fun a ↦ map (blockInclude (K := K) (V := W) a) (Q.constituent a))
      (permuteBlockAddress_symm_snd (A := A) (B := B) e s)
    rw [hL, hLE, hRE, hR₁, hR₂, hfixP, hfixQ]
    rw [← PiTensorProduct.map_reindex
      (fun c ↦ (partitionExternalEquiv (K := K) (V := V) (W := W) c).toLinearMap) e]
    rw [Tensor.permute_external]
    rfl

/-! ## Permuting a positive power -/

/-- **A leg permutation moves across a positive partitioned power**, with the identity label
equivalence: both alphabets read as `PositiveWord (A (e⁻¹ c)) n`.  Only the block-space families
differ, and only propositionally, since both recurse on the exponent --- which is why this is a
reindex equivalence and cannot be an equation.

Proof sketch: induction on the exponent.  At `0` both sides are the permuted certificate.  At a
successor, `external_permute` splits the permuted power into the permuted prefix times the permuted
base, the inductive hypothesis handles the prefix, and the resulting label equivalence
`Equiv.prodCongr (Equiv.refl _) (Equiv.refl _)` is the identity. -/
theorem reindexEquiv_permute_positivePower
    (P : PartitionedTensor (K := K) (A := A) V) (e : Orientation) :
    ∀ n : ℕ, ((P.positivePower n).permute e).ReindexEquiv
      ((P.permute e).positivePower n) (fun _ ↦ Equiv.refl _)
  | 0 => PartitionedTensor.ReindexEquiv.refl _
  | n + 1 => by
      have hstep := (reindexEquiv_permute_positivePower P e n).external
        (PartitionedTensor.ReindexEquiv.refl (P.permute e))
      rw [← external_permute] at hstep
      refine PartitionedTensor.ReindexEquiv.congr_equiv ?_ hstep
      funext c
      apply Equiv.ext
      rintro ⟨u, a⟩
      rfl

/-! ## Transporting a block cut along a reindex equivalence -/

/-- **A reindex equivalence carries a block cut to the cut by the transported predicate.**  This is
what lets two cuts of reindex-equivalent parents be compared by ordinary selection monotonicity. -/
theorem ReindexEquiv.isomorphic_select
    {P : PartitionedTensor (K := K) (A := A) V}
    {Q : PartitionedTensor (K := K) (A := B) W}
    {e : ∀ c, A c ≃ B c} (h : P.ReindexEquiv Q e)
    (keep : ∀ c, A c → Prop) [∀ c a, Decidable (keep c a)] :
    Isomorphic (P.select keep).realize
      (Q.select (fun c b ↦ keep c ((e c).symm b))).realize := by
  classical
  obtain ⟨f, rfl⟩ := h
  rw [← PartitionedTensor.reindex_select]
  exact Isomorphic.partitionedReindex (P.select keep) e f

end PartitionedTensor

end AlgebraicComplexity.Tensor
