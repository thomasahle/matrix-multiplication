/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Tensor.PartitionedPermutation
import AlgebraicComplexity.Tensor.PartitionedProductCore

set_option autoImplicit false

/-!
# Block selection commutes with leg permutation and with the external product

Layer 1 (`AlgebraicComplexity/Tensor/`).  `PartitionedTensor.select` filters the support and keeps
the constituent family verbatim (`Tensor/PartitionedCore.lean`), while `PartitionedTensor.permute`
and `PartitionedTensor.external` rebuild the constituents.  Because the selection never touches a
constituent, both structural operations carry a selection to a selection, and the two identities
below are equalities of partition certificates, not merely of realizations.

## Why this is what a symmetrized cut needs

A laser client cuts a partitioned power by a leg-local type condition and then symmetrizes.  The
value certificate it wants to meet is attached the other way round: it symmetrizes first and cuts
the symmetrized power.  These two identities are the whole content of "symmetrizing a cut is
cutting the symmetrization": composing them along the association of `symThreePartition` rewrites
`sym₃` of a cut certificate as a single cut of `sym₃` of the certificate, after which the two
cuts live over one parent and can be compared by ordinary selection monotonicity.

## The address bookkeeping

`PartitionedTensor.permute` transports addresses along `permuteBlockAddress`, an
`Equiv.piCongrLeft'`, whose inverse is only characterized at the permuted leg
(`permuteBlockAddress_symm_apply_apply`).  The two projection lemmas below say that this inverse
transport commutes with the two projections of a product block address; they are what makes the
support half of the external identity a `simp only`.  Both are proved by applying the equivalence
rather than by rewriting under it, since the address occurs in the type of everything around it.

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

variable {K : Type u} [CommSemiring K]
variable {A : Leg → Type w} [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]
variable {B : Leg → Type w} [∀ c, Fintype (B c)] [∀ c, DecidableEq (B c)]
variable {V : ∀ c, A c → Type (max u v)}
variable [∀ c a, AddCommMonoid (V c a)] [∀ c a, Module K (V c a)]
variable {W : ∀ c, B c → Type (max u v)}
variable [∀ c b, AddCommMonoid (W c b)] [∀ c b, Module K (W c b)]

/-! ## Inverse address transport through the two projections -/

omit [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]
  [∀ c, Fintype (B c)] [∀ c, DecidableEq (B c)] in
/-- The inverse permutation transport of a product address, read in the first factor, is the
inverse transport of its first projection. -/
theorem permuteBlockAddress_symm_fst (e : Orientation)
    (s : BlockAddress (PermutedBlockIndex e (ProductBlockIndex A B))) :
    (fun c ↦ ((permuteBlockAddress e).symm s c).1) =
      (permuteBlockAddress (A := A) e).symm (fun c ↦ (s c).1) := by
  refine (permuteBlockAddress (A := A) e).injective ?_
  rw [Equiv.apply_symm_apply]
  funext c
  rw [permuteBlockAddress_apply]
  exact congrArg Prod.fst (permuteBlockAddress_symm_apply_apply e s c)

omit [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]
  [∀ c, Fintype (B c)] [∀ c, DecidableEq (B c)] in
/-- The inverse permutation transport of a product address, read in the second factor, is the
inverse transport of its second projection. -/
theorem permuteBlockAddress_symm_snd (e : Orientation)
    (s : BlockAddress (PermutedBlockIndex e (ProductBlockIndex A B))) :
    (fun c ↦ ((permuteBlockAddress e).symm s c).2) =
      (permuteBlockAddress (A := B) e).symm (fun c ↦ (s c).2) := by
  refine (permuteBlockAddress (A := B) e).injective ?_
  rw [Equiv.apply_symm_apply]
  funext c
  rw [permuteBlockAddress_apply]
  exact congrArg Prod.snd (permuteBlockAddress_symm_apply_apply e s c)

/-! ## Selection commutes with leg permutation -/

/-- **Permuting a cut certificate cuts the permuted certificate.**

Proof sketch: `select` filters the support and copies the constituent family, and `permute`
transports addresses by `permuteBlockAddress` and rebuilds constituents from the source ones only,
so the two constituent families are literally the same function; the supports agree because
`permuteBlockAddress_apply` reads a transported address at `c` as the source address at
`e⁻¹(c)`. -/
theorem PartitionedTensor.permute_select
    (P : PartitionedTensor (K := K) (A := A) V)
    (keep : ∀ c, A c → Prop) [∀ c a, Decidable (keep c a)] (e : Orientation) :
    (P.select keep).permute e =
      (P.permute e).select (fun c a ↦ keep (e.symm c) a) := by
  classical
  apply PartitionedTensor.ext
  · ext s
    rw [PartitionedTensor.mem_permute_support, PartitionedTensor.mem_select_support,
      PartitionedTensor.mem_select_support, PartitionedTensor.mem_permute_support]
    refine and_congr_right fun _ ↦ ?_
    constructor
    · intro h c
      have hc := h (e.symm c)
      rwa [permuteBlockAddress_symm_apply_apply] at hc
    · intro h c
      obtain ⟨c', rfl⟩ : ∃ c', e.symm c' = c := ⟨e c, e.symm_apply_apply c⟩
      rw [permuteBlockAddress_symm_apply_apply]
      exact h c'
  · rfl

/-! ## Selection commutes with the external product -/

/-- **The external product of two cut certificates is a cut of the external product.**

Proof sketch: both sides keep the constituent family of `P.external Q` untouched, and an address
survives on the left exactly when each of its two projections survives its own factor, which is
the right-hand keep predicate. -/
theorem PartitionedTensor.external_select
    (P : PartitionedTensor (K := K) (A := A) V)
    (Q : PartitionedTensor (K := K) (A := B) W)
    (keepP : ∀ c, A c → Prop) [∀ c a, Decidable (keepP c a)]
    (keepQ : ∀ c, B c → Prop) [∀ c b, Decidable (keepQ c b)] :
    (P.select keepP).external (Q.select keepQ) =
      (P.external Q).select (fun c q ↦ keepP c q.1 ∧ keepQ c q.2) := by
  classical
  apply PartitionedTensor.ext
  · ext s
    rw [PartitionedTensor.mem_external_support, PartitionedTensor.mem_select_support,
      PartitionedTensor.mem_select_support, PartitionedTensor.mem_select_support,
      PartitionedTensor.mem_external_support]
    constructor
    · rintro ⟨⟨hP, hkP⟩, hQ, hkQ⟩
      exact ⟨⟨hP, hQ⟩, fun c ↦ ⟨hkP c, hkQ c⟩⟩
    · rintro ⟨⟨hP, hQ⟩, hk⟩
      exact ⟨⟨hP, fun c ↦ (hk c).1⟩, hQ, fun c ↦ (hk c).2⟩
  · rfl

end AlgebraicComplexity.Tensor
