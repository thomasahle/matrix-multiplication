/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Tensor.PositivePowerCoarseningFiber
import AlgebraicComplexity.Tensor.PositiveWordRelation

set_option autoImplicit false

/-!
# Factorwise restrictions from a whole positive-power fiber

This layer-1 composition module turns the structural whole-fiber isomorphism into the restriction
interface used by tensor-extraction clients.  If every one-letter coarsening fiber restricts to a
chosen target tensor, then the complete fiber over any coarse word restricts to the heterogeneous
external product of the corresponding targets.

The theorem isolates the algebraic composition implicit in the exceptional `(1,1,2)` argument of
[CoppersmithWinograd1990, pp. 270--272], transcribed in
`papers/notes/MMult1987.tex:174-285`.  It is also the factorwise restriction step in Theorem
`thm:exact-nested-total-weight-leaf` of `better_bound/paper.tex:1684-1718`.  Counting and selecting
coarse words remain separate: this module assumes only the explicitly supplied one-letter
restrictions.

## Reference

- [CoppersmithWinograd1990] Don Coppersmith and Shmuel Winograd, *Matrix Multiplication via
  Arithmetic Progressions*.
-/

namespace AlgebraicComplexity.Tensor

universe u v w x y

variable {K : Type u} [CommSemiring K]
variable {A : Leg → Type w} {B : Leg → Type x}
variable [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]
variable [∀ c, Fintype (B c)] [∀ c, DecidableEq (B c)]
variable {V : ∀ c, A c → Type (max u v)}
variable [∀ c a, AddCommMonoid (V c a)] [∀ c a, Module K (V c a)]

namespace Restricts

/-- Restricting every one-letter fiber restricts a complete positive-power fiber to the
corresponding positive-word tensor.

In human-readable terms, fix three coarse label words.  Transposing them gives a word of coarse
joint addresses.  If the entire fine fiber over each joint address restricts to a target tensor,
then the entire fine word fiber restricts to the external product of those targets in precisely
the transposed order.

Proof sketch: use `Isomorphic.positivePower_coarseningFiber_positiveWordTensor` to distribute the
whole fine word fiber into the positive-word product of whole one-letter fibers.  Then apply
`Restricts.positiveWordTensor` to the supplied restriction of every factor and compose the two
relations. -/
theorem positivePower_coarseningFiber_restricts_positiveWordTensor
    (P : PartitionedTensor (K := K) (A := A) V)
    (f : ∀ c, A c → B c)
    (E : BlockAddress B → LegModuleFamily.{u, y} K)
    (S : ∀ address : BlockAddress B, Tensor3 K (E address).Space)
    (h : ∀ address : BlockAddress B,
      Restricts ((P.coarseningFiber f address).realize) (S address))
    (n : ℕ)
    (target : BlockAddress (fun c ↦ PositiveWord (B c) n)) :
    Restricts
      (((P.positivePower n).coarseningFiber
        (fun c ↦ positiveWordMap (f c) n) target).realize)
      (AlgebraicComplexity.Tensor.positiveWordTensor E S n
        ((positiveWordBlockAddressEquiv B n).symm target)) := by
  exact
    (Isomorphic.positivePower_coarseningFiber_positiveWordTensor
      P f n target).restricts.trans
    (Restricts.positiveWordTensor
      (fun _address : BlockAddress B ↦
        LegModuleFamily.of.{u, max v w} (K := K)
          (PartitionedSpace K V))
      E
      (fun address ↦ (P.coarseningFiber f address).realize)
      S h n
      ((positiveWordBlockAddressEquiv B n).symm target))

end Restricts

end AlgebraicComplexity.Tensor
