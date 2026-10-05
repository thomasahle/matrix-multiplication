/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Combinatorics.WordType
import AlgebraicComplexity.Tensor.PartitionedPower
import AlgebraicComplexity.Tensor.PartitionedPowerRelabeling

set_option autoImplicit false

/-!
# Transporting a reference word onto every word of its type

Layer 3 (`AlgebraicComplexity/MatrixMultiplication/`).  `WordType.positionPermOfSameMultiplicity`
(`Combinatorics/WordType.lean:217`) turns an equality of letter multiplicities into a permutation
of positions.  `Tensor.Isomorphic.positivePower_constituent_of_same_type`
(`MatrixMultiplication/PartitionedTypeAssembly.lean:86`) already uses it, and its proof establishes

`positiveWordPositionEquiv P.support r e.symm left = right`

at `:109` --- and then discards it, keeping only the constituent isomorphism.  That discarded fact
is exactly what a *reference frame* needs: a single reference word together with, for every word of
the same type, a position permutation carrying the reference onto it.  This module exports it, and
packages the family form that `[duan2023faster]` §6.3's localized stage binds as `perm`/`hperm`.

## Why the family form is the useful one

The section 6.3 stage identifies every retained copy with **one** reference leaf through a position
relabeling, so it binds a family `perm : retained → Equiv.Perm (Fin (n + 1))` together with the
requirement that `perm a` carry the reference word onto the address of `a`.  Producing that family
needs nothing beyond one same-type witness per index, which is what
`exists_perm_positiveSupportWordBlockAddress` takes; the permutations themselves are then chosen by
`Classical.choice` through `choose`.

Nothing here mentions a hash, a hole, or a distribution: it is the statement that the symmetric
group acts transitively on each multiplicity class, pushed through
`positiveSupportWordBlockAddress`.

Exact source lines: `papers/sources/2210.10173/global_value.tex:332-378` (§6.3).
-/

namespace AlgebraicComplexity

open Tensor

universe u v w

/-! ## The word-level transport -/

section Words

variable {I : Type w} [Fintype I]

/-- **Two positive words with the same letter type differ by a permutation of positions.**

The export of the `have` at `PartitionedTypeAssembly.lean:109`; the proof body is that one,
verbatim. -/
theorem exists_positiveWordPositionEquiv_of_multiplicity_eq {r : ℕ}
    (left right : PositiveWord I r)
    (htype : WordType.multiplicity (positiveWordEquiv I r left) =
      WordType.multiplicity (positiveWordEquiv I r right)) :
    ∃ e : Equiv.Perm (Fin (r + 1)), positiveWordPositionEquiv I r e left = right := by
  classical
  let leftFunction := positiveWordEquiv I r left
  let rightFunction := positiveWordEquiv I r right
  let e := WordType.positionPermOfSameMultiplicity leftFunction rightFunction htype
  have he : rightFunction ∘ e = leftFunction :=
    WordType.positionPermOfSameMultiplicity_map leftFunction rightFunction htype
  have he' : leftFunction ∘ e.symm = rightFunction := by
    funext i
    have hi := congrFun he (e.symm i)
    simpa [Function.comp_apply] using hi.symm
  refine ⟨e.symm, ?_⟩
  apply (positiveWordEquiv I r).injective
  rw [positiveWordEquiv_position_apply]
  exact he'

end Words

/-! ## The block-address form, and the reference frame -/

section Addresses

variable {A : Leg → Type w}

/-- The same transport, read on block addresses. -/
theorem exists_positiveSupportWordBlockAddress_position
    (support : Finset (BlockAddress A)) (n : ℕ) (wRef w : PositiveWord support n)
    (htype : WordType.multiplicity (positiveWordEquiv (support : Type w) n wRef) =
      WordType.multiplicity (positiveWordEquiv (support : Type w) n w)) :
    ∃ e : Equiv.Perm (Fin (n + 1)),
      positiveSupportWordBlockAddress support n
          (positiveWordPositionEquiv (support : Type w) n e wRef) =
        positiveSupportWordBlockAddress support n w := by
  obtain ⟨e, he⟩ := exists_positiveWordPositionEquiv_of_multiplicity_eq wRef w htype
  exact ⟨e, by rw [he]⟩

/-- **The reference frame.**

One same-type witness per index is enough to produce the whole family of position permutations
carrying `wRef` onto the prescribed addresses.  This is the shape `[duan2023faster]` §6.3's
localized stage binds as `perm` together with `hperm`. -/
theorem exists_perm_positiveSupportWordBlockAddress
    (support : Finset (BlockAddress A)) (n : ℕ) (wRef : PositiveWord support n)
    {ι : Type v} (target : ι → BlockAddress fun c ↦ PositiveWord (A c) n)
    (hwitness : ∀ a : ι, ∃ w : PositiveWord support n,
      WordType.multiplicity (positiveWordEquiv (support : Type w) n wRef) =
          WordType.multiplicity (positiveWordEquiv (support : Type w) n w) ∧
        positiveSupportWordBlockAddress support n w = target a) :
    ∃ perm : ι → Equiv.Perm (Fin (n + 1)), ∀ a : ι,
      positiveSupportWordBlockAddress support n
          (positiveWordPositionEquiv (support : Type w) n (perm a) wRef) = target a := by
  classical
  choose w htype haddress using hwitness
  choose perm hperm using fun a : ι ↦
    exists_positiveWordPositionEquiv_of_multiplicity_eq wRef (w a) (htype a)
  exact ⟨perm, fun a ↦ by rw [hperm a, haddress a]⟩

end Addresses

end AlgebraicComplexity
