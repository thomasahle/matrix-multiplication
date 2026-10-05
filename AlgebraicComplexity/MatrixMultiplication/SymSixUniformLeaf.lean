/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.SymSixDistribution

/-!
# The uniform-leaf stage bridge

Layer 3 (`AlgebraicComplexity/MatrixMultiplication/`).  On `[DuanWuZhou2022]`'s route the hashed
object is the **plain** power `T^{tensor n}`; `sym₆` never touches it, and the sixth power of the
copy count appears only at the end because the hash produces a **uniform** leaf.

`Tensor/SymSixDistribution.lean` supplies every symmetrization law this needs --- in particular
`Isomorphic.symSix_indexedDirectSum_uniform` (`sym₆(⊕_ι L) ≅ ⊕_{ι⁶} sym₆(L)`) and
`Isomorphic.symSix_power_positive` (`sym₆(T^{⊗(n+1)}) ≅ sym₆(T)^{⊗(n+1)}`), the latter proved by
induction on the exponent.  This module adds only the two things that module does not have:

* **functoriality of `sym₃` and `sym₆` for `Restricts`.**  `SymSixDistribution` has
  `Isomorphic.symSix_congr`; a hashing stage produces a *restriction*, not an isomorphism, so the
  `Restricts` companion is what a stage transport actually consumes.  It is built from the
  committed `Restricts.external` and `Restricts.permute` (`Tensor/Restriction.lean:65`).
* **the stage transport itself**, composing the two with the functoriality.

## Correction to an earlier premise

An earlier draft of this module justified stating the distribution law as a `Restricts` by claiming
that `Tensor.permute` has no `Isomorphic` companion.  **That is false**:
`Tensor.Isomorphic.permute_legs` is committed at `Tensor/Restriction.lean:108`, and it is exactly
what lets `SymSixDistribution` state the law as an isomorphism.  The overlapping half of this
module has been dropped in favour of that stronger form; a client needing only a restriction takes
`.restricts`.

## Declared names

`Tensor.Restricts.symThree_congr`, `Tensor.Restricts.symSix_congr`,
`restricts_power_symSix_of_plainStage`.  Named `_congr` to match `Isomorphic.symSix_congr` and so
that nothing here shadows `symSix` itself.
-/

namespace AlgebraicComplexity

open Tensor

universe u v w z

section Functoriality

variable {K : Type u} [CommSemiring K]
variable {V : Leg → Type v} [∀ c, AddCommMonoid (V c)] [∀ c, Module K (V c)]
variable {W : Leg → Type z} [∀ c, AddCommMonoid (W c)] [∀ c, Module K (W c)]

/-- **`sym₃` is functorial for restrictions.**  The `Restricts` companion of
`Isomorphic.symThree_congr`: the three orientations of a restriction restrict factorwise. -/
theorem Tensor.Restricts.symThree_congr {A : Tensor3 K V} {B : Tensor3 K W}
    (h : Restricts A B) : Restricts (symThree K A) (symThree K B) := by
  show Restricts
    (Tensor.external (Tensor.external A (Tensor.permute cycle A))
      (Tensor.permute cycle.symm A))
    (Tensor.external (Tensor.external B (Tensor.permute cycle B))
      (Tensor.permute cycle.symm B))
  exact (h.external (h.permute cycle)).external (h.permute cycle.symm)

/-- **`sym₆` is functorial for restrictions.**  This is what a hashing stage needs: the stage is a
restriction, not an isomorphism, so `Isomorphic.symSix_congr` does not apply to it. -/
theorem Tensor.Restricts.symSix_congr {A : Tensor3 K V} {B : Tensor3 K W}
    (h : Restricts A B) : Restricts (symSix K A) (symSix K B) :=
  h.symThree_congr.external (h.symThree_congr.permute Tensor.swapXY)

end Functoriality

section Stage

variable {K : Type u} [CommSemiring K]
variable {V : Leg → Type v} [∀ c, AddCommMonoid (V c)] [∀ c, Module K (V c)]
variable {W : Leg → Type z} [∀ c, AddCommMonoid (W c)] [∀ c, Module K (W c)]
variable {ι : Type w} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- **The uniform-leaf stage transport.**

From a plain-power stage onto `ι` copies of one leaf `L`, the `sym₆` stage onto `ι⁶` copies of
`sym₆ L` --- the shape `Examples.exists_value_of_repairedStage_true` consumes.  Uniformity of the
leaf is essential: for a non-constant family the six-fold distribution produces cross terms
`L_{i₁} ⊗ L_{i₂}^c ⊗ ⋯` which are not `sym₆` of anything.

Every ingredient is committed: `Isomorphic.symSix_power_positive` and
`Isomorphic.symSix_indexedDirectSum_uniform` from `Tensor/SymSixDistribution.lean`, and the
`Restricts` functoriality above. -/
theorem restricts_power_symSix_of_plainStage
    {T : Tensor3 K V} {L : Tensor3 K W} (n : ℕ)
    (h : Restricts (Tensor.power T (n + 1))
      (Tensor.indexedDirectSum (V := fun _ : ι ↦ W) fun _ ↦ L)) :
    Restricts (Tensor.power (symSix K T) (n + 1))
      (Tensor.indexedDirectSum
        (fun _ : ((ι × ι) × ι) × ((ι × ι) × ι) ↦ symSix K L)) := by
  have h1 : Restricts (Tensor.power (symSix K T) (n + 1))
      (symSix K (Tensor.power T (n + 1))) :=
    (Tensor.Isomorphic.symSix_power_positive T n).symm.restricts
  have h2 : Restricts (symSix K (Tensor.power T (n + 1)))
      (symSix K (Tensor.indexedDirectSum (V := fun _ : ι ↦ W) fun _ ↦ L)) := h.symSix_congr
  have h3 := (Tensor.Isomorphic.symSix_indexedDirectSum_uniform (K := K) (ι := ι) L).restricts
  exact (h1.trans h2).trans h3

end Stage

end AlgebraicComplexity
