/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.SixSymmetrizedValue
import AlgebraicComplexity.Tensor.PermutationCoherence

/-!
# `sym₃` is invariant under cyclic rotation of the legs

Layer 3 (`AlgebraicComplexity/MatrixMultiplication/`).  `MatrixMultiplication/SixSymmetrizedValue.lean`
defines `symThree K T = T ⊗ T^rot ⊗ T^{rot rot}` and proves one symmetry of it,
`Isomorphic.permute_swapXY_symThree`: for an `X`--`Y` symmetric `T`, the transposition `swapXY`
fixes `sym₃(T)`.  That statement needs a hypothesis, because `swapXY` *reverses* the cyclic order
and only a symmetric `T` repairs the reversal.

The cyclic rotations need no hypothesis at all, and that is what this module adds:

`sym₃(T^rot) ≅ sym₃(T)`  for every tensor `T`.

The reason is purely combinatorial.  `sym₃(T)` is the external product of the three cyclic images
of `T`, and rotating `T` permutes those three images cyclically:

```text
sym₃(T^c) = ( T^c ⊗ T^{c²} ) ⊗ T^{c³}  =  ( T^c ⊗ T^{c⁻¹} ) ⊗ T,
sym₃(T)   = ( T   ⊗ T^c    ) ⊗ T^{c⁻¹}.
```

So the content is a *reassociation and commutation of `Tensor.external`*, together with the two
committed orientation identities `Tensor.cycle_trans_cycle` (`c² = c⁻¹`) and `c c⁻¹ = 1`.  No new
tensor mathematics is involved.

## Why this module exists

`[DuanWuZhou2022]`'s level-two component `T_{1,1,2}` is the only one with no non-rotational value
(`second_power.tex`, `note:T112`), so every weight for it is a weight for `sym₃` of it.  Its two
orbit partners `T_{1,2,1}` and `T_{2,1,1}` are the cyclic rotations
(`cwSquareConstituent_121_isomorphic_cycleSymm`, `cwSquareConstituent_211_isomorphic_cycle`), so
without cyclic invariance a `sym₃`-weight can only ever be *stated* on the `(1,1,2)` letter, even
though it holds verbatim for the other two.  `Examples/DuanWuZhouLevelTwoLeafTauWeightOrbit.lean`
is the client that spends this.

## Principal results

* `Isomorphic.external_rotate` --- `(A ⊗ B) ⊗ C ≅ (C ⊗ A) ⊗ B`, the three-factor rotation.
* `Isomorphic.symThree_congr` --- `sym₃` is a congruence for legwise isomorphism.
* `Isomorphic.symThree_permute_cycle` and `Isomorphic.symThree_permute_cycleSymm` --- the two
  cyclic invariances, unconditionally.
* `hasTauWeight_symThree_permute_cycle_iff` and its `cycle.symm` twin --- the `HasTauWeight`
  corollaries, in both directions.

## A duplicated three-line lemma

`Isomorphic.external_comm_of_map` below is `Tensor.Isomorphic.external_comm` of
`Tensor/AsymptoticRankCalculus.lean` (line 78), with the same three-line proof from
`Tensor.map_external_comm` (`Tensor/Product.lean`, line 65).  It is restated rather than imported
because `Tensor/AsymptoticRankCalculus.lean` carries the whole asymptotic-rank calculus, none of
which is used here; the two should be merged once `external_comm` moves down to
`Tensor/Product.lean` next to the `map_` lemma it is the bundled form of.  The names are kept
distinct so that both files can coexist until then.
-/

namespace AlgebraicComplexity

open Tensor

universe u v w z

section CycleInvariance

variable {K : Type u} [CommSemiring K]
variable {V : Leg → Type v} [∀ c, AddCommMonoid (V c)] [∀ c, Module K (V c)]
variable {W : Leg → Type w} [∀ c, AddCommMonoid (W c)] [∀ c, Module K (W c)]

namespace Isomorphic

/-- **Commuting the two factors of an external product** is a legwise isomorphism.  Bundled form
of `Tensor.map_external_comm`; see the module docstring on its relation to
`Tensor.Isomorphic.external_comm`. -/
theorem external_comm_of_map (T : Tensor3 K V) (S : Tensor3 K W) :
    Isomorphic (Tensor.external T S) (Tensor.external S T) :=
  ⟨fun c ↦ TensorProduct.comm K (V c) (W c), by
    simpa [PiTensorProduct.congr] using Tensor.map_external_comm T S⟩

/-- **Rotating a left-associated triple external product**: `(A ⊗ B) ⊗ C ≅ (C ⊗ A) ⊗ B`.

Proof: `Tensor.Isomorphic.external_swap_right` exchanges the last two factors, and
`Isomorphic.external_comm_of_map` then exchanges the two inner ones. -/
theorem external_rotate {U : Leg → Type z}
    [∀ c, AddCommMonoid (U c)] [∀ c, Module K (U c)]
    (A : Tensor3 K U) (B : Tensor3 K V) (C : Tensor3 K W) :
    Isomorphic (Tensor.external (Tensor.external A B) C)
      (Tensor.external (Tensor.external C A) B) :=
  (Tensor.Isomorphic.external_swap_right A B C).trans
    ((external_comm_of_map A C).external (Tensor.Isomorphic.refl B))

/-- **`sym₃` is a congruence for legwise isomorphism.**  Each of the three cyclic images is
transported by `Tensor.Isomorphic.permute_legs`. -/
theorem symThree_congr {X : Tensor3 K V} {Y : Tensor3 K W} (h : Isomorphic X Y) :
    Isomorphic (symThree K X) (symThree K Y) :=
  ((h.external (h.permute_legs cycle)).external (h.permute_legs cycle.symm))

/-- **`sym₃(T^rot) ≅ sym₃(T)`, unconditionally.**

Unlike `Isomorphic.permute_swapXY_symThree`, no symmetry hypothesis on `T` is needed: a cyclic
rotation permutes the three factors of `sym₃` cyclically rather than reversing them.

Proof sketch: expand `sym₃(T^c)` factorwise.  Its second factor `T^{cc}` is `T^{c⁻¹}`
(`Tensor.Isomorphic.permute_cycle_cycle`) and its third factor `T^{cc⁻¹}` is `T`, so `sym₃(T^c)`
is `(T^c ⊗ T^{c⁻¹}) ⊗ T`; one `Isomorphic.external_rotate` turns that into
`(T ⊗ T^c) ⊗ T^{c⁻¹} = sym₃(T)`. -/
theorem symThree_permute_cycle (T : Tensor3 K V) :
    Isomorphic (symThree K (Tensor.permute cycle T)) (symThree K T) := by
  have h2 : Isomorphic (Tensor.permute cycle (Tensor.permute cycle T))
      (Tensor.permute cycle.symm T) := Tensor.Isomorphic.permute_cycle_cycle T
  have h3 : Isomorphic (Tensor.permute cycle.symm (Tensor.permute cycle T)) T :=
    Tensor.Isomorphic.cancel_permute_symm_left cycle T
  show Isomorphic
    (Tensor.external
      (Tensor.external (Tensor.permute cycle T)
        (Tensor.permute cycle (Tensor.permute cycle T)))
      (Tensor.permute cycle.symm (Tensor.permute cycle T))) (symThree K T)
  exact (((Tensor.Isomorphic.refl _).external h2).external h3).trans
    (external_rotate _ _ _)

/-- **`sym₃(T^{rot⁻¹}) ≅ sym₃(T)`, unconditionally.**

Instantiate `Isomorphic.symThree_permute_cycle` at `T^{c⁻¹}` and cancel `c c⁻¹`. -/
theorem symThree_permute_cycleSymm (T : Tensor3 K V) :
    Isomorphic (symThree K (Tensor.permute cycle.symm T)) (symThree K T) :=
  (symThree_permute_cycle (K := K) (Tensor.permute cycle.symm T)).symm.trans
    (symThree_congr (Tensor.Isomorphic.cancel_permute_symm_right cycle T))

end Isomorphic

/-! ## The `HasTauWeight` corollaries -/

/-- A `tau`-weight on `sym₃` of a rotated tensor is a `tau`-weight on `sym₃` of the tensor, and
conversely. -/
theorem hasTauWeight_symThree_permute_cycle_iff {T : Tensor3 K V} {τ weight : ℝ} :
    HasTauWeight K (symThree K (Tensor.permute cycle T)) τ weight ↔
      HasTauWeight K (symThree K T) τ weight :=
  ⟨fun h ↦ h.of_restricts (Isomorphic.symThree_permute_cycle T).symm.restricts,
    fun h ↦ h.of_restricts (Isomorphic.symThree_permute_cycle T).restricts⟩

/-- The `cycle.symm` twin of `hasTauWeight_symThree_permute_cycle_iff`. -/
theorem hasTauWeight_symThree_permute_cycleSymm_iff {T : Tensor3 K V} {τ weight : ℝ} :
    HasTauWeight K (symThree K (Tensor.permute cycle.symm T)) τ weight ↔
      HasTauWeight K (symThree K T) τ weight :=
  ⟨fun h ↦ h.of_restricts (Isomorphic.symThree_permute_cycleSymm T).symm.restricts,
    fun h ↦ h.of_restricts (Isomorphic.symThree_permute_cycleSymm T).restricts⟩

end CycleInvariance

end AlgebraicComplexity
