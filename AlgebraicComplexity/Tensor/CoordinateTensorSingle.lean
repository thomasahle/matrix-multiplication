/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Tensor.Coordinates

set_option autoImplicit false

/-!
# Reading a reindexed pure basis tensor

Layer 1 (`AlgebraicComplexity/Tensor/`).  `coordinateTensorEquiv` (`Tensor/Coordinates.lean`)
identifies `(α → K) ⊗ (β → K)` with `α × β → K`, and
`coordinateTensorEquiv_single_tmul_single`
evaluates it on the tensor of two standard basis vectors.  A client that identifies one block of a
tensor square with a coordinate presentation of a block of a smaller partition composes that
evaluation with a reindexing `LinearMap.funLeft`, and there the two steps must be done together:
performed inline, the rewrite happens underneath a dependent block-space family and its motive is
not type-correct (the pair coordinate is typed by the *word* label `PositiveWord I 1`, not by the
pair of letters it reduces to).  The composite proved here mentions only plain types, so clients
apply it by unification and never build that motive.

Primary source: none; this is a coordinate-algebra convenience for the partitioned-tensor clients.
-/

namespace AlgebraicComplexity.Tensor

universe u v w y

section CoordinateTensor

variable {K : Type u} [CommRing K]

/-- **A reindexed pure basis tensor is a standard basis vector.**

`g` reads a coordinate of the target block as a pair of coordinates of the two source blocks.  If
`g` is injective and takes `j` to the pair `(a, b)`, then the tensor of the standard basis vectors
at `a` and `b`, read through the coordinate identification and reindexed along `g`, is the standard
basis vector at `j`.

Proof sketch: evaluate the coordinate identification on the pure basis tensor, then compare the two
coordinate functions pointwise; injectivity of `g` is what rules out a second index hitting the
pair. -/
theorem funLeft_coordinateTensorEquiv_single_tmul_single
    {α : Type v} {β : Type w} {γ : Type y}
    [Finite α] [Finite β] [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    (g : γ → α × β) (hg : Function.Injective g) (j : γ) (a : α) (b : β)
    (hj : g j = (a, b)) :
    LinearMap.funLeft K K g
        (coordinateTensorEquiv (K := K)
          (Pi.single a (1 : K) ⊗ₜ[K] Pi.single b (1 : K))) =
      Pi.single j (1 : K) := by
  rw [coordinateTensorEquiv_single_tmul_single]
  funext i
  rw [LinearMap.funLeft_apply]
  by_cases hi : i = j
  · subst hi
    rw [hj, Pi.single_eq_same, Pi.single_eq_same]
  · rw [Pi.single_eq_of_ne hi, Pi.single_eq_of_ne]
    intro hcontra
    exact hi (hg (hcontra.trans hj.symm))

end CoordinateTensor

end AlgebraicComplexity.Tensor
