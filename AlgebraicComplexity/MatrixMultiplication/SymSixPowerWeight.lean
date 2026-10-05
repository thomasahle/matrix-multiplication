/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.SixSymmetrizedValue

/-!
# From a `sym₃`-power weight to a `sym₆`-power weight

Layer 3 (`AlgebraicComplexity/MatrixMultiplication/`).  `HasTauWeight.symSix_pow_two` squares a
`sym₃` weight into a `sym₆` weight for a *single* tensor.  A laser client works with *powers*: an
orbit certificate for a component `X` is a weight on `X^{tensor M}` read through `sym₃`, i.e. on
`Tensor.power (sym₃ X) M`, and what the six-orientation stage consumes is a weight on
`Tensor.power (sym₆ X) M`.

The two are not the same object --- `sym₆` of a power is not a power of `sym₆` on the nose --- and
the bridge between them is proved inline inside
`TauValueCertificate.term_pow_two_le_tauValue_symSix` in `SixSymmetrizedValue.lean` but is not
available as a lemma.  This module extracts it.

`hasTauWeight_power_symSix_of_power_symThree` is the statement a values lane targets: whatever
orbit certificate it produces for `Tensor.power (sym₃ X) M`, squaring it lands on
`Tensor.power (sym₆ X) M`, which is exactly one group of `M` diagonal letters of the
six-orientation partition.
-/

namespace AlgebraicComplexity

open Tensor

universe u v

variable {K : Type u} [CommSemiring K]
variable {V : Leg → Type v} [∀ c, AddCommMonoid (V c)] [∀ c, Module K (V c)]

/-- **A positive power of `sym₆` restricts onto the external square of the `sym₃` power.**

`sym₆(X) = sym₃(X) ⊗ sym₃(X)^swap`, so its `(n+1)`-st power splits factorwise
(`Isomorphic.power_external_positive`) and the swapped factor's power is the swap of the power
(`Isomorphic.power_permute_positive_unbundled`). -/
theorem restricts_power_symSix_external_power_symThree (X : Tensor3 K V) (n : ℕ) :
    Restricts (Tensor.power (symSix K X) (n + 1))
      (Tensor.external (Tensor.power (symThree K X) (n + 1))
        (Tensor.permute Tensor.swapXY (Tensor.power (symThree K X) (n + 1)))) := by
  refine ((Tensor.Isomorphic.power_external_positive (symThree K X)
    (Tensor.permute Tensor.swapXY (symThree K X)) n).trans ?_).restricts
  exact (Tensor.Isomorphic.refl _).external
    (Tensor.Isomorphic.power_permute_positive_unbundled (symThree K X) n Tensor.swapXY)

/-- **A weight on a positive power of `sym₃` squares into a weight on the same power of `sym₆`.**

This is the interface between an orbit value certificate --- which a values lane produces on
`Tensor.power (sym₃ X) M` --- and the six-orientation stage, which consumes
`Tensor.power (sym₆ X) M`.  No root is taken and the power is unchanged; only the weight is
squared, because `sym₆` is `sym₃` tensored with its `X`-`Y` swap and the swap carries the same
weight (`HasTauWeight.permute_swapXY`). -/
theorem hasTauWeight_power_symSix_of_power_symThree
    {X : Tensor3 K V} {τ value : ℝ} {M : ℕ} (hM : 0 < M)
    (h : HasTauWeight K (Tensor.power (symThree K X) M) τ value) (hvalue : 0 ≤ value) :
    HasTauWeight K (Tensor.power (symSix K X) M) τ (value ^ 2) := by
  obtain ⟨n, hn⟩ : ∃ n, M = n + 1 := ⟨M - 1, by omega⟩
  subst hn
  have hprod := h.external h.permute_swapXY hvalue hvalue
  have hpow : value * value = value ^ 2 := by ring
  rw [hpow] at hprod
  exact hprod.of_restricts (restricts_power_symSix_external_power_symThree X n)

end AlgebraicComplexity
