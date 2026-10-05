/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/
import AlgebraicComplexity.Examples.GeneralizedCoppersmithWinograd

/-!
# Border rank inside the generalized Coppersmith--Winograd family

Layer 4 (`AlgebraicComplexity/Examples/`).  This module records what the repository can and cannot
say about the border rank of the family `CW_q^σ` of [AlmanVassilevskaWilliams2018, Definition 3.1].

## Main results

* `genCW_borderRankLE_refl`: `R̲(CW_q^{id}) ≤ q + 2` for an arbitrary finite middle index type,
  transported from the classical certificate `coppersmithWinograd_borderRankLE`
  ([CoppersmithWinograd1990, §6]) along `genCW_isomorphic_congr` and
  `genCW_isomorphic_coppersmithWinograd`.
* `borderRank_genCW_refl_le`: the same, stated on `Tensor.borderRank`.
* `borderRank_coordinateTensor_gcwTable_refl_le`: the same, read on the coefficient table
  `gcwTable K μ (Equiv.refl μ)`, which is the form the Galactic-exponent value
  `galacticValue a b c F (borderRank (power (coordinateTensor T) n))` consumes.

## Why only `σ = id`: a genuine obstruction, not a gap in the formalization

[AlmanVassilevskaWilliams2018] are explicitly conditional about the family
("*if* its border rank is `q + 2`, the Coppersmith--Winograd approach would give exactly the same
bound on `ω`"), and the module doc of `Examples/GeneralizedCoppersmithWinograd.lean` records the
same reservation.  The reservation is justified: for most `σ` the bound is **false**.

Two independent reasons.

*The classical degeneration does not twist.*  The `q + 2` certificate of
[CoppersmithWinograd1990] is built from the `q` curves `(x_0 + εx_i)(y_0 + εy_i)(z_0 + εz_i)`,
whose `ε²` coefficient is `∑_i (x_i y_i z_0 + x_i y_0 z_i + x_0 y_i z_i)`, together with two
cancellation curves.  Replacing the three index bijections by `a, b, c : μ ≃ μ` gives the middle
part `∑_i (x_{a i} y_{b i} z_0 + x_{a i} y_0 z_{c i} + x_0 y_{b i} z_{c i})`, and matching it
against AVW's display forces `c = a` (from the `101` family), `c = b` (from the `011` family) and
`b = σ ∘ a` (from the `110` family), hence `σ = id`.  Twisting one leg of `CW_q` by `σ` and
untwisting the other two always restores `σ = id`, so `CW_q^σ` is not legwise isomorphic to `CW_q`
through a middle-block permutation.

*Strassen's commutation equations rule out minimal border rank.*  `CW_q^σ` is concise in
`K^{q+2} ⊗ K^{q+2} ⊗ K^{q+2}`, so `R̲(CW_q^σ) ≥ q + 2` and the claim `R̲ = q + 2` is a claim of
*minimal* border rank.  Its `Z`-slices are

```text
M_{z_0} = E_{0,q+1} + E_{q+1,0} + ∑_i E_{i,σ i},   M_{z_i} = E_{i,0} + E_{0,i},
M_{z_{q+1}} = E_{0,0},
```

and `M_{z_0}` is the permutation matrix of `π = (0 ↦ q+1, q+1 ↦ 0, i ↦ σ i)`, so the tensor is
1-generic and Strassen's equations apply: minimal border rank forces the normalized slices
`A_z = M_{z_0}^{-1} M_z` to commute.  Here `A_{z_i} = E_{σ i, 0} + E_{q+1, i}` and
`A_{z_i} A_{z_j} = [i = σ j]·E_{q+1,0}`, so

```text
[A_{z_i}, A_{z_j}] = ([i = σ j] − [j = σ i]) · E_{q+1,0},
```

which vanishes for all `i, j` exactly when `σ = σ⁻¹`.  For any `σ` that is not an involution ---
already a `3`-cycle at `q = 3` --- some commutator has rank `1`, and Strassen's bound gives
`R̲(CW_q^σ) ≥ (q+2) + 1`.

That lower bound is now proved: `Tensor/StrassenEquations.lean` and `Examples/GeneralizedCoppersmithWinogradStrassen.lean` (`borderRank_genCW_ge_of_not_involutive`) (the
lower-bound tools present are conciseness, Koszul flattenings, the substitution method and slice
rank); this module therefore only *records* the computation and proves the positive `σ = id` case.
The consequence for the barrier program is stated where it matters, in
`Examples/GeneralizedCoppersmithWinogradGalacticUpper.lean`: the by-product
`ω_g^{coord}(CW_q^σ) ≤ f(q)` is proved from a border-rank hypothesis, discharged unconditionally
for the classical member `σ = id`.

## Position in the library

Layer 4.  It imports only `Examples/GeneralizedCoppersmithWinograd.lean` (which brings the
classical `Examples/CoppersmithWinograd.lean` certificate with it).  Nothing here is imported by a
lower layer.

## References

* [AlmanVassilevskaWilliams2018] J. Alman and V. Vassilevska Williams, *Limits on all known (and
  some unknown) approaches to matrix multiplication*, arXiv:1810.08671; Definition 3.1.
* [CoppersmithWinograd1990] D. Coppersmith and S. Winograd, *Matrix multiplication via arithmetic
  progressions*, J. Symbolic Comput. 9 (1990); §6.
* [Strassen1983] V. Strassen, *Rank and optimal computation of generic tensors*, Linear Algebra
  Appl. 52/53 (1983); the commutation equations for minimal border rank.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor

universe u v

section BorderRank

variable (K : Type u) [CommRing K] (μ : Type v) [Fintype μ] [DecidableEq μ]

/-- **The classical Coppersmith--Winograd border-rank certificate, on an arbitrary middle index
type**: `R̲(CW_q^{id}) ≤ q + 2` where `q = |μ|`.

Only the *untwisted* member of [AlmanVassilevskaWilliams2018, Definition 3.1] is covered; see the
module doc for the Strassen obstruction that makes the twisted members genuinely different.

Proof sketch: `genCW_isomorphic_congr` relabels the middle block along any bijection
`μ ≃ Fin |μ|`, carrying `CW^{id}` to `CW^{id}` because `Equiv.permCongr e 1 = 1`; then
`genCW_isomorphic_coppersmithWinograd` identifies that with the repository's classical
`coppersmithWinograd K |μ|`, whose `q + 2` certificate is
`coppersmithWinograd_borderRankLE`.  Border-rank bounds transport along legwise isomorphisms
(`Tensor.BorderRankLE.isomorphic`). -/
theorem genCW_borderRankLE_refl :
    BorderRankLE (Fintype.card μ + 2) (genCW K μ (Equiv.refl μ)) := by
  classical
  set e : μ ≃ Fin (Fintype.card μ) := Fintype.equivFin μ with he
  have hperm : Equiv.permCongr e (Equiv.refl μ) = Equiv.refl (Fin (Fintype.card μ)) := by
    ext j
    simp
  have h1 : Isomorphic (genCW K μ (Equiv.refl μ))
      (genCW K (Fin (Fintype.card μ)) (Equiv.refl (Fin (Fintype.card μ)))) := by
    have := genCW_isomorphic_congr (K := K) e (Equiv.refl μ)
    rwa [hperm] at this
  have h2 : Isomorphic (genCW K μ (Equiv.refl μ)) (coppersmithWinograd K (Fintype.card μ)) :=
    h1.trans (genCW_isomorphic_coppersmithWinograd K (Fintype.card μ))
  exact (BorderRankLE.isomorphic h2).mpr (coppersmithWinograd_borderRankLE K (Fintype.card μ))

/-- `borderRank (CW_q^{id}) ≤ q + 2`, the numeric form of `genCW_borderRankLE_refl`. -/
theorem borderRank_genCW_refl_le :
    Tensor.borderRank (genCW K μ (Equiv.refl μ)) ≤ Fintype.card μ + 2 :=
  Tensor.borderRank_le_iff.mpr (genCW_borderRankLE_refl K μ)

/-- `borderRank (CW_q^{id}) ≤ q + 2` read on the coefficient table of AVW Definition 3.1, which is
the presentation the coordinate Galactic values are computed in
(`coordinateTensor_gcwTable`). -/
theorem borderRank_coordinateTensor_gcwTable_refl_le :
    Tensor.borderRank (coordinateTensor (gcwTable K μ (Equiv.refl μ))) ≤ Fintype.card μ + 2 := by
  rw [coordinateTensor_gcwTable]
  exact borderRank_genCW_refl_le K μ

end BorderRank

end AlgebraicComplexity.Examples
