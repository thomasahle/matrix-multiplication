/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.GroupTensorCWDegeneration
import AlgebraicComplexity.Examples.GeneralizedCoppersmithWinogradIndependenceLower

/-!
# Lower bounds on `Ī` for group tensors, and large tri-coloured sum-free sets

Layer 4 (`AlgebraicComplexity/Examples/`).  This module is milestone **M9** of
`BARRIER_FRAMEWORK.md`: [AlmanVassilevskaWilliams2018, Theorem 7.4], the statement that the group
tensor `T_G` of *every* finite group has asymptotic independence number `Ī(T_G) ≥ |G|^{c_{|G|}}`
for a constant `c_{|G|} > 2/3` depending only on `|G|`, together with the combinatorial consequence
that `Gⁿ` contains tri-coloured sum-free sets of size `|G|^{c_{|G|} n - o(n)}`.

## Where the two inputs come from

Nothing new is proved about tensors here; the file is a junction of two committed results.

1. **The degeneration** (`Examples/GroupTensorCWDegeneration.lean`, AVW Theorem 7.2 plus
   Corollary 4.2): for any `g ≠ 1`,
   `Ī(CW_{|G|-2}^{σ_g}) ≤ Ī(T_G)` (`asymptoticIndependenceNumber_gcwTable_le_groupCoefficients`),
   where `σ_g(h) = h⁻¹ g` on the middle block `AVWMid g = G \ {1, g}`, whose cardinality is
   `|G| - 2` (`card_AVWMid`).
2. **The lower bound on the generalized Coppersmith--Winograd family**
   (`Examples/GeneralizedCoppersmithWinogradIndependenceLower.lean`, milestones M6/M7):
   `(27/4)·q² ≤ Ī(CW_q^σ)³` for `q ≥ 1` (`easyCW_independence_base_inequality`) and its weaker
   AVW-shaped consequence `(q+2)^{2/f(q)} ≤ Ī(CW_q^σ)` for `q ≥ 2`
   (`avw_theorem_seven_three`), with `f(q) = log_q (4(q+2)³/27)`.

Composing them at `q = |G| - 2` (so that `q + 2 = |G|`, `card_avwMid_add_two`) gives everything
below.

3. **The power law** `Ī(T_G)ⁿ = Ī(T_{Gⁿ})`, which is `Tensor.coordinatePower_groupCoefficients`
   (an equality of coefficient *functions*, `T_G^{⊗n} = T_{Gⁿ}` on the nose) followed by
   `Tensor.asymptoticIndependenceNumber_coordinatePower`.  Running the composition of 1 and 2 at
   the group `Gⁿ` instead of `G` and then dividing the exponent back down is therefore **lossless**,
   and it is what removes the last two open orders; see the power-lift section below.

## Main results

* `avw_theorem_seven_four_cube` (`3 ≤ |G|`): the **cube form**, strictly stronger than AVW's
  displayed inequality,

  ```text
  (27/4)·(|G| - 2)² ≤ Ī(T_G)³.
  ```

* `avw_theorem_seven_four` (`4 ≤ |G|`): **AVW's displayed inequality**, with the constant named,

  ```text
  |G|^{2/f(|G|-2)} ≤ Ī(T_G),      f(q) = log_q (4(q+2)³/27).
  ```

* `avw_theorem_seven_four_exists` (`5 ≤ |G|`): AVW Theorem 7.4 verbatim, `∃ c > 2/3` with
  `|G|^c ≤ Ī(T_G)`, witnessed by `c = avwGroupExponent |G| = 2/f(|G|-2)`; the strict inequality
  `c > 2/3` is `avwF_lt_three`, i.e. `f(q) < 3` for `q ≥ 3`.
* `avw_theorem_seven_four_exists_of_four_le` (`4 ≤ |G|`): the same conclusion `∃ c > 2/3` from the
  cube form, one group order *below* AVW's threshold, witnessed by
  `c = avwCubeExponent |G| = log((27/4)(|G|-2)²)/(3 log |G|)`.
* `avw_theorem_seven_four_cube_pow` (`n ≠ 0`, `3 ≤ |G|ⁿ`): the **power lift**, the cube form run at
  `Gⁿ` and transported back to `G` with no loss,

  ```text
  (27/4)·(|G|ⁿ - 2)² ≤ Ī(T_G)^{3n}.
  ```

* `avw_theorem_seven_four_exists_of_two_le` (`2 ≤ |G|`): **AVW Theorem 7.4 for every nontrivial
  finite group**, with no appeal to [KleinbergSawinSpeyer2018].  The witness is
  `c = avwCubeExponent (|G|²)`, which depends only on `|G|`; the strictness `c > 2/3` is the
  existing `two_div_three_lt_avwCubeExponent` read at `m = |G|² ≥ 4`.  Together with `|G| = 1`
  (where `Ī = 1` and the statement is vacuous) this covers *all* finite groups.
* `avw_theorem_seven_four_triColoredSumFree` (`2 ≤ |G|`): the combinatorial consequence,

  ```text
  ∃ c > 2/3, ∀ ε > 0, ∃ n₀, ∀ n ≥ n₀,  |G|^{(c-ε)·n} ≤ f(Gⁿ),
  ```

  where `f` is the tri-coloured sum-free number.  This is AVW's "`Gⁿ` has a tri-coloured sum-free
  set of size at least `|G|^{c_{|G|} n - o(n)}`", with the `o(n)` made explicit.
* `asymptoticIndependenceNumber_groupCoefficients_eq_supermultiplicativeLimit`: the identification
  `Ī(T_G) = lim_n f(Gⁿ)^{1/n}` that makes the previous item a statement about tri-coloured
  sum-free sets and nothing else.  In particular the left-hand side does not depend on the
  coefficient ring.
* `le_sawinConstant`, `avw_groupCoefficients_independence_sandwich`: the comparison with the
  Section-6 barrier.  Every constant `δ` witnessing Sawin's theorem for `G` satisfies
  `(27/4)(|G|-2)² ≤ (δ|G|)³`, i.e. `δ ≥ ((27/4)(|G|-2)²)^{1/3}/|G|`; for `|G| = 4` this is the
  clean `δ ≥ 3/4` (`three_div_four_le_sawinConstant_of_card_eq_four`).
* `le_sawinConstant_pow` and its numeric corollaries: the same comparison run through the power
  lift, `(27/4)(|G|ⁿ - 2)² ≤ (δ|G|)^{3n}`, which is strictly stronger at every small order:
  `δ ≥ 0.92` for `|G| = 2`, `δ ≥ 0.876` for `|G| = 3`, `δ ≥ 0.828` for `|G| = 4`.

## Which small groups are covered

AVW dispose of the five groups of order `< 5` (`C₁`, `C₂`, `C₃`, `C₄`, `C₂²`) by citing
[KleinbergSawinSpeyer2018].  That citation is *not* reproduced as a proof here, **and it is no
longer needed for Theorem 7.4**: the power lift of the cube form covers every order.  The status of
the small cases in this tree is:

| `|G|` | what is proved here | `∃ c > 2/3, |G|^c ≤ Ī(T_G)`? | route |
| --- | --- | --- | --- |
| `1` | `Ī(T_G) = 1` | yes, vacuously: `1^c = 1` | --- |
| `2` | `3^{5/9} = 1.84109… ≤ Ī(T_{C₂}) ≤ 2` | **yes**, `c = avwCubeExponent 8 = 0.880535…` | lift, `n = 3` |
| `3` | `(1323/4)^{1/6} = 2.62985… ≤ Ī(T_G)` | **yes**, `c = avwCubeExponent 9 = 0.880105…` | lift, `n = 2` |
| `4` | `1323^{1/6} = 3.31337… ≤ Ī(T_G)` | **yes**, `c = avwCubeExponent 16 = 0.864127…` | lift, `n = 2` |
| `≥ 5` | `avw_theorem_seven_four_exists` | yes | cube form, `n = 1` |

The declarations are `asymptoticIndependenceNumber_groupCoefficients_of_card_eq_one`,
`rpow_le_asymptoticIndependenceNumber_groupCoefficients_of_card_eq_two` (with the upper half of the
order-`2` row in `asymptoticIndependenceNumber_groupCoefficients_zmod_two_mem_Icc`), and
`…_of_card_eq_three`, `…_of_card_eq_four`; each has a rational companion `rat_le_…` certifying
`1.84`, `2.629`, `3.31`.

So **no group order is left open** for AVW Theorem 7.4.  The two orders `2` and `3` that the cube
form alone cannot reach --- at `|G| = 2` it is the empty statement `0 ≤ Ī³` (the bridge degenerates,
`q = |G| - 2 = 0`), and at `|G| = 3` it gives only `c = log(27/4)/(3 log 3) = 0.5793… < 2/3` --- are
reached by running the same bridge at `G³` and `G²` and taking the exponent back down; the power law
`Ī(T_G)ⁿ = Ī(T_{Gⁿ})` makes that step lossless.  Order `4` --- both `C₄` and
`C₂²`, since nothing below uses commutativity or the isomorphism type --- was already covered by the
cube form at `n = 1` (`3 ≤ Ī`), and the lift improves it to `3.3133… ≤ Ī`.

What [KleinbergSawinSpeyer2018] still supplies, and this tree does not, are the **sharp** capacities
`Ī(T_{C₂}) = 3/2^{2/3} = 1.88988…` and `Ī(T_{C₃}) = 2.75510…`; those are *not* claimed anywhere
here.  Every bound proved below sits strictly under them, as it must.

## Errata and deviations from [AlmanVassilevskaWilliams2018]

* AVW's `c_{|G|}` is unnamed; here it is `avwGroupExponent |G| = 2/f(|G|-2)`.
* The hypothesis for AVW's own route is `|G| ≥ 5`, since `f(q) < 3` --- the source of `c > 2/3` ---
  is false at `q = 2` (`4·4³ = 256 > 216 = 27·2³`) and `f(1)` is undefined.  This is the same
  erratum recorded in `Examples/GeneralizedCoppersmithWinogradIndependenceLower.lean`.  The power
  lift sidesteps that hypothesis entirely: the cube form at `Gⁿ` needs only `|G|ⁿ ≥ 3`.
* AVW state the conclusion for the abstract tensor `T_G`; `Ī` is basis dependent, so every
  statement below is about the *coefficient table* `Tensor.groupCoefficients K G`, whose abstract
  tensor is `Tensor.groupTensor K G` (`coordinateTensor_groupCoefficients`).
* The group is taken in `Type` rather than an arbitrary universe: milestone M6
  (`easyCW_independence_base_inequality`) fixes its index type in `Type`, and `AVWMid g` lives in
  the universe of `G`.  Nothing mathematical depends on this.
* Commutativity is never used, matching `Examples/GroupTensorCWDegeneration.lean`.

## Position in the library

Layer 4.  It imports the two sibling clients named above and nothing else; nothing here is
imported by a lower layer.  The arithmetic of `f` --- `avwF_ge_two`, `avwF_pos` and
`avwF_lt_three` --- lives with `avwF` itself in
`Examples/GeneralizedCoppersmithWinogradIndependenceLower.lean`.

## References

* [AlmanVassilevskaWilliams2018] J. Alman and V. Vassilevska Williams, *Limits on all known (and
  some unknown) approaches to matrix multiplication*, arXiv:1810.08671; Theorem 7.4 (and
  Theorems 7.2, 7.3, Remark 7.2, Lemma 6.1, Corollary 6.1).
* [KleinbergSawinSpeyer2018] R. Kleinberg, W. Sawin and D. E. Speyer, *The growth rate of
  tri-colored sum-free sets*, Discrete Analysis 2018:12, arXiv:1607.00047.  Cited by AVW for the
  groups of order `< 5`; **not** formalized here, and no longer needed for Theorem 7.4 --- only for
  the sharp capacities `3/2^{2/3}` and `2.75510…`, which are not claimed.
* [CoppersmithWinograd1990] D. Coppersmith and S. Winograd, *Matrix multiplication via arithmetic
  progressions*, J. Symbolic Comput. 9 (1990); §6, the source of `f(q)`.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor Filter

universe u v

/-! ## `Ī(T_G)` is the growth rate of tri-coloured sum-free sets

AVW Lemma 6.1 (`independenceNumber_groupCoefficients`) and the group-power identification
`Tensor.coordinatePower_groupCoefficients` together say that the Fekete sequence whose limit
defines `Ī(T_G)` *is* the sequence `n ↦ f(Gⁿ)` of tri-coloured sum-free numbers.  Everything in
this section is a consequence of that one observation together with the generic Fekete engine of
`Tensor/AsymptoticIndependenceNumber.lean`; no new limit theory is developed. -/

section TriColoured

variable {K : Type u} [CommSemiring K] [Nontrivial K]
variable {G : Type v} [Group G] [Fintype G] [DecidableEq G]

/-- The Fekete sequence of the table of `T_G` is the sequence of tri-coloured sum-free numbers of
the powers of `G`: `I(T_G^{⊗n}) = f(Gⁿ)`.  This is AVW Lemma 6.1 for `Gⁿ`, repackaged as a
statement about `independenceNumberPowerSequence`. -/
theorem independenceNumberPowerSequence_groupCoefficients (n : ℕ) :
    independenceNumberPowerSequence (groupCoefficients K G) n = triColoredSumFreeNumber (Fin n → G) :=
  independenceNumber_coordinatePower_groupCoefficients (K := K) n

/-- **`Ī(T_G)` is the growth rate of tri-coloured sum-free sets in the powers of `G`**:

```text
Ī(T_G) = sup_{n ≥ 1} f(Gⁿ)^{1/n}   ( = lim_n f(Gⁿ)^{1/n} by Fekete ).
```

The right-hand side mentions neither a tensor nor the coefficient ring, so this is also the
statement that `Ī(T_G)` is independent of `K`.  The `sup` is a genuine limit by
`Tensor.tendsto_asymptoticIndependenceNumber`. -/
theorem asymptoticIndependenceNumber_groupCoefficients_eq_supermultiplicativeLimit :
    asymptoticIndependenceNumber (groupCoefficients K G) =
      Growth.supermultiplicativeLimit fun n ↦ ((triColoredSumFreeNumber (Fin n → G) : ℕ) : ℝ) := by
  simp only [asymptoticIndependenceNumber,
    independenceNumberPowerSequence_groupCoefficients (K := K)]

/-- **The upper half**: `f(Gⁿ) ≤ Ī(T_G)^n` for every `n`, with no error term at all.  This is the
form in which AVW Corollary 6.1 consumes a bound on `Ī`. -/
theorem triColoredSumFreeNumber_le_pow_asymptoticIndependenceNumber (n : ℕ) :
    ((triColoredSumFreeNumber (Fin n → G) : ℕ) : ℝ) ≤
      asymptoticIndependenceNumber (groupCoefficients K G) ^ n := by
  have h := independenceNumber_coordinatePower_le_pow_of_asymptotic
    (B := groupCoefficients K G) le_rfl n
  rwa [show independenceNumber (coordinatePower (groupCoefficients K G) n)
      = triColoredSumFreeNumber (Fin n → G) from
    independenceNumberPowerSequence_groupCoefficients (K := K) n] at h

variable [NoZeroDivisors K]

/-- **The lower half**: every `b` strictly below `Ī(T_G)` is eventually dominated, that is
`bⁿ ≤ f(Gⁿ)` for all large `n`.

Together with `triColoredSumFreeNumber_le_pow_asymptoticIndependenceNumber` this pins the growth
of `n ↦ f(Gⁿ)` to `Ī(T_G)^{n - o(n)}`, which is what AVW's "`|G|^{c n - o(n)}`" means.

Proof sketch: `Tensor.tendsto_asymptoticIndependenceNumber` (Fekete, applicable because the table
is nonzero at the all-`1` triple) makes `f(Gⁿ)^{1/n}` converge to `Ī(T_G)`, so eventually
`b < f(Gⁿ)^{1/n}`; raising to the `n`th power removes the root. -/
theorem exists_pow_le_triColoredSumFreeNumber {b : ℝ} (hb0 : 0 ≤ b)
    (hb : b < asymptoticIndependenceNumber (groupCoefficients K G)) :
    ∃ n₀ : ℕ, ∀ n, n₀ ≤ n → b ^ n ≤ ((triColoredSumFreeNumber (Fin n → G) : ℕ) : ℝ) := by
  have hne : groupCoefficients K G (fun _ ↦ (1 : G)) ≠ 0 :=
    (groupCoefficients_ne_zero_iff (K := K) _).mpr (by simp)
  have htend := tendsto_asymptoticIndependenceNumber (K := K) hne
  have hev : ∀ᶠ n in atTop,
      b < Growth.nthRootSeq
        (fun m ↦ ((independenceNumberPowerSequence (groupCoefficients K G) m : ℕ) : ℝ)) n :=
    htend.eventually_const_lt hb
  obtain ⟨n₁, hn₁⟩ := eventually_atTop.mp hev
  refine ⟨max n₁ 1, fun n hn ↦ ?_⟩
  have hn1 : n₁ ≤ n := le_trans (le_max_left _ _) hn
  have hnpos : n ≠ 0 := by
    have := le_trans (le_max_right n₁ 1) hn
    omega
  have hroot := (hn₁ n hn1).le
  set a : ℝ := ((independenceNumberPowerSequence (groupCoefficients K G) n : ℕ) : ℝ) with ha
  have ha0 : (0 : ℝ) ≤ a := by positivity
  have hcalc : b ^ n ≤ (a ^ ((n : ℝ)⁻¹)) ^ n :=
    pow_le_pow_left₀ hb0 hroot n
  rw [Real.rpow_inv_natCast_pow ha0 hnpos] at hcalc
  rw [ha, independenceNumberPowerSequence_groupCoefficients (K := K)] at hcalc
  exact hcalc

end TriColoured

/-! ## AVW Theorem 7.4

The whole content is the composition of the two committed inputs at `q = |G| - 2`.  The cube form
comes first because it is the strongest statement available and every other form is arithmetic on
top of it. -/

section TheoremSevenFour

variable {K : Type u} [CommSemiring K] [NoZeroDivisors K] [Nontrivial K]
variable {G : Type} [Group G] [Fintype G] [DecidableEq G]

/-- The parameter bookkeeping of the bridge: the middle block `G \ {1, g}` has `|G| - 2` elements,
so the target generalized Coppersmith--Winograd tensor has parameter `q` with `q + 2 = |G|`.

This is the additive form of `card_AVWMid`, obtained from `card_genCWIndex_avwMid` (which already
knows `|G| ≥ 2`) and `GenCWIndex.card`. -/
theorem card_avwMid_add_two {g : G} (hg : g ≠ 1) :
    Fintype.card (AVWMid g) + 2 = Fintype.card G := by
  have h := card_genCWIndex_avwMid hg
  rwa [GenCWIndex.card] at h

/-- **[AlmanVassilevskaWilliams2018, Theorem 7.4], cube form** --- the strongest statement proved
here.  For every finite group with `|G| ≥ 3`,

```text
(27/4)·(|G| - 2)² ≤ Ī(T_G)³.
```

Proof sketch: pick any `g ≠ 1`.  AVW Theorem 7.2 in coefficient-table form
(`asymptoticIndependenceNumber_gcwTable_le_groupCoefficients`) gives
`Ī(CW_q^{σ_g}) ≤ Ī(T_G)` for `q = |G| - 2 = |AVWMid g|`, and milestone M6
(`easyCW_independence_base_inequality`, the coordinate shadow of the three-constituent laser
analysis of [CoppersmithWinograd1990, §6]) gives `(27/4)q² ≤ Ī(CW_q^{σ_g})³`.  Cubing the first
inequality --- legitimate since `Ī ≥ 0` --- and chaining is the whole proof. -/
theorem avw_theorem_seven_four_cube (hG : 3 ≤ Fintype.card G) :
    27 / 4 * ((Fintype.card G : ℝ) - 2) ^ 2 ≤
      asymptoticIndependenceNumber (groupCoefficients K G) ^ 3 := by
  have hnt : Nontrivial G := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨g, hg⟩ := exists_ne (1 : G)
  have hcard := card_avwMid_add_two hg
  have hq : 0 < Fintype.card (AVWMid g) := by omega
  have hcast : ((Fintype.card (AVWMid g) : ℕ) : ℝ) = (Fintype.card G : ℝ) - 2 := by
    have : ((Fintype.card (AVWMid g) + 2 : ℕ) : ℝ) = (Fintype.card G : ℝ) := by
      exact_mod_cast congrArg (Nat.cast : ℕ → ℝ) hcard
    push_cast at this
    linarith
  have hbase := easyCW_independence_base_inequality K (AVWMid g) (avwPerm g) hq
  have hbridge := asymptoticIndependenceNumber_gcwTable_le_groupCoefficients (K := K) hg
  have hcubed :
      asymptoticIndependenceNumber (gcwTable K (AVWMid g) (avwPerm g)) ^ 3 ≤
        asymptoticIndependenceNumber (groupCoefficients K G) ^ 3 :=
    pow_le_pow_left₀ (asymptoticIndependenceNumber_nonneg _) hbridge 3
  rw [hcast] at hbase
  exact hbase.trans hcubed

/-- **The interface to the cube form**: any nonnegative `x` whose cube is at most
`(27/4)(|G| - 2)²` is a lower bound for `Ī(T_G)`.

This is the group-tensor analogue of `le_asymptoticIndependenceNumber_gcwTable_of_cube_le`, and
every displayed lower bound below is obtained by feeding it an explicit `x`. -/
theorem le_asymptoticIndependenceNumber_groupCoefficients_of_cube_le (hG : 3 ≤ Fintype.card G)
    {x : ℝ} (hx : x ^ 3 ≤ 27 / 4 * ((Fintype.card G : ℝ) - 2) ^ 2) :
    x ≤ asymptoticIndependenceNumber (groupCoefficients K G) :=
  le_of_pow_le_pow_left₀ (n := 3) (by norm_num) (asymptoticIndependenceNumber_nonneg _)
    (hx.trans (avw_theorem_seven_four_cube (K := K) hG))

/-- **AVW's constant `c_{|G|}`**, named: `c_m = 2 / f(m - 2)` with
`f(q) = log_q (4(q+2)³/27)`, the exponent bound of [CoppersmithWinograd1990, §6].

[AlmanVassilevskaWilliams2018, Theorem 7.4] assert only that such a constant exists and depends
only on `|G|`; this is the value their proof produces.  It exceeds `2/3` exactly when `f(|G|-2)`
is below `3`, which holds for `|G| ≥ 5` (`avwF_lt_three`). -/
noncomputable def avwGroupExponent (m : ℕ) : ℝ := 2 / avwF (m - 2)

/-- **[AlmanVassilevskaWilliams2018, Theorem 7.4], displayed form.**  For every finite group with
`|G| ≥ 4`,

```text
|G|^{c_{|G|}} ≤ Ī(T_G),      c_{|G|} = 2 / f(|G| - 2).
```

The hypothesis is `|G| ≥ 4`, i.e. `q = |G| - 2 ≥ 2`, which is what AVW Theorem 7.3 needs after the
`f(1)` erratum; the *strict* inequality `c_{|G|} > 2/3` claimed by Theorem 7.4 needs `|G| ≥ 5` and
is `two_div_three_lt_avwGroupExponent`.

Proof sketch: apply `avw_theorem_seven_three` at `μ = AVWMid g` and `σ = avwPerm g`, whose
parameter is `q = |G| - 2` with `q + 2 = |G|` (`card_avwMid_add_two`), then transport the bound
along `asymptoticIndependenceNumber_gcwTable_le_groupCoefficients` (AVW Theorem 7.2). -/
theorem avw_theorem_seven_four (hG : 4 ≤ Fintype.card G) :
    (Fintype.card G : ℝ) ^ avwGroupExponent (Fintype.card G) ≤
      asymptoticIndependenceNumber (groupCoefficients K G) := by
  have hnt : Nontrivial G := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨g, hg⟩ := exists_ne (1 : G)
  have hcard := card_avwMid_add_two hg
  have hmid : Fintype.card (AVWMid g) = Fintype.card G - 2 := card_AVWMid hg
  have hq : 2 ≤ Fintype.card (AVWMid g) := by omega
  have h73 := avw_theorem_seven_three K (AVWMid g) (avwPerm g) hq
  rw [hcard, hmid] at h73
  exact h73.trans (asymptoticIndependenceNumber_gcwTable_le_groupCoefficients (K := K) hg)

/-- **The strictness in AVW Theorem 7.4**: `c_{|G|} = 2/f(|G|-2) > 2/3` for `|G| ≥ 5`.

Proof sketch: `f(q) < 3` for `q ≥ 3` (`avwF_lt_three`) and `f(q) > 0` (`avwF_pos`), so
`2/f(q) > 2/3`. -/
theorem two_div_three_lt_avwGroupExponent {m : ℕ} (hm : 5 ≤ m) :
    2 / 3 < avwGroupExponent m := by
  have hq3 : 3 ≤ m - 2 := by omega
  have hq2 : 2 ≤ m - 2 := by omega
  have hpos : 0 < avwF (m - 2) := avwF_pos hq2
  have hlt : avwF (m - 2) < 3 := avwF_lt_three hq3
  rw [avwGroupExponent, div_lt_div_iff₀ (by norm_num) hpos]
  linarith

/-- **[AlmanVassilevskaWilliams2018, Theorem 7.4] verbatim**, for `|G| ≥ 5`:

> for every (not necessarily abelian) finite group `G` there is a constant `c_{|G|} > 2/3`,
> depending only on `|G|`, such that `Ī(T_G) ≥ |G|^{c_{|G|}}`.

The witness is `avwGroupExponent |G| = 2/f(|G|-2)`, which indeed depends only on the *cardinality*
of `G`.  AVW additionally cover `|G| < 5` by citing [KleinbergSawinSpeyer2018]; that citation is
not reproduced and is not needed: `avw_theorem_seven_four_exists_of_four_le` covers `|G| = 4`
outright, and `avw_theorem_seven_four_exists_of_two_le` covers every remaining nontrivial order
through the power lift. -/
theorem avw_theorem_seven_four_exists (hG : 5 ≤ Fintype.card G) :
    ∃ c : ℝ, 2 / 3 < c ∧
      (Fintype.card G : ℝ) ^ c ≤ asymptoticIndependenceNumber (groupCoefficients K G) :=
  ⟨avwGroupExponent (Fintype.card G), two_div_three_lt_avwGroupExponent hG,
    avw_theorem_seven_four (by omega)⟩

/-! ### The cube form beats AVW's constant, and reaches `|G| = 4`

`avw_theorem_seven_four_cube` says `Ī(T_G) ≥ ((27/4)(|G|-2)²)^{1/3}`, and that number is already
strictly above `|G|^{2/3}` as soon as `|G| ≥ 4` --- the inequality is `27(|G|-2)² > 4|G|²`, i.e.
`23|G|² - 108|G| + 108 > 0`, which holds from `|G| = 4` (`44 > 0`) on.  So the group order `4`,
which [AlmanVassilevskaWilliams2018] hand to [KleinbergSawinSpeyer2018], is covered here. -/

/-- **The exponent produced by the cube form**: `log((27/4)(m-2)²) / (3 log m)`, so that
`m^{avwCubeExponent m} = ((27/4)(m-2)²)^{1/3}` (`rpow_avwCubeExponent`).

For `m ≥ 4` it exceeds AVW's `2/3` (`two_div_three_lt_avwCubeExponent`), and at `m = 4` it is
`log 3 / log 4 = 0.7924…`, comfortably above `2/3`. -/
noncomputable def avwCubeExponent (m : ℕ) : ℝ :=
  Real.log (27 / 4 * ((m : ℝ) - 2) ^ 2) / (3 * Real.log m)

/-- The defining property of `avwCubeExponent`: `m^{avwCubeExponent m} = ((27/4)(m-2)²)^{1/3}` for
`m ≥ 3`.

Proof sketch: both sides are `exp (log((27/4)(m-2)²)/3)`, using `log m ≠ 0` (which needs `m ≥ 2`)
on the left and `(27/4)(m-2)² > 0` (which needs `m ≠ 2`) on the right. -/
theorem rpow_avwCubeExponent {m : ℕ} (hm : 3 ≤ m) :
    (m : ℝ) ^ avwCubeExponent m = (27 / 4 * ((m : ℝ) - 2) ^ 2) ^ ((1 : ℝ) / 3) := by
  have hm3 : (3 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hmpos : (0 : ℝ) < (m : ℝ) := by linarith
  have hm1 : (1 : ℝ) < (m : ℝ) := by linarith
  have hlog : Real.log m ≠ 0 := (Real.log_pos hm1).ne'
  have hA : (0 : ℝ) < 27 / 4 * ((m : ℝ) - 2) ^ 2 := by nlinarith
  rw [Real.rpow_def_of_pos hmpos, Real.rpow_def_of_pos hA, avwCubeExponent]
  congr 1
  field_simp

/-- `avwCubeExponent m > 2/3` for `m ≥ 4`: the cube-root lower bound really is a bound of the shape
demanded by [AlmanVassilevskaWilliams2018, Theorem 7.4].

Proof sketch: `3 log m > 0`, so the claim is `log((27/4)(m-2)²) > 2 log m = log (m²)`, i.e.
`(27/4)(m-2)² > m²`, i.e. `23m² - 108m + 108 > 0`, which holds from `m = 4` on. -/
theorem two_div_three_lt_avwCubeExponent {m : ℕ} (hm : 4 ≤ m) : 2 / 3 < avwCubeExponent m := by
  have hm4 : (4 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hm1 : (1 : ℝ) < (m : ℝ) := by linarith
  have hlogpos : 0 < Real.log m := Real.log_pos hm1
  have hsq : ((m : ℝ)) ^ 2 < 27 / 4 * ((m : ℝ) - 2) ^ 2 := by nlinarith
  have hlt : Real.log (((m : ℝ)) ^ 2) < Real.log (27 / 4 * ((m : ℝ) - 2) ^ 2) :=
    Real.log_lt_log (by positivity) hsq
  rw [Real.log_pow] at hlt
  rw [avwCubeExponent, lt_div_iff₀ (by linarith)]
  push_cast at hlt
  linarith

/-- **AVW Theorem 7.4 for `|G| ≥ 4`**, one group order below the threshold of
[AlmanVassilevskaWilliams2018]: there is a constant `c > 2/3`, depending only on `|G|`, with
`|G|^c ≤ Ī(T_G)`.

The witness is `avwCubeExponent |G|`, the exponent of the cube form; AVW instead cite
[KleinbergSawinSpeyer2018] at `|G| = 4`.

Proof sketch: `m^{avwCubeExponent m} = ((27/4)(m-2)²)^{1/3}` (`rpow_avwCubeExponent`), whose cube
is `(27/4)(m-2)²`, so `le_asymptoticIndependenceNumber_groupCoefficients_of_cube_le` applies with
equality in its hypothesis. -/
theorem avw_theorem_seven_four_exists_of_four_le (hG : 4 ≤ Fintype.card G) :
    ∃ c : ℝ, 2 / 3 < c ∧
      (Fintype.card G : ℝ) ^ c ≤ asymptoticIndependenceNumber (groupCoefficients K G) := by
  refine ⟨avwCubeExponent (Fintype.card G), two_div_three_lt_avwCubeExponent hG, ?_⟩
  have hA : (0 : ℝ) ≤ 27 / 4 * ((Fintype.card G : ℝ) - 2) ^ 2 := by positivity
  refine le_asymptoticIndependenceNumber_groupCoefficients_of_cube_le (K := K) (by omega) ?_
  rw [rpow_avwCubeExponent (by omega), ← Real.rpow_natCast _ 3, ← Real.rpow_mul hA]
  norm_num

/-! ### The lossless power lift: AVW Theorem 7.4 for *every* finite group

`Tensor.coordinatePower_groupCoefficients` is an equality of coefficient *functions*,
`T_G^{⊗n} = T_{Gⁿ}` on the nose, and `Tensor.asymptoticIndependenceNumber_coordinatePower` is the
power law `Ī(T^{⊗n}) = Ī(T)^n`.  Composing them, a bound proved at the group `Gⁿ` transports back
to `G` **without any loss**: running the cube form at `Gⁿ` gives
`(27/4)(|G|ⁿ - 2)² ≤ Ī(T_G)^{3n}`, and the exponent it produces for `|G|` is literally
`avwCubeExponent (|G|ⁿ)` --- the same function of one natural number, evaluated at `|G|ⁿ`, so the
existing strictness lemma `two_div_three_lt_avwCubeExponent` applies verbatim once `|G|ⁿ ≥ 4`.

Since `|G| ≥ 2` already gives `|G|² ≥ 4`, this proves AVW Theorem 7.4 for every nontrivial finite
group, and (with the vacuous `|G| = 1`) for every finite group.  [KleinbergSawinSpeyer2018] is no
longer needed for Theorem 7.4; it is still the only source for the *sharp* capacities, which are
not claimed here. -/

/-- **[AlmanVassilevskaWilliams2018, Theorem 7.4], power form.**  For every `n ≥ 1` with
`|G|ⁿ ≥ 3`,

```text
(27/4)·(|G|ⁿ - 2)² ≤ Ī(T_G)^{3n}.
```

This is `avw_theorem_seven_four_cube` applied at the group `Gⁿ = Fin n → G`, whose order is `|G|ⁿ`
(`Fintype.card_fun`), and pulled back along `Ī(T_{Gⁿ}) = Ī(T_G)^n`.  The pullback is an *equality*,
so nothing is lost; for `n = 1` the statement is the cube form itself. -/
theorem avw_theorem_seven_four_cube_pow (n : ℕ) (hn : n ≠ 0) (hG : 3 ≤ Fintype.card G ^ n) :
    27 / 4 * ((Fintype.card G : ℝ) ^ n - 2) ^ 2 ≤
      asymptoticIndependenceNumber (groupCoefficients K G) ^ (3 * n) := by
  have hcard : Fintype.card (Fin n → G) = Fintype.card G ^ n := by simp
  have h := avw_theorem_seven_four_cube (K := K) (G := Fin n → G) (by rw [hcard]; exact hG)
  rw [hcard, ← coordinatePower_groupCoefficients (K := K) (G := G) n,
    asymptoticIndependenceNumber_coordinatePower _ hn] at h
  push_cast at h
  rw [Nat.mul_comm 3 n, pow_mul]
  exact h

/-- **The interface to the power form**, mirroring
`le_asymptoticIndependenceNumber_groupCoefficients_of_cube_le`: any `x` whose `3n`-th power is at
most `(27/4)(|G|ⁿ - 2)²` is a lower bound for `Ī(T_G)`.  Every displayed numeric bound below is
obtained by feeding it an explicit `x`. -/
theorem le_asymptoticIndependenceNumber_groupCoefficients_of_pow_le (n : ℕ) (hn : n ≠ 0)
    (hG : 3 ≤ Fintype.card G ^ n) {x : ℝ}
    (hx : x ^ (3 * n) ≤ 27 / 4 * ((Fintype.card G : ℝ) ^ n - 2) ^ 2) :
    x ≤ asymptoticIndependenceNumber (groupCoefficients K G) :=
  le_of_pow_le_pow_left₀ (n := 3 * n) (Nat.mul_ne_zero (by norm_num) hn)
    (asymptoticIndependenceNumber_nonneg _)
    (hx.trans (avw_theorem_seven_four_cube_pow (K := K) n hn hG))

/-- **`avwCubeExponent (mⁿ)` is the exponent the power lift produces for `m`**:

```text
m^{avwCubeExponent (mⁿ)} = ((27/4)(mⁿ - 2)²)^{1/(3n)}.
```

No new constant is needed --- the `n`-th lift reuses the *same* function `avwCubeExponent`, only
evaluated at `mⁿ`.  Proof sketch: both sides are `exp (log((27/4)(mⁿ-2)²)/(3n))`, using
`log (mⁿ) = n log m` and `log m ≠ 0` on the left. -/
theorem rpow_avwCubeExponent_pow {m n : ℕ} (hm : 2 ≤ m) (hn : n ≠ 0) (h : 3 ≤ m ^ n) :
    (m : ℝ) ^ avwCubeExponent (m ^ n)
      = (27 / 4 * ((m : ℝ) ^ n - 2) ^ 2) ^ ((1 : ℝ) / (3 * n)) := by
  have hcast : ((m ^ n : ℕ) : ℝ) = (m : ℝ) ^ n := by push_cast; ring
  have hm2 : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hmpos : (0 : ℝ) < (m : ℝ) := by linarith
  have hlog : Real.log m ≠ 0 := (Real.log_pos (by linarith)).ne'
  have hn' : ((n : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have h3 : (3 : ℝ) ≤ (m : ℝ) ^ n := by
    have h' : ((3 : ℕ) : ℝ) ≤ ((m ^ n : ℕ) : ℝ) := by exact_mod_cast h
    rwa [hcast] at h'
  have hA : (0 : ℝ) < 27 / 4 * ((m : ℝ) ^ n - 2) ^ 2 := by nlinarith
  rw [avwCubeExponent, hcast, Real.log_pow, Real.rpow_def_of_pos hmpos, Real.rpow_def_of_pos hA]
  congr 1
  field_simp

/-- **The power lift in displayed form**: `|G|^{avwCubeExponent (|G|ⁿ)} ≤ Ī(T_G)` whenever
`n ≥ 1`, `|G| ≥ 2` and `|G|ⁿ ≥ 3`.

Proof sketch: `rpow_avwCubeExponent_pow` identifies the left-hand side with
`((27/4)(|G|ⁿ-2)²)^{1/(3n)}`, whose `3n`-th power is exactly `(27/4)(|G|ⁿ-2)²`, so
`le_asymptoticIndependenceNumber_groupCoefficients_of_pow_le` applies with equality in its
hypothesis. -/
theorem avw_theorem_seven_four_rpow_pow (n : ℕ) (hn : n ≠ 0) (hcard : 2 ≤ Fintype.card G)
    (hG : 3 ≤ Fintype.card G ^ n) :
    (Fintype.card G : ℝ) ^ avwCubeExponent (Fintype.card G ^ n) ≤
      asymptoticIndependenceNumber (groupCoefficients K G) := by
  have hA : (0 : ℝ) ≤ 27 / 4 * ((Fintype.card G : ℝ) ^ n - 2) ^ 2 := by positivity
  have hcast3 : (((3 * n : ℕ)) : ℝ) = 3 * (n : ℝ) := by push_cast; ring
  have hpow := Real.rpow_inv_natCast_pow (n := 3 * n) hA (Nat.mul_ne_zero (by norm_num) hn)
  rw [hcast3] at hpow
  refine le_asymptoticIndependenceNumber_groupCoefficients_of_pow_le (K := K) n hn hG ?_
  rw [rpow_avwCubeExponent_pow hcard hn hG, one_div]
  exact hpow.le

/-- **[AlmanVassilevskaWilliams2018, Theorem 7.4] for every nontrivial finite group.**  For
`|G| ≥ 2` there is a constant `c > 2/3`, depending only on `|G|`, with `|G|^c ≤ Ī(T_G)`.

This removes the last appeal to [KleinbergSawinSpeyer2018] from Theorem 7.4: AVW need `|G| ≥ 5`,
`avw_theorem_seven_four_exists_of_four_le` reaches `|G| = 4`, and the power lift reaches `2` and
`3`.  (`|G| = 1` is `asymptoticIndependenceNumber_groupCoefficients_of_card_eq_one`, where the
statement is vacuous because `1^c = 1`.)

The witness is `c = avwCubeExponent (|G|²)`, using `n = 2`, which is admissible for every `|G| ≥ 2`
because `|G|² ≥ 4`; it depends only on the cardinality, as AVW require.  Larger `n` can give a
*better* constant at a fixed order --- `n = 3` is optimal for `|G| = 2` --- and
`avw_theorem_seven_four_rpow_pow` exposes every `n`; the small-groups section below records the
best value at each of the orders `2, 3, 4`. -/
theorem avw_theorem_seven_four_exists_of_two_le (hG : 2 ≤ Fintype.card G) :
    ∃ c : ℝ, 2 / 3 < c ∧
      (Fintype.card G : ℝ) ^ c ≤ asymptoticIndependenceNumber (groupCoefficients K G) := by
  have h4 : 4 ≤ Fintype.card G ^ 2 := by simpa using Nat.pow_le_pow_left hG 2
  exact ⟨avwCubeExponent (Fintype.card G ^ 2), two_div_three_lt_avwCubeExponent h4,
    avw_theorem_seven_four_rpow_pow (K := K) 2 (by norm_num) hG (by omega)⟩

end TheoremSevenFour

/-! ## The combinatorial consequence: large tri-coloured sum-free sets in `Gⁿ`

This is the "in particular" of [AlmanVassilevskaWilliams2018, Theorem 7.4]. -/

section Combinatorial

variable {K : Type u} [CommSemiring K] [NoZeroDivisors K] [Nontrivial K]
variable {G : Type} [Group G] [Fintype G] [DecidableEq G]

/-- **[AlmanVassilevskaWilliams2018, Theorem 7.4], combinatorial form.**  For every finite group
with `|G| ≥ 2` there is a constant `c > 2/3`, depending only on `|G|`, such that for every `ε > 0`
all sufficiently large powers of `G` contain a tri-coloured sum-free set of size at least
`|G|^{(c - ε)n}`:

```text
∃ c > 2/3, ∀ ε > 0, ∃ n₀, ∀ n ≥ n₀,  |G|^{(c - ε)·n} ≤ f(Gⁿ).
```

This is AVW's "`Gⁿ` has a tri-coloured sum-free set of size at least `|G|^{c_{|G|} n - o(n)}`",
with the `o(n)` spelled out as an `ε`-quantifier.  The `ε` cannot be removed: `Ī` is a supremum of
`n`th roots, and the finite numbers `f(Gⁿ)` are not claimed to reach it.

Since `avw_theorem_seven_four_exists_of_two_le` covers every nontrivial order, the hypothesis is
`|G| ≥ 2`: **every** nontrivial finite group has tri-coloured sum-free sets of size
`|G|^{c n - o(n)}` with `c > 2/3`, with no appeal to [KleinbergSawinSpeyer2018].

Proof sketch: `avw_theorem_seven_four_exists_of_two_le` gives `|G|^c ≤ Ī(T_G)`; for `ε > 0` the
number `b = |G|^{c-ε}` is strictly below `|G|^c` because `|G| > 1`, hence strictly below `Ī(T_G)`,
and `exists_pow_le_triColoredSumFreeNumber` --- the Fekete limit of
`Tensor/AsymptoticIndependenceNumber.lean` read through AVW Lemma 6.1 --- turns that into
`bⁿ ≤ f(Gⁿ)` for all large `n`.  Finally `bⁿ = |G|^{(c-ε)n}`. -/
theorem avw_theorem_seven_four_triColoredSumFree (hG : 2 ≤ Fintype.card G) :
    ∃ c : ℝ, 2 / 3 < c ∧ ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ, ∀ n, n₀ ≤ n →
      (Fintype.card G : ℝ) ^ ((c - ε) * n) ≤ ((triColoredSumFreeNumber (Fin n → G) : ℕ) : ℝ) := by
  obtain ⟨c, hc, hbound⟩ := avw_theorem_seven_four_exists_of_two_le (K := ℚ) hG
  refine ⟨c, hc, fun ε hε ↦ ?_⟩
  have hcard1 : (1 : ℝ) < (Fintype.card G : ℝ) := by
    have : (2 : ℝ) ≤ (Fintype.card G : ℝ) := by exact_mod_cast hG
    linarith
  have hcard0 : (0 : ℝ) ≤ (Fintype.card G : ℝ) := by linarith
  have hlt : (Fintype.card G : ℝ) ^ (c - ε) < (Fintype.card G : ℝ) ^ c :=
    Real.rpow_lt_rpow_left_iff hcard1 |>.mpr (by linarith)
  obtain ⟨n₀, hn₀⟩ := exists_pow_le_triColoredSumFreeNumber (K := ℚ) (G := G)
    (b := (Fintype.card G : ℝ) ^ (c - ε)) (Real.rpow_nonneg hcard0 _)
    (lt_of_lt_of_le hlt hbound)
  refine ⟨n₀, fun n hn ↦ ?_⟩
  have hrw : (Fintype.card G : ℝ) ^ ((c - ε) * (n : ℝ))
      = ((Fintype.card G : ℝ) ^ (c - ε)) ^ n := by
    rw [Real.rpow_mul hcard0, Real.rpow_natCast]
  rw [hrw]
  exact hn₀ n hn

end Combinatorial

/-! ## The small groups

[AlmanVassilevskaWilliams2018] dispose of `|G| < 5` by citing [KleinbergSawinSpeyer2018].  That
reference is not formalized, and after the power lift it is not needed for Theorem 7.4 either.
The numeric bound at each small order is the power lift at its optimal `n`:

| `|G|` | `n` | `(27/4)(|G|ⁿ-2)²` | bound on `Ī(T_G)` | `c` with `|G|^c ≤ Ī` |
| --- | --- | --- | --- | --- |
| `2` | `3` | `243 = 3⁵` | `3^{5/9} = 1.84109…` | `0.880535…` |
| `3` | `2` | `1323/4` | `(1323/4)^{1/6} = 2.62985…` | `0.880105…` |
| `4` | `2` | `1323` | `1323^{1/6} = 3.31337…` | `0.864127…` |

`n = 1` is optimal from `|G| ≥ 5` on, where the plain cube form already applies.  The `c` column
is `avwCubeExponent (|G|ⁿ)`; the ceiling of this whole route is `avwCubeExponent 8 = 0.880535…`.
All three bounds sit strictly below the true capacities `3/2^{2/3} = 1.88988…` and `2.75510…` of
[KleinbergSawinSpeyer2018], as they must. -/

section SmallGroups

variable {K : Type u} [CommSemiring K] [NoZeroDivisors K] [Nontrivial K]

omit [NoZeroDivisors K] in
/-- **`|G| = 1`**: `Ī(T_G) = 1`, so AVW Theorem 7.4 holds vacuously (`1^c = 1` for every `c`).

Proof sketch: `Ī ≤ |G| = 1` by the leg-dimension bound, and `Ī ≥ I(T_G) = f(G) ≥ 1` by AVW
Lemma 6.1 and the singleton `{(1,1,1)}`. -/
theorem asymptoticIndependenceNumber_groupCoefficients_of_card_eq_one
    {G : Type v} [Group G] [Fintype G] [DecidableEq G] (hG : Fintype.card G = 1) :
    asymptoticIndependenceNumber (groupCoefficients K G) = 1 := by
  refine le_antisymm ?_ ?_
  · have h := asymptoticIndependenceNumber_le_card (groupCoefficients K G) Leg.X
    rw [show Fintype.card (GroupIndex G Leg.X) = Fintype.card G from rfl, hG] at h
    exact_mod_cast h
  · have h := independenceNumber_le_asymptoticIndependenceNumber (groupCoefficients K G)
    rw [independenceNumber_groupCoefficients (K := K)] at h
    have h1 : (1 : ℝ) ≤ ((triColoredSumFreeNumber G : ℕ) : ℝ) := by
      exact_mod_cast one_le_triColoredSumFreeNumber (G := G)
    linarith

/-- **`|G| = 2`**, the group `C₂`: the finite independence number is `1`
(`independenceNumber_groupCoefficients_zmod_two`, equivalently the Hadamard witness of
`Tensor/IndependenceNumber.lean`), and the only bounds this tree gives on the asymptotic one are
the trivial `1 ≤ Ī(T_{C₂}) ≤ 2`.

**`Ī(T_{C₂})` is still not determined here.**  Determining it is exactly the growth rate of
tri-coloured sum-free sets in `C₂ⁿ`, which is the content of [KleinbergSawinSpeyer2018] (the value
is `3/2^{2/3} = 1.88988…`) and is not formalized.  AVW Theorem 7.4 *is* now available at `|G| = 2`:
the bridge degenerates at `G` itself (`q = |G| - 2 = 0`), but not at `G³`, where `q = 6`, and the
power lift transports the resulting bound back with no loss --- see
`rpow_le_asymptoticIndependenceNumber_groupCoefficients_of_card_eq_two`, which sharpens the trivial
`1 ≤ Ī` below to `3^{5/9} = 1.84109… ≤ Ī(T_{C₂}) ≤ 2`. -/
theorem asymptoticIndependenceNumber_groupCoefficients_zmod_two_mem_Icc :
    independenceNumber (groupCoefficients ℚ (Multiplicative (ZMod 2))) = 1 ∧
      1 ≤ asymptoticIndependenceNumber (groupCoefficients ℚ (Multiplicative (ZMod 2))) ∧
      asymptoticIndependenceNumber (groupCoefficients ℚ (Multiplicative (ZMod 2))) ≤ 2 := by
  refine ⟨independenceNumber_groupCoefficients_zmod_two, ?_, ?_⟩
  · have h := independenceNumber_le_asymptoticIndependenceNumber
      (groupCoefficients ℚ (Multiplicative (ZMod 2)))
    rw [independenceNumber_groupCoefficients_zmod_two] at h
    exact_mod_cast h
  · have h := asymptoticIndependenceNumber_le_card
      (groupCoefficients ℚ (Multiplicative (ZMod 2))) Leg.X
    rw [show Fintype.card (GroupIndex (Multiplicative (ZMod 2)) Leg.X)
        = Fintype.card (Multiplicative (ZMod 2)) from rfl] at h
    simpa using h

variable {G : Type} [Group G] [Fintype G] [DecidableEq G]

/-- **`|G| = 3`**: the bridge gives `27/4 ≤ Ī(T_G)³`, that is `Ī(T_G) ≥ 1.8898…`.

This is **weaker** than AVW Theorem 7.4 asks for: their conclusion at `|G| = 3` would need
`|G|^{2/3} = 3^{2/3} ≤ Ī(T_G)`, i.e. `9 ≤ Ī(T_G)³`, and `27/4 < 9`.  The loss is real and not an
artefact of the proof: at `n = 1` the bridge runs through a generalized Coppersmith--Winograd
tensor of parameter `q = |G| - 2 = 1`.  It is not, however, fatal --- running the same bridge at
`G²`, where `q = 7`, and lifting back gives
`rpow_le_asymptoticIndependenceNumber_groupCoefficients_of_card_eq_three`,
`(1323/4)^{1/6} = 2.62985… ≤ Ī(T_G)`, which does clear `3^{2/3} = 2.08008…`. -/
theorem asymptoticIndependenceNumber_groupCoefficients_cube_of_card_eq_three
    (hG : Fintype.card G = 3) :
    27 / 4 ≤ asymptoticIndependenceNumber (groupCoefficients K G) ^ 3 := by
  have h := avw_theorem_seven_four_cube (K := K) (G := G) (by omega)
  rw [hG] at h
  norm_num at h
  exact h

/-- **`|G| = 4`**, i.e. `C₄` and `C₂²`: `3 ≤ Ī(T_G)`.

The bound is exact in the cube form: `(27/4)·(4-2)² = 27 = 3³`.  Since `3 = 4^{0.7924…}` and
`0.7924… > 2/3`, this *proves* the conclusion of [AlmanVassilevskaWilliams2018, Theorem 7.4] at
`|G| = 4`, which AVW obtain by citing [KleinbergSawinSpeyer2018].  Nothing here distinguishes the
two groups of order `4`, and nothing uses commutativity. -/
theorem three_le_asymptoticIndependenceNumber_groupCoefficients_of_card_eq_four
    (hG : Fintype.card G = 4) :
    3 ≤ asymptoticIndependenceNumber (groupCoefficients K G) := by
  refine le_asymptoticIndependenceNumber_groupCoefficients_of_cube_le (K := K) (by omega) ?_
  rw [hG]
  norm_num

/-! ### The small orders under the power lift

Each bound below is `le_asymptoticIndependenceNumber_groupCoefficients_of_pow_le` at the optimal
`n` of the table above, in two forms: the exact real root, and a rational lower bound for it
certified by exact arithmetic. -/

/-- **`|G| = 2`, lifted**: `3^{5/9} = 1.84109… ≤ Ī(T_{C₂})`.

The power lift at `n = 3` gives `(27/4)(2³-2)² = (27/4)·36 = 243 = 3⁵ ≤ Ī(T_G)⁹`, so
`Ī(T_G) ≥ 243^{1/9} = 3^{5/9}`.  This is the strongest bound the route produces at order `2`, and
it corresponds to `c = avwCubeExponent 8 = 0.880535…`; the true value `3/2^{2/3} = 1.88988…` of
[KleinbergSawinSpeyer2018] is not claimed. -/
theorem rpow_le_asymptoticIndependenceNumber_groupCoefficients_of_card_eq_two
    (hG : Fintype.card G = 2) :
    (3 : ℝ) ^ ((5 : ℝ) / 9) ≤ asymptoticIndependenceNumber (groupCoefficients K G) := by
  refine le_asymptoticIndependenceNumber_groupCoefficients_of_pow_le (K := K) 3 (by norm_num)
    (by rw [hG]; norm_num) ?_
  rw [hG, ← Real.rpow_natCast ((3 : ℝ) ^ ((5 : ℝ) / 9)) (3 * 3), ← Real.rpow_mul (by norm_num),
    show (5 : ℝ) / 9 * ((3 * 3 : ℕ) : ℝ) = ((5 : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
  norm_num

/-- **`|G| = 2`, rational certificate**: `1.84 ≤ Ī(T_{C₂})`.  The exact check is
`1.84⁹ = 241.7466… ≤ 243`. -/
theorem rat_le_asymptoticIndependenceNumber_groupCoefficients_of_card_eq_two
    (hG : Fintype.card G = 2) :
    184 / 100 ≤ asymptoticIndependenceNumber (groupCoefficients K G) := by
  refine le_asymptoticIndependenceNumber_groupCoefficients_of_pow_le (K := K) 3 (by norm_num)
    (by rw [hG]; norm_num) ?_
  rw [hG]
  norm_num

/-- **`|G| = 3`, lifted**: `(1323/4)^{1/6} = 2.62985… ≤ Ī(T_G)`.

The power lift at `n = 2` gives `(27/4)(3²-2)² = (27/4)·49 = 1323/4 ≤ Ī(T_G)⁶`.  This clears
`3^{2/3} = 2.08008…`, so it proves AVW Theorem 7.4 at order `3`, which
`asymptoticIndependenceNumber_groupCoefficients_cube_of_card_eq_three` (the unlifted `n = 1` form)
cannot.  It corresponds to `c = avwCubeExponent 9 = 0.880105…`; the true value `2.75510…` of
[KleinbergSawinSpeyer2018] is not claimed. -/
theorem rpow_le_asymptoticIndependenceNumber_groupCoefficients_of_card_eq_three
    (hG : Fintype.card G = 3) :
    ((1323 : ℝ) / 4) ^ ((1 : ℝ) / 6) ≤ asymptoticIndependenceNumber (groupCoefficients K G) := by
  refine le_asymptoticIndependenceNumber_groupCoefficients_of_pow_le (K := K) 2 (by norm_num)
    (by rw [hG]; norm_num) ?_
  rw [hG, ← Real.rpow_natCast (((1323 : ℝ) / 4) ^ ((1 : ℝ) / 6)) (3 * 2),
    ← Real.rpow_mul (by norm_num),
    show (1 : ℝ) / 6 * ((3 * 2 : ℕ) : ℝ) = 1 by push_cast; ring, Real.rpow_one]
  norm_num

/-- **`|G| = 3`, rational certificate**: `2.629 ≤ Ī(T_G)`.  The exact check is
`2.629⁶ = 330.1744… ≤ 330.75 = 1323/4`. -/
theorem rat_le_asymptoticIndependenceNumber_groupCoefficients_of_card_eq_three
    (hG : Fintype.card G = 3) :
    2629 / 1000 ≤ asymptoticIndependenceNumber (groupCoefficients K G) := by
  refine le_asymptoticIndependenceNumber_groupCoefficients_of_pow_le (K := K) 2 (by norm_num)
    (by rw [hG]; norm_num) ?_
  rw [hG]
  norm_num

/-- **`|G| = 4`, lifted**: `1323^{1/6} = 3.31337… ≤ Ī(T_G)`, an improvement on the unlifted
`3 ≤ Ī(T_G)` of `three_le_asymptoticIndependenceNumber_groupCoefficients_of_card_eq_four`.

The power lift at `n = 2` gives `(27/4)(4²-2)² = (27/4)·196 = 1323 ≤ Ī(T_G)⁶`, corresponding to
`c = avwCubeExponent 16 = 0.864127…` in place of `avwCubeExponent 4 = 0.792481…`.  Nothing here
distinguishes `C₄` from `C₂²`. -/
theorem rpow_le_asymptoticIndependenceNumber_groupCoefficients_of_card_eq_four
    (hG : Fintype.card G = 4) :
    (1323 : ℝ) ^ ((1 : ℝ) / 6) ≤ asymptoticIndependenceNumber (groupCoefficients K G) := by
  refine le_asymptoticIndependenceNumber_groupCoefficients_of_pow_le (K := K) 2 (by norm_num)
    (by rw [hG]; norm_num) ?_
  rw [hG, ← Real.rpow_natCast ((1323 : ℝ) ^ ((1 : ℝ) / 6)) (3 * 2),
    ← Real.rpow_mul (by norm_num),
    show (1 : ℝ) / 6 * ((3 * 2 : ℕ) : ℝ) = 1 by push_cast; ring, Real.rpow_one]
  norm_num

/-- **`|G| = 4`, rational certificate**: `3.31 ≤ Ī(T_G)`.  The exact check is
`3.31⁶ = 1315.128… ≤ 1323`. -/
theorem rat_le_asymptoticIndependenceNumber_groupCoefficients_of_card_eq_four
    (hG : Fintype.card G = 4) :
    331 / 100 ≤ asymptoticIndependenceNumber (groupCoefficients K G) := by
  refine le_asymptoticIndependenceNumber_groupCoefficients_of_pow_le (K := K) 2 (by norm_num)
    (by rw [hG]; norm_num) ?_
  rw [hG]
  norm_num

end SmallGroups

/-! ## Comparison with the Section-6 barrier: a lower bound on Sawin's constant

`Examples/GroupTensorBarrier.lean` proves AVW Corollary 6.1: conditionally on the named proof
obligation `SawinBound G`, `Ī(T_G) ≤ δ|G|` for the Sawin constant `δ < 1`.  Theorem 7.4 pushes
from below.  The two together sandwich `Ī(T_G)`, and --- reading the sandwich as a constraint on
`δ` --- give an unconditional *lower* bound on any admissible Sawin constant.

`SawinBound` is and remains a named proof obligation: it is never assumed below except as an
explicit hypothesis, and nothing here proves it for any group. -/

section SawinComparison

/-- **AVW Corollary 6.1 for a named constant.**  If `δ` witnesses Sawin's bound for `G` --- every
tri-coloured sum-free set of `Gⁿ` has size at most `(δ|G|)ⁿ` --- then `Ī(T_G) ≤ δ|G|`.

This is `asymptoticIndependenceNumber_groupCoefficients_le_of_sawinBound` with the existential
opened, which is what a statement *about the constant* needs.

Proof sketch: `Ī` is the supremum of the roots `I(T_G^{⊗n})^{1/n}`
(`Tensor.asymptoticIndependenceNumber_le_of_pow`), `I(T_G^{⊗n}) = f(Gⁿ)` by AVW Lemma 6.1, and
`f(Gⁿ)` is attained by an explicit set (`exists_triColoredSumFree_card_eq`) to which the
hypothesis applies.  Nonnegativity of `δ|G|` comes from `one_le_of_sawinBound`. -/
theorem asymptoticIndependenceNumber_groupCoefficients_le_of_triColoredSumFree_bound
    {K : Type u} [CommSemiring K] [Nontrivial K]
    {G : Type v} [Group G] [Fintype G] [DecidableEq G] {δ : ℝ}
    (hb : ∀ (n : ℕ) (S : Finset ((Fin n → G) × (Fin n → G) × (Fin n → G))),
      TriColoredSumFree (Fin n → G) S → (S.card : ℝ) ≤ (δ * Fintype.card G) ^ n) :
    asymptoticIndependenceNumber (groupCoefficients K G) ≤ δ * Fintype.card G := by
  classical
  have h1 : 1 ≤ δ * Fintype.card G := one_le_of_sawinBound (G := G) hb
  refine asymptoticIndependenceNumber_le_of_pow (by linarith) fun n ↦ ?_
  obtain ⟨S, hS, hcard⟩ := exists_triColoredSumFree_card_eq (G := Fin n → G)
  have hbn := hb n S hS
  rw [hcard] at hbn
  rw [independenceNumberPowerSequence_groupCoefficients (K := K)]
  exact hbn

variable {K : Type u} [CommSemiring K] [NoZeroDivisors K] [Nontrivial K]
variable {G : Type} [Group G] [Fintype G] [DecidableEq G]

/-- **A lower bound on Sawin's constant.**  If `δ` witnesses Sawin's bound for a group with
`|G| ≥ 3`, then

```text
(27/4)·(|G| - 2)² ≤ (δ·|G|)³,     equivalently   δ ≥ ((27/4)(|G|-2)²)^{1/3} / |G|.
```

Nothing conditional survives in the conclusion: this is a theorem about which constants *could*
appear in Sawin's theorem, obtained by pressing the unconditional lower bound
`avw_theorem_seven_four_cube` against the conditional upper bound of AVW Corollary 6.1.

Proof sketch: `(27/4)(|G|-2)² ≤ Ī(T_G)³` (Theorem 7.4, cube form) and `Ī(T_G) ≤ δ|G|`
(`asymptoticIndependenceNumber_groupCoefficients_le_of_triColoredSumFree_bound`); cube the
second. -/
theorem le_sawinConstant {δ : ℝ} (hG : 3 ≤ Fintype.card G)
    (hb : ∀ (n : ℕ) (S : Finset ((Fin n → G) × (Fin n → G) × (Fin n → G))),
      TriColoredSumFree (Fin n → G) S → (S.card : ℝ) ≤ (δ * Fintype.card G) ^ n) :
    27 / 4 * ((Fintype.card G : ℝ) - 2) ^ 2 ≤ (δ * Fintype.card G) ^ 3 := by
  have hupper : asymptoticIndependenceNumber (groupCoefficients ℚ G) ≤ δ * Fintype.card G :=
    asymptoticIndependenceNumber_groupCoefficients_le_of_triColoredSumFree_bound (K := ℚ) hb
  refine (avw_theorem_seven_four_cube (K := ℚ) hG).trans ?_
  exact pow_le_pow_left₀ (asymptoticIndependenceNumber_nonneg _) hupper 3

/-- The same lower bound on Sawin's constant in root form:
`((27/4)(|G|-2)²)^{1/3} ≤ δ·|G|` for `|G| ≥ 3`. -/
theorem rpow_le_sawinConstant_mul_card {δ : ℝ} (hG : 3 ≤ Fintype.card G)
    (hb : ∀ (n : ℕ) (S : Finset ((Fin n → G) × (Fin n → G) × (Fin n → G))),
      TriColoredSumFree (Fin n → G) S → (S.card : ℝ) ≤ (δ * Fintype.card G) ^ n) :
    (27 / 4 * ((Fintype.card G : ℝ) - 2) ^ 2) ^ ((1 : ℝ) / 3) ≤ δ * Fintype.card G := by
  have h1 : 1 ≤ δ * Fintype.card G := one_le_of_sawinBound (G := G) hb
  have hcube := le_sawinConstant hG hb
  have hmono := Real.rpow_le_rpow (by positivity) hcube (by norm_num : (0 : ℝ) ≤ 1 / 3)
  have hid : ((δ * Fintype.card G) ^ (3 : ℕ)) ^ ((1 : ℝ) / 3) = δ * Fintype.card G := by
    rw [one_div, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num,
      Real.pow_rpow_inv_natCast (by linarith) (by norm_num)]
  rwa [hid] at hmono

/-- **The sandwich for `Ī(T_G)`**, `|G| ≥ 3`, conditional on the named proof obligation
`SawinBound G`:

```text
((27/4)(|G| - 2)²)^{1/3} ≤ Ī(T_G) ≤ δ·|G|,     δ < 1.
```

The lower half is unconditional (AVW Theorem 7.4, cube form); the upper half is AVW Corollary 6.1
and is the only place where `SawinBound G` --- never an axiom, never an instance --- is used.  The
resulting constraint on `δ` is `le_sawinConstant`. -/
theorem avw_groupCoefficients_independence_sandwich {F : Type u} [Field F]
    (hG : 3 ≤ Fintype.card G) (h : SawinBound G) :
    ∃ δ : ℝ, δ < 1 ∧
      27 / 4 * ((Fintype.card G : ℝ) - 2) ^ 2 ≤
        asymptoticIndependenceNumber (groupCoefficients F G) ^ 3 ∧
      asymptoticIndependenceNumber (groupCoefficients F G) ≤ δ * Fintype.card G ∧
      27 / 4 * ((Fintype.card G : ℝ) - 2) ^ 2 ≤ (δ * Fintype.card G) ^ 3 := by
  obtain ⟨δ, hδ, _, hupper⟩ :=
    asymptoticIndependenceNumber_groupCoefficients_le_of_sawinBound (K := F) h
  refine ⟨δ, hδ, avw_theorem_seven_four_cube (K := F) hG, hupper, ?_⟩
  exact (avw_theorem_seven_four_cube (K := F) hG).trans
    (pow_le_pow_left₀ (asymptoticIndependenceNumber_nonneg _) hupper 3)

/-- **The numeric instance at `|G| = 4`**: every constant `δ` witnessing Sawin's theorem for a
group of order `4` satisfies `δ ≥ 3/4`.

The cube form is exact here, `(27/4)(4-2)² = 27 = 3³`, so the constraint `27 ≤ (4δ)³` is
`3 ≤ 4δ`.  Combined with `δ < 1` this pins any Sawin constant for `C₄` or `C₂²` into `[3/4, 1)`.
The power lift sharpens `3/4` to `0.828` (`rat_le_sawinConstant_of_card_eq_four`). -/
theorem three_div_four_le_sawinConstant_of_card_eq_four {δ : ℝ} (hG : Fintype.card G = 4)
    (hb : ∀ (n : ℕ) (S : Finset ((Fin n → G) × (Fin n → G) × (Fin n → G))),
      TriColoredSumFree (Fin n → G) S → (S.card : ℝ) ≤ (δ * Fintype.card G) ^ n) :
    3 / 4 ≤ δ := by
  have h1 : 1 ≤ δ * Fintype.card G := one_le_of_sawinBound (G := G) hb
  have hcube := le_sawinConstant (by omega) hb
  rw [hG] at hcube h1
  have h3 : (3 : ℝ) ^ 3 ≤ (δ * 4) ^ 3 := by push_cast at hcube ⊢; linarith
  have := le_of_pow_le_pow_left₀ (n := 3) (by norm_num) (by push_cast at h1 ⊢; linarith) h3
  linarith

/-! ### The Sawin constant under the power lift

`le_sawinConstant` presses the cube form at `G` against AVW Corollary 6.1.  Pressing the *power*
form instead --- the upper bound `Ī(T_G) ≤ δ|G|` is a statement about `G` itself, so it may be
raised to any power for free --- gives a strictly stronger constraint at every small order. -/

/-- **A lower bound on Sawin's constant, power form.**  If `δ` witnesses Sawin's bound for `G` and
`|G|ⁿ ≥ 3` with `n ≥ 1`, then

```text
(27/4)·(|G|ⁿ - 2)² ≤ (δ·|G|)^{3n}.
```

At `n = 1` this is `le_sawinConstant`.  Nothing conditional survives in the conclusion: it is a
theorem about which constants *could* appear in Sawin's theorem.

Proof sketch: `avw_theorem_seven_four_cube_pow` bounds `Ī(T_G)^{3n}` from below, and
`asymptoticIndependenceNumber_groupCoefficients_le_of_triColoredSumFree_bound` bounds `Ī(T_G)` from
above by `δ|G|`; raise the second to the power `3n`. -/
theorem le_sawinConstant_pow {δ : ℝ} (n : ℕ) (hn : n ≠ 0) (hG : 3 ≤ Fintype.card G ^ n)
    (hb : ∀ (m : ℕ) (S : Finset ((Fin m → G) × (Fin m → G) × (Fin m → G))),
      TriColoredSumFree (Fin m → G) S → (S.card : ℝ) ≤ (δ * Fintype.card G) ^ m) :
    27 / 4 * ((Fintype.card G : ℝ) ^ n - 2) ^ 2 ≤ (δ * Fintype.card G) ^ (3 * n) := by
  have hupper : asymptoticIndependenceNumber (groupCoefficients ℚ G) ≤ δ * Fintype.card G :=
    asymptoticIndependenceNumber_groupCoefficients_le_of_triColoredSumFree_bound (K := ℚ) hb
  refine (avw_theorem_seven_four_cube_pow (K := ℚ) n hn hG).trans ?_
  exact pow_le_pow_left₀ (asymptoticIndependenceNumber_nonneg _) hupper (3 * n)

/-- **The small-order lifts, in one piece.**  At a group of order `c`, pressing the power form
`le_sawinConstant_pow` at exponent `n` against a rational `threshold` whose `3n`-th power still
fits under `(27/4)(cⁿ - 2)²` forces `threshold ≤ δ`.

Everything except `hnumeric` is uniform in the three instances below, and `hnumeric` is a closed
numerical inequality discharged by `norm_num`.

Proof sketch: `le_sawinConstant_pow` bounds `(δ|G|)^{3n}` from below, `hnumeric` inserts
`(threshold·c)^{3n}` under it, and `le_of_pow_le_pow_left₀` removes the common exponent; the
remaining factor `c > 0` cancels. -/
private theorem le_sawinConstant_of_pow_le {δ threshold : ℝ} {c n : ℕ}
    (hG : Fintype.card G = c) (hn : n ≠ 0) (hc : 3 ≤ c ^ n)
    (hnumeric : (threshold * (c : ℝ)) ^ (3 * n) ≤ 27 / 4 * ((c : ℝ) ^ n - 2) ^ 2)
    (hb : ∀ (m : ℕ) (S : Finset ((Fin m → G) × (Fin m → G) × (Fin m → G))),
      TriColoredSumFree (Fin m → G) S → (S.card : ℝ) ≤ (δ * Fintype.card G) ^ m) :
    threshold ≤ δ := by
  have h1 : 1 ≤ δ * Fintype.card G := one_le_of_sawinBound (G := G) hb
  have hpow := le_sawinConstant_pow (δ := δ) n hn (by rw [hG]; exact hc) hb
  rw [hG] at hpow h1
  have hδ : (0 : ℝ) ≤ δ * (c : ℝ) := by linarith
  have hle := le_of_pow_le_pow_left₀ (n := 3 * n) (by omega) hδ (hnumeric.trans hpow)
  have hc0 : (0 : ℕ) < c :=
    Nat.pos_of_ne_zero (by rintro rfl; rw [zero_pow hn] at hc; omega)
  exact le_of_mul_le_mul_right hle (by exact_mod_cast hc0)

/-- **`|G| = 2`**: every Sawin constant for `C₂` satisfies `δ ≥ 0.92`.

The lift at `n = 3` forces `243 ≤ (2δ)⁹`, and `1.84⁹ = 241.7466… ≤ 243`, so `2δ ≥ 1.84`.  Combined
with `δ < 1` this pins any Sawin constant for `C₂` into `[0.92, 1)`; the exact threshold the route
gives is `3^{5/9}/2 = 0.920546…`.  This is the first constraint on `δ` available at order `2` ---
`le_sawinConstant` is empty there, since `(27/4)(2-2)² = 0`. -/
theorem rat_le_sawinConstant_of_card_eq_two {δ : ℝ} (hG : Fintype.card G = 2)
    (hb : ∀ (m : ℕ) (S : Finset ((Fin m → G) × (Fin m → G) × (Fin m → G))),
      TriColoredSumFree (Fin m → G) S → (S.card : ℝ) ≤ (δ * Fintype.card G) ^ m) :
    92 / 100 ≤ δ :=
  le_sawinConstant_of_pow_le (n := 3) hG (by norm_num) (by norm_num) (by norm_num) hb

/-- **`|G| = 3`**: every Sawin constant for `C₃` satisfies `δ ≥ 0.876`.

The lift at `n = 2` forces `1323/4 ≤ (3δ)⁶`, and `2.628⁶ = 329.4216… ≤ 330.75`, so `3δ ≥ 2.628`.
The exact threshold the route gives is `(1323/4)^{1/6}/3 = 0.876617…`, well above the
`((27/4)·1)^{1/3}/3 = 0.629960…` of the unlifted `le_sawinConstant`. -/
theorem rat_le_sawinConstant_of_card_eq_three {δ : ℝ} (hG : Fintype.card G = 3)
    (hb : ∀ (m : ℕ) (S : Finset ((Fin m → G) × (Fin m → G) × (Fin m → G))),
      TriColoredSumFree (Fin m → G) S → (S.card : ℝ) ≤ (δ * Fintype.card G) ^ m) :
    876 / 1000 ≤ δ :=
  le_sawinConstant_of_pow_le (n := 2) hG (by norm_num) (by norm_num) (by norm_num) hb

/-- **`|G| = 4`**: every Sawin constant for `C₄` or `C₂²` satisfies `δ ≥ 0.828`, improving the
`δ ≥ 3/4` of `three_div_four_le_sawinConstant_of_card_eq_four`.

The lift at `n = 2` forces `1323 ≤ (4δ)⁶`, and `3.312⁶ = 1319.9028… ≤ 1323`, so `4δ ≥ 3.312`.  The
exact threshold the route gives is `1323^{1/6}/4 = 0.828343…`. -/
theorem rat_le_sawinConstant_of_card_eq_four {δ : ℝ} (hG : Fintype.card G = 4)
    (hb : ∀ (m : ℕ) (S : Finset ((Fin m → G) × (Fin m → G) × (Fin m → G))),
      TriColoredSumFree (Fin m → G) S → (S.card : ℝ) ≤ (δ * Fintype.card G) ^ m) :
    828 / 1000 ≤ δ :=
  le_sawinConstant_of_pow_le (n := 2) hG (by norm_num) (by norm_num) (by norm_num) hb

end SawinComparison

end AlgebraicComplexity.Examples
