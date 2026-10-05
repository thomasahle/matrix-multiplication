/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.GeneralizedCoppersmithWinograd
import AlgebraicComplexity.MatrixMultiplication.CornerBarrier
import AlgebraicComplexity.Tensor.IndependenceMeasure
import AlgebraicComplexity.Tensor.IndependenceSplitting
import AlgebraicComplexity.Analysis.Log
import AlgebraicComplexity.Analysis.LogConstants
import AlgebraicComplexity.Analysis.RpowInequalities

/-!
# The Galactic barrier for generalized Coppersmith--Winograd tensors

This file is milestone **K** of `BARRIER_FRAMEWORK.md`: **Lemma 7.1, both proofs of Lemma 7.2, and
the headline Theorem 7.1**
of

> J. Alman and V. Vassilevska Williams, *Limits on All Known (and Some Unknown) Approaches to
> Matrix Multiplication*, arXiv:1810.08671 (local copy `papers/1810.08671v1.pdf`), Section 7.1.

Everything below is about the literal coefficient table of AVW **Definition 3.1**, `CW_q^σ`,
formalized in `Examples/GeneralizedCoppersmithWinograd.lean` as `genCW K μ σ` with middle block
indexed by `μ` (so `q = |μ|`).

Lemma 7.2 handles the large parameters and is proved twice; Lemma 7.1 handles every parameter but
with a `q`-dependent constant; Theorem 7.1 glues them into a single universal constant valid for
every `q` and every `σ` with no hypothesis at all.  All three are proved here, and the certificate
side condition of AVW Corollary 4.3 is discharged.

AVW give two proofs of Lemma 7.2, and both are formalized here.  **Route 1** (Theorem 5.3, the
three-part cover) is stated for `q ≥ 24` and yields the constant `2000/999`; **route 2**
(Theorem 5.1, the two-step splitting at `x₀` and then at `y₀`) reaches `q ≥ 6`, at the price of
the weaker constant `60000/29999`.  The two are combined in `avw_lemma_seven_two_min_of_six_le`.
**Lemma 7.1** (Corollary 5.1, the two corner terms) is proved for *every* parameter with the
constant `6/(3 - cornerExponent (q+2))`, and **Theorem 7.1** takes the minimum; see the section
"AVW Theorem 7.1: the universal constant" below.

**The sharpened Theorem 7.1.**  The last two sections replace AVW's own inputs by Alman's
block-entropy bound `Ī(CW_q^σ) ≤ u^{1/3}(q + u + 1/u)` [Alman2019, §5.5.1], raising the universal
constant from `2.0000666…` to `2.027078…`:

* `gcw_entropy_rpow_bound` certifies the *uniform* exponent `93/100`, i.e. that the rational
  near-optimizer `u_q = 2/(q+2)` gives `u_q^{1/3}(q + u_q + 1/u_q) ≤ (q+2)^{93/100}` for every
  `q ≥ 1`.  This is pure real arithmetic and mentions no tensor.
* `six_div_le_coordinateGalacticExponent_gcwTable_entropy` turns it into the uniform Galactic
  constant `600/293 = 2.04778…` for every `q ≥ 1`, and `avwTheoremSevenOneSharpConstant` takes the
  minimum with the single remaining corner constant `6/(3 - cornerExponent 2) = 2.027078…` at
  `q = 0`, which is the binding branch (`avwTheoremSevenOneSharpConstant_eq`,
  `two_add_le_avwTheoremSevenOneSharpConstant : 2 + 27/1000 ≤ c`).

Because `Examples/GeneralizedCoppersmithWinogradIndependenceUpper.lean` --- where the
block-entropy bound is proved --- is *downstream* of this module, the entropy bound is carried as
an explicit hypothesis by `six_div_le_coordinateGalacticExponent_gcwTable_entropy`,
`avw_theorem_seven_one_sharp` and `avw_theorem_seven_one_exists_sharp`; it is discharged
downstream by `asymptoticIndependenceNumber_gcwTable_le_rpow_mul`, whose statement is exactly the
hypothesis shape used here.

The chain of route 1, with the AVW numbering of each link:

1. **The `§7` cover.**  The `3q + 3` terms of `CW_q^σ` are covered by three parts `T₁, T₂, T₃`,
   each of which uses only *one* variable of one of the three types (`gcwPart`, `gcwPart_cover`).
   Their minimal variable sets have sizes `1, q+1, q+1` in some order
   (`card_minimalLegSet_gcwPart`), so `μ(T₁) = μ(T₂) = μ(T₃) = (q+1)²`
   (`coordinateMeasure_gcwPart`, AVW **Definition 5.2**).
2. **AVW Theorem 5.3** (`Tensor.asymptoticIndependenceNumber_le_sum_rpow_coordinateMeasure_of_cover`)
   turns the cover into `Ī(CW_q^σ) ≤ 3·((q+1)²)^{1/3} = 3(q+1)^{2/3}`
   (`asymptoticIndependenceNumber_gcwTable_le`).
3. **Conciseness** (`isCoordinateConcise_gcwTable`): every standard basis vector of every leg is a
   slice of `CW_q^σ`, so `Tensor.card_le_asymptoticRank` gives `q + 2 ≤ R̃(CW_q^σ)`
   (`card_le_asymptoticRank_gcwTable`), the leg dimensions being `q + 2` by `GenCWIndex.card`.
4. **The numeric step**: `3(q+1)^{2/3} ≤ (q+2)^{0.997}` for every `q ≥ 24` (`gcw_rpow_bound`), by
   exact rational arithmetic (see below).
5. **AVW Corollary 4.3** (`six_div_add_two_le_coordinateGalacticExponent_of_concise`) with
   `s = 997/1000` then gives the *universal* constant

   ```text
   ω_g^{coord}(CW_q^σ) ≥ 6/(0.997 + 2) = 6000/2997 = 2000/999 > 2
   ```

   for every `q ≥ 24` and every permutation `σ` (`six_div_le_coordinateGalacticExponent_gcwTable`,
   `two_lt_coordinateGalacticExponent_gcwTable`).  The constant does not depend on `q` or on `σ`,
   which is exactly the content of AVW Lemma 7.2.

## Erratum to AVW's first proof of Lemma 7.2, and the corrected arithmetic

AVW display the parts (in their `z₀ ↔ z_{q+1}` presentation of `CW_q^σ`)

```text
T₁ = ∑_{i=1}^{q}   x₀ yᵢ zᵢ,
T₂ = ∑_{i=0}^{q+1} xᵢ y₀ zᵢ,
T₃ = x₀ y_{q+1} z_{q+1} + ∑_{i=1}^{q} xᵢ y_{σ(i)} z_{q+1},
```

and then assert `μ(T₁) = μ(T₂) = μ(T₃) = q²`.  **That is wrong for their own parts.**  Reading off
the minimal variable sets of AVW Definition 5.2:

* `T₁` uses `{x₀}`, `{y₁,…,y_q}`, `{z₁,…,z_q}`, so `μ(T₁) = 1·q·q = q²` (as printed);
* `T₂` uses `{x₀,…,x_{q+1}}`, `{y₀}`, `{z₀,…,z_{q+1}}`, so `μ(T₂) = (q+2)²`, **not** `q²`;
* `T₃` uses `q+1` `x`-variables, `q+1` `y`-variables and `{z_{q+1}}`, so `μ(T₃) = (q+1)²`,
  **not** `q²`.

Moving the single term `x₀ y₀ z₀` from `T₂` to `T₁` balances the three parts perfectly: all three
then have minimal variable sets of sizes `1, q+1, q+1`, hence `μ = (q+1)²` each, and Theorem 5.3
gives `Ī ≤ 3(q+1)^{2/3}` rather than AVW's `3q^{2/3}`.  This is the regrouping formalized here,
and it is the correction already recorded in `BARRIER_FRAMEWORK.md` §6 milestone K.

In the coordinates of Definition 3.1 the balanced parts are almost the three classes "`x`-index is
`0`", "`y`-index is `0`", "`z`-index is `0`": each of the `3q` middle terms has exactly one
coordinate equal to `0` and lands in the corresponding class, while each of the three corner terms
has *two* coordinates equal to `0` and is assigned to exactly one of its two candidate classes ---
`x₀ y₀ z_{q+1}` to the `X` part, `x_{q+1} y₀ z₀` to the `Y` part and `x₀ y_{q+1} z₀` to the `Z`
part.  Each part then has a single variable on its own leg, which is why `gcwPart` is indexed by
`Leg` rather than by `Fin 3`.

The displayed inequality has to be redone too, and both of its sides move.  AVW compare
`3q^{2/3}` with `q^{0.997}` and conclude for `q ≥ 28`.  Their left-hand side comes from the
erroneous `μ = q²` and is too small; the honest one is `3(q+1)^{2/3}`.  Their right-hand side, on
the other hand, understates what Corollary 4.3 offers: the base there is `R̃(T)`, and conciseness
gives `R̃(CW_q^σ) ≥ q + 2`, so `(q+2)^{0.997}` may be used in place of `q^{0.997}`.  The chain
proved here uses both corrected sides:

```text
Ī(CW_q^σ) ≤ 3(q+1)^{2/3} ≤ (q+2)^{0.997} ≤ R̃(CW_q^σ)^{0.997},
```

whose middle inequality is proved here for **every `q ≥ 24`**; at `q = 24` it reads
`3·25^{2/3} ≈ 25.6496 ≤ 26^{0.997} ≈ 25.7471`.  AVW's printed `3q^{2/3} < q^{0.997}` for `q ≥ 28`
is itself true but extremely tight (`27.663 < 27.721`) and compares against the wrong base; it is
not reused.

## The numerics, and how they are certified

Per `DESIGN.md` and `BARRIER_FRAMEWORK.md` §7, no floating point appears.  `s = 0.997` is the
rational `997/1000` throughout.  The inequality `3(q+1)^{2/3} ≤ (q+2)^{997/1000}` is proved in
logarithmic form,

```text
log 3 + (2/3)·log(q+1) ≤ (997/1000)·log(q+2)     for every natural q ≥ 24     (gcw_log_bound)
```

by induction from `q = 24` (`Nat.le_induction`):

* **Base case** (`gcw_log_bound_base`).  Writing `25 = 2⁴·(5/4)²` and `26 = 25·(26/25)`, the
  statement is linear in `log 3`, `log 2`, `log(5/4)` and `log(26/25)`, and is closed by
  `linarith` from four certified rational enclosures obtained from `Analysis/Log.lean`'s atanh
  series (`logRatioLower`/`logRatioUpper`, whose remainder bound is a closed rational expression):
  `log 3 ≤ 1.098614` (from `x = 1/2`, 10 terms), `log 2 ≥ 0.693147` (from `x = 1/3`, 8 terms),
  `log(5/4) ≥ 0.223143` (from `x = 1/9`, 4 terms) and `log(26/25) ≥ 0.039220` (from `x = 1/51`,
  3 terms).  The slack in the resulting comparison is `1.098614 ≤ 1.10240…`.
* **Induction step** (`gcw_log_step`).  Both increments are controlled by the elementary
  `Real.log_le_sub_one_of_pos`: `log(q+2) − log(q+1) ≤ 1/(q+1)` and
  `log(q+3) − log(q+2) ≥ 1/(q+3)`, so it suffices that `(2/3)/(q+1) ≤ (997/1000)/(q+3)`, i.e.
  `2000(q+3) ≤ 2991(q+1)`, i.e. `991·q ≥ 3009`, which holds far below `q = 24`.  This replaces the
  derivative-sign argument `0.997/(q+2) > (2/3)/(q+1)` by a `linarith`-checkable discrete step; no
  differentiation and no mean value theorem is needed.

## Route 2: AVW's second proof of Lemma 7.2, through Theorem 5.1 (`q ≥ 6`)

AVW's second proof (Section 7.1, immediately after the first) applies **Theorem 5.1**, the
splitting bound of `Tensor/IndependenceSplitting.lean`, twice.  In the coordinates of
Definition 3.1 the two splittings are:

1. **Split `CW_q^σ` at the `x`-variable `x₀`.**  The part avoiding `x₀` is AVW's

   ```text
   A = x_{q+1} y₀ z₀ + ∑_{i=1}^q (xᵢ y_{σ(i)} z₀ + xᵢ y₀ zᵢ),
   ```

   formalized as `gcwTableA = coordinateEraseVariable Leg.X GenCWIndex.zero (gcwTable K μ σ)`.
   The counts Theorem 5.1 needs are `q + 2` terms using `x₀`
   (`card_coordinateSupport_coordinateFixVariable_gcwTable`) and `q + 1` other `x`-variables
   (`card_erase_minimalLegSet_gcwTable`).
2. **Split `A` at the `y`-variable `y₀`.**  The part avoiding `y₀` is AVW's

   ```text
   B = ∑_{i=1}^q xᵢ y_{σ(i)} z₀,
   ```

   formalized as `gcwTableB = coordinateEraseVariable Leg.Y GenCWIndex.zero (gcwTableA K μ σ)`.
   The counts are `q + 1` terms using `y₀`
   (`card_coordinateSupport_coordinateFixVariable_gcwTableA`) and `q` other `y`-variables
   (`card_erase_minimalLegSet_gcwTableA`).  `B` uses the *single* `z`-variable `z₀`
   (`card_minimalLegSet_gcwTableB`), so `Ī(B) ≤ 1`
   (`asymptoticIndependenceNumber_gcwTableB_le_one`) — the base of the recursion.

At `q = 6` these are AVW's counts `7, 6` and `8, 7`, and the two numerical certificates of
`Tensor/IndependenceSplitting.lean` are consumed verbatim:
`asymptoticIndependenceNumber_le_of_splitVariable_seven` gives `Ī(A) ≤ 5.08` (AVW: `5.07905`)
and `asymptoticIndependenceNumber_lt_eight_of_splitVariable` gives
`Ī(CW_6^σ) < 8 = q + 2` (AVW: `7.9973`).  This is
`asymptoticIndependenceNumber_gcwTable_fin_six_lt_eight`, for every `σ`.

Corollary 4.3 needs a *quantitative* bound `Ī(T) ≤ R̃(T)^s` with an explicit `s < 1`, which the
strict `< 8` does not supply; `asymptoticIndependenceNumber_gcwTable_le_of_card_eq_six` therefore
re-runs the same named one-parameter family
`Tensor.asymptoticIndependenceNumber_le_rpow_of_splitVariable` at AVW's rational exponent
`θ = 31/32` to get the explicit `Ī(CW_6^σ) ≤ 7.9976`.  With `R̃(CW_6^σ) ≥ 8` this gives
`s = 9999/10000` (`gcw_le_rpow_eight`: `7.9976 ≤ 8^{9999/10000}`) and hence the constant
`6/(s+2) = 60000/29999`.

### What AVW claim for `q > 6`, and what is proved

AVW write, of the `q = 6` computation: *"We can then do the same process for any `q > 6` to yield
a constant `cq`, but our bound is improving with `q`, so we will get `cq ≥ c6` for all such
`q ≥ 6`."*  What they do display for general `q` is the closed form of Theorem 5.1 for `Ī(A)`,
together with the check that it stays below `(q+1)/(q+2)^{1/(q+1)}` — that is, that it satisfies
Theorem 5.1's own hypothesis `c ≤ (Q-1)/Q^{1/(Q-1)}` at `Q = q + 2`, so that the *second*
application is legitimate.  They display no `q`-parametric bound for `Ī(CW_q^σ)` itself and
verify no parameter other than `q = 6`; the monotonicity in `q` is asserted, not argued.  **It is
not taken on faith here.**  What is proved instead is a genuinely `q`-parametric two-step
splitting with *uniform rational* exponents, which sidesteps the closed form —  and with it the
hypothesis `c ≤ (Q-1)/Q^{1/(Q-1)}` — altogether, since
`Tensor.asymptoticIndependenceNumber_le_rpow_of_splitVariable` holds for every `θ ∈ [0,1]` with
no hypothesis on `c` beyond `0 ≤ c`:

```text
θ = 1/2  for A:         Ī(A) ≤ (q+1)^{1/2} + q^{1/2} ≤ 2(q+1)^{1/2},
θ = 9/10 for CW_q^σ:    Ī(CW_q^σ) ≤ (q+2)^{1/10} + 2^{1/10}·(q+1)^{19/20},
```

(`asymptoticIndependenceNumber_gcwTableA_le_two_mul_rpow`,
`asymptoticIndependenceNumber_gcwTable_le_split`; both hold for *every* `q` and every `σ`), and
then the certified numeric bound

```text
(q+2)^{1/10} + 2^{1/10}·(q+1)^{19/20} ≤ 0.999·(q+2)     for every natural q ≥ 7
```

(`gcw_split_bound`), by induction from `q = 7` — where it reads `8.9744 ≤ 8.991` — with both
increments controlled by Bernoulli's inequality `(1+z)^α ≤ 1 + αz` for `α ∈ [0,1]`
(`gcw_rpow_succ_le`, itself the weighted AM--GM inequality with weights `α, 1-α`).  The uniform
exponents lose a little against AVW's optimum — at `q = 6` they would give `8.039 > 8`, which is
exactly why `q = 6` is treated separately with the optimal `θ = 31/32` — but they are what makes
a single induction cover all `q ≥ 7` with no per-`q` certificates.

The three regimes are glued in `asymptoticIndependenceNumber_gcwTable_le_rpow_of_six_le` with the
*same* exponent `s = 9999/10000`, so that the resulting constant is uniform:

| `q`          | bound on `Ī(CW_q^σ)`         | source                            |
|--------------|------------------------------|-----------------------------------|
| `q = 6`      | `≤ 7.9976`                   | Theorem 5.1 twice, `θ = 31/32`    |
| `7 ≤ q ≤ 23` | `≤ 0.999·(q+2)`              | Theorem 5.1 twice, `θ = 1/2, 9/10`|
| `q ≥ 24`     | `≤ (q+2)^{997/1000}`         | route 1 (Theorem 5.3)             |

The middle row is capped at `23` only because route 1 takes over there; the bound
`Ī(CW_q^σ) ≤ 0.999·(q+2)` of `asymptoticIndependenceNumber_gcwTable_le_of_seven_le` itself holds
for every `q ≥ 7`.  The two conversions to a power of the base are
`gcw_mul_le_rpow` (`0.999·u ≤ u^{9999/10000}` for `1 ≤ u ≤ 25`, from `log 25 ≤ 3 log 3` and
`log(1000/999) ≥ 0.001`) and `gcw_le_rpow_eight` (`7.9976 ≤ 8^{9999/10000}`, from
`log 2 ≤ 0.693148` and `log(10000/9997) ≥ 0.0003`), both through `Analysis/Log.lean` enclosures.

The resulting universal constants are `2000/999 = 2.002002…` for `q ≥ 24` (route 1) and
`60000/29999 = 2.0000666…` for `q ≥ 6` (route 2); their minimum, valid for every `q ≥ 6`, is
`60000/29999` (`avw_lemma_seven_two_min_of_six_le`).  The gap between them is real and not an
artefact of the formalization: at `q = 6` the true splitting bound is `7.99737` against
`q + 2 = 8`, a relative gap of `3.3·10⁻⁴`, so no argument through Corollary 4.3 can give a
constant better than `6/(log(7.99737)/log 8 + 2) ≈ 2.000105` at that parameter.

## AVW Lemma 7.1: the corner route, and every remaining parameter

The parameters `q ≤ 5` that Lemma 7.2 does not reach are covered by **Lemma 7.1**, whose input is
**Corollary 5.1** of `MatrixMultiplication/IndependenceMassDistribution.lean` (milestone **I**):
a table with two *corner terms* — one term monopolising an `x`-variable, one monopolising a
`y`-variable, both using the same `z`-variable — has `Ī(T) ≤ Q^{1 - cornerExponent Q} < Q` with
`cornerExponent Q = 1/(Q²(Q+1)² log Q)`, where `Q` is the ambient number of variables per leg.
The table of `CW_q^σ` has `Q = q + 2` and the two corner terms `x_{q+1} y₀ z₀` and `x₀ y_{q+1} z₀`
of Definition 3.1, whence `asymptoticIndependenceNumber_gcwTable_le_cornerBound` and, through
Corollary 4.3, `six_div_le_coordinateGalacticExponent_gcwTable_corner`:

```text
ω_g^{coord}(CW_q^σ) ≥ 6/(3 − cornerExponent (q+2)) > 2.
```

Nothing in that chain needs a bound on `q` in either direction, so `avw_lemma_seven_one` is stated
for every `q` — AVW's `1 ≤ q ≤ 5` is where it is *used*, not where it holds.  The constant does
degrade with `q` (`cornerExponent` is antitone), which is why the large parameters go through
Lemma 7.2 instead.

## AVW Theorem 7.1: the universal constant

`avw_theorem_seven_one` is the headline of AVW Section 7, proved here in full and with **no
hypothesis**: for every parameter `q` and every permutation `σ`,

```text
ω_g^{coord}(CW_q^σ) ≥ avwTheoremSevenOneConstant
                    = min (60000/29999) (6/(3 − cornerExponent 7))
                    = 60000/29999 = 2.0000666…  ≥  2 + 1/15000.
```

Three regimes, all proved, the last two overlapping:

| `q`          | route                    | constant                      |
|--------------|--------------------------|-------------------------------|
| every `q`    | Cor. 5.1 (Lemma 7.1)     | `6/(3 − cornerExponent (q+2))`|
| `6 ≤ q`      | Thm 5.1 (Lemma 7.2, r.2) | `60000/29999`                 |
| `24 ≤ q`     | Thm 5.3 (Lemma 7.2, r.1) | `2000/999`                    |

The minimum is taken over the *best available* constant at each `q`: `60000/29999` from `q = 6`
on, and `6/(3 − cornerExponent (q+2))` below that.  Since `cornerExponent` is antitone
(`cornerExponent_anti`), the small-`q` minimum is attained at `q = 5`, i.e. at `Q = 7`
(`six_div_three_sub_cornerExponent_seven_le`), and since `cornerExponent 7 ≥ 1/10000` that value
is *above* `60000/29999` — so the binding constraint of the whole theorem is the *splitting*
argument for `q ≥ 6`, not the corner argument at `q = 5` (`avwTheoremSevenOneConstant_eq`).  The
certified rational lower bound `2 + 1/15000` (`two_add_le_avwTheoremSevenOneConstant`) needs the
`Analysis/Log.lean` enclosure `log 7 ≤ 1.945913` — itself obtained from
`log 7 = 3 log 2 − log (8/7)` with a three-term atanh series at `x = 1/15` — only to decide which
branch of the minimum binds; the value of the binding branch is exactly `2 + 2/29999`.
`avw_theorem_seven_one_exists` is the existential form
`∃ c > 2, ∀ q σ, c ≤ ω_g^{coord}(CW_q^σ)` in which AVW state the theorem informally.

**Scope.**  Per the milestone-F correction, the statement is about the **coordinate** Galactic
exponent of the literal Definition 3.1 table; the basis-free `galacticExponent` satisfies only
`galacticExponent ≤ coordinateGalacticExponent`, which transports upper bounds and not lower ones.
See the next section.

## What is *not* claimed here

* **No lower bound on the basis-free `galacticExponent`.**  `Ī` is basis-dependent, so AVW
  Theorem 4.1 bounds the *coordinate* exponent `coordinateGalacticExponent` of a fixed coefficient
  table; the available comparison
  `galacticExponent_le_coordinateGalacticExponent` runs in the direction
  `ω_g ≤ ω_g^{coord}` and therefore transports upper bounds, not lower ones.  This is recorded as
  `galacticExponent_genCW_le_coordinateGalacticExponent_gcwTable` and discussed in the
  correction note of `MatrixMultiplication/IndependenceBarrier.lean`.  For the same reason the
  statements below are about the literal table `gcwTable K μ σ` and are *not* transported along
  `Isomorphic` or through the predicate `IsGeneralizedCW`.
* **No border rank claim.**  `R̃(CW_q^σ) = q + 2` is not asserted; only the conciseness half
  `q + 2 ≤ R̃(CW_q^σ)`, which is the direction Corollary 4.3 consumes, is proved.
* **The existence of a Galactic certificate is a hypothesis of the Lemma 7.2 statements, and only
  of those.**  `coordinateGalacticExponent` is an infimum, so AVW Corollary 4.3 needs the
  certificate value set to be nonempty.  The Lemma 7.2 statements
  (`six_div_le_coordinateGalacticExponent_gcwTable`,
  `six_div_le_coordinateGalacticExponent_gcwTable_of_six_le`, `avw_lemma_seven_two`,
  `avw_lemma_seven_two_of_six_le`, `avw_lemma_seven_two_min_of_six_le` and their `2 <` corollaries)
  keep it as an explicit hypothesis, both because it is a hypothesis of Corollary 4.3 and because
  they were proved before the certificate below existed.  It is **discharged** by
  `coordinateGalacticValues_gcwTable_nonempty` — an explicit `(n,a,b,c,F) = (1,1,1,2,1)`
  certificate zeroing `CW_q^σ` out to `x₀ y₀ z_{q+1} + x₀ y_{q+1} z₀ ≅ ⟨1,1,2⟩` — so Lemma 7.1 and
  Theorem 7.1 carry no side condition at all.

## Layer placement and hypotheses

This is a layer-4 paper client under `AlgebraicComplexity/Examples/`.  Hypotheses are kept at the
weakest level each statement supports:

* the cover, the minimal variable sets and the measure are pure support combinatorics and need only
  `CommSemiring K` with `Nontrivial K` (to know that the coefficient `1` is not `0`);
* `Ī(CW_q^σ) ≤ 3(q+1)^{2/3}` likewise needs only `CommSemiring K` and `Nontrivial K`;
* `Field K` enters exactly twice, and only through the framework: for conciseness
  (`Tensor.IsCoordinateConcise` is a span statement over a field, and `Tensor.card_le_asymptoticRank`
  needs rank) and for `ω`/`R̃` in Corollary 4.3;
* the arithmetic sections are about real numbers only and mention no tensor;
* the corner bound `Ī(CW_q^σ) ≤ cornerBound (q+2)` inherits `CommSemiring K`, `NoZeroDivisors K`
  and `Nontrivial K` from AVW Corollary 5.1, and the Galactic certificate needs only
  `CommSemiring K` with `Nontrivial K`; the field hypothesis appears one step later, when
  `coordinateGalacticValues` is formed.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor

universe u v w

/-! ## The AVW §7 cover into three parts, each missing one variable type -/

section Parts

variable {K : Type u} [CommSemiring K] {μ : Type v}

/-- **The three parts of AVW's first proof of Lemma 7.2**, balanced as described in the module
header and read in the coordinates of Definition 3.1.  The part `GenCWPart σ j` is the one whose
minimal variable set on leg `j` is the single variable `0`:

* `j = X`: `x₀ y₀ z_{q+1} + ∑ᵢ x₀ yᵢ zᵢ`, using one `x`-variable;
* `j = Y`: `x_{q+1} y₀ z₀ + ∑ᵢ xᵢ y₀ zᵢ`, using one `y`-variable;
* `j = Z`: `x₀ y_{q+1} z₀ + ∑ᵢ xᵢ y_{σ(i)} z₀`, using one `z`-variable.

The three parts are in fact pairwise disjoint and exhaust the `3q + 3` terms of `CW_q^σ`, so they
form a genuine partition in AVW's sense --- but disjointness is *not* formalized, because AVW
Theorem 5.3 is available in the covering form
(`Tensor.asymptoticIndependenceNumber_le_sum_rpow_coordinateMeasure_of_cover`) and only the cover
property (`gcwPart_cover`) is needed. -/
def GenCWPart {μ : Type v} (σ : Equiv.Perm μ) : Leg → (∀ c, GenCWIndexFamily μ c) → Prop
  | .X => fun s ↦ (s .X = .zero ∧ s .Y = .zero ∧ s .Z = .last) ∨
      (∃ i, s .X = .zero ∧ s .Y = .middle i ∧ s .Z = .middle i)
  | .Y => fun s ↦ (s .X = .last ∧ s .Y = .zero ∧ s .Z = .zero) ∨
      (∃ i, s .X = .middle i ∧ s .Y = .zero ∧ s .Z = .middle i)
  | .Z => fun s ↦ (s .X = .zero ∧ s .Y = .last ∧ s .Z = .zero) ∨
      (∃ i, s .X = .middle i ∧ s .Y = .middle (σ i) ∧ s .Z = .zero)

open scoped Classical in
/-- The coefficient table of the part `GenCWPart σ j`, with the coefficient `1` on its terms. -/
noncomputable def gcwPart (K : Type u) [CommSemiring K] {μ : Type v} (σ : Equiv.Perm μ)
    (j : Leg) : (∀ c, GenCWIndexFamily μ c) → K :=
  fun s ↦ if GenCWPart σ j s then 1 else 0

/-- The support of a part is the family of triples it names. -/
theorem gcwPart_ne_zero_iff [Nontrivial K] (σ : Equiv.Perm μ) (j : Leg)
    (s : ∀ c, GenCWIndexFamily μ c) : gcwPart K σ j s ≠ 0 ↔ GenCWPart σ j s := by
  unfold gcwPart
  split_ifs with h
  · simp [h]
  · simp [h]

/-- The corner term of the part `j`: the one of the three corner terms of `CW_q^σ` assigned to that
part by the balancing described in the module header. -/
def gcwCorner {μ : Type v} : Leg → (∀ c, GenCWIndexFamily μ c)
  | .X => ofLegs .zero .zero .last
  | .Y => ofLegs .last .zero .zero
  | .Z => ofLegs .zero .last .zero

/-- The middle term of the part `j` at the middle index `k`. -/
def gcwMid {μ : Type v} (σ : Equiv.Perm μ) : Leg → μ → (∀ c, GenCWIndexFamily μ c)
  | .X => fun k ↦ ofLegs .zero (.middle k) (.middle k)
  | .Y => fun k ↦ ofLegs (.middle k) .zero (.middle k)
  | .Z => fun k ↦ ofLegs (.middle k) (.middle (σ k)) .zero

/-- The corner term of the part `j` belongs to the part `j`. -/
theorem gcwPart_corner (σ : Equiv.Perm μ) (j : Leg) : GenCWPart σ j (gcwCorner j) := by
  cases j <;> exact Or.inl ⟨rfl, rfl, rfl⟩

/-- The middle terms of the part `j` belong to the part `j`. -/
theorem gcwPart_mid (σ : Equiv.Perm μ) (j : Leg) (k : μ) :
    GenCWPart σ j (gcwMid σ j k) := by
  cases j <;> exact Or.inr ⟨k, rfl, rfl, rfl⟩

/-- On the leg `j` the part `j` uses only the variable `0`. -/
theorem gcwPart_eq_zero_leg (σ : Equiv.Perm μ) (j : Leg) {p : ∀ c, GenCWIndexFamily μ c}
    (hp : GenCWPart σ j p) : p j = GenCWIndex.zero := by
  cases j <;> rcases hp with ⟨h1, h2, h3⟩ | ⟨k, h1, h2, h3⟩ <;> assumption

/-- On any leg, a term of the part `j` uses either the corner variable of that part or a middle
variable.  Together with `gcwPart_corner` and `gcwMid_leg` this pins down the minimal variable
sets of AVW Definition 5.2. -/
theorem gcwPart_leg_mem (σ : Equiv.Perm μ) (j i : Leg) {p : ∀ c, GenCWIndexFamily μ c}
    (hp : GenCWPart σ j p) : p i = gcwCorner j i ∨ ∃ k : μ, p i = .middle k := by
  cases j <;> rcases hp with ⟨h1, h2, h3⟩ | ⟨k, h1, h2, h3⟩ <;> cases i <;>
    simp only [gcwCorner, ofLegs_X, ofLegs_Y, ofLegs_Z, h1, h2, h3] <;>
    first
      | exact Or.inl trivial
      | exact Or.inl rfl
      | exact Or.inr ⟨_, rfl⟩

/-- Off its own leg, the part `j` uses *every* middle variable. -/
theorem gcwMid_leg (σ : Equiv.Perm μ) (j i : Leg) (hij : i ≠ j) (k : μ) :
    ∃ k' : μ, gcwMid σ j k' i = (.middle k : GenCWIndex μ) := by
  cases j <;> cases i
  · exact absurd rfl hij
  · exact ⟨k, rfl⟩
  · exact ⟨k, rfl⟩
  · exact ⟨k, rfl⟩
  · exact absurd rfl hij
  · exact ⟨k, rfl⟩
  · exact ⟨k, rfl⟩
  · exact ⟨σ.symm k, by simp [gcwMid]⟩
  · exact absurd rfl hij

/-- The corner variable of a part is never a middle variable. -/
theorem gcwCorner_ne_middle (j i : Leg) (k : μ) :
    (gcwCorner j i : GenCWIndex μ) ≠ .middle k := by
  cases j <;> cases i <;> simp [gcwCorner]

variable [Fintype μ] [DecidableEq μ]

/-- **The cover property.**  Every term of `CW_q^σ` is a term of one of the three parts; this is
the only hypothesis AVW Theorem 5.3 needs (`Tensor.asymptoticIndependenceNumber_le_sum_rpow_coordinateMeasure_of_cover`).

The six families of AVW Definition 3.1 are distributed as follows: `x₀ y₀ z_{q+1}` and
`x₀ yᵢ zᵢ` go to the `X`-part, `x_{q+1} y₀ z₀` and `xᵢ y₀ zᵢ` to the `Y`-part, and
`x₀ y_{q+1} z₀` and `xᵢ y_{σ(i)} z₀` to the `Z`-part. -/
theorem gcwPart_cover [Nontrivial K] (σ : Equiv.Perm μ) (s : ∀ c, GenCWIndexFamily μ c)
    (hs : gcwTable K μ σ s ≠ 0) : ∃ j : Leg, gcwPart K σ j s ≠ 0 := by
  rcases (gcwTable_ne_zero_iff σ s).mp hs with h | h | h | ⟨i, h⟩ | ⟨i, h⟩ | ⟨i, h⟩
  · exact ⟨Leg.X, (gcwPart_ne_zero_iff σ Leg.X s).mpr (Or.inl h)⟩
  · exact ⟨Leg.Z, (gcwPart_ne_zero_iff σ Leg.Z s).mpr (Or.inl h)⟩
  · exact ⟨Leg.Y, (gcwPart_ne_zero_iff σ Leg.Y s).mpr (Or.inl h)⟩
  · exact ⟨Leg.Z, (gcwPart_ne_zero_iff σ Leg.Z s).mpr (Or.inr ⟨i, h⟩)⟩
  · exact ⟨Leg.Y, (gcwPart_ne_zero_iff σ Leg.Y s).mpr (Or.inr ⟨i, h⟩)⟩
  · exact ⟨Leg.X, (gcwPart_ne_zero_iff σ Leg.X s).mpr (Or.inr ⟨i, h⟩)⟩

end Parts

/-! ## The measure of the parts: `μ(Tⱼ) = (q+1)²` -/

section Measure

variable {K : Type u} [CommSemiring K] {μ : Type v} [Fintype μ] [DecidableEq μ]

/-- The `q` middle variables of a leg of `CW_q^σ`, as a `Finset`. -/
def gcwMiddles (μ : Type v) [Fintype μ] [DecidableEq μ] : Finset (GenCWIndex μ) :=
  Finset.univ.image GenCWIndex.middle

theorem mem_gcwMiddles {a : GenCWIndex μ} : a ∈ gcwMiddles μ ↔ ∃ k : μ, a = .middle k := by
  simp [gcwMiddles, eq_comm]

theorem card_gcwMiddles : (gcwMiddles μ).card = Fintype.card μ := by
  rw [gcwMiddles, Finset.card_image_of_injective _ (fun a b h ↦ by simpa using h),
    Finset.card_univ]

theorem card_insert_gcwMiddles {a : GenCWIndex μ} (ha : ∀ k : μ, a ≠ .middle k) :
    (insert a (gcwMiddles μ)).card = Fintype.card μ + 1 := by
  rw [Finset.card_insert_of_notMem, card_gcwMiddles]
  rw [mem_gcwMiddles]
  rintro ⟨k, rfl⟩
  exact ha k rfl

/-- **The minimal variable sets of the three parts** (AVW Definition 5.2).  On its own leg a part
has the single variable `0`; on each of the other two legs it has `q + 1` variables, the `q`
middle ones together with one corner variable.

This is the erratum of the module header, in the form the measure computation consumes: the three
sizes are `1, q+1, q+1` and never `1, q, q`. -/
theorem card_minimalLegSet_gcwPart [Nontrivial K] (σ : Equiv.Perm μ) (j i : Leg) :
    (minimalLegSet (gcwPart K σ j) i).card = if i = j then 1 else Fintype.card μ + 1 := by
  classical
  rcases eq_or_ne i j with rfl | hij
  · rw [if_pos rfl]
    have hset : minimalLegSet (gcwPart K σ i) i = {GenCWIndex.zero} := by
      ext b
      rw [mem_minimalLegSet, Finset.mem_singleton]
      constructor
      · rintro ⟨p, hp, rfl⟩
        exact gcwPart_eq_zero_leg σ i ((gcwPart_ne_zero_iff σ i p).mp hp)
      · rintro rfl
        refine ⟨gcwCorner i, (gcwPart_ne_zero_iff σ i _).mpr (gcwPart_corner σ i), ?_⟩
        cases i <;> rfl
    rw [hset, Finset.card_singleton]
  · rw [if_neg hij]
    have hset : minimalLegSet (gcwPart K σ j) i = insert (gcwCorner j i) (gcwMiddles μ) := by
      ext b
      rw [mem_minimalLegSet, Finset.mem_insert, mem_gcwMiddles]
      constructor
      · rintro ⟨p, hp, rfl⟩
        exact gcwPart_leg_mem σ j i ((gcwPart_ne_zero_iff σ j p).mp hp)
      · rintro (rfl | ⟨k, rfl⟩)
        · exact ⟨gcwCorner j, (gcwPart_ne_zero_iff σ j _).mpr (gcwPart_corner σ j), rfl⟩
        · obtain ⟨k', hk'⟩ := gcwMid_leg σ j i hij k
          exact ⟨gcwMid σ j k', (gcwPart_ne_zero_iff σ j _).mpr (gcwPart_mid σ j k'), hk'⟩
    rw [hset, card_insert_gcwMiddles (fun k ↦ gcwCorner_ne_middle j i k)]

/-- **`μ(T₁) = μ(T₂) = μ(T₃) = (q+1)²`** (AVW Definition 5.2, corrected; see the module header).
AVW print `q²`. -/
theorem coordinateMeasure_gcwPart [Nontrivial K] (σ : Equiv.Perm μ) (j : Leg) :
    coordinateMeasure (gcwPart K σ j) = (Fintype.card μ + 1) ^ 2 := by
  have h : ∀ i : Leg, (minimalLegSet (gcwPart K σ j) i).card =
      if i = j then 1 else Fintype.card μ + 1 := card_minimalLegSet_gcwPart σ j
  unfold coordinateMeasure
  rw [prod_leg, h Leg.X, h Leg.Y, h Leg.Z]
  cases j <;> simp [pow_two]

end Measure

/-! ## AVW Theorem 5.3 applied: `Ī(CW_q^σ) ≤ 3(q+1)^{2/3}` -/

section Bound

variable {K : Type u} [CommSemiring K] [Nontrivial K] {μ : Type v} [Fintype μ] [DecidableEq μ]

private theorem rpow_card_sq (q : ℕ) :
    ((((q + 1) ^ 2 : ℕ) : ℝ)) ^ ((3 : ℝ)⁻¹) = ((q : ℝ) + 1) ^ ((2 : ℝ) / 3) := by
  have hx : (0 : ℝ) ≤ (q : ℝ) + 1 := by positivity
  push_cast
  rw [← Real.rpow_natCast ((q : ℝ) + 1) 2, ← Real.rpow_mul hx]
  norm_num

/-- **AVW Lemma 7.2, step 2**: the asymptotic independence number of a generalized
Coppersmith--Winograd tensor of parameter `q` is at most `3(q+1)^{2/3}`.

This is AVW Theorem 5.3 (`Tensor.asymptoticIndependenceNumber_le_sum_rpow_coordinateMeasure_of_cover`)
applied to the three-part cover `gcwPart`, whose parts all have measure `(q+1)²`.  AVW's printed
bound is `3q^{2/3}`; see the erratum in the module header. -/
theorem asymptoticIndependenceNumber_gcwTable_le (σ : Equiv.Perm μ) :
    asymptoticIndependenceNumber (gcwTable K μ σ) ≤
      3 * ((Fintype.card μ : ℝ) + 1) ^ ((2 : ℝ) / 3) := by
  refine le_trans (asymptoticIndependenceNumber_le_sum_rpow_coordinateMeasure_of_cover
    (T := gcwTable K μ σ) (P := gcwPart K σ) (fun p hp ↦ gcwPart_cover σ p hp)) (le_of_eq ?_)
  rw [sum_leg]
  simp only [coordinateMeasure_gcwPart, rpow_card_sq]
  ring

end Bound

/-! ## Conciseness and `q + 2 ≤ R̃(CW_q^σ)` -/

section Concise

variable {K : Type u} [Field K] {μ : Type v} [Fintype μ] [DecidableEq μ]

/-- **`CW_q^σ` is concise in coordinates on every leg** (the single hypothesis of AVW Theorem 4.1
beyond the certificate).

Proof: for each leg `i` and each of the `q + 2` variables `a` of that leg there is an index triple
`p` such that, fixing the other two coordinates of `p` and letting the `i`-th vary, the only
surviving term of `CW_q^σ` is the one at `a` — so the corresponding slice is exactly the standard
basis vector `e_a`.  Concretely, on the `X` leg, `(·, y₀, z_i)` isolates `x_i`, `(·, y₀, z₀)`
isolates `x_{q+1}` and `(·, y_{q+1}, z₀)` isolates `x₀`; the other two legs are symmetric.  All
`q + 2` basis vectors are then slices, and `Tensor.isCoordinateConcise_of_forall_single`
concludes. -/
theorem isCoordinateConcise_gcwTable (K : Type u) [Field K] {μ : Type v} [Fintype μ]
    [DecidableEq μ] (σ : Equiv.Perm μ) (i : Leg) :
    Tensor.IsCoordinateConcise (gcwTable K μ σ) i := by
  classical
  have hsingle : ∀ a : GenCWIndex μ,
      (Pi.single a (1 : K) : GenCWIndex μ → K) ∈
        Set.range (Tensor.coordinateSlice (gcwTable K μ σ) i) := by
    intro a
    obtain ⟨p, hp⟩ : ∃ p : ∀ c, GenCWIndexFamily μ c,
        ∀ x : GenCWIndex μ, GenCWSupport σ (Function.update p i x) ↔ x = a := by
      cases i <;> rcases a with _ | k | _
      · exact ⟨ofLegs .zero .last .zero, fun x ↦ by
          simp [GenCWSupport, ofLegs]⟩
      · exact ⟨ofLegs .zero .zero (.middle k), fun x ↦ by
          simp [GenCWSupport, ofLegs]⟩
      · exact ⟨ofLegs .zero .zero .zero, fun x ↦ by
          simp [GenCWSupport, ofLegs]⟩
      · exact ⟨ofLegs .last .zero .zero, fun x ↦ by
          simp [GenCWSupport, ofLegs]⟩
      · exact ⟨ofLegs .zero .zero (.middle k), fun x ↦ by
          simp [GenCWSupport, ofLegs]⟩
      · exact ⟨ofLegs .zero .zero .zero, fun x ↦ by
          simp [GenCWSupport, ofLegs]⟩
      · exact ⟨ofLegs .last .zero .zero, fun x ↦ by
          simp [GenCWSupport, ofLegs]⟩
      · exact ⟨ofLegs .zero (.middle k) .zero, fun x ↦ by
          simp [GenCWSupport, ofLegs]⟩
      · exact ⟨ofLegs .zero .zero .zero, fun x ↦ by
          simp [GenCWSupport, ofLegs]⟩
    refine ⟨p, ?_⟩
    funext x
    show gcwTable K μ σ (Function.update p i x) = _
    rw [gcwTable_apply]
    by_cases hx : x = a
    · rw [if_pos ((hp x).mpr hx), hx, Pi.single_eq_same]
    · rw [if_neg (fun h ↦ hx ((hp x).mp h)), Pi.single_eq_of_ne hx]
  exact Tensor.isCoordinateConcise_of_forall_single hsingle

/-- **`q + 2 ≤ R̃(CW_q^σ)`** (AVW Lemma 7.2, step 3).  The leg dimensions of a generalized
Coppersmith--Winograd tensor of parameter `q` are `q + 2` (`GenCWIndex.card`), and conciseness
bounds them by the asymptotic rank (`Tensor.card_le_asymptoticRank`, the single use of conciseness
in AVW Theorem 4.1). -/
theorem card_le_asymptoticRank_gcwTable (σ : Equiv.Perm μ) :
    ((Fintype.card μ : ℝ) + 2) ≤
      Tensor.asymptoticRank (coordinateTensor (gcwTable K μ σ)) := by
  have h := Tensor.card_le_asymptoticRank (isCoordinateConcise_gcwTable K σ Leg.X)
  rw [show Fintype.card (GenCWIndexFamily μ Leg.X) = Fintype.card μ + 2 from GenCWIndex.card μ]
    at h
  push_cast at h
  linarith

end Concise

/-! ## The exact-arithmetic step: `3(q+1)^{2/3} ≤ (q+2)^{997/1000}` for `q ≥ 24` -/

section Arithmetic

open AlgebraicComplexity.Analysis

/-- **The base case of the numeric step**, `log 3 + (2/3)·log 25 ≤ (997/1000)·log 26`, i.e.
`3·25^{2/3} ≤ 26^{0.997}` in logarithmic form.

Writing `25 = 2⁴·(5/4)²` and `26 = 25·(26/25)` makes the statement linear in `log 3`, `log 2`,
`log (5/4)` and `log (26/25)`, and the four certified enclosures above close it by `linarith` with
slack `1.098614 ≤ 1.10240…`. -/
theorem gcw_log_bound_base :
    Real.log 3 + (2 / 3 : ℝ) * Real.log 25 ≤ (997 / 1000 : ℝ) * Real.log 26 := by
  have h25 : Real.log 25 = 4 * Real.log 2 + 2 * Real.log (5 / 4) := by
    have h : (25 : ℝ) = 2 ^ 4 * (5 / 4) ^ 2 := by norm_num
    rw [h, Real.log_mul (by norm_num) (by norm_num), Real.log_pow, Real.log_pow]
    push_cast
    ring
  have h26 : Real.log 26 = Real.log 25 + Real.log (26 / 25) := by
    have h : (26 : ℝ) = 25 * (26 / 25) := by norm_num
    conv_lhs => rw [h]
    rw [Real.log_mul (by norm_num) (by norm_num)]
  rw [h26, h25]
  linarith [log_three_le, log_two_ge, log_five_quarters_ge, log_twentysix_twentyfifths_ge]

/-- **The induction step of the numeric step.**  Both logarithmic increments are controlled by
`Real.log_le_sub_one_of_pos`: `log(q+2) − log(q+1) ≤ 1/(q+1)` and
`log(q+3) − log(q+2) ≥ 1/(q+3)`.  The comparison `(2/3)/(q+1) ≤ (997/1000)/(q+3)` is then the
rational inequality `2000(q+3) ≤ 2991(q+1)`, i.e. `991·q ≥ 3009`. -/
theorem gcw_log_step {x : ℝ} (hx : (24 : ℝ) ≤ x) :
    (2 / 3 : ℝ) * (Real.log (x + 2) - Real.log (x + 1)) ≤
      (997 / 1000 : ℝ) * (Real.log (x + 3) - Real.log (x + 2)) := by
  have hpos1 : (0 : ℝ) < x + 1 := by linarith
  have hpos2 : (0 : ℝ) < x + 2 := by linarith
  have hpos3 : (0 : ℝ) < x + 3 := by linarith
  have hA : Real.log (x + 2) - Real.log (x + 1) ≤ 1 / (x + 1) := by
    have h := Real.log_le_sub_one_of_pos (x := (x + 2) / (x + 1)) (by positivity)
    rw [Real.log_div (ne_of_gt hpos2) (ne_of_gt hpos1)] at h
    have heq : (x + 2) / (x + 1) - 1 = 1 / (x + 1) := by field_simp; ring
    rw [heq] at h
    exact h
  have hB : 1 / (x + 3) ≤ Real.log (x + 3) - Real.log (x + 2) := by
    have h := Real.log_le_sub_one_of_pos (x := (x + 2) / (x + 3)) (by positivity)
    rw [Real.log_div (ne_of_gt hpos2) (ne_of_gt hpos3)] at h
    have heq : (x + 2) / (x + 3) - 1 = -(1 / (x + 3)) := by field_simp; ring
    rw [heq] at h
    linarith
  have hC : (2 / 3 : ℝ) * (1 / (x + 1)) ≤ (997 / 1000 : ℝ) * (1 / (x + 3)) := by
    rw [mul_one_div, mul_one_div, div_le_div_iff₀ hpos1 hpos3]
    linarith
  have h1 : (2 / 3 : ℝ) * (Real.log (x + 2) - Real.log (x + 1)) ≤ (2 / 3 : ℝ) * (1 / (x + 1)) := by
    linarith
  have h2 : (997 / 1000 : ℝ) * (1 / (x + 3)) ≤
      (997 / 1000 : ℝ) * (Real.log (x + 3) - Real.log (x + 2)) := by linarith
  linarith

/-- **The numeric step in logarithmic form**: for every natural `q ≥ 24`,

```text
log 3 + (2/3)·log(q+1) ≤ (997/1000)·log(q+2).
```

Proved by `Nat.le_induction` from `gcw_log_bound_base` and `gcw_log_step`. -/
theorem gcw_log_bound (q : ℕ) (hq : 24 ≤ q) :
    Real.log 3 + (2 / 3 : ℝ) * Real.log ((q : ℝ) + 1) ≤
      (997 / 1000 : ℝ) * Real.log ((q : ℝ) + 2) := by
  induction q, hq using Nat.le_induction with
  | base =>
      have e1 : ((24 : ℕ) : ℝ) + 1 = 25 := by norm_num
      have e2 : ((24 : ℕ) : ℝ) + 2 = 26 := by norm_num
      rw [e1, e2]
      exact gcw_log_bound_base
  | succ n hn ih =>
      have hn' : (24 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      have e1 : ((n + 1 : ℕ) : ℝ) + 1 = (n : ℝ) + 2 := by push_cast; ring
      have e2 : ((n + 1 : ℕ) : ℝ) + 2 = (n : ℝ) + 3 := by push_cast; ring
      rw [e1, e2]
      linarith [gcw_log_step hn', ih]

/-- **AVW Lemma 7.2, step 4**, in the corrected form: for every natural `q ≥ 24`,

```text
3·(q+1)^{2/3} ≤ (q+2)^{0.997},
```

with `0.997` the exact rational `997/1000`.  At `q = 24` this reads
`3·25^{2/3} ≈ 25.6496 ≤ 26^{0.997} ≈ 25.7471`.

AVW's printed inequality is `3q^{2/3} < q^{0.997}` for `q ≥ 28`; it is true, but its left-hand
side comes from the erroneous `μ = q²` and its right-hand side understates the base that
Corollary 4.3 makes available (`R̃(CW_q^σ) ≥ q + 2`).  It is not used. -/
theorem gcw_rpow_bound (q : ℕ) (hq : 24 ≤ q) :
    3 * ((q : ℝ) + 1) ^ ((2 : ℝ) / 3) ≤ ((q : ℝ) + 2) ^ ((997 : ℝ) / 1000) := by
  have hq' : (24 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have h1 : (0 : ℝ) < (q : ℝ) + 1 := by linarith
  have h2 : (0 : ℝ) < (q : ℝ) + 2 := by linarith
  have hL : 3 * ((q : ℝ) + 1) ^ ((2 : ℝ) / 3)
      = Real.exp (Real.log 3 + Real.log ((q : ℝ) + 1) * (2 / 3)) := by
    rw [Real.rpow_def_of_pos h1, Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 3)]
  have hR : ((q : ℝ) + 2) ^ ((997 : ℝ) / 1000)
      = Real.exp (Real.log ((q : ℝ) + 2) * (997 / 1000)) := Real.rpow_def_of_pos h2 _
  rw [hL, hR]
  exact Real.exp_le_exp.mpr (by linarith [gcw_log_bound q hq])

end Arithmetic

/-! ## AVW Lemma 7.2 -/

section Barrier

variable {K : Type u} [Field K] {μ : Type v} [Fintype μ] [DecidableEq μ]

/-- **AVW Lemma 7.2, the hypothesis of Corollary 4.3**: for `q ≥ 24`,

```text
Ī(CW_q^σ) ≤ 3(q+1)^{2/3} ≤ (q+2)^{0.997} ≤ R̃(CW_q^σ)^{0.997}.
```

The first inequality is Theorem 5.3 on the three-part cover, the second is the certified numeric
step, and the third is conciseness. -/
theorem asymptoticIndependenceNumber_gcwTable_le_rpow_asymptoticRank (σ : Equiv.Perm μ)
    (hq : 24 ≤ Fintype.card μ) :
    asymptoticIndependenceNumber (gcwTable K μ σ) ≤
      Tensor.asymptoticRank (coordinateTensor (gcwTable K μ σ)) ^ ((997 : ℝ) / 1000) := by
  have h1 := asymptoticIndependenceNumber_gcwTable_le (K := K) σ
  have h2 := gcw_rpow_bound (Fintype.card μ) hq
  have h3 := card_le_asymptoticRank_gcwTable (K := K) σ
  have h4 : (((Fintype.card μ : ℝ)) + 2) ^ ((997 : ℝ) / 1000) ≤
      Tensor.asymptoticRank (coordinateTensor (gcwTable K μ σ)) ^ ((997 : ℝ) / 1000) :=
    Real.rpow_le_rpow (by positivity) h3 (by norm_num)
  linarith

/-- **AVW Lemma 7.2**, in the explicit Corollary-4.3 form.  For *every* parameter `q ≥ 24` and
*every* permutation `σ` of the `q` middle coordinates, the Galactic method applied to the
generalized Coppersmith--Winograd tensor `CW_q^σ` in its own variables cannot prove any exponent
bound below

```text
6/(0.997 + 2) = 6000/2997 = 2000/999 = 2.002002…
```

The constant is universal: it depends neither on `q` nor on `σ`.  This is exactly the statement of
AVW Lemma 7.2 with the explicit `c′ = 2000/999` and `q′ = 24`.

The hypothesis `hne` is the existence of at least one Galactic certificate for `CW_q^σ`, without
which `coordinateGalacticExponent` is an infimum over the empty set; it is a hypothesis of AVW
Corollary 4.3 as well and is not discharged here. -/
theorem six_div_le_coordinateGalacticExponent_gcwTable (σ : Equiv.Perm μ)
    (hq : 24 ≤ Fintype.card μ)
    (hne : (coordinateGalacticValues K (gcwTable K μ σ)).Nonempty) :
    (2000 : ℝ) / 999 ≤ coordinateGalacticExponent K (gcwTable K μ σ) := by
  have hconc : ∀ i, Tensor.IsCoordinateConcise (gcwTable K μ σ) i :=
    fun i ↦ isCoordinateConcise_gcwTable K σ i
  have hcard := card_le_asymptoticRank_gcwTable (K := K) σ
  have hq' : (24 : ℝ) ≤ (Fintype.card μ : ℝ) := by exact_mod_cast hq
  have hR : 1 < Tensor.asymptoticRank (coordinateTensor (gcwTable K μ σ)) := by linarith
  have hmain := six_div_add_two_le_coordinateGalacticExponent_of_concise K
    (s := (997 : ℝ) / 1000) hconc hR (by norm_num)
    (asymptoticIndependenceNumber_gcwTable_le_rpow_asymptoticRank σ hq) hne
  rwa [show (6 : ℝ) / ((997 : ℝ) / 1000 + 2) = 2000 / 999 by norm_num] at hmain

/-- **AVW Lemma 7.2**, final form: the coordinate Galactic exponent of every generalized
Coppersmith--Winograd tensor of parameter `q ≥ 24` is strictly above `2`, by the universal margin
`2000/999 − 2 = 2/999`. -/
theorem two_lt_coordinateGalacticExponent_gcwTable (σ : Equiv.Perm μ)
    (hq : 24 ≤ Fintype.card μ)
    (hne : (coordinateGalacticValues K (gcwTable K μ σ)).Nonempty) :
    2 < coordinateGalacticExponent K (gcwTable K μ σ) :=
  lt_of_lt_of_le (by norm_num) (six_div_le_coordinateGalacticExponent_gcwTable σ hq hne)

/-- The comparison with the basis-free Galactic exponent, recorded to make its *direction*
explicit: it bounds `ω_g(CW_q^σ)` **above** by the coordinate exponent, so the lower bound of
`six_div_le_coordinateGalacticExponent_gcwTable` does **not** transport to `galacticExponent`.
`Ī` is basis-dependent (see `MatrixMultiplication/IndependenceBarrier.lean`), and AVW conflate the
two exponents. -/
theorem galacticExponent_genCW_le_coordinateGalacticExponent_gcwTable (σ : Equiv.Perm μ)
    (hne : (coordinateGalacticValues K (gcwTable K μ σ)).Nonempty) :
    galacticExponent K (genCW K μ σ) ≤ coordinateGalacticExponent K (gcwTable K μ σ) := by
  have h := galacticExponent_le_coordinateGalacticExponent (K := K)
    (T := gcwTable K μ σ) hne
  rwa [coordinateTensor_gcwTable] at h

end Barrier

/-! ## The literal Definition 3.1 instance, `μ = Fin q` -/

section Literal

/-- **AVW Lemma 7.2 on the literal index set of Definition 3.1.**  For every integer `q ≥ 24` and
every permutation `σ` of `{1,…,q}`, the Galactic method applied to `CW_q^σ` cannot prove any
exponent below the universal constant `2000/999 > 2`. -/
theorem avw_lemma_seven_two (K : Type u) [Field K] (q : ℕ) (hq : 24 ≤ q)
    (σ : Equiv.Perm (Fin q))
    (hne : (coordinateGalacticValues K (gcwTable K (Fin q) σ)).Nonempty) :
    (2000 : ℝ) / 999 ≤ coordinateGalacticExponent K (gcwTable K (Fin q) σ) :=
  six_div_le_coordinateGalacticExponent_gcwTable σ (by simpa using hq) hne

/-- **AVW Lemma 7.2**, `2 < ω_g^{coord}(CW_q^σ)` for every `q ≥ 24` and every `σ`, on the literal
index set of Definition 3.1. -/
theorem two_lt_coordinateGalacticExponent_genCW (K : Type u) [Field K] (q : ℕ) (hq : 24 ≤ q)
    (σ : Equiv.Perm (Fin q))
    (hne : (coordinateGalacticValues K (gcwTable K (Fin q) σ)).Nonempty) :
    2 < coordinateGalacticExponent K (gcwTable K (Fin q) σ) :=
  two_lt_coordinateGalacticExponent_gcwTable σ (by simpa using hq) hne

end Literal

/-! ## Route 2, the tables `A` and `B` of AVW's second proof of Lemma 7.2 -/

section SplitTables

variable {K : Type u} [CommSemiring K] {μ : Type v} [Fintype μ] [DecidableEq μ]

/-- **AVW's intermediate table `A`** (Section 7.1, second proof of Lemma 7.2): the table obtained
from `CW_q^σ` by zeroing out the single `x`-variable `x₀`, i.e. by AVW Definition 5.1 the part
`T|_{X ∖ {x₀}}` of the splitting of `CW_q^σ` at `x₀`.

In AVW's display
`A = x_{q+1} y₀ z₀ + ∑_{i=1}^q (xᵢ y_{σ(i)} z₀ + xᵢ y₀ zᵢ)`. -/
noncomputable def gcwTableA (K : Type u) [CommSemiring K] (μ : Type v) [Fintype μ]
    [DecidableEq μ] (σ : Equiv.Perm μ) : (∀ c, GenCWIndexFamily μ c) → K :=
  Tensor.coordinateEraseVariable Leg.X GenCWIndex.zero (gcwTable K μ σ)

/-- **AVW's intermediate table `B`** (Section 7.1, second proof of Lemma 7.2): the table obtained
from `A` by zeroing out the single `y`-variable `y₀`, i.e. the part `A|_{Y ∖ {y₀}}` of the
splitting of `A` at `y₀`.

In AVW's display `B = ∑_{i=1}^q xᵢ y_{σ(i)} z₀`; it uses the single `z`-variable `z₀`, which is
what makes `Ī(B) ≤ 1`. -/
noncomputable def gcwTableB (K : Type u) [CommSemiring K] (μ : Type v) [Fintype μ]
    [DecidableEq μ] (σ : Equiv.Perm μ) : (∀ c, GenCWIndexFamily μ c) → K :=
  Tensor.coordinateEraseVariable Leg.Y GenCWIndex.zero (gcwTableA K μ σ)

/-- The support of `A`: the `2q + 1` terms of `CW_q^σ` that do not use `x₀`. -/
theorem gcwTableA_ne_zero_iff [Nontrivial K] (σ : Equiv.Perm μ)
    (s : ∀ c, GenCWIndexFamily μ c) :
    gcwTableA K μ σ s ≠ 0 ↔
      (s .X = .last ∧ s .Y = .zero ∧ s .Z = .zero) ∨
      (∃ i, s .X = .middle i ∧ s .Y = .middle (σ i) ∧ s .Z = .zero) ∨
      (∃ i, s .X = .middle i ∧ s .Y = .zero ∧ s .Z = .middle i) := by
  unfold gcwTableA
  constructor
  · intro h
    obtain ⟨hT, hX⟩ := Tensor.coordinateEraseVariable_ne_zero h
    rcases (gcwTable_ne_zero_iff σ s).mp hT with h1 | h1 | h1 | ⟨i, h1⟩ | ⟨i, h1⟩ | ⟨i, h1⟩
    · exact absurd h1.1 hX
    · exact absurd h1.1 hX
    · exact Or.inl h1
    · exact Or.inr (Or.inl ⟨i, h1⟩)
    · exact Or.inr (Or.inr ⟨i, h1⟩)
    · exact absurd h1.1 hX
  · intro h
    have hX : s .X ≠ GenCWIndex.zero := by
      rcases h with ⟨h1, _⟩ | ⟨i, h1, _⟩ | ⟨i, h1, _⟩ <;> rw [h1] <;> simp
    rw [Tensor.coordinateEraseVariable_of_ne hX, gcwTable_ne_zero_iff]
    rcases h with h1 | ⟨i, h1⟩ | ⟨i, h1⟩
    · exact Or.inr (Or.inr (Or.inl h1))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨i, h1⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨i, h1⟩))))

/-- The support of `B`: the `q` terms `xᵢ y_{σ(i)} z₀`. -/
theorem gcwTableB_ne_zero_iff [Nontrivial K] (σ : Equiv.Perm μ)
    (s : ∀ c, GenCWIndexFamily μ c) :
    gcwTableB K μ σ s ≠ 0 ↔
      ∃ i, s .X = .middle i ∧ s .Y = .middle (σ i) ∧ s .Z = .zero := by
  unfold gcwTableB
  constructor
  · intro h
    obtain ⟨hA, hY⟩ := Tensor.coordinateEraseVariable_ne_zero h
    rcases (gcwTableA_ne_zero_iff σ s).mp hA with h1 | ⟨i, h1⟩ | ⟨i, h1⟩
    · exact absurd h1.2.1 hY
    · exact ⟨i, h1⟩
    · exact absurd h1.2.1 hY
  · rintro ⟨i, h1⟩
    have hY : s .Y ≠ GenCWIndex.zero := by rw [h1.2.1]; simp
    rw [Tensor.coordinateEraseVariable_of_ne hY, gcwTableA_ne_zero_iff]
    exact Or.inr (Or.inl ⟨i, h1⟩)

end SplitTables

/-! ### The four counts of AVW's second proof

Both applications of Theorem 5.1 need two counts: how many terms use the deleted variable, and
how many *other* variables the table has on the same leg.  With `q = |μ|` these are `q + 1` and
`q` for the splitting of `A` at `y₀`, and `q + 2` and `q + 1` for the splitting of `CW_q^σ` at
`x₀`.  At `q = 6` they are `7, 6` and `8, 7`, which are exactly the counts of the two numerical
certificates of `Tensor/IndependenceSplitting.lean`. -/

section SplitCounts

variable {K : Type u} [CommSemiring K] [Nontrivial K] {μ : Type v} [Fintype μ] [DecidableEq μ]

omit [Nontrivial K] in
/-- `A` is the part of the splitting of `CW_q^σ` at `x₀` that avoids `x₀`. -/
theorem coordinateEraseVariable_gcwTable (σ : Equiv.Perm μ) :
    coordinateEraseVariable Leg.X GenCWIndex.zero (gcwTable K μ σ) = gcwTableA K μ σ := rfl

omit [Nontrivial K] in
/-- `B` is the part of the splitting of `A` at `y₀` that avoids `y₀`. -/
theorem coordinateEraseVariable_gcwTableA (σ : Equiv.Perm μ) :
    coordinateEraseVariable Leg.Y GenCWIndex.zero (gcwTableA K μ σ) = gcwTableB K μ σ := rfl

omit [Fintype μ] [DecidableEq μ] in
/-- A triple is determined by its three legs. -/
private theorem gcw_eq_ofLegs {p : ∀ c, GenCWIndexFamily μ c} {x y z : GenCWIndex μ}
    (hx : p .X = x) (hy : p .Y = y) (hz : p .Z = z) :
    p = ofLegs (V := GenCWIndexFamily μ) x y z := by
  funext c
  cases c
  · exact hx
  · exact hy
  · exact hz

/-- **`x₀` occurs in `q + 2` terms of `CW_q^σ`**: the corner terms `x₀ y₀ z_{q+1}` and
`x₀ y_{q+1} z₀` and the `q` middle terms `x₀ yᵢ zᵢ`.  This is the first hypothesis of Theorem 5.1
for the outer splitting; at `q = 6` it is the `8`. -/
theorem card_coordinateSupport_coordinateFixVariable_gcwTable (σ : Equiv.Perm μ) :
    (coordinateSupport
        (coordinateFixVariable Leg.X GenCWIndex.zero (gcwTable K μ σ))).card ≤
      Fintype.card μ + 2 := by
  classical
  have hsub : coordinateSupport
      (coordinateFixVariable Leg.X GenCWIndex.zero (gcwTable K μ σ)) ⊆
      insert (ofLegs (V := GenCWIndexFamily μ) .zero .zero .last)
        (insert (ofLegs (V := GenCWIndexFamily μ) .zero .last .zero)
          (Finset.univ.image fun i : μ ↦
            ofLegs (V := GenCWIndexFamily μ) .zero (.middle i) (.middle i))) := by
    intro p hp
    rw [mem_coordinateSupport] at hp
    obtain ⟨hT, hX⟩ := coordinateFixVariable_ne_zero hp
    rcases (gcwTable_ne_zero_iff σ p).mp hT with h | h | h | ⟨i, h⟩ | ⟨i, h⟩ | ⟨i, h⟩
    · rw [gcw_eq_ofLegs h.1 h.2.1 h.2.2]
      exact Finset.mem_insert_self _ _
    · rw [gcw_eq_ofLegs h.1 h.2.1 h.2.2]
      exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
    · exact absurd (h.1.symm.trans hX) (by simp)
    · exact absurd (h.1.symm.trans hX) (by simp)
    · exact absurd (h.1.symm.trans hX) (by simp)
    · rw [gcw_eq_ofLegs h.1 h.2.1 h.2.2]
      exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
        (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩))
  refine le_trans (Finset.card_le_card hsub) ?_
  have h1 := Finset.card_insert_le (ofLegs (V := GenCWIndexFamily μ) .zero .zero .last)
      (insert (ofLegs (V := GenCWIndexFamily μ) .zero .last .zero)
        (Finset.univ.image fun i : μ ↦
          ofLegs (V := GenCWIndexFamily μ) .zero (.middle i) (.middle i)))
  have h2 := Finset.card_insert_le (ofLegs (V := GenCWIndexFamily μ) .zero .last .zero)
      (Finset.univ.image fun i : μ ↦
        ofLegs (V := GenCWIndexFamily μ) .zero (.middle i) (.middle i))
  have h3 : (Finset.univ.image fun i : μ ↦
      ofLegs (V := GenCWIndexFamily μ) .zero (.middle i) (.middle i)).card ≤
        Fintype.card μ := by
    simpa using Finset.card_image_le (s := (Finset.univ : Finset μ))
      (f := fun i : μ ↦ ofLegs (V := GenCWIndexFamily μ) .zero (.middle i) (.middle i))
  omega

/-- **`CW_q^σ` has `q + 1` `x`-variables other than `x₀`**: `x_{q+1}` and the `q` middle ones.
This is the second hypothesis of Theorem 5.1 for the outer splitting; at `q = 6` it is the `7`. -/
theorem card_erase_minimalLegSet_gcwTable (σ : Equiv.Perm μ) :
    ((minimalLegSet (gcwTable K μ σ) Leg.X).erase GenCWIndex.zero).card ≤
      Fintype.card μ + 1 := by
  classical
  have hsub : (minimalLegSet (gcwTable K μ σ) Leg.X).erase GenCWIndex.zero ⊆
      insert (GenCWIndex.last : GenCWIndex μ) (gcwMiddles μ) := by
    intro a ha
    rw [Finset.mem_erase] at ha
    obtain ⟨hne, hmem⟩ := ha
    rw [mem_minimalLegSet] at hmem
    obtain ⟨p, hp, rfl⟩ := hmem
    rcases (gcwTable_ne_zero_iff σ p).mp hp with h | h | h | ⟨i, h⟩ | ⟨i, h⟩ | ⟨i, h⟩
    · exact absurd h.1 hne
    · exact absurd h.1 hne
    · rw [h.1]; exact Finset.mem_insert_self _ _
    · rw [h.1]; exact Finset.mem_insert_of_mem (mem_gcwMiddles.mpr ⟨i, rfl⟩)
    · rw [h.1]; exact Finset.mem_insert_of_mem (mem_gcwMiddles.mpr ⟨i, rfl⟩)
    · exact absurd h.1 hne
  exact le_trans (Finset.card_le_card hsub)
    (le_of_eq (card_insert_gcwMiddles (fun k ↦ by simp)))

/-- **`y₀` occurs in `q + 1` terms of `A`**: the corner term `x_{q+1} y₀ z₀` and the `q` middle
terms `xᵢ y₀ zᵢ`.  This is the first hypothesis of Theorem 5.1 for the inner splitting; at
`q = 6` it is the `7`. -/
theorem card_coordinateSupport_coordinateFixVariable_gcwTableA (σ : Equiv.Perm μ) :
    (coordinateSupport
        (coordinateFixVariable Leg.Y GenCWIndex.zero (gcwTableA K μ σ))).card ≤
      Fintype.card μ + 1 := by
  classical
  have hsub : coordinateSupport
      (coordinateFixVariable Leg.Y GenCWIndex.zero (gcwTableA K μ σ)) ⊆
      insert (ofLegs (V := GenCWIndexFamily μ) .last .zero .zero)
        (Finset.univ.image fun i : μ ↦
          ofLegs (V := GenCWIndexFamily μ) (.middle i) .zero (.middle i)) := by
    intro p hp
    rw [mem_coordinateSupport] at hp
    obtain ⟨hA, hY⟩ := coordinateFixVariable_ne_zero hp
    rcases (gcwTableA_ne_zero_iff σ p).mp hA with h | ⟨i, h⟩ | ⟨i, h⟩
    · rw [gcw_eq_ofLegs h.1 h.2.1 h.2.2]
      exact Finset.mem_insert_self _ _
    · exact absurd (h.2.1.symm.trans hY) (by simp)
    · rw [gcw_eq_ofLegs h.1 h.2.1 h.2.2]
      exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)
  refine le_trans (Finset.card_le_card hsub) ?_
  have h1 := Finset.card_insert_le (ofLegs (V := GenCWIndexFamily μ) .last .zero .zero)
      (Finset.univ.image fun i : μ ↦
        ofLegs (V := GenCWIndexFamily μ) (.middle i) .zero (.middle i))
  have h2 : (Finset.univ.image fun i : μ ↦
      ofLegs (V := GenCWIndexFamily μ) (.middle i) .zero (.middle i)).card ≤
        Fintype.card μ := by
    simpa using Finset.card_image_le (s := (Finset.univ : Finset μ))
      (f := fun i : μ ↦ ofLegs (V := GenCWIndexFamily μ) (.middle i) .zero (.middle i))
  omega

/-- **`A` has `q` `y`-variables other than `y₀`**: the `q` middle ones, reached through `σ`.
This is the second hypothesis of Theorem 5.1 for the inner splitting; at `q = 6` it is the `6`. -/
theorem card_erase_minimalLegSet_gcwTableA (σ : Equiv.Perm μ) :
    ((minimalLegSet (gcwTableA K μ σ) Leg.Y).erase GenCWIndex.zero).card ≤
      Fintype.card μ := by
  classical
  have hsub : (minimalLegSet (gcwTableA K μ σ) Leg.Y).erase GenCWIndex.zero ⊆
      gcwMiddles μ := by
    intro a ha
    rw [Finset.mem_erase] at ha
    obtain ⟨hne, hmem⟩ := ha
    rw [mem_minimalLegSet] at hmem
    obtain ⟨p, hp, rfl⟩ := hmem
    rcases (gcwTableA_ne_zero_iff σ p).mp hp with h | ⟨i, h⟩ | ⟨i, h⟩
    · exact absurd h.2.1 hne
    · rw [h.2.1]; exact mem_gcwMiddles.mpr ⟨σ i, rfl⟩
    · exact absurd h.2.1 hne
  exact le_trans (Finset.card_le_card hsub) (le_of_eq card_gcwMiddles)

/-- **`B` uses the single `z`-variable `z₀`.**  This is AVW's observation that makes the inner
splitting start from `Ī(B) = 1`. -/
theorem card_minimalLegSet_gcwTableB (σ : Equiv.Perm μ) :
    (minimalLegSet (gcwTableB K μ σ) Leg.Z).card ≤ 1 := by
  classical
  have hsub : minimalLegSet (gcwTableB K μ σ) Leg.Z ⊆ {GenCWIndex.zero} := by
    intro a ha
    rw [mem_minimalLegSet] at ha
    obtain ⟨p, hp, rfl⟩ := ha
    obtain ⟨i, h⟩ := (gcwTableB_ne_zero_iff σ p).mp hp
    rw [h.2.2]
    exact Finset.mem_singleton_self _
  simpa using Finset.card_le_card hsub

/-- **`Ī(B) ≤ 1`**, the starting point of AVW's second proof: `B` uses one `z`-variable, and an
independent set injects into every minimal variable set
(`Tensor.asymptoticIndependenceNumber_le_card_minimalLegSet`). -/
theorem asymptoticIndependenceNumber_gcwTableB_le_one (σ : Equiv.Perm μ) :
    asymptoticIndependenceNumber (gcwTableB K μ σ) ≤ 1 := by
  refine le_trans (asymptoticIndependenceNumber_le_card_minimalLegSet _ Leg.Z) ?_
  exact_mod_cast card_minimalLegSet_gcwTableB (K := K) σ

end SplitCounts

/-! ### The exact arithmetic of the second proof

Two families of numerical obligations, all in exact rational arithmetic or through the certified
enclosures of `Analysis/Log.lean`, per `DESIGN.md` and `BARRIER_FRAMEWORK.md` §7:

* the `q ≥ 7` bound `(q+2)^{1/10} + 2^{1/10}(q+1)^{19/20} ≤ 0.999·(q+2)` (`gcw_split_bound`),
  proved by induction from `q = 7` with Bernoulli's inequality controlling both increments;
* the two conversions of a linear bound into a power of the base that AVW Corollary 4.3 consumes:
  `0.999·u ≤ u^{9999/10000}` for `u ≤ 25` (`gcw_mul_le_rpow`) and the sharper
  `7.9976 ≤ 8^{9999/10000}` needed at `q = 6` (`gcw_le_rpow_eight`). -/

section SplitArithmetic

open AlgebraicComplexity.Analysis

/-- `x ^ (j/N) ≤ y` from the exact inequality `x^j ≤ y^N`.  The named exponent `e` is the only
addition to `Analysis.rpow_div_le_of_pow_le_pow`: it lets a caller supply the exponent in whatever
normal form the surrounding computation produced it. -/
private theorem gcw_rpow_le {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) {j N : ℕ} (hN : N ≠ 0)
    {e : ℝ} (he : e = (j : ℝ) / (N : ℝ)) (h : x ^ j ≤ y ^ N) : x ^ e ≤ y :=
  he ▸ rpow_div_le_of_pow_le_pow hx hy hN h

/-- `y ≤ x ^ (j/N)` from the exact inequality `y^N ≤ x^j`, the exponent-normalizing wrapper of
`Analysis.le_rpow_div_of_pow_le_pow`. -/
private theorem gcw_le_rpow {x y : ℝ} (hx : 0 ≤ x) {j N : ℕ} (hN : N ≠ 0)
    {e : ℝ} (he : e = (j : ℝ) / (N : ℝ)) (h : y ^ N ≤ x ^ j) : y ≤ x ^ e :=
  he ▸ le_rpow_div_of_pow_le_pow hx hN h

/-- Bernoulli's inequality for exponents in `[0,1]`, in the increment form. -/
private theorem gcw_rpow_succ_le {x α : ℝ} (hx : 0 < x) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) :
    (x + 1) ^ α ≤ x ^ α + α * (x ^ α / x) := by
  have hxa : (0:ℝ) < x ^ α := Real.rpow_pos_of_pos hx α
  have hratio : (0:ℝ) ≤ (x + 1) / x := by positivity
  have hg := Real.geom_mean_le_arith_mean2_weighted hα0 (by linarith : (0:ℝ) ≤ 1 - α)
    hratio zero_le_one (by ring)
  simp only [Real.one_rpow, mul_one] at hg
  have hkey : (x + 1) ^ α = x ^ α * ((x + 1) / x) ^ α := by
    rw [← Real.mul_rpow (le_of_lt hx) hratio]
    congr 1
    field_simp
  rw [hkey]
  have h2 : x ^ α * ((x + 1) / x) ^ α ≤ x ^ α * (α * ((x + 1) / x) + (1 - α)) :=
    mul_le_mul_of_nonneg_left hg (le_of_lt hxa)
  refine h2.trans (le_of_eq ?_)
  field_simp
  ring

/-- `x^α / x ≤ 1/r` whenever `r ≤ x^{1-α}`. -/
private theorem gcw_rpow_div_self_le {x α r : ℝ} (hx : 0 < x) (hr : 0 < r)
    (h : r ≤ x ^ (1 - α)) : x ^ α / x ≤ 1 / r := by
  have hxa : (0:ℝ) < x ^ α := Real.rpow_pos_of_pos hx α
  have hx1 : x ^ α * x ^ (1 - α) = x := by
    rw [← Real.rpow_add hx]
    norm_num
  rw [div_le_div_iff₀ hx hr]
  calc x ^ α * r ≤ x ^ α * x ^ (1 - α) := by nlinarith
    _ = x := hx1
    _ = 1 * x := by ring

/-- `3 ≤ x^{9/10}` for `x ≥ 9`. -/
private theorem three_le_rpow {x : ℝ} (hx : (9:ℝ) ≤ x) : (3:ℝ) ≤ x ^ ((9:ℝ)/10) := by
  refine gcw_le_rpow (by linarith) (j := 9) (N := 10) (by norm_num) (by norm_num) ?_
  calc (3:ℝ) ^ 10 ≤ (9:ℝ) ^ 9 := by norm_num
    _ ≤ x ^ 9 := by gcongr

/-- `11/10 ≤ x^{1/20}` for `x ≥ 8`. -/
private theorem eleven_tenths_le_rpow {x : ℝ} (hx : (8:ℝ) ≤ x) :
    (11:ℝ)/10 ≤ x ^ ((1:ℝ)/20) := by
  refine gcw_le_rpow (by linarith) (j := 1) (N := 20) (by norm_num) (by norm_num) ?_
  have hb : ((11:ℝ)/10) ^ 20 ≤ 8 := by norm_num
  simpa using hb.trans hx

/-- `2^{1/10} ≤ 1.0718`. -/
private theorem two_rpow_tenth_le : (2:ℝ) ^ ((1:ℝ)/10) ≤ 10718/10000 :=
  gcw_rpow_le (by norm_num) (by norm_num) (j := 1) (N := 10) (by norm_num) (by norm_num)
    (by norm_num)

/-- **The induction step** of the `q ≥ 7` bound. -/
private theorem gcw_split_step {x : ℝ} (hx : (7:ℝ) ≤ x) :
    (x + 3) ^ ((1:ℝ)/10) + 2 ^ ((1:ℝ)/10) * ((x + 2) ^ ((19:ℝ)/20)) ≤
      ((x + 2) ^ ((1:ℝ)/10) + 2 ^ ((1:ℝ)/10) * ((x + 1) ^ ((19:ℝ)/20))) + 999/1000 := by
  have hx2 : (0:ℝ) < x + 2 := by linarith
  have hx1 : (0:ℝ) < x + 1 := by linarith
  have h1 : (x + 2 + 1) ^ ((1:ℝ)/10) ≤
      (x + 2) ^ ((1:ℝ)/10) + (1/10) * ((x + 2) ^ ((1:ℝ)/10) / (x + 2)) :=
    gcw_rpow_succ_le hx2 (by norm_num) (by norm_num)
  have h2 : (x + 1 + 1) ^ ((19:ℝ)/20) ≤
      (x + 1) ^ ((19:ℝ)/20) + (19/20) * ((x + 1) ^ ((19:ℝ)/20) / (x + 1)) :=
    gcw_rpow_succ_le hx1 (by norm_num) (by norm_num)
  rw [show x + 2 + 1 = x + 3 from by ring] at h1
  rw [show x + 1 + 1 = x + 2 from by ring] at h2
  have he : (x + 2) ^ ((1:ℝ)/10) / (x + 2) ≤ 1 / 3 := by
    refine gcw_rpow_div_self_le hx2 (by norm_num) ?_
    rw [show (1:ℝ) - 1/10 = 9/10 from by norm_num]
    exact three_le_rpow (by linarith)
  have hd : (x + 1) ^ ((19:ℝ)/20) / (x + 1) ≤ 1 / (11/10) := by
    refine gcw_rpow_div_self_le hx1 (by norm_num) ?_
    rw [show (1:ℝ) - 19/20 = 1/20 from by norm_num]
    exact eleven_tenths_le_rpow (by linarith)
  have hd0 : (0:ℝ) ≤ (x + 1) ^ ((19:ℝ)/20) / (x + 1) := by positivity
  have ht0 : (0:ℝ) ≤ (2:ℝ) ^ ((1:ℝ)/10) := Real.rpow_nonneg (by norm_num) _
  have ht := two_rpow_tenth_le
  have hprod : (2:ℝ) ^ ((1:ℝ)/10) * ((19/20) * ((x + 1) ^ ((19:ℝ)/20) / (x + 1))) ≤
      (10718/10000) * ((19/20) * (1/(11/10))) :=
    mul_le_mul ht (mul_le_mul_of_nonneg_left hd (by norm_num)) (by positivity) (by norm_num)
  have hmul : (2:ℝ) ^ ((1:ℝ)/10) * ((x + 2) ^ ((19:ℝ)/20)) ≤
      (2:ℝ) ^ ((1:ℝ)/10) * ((x + 1) ^ ((19:ℝ)/20)) +
      (2:ℝ) ^ ((1:ℝ)/10) * ((19/20) * ((x + 1) ^ ((19:ℝ)/20) / (x + 1))) := by
    have := mul_le_mul_of_nonneg_left h2 ht0
    nlinarith [this]
  linarith

/-- **The `q ≥ 7` numeric bound**: `(q+2)^{1/10} + 2^{1/10}(q+1)^{19/20} ≤ 0.999·(q+2)`. -/
theorem gcw_split_bound (q : ℕ) (hq : 7 ≤ q) :
    ((q:ℝ) + 2) ^ ((1:ℝ)/10) + 2 ^ ((1:ℝ)/10) * (((q:ℝ) + 1) ^ ((19:ℝ)/20)) ≤
      (999/1000 : ℝ) * ((q:ℝ) + 2) := by
  induction q, hq using Nat.le_induction with
  | base =>
      have e1 : ((7:ℕ):ℝ) + 1 = 8 := by norm_num
      have e2 : ((7:ℕ):ℝ) + 2 = 9 := by norm_num
      rw [e1, e2]
      have h1 : (9:ℝ) ^ ((1:ℝ)/10) ≤ 12458/10000 :=
        gcw_rpow_le (by norm_num) (by norm_num) (j := 1) (N := 10) (by norm_num) (by norm_num)
          (by norm_num)
      have h2 := two_rpow_tenth_le
      have h3 : (8:ℝ) ^ ((19:ℝ)/20) ≤ 72108/10000 :=
        gcw_rpow_le (by norm_num) (by norm_num) (j := 19) (N := 20) (by norm_num) (by norm_num)
          (by norm_num)
      have h4 : (2:ℝ) ^ ((1:ℝ)/10) * ((8:ℝ) ^ ((19:ℝ)/20)) ≤
          (10718/10000) * (72108/10000) :=
        mul_le_mul h2 h3 (Real.rpow_nonneg (by norm_num) _) (by norm_num)
      norm_num at h1 h4 ⊢
      linarith
  | succ n hn ih =>
      have hn' : (7:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
      have e1 : ((n + 1 : ℕ):ℝ) + 1 = (n:ℝ) + 2 := by push_cast; ring
      have e2 : ((n + 1 : ℕ):ℝ) + 2 = (n:ℝ) + 3 := by push_cast; ring
      rw [e1, e2]
      have hstep := gcw_split_step hn'
      have harith : (999/1000:ℝ) * ((n:ℝ) + 3) = (999/1000:ℝ) * ((n:ℝ) + 2) + 999/1000 := by
        ring
      linarith

/-- For `1 ≤ u ≤ 25`, `0.999·u ≤ u^{9999/10000}`. -/
theorem gcw_mul_le_rpow {u : ℝ} (h1 : 1 ≤ u) (h25 : u ≤ 25) :
    (999/1000 : ℝ) * u ≤ u ^ ((9999:ℝ)/10000) := by
  have hu0 : (0:ℝ) < u := by linarith
  have hsplit : u ^ ((9999:ℝ)/10000) * u ^ ((1:ℝ)/10000) = u := by
    rw [← Real.rpow_add hu0]
    norm_num
  have hlog : Real.log u ≤ 3295842/1000000 := by
    have ha : Real.log u ≤ Real.log 25 := Real.log_le_log hu0 h25
    have hb : Real.log 25 ≤ Real.log 27 := Real.log_le_log (by norm_num) (by norm_num)
    have hc : Real.log 27 = 3 * Real.log 3 := by
      rw [show (27:ℝ) = 3 ^ (3:ℕ) by norm_num, Real.log_pow]
      push_cast
      ring
    linarith [log_three_le]
  have hkey : u ^ ((1:ℝ)/10000) ≤ 1000/999 := by
    rw [Real.rpow_def_of_pos hu0,
      show (1000:ℝ)/999 = Real.exp (Real.log (1000/999)) from (Real.exp_log (by norm_num)).symm]
    exact Real.exp_le_exp.mpr (by linarith [log_thousand_ratio_ge])
  have hpos : (0:ℝ) < u ^ ((9999:ℝ)/10000) := Real.rpow_pos_of_pos hu0 _
  have h := mul_le_mul_of_nonneg_left hkey (le_of_lt hpos)
  rw [hsplit] at h
  linarith

/-- The `q = 6` conversion: `7.9976 ≤ 8^{9999/10000}`. -/
theorem gcw_le_rpow_eight : (7.9976 : ℝ) ≤ (8:ℝ) ^ ((9999:ℝ)/10000) := by
  have hlog8 : Real.log 8 = 3 * Real.log 2 := by
    rw [show (8:ℝ) = 2 ^ (3:ℕ) by norm_num, Real.log_pow]
    push_cast
    ring
  have hratio : Real.log (10000/9997) = Real.log 8 - Real.log 7.9976 := by
    rw [show (10000:ℝ)/9997 = 8/7.9976 by norm_num,
      Real.log_div (by norm_num) (by norm_num)]
  rw [Real.rpow_def_of_pos (by norm_num : (0:ℝ) < 8),
    show (7.9976:ℝ) = Real.exp (Real.log 7.9976) from (Real.exp_log (by norm_num)).symm]
  refine Real.exp_le_exp.mpr ?_
  linarith [log_two_le, log_ninetynineninetyseven_ratio_ge]

end SplitArithmetic

/-! ### The two applications of Theorem 5.1 -/

section SplitBounds

variable {K : Type u} [CommSemiring K] [NoZeroDivisors K] [Nontrivial K]
variable {μ : Type v} [Fintype μ] [DecidableEq μ]

/-- **AVW's first application of Theorem 5.1 at `q = 6`** (Section 7.1, second proof of
Lemma 7.2): the counts `7` and `6` for the splitting of `A` at `y₀`, together with `Ī(B) ≤ 1`,
give `Ī(A) ≤ 5.08`.

The certificate `Tensor.asymptoticIndependenceNumber_le_of_splitVariable_seven` is consumed
verbatim; AVW report the optimum of `splittingBound 7 1` as `5.07905`. -/
theorem asymptoticIndependenceNumber_gcwTableA_le_of_card_eq_six (σ : Equiv.Perm μ)
    (hq : Fintype.card μ = 6) :
    asymptoticIndependenceNumber (gcwTableA K μ σ) ≤ 5.08 := by
  refine asymptoticIndependenceNumber_le_of_splitVariable_seven
    (i₀ := Leg.Y) (a := GenCWIndex.zero) ?_ ?_ ?_
  · have h := card_coordinateSupport_coordinateFixVariable_gcwTableA (K := K) σ
    rw [hq] at h
    have h7 : (coordinateSupport
        (coordinateFixVariable Leg.Y GenCWIndex.zero (gcwTableA K μ σ))).card ≤ 7 := by omega
    exact_mod_cast h7
  · have h := card_erase_minimalLegSet_gcwTableA (K := K) σ
    rw [hq] at h
    exact_mod_cast h
  · rw [coordinateEraseVariable_gcwTableA]
    exact asymptoticIndependenceNumber_gcwTableB_le_one σ

/-- **AVW's second application of Theorem 5.1 at `q = 6`**, the headline of their second proof of
Lemma 7.2: the counts `8` and `7` for the splitting of `CW_6^σ` at `x₀`, together with the
`Ī(A) ≤ 5.08` above, give `Ī(CW_6^σ) < 8 = q + 2`.

The certificate `Tensor.asymptoticIndependenceNumber_lt_eight_of_splitVariable` is consumed
verbatim; AVW report `7.9973`.  The bound holds for *every* permutation `σ`, since `σ` never
enters the counts. -/
theorem asymptoticIndependenceNumber_gcwTable_lt_eight_of_card_eq_six (σ : Equiv.Perm μ)
    (hq : Fintype.card μ = 6) :
    asymptoticIndependenceNumber (gcwTable K μ σ) < 8 := by
  refine asymptoticIndependenceNumber_lt_eight_of_splitVariable
    (i₀ := Leg.X) (a := GenCWIndex.zero) ?_ ?_ ?_
  · have h := card_coordinateSupport_coordinateFixVariable_gcwTable (K := K) σ
    rw [hq] at h
    have h8 : (coordinateSupport
        (coordinateFixVariable Leg.X GenCWIndex.zero (gcwTable K μ σ))).card ≤ 8 := by omega
    exact_mod_cast h8
  · have h := card_erase_minimalLegSet_gcwTable (K := K) σ
    rw [hq] at h
    have h7 : ((minimalLegSet (gcwTable K μ σ) Leg.X).erase GenCWIndex.zero).card ≤ 7 := by omega
    exact_mod_cast h7
  · rw [coordinateEraseVariable_gcwTable]
    exact asymptoticIndependenceNumber_gcwTableA_le_of_card_eq_six σ hq

/-- The **quantitative** form of the previous theorem, which is what AVW Corollary 4.3 consumes:
`Ī(CW_6^σ) ≤ 7.9976`, an explicit rational strictly below `q + 2 = 8`.

`Tensor.asymptoticIndependenceNumber_lt_eight_of_splitVariable` states only `< 8`, so the
explicit constant is obtained from the same named one-parameter family
`Tensor.asymptoticIndependenceNumber_le_rpow_of_splitVariable` at the same rational exponent
`θ = 31/32` and with the same enclosures `8^{1/32} ≤ 1.06715`, `7^{31/32} ≤ 6.5871`,
`5.08^{1/32} ≤ 1.05211`, whose combination is `7.99751 ≤ 7.9976`. -/
theorem asymptoticIndependenceNumber_gcwTable_le_of_card_eq_six (σ : Equiv.Perm μ)
    (hq : Fintype.card μ = 6) :
    asymptoticIndependenceNumber (gcwTable K μ σ) ≤ 7.9976 := by
  refine le_trans (asymptoticIndependenceNumber_le_rpow_of_splitVariable
    (T := gcwTable K μ σ) (i₀ := Leg.X) (a := GenCWIndex.zero)
    (M := 8) (R := 7) (c := 5.08) (θ := 31/32)
    (by norm_num) (by norm_num) (by norm_num) ?_ ?_ ?_) ?_
  · have h := card_coordinateSupport_coordinateFixVariable_gcwTable (K := K) σ
    rw [hq] at h
    have h8 : (coordinateSupport
        (coordinateFixVariable Leg.X GenCWIndex.zero (gcwTable K μ σ))).card ≤ 8 := by omega
    exact_mod_cast h8
  · have h := card_erase_minimalLegSet_gcwTable (K := K) σ
    rw [hq] at h
    have h7 : ((minimalLegSet (gcwTable K μ σ) Leg.X).erase GenCWIndex.zero).card ≤ 7 := by omega
    exact_mod_cast h7
  · rw [coordinateEraseVariable_gcwTable]
    exact asymptoticIndependenceNumber_gcwTableA_le_of_card_eq_six σ hq
  · have h1 : (8:ℝ) ^ (1 - (31:ℝ)/32) ≤ 1.06715 :=
      gcw_rpow_le (by norm_num) (by norm_num) (j := 1) (N := 32) (by norm_num) (by norm_num)
        (by norm_num)
    have h2 : (7:ℝ) ^ ((31:ℝ)/32) ≤ 6.5871 :=
      gcw_rpow_le (by norm_num) (by norm_num) (j := 31) (N := 32) (by norm_num) (by norm_num)
        (by norm_num)
    have h3 : (5.08:ℝ) ^ (1 - (31:ℝ)/32) ≤ 1.05211 :=
      gcw_rpow_le (by norm_num) (by norm_num) (j := 1) (N := 32) (by norm_num) (by norm_num)
        (by norm_num)
    have hmul : (7:ℝ) ^ ((31:ℝ)/32) * (5.08:ℝ) ^ (1 - (31:ℝ)/32) ≤ 6.5871 * 1.05211 :=
      mul_le_mul h2 h3 (Real.rpow_nonneg (by norm_num) _) (by norm_num)
    norm_num at h1 hmul ⊢
    linarith

/-- **Theorem 5.1 applied to `A` for every `q`**, with the uniform rational exponent `θ = 1/2`:
the counts `q + 1` and `q` and `Ī(B) ≤ 1` give `Ī(A) ≤ (q+1)^{1/2} + q^{1/2} ≤ 2(q+1)^{1/2}`.

`θ = 1/2` is not optimal — AVW's optimum is at `θ ≈ 0.543` and gives `5.07905` instead of
`√7 + √6 = 5.0953` at `q = 6` — but it is uniform in `q`, which is what the `q ≥ 7` half of the
proof needs. -/
theorem asymptoticIndependenceNumber_gcwTableA_le_two_mul_rpow (σ : Equiv.Perm μ) :
    asymptoticIndependenceNumber (gcwTableA K μ σ) ≤
      2 * ((Fintype.card μ : ℝ) + 1) ^ ((1:ℝ)/2) := by
  refine le_trans (asymptoticIndependenceNumber_le_rpow_of_splitVariable
    (T := gcwTableA K μ σ) (i₀ := Leg.Y) (a := GenCWIndex.zero)
    (M := (Fintype.card μ : ℝ) + 1) (R := (Fintype.card μ : ℝ)) (c := 1) (θ := 1/2)
    zero_le_one (by norm_num) (by norm_num) ?_ ?_ ?_) ?_
  · have h := card_coordinateSupport_coordinateFixVariable_gcwTableA (K := K) σ
    have h' : ((coordinateSupport
        (coordinateFixVariable Leg.Y GenCWIndex.zero (gcwTableA K μ σ))).card : ℝ) ≤
        ((Fintype.card μ + 1 : ℕ) : ℝ) := by exact_mod_cast h
    push_cast at h'
    exact h'
  · have h := card_erase_minimalLegSet_gcwTableA (K := K) σ
    exact_mod_cast h
  · rw [coordinateEraseVariable_gcwTableA]
    exact asymptoticIndependenceNumber_gcwTableB_le_one σ
  · have hq1 : (0:ℝ) ≤ (Fintype.card μ : ℝ) + 1 := by positivity
    have hmono : ((Fintype.card μ : ℝ)) ^ ((1:ℝ)/2) ≤ ((Fintype.card μ : ℝ) + 1) ^ ((1:ℝ)/2) :=
      Real.rpow_le_rpow (by positivity) (by linarith) (by norm_num)
    rw [Real.one_rpow, mul_one, show (1:ℝ) - 1/2 = 1/2 from by norm_num]
    linarith

/-- **The two-step splitting bound for every `q`**, with the uniform rational exponents
`θ = 1/2` (for `A`, above) and `θ = 9/10` (for `CW_q^σ`):

```text
Ī(CW_q^σ) ≤ (q+2)^{1/10} + 2^{1/10}·(q+1)^{19/20}.
```

The counts for the outer splitting are `q + 2` terms using `x₀` and `q + 1` other `x`-variables,
and `c = 2(q+1)^{1/2}` is the bound on `Ī(A)`. -/
theorem asymptoticIndependenceNumber_gcwTable_le_split (σ : Equiv.Perm μ) :
    asymptoticIndependenceNumber (gcwTable K μ σ) ≤
      ((Fintype.card μ : ℝ) + 2) ^ ((1:ℝ)/10) +
        2 ^ ((1:ℝ)/10) * (((Fintype.card μ : ℝ) + 1) ^ ((19:ℝ)/20)) := by
  have hq1 : (0:ℝ) < (Fintype.card μ : ℝ) + 1 := by positivity
  refine le_trans (asymptoticIndependenceNumber_le_rpow_of_splitVariable
    (T := gcwTable K μ σ) (i₀ := Leg.X) (a := GenCWIndex.zero)
    (M := (Fintype.card μ : ℝ) + 2) (R := (Fintype.card μ : ℝ) + 1)
    (c := 2 * ((Fintype.card μ : ℝ) + 1) ^ ((1:ℝ)/2)) (θ := 9/10)
    (by positivity) (by norm_num) (by norm_num) ?_ ?_ ?_) (le_of_eq ?_)
  · have h := card_coordinateSupport_coordinateFixVariable_gcwTable (K := K) σ
    have h' : ((coordinateSupport
        (coordinateFixVariable Leg.X GenCWIndex.zero (gcwTable K μ σ))).card : ℝ) ≤
        ((Fintype.card μ + 2 : ℕ) : ℝ) := by exact_mod_cast h
    push_cast at h'
    exact h'
  · have h := card_erase_minimalLegSet_gcwTable (K := K) σ
    have h' : (((minimalLegSet (gcwTable K μ σ) Leg.X).erase GenCWIndex.zero).card : ℝ) ≤
        ((Fintype.card μ + 1 : ℕ) : ℝ) := by exact_mod_cast h
    push_cast at h'
    exact h'
  · rw [coordinateEraseVariable_gcwTable]
    exact asymptoticIndependenceNumber_gcwTableA_le_two_mul_rpow σ
  · rw [show (1:ℝ) - 9/10 = 1/10 from by norm_num,
      Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) (Real.rpow_nonneg hq1.le _),
      ← Real.rpow_mul hq1.le, show (1:ℝ)/2 * (1/10) = 1/20 from by norm_num,
      show ((Fintype.card μ : ℝ) + 1) ^ ((9:ℝ)/10) *
          (2 ^ ((1:ℝ)/10) * ((Fintype.card μ : ℝ) + 1) ^ ((1:ℝ)/20)) =
        2 ^ ((1:ℝ)/10) * (((Fintype.card μ : ℝ) + 1) ^ ((9:ℝ)/10) *
          ((Fintype.card μ : ℝ) + 1) ^ ((1:ℝ)/20)) from by ring,
      ← Real.rpow_add hq1]
    norm_num

/-- **`Ī(CW_q^σ) ≤ 0.999·(q+2)` for every `q ≥ 7` and every `σ`**: the two-step splitting bound
against the certified `q ≥ 7` numeric bound `gcw_split_bound`.

At `q = 7` this reads `8.9744 ≤ 8.991`; the margin grows with `q`, the left-hand side being
`O(q^{19/20})`. -/
theorem asymptoticIndependenceNumber_gcwTable_le_of_seven_le (σ : Equiv.Perm μ)
    (hq : 7 ≤ Fintype.card μ) :
    asymptoticIndependenceNumber (gcwTable K μ σ) ≤
      (999/1000 : ℝ) * ((Fintype.card μ : ℝ) + 2) :=
  le_trans (asymptoticIndependenceNumber_gcwTable_le_split σ) (gcw_split_bound _ hq)

end SplitBounds

/-! ## AVW Lemma 7.2 for every `q ≥ 6` -/

section BarrierSix

variable {K : Type u} [Field K] {μ : Type v} [Fintype μ] [DecidableEq μ]

/-- **The hypothesis of AVW Corollary 4.3 for every `q ≥ 6`**:

```text
Ī(CW_q^σ) ≤ (q+2)^{9999/10000}.
```

Three regimes, with the same exponent `s = 9999/10000` throughout so that the resulting constant
is uniform:

* `q = 6`: the two-step splitting of AVW's second proof gives `Ī ≤ 7.9976`, and
  `7.9976 ≤ 8^{9999/10000}` (`gcw_le_rpow_eight`).  This is the tight case: the true bound
  `7.99737` and `q + 2 = 8` differ by less than `3·10⁻⁴`, which is what forces `s` this close
  to `1`;
* `7 ≤ q ≤ 23`: the same two-step splitting with the uniform exponents `1/2` and `9/10` gives
  `Ī ≤ 0.999·(q+2)`, and `0.999·u ≤ u^{9999/10000}` for `u ≤ 25` (`gcw_mul_le_rpow`);
* `q ≥ 24`: route 1 (Theorem 5.3) gives `Ī ≤ (q+2)^{997/1000}`, and `997/1000 ≤ 9999/10000`.

The middle regime is bounded above by `23` only because route 1 takes over there; the bound
`Ī(CW_q^σ) ≤ 0.999·(q+2)` of `asymptoticIndependenceNumber_gcwTable_le_of_seven_le` itself holds
for every `q ≥ 7`. -/
theorem asymptoticIndependenceNumber_gcwTable_le_rpow_of_six_le (σ : Equiv.Perm μ)
    (hq : 6 ≤ Fintype.card μ) :
    asymptoticIndependenceNumber (gcwTable K μ σ) ≤
      ((Fintype.card μ : ℝ) + 2) ^ ((9999:ℝ)/10000) := by
  have hcast : (0:ℝ) ≤ (Fintype.card μ : ℝ) := by positivity
  rcases eq_or_lt_of_le hq with h6 | h7
  · have hq6 : Fintype.card μ = 6 := h6.symm
    have hc : ((Fintype.card μ : ℝ) + 2) = 8 := by rw [hq6]; norm_num
    rw [hc]
    exact le_trans (asymptoticIndependenceNumber_gcwTable_le_of_card_eq_six σ hq6)
      gcw_le_rpow_eight
  · have h7' : 7 ≤ Fintype.card μ := h7
    rcases Nat.lt_or_ge (Fintype.card μ) 24 with h23 | h24
    · refine le_trans (asymptoticIndependenceNumber_gcwTable_le_of_seven_le σ h7')
        (gcw_mul_le_rpow (by linarith) ?_)
      have h23' : Fintype.card μ ≤ 23 := by omega
      have : ((Fintype.card μ : ℝ)) ≤ 23 := by exact_mod_cast h23'
      linarith
    · refine le_trans (le_trans (asymptoticIndependenceNumber_gcwTable_le σ)
        (gcw_rpow_bound _ h24)) ?_
      exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)

/-- **AVW Lemma 7.2 for `q ≥ 6`**, in the explicit Corollary-4.3 form.  For *every* parameter
`q ≥ 6` and *every* permutation `σ` of the `q` middle coordinates, the Galactic method applied to
the generalized Coppersmith--Winograd tensor `CW_q^σ` in its own variables cannot prove any
exponent bound below

```text
6/(0.9999 + 2) = 60000/29999 = 2.0000666…
```

The constant is universal: it depends neither on `q` nor on `σ`.  It is *weaker* than the
`2000/999` of `six_div_le_coordinateGalacticExponent_gcwTable`, which route 1 obtains for
`q ≥ 24`; the price of covering `q = 6` — where `Ī` is within `3·10⁻⁴` of `q + 2` — is a constant
that much closer to `2`.  The two are combined in `min` form by
`avw_lemma_seven_two_of_six_le`.

The hypothesis `hne` is the existence of at least one Galactic certificate for `CW_q^σ`; it is a
hypothesis of AVW Corollary 4.3 as well and is not discharged here. -/
theorem six_div_le_coordinateGalacticExponent_gcwTable_of_six_le (σ : Equiv.Perm μ)
    (hq : 6 ≤ Fintype.card μ)
    (hne : (coordinateGalacticValues K (gcwTable K μ σ)).Nonempty) :
    (60000 : ℝ) / 29999 ≤ coordinateGalacticExponent K (gcwTable K μ σ) := by
  have hconc : ∀ i, Tensor.IsCoordinateConcise (gcwTable K μ σ) i :=
    fun i ↦ isCoordinateConcise_gcwTable K σ i
  have hcard := card_le_asymptoticRank_gcwTable (K := K) σ
  have hq' : (6:ℝ) ≤ (Fintype.card μ : ℝ) := by exact_mod_cast hq
  have hR : 1 < Tensor.asymptoticRank (coordinateTensor (gcwTable K μ σ)) := by linarith
  have hIs : asymptoticIndependenceNumber (gcwTable K μ σ) ≤
      Tensor.asymptoticRank (coordinateTensor (gcwTable K μ σ)) ^ ((9999:ℝ)/10000) :=
    le_trans (asymptoticIndependenceNumber_gcwTable_le_rpow_of_six_le σ hq)
      (Real.rpow_le_rpow (by linarith) hcard (by norm_num))
  have hmain := six_div_add_two_le_coordinateGalacticExponent_of_concise K
    (s := (9999:ℝ)/10000) hconc hR (by norm_num) hIs hne
  rwa [show (6:ℝ) / ((9999:ℝ)/10000 + 2) = 60000/29999 by norm_num] at hmain

/-- **AVW Lemma 7.2 for `q ≥ 6`**, final form: the coordinate Galactic exponent of every
generalized Coppersmith--Winograd tensor of parameter `q ≥ 6` is strictly above `2`, by the
universal margin `60000/29999 − 2 = 2/29999`. -/
theorem two_lt_coordinateGalacticExponent_gcwTable_of_six_le (σ : Equiv.Perm μ)
    (hq : 6 ≤ Fintype.card μ)
    (hne : (coordinateGalacticValues K (gcwTable K μ σ)).Nonempty) :
    2 < coordinateGalacticExponent K (gcwTable K μ σ) :=
  lt_of_lt_of_le (by norm_num)
    (six_div_le_coordinateGalacticExponent_gcwTable_of_six_le σ hq hne)

end BarrierSix

/-! ## The literal Definition 3.1 instances of route 2 -/

section LiteralSix

/-- **AVW's headline numerical claim**, `Ī(CW_6^σ) < 8 = q + 2`, on the literal index set of
Definition 3.1 and for every permutation `σ` of `{1,…,6}`.  This is the conclusion of the two-step
splitting with AVW's two numerical certificates consumed verbatim. -/
theorem asymptoticIndependenceNumber_gcwTable_fin_six_lt_eight (K : Type u) [CommSemiring K]
    [NoZeroDivisors K] [Nontrivial K] (σ : Equiv.Perm (Fin 6)) :
    asymptoticIndependenceNumber (gcwTable K (Fin 6) σ) < 8 :=
  asymptoticIndependenceNumber_gcwTable_lt_eight_of_card_eq_six σ (by simp)

/-- **AVW Lemma 7.2, route 2, on the literal index set of Definition 3.1.**  For every integer
`q ≥ 6` and every permutation `σ` of `{1,…,q}`, the Galactic method applied to `CW_q^σ` cannot
prove any exponent below the universal constant `60000/29999 > 2`.

Together with `avw_lemma_seven_two` (route 1, constant `2000/999`, `q ≥ 24`) this is the whole of
AVW Lemma 7.2 as far as it is proved here; the best constant available for a given `q` is
`2000/999` when `q ≥ 24` and `60000/29999` when `6 ≤ q ≤ 23`, and the uniform one over all
`q ≥ 6` is their minimum `60000/29999`
(`avw_lemma_seven_two_min_of_six_le`). -/
theorem avw_lemma_seven_two_of_six_le (K : Type u) [Field K] (q : ℕ) (hq : 6 ≤ q)
    (σ : Equiv.Perm (Fin q))
    (hne : (coordinateGalacticValues K (gcwTable K (Fin q) σ)).Nonempty) :
    (60000 : ℝ) / 29999 ≤ coordinateGalacticExponent K (gcwTable K (Fin q) σ) :=
  six_div_le_coordinateGalacticExponent_gcwTable_of_six_le σ (by simpa using hq) hne

/-- **The two routes combined**, with the better constant for each range and their minimum
`min (2000/999) (60000/29999) = 60000/29999` as the uniform one.  For `q ≥ 24` route 1 gives the
strictly better `2000/999 = 2.002002…`; for `6 ≤ q ≤ 23` only route 2 applies and the constant is
`60000/29999 = 2.0000666…`. -/
theorem avw_lemma_seven_two_min_of_six_le (K : Type u) [Field K] (q : ℕ) (hq : 6 ≤ q)
    (σ : Equiv.Perm (Fin q))
    (hne : (coordinateGalacticValues K (gcwTable K (Fin q) σ)).Nonempty) :
    min ((2000 : ℝ) / 999) ((60000 : ℝ) / 29999) ≤
      coordinateGalacticExponent K (gcwTable K (Fin q) σ) := by
  rw [show min ((2000 : ℝ) / 999) ((60000 : ℝ) / 29999) = 60000 / 29999 by norm_num]
  exact avw_lemma_seven_two_of_six_le K q hq σ hne

/-- **AVW Lemma 7.2, route 2**: `2 < ω_g^{coord}(CW_q^σ)` for every `q ≥ 6` and every `σ`, on the
literal index set of Definition 3.1. -/
theorem two_lt_coordinateGalacticExponent_genCW_of_six_le (K : Type u) [Field K] (q : ℕ)
    (hq : 6 ≤ q) (σ : Equiv.Perm (Fin q))
    (hne : (coordinateGalacticValues K (gcwTable K (Fin q) σ)).Nonempty) :
    2 < coordinateGalacticExponent K (gcwTable K (Fin q) σ) :=
  two_lt_coordinateGalacticExponent_gcwTable_of_six_le σ (by simpa using hq) hne

end LiteralSix

/-! ## AVW Lemma 7.1: the corner argument, valid at every parameter `q`

Route 1 needs `q ≥ 24` and route 2 needs `q ≥ 6`.  The remaining parameters are covered by AVW's
**Lemma 7.1**, whose input is **Corollary 5.1** of
`MatrixMultiplication/IndependenceMassDistribution.lean` rather than Theorem 5.1 or Theorem 5.3:
a table with *two corner terms* --- one term monopolising an `x`-variable, one monopolising a
`y`-variable, both using the same `z`-variable --- has

```text
Ī(T) ≤ cornerBound Q = Q^{1 - cornerExponent Q} < Q,     cornerExponent Q = 1/(Q²(Q+1)² log Q),
```

where `Q` is the number of variables on each leg.  The generalized Coppersmith--Winograd table has
`Q = q + 2` variables per leg (`GenCWIndex.card`) and *is* such a table, with the corners

```text
x_{q+1} y₀ z₀   and   x₀ y_{q+1} z₀
```

of AVW Definition 3.1: the coordinate `x_{q+1}` (`GenCWIndex.last` on the `X` leg) occurs in the
single term `x_{q+1} y₀ z₀`, the coordinate `y_{q+1}` occurs in the single term `x₀ y_{q+1} z₀`,
both terms use `z₀`, and `x₀ ≠ x_{q+1}`.  The argument needs *no* hypothesis on `q` at all: it is
stated below for every `μ`, including `μ` empty.
-/

section Corner

variable {K : Type u} [CommSemiring K] [NoZeroDivisors K] [Nontrivial K]
variable {μ : Type v} [Fintype μ] [DecidableEq μ]

/-- **AVW Lemma 7.1, step 1**: `Ī(CW_q^σ) ≤ c_{q+2} = (q+2)^{1 - cornerExponent (q+2)} < q + 2`,
for every parameter `q` and every permutation `σ`.

Proof sketch: the two corner terms `x_{q+1} y₀ z₀` and `x₀ y_{q+1} z₀` of AVW Definition 3.1
satisfy the hypotheses of AVW Corollary 5.1
(`asymptoticIndependenceNumber_le_cornerBound_of_corner_terms`) with
`xOne = x₀`, `xLast = x_{q+1}`, `yOne = y₀`, `yLast = y_{q+1}` and `zOne = z₀`: reading off the six
shapes of `GenCWSupport`, the only displayed triple whose `X`-coordinate is `x_{q+1}` is
`x_{q+1} y₀ z₀`, and the only one whose `Y`-coordinate is `y_{q+1}` is `x₀ y_{q+1} z₀`.  The
ambient variable count on each leg is `q + 2` by `GenCWIndex.card`. -/
theorem asymptoticIndependenceNumber_gcwTable_le_cornerBound (σ : Equiv.Perm μ) :
    asymptoticIndependenceNumber (gcwTable K μ σ) ≤ cornerBound (Fintype.card μ + 2) := by
  refine asymptoticIndependenceNumber_le_cornerBound_of_corner_terms (gcwTable K μ σ)
    (q := Fintype.card μ + 2) (by omega) (fun _ ↦ GenCWIndex.card μ)
    (xOne := .zero) (xLast := .last) (yOne := .zero) (yLast := .last) (zOne := .zero)
    (by simp) ?_ ?_ ?_ ?_
  · rw [gcwTable_ne_zero_iff]
    exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩))
  · rw [gcwTable_ne_zero_iff]
    exact Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)
  · intro p hp hx
    rw [gcwTable_ne_zero_iff] at hp
    obtain ⟨h1, h2, h3⟩ : p .X = .last ∧ p .Y = .zero ∧ p .Z = .zero := by
      rcases hp with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨i, h1, h2, h3⟩ |
        ⟨i, h1, h2, h3⟩ | ⟨i, h1, h2, h3⟩
      · simp [h1] at hx
      · simp [h1] at hx
      · exact ⟨h1, h2, h3⟩
      · simp [h1] at hx
      · simp [h1] at hx
      · simp [h1] at hx
    funext j
    cases j <;> simp [ofLegs, h1, h2, h3]
  · intro p hp hy
    rw [gcwTable_ne_zero_iff] at hp
    obtain ⟨h1, h2, h3⟩ : p .X = .zero ∧ p .Y = .last ∧ p .Z = .zero := by
      rcases hp with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨i, h1, h2, h3⟩ |
        ⟨i, h1, h2, h3⟩ | ⟨i, h1, h2, h3⟩
      · simp [h2] at hy
      · exact ⟨h1, h2, h3⟩
      · simp [h2] at hy
      · simp [h2] at hy
      · simp [h2] at hy
      · simp [h2] at hy
    funext j
    cases j <;> simp [ofLegs, h1, h2, h3]

end Corner

/-! ## The Galactic certificate of `CW_q^σ`, and the removal of the nonemptiness hypothesis

`coordinateGalacticExponent` is an infimum over the certificate value set, so every statement of
AVW Corollary 4.3 carries the side condition that this set is nonempty.  Route 1 and route 2 above
keep it as an explicit hypothesis.  It is discharged here, for **every** parameter `q` and every
`σ`, by an explicit certificate, exactly as `Examples/GroupTensorBarrier.lean` does for `T_G`:

zero out the `X` leg to the single variable `x₀` --- weight `0` on `x₀`, `1` on every other
`x`-variable, and weight `1` on the middle `y`- and `z`-variables --- and the surviving
minimum-weight part of `CW_q^σ` is

```text
x₀ y₀ z_{q+1} + x₀ y_{q+1} z₀,
```

which is one copy of `⟨1,1,2⟩`: one `x`-variable, two `y`-variables, two `z`-variables, paired by
the bijection `y₀ ↦ z_{q+1}`, `y_{q+1} ↦ z₀`.  So `(n,a,b,c,F) = (1,1,1,2,1)` with `abc = 2 ≥ 2`,
and the certificate exists for every `μ` --- no middle coordinate is used, so `μ` may even be
empty.  A `q`-dependent certificate with a better value is available (keeping the whole
`x₀`-slice gives `⟨1,1,q+2⟩`), but only nonemptiness is needed, and the two-term certificate is
uniform in `q` and needs no enumeration of the middle block.
-/

section Certificate

/-- **A coordinate Galactic certificate for `CW_q^σ`**, with data `(n,a,b,c,F) = (1,1,1,2,1)`:
the first Kronecker power of `CW_q^σ` monomially degenerates, in its own variables, onto one copy
of `⟨1,1,2⟩`.

Proof sketch: this is the pivot-bijection certificate
`AlgebraicComplexity.coordinateGalacticCertificate_of_pivot_bijection` with pivot `x₀`, the two
extreme variables `{y₀, y_{q+1}}` and `{z₀, z_{q+1}}` retained, and the swap `y₀ ↦ z_{q+1}`,
`y_{q+1} ↦ z₀` as the matching bijection.  Only the support condition has to be checked: among the
four triples `x₀ y z` with `y, z` extreme, AVW Definition 3.1 contains exactly `x₀ y₀ z_{q+1}` and
`x₀ y_{q+1} z₀`, which is the graph of the swap. -/
theorem coordinateGalacticCertificate_gcwTable (K : Type u) [CommSemiring K] [Nontrivial K]
    {μ : Type v} [Fintype μ] [DecidableEq μ] (σ : Equiv.Perm μ) :
    CoordinateGalacticCertificate K (gcwTable K μ σ) 1 1 1 2 1 := by
  classical
  have hne : (GenCWIndex.zero : GenCWIndex μ) ≠ GenCWIndex.last := by simp
  have h : CoordinateGalacticCertificate K (gcwTable K μ σ) 1 1 1
      ({GenCWIndex.zero, GenCWIndex.last} : Finset (GenCWIndex μ)).card 1 := by
    refine coordinateGalacticCertificate_of_pivot_bijection K
      (T := gcwTable K μ σ)
      (fun i ↦ match i with
        | .X => ({GenCWIndex.zero} : Finset (GenCWIndex μ))
        | .Y => ({GenCWIndex.zero, GenCWIndex.last} : Finset (GenCWIndex μ))
        | .Z => ({GenCWIndex.zero, GenCWIndex.last} : Finset (GenCWIndex μ)))
      GenCWIndex.zero rfl ⟨GenCWIndex.zero, by simp⟩
      (Equiv.subtypeEquiv (Equiv.swap GenCWIndex.zero GenCWIndex.last)
        (fun a ↦ by cases a <;> simp [Equiv.swap_apply_of_ne_of_ne])) ?_
    intro y hy z hz
    rw [gcwTable_apply]
    rcases (by simpa using hy : y = GenCWIndex.zero ∨ y = GenCWIndex.last) with rfl | rfl <;>
      rcases (by simpa using hz : z = GenCWIndex.zero ∨ z = GenCWIndex.last) with rfl | rfl <;>
      simp [GenCWSupport, ofLegs]
  rwa [Finset.card_pair hne] at h

/-- **The nonemptiness side hypothesis of AVW Corollary 4.3, discharged for `CW_q^σ`.**  The
certificate value set of the table of `CW_q^σ` is nonempty for every parameter `q` and every
permutation `σ`, so `ω_g^{coord}(CW_q^σ)` is a genuine infimum and the theorems below carry no
side condition. -/
theorem coordinateGalacticValues_gcwTable_nonempty (K : Type u) [Field K]
    {μ : Type v} [Fintype μ] [DecidableEq μ] (σ : Equiv.Perm μ) :
    (coordinateGalacticValues K (gcwTable K μ σ)).Nonempty :=
  ⟨_, ⟨1, 1, 1, 2, 1, coordinateGalacticCertificate_gcwTable K σ, by norm_num, le_rfl, rfl⟩⟩

end Certificate

/-! ## AVW Lemma 7.1 through Corollary 4.3 -/

section CornerBarrier

variable {K : Type u} [Field K] {μ : Type v} [Fintype μ] [DecidableEq μ]

/-- **AVW Lemma 7.1, step 2**: the Corollary-4.3 shape `Ī(T) ≤ R̃(T)^s` with the explicit
exponent `s = 1 - cornerExponent (q+2) < 1`.  This is the generic first step of the corner chain,
`AlgebraicComplexity.asymptoticIndependenceNumber_le_rpow_asymptoticRank_of_le_cornerBound`, fed by
`asymptoticIndependenceNumber_gcwTable_le_cornerBound` and the conciseness bound
`q + 2 ≤ R̃(CW_q^σ)` (`card_le_asymptoticRank_gcwTable`). -/
theorem asymptoticIndependenceNumber_gcwTable_le_rpow_asymptoticRank_corner (σ : Equiv.Perm μ) :
    asymptoticIndependenceNumber (gcwTable K μ σ) ≤
      Tensor.asymptoticRank (coordinateTensor (gcwTable K μ σ)) ^
        (1 - cornerExponent (Fintype.card μ + 2)) :=
  asymptoticIndependenceNumber_le_rpow_asymptoticRank_of_le_cornerBound (by omega)
    (by simpa using card_le_asymptoticRank_gcwTable (K := K) σ)
    (asymptoticIndependenceNumber_gcwTable_le_cornerBound (K := K) σ)

/-- **AVW Lemma 7.1**, in the explicit Corollary-4.3 form and with no side hypothesis: for every
parameter `q` and every permutation `σ` of the middle block, the Galactic method applied to the
generalized Coppersmith--Winograd tensor `CW_q^σ` in its own variables cannot prove any exponent
bound below the explicit constant

```text
c_q = 6/(3 - cornerExponent (q+2)),     cornerExponent Q = 1/(Q²(Q+1)² log Q).
```

The constant is `> 2` for every `q` (`two_lt_coordinateGalacticExponent_gcwTable_corner`) but
degrades as `q` grows, which is why AVW use it only for small `q` and switch to Lemma 7.2 for
large `q`.  The nonemptiness hypothesis of Corollary 4.3 is supplied by
`coordinateGalacticValues_gcwTable_nonempty`. -/
theorem six_div_le_coordinateGalacticExponent_gcwTable_corner (σ : Equiv.Perm μ) :
    6 / (3 - cornerExponent (Fintype.card μ + 2)) ≤
      coordinateGalacticExponent K (gcwTable K μ σ) :=
  six_div_sub_cornerExponent_le_coordinateGalacticExponent_of_concise K (by omega)
    (fun i ↦ isCoordinateConcise_gcwTable K σ i)
    (by simpa using card_le_asymptoticRank_gcwTable (K := K) σ)
    (asymptoticIndependenceNumber_gcwTable_le_cornerBound (K := K) σ)
    (coordinateGalacticValues_gcwTable_nonempty K σ)

/-- **AVW Lemma 7.1**, final form: the coordinate Galactic exponent of every generalized
Coppersmith--Winograd tensor, of every parameter, is strictly above `2`.  The margin
`6/(3 - cornerExponent (q+2)) - 2` shrinks with `q`, so this alone does not give a universal
constant; see `avw_theorem_seven_one`. -/
theorem two_lt_coordinateGalacticExponent_gcwTable_corner (σ : Equiv.Perm μ) :
    2 < coordinateGalacticExponent K (gcwTable K μ σ) :=
  lt_of_lt_of_le (two_lt_six_div_sub_cornerExponent (by omega))
    (six_div_le_coordinateGalacticExponent_gcwTable_corner (K := K) σ)

end CornerBarrier

/-! ## The literal Definition 3.1 instance of Lemma 7.1 -/

section LiteralCorner

/-- **AVW Lemma 7.1 on the literal index set of Definition 3.1.**  For every integer `q` and every
permutation `σ` of `{1,…,q}`, the Galactic method applied to `CW_q^σ` cannot prove any exponent
below the explicit constant `c_q = 6/(3 - cornerExponent (q+2)) > 2`.

AVW state Lemma 7.1 for `1 ≤ q ≤ 5`, those being the parameters their Lemma 7.2 leaves open.
Nothing in the argument needs an upper *or* a lower bound on `q`, so none is assumed here; the
restriction to small `q` reappears only in the assembly of Theorem 7.1, where the better constant
of Lemma 7.2 is used as soon as it is available. -/
theorem avw_lemma_seven_one (K : Type u) [Field K] (q : ℕ) (σ : Equiv.Perm (Fin q)) :
    6 / (3 - cornerExponent (q + 2)) ≤ coordinateGalacticExponent K (gcwTable K (Fin q) σ) := by
  have h := six_div_le_coordinateGalacticExponent_gcwTable_corner (K := K) σ
  rwa [Fintype.card_fin] at h

/-- **AVW Lemma 7.1**, `2 < ω_g^{coord}(CW_q^σ)` for every `q` and every `σ`, on the literal index
set of Definition 3.1 and with no side hypothesis. -/
theorem two_lt_coordinateGalacticExponent_genCW_corner (K : Type u) [Field K] (q : ℕ)
    (σ : Equiv.Perm (Fin q)) : 2 < coordinateGalacticExponent K (gcwTable K (Fin q) σ) :=
  two_lt_coordinateGalacticExponent_gcwTable_corner σ

end LiteralCorner

/-! ### The exact arithmetic of Theorem 7.1

The universal constant of Theorem 7.1 is the minimum of the Lemma 7.2 constant `60000/29999` and
the Lemma 7.1 constants `6/(3 - cornerExponent (q+2))` for the parameters `q` that Lemma 7.2 does
not reach.  `cornerExponent` is *antitone* on `[2,∞)` --- its denominator `Q²(Q+1)² log Q` is a
product of nondecreasing nonnegative factors --- so `c_q` decreases with `q` and the minimum over
`q ≤ 5` is attained at `q = 5`, i.e. at `Q = q + 2 = 7`:

```text
cornerExponent 7 = 1/(7²·8²·log 7) = 1/(3136 log 7).
```

Both enclosures of `log 7` used below are obtained from `Analysis/Log.lean` through the identity
`log 7 = 3 log 2 - log (8/7)`, the second logarithm being computed from the atanh series at
`x = 1/15` (three terms suffice, the remainder being below `1.2·10⁻⁸`).  Combined with the
existing `log_two_le`/`log_two_ge` this gives `1.945909 ≤ log 7 ≤ 1.945913`, against the true
value `1.9459101…`.
-/

section TheoremArithmetic

open AlgebraicComplexity.Analysis

/-- The closed rational form of the Corollary-5.1 exponent gap at `Q = 7`. -/
private theorem gcw_cornerExponent_seven : cornerExponent 7 = 1 / (3136 * Real.log 7) := by
  rw [cornerExponent]
  norm_num

/-- `cornerExponent 7 ≥ 1/6103`, from `log 7 ≤ 1.945913` and `3136 · 1.945913 < 6103`.  This is
what makes the Lemma 7.2 constant `60000/29999` the *smaller* of the two constants of
Theorem 7.1: it gives `cornerExponent 7 ≥ 1/10000`, which is exactly the threshold at which
`6/(3 − cornerExponent 7)` overtakes `60000/29999`. -/
private theorem gcw_cornerExponent_seven_ge : (1 : ℝ) / 6103 ≤ cornerExponent 7 := by
  have hlog : 0 < Real.log 7 := Real.log_pos (by norm_num)
  rw [gcw_cornerExponent_seven]
  refine one_div_le_one_div_of_le (by positivity) ?_
  linarith [log_seven_le]

/-- `cornerExponent 7 ≤ 1/6102`, from `log 7 ≥ 1.945909` and `3136 · 1.945909 > 6102`. -/
private theorem gcw_cornerExponent_seven_le : cornerExponent 7 ≤ (1 : ℝ) / 6102 := by
  rw [gcw_cornerExponent_seven]
  refine one_div_le_one_div_of_le (by norm_num) ?_
  linarith [log_seven_ge]

/-- **The minimum of the Lemma 7.1 constants over `q ≤ 5` is attained at `q = 5`.**  For every
`q` with `q + 2 ≤ 7`, `6/(3 - cornerExponent 7) ≤ 6/(3 - cornerExponent (q+2))`. -/
theorem six_div_three_sub_cornerExponent_seven_le (q : ℕ) (hq : q + 2 ≤ 7) :
    6 / (3 - cornerExponent 7) ≤ 6 / (3 - cornerExponent (q + 2)) := by
  have h := cornerExponent_anti (a := q + 2) (b := 7) (by omega) hq
  have h1 : cornerExponent (q + 2) ≤ 1 := cornerExponent_le_one (by omega)
  have hpos : (0 : ℝ) < 3 - cornerExponent (q + 2) := by linarith
  gcongr

end TheoremArithmetic

/-! ## AVW Theorem 7.1 -/

section Headline

/-- **The universal constant of AVW Theorem 7.1**: the smaller of the Lemma 7.2 constant
`60000/29999` (valid for `q ≥ 6`) and the Lemma 7.1 constant `6/(3 - cornerExponent 7)` at the
largest parameter Lemma 7.2 leaves open, `q = 5`.  By
`avwTheoremSevenOneConstant_eq` the minimum is the first, and by
`two_add_le_avwTheoremSevenOneConstant` it exceeds `2 + 1/15000`. -/
noncomputable def avwTheoremSevenOneConstant : ℝ :=
  min (60000 / 29999) (6 / (3 - cornerExponent 7))

/-- The universal constant is the Lemma 7.2 constant: the large-`q` splitting argument, not the
small-`q` corner argument, is the binding constraint.

Proof sketch: `6/(3 - e) ≥ 60000/29999` is equivalent to `e ≥ 1/10000`, and the certified
enclosure `cornerExponent 7 ≥ 1/6103` (from `log 7 ≤ 1.945913`) is comfortably stronger. -/
theorem avwTheoremSevenOneConstant_eq :
    avwTheoremSevenOneConstant = 60000 / 29999 := by
  have hge := gcw_cornerExponent_seven_ge
  have hle := gcw_cornerExponent_seven_le
  have hpos : (0 : ℝ) < 3 - cornerExponent 7 := by linarith
  refine min_eq_left ?_
  rw [div_le_div_iff₀ (by norm_num) hpos]
  linarith

/-- **A certified rational lower bound for the universal constant**: `c ≥ 2 + 1/15000`.

Proof sketch: the two branches of the minimum are handled separately.  On the left,
`60000/29999 = 2 + 2/29999 > 2 + 1/15000` is rational arithmetic.  On the right,
`6/(3 - e) - 2 = 2e/(3 - e) ≥ 2e/3` for `0 < e ≤ 1`, and the certified enclosure
`cornerExponent 7 ≥ 1/6103` (from `log 7 ≤ 1.945913`) gives `2e/3 ≥ 2/18309 > 1/15000`.  The
binding branch is the left one, so `1/15000` is essentially optimal for this constant: the exact
gap is `2/29999`. -/
theorem two_add_le_avwTheoremSevenOneConstant :
    2 + (1 : ℝ) / 15000 ≤ avwTheoremSevenOneConstant := by
  have he := gcw_cornerExponent_seven_ge
  have he1 : cornerExponent 7 ≤ 1 := cornerExponent_le_one (by norm_num)
  have hpos : (0 : ℝ) < 3 - cornerExponent 7 := by linarith
  refine le_min (by norm_num) ?_
  rw [le_div_iff₀ hpos]
  nlinarith

/-- The universal constant of Theorem 7.1 is strictly above `2`. -/
theorem two_lt_avwTheoremSevenOneConstant : 2 < avwTheoremSevenOneConstant := by
  have := two_add_le_avwTheoremSevenOneConstant
  linarith

/-- **AVW Theorem 7.1**, with the explicit constant and no hypothesis whatsoever:

> there is a constant `c > 2` such that, for every parameter `q` and every permutation `σ` of the
> middle block, the Galactic method applied to the generalized Coppersmith--Winograd tensor
> `CW_q^σ` in its own variables cannot prove any exponent bound below `c`.

The constant is `avwTheoremSevenOneConstant = min (60000/29999) (6/(3 - cornerExponent 7))`,
which equals `60000/29999 = 2.0000666…` and is at least `2 + 1/15000`.

Proof sketch: three regimes, glued by a case split on `q ≥ 6`.

* `q ≥ 6`: Lemma 7.2, `avw_lemma_seven_two_of_six_le`, with the constant `60000/29999` --- itself
  the union of the `q = 6` and `7 ≤ q` splitting certificates and, for `q ≥ 24`, the stronger
  `2000/999` of route 1.
* `q ≤ 5`: Lemma 7.1, `avw_lemma_seven_one`, with the constant `6/(3 - cornerExponent (q+2))`,
  which is at least its value at `q = 5` because `cornerExponent` is antitone
  (`six_div_three_sub_cornerExponent_seven_le`).

The certificate-nonemptiness side condition of Corollary 4.3 is discharged in both regimes by
`coordinateGalacticValues_gcwTable_nonempty`. -/
theorem avw_theorem_seven_one (K : Type u) [Field K] (q : ℕ) (σ : Equiv.Perm (Fin q)) :
    avwTheoremSevenOneConstant ≤ coordinateGalacticExponent K (gcwTable K (Fin q) σ) := by
  rcases Nat.lt_or_ge q 6 with hq | hq
  · refine le_trans (min_le_right _ _) (le_trans ?_ (avw_lemma_seven_one K q σ))
    exact six_div_three_sub_cornerExponent_seven_le q (by omega)
  · exact le_trans (min_le_left _ _)
      (avw_lemma_seven_two_of_six_le K q hq σ (coordinateGalacticValues_gcwTable_nonempty K σ))

/-- **AVW Theorem 7.1**, in the existential form in which AVW state it informally: there is a
constant `c > 2` that no Galactic-method analysis of any generalized Coppersmith--Winograd tensor,
in that tensor's own variables, can beat.  The witness is `avwTheoremSevenOneConstant`. -/
theorem avw_theorem_seven_one_exists (K : Type u) [Field K] :
    ∃ c : ℝ, 2 < c ∧ ∀ (q : ℕ) (σ : Equiv.Perm (Fin q)),
      c ≤ coordinateGalacticExponent K (gcwTable K (Fin q) σ) :=
  ⟨avwTheoremSevenOneConstant, two_lt_avwTheoremSevenOneConstant,
    fun q σ ↦ avw_theorem_seven_one K q σ⟩

end Headline

/-! ### The exact arithmetic of the uniform block-entropy exponent

Alman's block-entropy bound gives, for every parameter `q ≥ 1`, every permutation `σ` and every
real `u > 0`,

```text
Ī(CW_q^σ) ≤ u^{1/3}·(q + u + 1/u)
```

(`Examples/GeneralizedCoppersmithWinogradIndependenceUpper.lean`,
`asymptoticIndependenceNumber_gcwTable_le_rpow_mul`).  Optimizing `u` exactly means solving
`4u² + qu − 2 = 0`, whose root is irrational; the *uniform* certificate used here is the rational
near-optimizer

```text
u_q = 2/(q+2),
```

for which the bound collapses to a single closed rational multiple of a cube root: writing
`x = q + 2` for the number of variables per leg,

```text
u_q^{1/3}(q + u_q + 1/u_q) = (2/x)^{1/3} · (3x² − 4x + 4)/(2x).
```

The section below certifies that this is at most `x^{93/100}` for every `q ≥ 1`
(`gcw_entropy_rpow_bound`), i.e. that `93/100` is a *uniform* exponent for the whole family.  The
sharp exponent of the same certificate is `log(2.7663…)/log 3 = 0.92610…` at `q = 1` and decreases
in `q`, so `93/100` costs about `4·10⁻³` at the binding parameter and nothing elsewhere; the sharp
exponent of the *optimal* `u` is `0.92232…` at `q = 1`.  Anything below `0.9604` suffices for the
sharpened Theorem 7.1 below, since at that value the entropy constant `6/(2+s)` overtakes the
`q = 0` corner constant.

The proof is the same base-plus-step shape as `gcw_log_bound`, but with the *sharp* logarithm
increment bounds of `Analysis/LogConstants.lean` rather than `Real.log_le_sub_one_of_pos`, which at
the binding parameter `x = 3` overshoots the increment by `20%` *and* understates the decrement by
`13%` --- together forcing `s ≥ 1.35`, i.e. no bound at all.

* the **base** `q = 1` is `(1/3)(log 2 − log 3) + log(19/6) ≤ (93/100)·log 3`, which after
  `19/6 = 3·(19/18)` is the linear combination `(1/3)log 2 + log(19/18) ≤ (79/300)·log 3` of the
  certified enclosures `log 2 ≤ 0.693148`, `log 3 ≥ 1.098611` and `log(19/18) ≤ 0.054068` (slack
  `4.2·10⁻³`);
* the **step** is `log H(x+1) − log H(x) ≤ (379/300)(log(x+1) − log x)` for real `x ≥ 3`, where
  `H(x) = (3x² − 4x + 4)/(2x)` and `379/300 = 93/100 + 1/3` absorbs the `x^{-1/3}` factor.  With
  `A = x(3x²+2x+3)` and `B = (x+1)(3x²−4x+4)` --- so that `H(x+1)/H(x) = A/B` --- the two sharp
  enclosures turn it into the polynomial inequality `75(2x+1)(A² − B²) ≤ 379·A·B`, whose difference
  has *nonnegative* coefficients in `x − 3`:

  ```text
  379AB − 75(2x+1)(A²−B²) = 711(x−3)⁶ + 9435(x−3)⁵ + 48418(x−3)⁴ + 117567(x−3)³
                            + 128873(x−3)² + 50484(x−3) + 19632.
  ```

  The true increment ratio at `x = 3` is `1.22145…` against the available `379/300 = 1.26333…`.
-/

section EntropyArithmetic

open AlgebraicComplexity.Analysis

/-- **The induction step of the uniform block-entropy exponent.**  For every real `x ≥ 3`,

```text
log H(x+1) − log H(x) ≤ (379/300)·(log(x+1) − log x),     H(x) = (3x² − 4x + 4)/(2x).
```

Proof sketch: `H(x+1)/H(x) = A/B` with `A = 3x³+2x²+3x` and `B = 3x³−x²+4` (both numerators over
the common denominator `2x(x+1)`).  `log_sub_log_le_sq_div` bounds the left side by
`(A²−B²)/(2AB)` and `two_div_le_log_succ_sub_log` bounds the right side below by
`(379/300)·2/(2x+1)`, and the resulting polynomial inequality
`75(2x+1)(A²−B²) ≤ 379AB` is the displayed nonnegative expansion in `x − 3`. -/
private theorem gcw_entropy_log_step {x : ℝ} (hx : 3 ≤ x) :
    Real.log ((3 * (x + 1) ^ 2 - 4 * (x + 1) + 4) / (2 * (x + 1)))
        - Real.log ((3 * x ^ 2 - 4 * x + 4) / (2 * x))
      ≤ (379 / 300 : ℝ) * (Real.log (x + 1) - Real.log x) := by
  have hx0 : (0 : ℝ) < x := by linarith
  have hx1 : (0 : ℝ) < x + 1 := by linarith
  set A : ℝ := 3 * x ^ 3 + 2 * x ^ 2 + 3 * x with hA
  set B : ℝ := 3 * x ^ 3 - x ^ 2 + 4 with hB
  have hBpos : (0 : ℝ) < B := by rw [hB]; nlinarith
  have hApos : (0 : ℝ) < A := by rw [hA]; nlinarith
  have hBA : B ≤ A := by rw [hA, hB]; nlinarith
  have hD : (0 : ℝ) < 2 * x * (x + 1) := by positivity
  have e1 : (3 * (x + 1) ^ 2 - 4 * (x + 1) + 4) / (2 * (x + 1)) = A / (2 * x * (x + 1)) := by
    rw [hA]; field_simp; ring
  have e2 : (3 * x ^ 2 - 4 * x + 4) / (2 * x) = B / (2 * x * (x + 1)) := by
    rw [hB]; field_simp; ring
  rw [e1, e2, Real.log_div (ne_of_gt hApos) (ne_of_gt hD),
    Real.log_div (ne_of_gt hBpos) (ne_of_gt hD)]
  have hstep := log_sub_log_le_sq_div hBpos hBA
  have hlog := two_div_le_log_succ_sub_log hx0
  have hnum : (A ^ 2 - B ^ 2) / (2 * A * B) ≤ (379 / 300 : ℝ) * (2 / (2 * x + 1)) := by
    have hxx : (0 : ℝ) < 2 * x + 1 := by linarith
    have hrw : (379 / 300 : ℝ) * (2 / (2 * x + 1)) = 379 / (150 * (2 * x + 1)) := by
      field_simp; ring
    rw [hrw, div_le_div_iff₀ (by positivity) (by positivity)]
    have key : 379 * A * B - 75 * (2 * x + 1) * (A ^ 2 - B ^ 2)
        = 711 * (x - 3) ^ 6 + 9435 * (x - 3) ^ 5 + 48418 * (x - 3) ^ 4
          + 117567 * (x - 3) ^ 3 + 128873 * (x - 3) ^ 2 + 50484 * (x - 3) + 19632 := by
      rw [hA, hB]; ring
    have hy : (0 : ℝ) ≤ x - 3 := by linarith
    have h2 : (0 : ℝ) ≤ (x - 3) ^ 2 := by positivity
    have h3 : (0 : ℝ) ≤ (x - 3) ^ 3 := by positivity
    have h4 : (0 : ℝ) ≤ (x - 3) ^ 4 := by positivity
    have h5 : (0 : ℝ) ≤ (x - 3) ^ 5 := by positivity
    have h6 : (0 : ℝ) ≤ (x - 3) ^ 6 := by positivity
    nlinarith [key, hy, h2, h3, h4, h5, h6]
  have hmul : (379 / 300 : ℝ) * (2 / (2 * x + 1))
      ≤ (379 / 300 : ℝ) * (Real.log (x + 1) - Real.log x) :=
    mul_le_mul_of_nonneg_left hlog (by norm_num)
  linarith

/-- **The uniform block-entropy exponent in logarithmic form**: for every natural `q ≥ 1`, with
`x = q + 2`,

```text
(1/3)(log 2 − log x) + log ((3x² − 4x + 4)/(2x)) ≤ (93/100)·log x.
```

Proved by `Nat.le_induction` from the certified base case at `q = 1` and `gcw_entropy_log_step`. -/
theorem gcw_entropy_log_bound (q : ℕ) (hq : 1 ≤ q) :
    (1 / 3 : ℝ) * (Real.log 2 - Real.log ((q : ℝ) + 2))
        + Real.log ((3 * ((q : ℝ) + 2) ^ 2 - 4 * ((q : ℝ) + 2) + 4) / (2 * ((q : ℝ) + 2)))
      ≤ (93 / 100 : ℝ) * Real.log ((q : ℝ) + 2) := by
  induction q, hq using Nat.le_induction with
  | base =>
      have e : ((1 : ℕ) : ℝ) + 2 = 3 := by norm_num
      rw [e]
      have e2 : (3 * (3 : ℝ) ^ 2 - 4 * 3 + 4) / (2 * 3) = 3 * (19 / 18) := by norm_num
      rw [e2, Real.log_mul (by norm_num) (by norm_num)]
      linarith [log_two_le, log_three_ge, log_nineteen_eighteenths_le]
  | succ n hn ih =>
      have hn' : (3 : ℝ) ≤ (n : ℝ) + 2 := by
        have : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
        linarith
      have e : ((n + 1 : ℕ) : ℝ) + 2 = ((n : ℝ) + 2) + 1 := by push_cast; ring
      rw [e]
      linarith [gcw_entropy_log_step hn', ih]

/-- **The uniform block-entropy exponent.**  For every natural `q ≥ 1`, the rational near-optimizer
`u_q = 2/(q+2)` of Alman's block-entropy bound satisfies

```text
u_q^{1/3}·(q + u_q + 1/u_q) ≤ (q+2)^{93/100}.
```

The left side is the value of the analytic bound `u^{1/3}(q + u + 1/u)` at `u = u_q`; the right
side is the leg-dimension count `q + 2` raised to a *uniform* exponent below `1`, which is what
AVW Corollary 4.3 consumes.  At `q = 1` the two sides are `2.7663…` and `2.7777…`. -/
theorem gcw_entropy_rpow_bound (q : ℕ) (hq : 1 ≤ q) :
    ((2 : ℝ) / ((q : ℝ) + 2)) ^ ((3 : ℝ)⁻¹)
        * ((q : ℝ) + 2 / ((q : ℝ) + 2) + ((q : ℝ) + 2) / 2)
      ≤ ((q : ℝ) + 2) ^ ((93 : ℝ) / 100) := by
  have hx : (3 : ℝ) ≤ (q : ℝ) + 2 := by
    have : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
    linarith
  have hxpos : (0 : ℝ) < (q : ℝ) + 2 := by linarith
  have hupos : (0 : ℝ) < (2 : ℝ) / ((q : ℝ) + 2) := by positivity
  have hH : (q : ℝ) + 2 / ((q : ℝ) + 2) + ((q : ℝ) + 2) / 2
      = (3 * ((q : ℝ) + 2) ^ 2 - 4 * ((q : ℝ) + 2) + 4) / (2 * ((q : ℝ) + 2)) := by
    field_simp; ring
  have hHpos : (0 : ℝ)
      < (3 * ((q : ℝ) + 2) ^ 2 - 4 * ((q : ℝ) + 2) + 4) / (2 * ((q : ℝ) + 2)) := by
    apply div_pos _ (by linarith)
    nlinarith
  rw [hH]
  have hL : ((2 : ℝ) / ((q : ℝ) + 2)) ^ ((3 : ℝ)⁻¹)
        * ((3 * ((q : ℝ) + 2) ^ 2 - 4 * ((q : ℝ) + 2) + 4) / (2 * ((q : ℝ) + 2)))
      = Real.exp (Real.log ((2 : ℝ) / ((q : ℝ) + 2)) * (3 : ℝ)⁻¹
          + Real.log ((3 * ((q : ℝ) + 2) ^ 2 - 4 * ((q : ℝ) + 2) + 4)
              / (2 * ((q : ℝ) + 2)))) := by
    rw [Real.rpow_def_of_pos hupos, Real.exp_add, Real.exp_log hHpos]
  have hR : ((q : ℝ) + 2) ^ ((93 : ℝ) / 100)
      = Real.exp (Real.log ((q : ℝ) + 2) * (93 / 100)) := Real.rpow_def_of_pos hxpos _
  rw [hL, hR]
  refine Real.exp_le_exp.mpr ?_
  rw [Real.log_div (by norm_num) (ne_of_gt hxpos)]
  linarith [gcw_entropy_log_bound q hq]

end EntropyArithmetic

/-! ## The barrier from the block-entropy bound

The two statements below are the *hypothesis-taking* halves of the sharpened barrier: they consume
Alman's block-entropy bound `Ī(CW_q^σ) ≤ u^{1/3}(q + u + 1/u)` --- proved, for every `u > 0` and
every `q ≥ 1`, by `asymptoticIndependenceNumber_gcwTable_le_rpow_mul` of
`Examples/GeneralizedCoppersmithWinogradIndependenceUpper.lean` --- and produce the Corollary-4.3
shape and the Galactic constant.

They keep the bound as a hypothesis rather than importing it, because
`GeneralizedCoppersmithWinogradIndependenceUpper` is *downstream* of this file
(`…IndependenceUpper` imports `…IndependenceLower`, which imports this module), so the implication
must be stated here and discharged there.  Discharging it is a one-liner:
`asymptoticIndependenceNumber_gcwTable_le_rpow_mul σ hq` has exactly the hypothesis shape below.
-/

section EntropyBarrier

variable {K : Type u} {μ : Type v} [Fintype μ] [DecidableEq μ]

/-- **Alman's block-entropy bound in the shape Corollary 4.3 consumes.**  If the asymptotic
independence number of `CW_q^σ` obeys the analytic bound `u^{1/3}(q + u + 1/u)` for every `u > 0`
--- which it does for every `q ≥ 1`, by
`asymptoticIndependenceNumber_gcwTable_le_rpow_mul` --- then it obeys the absolute bound

```text
Ī(CW_q^σ) ≤ (q+2)^{1 − 7/100}
```

with a gap `7/100` uniform in `q`.  The certificate is the rational parameter `u_q = 2/(q+2)` and
the exact arithmetic is `gcw_entropy_rpow_bound`. -/
theorem asymptoticIndependenceNumber_gcwTable_le_rpow_card_of_le_rpow_mul [CommSemiring K]
    (σ : Equiv.Perm μ) (hq : 1 ≤ Fintype.card μ)
    (hI : ∀ u : ℝ, 0 < u → asymptoticIndependenceNumber (gcwTable K μ σ)
      ≤ u ^ ((3 : ℝ)⁻¹) * ((Fintype.card μ : ℝ) + u + u⁻¹)) :
    asymptoticIndependenceNumber (gcwTable K μ σ)
      ≤ ((Fintype.card μ + 2 : ℕ) : ℝ) ^ (1 - (7 : ℝ) / 100) := by
  have hqR : (1 : ℝ) ≤ (Fintype.card μ : ℝ) := by exact_mod_cast hq
  have hxpos : (0 : ℝ) < (Fintype.card μ : ℝ) + 2 := by linarith
  have hupos : (0 : ℝ) < (2 : ℝ) / ((Fintype.card μ : ℝ) + 2) := by positivity
  have hinv : ((2 : ℝ) / ((Fintype.card μ : ℝ) + 2))⁻¹ = ((Fintype.card μ : ℝ) + 2) / 2 := by
    rw [inv_div]
  have hcast : ((Fintype.card μ + 2 : ℕ) : ℝ) = (Fintype.card μ : ℝ) + 2 := by push_cast; ring
  have hexp : (1 : ℝ) - (7 : ℝ) / 100 = (93 : ℝ) / 100 := by norm_num
  rw [hcast, hexp]
  refine le_trans (hI _ hupos) ?_
  rw [hinv]
  exact gcw_entropy_rpow_bound _ hq

/-- **The sharpened Galactic barrier for `CW_q^σ`, every `q ≥ 1`.**  Given Alman's block-entropy
bound, the Galactic method applied to `CW_q^σ` in its own variables cannot prove any exponent
bound below

```text
6/(3 − 7/100) = 600/293 = 2.04778…,
```

*uniformly in `q`* --- a genuine improvement on AVW's own `min (60000/29999) (6/(3 −
cornerExponent (q+2)))`, whose value degrades towards `2` as `q` grows.

Proof sketch: `asymptoticIndependenceNumber_gcwTable_le_rpow_card_of_le_rpow_mul` supplies the
gap-parametric hypothesis of
`six_div_sub_le_coordinateGalacticExponent_of_le_rpow_card` with `Q = q + 2` and `g = 7/100`; the
conciseness and asymptotic-rank inputs are `isCoordinateConcise_gcwTable` and
`card_le_asymptoticRank_gcwTable`, and the certificate side condition is discharged by
`coordinateGalacticValues_gcwTable_nonempty`. -/
theorem six_div_le_coordinateGalacticExponent_gcwTable_entropy [Field K]
    (σ : Equiv.Perm μ) (hq : 1 ≤ Fintype.card μ)
    (hI : ∀ u : ℝ, 0 < u → asymptoticIndependenceNumber (gcwTable K μ σ)
      ≤ u ^ ((3 : ℝ)⁻¹) * ((Fintype.card μ : ℝ) + u + u⁻¹)) :
    (600 : ℝ) / 293 ≤ coordinateGalacticExponent K (gcwTable K μ σ) := by
  have hmain := six_div_sub_le_coordinateGalacticExponent_of_le_rpow_card K
    (Q := Fintype.card μ + 2) (g := (7 : ℝ) / 100) (by omega) (by norm_num)
    (fun i ↦ isCoordinateConcise_gcwTable K σ i)
    (by simpa using card_le_asymptoticRank_gcwTable (K := K) σ)
    (asymptoticIndependenceNumber_gcwTable_le_rpow_card_of_le_rpow_mul σ hq hI)
    (coordinateGalacticValues_gcwTable_nonempty K σ)
  rwa [show (3 : ℝ) - (7 : ℝ) / 100 = 293 / 100 by norm_num,
    show (6 : ℝ) / (293 / 100) = 600 / 293 by norm_num] at hmain

end EntropyBarrier

/-! ### The exact arithmetic of the sharpened Theorem 7.1

The sharpened universal constant is the minimum of the *uniform* entropy constant `600/293`, valid
for every `q ≥ 1`, and the single corner constant that the entropy bound does not reach, namely the
one at `q = 0` (empty middle block, `Q = q + 2 = 2` variables per leg):

```text
cornerExponent 2 = 1/(2²·3²·log 2) = 1/(36 log 2) = 0.0400748…,
6/(3 − cornerExponent 2) = 2.027078….
```

Unlike the original Theorem 7.1, where the *splitting* constant `60000/29999` was the binding one,
here the binding branch is the corner argument at `q = 0`: the entropy branch `2.04778…` is the
larger of the two.  Both enclosures below come from `log 2` alone.
-/

section SharpTheoremArithmetic

open AlgebraicComplexity.Analysis

/-- The closed rational form of the Corollary-5.1 exponent gap at `Q = 2`. -/
private theorem gcw_cornerExponent_two : cornerExponent 2 = 1 / (36 * Real.log 2) := by
  rw [cornerExponent]
  norm_num

/-- `cornerExponent 2 ≥ 1/25`, from `log 2 ≤ 0.693148` and `36 · 0.693148 < 25`.  This is what
certifies the rational lower bound `2 + 27/1000` for the sharpened constant. -/
private theorem gcw_cornerExponent_two_ge : (1 : ℝ) / 25 ≤ cornerExponent 2 := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rw [gcw_cornerExponent_two]
  refine one_div_le_one_div_of_le (by positivity) ?_
  linarith [log_two_le]

/-- `cornerExponent 2 ≤ 1/24`, from `log 2 ≥ 0.693147` and `36 · 0.693147 > 24`.  This is what
shows the corner branch, not the entropy branch, is the binding one. -/
private theorem gcw_cornerExponent_two_le : cornerExponent 2 ≤ (1 : ℝ) / 24 := by
  rw [gcw_cornerExponent_two]
  refine one_div_le_one_div_of_le (by norm_num) ?_
  linarith [log_two_ge]

end SharpTheoremArithmetic

/-! ## AVW Theorem 7.1, sharpened by the block-entropy bound -/

section SharpHeadline

/-- **The sharpened universal constant of AVW Theorem 7.1**: the smaller of the uniform
block-entropy constant `600/293` (valid for every `q ≥ 1`) and the corner constant
`6/(3 − cornerExponent 2)` at the one parameter the entropy bound does not reach, `q = 0`.

By `avwTheoremSevenOneSharpConstant_eq` the minimum is the second, `2.027078…`, and by
`two_add_le_avwTheoremSevenOneSharpConstant` it is at least `2 + 27/1000`.  This is three orders
of magnitude above the margin `2 + 1/15000` of `avwTheoremSevenOneConstant`, which the splitting
argument of AVW Lemma 7.2 forced. -/
noncomputable def avwTheoremSevenOneSharpConstant : ℝ :=
  min (600 / 293) (6 / (3 - cornerExponent 2))

/-- The sharpened universal constant is the `q = 0` corner constant: with the block-entropy bound
in hand, the binding constraint is the *one* parameter the entropy bound does not cover.

Proof sketch: `6/(3 − e) ≤ 600/293` is equivalent to `e ≤ 7/100`, and the certified enclosure
`cornerExponent 2 ≤ 1/24` (from `log 2 ≥ 0.693147`) is comfortably stronger. -/
theorem avwTheoremSevenOneSharpConstant_eq :
    avwTheoremSevenOneSharpConstant = 6 / (3 - cornerExponent 2) := by
  have hle := gcw_cornerExponent_two_le
  have hge := gcw_cornerExponent_two_ge
  have hpos : (0 : ℝ) < 3 - cornerExponent 2 := by linarith
  refine min_eq_right ?_
  rw [div_le_div_iff₀ hpos (by norm_num)]
  linarith

/-- **A certified rational lower bound for the sharpened universal constant**: `c ≥ 2 + 27/1000`.

Proof sketch: on the entropy branch, `600/293 = 2.04778… > 2.027` is rational arithmetic.  On the
corner branch, `6/(3 − e) ≥ 2027/1000` is equivalent to `2027·e ≥ 81`, and the certified enclosure
`cornerExponent 2 ≥ 1/25` (from `log 2 ≤ 0.693148`) gives `2027/25 = 81.08`.  The binding branch is
the corner one, whose exact value is `2.027078…`, so `27/1000` is essentially optimal here. -/
theorem two_add_le_avwTheoremSevenOneSharpConstant :
    2 + (27 : ℝ) / 1000 ≤ avwTheoremSevenOneSharpConstant := by
  have hge := gcw_cornerExponent_two_ge
  have hle : cornerExponent 2 ≤ 1 := cornerExponent_le_one (by norm_num)
  have hpos : (0 : ℝ) < 3 - cornerExponent 2 := by linarith
  refine le_min (by norm_num) ?_
  rw [le_div_iff₀ hpos]
  linarith

/-- The sharpened universal constant is strictly above `2`, by more than `1/40`. -/
theorem two_lt_avwTheoremSevenOneSharpConstant : 2 < avwTheoremSevenOneSharpConstant := by
  have := two_add_le_avwTheoremSevenOneSharpConstant
  linarith

/-- **AVW Theorem 7.1, sharpened**: with Alman's block-entropy bound as input, the Galactic method
applied to any generalized Coppersmith--Winograd tensor `CW_q^σ` in its own variables cannot prove
any exponent bound below

```text
avwTheoremSevenOneSharpConstant = min (600/293) (6/(3 − cornerExponent 2)) = 2.027078…,
```

against the `2.0000666…` of `avw_theorem_seven_one`.

The hypothesis is exactly `asymptoticIndependenceNumber_gcwTable_le_rpow_mul` of
`Examples/GeneralizedCoppersmithWinogradIndependenceUpper.lean`, which is downstream of this file
and therefore cannot be imported here; discharging it there turns this into an unconditional
statement.

Proof sketch: two regimes.

* `q ≥ 1`: `six_div_le_coordinateGalacticExponent_gcwTable_entropy`, the uniform constant
  `600/293` from the exponent `93/100` of `gcw_entropy_rpow_bound`.
* `q = 0`: the middle block is empty and the entropy bound does not apply; AVW Lemma 7.1
  (`avw_lemma_seven_one`) gives `6/(3 − cornerExponent 2)`, which is the binding branch. -/
theorem avw_theorem_seven_one_sharp (K : Type u) [Field K] (q : ℕ) (σ : Equiv.Perm (Fin q))
    (hI : 1 ≤ q → ∀ u : ℝ, 0 < u → asymptoticIndependenceNumber (gcwTable K (Fin q) σ)
      ≤ u ^ ((3 : ℝ)⁻¹) * ((q : ℝ) + u + u⁻¹)) :
    avwTheoremSevenOneSharpConstant ≤ coordinateGalacticExponent K (gcwTable K (Fin q) σ) := by
  rcases Nat.eq_zero_or_pos q with hq | hq
  · subst hq
    refine le_trans (min_le_right _ _) ?_
    simpa using avw_lemma_seven_one K 0 σ
  · refine le_trans (min_le_left _ _) ?_
    have hq1 : 1 ≤ q := hq
    have hcard : 1 ≤ Fintype.card (Fin q) := by simpa using hq1
    have hI' : ∀ u : ℝ, 0 < u → asymptoticIndependenceNumber (gcwTable K (Fin q) σ)
        ≤ u ^ ((3 : ℝ)⁻¹) * ((Fintype.card (Fin q) : ℝ) + u + u⁻¹) := by
      simpa using hI hq1
    exact six_div_le_coordinateGalacticExponent_gcwTable_entropy σ hcard hI'

/-- **AVW Theorem 7.1, sharpened, in existential form**: given Alman's block-entropy bound for the
whole family, there is a constant `c ≥ 2 + 27/1000` that no Galactic-method analysis of any
generalized Coppersmith--Winograd tensor, in that tensor's own variables, can beat.  The witness is
`avwTheoremSevenOneSharpConstant = 2.027078…`. -/
theorem avw_theorem_seven_one_exists_sharp (K : Type u) [Field K]
    (hI : ∀ (q : ℕ) (σ : Equiv.Perm (Fin q)), 1 ≤ q → ∀ u : ℝ, 0 < u →
      asymptoticIndependenceNumber (gcwTable K (Fin q) σ)
        ≤ u ^ ((3 : ℝ)⁻¹) * ((q : ℝ) + u + u⁻¹)) :
    ∃ c : ℝ, 2 + (27 : ℝ) / 1000 ≤ c ∧ ∀ (q : ℕ) (σ : Equiv.Perm (Fin q)),
      c ≤ coordinateGalacticExponent K (gcwTable K (Fin q) σ) :=
  ⟨avwTheoremSevenOneSharpConstant, two_add_le_avwTheoremSevenOneSharpConstant,
    fun q σ ↦ avw_theorem_seven_one_sharp K q σ (hI q σ)⟩

end SharpHeadline

end AlgebraicComplexity.Examples
