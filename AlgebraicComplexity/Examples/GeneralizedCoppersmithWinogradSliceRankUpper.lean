/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.GeneralizedCoppersmithWinogradIndependenceUpper
import AlgebraicComplexity.Tensor.SliceRankBlockEntropy

/-!
# The block-entropy upper bound on `S̃(CW_q^σ)`

This file proves the bound that [Alman2019, §5.5.1] actually states: an upper bound on the
**asymptotic slice rank** of the generalized Coppersmith--Winograd tensors

```text
CW_q^σ = x₀y₀z_{q+1} + x₀y_{q+1}z₀ + x_{q+1}y₀z₀ + ∑ᵢ (xᵢy_{σ(i)}z₀ + xᵢy₀zᵢ + x₀yᵢzᵢ)
```

from the classical six-block partition, through
`Tensor.asymptoticSliceRank_coordinateTensor_le_of_blockEntropy` (Theorem 5.3, see
`Tensor/SliceRankBlockEntropy.lean`).

Every numerical input is shared with `Examples/GeneralizedCoppersmithWinogradIndependenceUpper.lean`:
the block labelling `gcwCoarseLabelling`, the six-block cover `gcwTable_blockCover`, and the four
block value certificates `gcwBlockLegValue_le_of_reference`, `gcwBlockLegValue_le_rpow_mul`,
`gcwBlockLegValue_fin_six_le` and `gcwBlockLegValue_fin_one_le`.  Only the invariant differs, so
each theorem below is a one-line application.  Since `Ī ≤ S̃`
(`Tensor.asymptoticIndependenceNumber_le_asymptoticSliceRank`), the bounds here are formally
stronger than their `Ī` twins over a field; the `Ī` file is kept because it needs no field
hypothesis and states its bounds without mentioning the abstract tensor.

## Main results

* `asymptoticSliceRank_gcwTable_le_rpow_mul` (**the headline analytic bound**): for every `q ≥ 1`,
  every `σ` and every real `u > 0`,

  ```text
  S̃(CW_q^σ) ≤ u^{1/3} · (q + u + 1/u).
  ```

  The infimum over `u > 0` of the right-hand side is Alman's

  ```text
  S̃(CW_{q,σ}) = sup_{v ∈ [0,1/3]} q^{2(1/3−v)} / (v^v (2/3−2v)^{2/3−2v} (1/3+v)^{1/3+v}),
  ```

  the two being Legendre-dual descriptions of the same number; the optimal `u` is the positive root
  of `4u² + qu − 2 = 0`.  Alman proves this bound is *tight* (his Theorem 5.6, not formalized), so
  the inequality here is the whole content.
* `asymptoticSliceRank_gcwTable_le_of_reference`: the general reference-vector form.
* `asymptoticSliceRank_gcwTable_fin_six_le`: `S̃(CW_6^σ) ≤ 6.45`, against Alman's exact
  `6.44493…`; `asymptoticSliceRank_gcwTable_fin_one_le`: `S̃(CW_1^σ) ≤ 2.7552`, against his exact
  `2.7551…` (the value that binds the barrier of
  `Examples/GeneralizedCoppersmithWinogradUniversalBarrier.lean`).

## Position in the library

Layer 4 (`AlgebraicComplexity/Examples/`), a named client.  It imports the `Ī` client for the
shared partition data and the layer-1 slice-rank entropy bound, and nothing else.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor

universe u

section Upper

variable {K : Type u} [CommSemiring K] [Nontrivial K]
variable {μ : Type} [Fintype μ] [DecidableEq μ]

/-- **Alman's Theorem 5.3 on `CW_q^σ`, in reference-vector form.**  Let `r` be a probability vector
with positive weights on the three blocks `{0}`, `{1,…,q}`, `{q+1}`.  If

```text
(q / r_middle)² ≤ (1 / r_last) · (1 / r_zero)      and      (1 / r_last) · (1 / r_zero)² ≤ M³,
```

then `S̃(CW_q^σ) ≤ M`.

Proof: `Tensor.asymptoticSliceRank_coordinateTensor_le_of_blockEntropy` applied to the six-block
cover `gcwTable_blockCover` and the block value certificate `gcwBlockLegValue_le_of_reference`. -/
theorem asymptoticSliceRank_gcwTable_le_of_reference (σ : Equiv.Perm μ)
    (hq : 1 ≤ Fintype.card μ) {r : CWBlock → ℝ} (hr : ∀ a, 0 < r a) (hrsum : ∑ a, r a = 1)
    {M : ℝ} (hM : 0 ≤ M)
    (hratio : ((Fintype.card μ : ℝ) / r .middle) ^ 2 ≤ (1 / r .last) * (1 / r .zero))
    (hcube : (1 / r .last) * (1 / r .zero) ^ 2 ≤ M ^ 3) :
    Tensor.asymptoticSliceRank (coordinateTensor (gcwTable K μ σ)) ≤ M :=
  Tensor.asymptoticSliceRank_coordinateTensor_le_of_blockEntropy
    (blk := gcwCoarseLabelling μ) (β := gcwBlockAddress)
    (fun s hs ↦ gcwTable_blockCover (K := K) σ s hs) hM
    (gcwBlockLegValue_le_of_reference hq hr hrsum hM hratio hcube)

/-- **The closed-form block-entropy bound on `S̃(CW_q^σ)`** [Alman2019, §5.5.1].  For every
parameter `q ≥ 1`, every middle permutation `σ` and every real `u > 0`,

```text
S̃(CW_q^σ) ≤ u^{1/3} · (q + u + 1/u).
```

Numerically the optimum over `u` is `2.7551…` at `q = 1` and `6.44493…` at `q = 6`, reproducing the
table on p. 71 of [Alman2019]. -/
theorem asymptoticSliceRank_gcwTable_le_rpow_mul (σ : Equiv.Perm μ)
    (hq : 1 ≤ Fintype.card μ) {u : ℝ} (hu : 0 < u) :
    Tensor.asymptoticSliceRank (coordinateTensor (gcwTable K μ σ)) ≤
      u ^ ((3 : ℝ)⁻¹) * ((Fintype.card μ : ℝ) + u + u⁻¹) :=
  Tensor.asymptoticSliceRank_coordinateTensor_le_of_blockEntropy
    (blk := gcwCoarseLabelling μ) (β := gcwBlockAddress)
    (fun s hs ↦ gcwTable_blockCover (K := K) σ s hs)
    (by
      have : (0 : ℝ) < (Fintype.card μ : ℝ) := by exact_mod_cast hq
      positivity)
    (gcwBlockLegValue_le_rpow_mul hq hu)

/-- **`S̃(CW_6^σ) ≤ 6.45`** for every permutation `σ` of the six middle coordinates, from the
rational certificate `u = (13/20)³`, whose value is `6.4453701…`.  Alman's exact value is
`6.44493…` [Alman2019, p. 71]. -/
theorem asymptoticSliceRank_gcwTable_fin_six_le (σ : Equiv.Perm (Fin 6)) :
    Tensor.asymptoticSliceRank (coordinateTensor (gcwTable K (Fin 6) σ)) ≤ 6.45 :=
  Tensor.asymptoticSliceRank_coordinateTensor_le_of_blockEntropy
    (blk := gcwCoarseLabelling (Fin 6)) (β := gcwBlockAddress)
    (fun s hs ↦ gcwTable_blockCover (K := K) σ s hs) (by norm_num)
    gcwBlockLegValue_fin_six_le

/-- **`S̃(CW_1^σ) ≤ 2.7552`**, the smallest parameter of Alman's table on p. 71 of [Alman2019],
whose exact value is `2.7551…`.  The certificate is `u = (21/25)³`, for which the analytic bound
evaluates to `474609871/172265625 = 2.7551049…`.

This is the instance that binds the universal-method barrier: the exponent
`s = log_{q+2} S̃(CW_q^σ)` of Corollary 5.2 is *largest* at `q = 1`. -/
theorem asymptoticSliceRank_gcwTable_fin_one_le (σ : Equiv.Perm (Fin 1)) :
    Tensor.asymptoticSliceRank (coordinateTensor (gcwTable K (Fin 1) σ)) ≤ 2.7552 :=
  Tensor.asymptoticSliceRank_coordinateTensor_le_of_blockEntropy
    (blk := gcwCoarseLabelling (Fin 1)) (β := gcwBlockAddress)
    (fun s hs ↦ gcwTable_blockCover (K := K) σ s hs) (by norm_num)
    gcwBlockLegValue_fin_one_le

end Upper

end AlgebraicComplexity.Examples
