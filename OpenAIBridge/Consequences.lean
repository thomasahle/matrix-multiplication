/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.AsymptoticRank
import AlgebraicComplexity.MatrixMultiplication.RankComplexityRecursion
import AlgebraicComplexity.MatrixMultiplication.RectangularInterpolation
import OpenAIBridge.NineQuarters

/-!
# What `ω ≤ 9/4` gives in this library

`OpenAIBridge/NineQuarters.lean` proves `omega K ≤ 9/4` over every field from the vendored
development in `ThirdParty/OAI/`.  The theorems here push that one inequality through machinery
this repository already has.  They contain no new mathematics; they are the readings of the bound
that the rest of the library is phrased in.

## Main results

* `omega_lt`: `omega K < c` for every `c > 9/4`, the strict shape used by `Frontier.OmegaBound`.
* `rectangularOmega_le`: `ω(κ) ≤ 2 + κ/4` for `0 ≤ κ ≤ 1`, by the interpolation bound.
* `asymptoticRank_matrixMultiplication_le`: `R̃(⟨n,n,n⟩) ≤ n^(9/4)`.
* `exists_straightline_matrixProduct`: for every `τ > 9/4`, straight-line programs in this
  repository's own model (`MatrixMultiplication/RankComplexity.lean`) computing the `n × n`
  product with at most `C · n^τ` arithmetic operations.

All of them hold over an arbitrary field.
-/

namespace AlgebraicComplexity.OpenAIBridge

open Tensor

universe u

variable (K : Type u) [Field K]

/-- `omega K < c` for every `c > 9/4`: the strict form of the bound. -/
theorem omega_lt {c : ℝ} (hc : 9 / 4 < c) : omega K < c :=
  lt_of_le_of_lt (omega_le_nine_quarters K) hc

/-- The rectangular exponent satisfies `ω(κ) ≤ 2 + κ/4` for `0 ≤ κ ≤ 1`. -/
theorem rectangularOmega_le {κ : ℝ} (hκ₀ : 0 ≤ κ) (hκ₁ : κ ≤ 1) :
    rectangularOmega K κ ≤ 2 + κ / 4 := by
  have h := rectangularOmega_le_interpolation K hκ₀ hκ₁
  have h9 := omega_le_nine_quarters K
  nlinarith

/-- The asymptotic rank of `⟨n,n,n⟩` is at most `n^(9/4)`. -/
theorem asymptoticRank_matrixMultiplication_le {n : ℕ} (hn : 1 ≤ n) :
    asymptoticRank (matrixMultiplication (K := K) n n n) ≤ (n : ℝ) ^ (9 / 4 : ℝ) := by
  rw [asymptoticRank_matrixMultiplication_eq_rpow_omega hn]
  exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn) (omega_le_nine_quarters K)

/-- For every exponent `τ > 9/4` there is a constant `C` and, for every `n ≥ 1`, a straight-line
program computing the `n × n` matrix product over `K` with at most `C · n^τ` arithmetic
operations. -/
theorem exists_straightline_matrixProduct {τ : ℝ} (hτ : 9 / 4 < τ) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
      ∃ p : Straightline K (Fin n × Fin n) ((Fin n × Fin n) ⊕ (Fin n × Fin n)),
        (∀ (x y : Fin n × Fin n → K) (z : Fin n × Fin n),
            p.eval (Sum.elim x y) z = matrixProductMap (K := K) n n n x y z)
          ∧ (p.totalOps : ℝ) ≤ C * (n : ℝ) ^ τ :=
  exists_straightline_matrixProduct_of_omega_lt (omega_lt K hτ)

end AlgebraicComplexity.OpenAIBridge
