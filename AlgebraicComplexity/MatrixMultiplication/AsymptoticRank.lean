/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.Exponent
import AlgebraicComplexity.MatrixMultiplication.TypeExtraction
import AlgebraicComplexity.Tensor.AsymptoticRankCalculus
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# Asymptotic rank of matrix-multiplication tensors

The exponent `omega` is defined in `MatrixMultiplication/Exponent.lean` as a polynomial growth
exponent of the ranks of the *square* tensors `⟨n,n,n⟩`.  This file identifies it with the
asymptotic rank of a single square tensor,

`asymptoticRank ⟨n,n,n⟩ = n ^ omega`,

and records the rectangular half of the identification, Strassen's volume lower bound

`(m·n·p) ^ (omega/3) ≤ asymptoticRank ⟨m,n,p⟩`.

## The rectangular upper bound is *not* the volume

The matching upper bound `asymptoticRank ⟨m,n,p⟩ ≤ (m·n·p)^(omega/3)` is **false**: flattening on
the `Y` leg already gives `asymptoticRank ⟨1,1,p⟩ ≥ p`, while `(1·1·p)^(omega/3) = p^(omega/3) < p`
whenever `p > 1` and `omega < 3`.  The correct general statement is the one of
[Str88, Proposition 4.3]: on the asymptotic spectrum, `⟨m,n,p⟩` has value
`m^θ₁ n^θ₂ p^θ₃` with `θ₁ + θ₂ + θ₃ ≤ omega`, and its asymptotic rank is the maximum of that
value.  Only the *symmetric* specialization `m = n = p` collapses to a power of the volume.  See
the module documentation of `Examples/AlmanLiSpeedup.lean` for the consequences.

## References

* V. Strassen, *The asymptotic spectrum of tensors*, J. reine angew. Math. 384 (1988), 102--152
  ([Strassen1988]).
-/

namespace AlgebraicComplexity

open Tensor Growth

universe u

section CommSemiring

variable {K : Type u} [CommSemiring K]

/-- Positive canonical tensor powers of a matrix-multiplication tensor are again
matrix-multiplication tensors.

The zeroth power is excluded because it is a pure tensor with one-dimensional legs, which is a
matrix-multiplication tensor only after an identification of leg spaces that this statement does
not need.

Proof sketch: induct on the exponent, splitting off one factor with
`isomorphic_external_power` and multiplying the dimensions with
`Tensor.Isomorphic.matrixMultiplication_external` of `MatrixMultiplication/TypeExtraction.lean`. -/
theorem Tensor.Isomorphic.power_matrixMultiplication (m n p k : ℕ) :
    Isomorphic (Tensor.power (matrixMultiplication (K := K) m n p) (k + 1))
      (matrixMultiplication (K := K) (m ^ (k + 1)) (n ^ (k + 1)) (p ^ (k + 1))) := by
  induction k with
  | zero =>
      exact (Tensor.Isomorphic.power_one (matrixMultiplication (K := K) m n p)).trans
        (Tensor.Isomorphic.matrixMultiplication_congr (pow_one m).symm (pow_one n).symm
          (pow_one p).symm)
  | succ k ih =>
      rw [pow_succ m (k + 1), pow_succ n (k + 1), pow_succ p (k + 1)]
      exact ((isomorphic_external_power (matrixMultiplication (K := K) m n p) (k + 1) 1).symm.trans
          (ih.external (Isomorphic.power_one (matrixMultiplication (K := K) m n p)))).trans
        (Tensor.Isomorphic.matrixMultiplication_external _ _ _ m n p)

/-- Raising a natural number to a power commutes with a real exponent:
`((v ^ j : ℕ) : ℝ) ^ t = ((v : ℝ) ^ t) ^ j`. -/
private theorem cast_pow_rpow (v : ℕ) (t : ℝ) (j : ℕ) :
    ((v ^ j : ℕ) : ℝ) ^ t = ((v : ℝ) ^ t) ^ j := by
  have h0 : (0 : ℝ) ≤ (v : ℝ) := by positivity
  rw [Nat.cast_pow, ← Real.rpow_natCast (v : ℝ) j, ← Real.rpow_mul h0,
    ← Real.rpow_natCast ((v : ℝ) ^ t) j, ← Real.rpow_mul h0]
  congr 1
  ring

/-- **The asymptotic rank of a square matrix-multiplication tensor is at most `n ^ omega`.**

Proof sketch: every exponent `τ > omega` gives a constant `C` with
`R⟨j,j,j⟩ ≤ C · j^τ` for all positive `j`; reading this at `j = n^k` and using
`Tensor.Isomorphic.power_matrixMultiplication` exhibits `(n : ℝ)^τ` as an admissible exponential
base for the ranks of the powers of `⟨n,n,n⟩`.  Letting `τ` decrease to `omega` is
`le_of_forall_gt_le` for the continuous function `τ ↦ (n : ℝ)^τ`. -/
theorem asymptoticRank_matrixMultiplication_le_rpow_omega {n : ℕ} (hn : 1 ≤ n) :
    asymptoticRank (matrixMultiplication (K := K) n n n) ≤ (n : ℝ) ^ omega K := by
  have hbase : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  refine le_of_forall_gt_le (g := fun t : ℝ ↦ (n : ℝ) ^ t)
    (Real.continuousAt_const_rpow (ne_of_gt hbase)) ?_
  intro τ hτ
  obtain ⟨hτ0, C, hC, hb⟩ := matrixExponentLE_of_omega_lt K hτ
  refine asymptoticRank_le ⟨by positivity, max C 1, by positivity, fun k ↦ ?_⟩
  cases k with
  | zero =>
      have h1 : rankPowerSequence (matrixMultiplication (K := K) n n n) 0 ≤ 1 := by
        exact rank_pure_le_one _
      calc ((rankPowerSequence (matrixMultiplication (K := K) n n n) 0 : ℕ) : ℝ)
          ≤ 1 := by exact_mod_cast h1
        _ ≤ max C 1 * ((n : ℝ) ^ τ) ^ 0 := by simp
  | succ k =>
      have hpos : 1 ≤ n ^ (k + 1) := Nat.one_le_pow _ _ hn
      have hrank : rankPowerSequence (matrixMultiplication (K := K) n n n) (k + 1) =
          squareMatrixRankSequence K (n ^ (k + 1)) := by
        exact rank_isomorphic (Tensor.Isomorphic.power_matrixMultiplication n n n k)
      calc ((rankPowerSequence (matrixMultiplication (K := K) n n n) (k + 1) : ℕ) : ℝ)
          = ((squareMatrixRankSequence K (n ^ (k + 1)) : ℕ) : ℝ) := by rw [hrank]
        _ ≤ C * ((n ^ (k + 1) : ℕ) : ℝ) ^ τ := hb _ hpos
        _ = C * ((n : ℝ) ^ τ) ^ (k + 1) := by rw [cast_pow_rpow]
        _ ≤ max C 1 * ((n : ℝ) ^ τ) ^ (k + 1) :=
            mul_le_mul_of_nonneg_right (le_max_left C 1) (by positivity)

end CommSemiring

section Field

variable {K : Type u} [Field K]

/-- **Strassen's volume lower bound for asymptotic rank**:
`(m · n · p) ^ (omega/3) ≤ asymptoticRank ⟨m,n,p⟩` for positive dimensions.

Proof sketch: the fixed-size symmetrized inequality
`matrixMultiplication_volume_rpow_omega_div_three_le_of_rankLE`, applied to an optimal rank
decomposition of the `(k+1)`st power `⟨m^{k+1}, n^{k+1}, p^{k+1}⟩`, is exactly the geometric lower
bound `((m·n·p)^{omega/3})^{k+1} ≤ R(⟨m,n,p⟩^{⊗(k+1)})`; conciseness supplies the required
`1 ≤ R`.  Only positive exponents are used, so the zeroth power is never inspected. -/
theorem rpow_omega_div_three_le_asymptoticRank_matrixMultiplication
    {m n p : ℕ} (hm : 0 < m) (hn : 0 < n) (hp : 0 < p) :
    ((m * n * p : ℕ) : ℝ) ^ (omega K / 3) ≤
      asymptoticRank (matrixMultiplication (K := K) m n p) := by
  unfold asymptoticRank
  refine Growth.le_exponentialRate_of_pow_succ_le_mul_polynomial (C := 1) (k := 0)
    ⟨rank _, rank_exponentialBound _⟩ one_pos ?_
  intro k
  have hmk : 0 < m ^ (k + 1) := pow_pos hm (k + 1)
  have hnk : 0 < n ^ (k + 1) := pow_pos hn (k + 1)
  have hpk : 0 < p ^ (k + 1) := pow_pos hp (k + 1)
  have hspec := rank_spec (matrixMultiplication (K := K)
    (m ^ (k + 1)) (n ^ (k + 1)) (p ^ (k + 1)))
  have hone : 1 ≤ rank (matrixMultiplication (K := K)
      (m ^ (k + 1)) (n ^ (k + 1)) (p ^ (k + 1))) := by
    have hlow := matrixMultiplication_rank_lower_X (K := K) hpk hspec
    exact le_trans (Nat.one_le_iff_ne_zero.mpr (by positivity)) hlow
  have hvol := matrixMultiplication_volume_rpow_omega_div_three_le_of_rankLE K
    hmk hnk hpk hone hspec
  have hrank : rankPowerSequence (matrixMultiplication (K := K) m n p) (k + 1) =
      rank (matrixMultiplication (K := K)
        (m ^ (k + 1)) (n ^ (k + 1)) (p ^ (k + 1))) :=
    rank_isomorphic (Tensor.Isomorphic.power_matrixMultiplication m n p k)
  have hvolume : (m ^ (k + 1) * n ^ (k + 1) * p ^ (k + 1) : ℕ) = (m * n * p) ^ (k + 1) := by
    rw [mul_pow, mul_pow]
  rw [hvolume, cast_pow_rpow] at hvol
  calc (((m * n * p : ℕ) : ℝ) ^ (omega K / 3)) ^ (k + 1)
      ≤ ((rank (matrixMultiplication (K := K)
          (m ^ (k + 1)) (n ^ (k + 1)) (p ^ (k + 1))) : ℕ) : ℝ) := hvol
    _ = ((rankPowerSequence (matrixMultiplication (K := K) m n p) (k + 1) : ℕ) : ℝ) := by
        rw [hrank]
    _ = 1 * ((k + 2 : ℕ) : ℝ) ^ 0 *
          ((rankPowerSequence (matrixMultiplication (K := K) m n p) (k + 1) : ℕ) : ℝ) := by
        simp

/-- **The asymptotic rank of a square matrix-multiplication tensor is exactly `n ^ omega`.**

This is the tensor-side reformulation of the definition of the exponent: `omega` is a growth
exponent of ranks of a *sequence* of tensors, while `asymptoticRank ⟨n,n,n⟩` is a growth rate of
the powers of a *single* tensor. -/
theorem asymptoticRank_matrixMultiplication_eq_rpow_omega {n : ℕ} (hn : 1 ≤ n) :
    asymptoticRank (matrixMultiplication (K := K) n n n) = (n : ℝ) ^ omega K := by
  refine le_antisymm (asymptoticRank_matrixMultiplication_le_rpow_omega hn) ?_
  have hpos : 0 < n := hn
  have h := rpow_omega_div_three_le_asymptoticRank_matrixMultiplication
    (K := K) hpos hpos hpos
  have hcube : ((n * n * n : ℕ) : ℝ) ^ (omega K / 3) = (n : ℝ) ^ omega K := by
    simpa using cubeVolume_rpow_omega_div_three K n 1 hpos
  rwa [hcube] at h

end Field

end AlgebraicComplexity
