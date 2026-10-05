/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoCounting
import AlgebraicComplexity.Probability.MaximumEntropyDual

/-!
# The Duan--Wu--Zhou level-two triple-entropy bound, from the committed Gibbs dual

`Examples/DuanWuZhouLevelTwoCounting.lean` states `Dwz63TripleEntropyBound` and calls it "the only
genuinely new mathematics the count side of section 6.3 needs": every fifteen-cell type sharing
`alpha`'s three coordinate marginals has entropy at most `H(alpha) + log K`, with
`K = 1 + 10 ^ (-10)`.  In `[DuanWuZhou2022]` this is estimate (d'), the statement that
`max_{alpha' in D_alpha} 2 ^ H(alpha')` exceeds `2 ^ H(alpha)` by at most the declared hash loss.

This module is the first half of discharging it, and records the finding that it does **not** need
new mathematics: it is the composition of three things the repository already contains.  What is
proved here is the reading of the Gibbs witness; the entropy comparison itself is the second half
and is not in this file.  Nothing here may be cited as a proof of `Dwz63TripleEntropyBound`.

## The three committed ingredients

* **Weak duality**, `Probability/MaximumEntropyDual.lean`.  `entropy_le_logPartition_sub_expectation`
  is Gibbs' inequality in the form `H(p) <= log Z(s) - E_p[s]` for an arbitrary score `s`, and
  `coordinateScore_expectation` says that when `s` is a sum of three coordinate potentials the
  expectation `E_p[s]` depends on `p` **only through its three marginals**.  That pair is exactly
  the transportation-polytope duality section 6.3 needs, and it is generic: no alphabet, no
  tensor, no section 6.3 datum occurs there.
* **The witness**, `dwz63_partitionSum_eq` (`DuanWuZhouLevelTwoGlobalArithmetic.lean`).  The
  inverse-iterative-proportional-fitting fixed point, rounded to denominator `10 ^ 6`.  Its
  partition sum is recorded there as an exact rational.
* **The numeric certificate**, `dwz63_gibbsDeficit_le_log_hashLossMultiplier` (same file), already
  proved from the sixteen committed directed enclosures.

## What this module proves

`dwz63GibbsX`, `dwz63GibbsY`, `dwz63GibbsZ` are the three potential vectors read off the committed
partition-sum witness, and

* `dwz63_partition_dwz63GibbsScore` --- the partition function of the coordinate score at these
  potentials is the committed `dwz63_partitionSum_eq` value.

That identity is what pins the reading down: `dwz63GibbsZ` runs in the **opposite** order to the
factors of `dwz63_partitionSum_eq`, because `dwz63ZIndex` is the descending coordinate
`k = 4 - i - j`, and getting it backwards would fail here rather than silently later.  Also proved
are `marginal_div_profileMass`, which is how the fixed marginals of the hypothesis enter the dual,
and the generic `profileEntropyNats_nonneg`.

## What remains, and where it goes

The second half is the entropy comparison: that the dual gap `log W - E_alpha[s] - H(alpha)` is the
committed constant `dwz63GibbsDeficit`, whence `Dwz63TripleEntropyBound` via
`dwz63_gibbsDeficit_le_log_hashLossMultiplier`.  That gap identity has been verified exactly in
rational arithmetic outside Lean --- all fifteen cell terms of `dwz63GibbsDeficit` match
`(alpha(c) / 10 ^ 8) * log ((alpha(c) / 10 ^ 8) / (u_i v_j w_k))` uniquely, with the sixteenth term
exactly `log W` and no term left over on either side --- but it is not formalized here.

## Position in the library

Layer 4 (a client).  It imports the section 6.3 counting data and the generic maximum-entropy
dual, and assumes nothing: `dwz63_tripleEntropyBound` is unconditional.

Primary source: Ran Duan, Hongxun Wu and Renfei Zhou, *Faster Matrix Multiplication via
Asymmetric Hashing*, arXiv:2210.10173, section 6.2 and `hashing.tex` `lem:numtriple_singledist`.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity WordType

noncomputable section

/-! ## Entropy of an integral profile is nonnegative

A small generic fact that `Probability/IntegralProfileCore.lean` does not record.  It is stated
here rather than there because that file belongs to another lane's cone; it is a candidate for
promotion once the tranches merge. -/

/-- Each normalized coordinate of an integral profile is at most one. -/
theorem profile_div_profileMass_le_one {I : Type*} [Fintype I] (a : I → ℕ) (i : I) :
    (a i : ℝ) / (profileMass a : ℝ) ≤ 1 := by
  rcases Nat.eq_zero_or_pos (profileMass a) with hzero | hpos
  · simp [hzero]
  · rw [div_le_one (by exact_mod_cast hpos)]
    have : a i ≤ profileMass a := Finset.single_le_sum (f := a) (fun _ _ ↦ Nat.zero_le _)
      (Finset.mem_univ i)
    exact_mod_cast this

/-- Shannon entropy of an integral profile is nonnegative. -/
theorem profileEntropyNats_nonneg {I : Type*} [Fintype I] (a : I → ℕ) :
    0 ≤ profileEntropyNats a := by
  unfold profileEntropyNats
  exact Finset.sum_nonneg fun i _ ↦
    Real.negMulLog_nonneg (by positivity) (profile_div_profileMass_le_one a i)

/-! ## The three Gibbs potentials of section 6.3

Read off the committed `dwz63_partitionSum_eq` witness.  `dwz63GibbsZ` is indexed by the `Z`
coordinate itself, so it runs opposite to the order the factors appear there. -/

/-- The `X` potential of the section 6.3 Gibbs witness.

Defined by pattern matching rather than as a `![...]` literal: the equation lemmas that a match
generates rewrite at *numeral* indices, whereas `Matrix.cons_val_*` only reaches indices `0` and
`1` in this Mathlib (there is no `cons_val_two`/`three`/`four`), which leaves a fifteen-term
partition sum half-evaluated. -/
def dwz63GibbsX : Fin 5 → ℝ
  | 0 => 20881 / 500000
  | 1 => 101843 / 1000000
  | 2 => 128169 / 1000000
  | 3 => 20099 / 1000000
  | 4 => 121 / 125000

/-- The `Y` potential of the section 6.3 Gibbs witness. -/
def dwz63GibbsY : Fin 5 → ℝ
  | 0 => 542361 / 1000000
  | 1 => 165329 / 125000
  | 2 => 104033 / 62500
  | 3 => 8157 / 31250
  | 4 => 393 / 31250

/-- The `Z` potential of the section 6.3 Gibbs witness, indexed by the `Z` coordinate. -/
def dwz63GibbsZ : Fin 5 → ℝ
  | 0 => 470879 / 1000000
  | 1 => 1223123 / 1000000
  | 2 => 1491349 / 1000000
  | 3 => 21927 / 100000
  | 4 => 921 / 100000

theorem dwz63GibbsX_pos (x : Fin 5) : 0 < dwz63GibbsX x := by
  fin_cases x <;> norm_num [dwz63GibbsX]

theorem dwz63GibbsY_pos (y : Fin 5) : 0 < dwz63GibbsY y := by
  fin_cases y <;> norm_num [dwz63GibbsY]

theorem dwz63GibbsZ_pos (z : Fin 5) : 0 < dwz63GibbsZ z := by
  fin_cases z <;> norm_num [dwz63GibbsZ]

/-- The section 6.3 coordinate score: the logarithm of the product weight `u_i v_j w_k`. -/
def dwz63GibbsScore : Fin 15 → ℝ :=
  MaximumEntropyDual.coordinateScore dwz63XIndex dwz63YIndex dwz63ZIndex
    (fun x ↦ Real.log (dwz63GibbsX x)) (fun y ↦ Real.log (dwz63GibbsY y))
    (fun z ↦ Real.log (dwz63GibbsZ z))

/-- Exponentiating the score recovers the product weight. -/
theorem exp_dwz63GibbsScore (c : Fin 15) :
    Real.exp (dwz63GibbsScore c) =
      dwz63GibbsX (dwz63XIndex c) * dwz63GibbsY (dwz63YIndex c) *
        dwz63GibbsZ (dwz63ZIndex c) := by
  unfold dwz63GibbsScore MaximumEntropyDual.coordinateScore
  rw [Real.exp_add, Real.exp_add, Real.exp_log (dwz63GibbsX_pos _),
    Real.exp_log (dwz63GibbsY_pos _), Real.exp_log (dwz63GibbsZ_pos _)]

/-- **The partition function is the committed partition sum.**  This reproduces
`dwz63_partitionSum_eq` from the potential vectors, and is the point at which the reading of the
committed witness is pinned down. -/
theorem dwz63_partition_dwz63GibbsScore :
    MaximumEntropyDual.partition dwz63GibbsScore =
      249999816060193851 / 250000000000000000 := by
  rw [MaximumEntropyDual.partition]
  simp only [exp_dwz63GibbsScore, dwz63XIndex, dwz63YIndex, dwz63ZIndex,
    dwz63GibbsX, dwz63GibbsY, dwz63GibbsZ, Fin.sum_univ_succ, Fin.sum_univ_zero,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_succ, Matrix.head_fin_const]
  norm_num

/-! ## Marginals of a normalized integral profile -/

/-- The marginal of a normalized integral profile is the normalized pushforward profile. -/
theorem marginal_div_profileMass {I B : Type*} [Fintype I] [Fintype B] [DecidableEq B]
    (coord : I → B) (a : I → ℕ) (mass : ℝ) (b : B) :
    MaximumEntropyDual.marginal coord (fun i ↦ (a i : ℝ) / mass) b =
      (mappedType coord a b : ℝ) / mass := by
  rw [MaximumEntropyDual.marginal, mappedType_eq_sum_ite]
  push_cast
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  split <;> simp

end

end AlgebraicComplexity.Examples
