/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.BlaeserLowerBound
import AlgebraicComplexity.MatrixMultiplication.Concise
import AlgebraicComplexity.Tensor.SliceRank
import AlgebraicComplexity.Tensor.SubstitutionMethod

/-!
# Substitution-method lower bounds for small matrix multiplication

This client records the first two rungs above the flattening lower bounds of
`MatrixMultiplication/Concise.lean` for matrix multiplication: `n*p + 1` and `n*p + 2`, hence
`rank ⟨2,2,2⟩ ≥ 5` and `≥ 6`.

Both are *specializations*, not separate arguments: they are the one-kill and two-kill cases of
the row-kill bound `matrixMultiplication_rank_lower_rowKill_Y` of
`Examples/BlaeserLowerBound.lean`, which kills all `(m-1)*n` `X`-coordinates outside a single
protected row at once.  They are kept under their own names because they are the statements that
the `⟨2,2,2⟩` corollaries and the enforcing trust audit refer to, and because their hypotheses (`2 ≤ m`,
`2 ≤ n`) are the historically quoted ones.

## Principal results

* `diagonalTwo_rank_lower`: a deliberately tiny sanity client.  The rank-two diagonal tensor
  (`Tensor.diagonalTensor K (Fin 2)`) drops to a nonzero tensor after one substitution, so every
  rank certificate has length at least two.  The fact itself is `Tensor.rank_diagonalTensor`,
  proved by an unrelated method; this client exists to catch relation-direction errors in the
  substitution API on a two-line example.
* `matrixMultiplication_rank_lower_substitution_Y`: for `2 ≤ m`, `0 < n`, `0 < p`, every rank
  certificate for `⟨m,n,p⟩` has length at least `n*p + 1` (one more than the `Y`-flattening
  bound); `..._X` and `..._Z` are the cyclic rotations of this statement.
* `matrixMultiplication_two_rank_lower` and `five_le_rank_matrixMultiplication_two`: the
  classical bound that `2 × 2` matrix multiplication has rank at least five, over every field.
  This strictly exceeds the flattening bound of four from
  `matrixMultiplication_rank_lower_max` and is the first substitution-method bound in the
  repository.
* `matrixMultiplication_rank_lower_double_substitution_Y`,
  `matrixMultiplication_two_rank_lower_six`, and `six_le_rank_matrixMultiplication_two`: a
  second substitution step in the same `X`-row raises the bound to `n*p + 2`, hence to six for
  `⟨2,2,2⟩`.  The full lower bound of seven is due to Winograd [*On multiplication of 2×2
  matrices*, Linear Algebra Appl. 4 (1971)] and Hopcroft–Kerr [*On minimizing the number of
  multiplications necessary for matrix multiplication*, SIAM J. Appl. Math. 20 (1971)]; the
  bounds proved here are the substitution steps on that road that stay uniform in the
  substitution directions, and are deliberately kept as small regression clients for the
  reusable lemma.

## Strategy

The two matrix-multiplication bounds are three-line consequences of
`matrixMultiplication_rank_lower_rowKill_Y`: that theorem gives `n*p + (m-1)*n ≤ r`, and
`1 ≤ (m-1)*n` (resp. `2 ≤ (m-1)*n`, using `2 ≤ n`) finishes by `omega`.  Its own hypotheses
(`0 < m`, `0 < p`) are weaker than the ones quoted here, so nothing is lost.  The substitution
bookkeeping that used to be repeated in this file — the detection covector, the protected row,
the surviving `Y`-conciseness — now lives once, in the chain form, in
`Examples/BlaeserLowerBound.lean`.

The one place where the single-step API is still driven directly is `diagonalTwo_rank_lower`.

## Three independent routes to `rank ⟨2,2,2⟩`

`six_le_rank_matrixMultiplication_two` is **not** an independent third proof of `rank ⟨2,2,2⟩ ≥ 6`:
it is the row-kill chain specialized.  The three methodologically distinct routes in the
repository are

1. *substitution / row-kill* — `Examples/BlaeserLowerBound.lean` (`6`, and this file's `5` and `6`
   as its one- and two-kill cases);
2. *Koszul flattening* — `MatrixMultiplication/KoszulBorderRank.lean` (`6`, as a *border*-rank
   bound);
3. *trilinear substitution with sandwich normalization* — `Examples/WinogradLowerBound.lean`
   (the exact value `7`).

## Non-goals

Nothing here handles substitutions whose effect on the surviving contractions depends on the
substitution direction; that is exactly what the exact value `7` for `⟨2,2,2⟩` needs (an
invertible matrix in every trace-hyperplane), and it is carried out in
`Examples/WinogradLowerBound.lean`.
-/

namespace AlgebraicComplexity

open Tensor

universe u

variable {K : Type u} [Field K]

/-! ### A tiny sanity client: the diagonal tensor of size two -/

/-- The diagonal (unit) tensor of size two: `e₀ ⊗ e₀ ⊗ e₀ + e₁ ⊗ e₁ ⊗ e₁` with all three leg
spaces equal to `K²`.  An abbreviation for `Tensor.diagonalTensor K (Fin 2)`, which it is
syntactically equal to; the name survives only because the sanity client below reads better
with it. -/
noncomputable abbrev diagonalTwo : Tensor3 K (fun _ ↦ Fin 2 → K) :=
  Tensor.diagonalTensor K (Fin 2)

/-- Contracting the diagonal tensor against the coordinate covectors at `a₀` on `Y` and `Z`
isolates the `X`-basis vector at `a₀`. -/
private theorem contractX_diagonalTwo (a₀ : Fin 2) :
    contractX (LinearMap.proj (R := K) a₀) (LinearMap.proj (R := K) a₀)
        (diagonalTwo (K := K)) = Pi.single a₀ 1 := by
  unfold diagonalTwo Tensor.diagonalTensor
  rw [map_sum]
  fin_cases a₀ <;>
    simp [Pi.single_apply]

/-- Sanity check for the substitution step: every rank certificate for the diagonal tensor of
size two has length at least two.

This establishes nothing new: `Tensor.rank_diagonalTensor` proves the same bound exactly, by the
slice-rank route.  The client exists to exercise `RankLE.exists_substituteX` on a two-line
example, so that a relation-direction error in the substitution API fails here rather than inside
a matrix-multiplication proof.

Proof sketch: the coordinate covector at `1` detects the tensor, so one substitution yields a
certificate of length `r - 1` for the substituted tensor; the latter is nonzero because its
`X`-retaining contraction at coordinate `0` is the unchanged basis vector `e₀`, so `r ≥ 2`. -/
theorem diagonalTwo_rank_lower {r : ℕ} (h : RankLE r (diagonalTwo (K := K))) : 2 ≤ r := by
  classical
  have hslice : (LinearMap.proj (R := K) (1 : Fin 2))
      (contractX (LinearMap.proj (R := K) (1 : Fin 2)) (LinearMap.proj (R := K) (1 : Fin 2))
        (diagonalTwo (K := K))) ≠ 0 := by
    rw [contractX_diagonalTwo]
    simp
  obtain ⟨v, hv, hrank⟩ := h.exists_substituteX (LinearMap.proj (R := K) (1 : Fin 2)) hslice
  have hcontr : contractX (LinearMap.proj (R := K) (0 : Fin 2))
      (LinearMap.proj (R := K) (0 : Fin 2))
      (substituteX (LinearMap.proj (R := K) (1 : Fin 2)) v (diagonalTwo (K := K))) =
      Pi.single (0 : Fin 2) 1 := by
    rw [contractX_substituteX, contractX_diagonalTwo, substProjX_apply]
    simp
  have hne : substituteX (LinearMap.proj (R := K) (1 : Fin 2)) v (diagonalTwo (K := K)) ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hcontr
    have h1 : (0 : K) = 1 := by simpa using congrFun hcontr (0 : Fin 2)
    exact zero_ne_one h1
  have h1 : 1 ≤ r - 1 := by
    rcases Nat.eq_zero_or_pos (r - 1) with h0 | h0
    · rw [h0] at hrank
      exact absurd hrank.eq_zero hne
    · exact h0
  omega

/-! ### Substitution-method lower bounds for matrix multiplication -/

/-- Substitution-method lower bound, `Y`-flattening form: for `m ≥ 2` and positive `n, p`,
every rank certificate for `⟨m,n,p⟩` has length at least `n*p + 1`, one more than the
`Y`-flattening bound.

This is the one-kill case of the row-kill bound
`matrixMultiplication_rank_lower_rowKill_Y` of `Examples/BlaeserLowerBound.lean`, which kills
all `(m-1)*n` `X`-coordinates outside one row at once. -/
theorem matrixMultiplication_rank_lower_substitution_Y
    {m n p r : ℕ} (hm : 2 ≤ m) (hn : 0 < n) (hp : 0 < p)
    (h : RankLE r (matrixMultiplication (K := K) m n p)) :
    n * p + 1 ≤ r := by
  have hkey := matrixMultiplication_rank_lower_rowKill_Y (K := K) (by omega : 0 < m) hp h
  have h1 : 1 ≤ (m - 1) * n := Nat.one_le_iff_ne_zero.mpr
    (Nat.mul_ne_zero (by omega) (by omega))
  omega

/-- Substitution-method lower bound, `X`-flattening form: for `p ≥ 2` and positive `m, n`,
every rank certificate for `⟨m,n,p⟩` has length at least `m*n + 1`.  Obtained from the
`Y`-flattening form by one cyclic rotation of the three roles. -/
theorem matrixMultiplication_rank_lower_substitution_X
    {m n p r : ℕ} (hp : 2 ≤ p) (hm : 0 < m) (hn : 0 < n)
    (h : RankLE r (matrixMultiplication (K := K) m n p)) :
    m * n + 1 ≤ r :=
  matrixMultiplication_rank_lower_substitution_Y hp hm hn h.matrixMultiplication_cycle

/-- Substitution-method lower bound, `Z`-flattening form: for `n ≥ 2` and positive `p, m`,
every rank certificate for `⟨m,n,p⟩` has length at least `p*m + 1`.  Obtained from the
`Y`-flattening form by two cyclic rotations of the three roles. -/
theorem matrixMultiplication_rank_lower_substitution_Z
    {m n p r : ℕ} (hn : 2 ≤ n) (hp : 0 < p) (hm : 0 < m)
    (h : RankLE r (matrixMultiplication (K := K) m n p)) :
    p * m + 1 ≤ r :=
  matrixMultiplication_rank_lower_substitution_Y hn hp hm
    h.matrixMultiplication_cycle.matrixMultiplication_cycle

/-- The rank of `2 × 2` matrix multiplication is at least five, over every field: every rank
certificate for `⟨2,2,2⟩` has length at least `5`.  This is one substitution step beyond the
flattening bound of four provided by `matrixMultiplication_rank_lower_max`. -/
theorem matrixMultiplication_two_rank_lower {r : ℕ}
    (h : RankLE r (matrixMultiplication (K := K) 2 2 2)) : 5 ≤ r := by
  have h5 := matrixMultiplication_rank_lower_substitution_Y
    (by norm_num) (by norm_num) (by norm_num) h
  omega

/-- The rank of the `2 × 2` matrix-multiplication tensor is at least five, over every field. -/
theorem five_le_rank_matrixMultiplication_two :
    5 ≤ rank (matrixMultiplication (K := K) 2 2 2) :=
  matrixMultiplication_two_rank_lower (rank_spec _)

/-! ### Two substitution steps -/

/-- Double-substitution lower bound: for `m ≥ 2`, `n ≥ 2` and positive `p`, every rank
certificate for `⟨m,n,p⟩` has length at least `n*p + 2`, two more than the `Y`-flattening
bound.

This is the two-kill case of `matrixMultiplication_rank_lower_rowKill_Y`
(`Examples/BlaeserLowerBound.lean`), which kills the whole complement of one `X`-row. -/
theorem matrixMultiplication_rank_lower_double_substitution_Y
    {m n p r : ℕ} (hm : 2 ≤ m) (hn : 2 ≤ n) (hp : 0 < p)
    (h : RankLE r (matrixMultiplication (K := K) m n p)) :
    n * p + 2 ≤ r := by
  have hkey := matrixMultiplication_rank_lower_rowKill_Y (K := K) (by omega : 0 < m) hp h
  have h1 : 2 ≤ (m - 1) * n := le_trans hn (Nat.le_mul_of_pos_left n (by omega))
  omega

/-- Two substitution steps for `2 × 2` matrix multiplication: every rank certificate for
`⟨2,2,2⟩` has length at least `6`, over every field. -/
theorem matrixMultiplication_two_rank_lower_six {r : ℕ}
    (h : RankLE r (matrixMultiplication (K := K) 2 2 2)) : 6 ≤ r := by
  have h6 := matrixMultiplication_rank_lower_double_substitution_Y
    (by norm_num) (by norm_num) (by norm_num) h
  omega

/-- The rank of the `2 × 2` matrix-multiplication tensor is at least six, over every field.
The exact value is seven (Winograd 1971, Hopcroft–Kerr 1971), proved in
`Examples/WinogradLowerBound.lean`; this simpler bound survives as a regression client for the
uniform-substitution fragment of the API. -/
theorem six_le_rank_matrixMultiplication_two :
    6 ≤ rank (matrixMultiplication (K := K) 2 2 2) :=
  matrixMultiplication_two_rank_lower_six (rank_spec _)

end AlgebraicComplexity
