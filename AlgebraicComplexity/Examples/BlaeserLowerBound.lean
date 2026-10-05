/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.Concise
import AlgebraicComplexity.Tensor.SubstitutionMethodScale

/-!
# Substitution-method rank lower bounds for general `n`: the `2n² - n` rung

This client proves, over an arbitrary field and for all dimensions, the *row-kill* bound

  `rank ⟨m,n,p⟩ ≥ n*p + (m-1)*n`,

together with its two cyclic rotations, and specializes it to the square case

  `rank ⟨n,n,n⟩ ≥ 2n² - n`.

This is the first bound in the repository whose leading coefficient exceeds the flattening bound
for all `n`: flattening gives `n²` and the previously formalized substitution bounds gave `n² + 1`
and `n² + 2` (`Examples/SmallMatrixLowerBounds.lean`).

## Route

The whole argument is a single application of the multi-step substitution machinery of
`Tensor/SubstitutionMethodScale.lean`.  Fix the row index `i₁ = 0` of the `X` leg.  The killed
family is the set of *all* `X`-coordinates outside that row, i.e. the `(m-1)*n` positions `(i,j)`
with `i ≠ i₁`.

* *Detection.*  The coordinate covector at `(i,j)` is detected in `⟨m,n,p⟩` by the product
  contraction at `Y`-index `(j,k₀)` and `Z`-index `(k₀,i)`, whose value is exactly the standard
  `X`-basis vector at `(i,j)` (`contractX_matrixMultiplication_basis`).  That value is normalized
  against the entire killed family: every other coordinate covector of the family annihilates it.
  This is
  precisely the uniform detection certificate required by
  `Tensor.RankLE.exists_substituteXChain`, so all `(m-1)*n` substitutions can be performed, each
  removing one term of the certificate, whatever directions the decomposition forces.
* *Survival.*  Every covector of the family annihilates the standard basis vectors of the
  protected row `i₁`, so by the protection lemma
  `Tensor.substProjXChain_apply_of_forall_ker` the composite substitution map fixes them,
  uniformly in the adversarial substitution directions.  Contracting the substituted tensor
  against the `X`-covector at `(i₁,b)` and the `Z`-covector at `(c,i₁)` therefore still isolates
  the `Y`-basis vector at `(b,c)` (`contractY_matrixMultiplication_row`): the surviving tensor is
  still concise in `Y`, so its remaining certificate has length at least `n*p`.

Adding the two counts gives `n*p + (m-1)*n`.

## What is *not* proved here, and why

The intended target of this file is Bläser's bound `rank ⟨n,n,n⟩ ≥ (5/2)n² - 3n` [Markus Bläser,
*A 5/2 n²-lower bound for the rank of n×n-matrix multiplication over arbitrary fields*,
Proc. 40th Annual Symposium on Foundations of Computer Science (FOCS), 1999], whose classical
predecessor is the Alder–Strassen bound `rank A ≥ 2 dim A - t(A)` for a finite-dimensional
associative algebra `A` with `t(A)` maximal two-sided ideals [A. Alder and V. Strassen, *On the
algorithmic complexity of associative algebras*, Theoretical Computer Science 15 (1981)]; applied
to the simple algebra `K^{n×n}` it gives `rank ⟨n,n,n⟩ ≥ 2n² - 1`.  Only the `2n² - n` rung is
proved here.  The module deliberately stops where the method has to change, and the reason is
worth recording (the following accounting is an informal explanation of the design decision, not
a formalized theorem):

*The uniform-substitution fragment appears to stop at `2n² - n`.*  Every bound obtainable by
killing coordinate variables and finishing with a flattening of an untouched leg has the shape
(number of kills) + (dimension of a leg that survives).  For `⟨n,n,n⟩` the surviving data must
contain, for each of the `n²` target `Y`-coordinates `(b,c)`, an `X`-covector on the protected row
`i₁` and a `Z`-covector in the protected column `i₁`; killing one of those gains one term but
costs `n` from the flattening, and protecting `ρ` rows rather than one trades `ρ - 1` blocks of
`n` `X`-kills for `ρ - 1` blocks of `p` `Z`-kills — in the square case an even exchange, and in
the rectangular case exactly the interpolation between the `Y`-form and the `Z`-form of the bound
below.  The count is also tight for the *residual*: when the substitution directions happen to
vanish, the surviving tensor is exactly `⟨1,n,n⟩`, of rank `n²`, so no better terminal bound is
available.  Passing to `2n² - 1` needs the genuinely different Alder–Strassen argument (restrict
the algorithm to the subspace of `B`-variables annihilated by the `v`-forms outside a basis of the
`u`-forms, and exploit the two-sided ideal structure of `K^{n×n}`), and Bläser's `5/2 n² - 3n`
needs in addition the sandwich normalization `(A,B,C) ↦ (P'A, BR', RCP)` at scale, i.e. a rank
normal form for the detecting covector — the `2 × 2` instance of that normalization is
`Winograd.exists_sandwich_normalizer` in `Examples/WinogradLowerBound.lean`.  Neither is
formalized in this repository yet; the adaptive interface `Tensor.RankLE.exists_killChainX` of
`Tensor/SubstitutionMethodScale.lean`, whose invariant may depend on all previously chosen
substitution directions, is the intended substrate for them.

## Three independent routes to `rank ⟨2,2,2⟩`

The repository proves three lower bounds on `rank ⟨2,2,2⟩`, and exactly three of them are
methodologically independent:

1. *substitution / row-kill* (this file): `rank_matrixMultiplication_rowKill` gives `6`, and the
   `Examples/SmallMatrixLowerBounds.lean` bounds `5` and `6` are its one- and two-kill
   specializations, not separate arguments;
2. *Koszul flattening* (`MatrixMultiplication/KoszulBorderRank.lean`): `6` again, but as a
   *border*-rank bound, from the rank of an explicit `12 × 8` matrix;
3. *trilinear substitution with sandwich normalization* (`Examples/WinogradLowerBound.lean`): the
   exact value `7`, the only route that reaches it.

## Non-goals

No border-rank statement is made: substitution is applied to exact rank certificates only.  The
`2 × 2` case is not improved here — the exact value `rank ⟨2,2,2⟩ = 7` is proved in
`Examples/WinogradLowerBound.lean`, and the bound of this file gives `6` there.
-/

namespace AlgebraicComplexity

open Tensor

universe u

variable {K : Type u} [Field K]

/-! ### The row-kill bound -/

/-- **Row-kill substitution bound, `Y`-flattening form.**  For positive dimensions, the rank of
the rectangular matrix-multiplication tensor satisfies

  `rank ⟨m,n,p⟩ ≥ (m-1)*n + n*p`.

Proof sketch: substitute away all `(m-1)*n` `X`-variables outside the first row.  Each of them is
detected in the source tensor by an explicit product contraction whose value is the corresponding
standard basis vector, and those values are normalized against the whole killed family, so
`Tensor.RankLE.exists_substituteXChain` performs the whole chain and removes `(m-1)*n` terms.  The
substitution projections fix every basis vector of the protected first row, so the substituted
tensor is still concise in `Y` (`contractY_matrixMultiplication_row`) and its remaining
certificate has length at least `n*p`. -/
theorem rank_matrixMultiplication_rowKill
    {m n p : ℕ} (hm : 0 < m) (hp : 0 < p) :
    (m - 1) * n + n * p ≤ rank (matrixMultiplication (K := K) m n p) := by
  classical
  set i₁ : Fin m := ⟨0, hm⟩ with hi₁
  set k₀ : Fin p := ⟨0, hp⟩ with hk₀
  set qs : List (Fin m × Fin n) :=
    (((Finset.univ.erase i₁) ×ˢ (Finset.univ : Finset (Fin n))).toList) with hqs
  have hmem : ∀ q : Fin m × Fin n, q ∈ qs ↔ q.1 ≠ i₁ := by
    intro q
    rw [hqs, Finset.mem_toList, Finset.mem_product, Finset.mem_erase]
    simp
  have hnd : qs.Nodup := Finset.nodup_toList _
  have hlen : qs.length = (m - 1) * n := by
    rw [hqs, Finset.length_toList, Finset.card_product,
      Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Finset.card_univ,
      Fintype.card_fin, Fintype.card_fin]
  have hkey :=
    rank_lower_of_substituteXChain
      (K := K) (V := MMSpace K m n p) (ι := Fin m × Fin n)
      (fun q ↦ LinearMap.proj (R := K) q)
      (T := matrixMultiplication (K := K) m n p) (s := n * p) hnd ?_ ?_
  · rw [hlen] at hkey
    exact hkey
  · -- detection: each killed coordinate is isolated by an explicit product contraction
    rintro ⟨i, j⟩ hq
    refine ⟨LinearMap.proj (R := K) (j, k₀), LinearMap.proj (R := K) (k₀, i), fun q' _ ↦ ?_⟩
    rw [contractX_matrixMultiplication_basis]
    simp [Pi.single_apply]
  · -- survival: the protected first row is untouched, so `Y`-conciseness persists
    intro L hmap hnorm
    have hker : ∀ (j : Fin n) (qv : (Fin m × Fin n) × MMSpace K m n p .X), qv ∈ L →
        (LinearMap.proj (R := K) qv.1) ((Pi.single (i₁, j) 1 : MMSpace K m n p .X)) = 0 := by
      intro j qv hqv
      have hq1 : qv.1 ∈ qs := by
        rw [← hmap]
        exact List.mem_map_of_mem hqv
      have hne : qv.1 ≠ (i₁, j) := by
        intro h
        exact ((hmem qv.1).mp hq1) (by rw [h])
      simp [hne]
    have hconc : IsConciseY (substituteXChain (fun q ↦ LinearMap.proj (R := K) q) L
        (matrixMultiplication (K := K) m n p)) := by
      apply le_antisymm le_top
      rw [← (Pi.basisFun K (Fin n × Fin p)).span_eq]
      apply Submodule.span_mono
      rintro _ ⟨⟨b, c⟩, rfl⟩
      rw [Pi.basisFun_apply]
      refine ⟨(LinearMap.proj (R := K) (i₁, b), LinearMap.proj (R := K) (c, i₁)), ?_⟩
      show contractY (LinearMap.proj (R := K) (i₁, b)) (LinearMap.proj (R := K) (c, i₁))
          (substituteXChain (fun q ↦ LinearMap.proj (R := K) q) L
            (matrixMultiplication (K := K) m n p)) = _
      rw [contractY_substituteXChain]
      refine contractY_matrixMultiplication_row c (fun j ↦ ?_)
      rw [comp_substProjXChain_apply _ _ (hker j)]
      by_cases hj : j = b
      · subst hj
        simp
      · simp [Ne.symm hj, hj]
    have hdim := (rank_spec _).finrank_Y_le hconc
    simpa [MMSpace, MMIndex, Module.finrank_fintype_fun_eq_card] using hdim

/-- Certificate form of the row-kill bound: every rank certificate for `⟨m,n,p⟩` has length at
least `n*p + (m-1)*n`. -/
theorem matrixMultiplication_rank_lower_rowKill_Y
    {m n p r : ℕ} (hm : 0 < m) (hp : 0 < p)
    (h : RankLE r (matrixMultiplication (K := K) m n p)) :
    n * p + (m - 1) * n ≤ r := by
  have hkey := rank_matrixMultiplication_rowKill (K := K) (n := n) hm hp
  have hle : rank (matrixMultiplication (K := K) m n p) ≤ r := rank_le_iff.mpr h
  omega

/-- Row-kill bound, `X`-flattening form: every rank certificate for `⟨m,n,p⟩` has length at least
`m*n + (p-1)*m`.  Obtained from the `Y`-form by one cyclic rotation of the three roles. -/
theorem matrixMultiplication_rank_lower_rowKill_X
    {m n p r : ℕ} (hn : 0 < n) (hp : 0 < p)
    (h : RankLE r (matrixMultiplication (K := K) m n p)) :
    m * n + (p - 1) * m ≤ r :=
  matrixMultiplication_rank_lower_rowKill_Y hp hn h.matrixMultiplication_cycle

/-- Row-kill bound, `Z`-flattening form: every rank certificate for `⟨m,n,p⟩` has length at least
`p*m + (n-1)*p`.  Obtained from the `Y`-form by two cyclic rotations of the three roles. -/
theorem matrixMultiplication_rank_lower_rowKill_Z
    {m n p r : ℕ} (hm : 0 < m) (hn : 0 < n)
    (h : RankLE r (matrixMultiplication (K := K) m n p)) :
    p * m + (n - 1) * p ≤ r :=
  matrixMultiplication_rank_lower_rowKill_Y hn hm
    h.matrixMultiplication_cycle.matrixMultiplication_cycle

/-- All three rotations at once: every rank certificate for a positive rectangular
matrix-multiplication tensor has length at least the largest of the three row-kill bounds.  This
is the row-kill analogue of `matrixMultiplication_rank_lower_max`, which packages the three
flattening bounds. -/
theorem matrixMultiplication_rank_lower_rowKill_max
    {m n p r : ℕ} (hm : 0 < m) (hn : 0 < n) (hp : 0 < p)
    (h : RankLE r (matrixMultiplication (K := K) m n p)) :
    max (n * p + (m - 1) * n) (max (m * n + (p - 1) * m) (p * m + (n - 1) * p)) ≤ r :=
  max_le (matrixMultiplication_rank_lower_rowKill_Y hm hp h)
    (max_le (matrixMultiplication_rank_lower_rowKill_X hn hp h)
      (matrixMultiplication_rank_lower_rowKill_Z hm hn h))

/-! ### The square case -/

/-- **`rank ⟨n,n,n⟩ ≥ 2n² - n` over every field.**  Certificate form: every rank certificate for
the `n × n` matrix-multiplication tensor has length at least `2n² - n`.

This is the square specialization of `matrixMultiplication_rank_lower_rowKill_Y`: `n²` from the
`Y`-flattening of the surviving tensor plus `n² - n` substituted `X`-variables. -/
theorem matrixMultiplication_square_rank_lower
    {n r : ℕ} (hn : 0 < n)
    (h : RankLE r (matrixMultiplication (K := K) n n n)) :
    2 * n ^ 2 - n ≤ r := by
  have key : n * n + (n - 1) * n ≤ r :=
    matrixMultiplication_rank_lower_rowKill_Y hn hn h
  have h1 : (n - 1) * n = n * n - n := Nat.sub_one_mul n n
  have h2 : n ≤ n * n := Nat.le_mul_of_pos_left n hn
  have h3 : 2 * n ^ 2 = n * n + n * n := by ring
  rw [h1] at key
  rw [h3]
  generalize n * n = N at key h2 ⊢
  omega

/-- **`rank ⟨n,n,n⟩ ≥ 2n² - n` over every field**, in terms of the tensor rank itself. -/
theorem two_sq_sub_le_rank_matrixMultiplication_square {n : ℕ} (hn : 0 < n) :
    2 * n ^ 2 - n ≤ rank (matrixMultiplication (K := K) n n n) :=
  matrixMultiplication_square_rank_lower hn (rank_spec _)

/-! ### Tiny regression clients

Two small instances, checked against results already in the tree: for `⟨2,2,2⟩` the bound
reproduces the value `6` of `Examples/SmallMatrixLowerBounds.lean` (the exact value `7` needs the
adaptive argument of `Examples/WinogradLowerBound.lean`), and for `⟨3,3,3⟩` it gives `15`. -/

example : 6 ≤ rank (matrixMultiplication (K := K) 2 2 2) := by
  simpa using two_sq_sub_le_rank_matrixMultiplication_square (K := K) (n := 2) (by norm_num)

example : 15 ≤ rank (matrixMultiplication (K := K) 3 3 3) := by
  simpa using two_sq_sub_le_rank_matrixMultiplication_square (K := K) (n := 3) (by norm_num)

/-- The bound is exact for matrix-vector products: for `p = 1` it returns `m*n`, which is the
rank of `⟨m,n,1⟩`.  This pins down the normalization of the statement. -/
example {m n : ℕ} (hm : 0 < m) :
    m * n ≤ rank (matrixMultiplication (K := K) m n 1) := by
  have := rank_matrixMultiplication_rowKill (K := K) (n := n) hm (by norm_num : 0 < 1)
  have h1 : (m - 1) * n = m * n - n := Nat.sub_one_mul m n
  have h2 : n ≤ m * n := Nat.le_mul_of_pos_left n hm
  rw [h1, mul_one] at this
  omega

end AlgebraicComplexity
