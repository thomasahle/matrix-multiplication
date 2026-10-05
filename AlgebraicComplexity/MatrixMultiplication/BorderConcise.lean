/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.BorderRank
import AlgebraicComplexity.MatrixMultiplication.Concise
import AlgebraicComplexity.Tensor.BorderConcise

/-!
# Border-rank lower bounds for matrix-multiplication tensors

This leaf module combines the conciseness certificates of
`AlgebraicComplexity/MatrixMultiplication/Concise.lean` with the border-rank conciseness bounds
of `AlgebraicComplexity/Tensor/BorderConcise.lean`: every constructive border-rank certificate
for a positive rectangular matrix-multiplication tensor has size at least each product of two of
the dimensions, and hence at least the largest such product.  This instantiates Theorem 3.4 of
He and Williams's CS 6810 notes (a roadmap, not the normative source; see `DESIGN.md`) for the
tensors `⟨m,n,p⟩`, strengthening the exact-rank bounds of
`matrixMultiplication_rank_lower_max` to border rank.

The bounds are stated both against explicit `BorderRankLE` certificates and against the numeric
`borderRank`.  As with the exact-rank module, the file lives in the matrix-multiplication layer
because it mentions a named tensor; the reusable mathematics stays in the tensor layer.

Only the `X`-leg bound is proved directly from conciseness: the `Y` and `Z` bounds follow from it
by the cyclic symmetry `⟨m,n,p⟩ ↦ ⟨p,m,n⟩` of matrix multiplication
(`Tensor.BorderRankLE.matrixMultiplication_cycle`), which rotates both the certificate and the
positivity hypothesis.
-/

namespace AlgebraicComplexity

open Tensor

universe u

variable {K : Type u} [Field K]

/-- Flattening on the `X` leg: a border-rank certificate for `⟨m,n,p⟩` with `p` positive has
size at least `m * n`. -/
theorem matrixMultiplication_borderRank_lower_X
    {m n p r : ℕ} (hp : 0 < p)
    (h : BorderRankLE r (matrixMultiplication (K := K) m n p)) :
    m * n ≤ r := by
  have hdim := h.finrank_X_le (matrixMultiplication_isConciseX (K := K) hp)
  simpa [MMSpace, MMIndex, Module.finrank_fintype_fun_eq_card] using hdim

/-- Flattening on the `Y` leg: a border-rank certificate for `⟨m,n,p⟩` with `m` positive has
size at least `n * p`.

Proof: rotating the certificate twice turns `⟨m,n,p⟩` into `⟨n,p,m⟩`, whose `X`-leg bound is
exactly `n * p ≤ r` and whose contracted dimension is the original `m`. -/
theorem matrixMultiplication_borderRank_lower_Y
    {m n p r : ℕ} (hm : 0 < m)
    (h : BorderRankLE r (matrixMultiplication (K := K) m n p)) :
    n * p ≤ r :=
  matrixMultiplication_borderRank_lower_X (K := K) hm
    h.matrixMultiplication_cycle.matrixMultiplication_cycle

/-- Flattening on the `Z` leg: a border-rank certificate for `⟨m,n,p⟩` with `n` positive has
size at least `p * m`.

Proof: rotating the certificate once turns `⟨m,n,p⟩` into `⟨p,m,n⟩`, whose `X`-leg bound is
exactly `p * m ≤ r` and whose contracted dimension is the original `n`. -/
theorem matrixMultiplication_borderRank_lower_Z
    {m n p r : ℕ} (hn : 0 < n)
    (h : BorderRankLE r (matrixMultiplication (K := K) m n p)) :
    p * m ≤ r :=
  matrixMultiplication_borderRank_lower_X (K := K) hn h.matrixMultiplication_cycle

/-- Every border-rank certificate for positive rectangular matrix multiplication has size at
least the largest product of two of the three dimensions. -/
theorem matrixMultiplication_borderRank_lower_max
    {m n p r : ℕ} (hm : 0 < m) (hn : 0 < n) (hp : 0 < p)
    (h : BorderRankLE r (matrixMultiplication (K := K) m n p)) :
    max (m * n) (max (n * p) (p * m)) ≤ r := by
  have hdim := h.max_finrank_le
    (matrixMultiplication_isConcise (K := K) hm hn hp)
  simpa [MMSpace, MMIndex, Module.finrank_fintype_fun_eq_card] using hdim

/-- Numeric form: the border rank of a positive rectangular matrix-multiplication tensor is at
least the largest product of two of its dimensions. -/
theorem max_le_borderRank_matrixMultiplication
    {m n p : ℕ} (hm : 0 < m) (hn : 0 < n) (hp : 0 < p) :
    max (m * n) (max (n * p) (p * m)) ≤
      borderRank (matrixMultiplication (K := K) m n p) :=
  matrixMultiplication_borderRank_lower_max hm hn hp (borderRank_spec _)

end AlgebraicComplexity
