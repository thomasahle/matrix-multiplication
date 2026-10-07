/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication
import AlgebraicComplexity.MatrixMultiplication.Exponent
import OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Arithmetic.FieldExtension
import OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Arithmetic.RankBound

/-!
# `ω ≤ 9/4` over every field, for this repository's exponent

`ThirdParty/OAI/` vendors the Lean proof that the matrix-multiplication exponent is at most
`9/4`: OpenAI's proof over `ℂ` (`openai/math`), in the form generalized to every field by
`selanavot/matrix-multiplication-all-fields` (see `ThirdParty/README.md` for sources, commits
and licences).  That development has its own coordinate tensors `X → Y → Z → K`, its own rank
predicate `Tensor.RankAtMost`, and its own exponent
`exactRankExponent K = inf_{n ≥ 2} log_n R_K(⟨n,n,n⟩)`.

This file is the bridge to the definitions of this repository.  It proves that an exact
decomposition in their sense is a `RankLE` certificate of `matrixMultiplication n n n` here, and
then feeds the finite-rank consequence of their exponent bound through `omega_le_log_of_rankLE`.
Nothing of their arithmetic-program model is used, and none of it is imported: the conclusion is
a statement about `AlgebraicComplexity.omega`, the polynomial growth exponent of tensor rank.

## Main results

* `rankLE_matrixMultiplication_of_rankAtMost`: an `OAI` rank decomposition of `⟨n,n,n⟩` over a
  field `K` is a `RankLE` certificate.
* `omega_le_exactRankExponent`: `omega K` is at most their exact-rank exponent.
* `exactRankExponent_le_nine_quarters`: their bound over an arbitrary field, assembled from the
  algebraically closed case and the descent along `K → AlgebraicClosure K`.
* `omega_le_nine_quarters`: **`omega K ≤ 9/4` for every field `K`**.

## Trust

The statement is this repository's; the proof is theirs.  The enforcing axiom audit for the
headline is in `OpenAIBridge/Audit.lean`.
-/

namespace AlgebraicComplexity.OpenAIBridge

open Tensor

universe u

variable {K : Type u} [Field K]

/-- An exact decomposition of the `OAI` coordinate tensor `⟨n,n,n⟩` into `R` simple tensors is a
rank certificate for this repository's `matrixMultiplication n n n`.

The two tensors use the same index convention — `X = (i,j)`, `Y = (j,k)`, `Z = (k,i)` — so the
vectors of the decomposition are used unchanged and the two sides are compared coefficient by
coefficient. -/
theorem rankLE_matrixMultiplication_of_rankAtMost {n R : ℕ}
    (h : OAI.MatrixMultiplication.Foundation.Tensor.RankAtMost
      (OAI.MatrixMultiplication.AuxiliarySeparation.matrixMultiplicationTensor (K := K) n n n)
      R) :
    RankLE R (matrixMultiplication (K := K) n n n) := by
  classical
  obtain ⟨a, b, c, habc⟩ := h
  have hT : matrixMultiplication (K := K) n n n =
      ∑ i : Fin R, pure (K := K) (ofLegs (V := MMSpace K n n n) (a i) (b i) (c i)) := by
    refine standardCoordinate_ext fun p ↦ ?_
    rw [standardCoordinateEquiv_matrixMultiplication, map_sum, Finset.sum_apply]
    simp only [standardCoordinateEquiv_pure, prod_leg, ofLegs_X, ofLegs_Y, ofLegs_Z]
    have hp := congrFun (congrFun (congrFun habc (p .X)) (p .Y)) (p .Z)
    simp only [OAI.MatrixMultiplication.AuxiliarySeparation.matrixMultiplicationTensor,
      OAI.MatrixMultiplication.Foundation.Tensor.rankOne] at hp
    rw [← hp]
  rw [hT]
  simpa using RankLE.fintype_sum_pure (K := K)
    fun i : Fin R ↦ ofLegs (V := MMSpace K n n n) (a i) (b i) (c i)

/-- This repository's exponent over `K` is at most the `OAI` exact-rank exponent of `K`. -/
theorem omega_le_exactRankExponent (K : Type u) [Field K] :
    omega K ≤ OAI.MatrixMultiplication.AuxiliarySeparation.exactRankExponent K := by
  refine le_of_forall_pos_le_add fun ε hε ↦ ?_
  obtain ⟨n, R, hn, hR, hbound⟩ :=
    OAI.MatrixMultiplication.AuxiliarySeparation.exists_rankAtMost_of_exponent_slack
      (K := K) hε
  have hn1 : 1 < n := by omega
  have hRpos : 1 ≤ R := by
    have h := OAI.MatrixMultiplication.AuxiliarySeparation.matrixMultiplication_rank_lower
      (by omega : 0 < n) hR
    have h2 : 0 < n ^ 2 := pow_pos (by omega) 2
    omega
  have h1 := omega_le_log_of_rankLE K hn1 hRpos (rankLE_matrixMultiplication_of_rankAtMost hR)
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hlogn : 0 < Real.log n := Real.log_pos (by exact_mod_cast hn1)
  have hlog : Real.log R / Real.log n ≤
      OAI.MatrixMultiplication.AuxiliarySeparation.exactRankExponent K + ε := by
    rw [div_le_iff₀ hlogn]
    have h := Real.log_le_log (by exact_mod_cast hRpos : (0 : ℝ) < R) hbound
    rwa [Real.log_rpow hnpos] at h
  exact h1.trans hlog

/-- The `OAI` exact-rank exponent of every field is at most `9/4`: the algebraically closed case
(OpenAI's argument, with the field-sensitive steps generalized) followed by the descent along
`K → AlgebraicClosure K`.  This is the statement `exactRankExponent_le_nine_quarters_allFields` of
the vendored `AuxiliarySeparation/Main.lean`, re-derived here from its two ingredients so that
this bridge need not import the arithmetic-program layer. -/
theorem exactRankExponent_le_nine_quarters (K : Type u) [Field K] :
    OAI.MatrixMultiplication.AuxiliarySeparation.exactRankExponent K ≤ 9 / 4 :=
  (OAI.MatrixMultiplication.AuxiliarySeparation.exactRankExponent_le_algebraicClosure K).trans
    (OAI.MatrixMultiplication.AuxiliarySeparation.exactRankExponent_le_nine_quarters
      (K := AlgebraicClosure K))

/-- **The matrix-multiplication exponent of every field is at most `9/4`**, for the rank-based
exponent `omega` of this repository.  The mathematical content is the vendored development in
`ThirdParty/OAI/`. -/
theorem omega_le_nine_quarters (K : Type u) [Field K] : omega K ≤ 9 / 4 :=
  (omega_le_exactRankExponent K).trans (exactRankExponent_le_nine_quarters K)

end AlgebraicComplexity.OpenAIBridge
