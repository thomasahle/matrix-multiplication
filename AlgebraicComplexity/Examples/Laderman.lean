/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.CoordinateCertificate
import AlgebraicComplexity.MatrixMultiplication.Exponent

/-!
# Laderman's 23-multiplication algorithm for `3 × 3` matrices

This file is a self-contained regression client (layer 4 of `DESIGN.md`) for the constructive
tensor-rank API.  It records Laderman's explicit bilinear algorithm for the `3 × 3` matrix
product as 23 integer coordinate triples, verifies the resulting trilinear identity by a
kernel-checked computation over `ℤ`, and packages the result as the tensor-rank certificate
`RankLE 23 (matrixMultiplication K 3 3 3)` over an arbitrary commutative ring `K`.

Primary source: J. D. Laderman, *A noncommutative algorithm for multiplying `3 × 3` matrices
using 23 multiplications*, Bull. Amer. Math. Soc. **82** (1976), no. 1, 126--128.

The 23 triples of `ladermanTable` are transcribed, in order and with their signs, from the
full contraction of the Laderman tensor displayed as equation (12) of A. Sedoglavic,
*Laderman matrix multiplication algorithm can be constructed using Strassen algorithm and
related tensor's isotropies*, arXiv:1703.08298, which reproduces Laderman's original
algorithm rather than one of its isotropy variants.  As a cross-check on the transcription,
the first triple is the product `(a11 + a12 + a13 - a21 - a22 - a32 - a33) * b22` that is
quoted from Laderman's paper throughout the literature, and the last five triples are the
five plain products `a12 b21`, `a23 b32`, `a21 b13`, `a31 b12`, `a33 b33`.  In any case the
identity is verified here from scratch: nothing about the table is taken on trust.

## Hypotheses

The certificate is **not** subtraction-free: sixteen of the 23 triples contain a `-1`
coefficient, and Laderman's identity genuinely cancels terms.  A commutative *semiring* is
therefore not enough and `CommRing K` is the weakest hypothesis available here.  Beyond
subtraction nothing is used: all coefficients lie in `{-1, 0, 1}`, so the algorithm is valid
over every commutative ring, with no division, no characteristic assumption, no field
hypothesis and no invertible constant.

## Layout of the certificate

`AlgebraicComplexity.MatrixMultiplication` fixes the trilinear form
`⟨m,n,p⟩ = ∑ i j k, x_{ij} ⊗ y_{jk} ⊗ z_{ki}`, so the three legs of a term are indexed by
`(i,j)`, `(j,k)` and `(k,i)` respectively.  Accordingly each entry of `ladermanTable` is a
triple of `3 × 3` integer matrices `(A, B, C)` read as

* `A i j` — the coefficient of `a_{ij}` in the left factor;
* `B j k` — the coefficient of `b_{jk}` in the right factor;
* `C k i` — the coefficient of `c_{ki}`, i.e. of the `(i,k)` entry of the product, in the
  output combination.

The comment above each entry displays that triple in the notation of the source.

## Verification strategy

Following the `Int`-certificate-plus-cast pattern of `DESIGN.md` and `Examples/Strassen.lean`:

1. `ladermanIntCoefficient` evaluates the 23-term coordinate sum over `ℤ` at one standard
   basis index of the three legs.  It mentions no ring casts and no `Finset`, so its
   defining equation reduces cheaply in the kernel.
2. `ladermanIntCoefficient_eq` checks that this integer table is exactly the support
   indicator `MMCompatible` of `⟨3,3,3⟩`, at all `9 * 9 * 9 = 729` basis indices.  This
   single finite computation is the whole mathematical content of the algorithm.
3. `coefficient_ladermanIntTerms` identifies that table with the house-harness coefficient of
   `ladermanIntTerms`, and `MMCertificate.rankLE_of_intCoefficient`
   (`MatrixMultiplication/CoordinateCertificate.lean`) transports it to an arbitrary commutative
   ring `K` through `Int.cast`, so no symbolic ring computation is ever repeated.
4. `laderman_decomposition` and `laderman_rankLE` package the identity as a tensor equation
   and then as a constructive rank certificate.

Step 2 is discharged by `decide` on the auxiliary lemma `ladermanIntCoefficient_aux`, whose
six loose `Fin 3` arguments make the enumeration go through `Fin`'s inexpensive `Fintype`
instance.  The `+kernel` modifier sends the resulting closed evaluation straight to the
kernel instead of running it in the elaborator: the same computation, checked by the same
trusted kernel, but about four times faster here.  It enlarges the trusted base by nothing,
and unlike compiler-backed evaluation it carries no soundness postulate.  The audited
declarations of this file depend only on `propext`, `Classical.choice` and `Quot.sound`.

## Non-goals

The matching lower bound is not addressed here; the best published lower bound for
`R(⟨3,3,3⟩)` is Bläser's `19`, and whether `23` is optimal is open.  Only the exact rank
upper bound and its exponent corollary are proved.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor

universe u

/-- Laderman's 23 triples, as integer coordinate tables.

Each entry `(A, B, C)` stands for the pure tensor
`(∑ i j, A i j * a_{ij}) ⊗ (∑ j k, B j k * b_{jk}) ⊗ (∑ k i, C k i * c_{ki})`,
matching the leg indexing of `matrixMultiplication K 3 3 3`.  All coefficients are `-1`, `0`
or `1`.  The comment on each line displays the triple in the notation of Laderman's paper.
-/
def ladermanTable :
    List ((Fin 3 → Fin 3 → ℤ) × (Fin 3 → Fin 3 → ℤ) × (Fin 3 → Fin 3 → ℤ)) :=
[
  --  1.  (a11+a12+a13-a21-a22-a32-a33) · (b22) · (c21)
  (![![ 1, 1, 1], ![-1,-1, 0], ![ 0,-1,-1]],
   ![![ 0, 0, 0], ![ 0, 1, 0], ![ 0, 0, 0]],
   ![![ 0, 0, 0], ![ 1, 0, 0], ![ 0, 0, 0]]),
  --  2.  (a22) · (-b11+b12+b21-b22-b23-b31+b33) · (c12)
  (![![ 0, 0, 0], ![ 0, 1, 0], ![ 0, 0, 0]],
   ![![-1, 1, 0], ![ 1,-1,-1], ![-1, 0, 1]],
   ![![ 0, 1, 0], ![ 0, 0, 0], ![ 0, 0, 0]]),
  --  3.  (a13) · (b31) · (c11+c12+c13+c21+c23+c31+c32)
  (![![ 0, 0, 1], ![ 0, 0, 0], ![ 0, 0, 0]],
   ![![ 0, 0, 0], ![ 0, 0, 0], ![ 1, 0, 0]],
   ![![ 1, 1, 1], ![ 1, 0, 1], ![ 1, 1, 0]]),
  --  4.  (a11+a12+a13-a22-a23-a31-a32) · (b23) · (c31)
  (![![ 1, 1, 1], ![ 0,-1,-1], ![-1,-1, 0]],
   ![![ 0, 0, 0], ![ 0, 0, 1], ![ 0, 0, 0]],
   ![![ 0, 0, 0], ![ 0, 0, 0], ![ 1, 0, 0]]),
  --  5.  (a32) · (-b11+b13+b21-b22-b23-b31+b32) · (c13)
  (![![ 0, 0, 0], ![ 0, 0, 0], ![ 0, 1, 0]],
   ![![-1, 0, 1], ![ 1,-1,-1], ![-1, 1, 0]],
   ![![ 0, 0, 1], ![ 0, 0, 0], ![ 0, 0, 0]]),
  --  6.  (a11) · (b11) · (c11+c12+c13+c21+c22+c31+c33)
  (![![ 1, 0, 0], ![ 0, 0, 0], ![ 0, 0, 0]],
   ![![ 1, 0, 0], ![ 0, 0, 0], ![ 0, 0, 0]],
   ![![ 1, 1, 1], ![ 1, 1, 0], ![ 1, 0, 1]]),
  --  7.  (-a11+a31+a32) · (b11-b13+b23) · (c13+c31+c33)
  (![![-1, 0, 0], ![ 0, 0, 0], ![ 1, 1, 0]],
   ![![ 1, 0,-1], ![ 0, 0, 1], ![ 0, 0, 0]],
   ![![ 0, 0, 1], ![ 0, 0, 0], ![ 1, 0, 1]]),
  --  8.  (-a13+a22+a23) · (b23+b31-b33) · (c12+c31+c32)
  (![![ 0, 0,-1], ![ 0, 1, 1], ![ 0, 0, 0]],
   ![![ 0, 0, 0], ![ 0, 0, 1], ![ 1, 0,-1]],
   ![![ 0, 1, 0], ![ 0, 0, 0], ![ 1, 1, 0]]),
  --  9.  (-a11+a21+a22) · (b11-b12+b22) · (c12+c21+c22)
  (![![-1, 0, 0], ![ 1, 1, 0], ![ 0, 0, 0]],
   ![![ 1,-1, 0], ![ 0, 1, 0], ![ 0, 0, 0]],
   ![![ 0, 1, 0], ![ 1, 1, 0], ![ 0, 0, 0]]),
  -- 10.  (-a13+a32+a33) · (b22+b31-b32) · (c13+c21+c23)
  (![![ 0, 0,-1], ![ 0, 0, 0], ![ 0, 1, 1]],
   ![![ 0, 0, 0], ![ 0, 1, 0], ![ 1,-1, 0]],
   ![![ 0, 0, 1], ![ 1, 0, 1], ![ 0, 0, 0]]),
  -- 11.  (a21+a22) · (-b11+b12) · (c21+c22)
  (![![ 0, 0, 0], ![ 1, 1, 0], ![ 0, 0, 0]],
   ![![-1, 1, 0], ![ 0, 0, 0], ![ 0, 0, 0]],
   ![![ 0, 0, 0], ![ 1, 1, 0], ![ 0, 0, 0]]),
  -- 12.  (a31+a32) · (-b11+b13) · (c31+c33)
  (![![ 0, 0, 0], ![ 0, 0, 0], ![ 1, 1, 0]],
   ![![-1, 0, 1], ![ 0, 0, 0], ![ 0, 0, 0]],
   ![![ 0, 0, 0], ![ 0, 0, 0], ![ 1, 0, 1]]),
  -- 13.  (a13-a33) · (b22-b32) · (c13+c23)
  (![![ 0, 0, 1], ![ 0, 0, 0], ![ 0, 0,-1]],
   ![![ 0, 0, 0], ![ 0, 1, 0], ![ 0,-1, 0]],
   ![![ 0, 0, 1], ![ 0, 0, 1], ![ 0, 0, 0]]),
  -- 14.  (a11-a21) · (-b12+b22) · (c12+c22)
  (![![ 1, 0, 0], ![-1, 0, 0], ![ 0, 0, 0]],
   ![![ 0,-1, 0], ![ 0, 1, 0], ![ 0, 0, 0]],
   ![![ 0, 1, 0], ![ 0, 1, 0], ![ 0, 0, 0]]),
  -- 15.  (a32+a33) · (-b31+b32) · (c21+c23)
  (![![ 0, 0, 0], ![ 0, 0, 0], ![ 0, 1, 1]],
   ![![ 0, 0, 0], ![ 0, 0, 0], ![-1, 1, 0]],
   ![![ 0, 0, 0], ![ 1, 0, 1], ![ 0, 0, 0]]),
  -- 16.  (-a11+a31) · (b13-b23) · (c13+c33)
  (![![-1, 0, 0], ![ 0, 0, 0], ![ 1, 0, 0]],
   ![![ 0, 0, 1], ![ 0, 0,-1], ![ 0, 0, 0]],
   ![![ 0, 0, 1], ![ 0, 0, 0], ![ 0, 0, 1]]),
  -- 17.  (a13-a23) · (b23-b33) · (c12+c32)
  (![![ 0, 0, 1], ![ 0, 0,-1], ![ 0, 0, 0]],
   ![![ 0, 0, 0], ![ 0, 0, 1], ![ 0, 0,-1]],
   ![![ 0, 1, 0], ![ 0, 0, 0], ![ 0, 1, 0]]),
  -- 18.  (a22+a23) · (-b31+b33) · (c31+c32)
  (![![ 0, 0, 0], ![ 0, 1, 1], ![ 0, 0, 0]],
   ![![ 0, 0, 0], ![ 0, 0, 0], ![-1, 0, 1]],
   ![![ 0, 0, 0], ![ 0, 0, 0], ![ 1, 1, 0]]),
  -- 19.  (a12) · (b21) · (c11)
  (![![ 0, 1, 0], ![ 0, 0, 0], ![ 0, 0, 0]],
   ![![ 0, 0, 0], ![ 1, 0, 0], ![ 0, 0, 0]],
   ![![ 1, 0, 0], ![ 0, 0, 0], ![ 0, 0, 0]]),
  -- 20.  (a23) · (b32) · (c22)
  (![![ 0, 0, 0], ![ 0, 0, 1], ![ 0, 0, 0]],
   ![![ 0, 0, 0], ![ 0, 0, 0], ![ 0, 1, 0]],
   ![![ 0, 0, 0], ![ 0, 1, 0], ![ 0, 0, 0]]),
  -- 21.  (a21) · (b13) · (c32)
  (![![ 0, 0, 0], ![ 1, 0, 0], ![ 0, 0, 0]],
   ![![ 0, 0, 1], ![ 0, 0, 0], ![ 0, 0, 0]],
   ![![ 0, 0, 0], ![ 0, 0, 0], ![ 0, 1, 0]]),
  -- 22.  (a31) · (b12) · (c23)
  (![![ 0, 0, 0], ![ 0, 0, 0], ![ 1, 0, 0]],
   ![![ 0, 1, 0], ![ 0, 0, 0], ![ 0, 0, 0]],
   ![![ 0, 0, 0], ![ 0, 0, 1], ![ 0, 0, 0]]),
  -- 23.  (a33) · (b33) · (c33)
  (![![ 0, 0, 0], ![ 0, 0, 0], ![ 0, 0, 1]],
   ![![ 0, 0, 0], ![ 0, 0, 0], ![ 0, 0, 1]],
   ![![ 0, 0, 0], ![ 0, 0, 0], ![ 0, 0, 1]])
]

/-- Laderman's certificate has exactly 23 terms. -/
@[simp] theorem ladermanTable_length : ladermanTable.length = 23 := rfl

/-- The integer coefficient of Laderman's 23-term sum at one standard basis index of the three
legs.

For `a` a triple of basis indices `(i,j)`, `(j,k)`, `(k,i)`, this is
`∑_{t < 23} A_t i j * B_t j k * C_t k i`.  It is stated over `ℤ` and without any `Finset` or
cast, so that the kernel can evaluate it directly. -/
def ladermanIntCoefficient (a : ∀ c, MMIndex 3 3 3 c) : ℤ :=
  (ladermanTable.map fun t ↦
      t.1 (a .X).1 (a .X).2 * t.2.1 (a .Y).1 (a .Y).2 * t.2.2 (a .Z).1 (a .Z).2).sum

/-- The finite computation behind Laderman's identity, stated on six loose `Fin 3` indices.

Reading `a_{ij} · b_{j'k} · c_{k'i'}`, the 23-term integer table evaluates to `1` exactly when
the three basis indices are compatible, that is when `j = j'`, `k = k'` and `i' = i`, and to
`0` otherwise.

Proof sketch: a closed finite statement over `ℤ`, discharged by kernel-checked `decide` after
reverting the six indices.  It is phrased on six separate `Fin 3` arguments rather than on a
dependent function `∀ c, MMIndex 3 3 3 c` because the decision procedure then enumerates
`3 ^ 6 = 729` tuples through `Fin`'s cheap `Fintype` instance instead of through the much more
expensive `Finset.pi` machinery behind `Pi.fintype`. -/
private theorem ladermanIntCoefficient_aux (i j j' k k' i' : Fin 3) :
    (ladermanTable.map fun t ↦ t.1 i j * t.2.1 j' k * t.2.2 k' i').sum =
      if j = j' ∧ k = k' ∧ i' = i then 1 else 0 := by
  decide +kernel +revert

/-- **Laderman's identity, as a finite integer computation.**  The 23-term coordinate table
agrees, at every one of the `729` standard basis indices, with the support indicator of the
`3 × 3` matrix-multiplication tensor: it is `1` on compatible triples `(i,j), (j,k), (k,i)`
and `0` elsewhere.

Proof sketch: destructure the three basis indices into six `Fin 3` components and apply
`ladermanIntCoefficient_aux`; `MMCompatible` unfolds to exactly the three componentwise
equations appearing there.  This one finite check is the entire mathematical content of the
algorithm. -/
theorem ladermanIntCoefficient_eq (a : ∀ c, MMIndex 3 3 3 c) :
    ladermanIntCoefficient a = if MMCompatible a then 1 else 0 := by
  rcases hX : a .X with ⟨i, j⟩
  rcases hY : a .Y with ⟨j', k⟩
  rcases hZ : a .Z with ⟨k', i'⟩
  simp only [ladermanIntCoefficient, MMCompatible, hX, hY, hZ]
  exact ladermanIntCoefficient_aux i j j' k k' i'

/-- Laderman's 23 rank-one terms as integer coordinate triples, in the leg indexing of
`matrixMultiplication ℤ 3 3 3`. -/
def ladermanIntTerms : List (∀ c, MMSpace ℤ 3 3 3 c) :=
  ladermanTable.map fun t ↦
    ofLegs (fun q ↦ t.1 q.1 q.2) (fun q ↦ t.2.1 q.1 q.2) (fun q ↦ t.2.2 q.1 q.2)

/-- The integer coefficient table of `ladermanIntTerms` is the kernel-checked
`ladermanIntCoefficient`: the house harness's coordinate sum over the three legs expands to the
`Finset`-free product of the three table entries. -/
theorem coefficient_ladermanIntTerms (a : ∀ c, MMIndex 3 3 3 c) :
    MMCertificate.coefficient ℤ ladermanIntTerms a = ladermanIntCoefficient a := by
  simp [MMCertificate.coefficient, ladermanIntTerms, ladermanIntCoefficient, List.map_map,
    Function.comp_def, prod_leg]

section

variable (K : Type u) [CommRing K]

/-- The 23 triples of linear forms in Laderman's decomposition, over an arbitrary commutative
ring `K`: the single integer table `ladermanTable`, read entrywise through `Int.cast`. -/
def ladermanTerms : List (∀ c, MMSpace K 3 3 3 c) :=
  MMCertificate.castTerms K ladermanIntTerms

/-- Laderman's decomposition uses 23 pure tensors. -/
@[simp] theorem ladermanTerms_length : (ladermanTerms K).length = 23 := by
  simp [ladermanTerms, ladermanIntTerms]

/-- **Laderman's decomposition.**  The 23 displayed pure tensors sum to the `3 × 3`
matrix-multiplication tensor over any commutative ring.

Proof sketch: the house harness's `Int`-certificate one-shot
`MMCertificate.decomposition_of_intCoefficient` needs exactly one input — that the integer
coefficient table of `ladermanIntTerms` is the support indicator of `⟨3,3,3⟩` — which is
`ladermanIntCoefficient_eq` read through `coefficient_ladermanIntTerms`. -/
theorem laderman_decomposition :
    matrixMultiplication (K := K) 3 3 3 =
      ((ladermanTerms K).map (pure (K := K))).sum :=
  MMCertificate.decomposition_of_intCoefficient ladermanIntTerms fun a ↦
    (coefficient_ladermanIntTerms a).trans (ladermanIntCoefficient_eq a)

/-- **Laderman's bound.**  The constructive tensor-rank upper bound
`R(⟨3,3,3⟩) ≤ 23` over every commutative ring. -/
theorem laderman_rankLE :
    RankLE 23 (matrixMultiplication (K := K) 3 3 3) :=
  MMCertificate.rankLE_of_intCoefficient ladermanIntTerms (by simp [ladermanIntTerms])
    fun a ↦ (coefficient_ladermanIntTerms a).trans (ladermanIntCoefficient_eq a)

/-- Tensor powers of Laderman's decomposition give rank `23 ^ k` for multiplication of
`3 ^ k × 3 ^ k` matrices. -/
theorem laderman_rankLE_pow (k : ℕ) :
    RankLE (23 ^ k)
      (matrixMultiplication (K := K) (3 ^ k) (3 ^ k) (3 ^ k)) :=
  (laderman_rankLE K).matrixMultiplication_pow k

/-- Laderman's exact algorithm gives the exponent bound `ω ≤ log₃(23) ≈ 2.854`.

This is weaker than Strassen's `log₂ 7 ≈ 2.807`; Laderman's algorithm is a landmark for the
exact rank of `⟨3,3,3⟩`, not for the exponent. -/
theorem laderman_omega_le_log :
    omega K ≤ Real.log 23 / Real.log 3 :=
  omega_le_log_of_rankLE K (by norm_num) (by norm_num) (laderman_rankLE K)

end

end AlgebraicComplexity.Examples
