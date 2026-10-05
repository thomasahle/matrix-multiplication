/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.CoordinateCertificate

/-!
# Hopcroft--Kerr upper bounds for `(p × 2) · (2 × n)` products

Primary source: J. E. Hopcroft and L. R. Kerr, *On minimizing the number of multiplications
necessary for matrix multiplication*, SIAM J. Appl. Math. **20** (1971), no. 1, 30--36.

Theorem 1 (p. 31) states that a `p × 2` matrix can be multiplied by a `2 × n` matrix using
`⌈(3pn + max(n,p))/2⌉` multiplications, without using commutativity of the matrix entries.  In
the tensor language of this repository "without commutativity" is exactly a decomposition of the
matrix-multiplication tensor into that many pure tensors, i.e. a `RankLE` certificate.

## Orientation

`matrixMultiplication K m n p` has legs indexed by `Fin m × Fin n`, `Fin n × Fin p` and
`Fin p × Fin m`; it is the tensor of the product of an `m × n` matrix with an `n × p` matrix.
Hopcroft--Kerr's `(p × 2) · (2 × n)` product therefore corresponds to
`matrixMultiplication K p 2 n` in the local naming, and their parameter `p` is the *first*
dimension while their `n` is the *last* one.  The instance formalized here is their `p = 2`,
`n = 3`, i.e. a `(2 × 2) · (2 × 3)` product, which is `matrixMultiplication K 2 2 3`.  Its
Hopcroft--Kerr count is

```text
⌈(3 · 2 · 3 + max 3 2)/2⌉ = ⌈21/2⌉ = 11.
```

This is the smallest instance of Theorem 1 that is not already Strassen's `2 × 2` algorithm
(`p = n = 2` gives `⌈14/2⌉ = 7`), and it is genuinely the tensor rank: Theorems 2 and 3
(pp. 35) of the same paper prove the matching `⌈7n/2⌉` lower bound for `(2 × 2) · (2 × n)`
products over the mod-`2` coefficient domain.  Only the *upper* bound is formalized here; the
matching lower bound needs the nine-group averaging argument of their Lemmas 3--5 and is listed
as a separate target in `LOWER_BOUNDS_ROADMAP.md`.

## What is verified, and what the paper actually contains

The published proof of Theorem 1 is explicitly a sketch: the authors write "The details are
tedious and of little interest to the development and thus are omitted" (footnote 1, p. 31) and
refer to Cornell TR 69-44 for the transformation-group bookkeeping that produces the individual
products.  That technical report is not available to this repository, so the paper alone does not
determine a unique term list for `⟨2,2,3⟩`.  What this file therefore ships is an explicit
eleven-term certificate that *realizes* the Hopcroft--Kerr count for this instance and is checked
by the Lean kernel: seven Strassen products handle output columns `0` and `1`, and four plain
products handle the remaining output column.  The count `7 + 4 = 11` agrees with Theorem 1, and
by Theorem 3 no shorter certificate exists.  Nothing here claims to reproduce the particular
products that Hopcroft and Kerr's group-theoretic construction would emit.

## Layer placement and house pattern

This is a layer-4 regression client (see `DESIGN.md`): it consumes the public
`matrixMultiplication`/`RankLE` API and contributes no reusable definitions.  It follows the
house certificate pattern of `MatrixMultiplication/CoordinateCertificate.lean`, as
`Examples/Strassen.lean` does: the finite identity is checked once over `ℤ` by kernel `decide`,
and `MMCertificate.rankLE_of_intCoefficient` transports the integer coefficient table to an
arbitrary commutative ring.

## Main results

* `HopcroftKerr.count` -- the paper's Theorem 1 formula, and its values at `(2,2)` and `(2,3)`;
* `HopcroftKerr.decomposition` -- the eleven displayed pure tensors sum to `⟨2,2,3⟩`;
* `HopcroftKerr.rankLE_two_two_three` -- `R(⟨2,2,3⟩) ≤ 11 = count 2 3`;
* `HopcroftKerr.rankLE_three_two_two`, `HopcroftKerr.rankLE_two_three_two` -- the two cyclic
  rotations, which are the `(3 × 2) · (2 × 2)` and `(2 × 3) · (3 × 2)` readings of the same
  algorithm;
* `HopcroftKerr.rankLE_sq` -- `R(⟨4,4,9⟩) ≤ 121`, a small exercise of the product law.

## Non-goals

The general recursive statement of Theorem 1 for all `(p, n)`, the `⌈7n/2⌉` lower bound
(Theorem 2), the `rank ⟨3,2,3⟩ = 15` remark (p. 35), and the commutativity comparison of §3 are
deliberately out of scope here.
-/

namespace AlgebraicComplexity.Examples.HopcroftKerr

open AlgebraicComplexity Tensor

universe u

/-- The Hopcroft--Kerr Theorem 1 multiplication count `⌈(3pn + max(n,p))/2⌉` for a
`(p × 2) · (2 × n)` product, written with natural-number division.

Here `p` is the number of rows of the left factor and `n` the number of columns of the right
factor, matching the paper's notation. -/
def count (p n : ℕ) : ℕ := (3 * p * n + max n p + 1) / 2

/-- At `p = n = 2` the Hopcroft--Kerr count is Strassen's seven. -/
@[simp] theorem count_two_two : count 2 2 = 7 := by norm_num [count]

/-- At `p = 2`, `n = 3` the Hopcroft--Kerr count is eleven; this is the instance certified
below. -/
@[simp] theorem count_two_three : count 2 3 = 11 := by norm_num [count]

/-- At `p = n = 3` the Hopcroft--Kerr count is fifteen, the value the paper reports (p. 35) as
necessary and sufficient for `(3 × 2) · (2 × 3)`.  Recorded for reference only; no certificate
for `⟨3,2,3⟩` is provided in this file. -/
theorem count_three_three : count 3 3 = 15 := by norm_num [count]

/-- Standard basis vector `a i j` of the left `2 × 2` factor. -/
private def eA (i j : Fin 2) : MMSpace ℤ 2 2 3 .X := Pi.single (i, j) 1

/-- Standard basis vector `x j k` of the right `2 × 3` factor. -/
private def eB (j : Fin 2) (k : Fin 3) : MMSpace ℤ 2 2 3 .Y := Pi.single (j, k) 1

/-- Standard basis vector of the output leg.  The `Z` index is ordered
`(output column, output row)`, so `eC k i` is the coefficient functional reading off the
`(i, k)` entry of the product. -/
private def eC (k : Fin 3) (i : Fin 2) : MMSpace ℤ 2 2 3 .Z := Pi.single (k, i) 1

/-- The eleven integer triples of linear forms certifying `R(⟨2,2,3⟩) ≤ 11`.

The first seven entries are Strassen's products, applied to the `2 × 2` submatrix formed by
columns `0` and `1` of the right factor; the last four are the plain inner products computing
the remaining output column.  The `Z` coordinate is ordered `(output column, output row)`,
matching `matrixMultiplication K 2 2 3`. -/
def intTerms : List (∀ c, MMSpace ℤ 2 2 3 c) :=
  [ ofLegs (eA 0 0 + eA 1 1) (eB 0 0 + eB 1 1) (eC 0 0 + eC 1 1),
    ofLegs (eA 1 0 + eA 1 1) (eB 0 0)          (eC 0 1 - eC 1 1),
    ofLegs (eA 0 0)          (eB 0 1 - eB 1 1) (eC 1 0 + eC 1 1),
    ofLegs (eA 1 1)          (eB 1 0 - eB 0 0) (eC 0 0 + eC 0 1),
    ofLegs (eA 0 0 + eA 0 1) (eB 1 1)          (eC 1 0 - eC 0 0),
    ofLegs (eA 1 0 - eA 0 0) (eB 0 0 + eB 0 1) (eC 1 1),
    ofLegs (eA 0 1 - eA 1 1) (eB 1 0 + eB 1 1) (eC 0 0),
    ofLegs (eA 0 0)          (eB 0 2)          (eC 2 0),
    ofLegs (eA 0 1)          (eB 1 2)          (eC 2 0),
    ofLegs (eA 1 0)          (eB 0 2)          (eC 2 1),
    ofLegs (eA 1 1)          (eB 1 2)          (eC 2 1) ]

-- The kernel evaluation of the `144`-entry coefficient table below is deeper than the default
-- recursion limit; this is a closed finite computation, not a proof-search budget.
set_option maxRecDepth 8000 in
/-- The finite integer coefficient table underlying the Hopcroft--Kerr identity: at every one of
the `4 · 6 · 6` basis indices the displayed sum has coefficient `1` on the support of
`⟨2,2,3⟩` and `0` elsewhere.

Proof sketch: the statement is a closed decidable proposition over a finite index type, so the
kernel evaluates all `144` coordinates directly.  Checking the table once over `ℤ` is the whole
mathematical content; the house harness of
`MatrixMultiplication/CoordinateCertificate.lean` transports it to every commutative ring. -/
theorem coefficient_int (a : ∀ c, MMIndex 2 2 3 c) :
    MMCertificate.coefficient ℤ intTerms a = if MMCompatible a then 1 else 0 := by
  decide +revert

section

variable (K : Type u) [CommRing K]

/-- The eleven triples of linear forms over an arbitrary commutative ring: the integer table
`intTerms`, read entrywise through `Int.cast`. -/
def terms : List (∀ c, MMSpace K 2 2 3 c) :=
  MMCertificate.castTerms K intTerms

/-- The certificate uses exactly the Hopcroft--Kerr count of products. -/
@[simp] theorem terms_length : (terms K).length = count 2 3 := by
  simp [terms, intTerms, count]

/-- The eleven displayed pure tensors sum to the `(2 × 2) · (2 × 3)` matrix-multiplication
tensor.

Proof sketch: the `Int`-certificate one-shot `MMCertificate.decomposition_of_intCoefficient`
applied to the kernel-checked table `coefficient_int`. -/
theorem decomposition :
    matrixMultiplication (K := K) 2 2 3 = ((terms K).map (pure (K := K))).sum :=
  MMCertificate.decomposition_of_intCoefficient intTerms coefficient_int

/-- **Hopcroft--Kerr, Theorem 1 at `p = 2`, `n = 3`.**  A `2 × 2` matrix can be multiplied by a
`2 × 3` matrix with eleven noncommutative multiplications: `R(⟨2,2,3⟩) ≤ 11`. -/
theorem rankLE_two_two_three :
    RankLE 11 (matrixMultiplication (K := K) 2 2 3) :=
  MMCertificate.rankLE_of_intCoefficient intTerms (by simp [intTerms]) coefficient_int

/-- The same bound stated with the paper's own count formula, `R(⟨2,2,3⟩) ≤ ⌈(3·2·3+3)/2⌉`. -/
theorem rankLE_count :
    RankLE (count 2 3) (matrixMultiplication (K := K) 2 2 3) := by
  simpa using rankLE_two_two_three K

/-- Cyclic rotation of the certificate: `R(⟨3,2,2⟩) ≤ 11`, the `(3 × 2) · (2 × 2)` reading of
the same algorithm (Hopcroft--Kerr Theorem 1 at `p = 3`, `n = 2`, whose count is also
`⌈(18+3)/2⌉ = 11`). -/
theorem rankLE_three_two_two :
    RankLE 11 (matrixMultiplication (K := K) 3 2 2) :=
  (rankLE_two_two_three K).matrixMultiplication_cycle

/-- Cyclic rotation of the certificate: `R(⟨2,3,2⟩) ≤ 11`. -/
theorem rankLE_two_three_two :
    RankLE 11 (matrixMultiplication (K := K) 2 3 2) :=
  (rankLE_three_two_two K).matrixMultiplication_cycle

/-- Squaring the Hopcroft--Kerr certificate: `R(⟨4,4,9⟩) ≤ 121`.

Proof sketch: `RankLE.matrixMultiplication_mul` transports a product of two rank certificates
across the canonical reindexing of the external tensor product, which sends
`⟨2,2,3⟩ ⊗ ⟨2,2,3⟩` to `⟨4,4,9⟩`.  This is recorded only as a small exercise of the product law;
the resulting exponent bound is weaker than Strassen's, exactly as Hopcroft and Kerr note (their
goal is exact small counts, not asymptotics). -/
theorem rankLE_sq :
    RankLE 121 (matrixMultiplication (K := K) 4 4 9) := by
  simpa using (rankLE_two_two_three K).matrixMultiplication_mul (rankLE_two_two_three K)

end

end AlgebraicComplexity.Examples.HopcroftKerr

