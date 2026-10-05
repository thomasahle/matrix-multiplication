/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.CoordinateCertificate
import Mathlib.Data.ZMod.Basic

/-!
# Machine-discovered matrix-multiplication decompositions over a field of characteristic two

This is a layer-4 regression client (see `DESIGN.md`).  It packages *search-produced* rank
certificates for small matrix-multiplication tensors, together with a small reusable-in-file
harness that turns a table of `0/1` coefficient bitmasks into a kernel-checked `RankLE`
certificate over any commutative ring in which `2 = 0`.

## Provenance of the data, and what is deliberately absent

The two decompositions shipped here were produced by a flip-graph search over `GF(2)` in the
style of M. Kauers and J. Moosbauer, *Flip graphs for matrix multiplication*, ISSAC 2023 --- the
search was run locally while preparing this file, and its output is reproduced verbatim below.
Nothing in the tables is transcribed from a paper, and nothing is asserted without the Lean
kernel re-checking every coordinate of the resulting tensor identity.

Two better-known machine-discovered decompositions were **not** formalized, because the
repository's local sources do not contain their factor tables:

* **AlphaTensor's rank-`47` decomposition of `⟨4,4,4⟩` over `GF(2)`** (Fawzi et al., *Discovering
  faster matrix multiplication algorithms with reinforcement learning*, Nature 610 (2022)).  That
  paper is not in `papers/`, and its factor tables live in the paper's supplementary data /
  the `deepmind-research` repository, neither of which is available here.
* **AlphaEvolve's rank-`48` complex decomposition of `⟨4,4,4⟩`** (entries in `ℤ[1/2]` and
  `ℤ[i]/2`).  The only AlphaEvolve-related source in `papers/` is `2608.16884`, *Improving the
  matrix multiplication exponent with modern optimization and AlphaEvolve*; that note is about
  the non-convex optimization problem inside combination-loss analysis of the laser method and
  contains **no** explicit tensor decomposition at all (its content is the `ω < 2.371177`
  bound).  Neither `papers/sources/2608.16884/main.tex` nor the PDF mentions a `4 × 4 × 4`
  factor table.

Reconstructing either table from memory is exactly the kind of unverifiable certificate that
`DESIGN.md` forbids, so those two rows stay open.  What is needed to close them is the
supplementary factorization data of the Nature paper (a `47 × 3 × 16` integer array) and of the
AlphaEvolve report (a `48 × 3 × 16` array over `ℤ[1/2]`); both are plain numerical data and
would drop straight into the harness below once a redistributable copy is in `papers/`.

Rediscovering the `⟨4,4,4⟩` rank-`47` decomposition locally was attempted and did not succeed.
The same `GF(2)` flip-graph walk that reaches rank `23` for `⟨3,3,3⟩` within seconds got no
further than rank `53` starting from the naive rank-`64` decomposition, and a second walk seeded
at the Strassen-squared rank-`49` decomposition produced no reduction at all in the time
available.  A signed flip-graph walk over `ℤ` was also run, and reached only `17` for `⟨3,2,3⟩`
and `26` for `⟨3,3,3⟩`; that is why the two theorems below are stated in characteristic two
rather than over an arbitrary commutative ring.  These are limits of the local search, not
mathematical obstructions: integer decompositions of the stated lengths are known to exist
(Hopcroft--Kerr for `⟨3,2,3⟩`, Laderman for `⟨3,3,3⟩`).  Note also that a `⟨4,4,4⟩` certificate
of length `49` would carry no information beyond Strassen's, since `RankLE.matrixMultiplication_mul`
already derives it.

## Contents

* `bitOf`, `maskTerm`, `maskTerms` --- a `0/1` certificate encoding in which
  each leg of each rank-one term is a natural-number bitmask.  Bit extraction is
  `w / 2 ^ t % 2`, and the certificate condition is stated entirely in `ℕ`, which the Lean kernel
  evaluates with its accelerated arithmetic; a whole coefficient table therefore stays inside a
  single feasible `decide`.
* `maskCount`, `coefficient_maskTerms` --- the same coordinate computed purely in `ℕ`, and
  the fact that every coordinate over a ring is the image of that natural number.
* `decomposition_of_odd_count`, `rankLE_of_odd_count` --- if at every basis index the number of
  covering table rows is odd exactly on the support of `⟨m,n,p⟩`, the table is an exact
  decomposition over any commutative ring with `2 = 0`, hence a rank certificate of length
  `tbl.length`.
* `table323`, `rankLE_three_two_three` --- `R(⟨3,2,3⟩) ≤ 15` in characteristic two, with its two
  cyclic rotations `rankLE_three_three_two` and `rankLE_two_three_three`.
* `table333`, `rankLE_three_three_three` --- `R(⟨3,3,3⟩) ≤ 23` in characteristic two, and its
  square `rankLE_nine`.

## Why these two targets

`R(⟨3,2,3⟩) ≤ 15` is the count Hopcroft and Kerr report on p. 35 of *On minimizing the number of
multiplications necessary for matrix multiplication*, SIAM J. Appl. Math. **20** (1971), 30--36:
"By similar techniques, one can show that 15 multiplications are necessary and sufficient for the
`(3 × 2) × (2 × 3)` case."  They give no construction --- the details are deferred to Cornell TR
69-44, which this repository does not have --- so the certificate below is an independent
machine-produced witness for the upper half of that claim, in characteristic two.  It agrees with
their Theorem 1 formula `⌈(3pn + max(n,p))/2⌉ = ⌈30/2⌉ = 15`; the companion file
`Examples/HopcroftKerrUpper.lean` verifies the `⟨2,2,3⟩` instance over an arbitrary commutative
ring.

`R(⟨3,3,3⟩) ≤ 23` is the classical Laderman bound (J. D. Laderman, *A noncommutative algorithm
for multiplying 3 × 3 matrices using 23 multiplications*, Bull. AMS **82** (1976), 126--128) and
is also the value AlphaTensor reports for `⟨3,3,3⟩` over `GF(2)`.  The certificate below is not
Laderman's; it is the search output, and it is only claimed in characteristic two.

## Scope of the statements

Both theorems are stated for a commutative ring `K` with `(2 : K) = 0` --- the weakest hypothesis
the certificates support, since they are `0/1` tables that reproduce the matrix-multiplication
tensor only modulo two.  `ZMod 2` corollaries are recorded as concrete instances.  No claim is
made over `ℤ` or over fields of other characteristic, and no exponent bound is derived: the
resulting exponents (`3 log 15 / log 18 ≈ 2.937`, `3 log 23 / log 27 ≈ 2.854`) are weaker than
Strassen's and would in any case be restricted to characteristic two.
-/

namespace AlgebraicComplexity.Examples.DiscoveredDecompositions

open AlgebraicComplexity Tensor

universe u

/-! ## A `0/1` bitmask certificate harness -/

/-- Flatten a pair of finite indices to a single natural number, row-major in the second
dimension.  On the three legs of `⟨m,n,p⟩` this sends `(i,j) ↦ i*n+j`, `(j,k) ↦ j*p+k` and
`(k,i) ↦ k*m+i`, which is the flattening used by the search program that produced the tables. -/
private def flat {a b : ℕ} (x : Fin a × Fin b) : ℕ := x.1.val * b + x.2.val

/-- Bit number `t` of the natural number `w`, as an element of `R`: the natural number
`w / 2 ^ t % 2`, which is `0` or `1`, cast into `R`.

Writing the bit as a cast natural number rather than an `if` is what lets every coefficient
check below run in `ℕ`, whose division and remainder the Lean kernel evaluates with accelerated
arithmetic. -/
def bitOf (R : Type u) [CommRing R] (w t : ℕ) : R := ((w / 2 ^ t % 2 : ℕ) : R)

/-- The rank-one term of `⟨m,n,p⟩` whose three legs are the `0/1` indicator vectors of the three
bitmasks in `t`. -/
def maskTerm (R : Type u) [CommRing R] (m n p : ℕ) (t : ℕ × ℕ × ℕ) :
    ∀ c, MMSpace R m n p c :=
  ofLegs (V := MMSpace R m n p)
    (fun a ↦ bitOf R t.1 (flat a))
    (fun a ↦ bitOf R t.2.1 (flat a))
    (fun a ↦ bitOf R t.2.2 (flat a))

/-- The list of rank-one terms encoded by a table of bitmask triples. -/
def maskTerms (R : Type u) [CommRing R] (m n p : ℕ) (tbl : List (ℕ × ℕ × ℕ)) :
    List (∀ c, MMSpace R m n p c) :=
  tbl.map (maskTerm R m n p)

/-- The number of rank-one terms is the length of the table. -/
@[simp] theorem maskTerms_length (R : Type u) [CommRing R] (m n p : ℕ)
    (tbl : List (ℕ × ℕ × ℕ)) : (maskTerms R m n p tbl).length = tbl.length := by
  simp [maskTerms]

/-- The same coordinate computed in `ℕ`: the number of table rows whose three bitmasks all
contain the given basis index.

This is the form every certificate check below is stated in.  It contains no ring operations,
no `ite`, and no `Int`, so the kernel evaluates a whole coefficient table using only accelerated
natural-number division, remainder, multiplication and addition. -/
def maskCount (m n p : ℕ) (tbl : List (ℕ × ℕ × ℕ)) (a : ∀ c, MMIndex m n p c) : ℕ :=
  (tbl.map fun t ↦
    t.1 / 2 ^ flat (a .X) % 2 * (t.2.1 / 2 ^ flat (a .Y) % 2)
      * (t.2.2 / 2 ^ flat (a .Z) % 2)).sum

/-- Every coordinate of a bitmask certificate is the image in `R` of its natural-number count.

Proof sketch: induction on the table.  Each leg entry is by definition a cast natural number, so
one row's coordinate is `Nat.cast` of a product of three natural numbers, and `Nat.cast`
commutes with the list sum. -/
theorem coefficient_maskTerms (R : Type u) [CommRing R] (m n p : ℕ)
    (tbl : List (ℕ × ℕ × ℕ)) (a : ∀ c, MMIndex m n p c) :
    MMCertificate.coefficient R (maskTerms R m n p tbl) a = (maskCount m n p tbl a : R) := by
  simp only [MMCertificate.coefficient, maskTerms, maskCount, List.map_map, Function.comp_def]
  induction tbl with
  | nil => simp
  | cons t rest ih =>
      simp only [List.map_cons, List.sum_cons, Nat.cast_add, ih]
      congr 1
      rw [prod_leg]
      simp [maskTerm, ofLegs, bitOf]

/-- **Characteristic-two soundness of a bitmask certificate.**  If at every basis index the
number of table rows covering that index is odd exactly on the support of `⟨m,n,p⟩`, then over a
commutative ring in which `2 = 0` the encoded rank-one terms sum exactly to `⟨m,n,p⟩`.

Proof sketch: the characteristic-two one-shot of the house harness
(`MMCertificate.decomposition_of_natCoefficient_mod_two`) applied with the natural-number count
`maskCount` and the identification `coefficient_maskTerms`. -/
theorem decomposition_of_odd_count {K : Type u} [CommRing K] (h2 : (2 : K) = 0)
    {m n p : ℕ} (tbl : List (ℕ × ℕ × ℕ))
    (h : ∀ a : ∀ c, MMIndex m n p c,
      maskCount m n p tbl a % 2 = if MMCompatible a then 1 else 0) :
    matrixMultiplication (K := K) m n p =
      ((maskTerms K m n p tbl).map (pure (K := K))).sum :=
  MMCertificate.decomposition_of_natCoefficient_mod_two h2 _ _
    (coefficient_maskTerms K m n p tbl) h

/-- **Rank certificate from a characteristic-two bitmask table.**  Under the same hypothesis as
`decomposition_of_odd_count`, the table witnesses `R(⟨m,n,p⟩) ≤ tbl.length` over any commutative
ring with `2 = 0`. -/
theorem rankLE_of_odd_count {K : Type u} [CommRing K] (h2 : (2 : K) = 0)
    {m n p : ℕ} (tbl : List (ℕ × ℕ × ℕ))
    (h : ∀ a : ∀ c, MMIndex m n p c,
      maskCount m n p tbl a % 2 = if MMCompatible a then 1 else 0) :
    RankLE tbl.length (matrixMultiplication (K := K) m n p) :=
  MMCertificate.rankLE_of_natCoefficient_mod_two h2 _
    (le_of_eq (maskTerms_length K m n p tbl)) _
    (coefficient_maskTerms K m n p tbl) h

/-! ## `⟨3,2,3⟩` in fifteen multiplications -/

/-- A fifteen-term `GF(2)` decomposition of `⟨3,2,3⟩`, found by a local flip-graph search.

Each triple `(u, v, w)` encodes one rank-one term: `u` is a six-bit mask on the left factor's
`3 × 2` entries (bit `2i + j` is entry `(i,j)`), `v` a six-bit mask on the right factor's
`2 × 3` entries (bit `3j + k`), and `w` a nine-bit mask on the output leg (bit `3k + i`, the
output entry `(i,k)`). -/
def table323 : List (ℕ × ℕ × ℕ) :=
  [(60, 5, 36), (40, 45, 3), (48, 56, 292), (11, 52, 237), (10, 36, 363),
   (16, 63, 6), (41, 53, 39), (1, 54, 46), (26, 60, 290), (42, 24, 291),
   (21, 3, 38), (4, 2, 54), (3, 48, 228), (15, 4, 164), (8, 16, 219)]

/-- The `⟨3,2,3⟩` table has the Hopcroft--Kerr count `⌈(3·3·3 + 3)/2⌉ = 15`. -/
@[simp] theorem table323_length : table323.length = 15 := by simp [table323]

-- The kernel evaluates the `6 · 6 · 9 = 324` coordinates of the table below; this is a closed
-- finite computation, not a proof-search budget.
set_option maxRecDepth 40000 in
/-- At every basis index, an odd number of rows of the `⟨3,2,3⟩` table cover that index exactly
on the support of `⟨3,2,3⟩`.

Proof sketch: a closed decidable statement over the finite index type
`∀ c, MMIndex 3 2 3 c`, evaluated by the kernel at all `324` basis indices in `ℕ`. -/
theorem table323_count (a : ∀ c, MMIndex 3 2 3 c) :
    maskCount 3 2 3 table323 a % 2 = if MMCompatible a then 1 else 0 := by
  decide +revert

/-- **`R(⟨3,2,3⟩) ≤ 15` in characteristic two.**  A `3 × 2` matrix can be multiplied by a
`2 × 3` matrix with fifteen noncommutative multiplications over any commutative ring in which
`2 = 0`.  This is the upper half of the count Hopcroft and Kerr report (p. 35) as necessary and
sufficient for `(3 × 2) · (2 × 3)`. -/
theorem rankLE_three_two_three {K : Type u} [CommRing K] (h2 : (2 : K) = 0) :
    RankLE 15 (matrixMultiplication (K := K) 3 2 3) := by
  simpa using rankLE_of_odd_count h2 table323 table323_count

/-- The `⟨3,2,3⟩` bound over the two-element field. -/
theorem rankLE_three_two_three_zmod :
    RankLE 15 (matrixMultiplication (K := ZMod 2) 3 2 3) :=
  rankLE_three_two_three (by decide)

/-- Cyclic rotation of the `⟨3,2,3⟩` certificate: `R(⟨3,3,2⟩) ≤ 15` in characteristic two. -/
theorem rankLE_three_three_two {K : Type u} [CommRing K] (h2 : (2 : K) = 0) :
    RankLE 15 (matrixMultiplication (K := K) 3 3 2) :=
  (rankLE_three_two_three h2).matrixMultiplication_cycle

/-- Cyclic rotation of the `⟨3,2,3⟩` certificate: `R(⟨2,3,3⟩) ≤ 15` in characteristic two. -/
theorem rankLE_two_three_three {K : Type u} [CommRing K] (h2 : (2 : K) = 0) :
    RankLE 15 (matrixMultiplication (K := K) 2 3 3) :=
  (rankLE_three_three_two h2).matrixMultiplication_cycle

/-! ## `⟨3,3,3⟩` in twenty-three multiplications -/

/-- A twenty-three-term `GF(2)` decomposition of `⟨3,3,3⟩`, found by a local flip-graph search.

Each triple `(u, v, w)` encodes one rank-one term by nine-bit masks: bit `3i + j` of `u` is the
left entry `(i,j)`, bit `3j + k` of `v` is the right entry `(j,k)`, and bit `3k + i` of `w` is
the output entry `(i,k)`. -/
def table333 : List (ℕ × ℕ × ℕ) :=
  [(388, 235, 55), (455, 292, 65), (260, 365, 54), (341, 290, 503),
   (504, 1, 130), (389, 5, 360), (237, 257, 367), (448, 6, 455),
   (384, 198, 7), (504, 7, 495), (146, 276, 8), (144, 63, 219),
   (288, 390, 16), (4, 390, 63), (325, 5, 432), (288, 65, 2),
   (278, 300, 217), (365, 262, 511), (144, 54, 195), (469, 293, 438),
   (390, 40, 216), (128, 221, 48), (219, 260, 144)]

/-- The `⟨3,3,3⟩` table has Laderman's length. -/
@[simp] theorem table333_length : table333.length = 23 := by simp [table333]

-- The kernel evaluates the `9 · 9 · 9 = 729` coordinates of the table below.
set_option maxRecDepth 100000 in
/-- At every basis index, an odd number of rows of the `⟨3,3,3⟩` table cover that index exactly
on the support of `⟨3,3,3⟩`.

Proof sketch: a closed decidable statement over the finite index type
`∀ c, MMIndex 3 3 3 c`, evaluated by the kernel at all `729` basis indices in `ℕ`. -/
theorem table333_count (a : ∀ c, MMIndex 3 3 3 c) :
    maskCount 3 3 3 table333 a % 2 = if MMCompatible a then 1 else 0 := by
  decide +revert

/-- **`R(⟨3,3,3⟩) ≤ 23` in characteristic two.**  Two `3 × 3` matrices can be multiplied with
twenty-three noncommutative multiplications over any commutative ring in which `2 = 0`.  This
matches Laderman's classical count and AlphaTensor's `GF(2)` count for `⟨3,3,3⟩`; the certificate
itself is the search output verified above, not Laderman's algorithm. -/
theorem rankLE_three_three_three {K : Type u} [CommRing K] (h2 : (2 : K) = 0) :
    RankLE 23 (matrixMultiplication (K := K) 3 3 3) := by
  simpa using rankLE_of_odd_count h2 table333 table333_count

/-- The `⟨3,3,3⟩` bound over the two-element field. -/
theorem rankLE_three_three_three_zmod :
    RankLE 23 (matrixMultiplication (K := ZMod 2) 3 3 3) :=
  rankLE_three_three_three (by decide)

/-- Squaring the `⟨3,3,3⟩` certificate: `R(⟨9,9,9⟩) ≤ 529` in characteristic two.  Recorded as a
small exercise of the product law; the exponent it gives is weaker than Strassen's. -/
theorem rankLE_nine {K : Type u} [CommRing K] (h2 : (2 : K) = 0) :
    RankLE 529 (matrixMultiplication (K := K) 9 9 9) := by
  simpa using (rankLE_three_three_three h2).matrixMultiplication_mul
    (rankLE_three_three_three h2)

end AlgebraicComplexity.Examples.DiscoveredDecompositions


