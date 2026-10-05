/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication
import Mathlib.LinearAlgebra.Vandermonde

/-!
# Partial matrix multiplication and Schönhage's compression step

This module holds the *ring-level* half of Arnold Schönhage, *Partial and Total Matrix
Multiplication*, SIAM Journal on Computing **10**(3), 434–455 (1981): the tensor of partial matrix
multiplication over arbitrary finite index types, its coordinate description and its variable
counts, and the compression certificate of §4.2 that carries a partial tensor onto a *total*
rectangular one.  The asymptotic half — Kronecker powers, the filling lemma at a multiplicity type
and the `τ`-theorem itself — lives downstream in
`AlgebraicComplexity/MatrixMultiplication/PartialAsymptoticSum.lean`, which is where the
border-rank, interpolation and word-type machinery is first needed.

Splitting the two halves keeps this module's import surface at the plain
matrix-multiplication/coordinate layer, and keeps either half elaborable on its own.

## Objects

* `PMMIndex`, `PMMSpace`, `pmmTerm`, `pmmSupport`: matrix-multiplication coordinates over
  arbitrary finite row, inner, and column index types.  The `Fin`-indexed `matrixMultiplication`
  of `AlgebraicComplexity/MatrixMultiplication.lean` is not usable for the argument: the `s`-fold
  Kronecker power of a pattern is naturally indexed by words `Fin s → κ`, and the
  multiplicity-type selection of Schönhage §4.1 and §4.4 lives on exactly those words.
* `partialMatrixMultiplication I J` (Schönhage §3): the trilinear tensor of the product `A · B`
  where the `κ × μ` left factor carries variables exactly in the positions `I`, the `μ × ν` right
  factor exactly in the positions `J`, all other positions are filled with zeros, and every entry
  of the product is computed.
* `pmmColumn`, `pmmRow` and `card_pmmSupport`: the column counts `k_j`, the row counts `n_j`, and
  Schönhage's equation (3.6), `f = ∑_j k_j n_j`.
* `PMMCompression`: a certificate for the sandwich `G A = U`, `B Q = V`, `W = G A B Q` of §4.2.

## Principal results

* `standardCoordinateEquiv_partialMatrixMultiplication`: the coordinate support formula, with
  `eq_partialMatrixMultiplication_of_coordinates` as the identification criterion for clients.
* `PMMCompression.map_legMap_partialMatrixMultiplication` and `PMMCompression.restricts` (§4.2):
  a compression certificate carries the partial tensor onto the *total* tensor `⟨kd, md, nd⟩` by
  legwise linear maps.  This step needs only a commutative ring.
* `exists_pmmCompression` (equation (4.11)): over an infinite field a compression certificate
  exists as soon as every selected inner index has at least `kd` variables in its column of the
  left factor and at least `nd` variables in its row of the right factor.

`[Infinite F]` is used exactly once, in `exists_pmmCompression`, to produce Vandermonde matrices
all of whose maximal minors are invertible (Schönhage's equation (4.11)).  Schönhage removes the
hypothesis afterwards through his Theorem 2.8 (`ω(F)` depends only on the characteristic of `F`);
that reduction is *not* formalized here, so the hypothesis stays explicit downstream.

## References

* A. Schönhage, *Partial and total matrix multiplication*, SIAM J. Comput. **10**(3) (1981),
  434--455.  §3, pp. 439--441: partial matrix multiplication, its coordinates and the variable
  count (3.6); §4.2, pp. 442--444: the compression step and the Vandermonde construction (4.11);
  Theorem 2.8, p. 438: the characteristic-only dependence of `ω(F)` that removes `[Infinite F]`.
-/

namespace AlgebraicComplexity

open Tensor

universe u v

section Index

variable (κ μ ν : Type v)

/-- Coordinate index types on the three legs of a matrix product whose row, inner, and column
indices are arbitrary finite types. -/
abbrev PMMIndex : Leg → Type v
  | .X => κ × μ
  | .Y => μ × ν
  | .Z => ν × κ

instance [Fintype κ] [Fintype μ] [Fintype ν] (c : Leg) : Fintype (PMMIndex κ μ ν c) := by
  cases c <;> infer_instance

instance [DecidableEq κ] [DecidableEq μ] [DecidableEq ν] (c : Leg) :
    DecidableEq (PMMIndex κ μ ν c) := by
  cases c <;> infer_instance

/-- The three coordinate spaces of a matrix product with general finite index types. -/
abbrev PMMSpace (K : Type u) [CommSemiring K] : Leg → Type (max u v) :=
  CoordinateSpace K (PMMIndex κ μ ν)

end Index

section Basic

variable {K : Type u} [CommSemiring K]
variable {κ μ ν : Type v}
variable [Fintype κ] [Fintype μ] [Fintype ν]
variable [DecidableEq κ] [DecidableEq μ] [DecidableEq ν]

/-- The pure summand `x_{ij} ⊗ y_{jk} ⊗ z_{ki}` selected by a summation triple. -/
def pmmTerm (t : κ × μ × ν) : ∀ c, PMMSpace κ μ ν K c
  | .X => Pi.single (t.1, t.2.1) 1
  | .Y => Pi.single (t.2.1, t.2.2) 1
  | .Z => Pi.single (t.2.2, t.1) 1

/-- The standard coordinate index family selected by a summation triple. -/
def pmmPoint (t : κ × μ × ν) : ∀ c, PMMIndex κ μ ν c :=
  ofLegs (t.1, t.2.1) (t.2.1, t.2.2) (t.2.2, t.1)

/-- Compatibility equations characterizing the support of a matrix-multiplication tensor with
general index types. -/
abbrev PMMCompatible (a : ∀ c, PMMIndex κ μ ν c) : Prop :=
  (a .X).2 = (a .Y).1 ∧ (a .Y).2 = (a .Z).1 ∧ (a .Z).2 = (a .X).1

/-- The summation triples of the partial product determined by the variable positions `I` of the
left factor and `J` of the right factor. -/
def pmmSupport (I : Finset (κ × μ)) (J : Finset (μ × ν)) : Finset (κ × μ × ν) :=
  Finset.univ.filter fun t ↦ (t.1, t.2.1) ∈ I ∧ (t.2.1, t.2.2) ∈ J

/-- A triple lies in the support exactly when both of its index pairs carry variables. -/
@[simp] theorem mem_pmmSupport {I : Finset (κ × μ)} {J : Finset (μ × ν)} {t : κ × μ × ν} :
    t ∈ pmmSupport I J ↔ (t.1, t.2.1) ∈ I ∧ (t.2.1, t.2.2) ∈ J := by
  simp [pmmSupport]

/-- **Partial matrix multiplication** in the sense of Schönhage (1981, §3): the trilinear tensor
computing the product `A · B` of a `κ × μ` matrix `A` whose variable positions form `I` with a
`μ × ν` matrix `B` whose variable positions form `J`.  All positions outside `I` and `J` are
filled with zeros, while every entry of the product is computed. -/
noncomputable def partialMatrixMultiplication
    (I : Finset (κ × μ)) (J : Finset (μ × ν)) : Tensor3 K (PMMSpace κ μ ν K) :=
  ∑ t ∈ pmmSupport I J, pure (K := K) (pmmTerm (K := K) t)

omit [Fintype κ] [Fintype μ] [Fintype ν] in
/-- The leg components of `pmmTerm` are standard basis vectors at the coordinates `pmmPoint`. -/
theorem pmmTerm_eq_single (t : κ × μ × ν) (c : Leg) :
    pmmTerm (K := K) t c = Pi.single (pmmPoint t c) 1 := by
  cases c <;> rfl

omit [Fintype κ] [Fintype μ] [Fintype ν] in
/-- One defining summand contributes `1` exactly at its own coordinate index family. -/
theorem prod_pmmTerm_apply (t : κ × μ × ν) (a : ∀ c, PMMIndex κ μ ν c) :
    (∏ c, pmmTerm (K := K) t c (a c)) = if a = pmmPoint t then 1 else 0 := by
  have hfactor (c : Leg) :
      pmmTerm (K := K) t c (a c) = if a c = pmmPoint t c then 1 else 0 := by
    rw [pmmTerm_eq_single]
    simp [Pi.single_apply]
  by_cases h : a = pmmPoint t
  · subst h
    simp [hfactor]
  · rw [if_neg h]
    obtain ⟨c, hc⟩ := Function.ne_iff.mp h
    exact Finset.prod_eq_zero (Finset.mem_univ c) (by simp [hfactor, hc])

/-- Coordinate support formula: the coefficient of the partial tensor at a standard basis index
is `1` exactly on the compatible triples whose left index lies in `I` and whose right index lies
in `J`, and `0` elsewhere. -/
theorem standardCoordinateEquiv_partialMatrixMultiplication
    (I : Finset (κ × μ)) (J : Finset (μ × ν)) (a : ∀ c, PMMIndex κ μ ν c) :
    standardCoordinateEquiv (K := K) (κ := PMMIndex κ μ ν)
        (partialMatrixMultiplication (K := K) I J) a =
      if PMMCompatible a ∧ (a .X) ∈ I ∧ (a .Y) ∈ J then 1 else 0 := by
  classical
  unfold partialMatrixMultiplication
  rw [map_sum]
  simp only [Finset.sum_apply, standardCoordinateEquiv_pure, prod_pmmTerm_apply]
  by_cases hcomp : PMMCompatible a
  · obtain ⟨h1, h2, h3⟩ := hcomp
    have hX : a .X = ((a .X).1, (a .X).2) := Prod.mk.eta.symm
    have hY : a .Y = ((a .X).2, (a .Y).2) := Prod.ext h1.symm rfl
    have hZ : a .Z = ((a .Y).2, (a .X).1) := Prod.ext h2.symm h3
    have hiff (t : κ × μ × ν) :
        (a = pmmPoint t) ↔ t = ((a .X).1, (a .X).2, (a .Y).2) := by
      constructor
      · intro h
        subst h
        rcases t with ⟨x, j, y⟩
        rfl
      · intro h
        subst h
        funext c
        cases c
        · exact hX
        · exact hY
        · exact hZ
    simp only [hiff]
    rw [Finset.sum_ite_eq' (pmmSupport I J) ((a .X).1, (a .X).2, (a .Y).2)
      (fun _ ↦ (1 : K))]
    have hmem : (((a .X).1, (a .X).2, (a .Y).2) ∈ pmmSupport I J) ↔
        ((a .X) ∈ I ∧ (a .Y) ∈ J) := by
      rw [mem_pmmSupport, ← hX, ← hY]
    by_cases hIJ : (a .X) ∈ I ∧ (a .Y) ∈ J
    · rw [if_pos (hmem.mpr hIJ), if_pos ⟨⟨h1, h2, h3⟩, hIJ⟩]
    · rw [if_neg (fun hx ↦ hIJ (hmem.mp hx)), if_neg (fun hx ↦ hIJ hx.2)]
  · have hzero (t : κ × μ × ν) : (if a = pmmPoint t then (1 : K) else 0) = 0 := by
      rw [if_neg]
      intro h
      subst h
      exact hcomp ⟨rfl, rfl, rfl⟩
    simp [hzero, hcomp]

/-- Identification criterion: a tensor whose coordinates follow the partial support formula is
the partial matrix-multiplication tensor.  Downstream clients use this to recognize a hand-built
partial tensor as an instance of `partialMatrixMultiplication`. -/
theorem eq_partialMatrixMultiplication_of_coordinates
    {T : Tensor3 K (PMMSpace κ μ ν K)} {I : Finset (κ × μ)} {J : Finset (μ × ν)}
    (h : ∀ a, standardCoordinateEquiv (K := K) (κ := PMMIndex κ μ ν) T a =
      if PMMCompatible a ∧ (a .X) ∈ I ∧ (a .Y) ∈ J then 1 else 0) :
    T = partialMatrixMultiplication (K := K) I J := by
  apply standardCoordinate_ext
  intro a
  rw [h a, standardCoordinateEquiv_partialMatrixMultiplication]

/-- The elementary expansion of the partial tensor gives the trivial rank bound: one
multiplication per triple of its support. -/
theorem partialMatrixMultiplication_rankLE (I : Finset (κ × μ)) (J : Finset (μ × ν)) :
    RankLE (pmmSupport I J).card (partialMatrixMultiplication (K := K) I J) := by
  simpa [partialMatrixMultiplication] using
    RankLE.finset_sum_pure (K := K) (V := PMMSpace κ μ ν K)
      (pmmSupport I J) (pmmTerm (K := K))

end Basic

section Counts

variable {α β : Type v} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

/-- The variable positions of the `j`-th column of a partially filled matrix. -/
def pmmColumn (I : Finset (α × β)) (j : β) : Finset α :=
  Finset.univ.filter fun x ↦ (x, j) ∈ I

/-- The variable positions of the `j`-th row of a partially filled matrix. -/
def pmmRow (J : Finset (β × α)) (j : β) : Finset α :=
  Finset.univ.filter fun y ↦ (j, y) ∈ J

omit [Fintype β] in
/-- Membership in the `j`-th column: `x` is listed exactly when `(x, j)` carries a variable. -/
@[simp] theorem mem_pmmColumn {I : Finset (α × β)} {j : β} {x : α} :
    x ∈ pmmColumn I j ↔ (x, j) ∈ I := by simp [pmmColumn]

omit [Fintype β] in
/-- Membership in the `j`-th row: `y` is listed exactly when `(j, y)` carries a variable. -/
@[simp] theorem mem_pmmRow {J : Finset (β × α)} {j : β} {y : α} :
    y ∈ pmmRow J j ↔ (j, y) ∈ J := by simp [pmmRow]

variable {κ μ ν : Type v} [Fintype κ] [Fintype μ] [Fintype ν]
variable [DecidableEq κ] [DecidableEq μ] [DecidableEq ν]

/-- Schönhage's count (1981, equation (3.6)): the number of ones in a partial
matrix-multiplication tensor is `∑_j k_j n_j`, where `k_j` counts the variables in column `j` of
the left factor and `n_j` counts the variables in row `j` of the right factor.  It is the number
of scalar multiplications used by the straightforward algorithm. -/
theorem card_pmmSupport (I : Finset (κ × μ)) (J : Finset (μ × ν)) :
    (pmmSupport I J).card = ∑ j : μ, (pmmColumn I j).card * (pmmRow J j).card := by
  classical
  have hcard : (pmmSupport I J).card =
      ∑ x : κ, ∑ j : μ, ∑ y : ν, (if (x, j) ∈ I ∧ (j, y) ∈ J then 1 else 0) := by
    rw [pmmSupport, Finset.card_filter, Fintype.sum_prod_type]
    exact Finset.sum_congr rfl fun x _ ↦ Fintype.sum_prod_type _
  rw [hcard, Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  have hsplit : ∀ (x : κ) (y : ν),
      (if (x, j) ∈ I ∧ (j, y) ∈ J then (1 : ℕ) else 0) =
        (if (x, j) ∈ I then 1 else 0) * (if (j, y) ∈ J then 1 else 0) := by
    intro x y
    by_cases h1 : (x, j) ∈ I <;> by_cases h2 : (j, y) ∈ J <;> simp [h1, h2]
  simp only [hsplit]
  rw [← Finset.sum_mul_sum, pmmColumn, pmmRow, Finset.card_filter, Finset.card_filter]

end Counts

section Compression

variable {F : Type u} [CommRing F]
variable {κ μ ν : Type v}

/-- **Compression certificate** for Schönhage's passage from a partial to a total matrix
multiplication (1981, §4.2).

`select` picks `md` inner indices.  `left` is the scalar `kd × κ` matrix `G` and `right` the
scalar `ν × nd` matrix `Q` of the sandwich `GA = U`, `BQ = V`, `W = GABQ`.  `leftSection` and
`rightSection` are the corresponding local inverses `H_j` and `R_j`: they reconstruct the entries
of the `j`-th column of `A` and of the `j`-th row of `B` from the compressed variables.  The two
vanishing conditions say that the reconstruction only ever writes into positions that actually
carry a variable, so the reconstructed matrices really are of the prescribed partial shape; the
two inverse conditions say that compressing a reconstruction returns the original compressed
variable. -/
structure PMMCompression (F : Type u) [CommRing F] {κ μ ν : Type v}
    [Fintype κ] [Fintype ν]
    (I : Finset (κ × μ)) (J : Finset (μ × ν)) (kd md nd : ℕ) where
  /-- The `md` selected inner indices. -/
  select : Fin md → μ
  /-- Distinct inner indices are selected. -/
  select_injective : Function.Injective select
  /-- The left compression matrix `G`. -/
  left : Fin kd → κ → F
  /-- The right compression matrix `Q`. -/
  right : ν → Fin nd → F
  /-- Reconstruction of the selected columns of the left factor. -/
  leftSection : Fin md → Fin kd → κ → F
  /-- Reconstruction of the selected rows of the right factor. -/
  rightSection : Fin md → Fin nd → ν → F
  /-- The column reconstruction is supported on variable positions of the left factor. -/
  leftSection_eq_zero : ∀ i q x, (x, select i) ∉ I → leftSection i q x = 0
  /-- The row reconstruction is supported on variable positions of the right factor. -/
  rightSection_eq_zero : ∀ i r y, (select i, y) ∉ J → rightSection i r y = 0
  /-- Reconstructing and then compressing is the identity on the left. -/
  leftSection_left : ∀ i q q', ∑ x, leftSection i q x * left q' x = if q = q' then 1 else 0
  /-- Reconstructing and then compressing is the identity on the right. -/
  rightSection_right : ∀ i r r', ∑ y, rightSection i r y * right y r' = if r = r' then 1 else 0

namespace PMMCompression

variable [Fintype κ] [Fintype μ] [Fintype ν]
variable [DecidableEq κ] [DecidableEq μ] [DecidableEq ν]
variable {I : Finset (κ × μ)} {J : Finset (μ × ν)} {kd md nd : ℕ}

/-- Value of a matrix map on a standard basis vector. -/
private theorem mulVecLin_single {n m : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix m n F) (j : n) (i : m) :
    M.mulVecLin (Pi.single j 1) i = M i j := by
  simp

/-- Matrix of the `X`-leg compression map: reconstruct the left factor from the compressed
variables. -/
def matrixX (C : PMMCompression F I J kd md nd) : Matrix (Fin kd × Fin md) (κ × μ) F :=
  Matrix.of fun p u ↦ if u.2 = C.select p.2 then C.leftSection p.2 p.1 u.1 else 0

/-- Matrix of the `Y`-leg compression map: reconstruct the right factor from the compressed
variables. -/
def matrixY (C : PMMCompression F I J kd md nd) : Matrix (Fin md × Fin nd) (μ × ν) F :=
  Matrix.of fun p u ↦ if u.1 = C.select p.1 then C.rightSection p.1 p.2 u.2 else 0

/-- Matrix of the `Z`-leg compression map: read the compressed product `W = G D Q`. -/
def matrixZ (C : PMMCompression F I J kd md nd) : Matrix (Fin nd × Fin kd) (ν × κ) F :=
  Matrix.of fun p u ↦ C.left p.2 u.2 * C.right u.1 p.1

/-- The three legwise linear maps realizing the compression. -/
noncomputable def legMap (C : PMMCompression F I J kd md nd) :
    ∀ c, PMMSpace κ μ ν F c →ₗ[F] MMSpace F kd md nd c :=
  ofLegs C.matrixX.mulVecLin C.matrixY.mulVecLin C.matrixZ.mulVecLin

/-- Value of the `X`-leg compression map on a defining basis vector. -/
theorem legMap_pmmTerm_X (C : PMMCompression F I J kd md nd)
    (t : κ × μ × ν) (p : Fin kd × Fin md) :
    C.legMap .X (pmmTerm (K := F) t .X) p =
      if t.2.1 = C.select p.2 then C.leftSection p.2 p.1 t.1 else 0 := by
  show C.matrixX.mulVecLin (Pi.single (t.1, t.2.1) 1) p = _
  rw [mulVecLin_single]
  rfl

/-- Value of the `Y`-leg compression map on a defining basis vector. -/
theorem legMap_pmmTerm_Y (C : PMMCompression F I J kd md nd)
    (t : κ × μ × ν) (p : Fin md × Fin nd) :
    C.legMap .Y (pmmTerm (K := F) t .Y) p =
      if t.2.1 = C.select p.1 then C.rightSection p.1 p.2 t.2.2 else 0 := by
  show C.matrixY.mulVecLin (Pi.single (t.2.1, t.2.2) 1) p = _
  rw [mulVecLin_single]
  rfl

/-- Value of the `Z`-leg compression map on a defining basis vector. -/
theorem legMap_pmmTerm_Z (C : PMMCompression F I J kd md nd)
    (t : κ × μ × ν) (p : Fin nd × Fin kd) :
    C.legMap .Z (pmmTerm (K := F) t .Z) p =
      C.left p.2 t.1 * C.right t.2.2 p.1 := by
  show C.matrixZ.mulVecLin (Pi.single (t.2.2, t.1) 1) p = _
  rw [mulVecLin_single]
  rfl

/-- **Schönhage's compression step** (1981, §4.2).  A compression certificate carries the partial
matrix-multiplication tensor onto the *total* `⟨kd, md, nd⟩` matrix-multiplication tensor by
legwise linear maps.

Proof sketch: evaluate both sides in standard coordinates.  A basis coordinate of the image is a
sum over the support triples `(x, j, y)` of `leftSection` times `rightSection` times the two
compression matrices.  Both reconstruction factors force the inner index `j` to be the selected
index of their own leg, so injectivity of `select` kills every coordinate whose two inner indices
disagree — exactly the first matrix-multiplication compatibility equation.  When they agree, the
support restriction may be dropped, because the reconstructions vanish outside the variable
positions; the remaining double sum factors into the two inverse identities, producing the other
two compatibility equations. -/
theorem map_legMap_partialMatrixMultiplication (C : PMMCompression F I J kd md nd) :
    Tensor.map C.legMap (partialMatrixMultiplication (K := F) I J) =
      matrixMultiplication (K := F) kd md nd := by
  classical
  apply standardCoordinate_ext
  intro p
  rw [standardCoordinateEquiv_matrixMultiplication]
  have hcoord : standardCoordinateEquiv (K := F) (κ := MMIndex kd md nd)
      (Tensor.map C.legMap (partialMatrixMultiplication (K := F) I J)) p =
      ∑ t ∈ pmmSupport I J,
        (if t.2.1 = C.select (p .X).2 then C.leftSection (p .X).2 (p .X).1 t.1 else 0) *
          (if t.2.1 = C.select (p .Y).1 then C.rightSection (p .Y).1 (p .Y).2 t.2.2 else 0) *
          (C.left (p .Z).2 t.1 * C.right t.2.2 (p .Z).1) := by
    unfold partialMatrixMultiplication
    simp only [map_sum, Finset.sum_apply, Tensor.map_pure, standardCoordinateEquiv_pure]
    refine Finset.sum_congr rfl fun t _ ↦ ?_
    rw [prod_leg, C.legMap_pmmTerm_X, C.legMap_pmmTerm_Y, C.legMap_pmmTerm_Z]
  rw [hcoord]
  by_cases hi : (p .X).2 = (p .Y).1
  · have hterm : ∀ t : κ × μ × ν,
        (if t.2.1 = C.select (p .X).2 then C.leftSection (p .X).2 (p .X).1 t.1 else 0) *
            (if t.2.1 = C.select (p .Y).1 then C.rightSection (p .Y).1 (p .Y).2 t.2.2 else 0) *
            (C.left (p .Z).2 t.1 * C.right t.2.2 (p .Z).1) =
          if t.2.1 = C.select (p .X).2 then
            (C.leftSection (p .X).2 (p .X).1 t.1 * C.left (p .Z).2 t.1) *
              (C.rightSection (p .Y).1 (p .Y).2 t.2.2 * C.right t.2.2 (p .Z).1)
          else 0 := by
      intro t
      rw [← hi]
      by_cases hc : t.2.1 = C.select (p .X).2
      · rw [if_pos hc, if_pos hc, if_pos hc]; ring
      · rw [if_neg hc, if_neg hc, if_neg hc]; ring
    simp only [hterm]
    have hzero : ∀ t ∈ (Finset.univ : Finset (κ × μ × ν)), t ∉ pmmSupport I J →
        (if t.2.1 = C.select (p .X).2 then
          (C.leftSection (p .X).2 (p .X).1 t.1 * C.left (p .Z).2 t.1) *
            (C.rightSection (p .Y).1 (p .Y).2 t.2.2 * C.right t.2.2 (p .Z).1)
        else 0) = 0 := by
      intro t _ hnot
      by_cases hc : t.2.1 = C.select (p .X).2
      · rw [if_pos hc]
        rw [mem_pmmSupport, not_and_or] at hnot
        rcases hnot with hI | hJ
        · rw [C.leftSection_eq_zero (p .X).2 (p .X).1 t.1 (by rw [← hc]; exact hI)]
          ring
        · rw [C.rightSection_eq_zero (p .Y).1 (p .Y).2 t.2.2 (by rw [← hi, ← hc]; exact hJ)]
          ring
      · rw [if_neg hc]
    rw [Finset.sum_subset (Finset.subset_univ (pmmSupport I J)) hzero]
    have hexpand : ∑ t : κ × μ × ν,
        (if t.2.1 = C.select (p .X).2 then
          (C.leftSection (p .X).2 (p .X).1 t.1 * C.left (p .Z).2 t.1) *
            (C.rightSection (p .Y).1 (p .Y).2 t.2.2 * C.right t.2.2 (p .Z).1)
        else 0) =
        ∑ x : κ, ∑ y : ν,
          (C.leftSection (p .X).2 (p .X).1 x * C.left (p .Z).2 x) *
            (C.rightSection (p .Y).1 (p .Y).2 y * C.right y (p .Z).1) := by
      rw [Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun x _ ↦ ?_
      rw [Fintype.sum_prod_type, Finset.sum_eq_single (C.select (p .X).2)]
      · simp
      · intro j _ hj
        simp [hj]
      · intro h
        exact absurd (Finset.mem_univ _) h
    rw [hexpand, ← Finset.sum_mul_sum, C.leftSection_left, C.rightSection_right]
    have hcompat : MMCompatible p ↔ ((p .Y).2 = (p .Z).1 ∧ (p .Z).2 = (p .X).1) := by
      constructor
      · rintro ⟨-, h2, h3⟩
        exact ⟨h2, h3⟩
      · rintro ⟨h2, h3⟩
        exact ⟨hi, h2, h3⟩
    by_cases h2 : (p .Y).2 = (p .Z).1
    · by_cases h3 : (p .Z).2 = (p .X).1
      · rw [if_pos (show (p .X).1 = (p .Z).2 from h3.symm), if_pos h2,
          if_pos (show MMCompatible p from hcompat.mpr ⟨h2, h3⟩), one_mul]
      · rw [if_neg (show ¬((p .X).1 = (p .Z).2) from fun hx ↦ h3 hx.symm), if_pos h2,
          if_neg (show ¬MMCompatible p from fun hc ↦ h3 (hcompat.mp hc).2), zero_mul]
    · rw [if_neg h2, if_neg (show ¬MMCompatible p from fun hc ↦ h2 (hcompat.mp hc).1), mul_zero]
  · rw [if_neg (show ¬MMCompatible p from fun hc ↦ hi hc.1)]
    apply Finset.sum_eq_zero
    intro t _
    by_cases h1 : t.2.1 = C.select (p .X).2
    · have h2 : ¬ (t.2.1 = C.select (p .Y).1) := fun h2 ↦
        hi (C.select_injective (h1.symm.trans h2))
      rw [if_neg h2, mul_zero, zero_mul]
    · rw [if_neg h1, zero_mul, zero_mul]

/-- Relation-level form of the compression step: the total `⟨kd, md, nd⟩` tensor is a restriction
of the partial tensor.  The source of the restriction is the partial tensor. -/
theorem restricts (C : PMMCompression F I J kd md nd) :
    Restricts (partialMatrixMultiplication (K := F) I J)
      (matrixMultiplication (K := F) kd md nd) :=
  ⟨C.legMap, C.map_legMap_partialMatrixMultiplication⟩

end PMMCompression

end Compression

section GenericCompression

variable (F : Type u) [Field F] [Infinite F]

omit [Field F] in
/-- Every finite type embeds into an infinite field. -/
private theorem exists_injective_to_field (α : Type v) [Fintype α] :
    ∃ f : α → F, Function.Injective f := by
  classical
  refine ⟨fun x ↦ Infinite.natEmbedding F ((Fintype.equivFin α x : Fin (Fintype.card α)) : ℕ),
    fun a b hab ↦ ?_⟩
  exact (Fintype.equivFin α).injective
    (Fin.val_injective ((Infinite.natEmbedding F).injective hab))

variable {κ μ ν : Type v}
variable [Fintype κ] [Fintype μ] [Fintype ν]
variable [DecidableEq κ] [DecidableEq μ] [DecidableEq ν]

omit [Fintype μ] in
/-- **Existence of Schönhage's generic compression** (1981, equation (4.11)).  Over an *infinite*
field, choose distinct field elements `α_x` and build the Vandermonde matrix `G_{q,x} = α_x^q`;
every `kd × kd` minor of `G` is a Vandermonde determinant in distinct nodes, hence invertible.
Consequently every selected inner index whose column of the left factor carries at least `kd`
variables and whose row of the right factor carries at least `nd` variables can be compressed.

This is the only step of the partial `τ`-theorem that needs the field to be infinite. -/
theorem exists_pmmCompression
    (I : Finset (κ × μ)) (J : Finset (μ × ν)) {kd md nd : ℕ}
    (sel : Fin md → μ) (hsel : Function.Injective sel)
    (hI : ∀ i, kd ≤ (pmmColumn I (sel i)).card)
    (hJ : ∀ i, nd ≤ (pmmRow J (sel i)).card) :
    Nonempty (PMMCompression F I J kd md nd) := by
  classical
  obtain ⟨α, hα⟩ := exists_injective_to_field F κ
  obtain ⟨β, hβ⟩ := exists_injective_to_field F ν
  have hAexists : ∀ i : Fin md,
      ∃ f : Fin kd → κ, Function.Injective f ∧ ∀ q, (f q, sel i) ∈ I := by
    intro i
    obtain ⟨A, hAsub, hAcard⟩ := Finset.exists_subset_card_eq (hI i)
    refine ⟨fun q ↦ (((Finset.equivFinOfCardEq hAcard).symm q : ↥A) : κ), ?_, ?_⟩
    · intro q q' hq
      exact (Finset.equivFinOfCardEq hAcard).symm.injective (Subtype.ext hq)
    · intro q
      simpa using hAsub ((Finset.equivFinOfCardEq hAcard).symm q).2
  have hBexists : ∀ i : Fin md,
      ∃ f : Fin nd → ν, Function.Injective f ∧ ∀ r, (sel i, f r) ∈ J := by
    intro i
    obtain ⟨B, hBsub, hBcard⟩ := Finset.exists_subset_card_eq (hJ i)
    refine ⟨fun r ↦ (((Finset.equivFinOfCardEq hBcard).symm r : ↥B) : ν), ?_, ?_⟩
    · intro r r' hr
      exact (Finset.equivFinOfCardEq hBcard).symm.injective (Subtype.ext hr)
    · intro r
      simpa using hBsub ((Finset.equivFinOfCardEq hBcard).symm r).2
  choose a hainj hamem using hAexists
  choose b hbinj hbmem using hBexists
  let Gm : Fin md → Matrix (Fin kd) (Fin kd) F :=
    fun i ↦ Matrix.of fun s s' ↦ α (a i s') ^ (s : ℕ)
  let Qm : Fin md → Matrix (Fin nd) (Fin nd) F :=
    fun i ↦ Matrix.of fun s s' ↦ β (b i s) ^ (s' : ℕ)
  have hGm_apply : ∀ i s s', Gm i s s' = α (a i s') ^ (s : ℕ) := fun _ _ _ ↦ rfl
  have hQm_apply : ∀ i s s', Qm i s s' = β (b i s) ^ (s' : ℕ) := fun _ _ _ ↦ rfl
  have hGdet : ∀ i, IsUnit (Gm i).det := by
    intro i
    rw [isUnit_iff_ne_zero]
    have hEq : Gm i = (Matrix.vandermonde fun s ↦ α (a i s)).transpose := rfl
    rw [hEq, Matrix.det_transpose]
    exact Matrix.det_vandermonde_ne_zero_iff.mpr fun s s' hs ↦ hainj i (hα hs)
  have hQdet : ∀ i, IsUnit (Qm i).det := by
    intro i
    rw [isUnit_iff_ne_zero]
    have hEq : Qm i = Matrix.vandermonde fun s ↦ β (b i s) := rfl
    rw [hEq]
    exact Matrix.det_vandermonde_ne_zero_iff.mpr fun s s' hs ↦ hbinj i (hβ hs)
  refine ⟨{
    select := sel
    select_injective := hsel
    left := fun q x ↦ α x ^ (q : ℕ)
    right := fun y r ↦ β y ^ (r : ℕ)
    leftSection := fun i q x ↦ ∑ q₁, (if x = a i q₁ then (Gm i)⁻¹ q₁ q else 0)
    rightSection := fun i r y ↦ ∑ r₁, (if y = b i r₁ then (Qm i)⁻¹ r r₁ else 0)
    leftSection_eq_zero := ?_
    rightSection_eq_zero := ?_
    leftSection_left := ?_
    rightSection_right := ?_ }⟩
  · intro i q x hx
    refine Finset.sum_eq_zero fun q₁ _ ↦ ?_
    rw [if_neg]
    intro hq
    exact hx (by rw [hq]; exact hamem i q₁)
  · intro i r y hy
    refine Finset.sum_eq_zero fun r₁ _ ↦ ?_
    rw [if_neg]
    intro hr
    exact hy (by rw [hr]; exact hbmem i r₁)
  · intro i q q'
    have hstep : ∀ x : κ,
        (∑ q₁, (if x = a i q₁ then (Gm i)⁻¹ q₁ q else 0)) * (α x ^ (q' : ℕ)) =
          ∑ q₁, (if x = a i q₁ then (Gm i)⁻¹ q₁ q * (α x ^ (q' : ℕ)) else 0) := by
      intro x
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun q₁ _ ↦ by split <;> simp
    simp only [hstep]
    rw [Finset.sum_comm]
    have hinner : ∀ q₁ : Fin kd,
        (∑ x : κ, if x = a i q₁ then (Gm i)⁻¹ q₁ q * (α x ^ (q' : ℕ)) else 0) =
          (Gm i) q' q₁ * (Gm i)⁻¹ q₁ q := by
      intro q₁
      rw [Finset.sum_ite_eq' Finset.univ (a i q₁)
        (fun x ↦ (Gm i)⁻¹ q₁ q * (α x ^ (q' : ℕ))), if_pos (Finset.mem_univ _), hGm_apply]
      ring
    simp only [hinner]
    rw [← Matrix.mul_apply, Matrix.mul_nonsing_inv _ (hGdet i), Matrix.one_apply]
    by_cases hqq : q = q'
    · simp [hqq]
    · simp [hqq, Ne.symm hqq]
  · intro i r r'
    have hstep : ∀ y : ν,
        (∑ r₁, (if y = b i r₁ then (Qm i)⁻¹ r r₁ else 0)) * (β y ^ (r' : ℕ)) =
          ∑ r₁, (if y = b i r₁ then (Qm i)⁻¹ r r₁ * (β y ^ (r' : ℕ)) else 0) := by
      intro y
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun r₁ _ ↦ by split <;> simp
    simp only [hstep]
    rw [Finset.sum_comm]
    have hinner : ∀ r₁ : Fin nd,
        (∑ y : ν, if y = b i r₁ then (Qm i)⁻¹ r r₁ * (β y ^ (r' : ℕ)) else 0) =
          (Qm i)⁻¹ r r₁ * (Qm i) r₁ r' := by
      intro r₁
      rw [Finset.sum_ite_eq' Finset.univ (b i r₁)
        (fun y ↦ (Qm i)⁻¹ r r₁ * (β y ^ (r' : ℕ))), if_pos (Finset.mem_univ _), hQm_apply]
    simp only [hinner]
    rw [← Matrix.mul_apply, Matrix.nonsing_inv_mul _ (hQdet i), Matrix.one_apply]

end GenericCompression

end AlgebraicComplexity
