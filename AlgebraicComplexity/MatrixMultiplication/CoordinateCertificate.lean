/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication

/-!
# The house harness for coordinate rank certificates

Every explicit matrix-multiplication algorithm in `AlgebraicComplexity/Examples/` is shipped the
same way: a finite table of coordinate vectors, a kernel-checked evaluation of the resulting
coefficient table over `ℤ` (or `ℕ`), and a scalar-cast bridge transporting that one finite check
to an arbitrary commutative ring.  This module owns that pattern once, so that a client file
contains only its table, one `decide`, and one application of the corresponding one-shot lemma.

## Contents

* `Tensor.standardCoordinateEquiv_list_sum_pure` — the coordinate of a list sum of pure tensors
  is the list sum of the leg-component products.  Stated for arbitrary standard coordinate
  spaces; it is the only tensor-layer fact the harness needs, and is a candidate for migration
  into `Tensor/Coordinates.lean` in a coordinated refactor.
* `MMCertificate.coefficient` — the coordinate of a list of rank-one terms at a basis index.
* `MMCertificate.decomposition_of_coefficient`, `MMCertificate.rankLE_of_coefficient` — the
  one-shot lemmas: a coefficient table equal to the support indicator of `⟨m,n,p⟩` *is* a
  decomposition, hence a rank certificate.
* `MMCertificate.castTerms`, `MMCertificate.coefficient_castTerms` — the `Int`-table layer: a
  single integer table is cast entrywise, and its coefficient table casts with it.
* `MMCertificate.decomposition_of_intCoefficient`, `MMCertificate.rankLE_of_intCoefficient` —
  the one-shot for the `Int`-certificate-plus-cast pattern of `DESIGN.md`.
* `MMCertificate.rankLE_of_natCoefficient_mod_two` — the characteristic-two one-shot for
  `0/1` tables verified by a parity count in `ℕ`.
* `mmPoint` and `mmTermOfTriple_eq_single` — the defining summand of a triple written as a family
  of standard basis vectors.  Clients that expand `mmTermOfTriple` by hand should rewrite with
  this instead.

## Layer placement

A leaf of the matrix-multiplication theory layer: it imports only
`AlgebraicComplexity/MatrixMultiplication.lean` and is imported by the certificate clients.  It
contributes no named construction and no numerical bound.
-/

namespace AlgebraicComplexity

open Tensor

universe u w

/-- The coordinate of a finite sum of pure coordinate tensors at a standard basis index is the
sum of the leg-component products of the individual terms. -/
theorem Tensor.standardCoordinateEquiv_list_sum_pure {K : Type u} [CommSemiring K]
    {κ : Leg → Type w} [∀ i, Finite (κ i)]
    (terms : List (∀ i, CoordinateSpace K κ i)) (a : ∀ i, κ i) :
    standardCoordinateEquiv (K := K) (κ := κ) ((terms.map (pure (K := K))).sum) a =
      (terms.map fun x ↦ ∏ i, x i (a i)).sum := by
  induction terms with
  | nil => simp
  | cons x terms ih => simp [ih]

/-! ## Basis-vector spelling of the defining summands -/

variable {m n p : ℕ}

/-- The three basis indices selected by a summation triple `(i, j, k)`, bundled as one coordinate
family: `(i, j)` on the `X` leg, `(j, k)` on the `Y` leg, and `(k, i)` on the `Z` leg. -/
def mmPoint (t : MMTriple m n p) : ∀ c, MMIndex m n p c :=
  ofLegs (t.1, t.2.1) (t.2.1, t.2.2) (t.2.2, t.1)

/-- The standard `⟨m,n,p⟩` summand of a triple is the pure basis tensor at its index family.
This is the one rewrite that turns the defining term list into `Pi.single`s, which is what every
coordinate computation on a matrix-multiplication tensor actually needs. -/
theorem mmTermOfTriple_eq_single {K : Type u} [CommSemiring K] (t : MMTriple m n p) :
    mmTermOfTriple (K := K) m n p t = fun c ↦ Pi.single (mmPoint t c) 1 := by
  funext c
  cases c <;> rfl

namespace MMCertificate

/-- The coordinate of a list of rank-one terms at a standard basis index of the three legs. -/
def coefficient (R : Type u) [CommSemiring R] (L : List (∀ c, MMSpace R m n p c))
    (a : ∀ c, MMIndex m n p c) : R :=
  (L.map fun x ↦ ∏ c, x c (a c)).sum

/-- The coordinate of the tensor sum of a term list is its coefficient table. -/
@[simp] theorem standardCoordinateEquiv_list_sum_pure_eq (K : Type u) [CommSemiring K]
    (L : List (∀ c, MMSpace K m n p c)) (a : ∀ c, MMIndex m n p c) :
    standardCoordinateEquiv (K := K) (κ := MMIndex m n p) ((L.map (pure (K := K))).sum) a =
      coefficient K L a :=
  Tensor.standardCoordinateEquiv_list_sum_pure (κ := MMIndex m n p) L a

/-- **The one-shot decomposition lemma.**  A list of rank-one terms whose coefficient table is
the support indicator of `⟨m,n,p⟩` sums to `⟨m,n,p⟩`. -/
theorem decomposition_of_coefficient {K : Type u} [CommSemiring K]
    (L : List (∀ c, MMSpace K m n p c))
    (h : ∀ a, coefficient K L a = if MMCompatible a then 1 else 0) :
    matrixMultiplication (K := K) m n p = (L.map (pure (K := K))).sum := by
  refine standardCoordinate_ext fun a ↦ ?_
  rw [standardCoordinateEquiv_matrixMultiplication, standardCoordinateEquiv_list_sum_pure_eq,
    h a]

/-- **The one-shot rank-certificate lemma.**  A list of at most `r` rank-one terms whose
coefficient table is the support indicator of `⟨m,n,p⟩` certifies `R(⟨m,n,p⟩) ≤ r`. -/
theorem rankLE_of_coefficient {K : Type u} [CommSemiring K] {r : ℕ}
    (L : List (∀ c, MMSpace K m n p c)) (hlen : L.length ≤ r)
    (h : ∀ a, coefficient K L a = if MMCompatible a then 1 else 0) :
    RankLE r (matrixMultiplication (K := K) m n p) := by
  rw [decomposition_of_coefficient L h]
  exact (RankLE.list_sum_pure (K := K) L).mono hlen

/-! ## The integer-table layer -/

/-- Read an integer term table over an arbitrary commutative ring, entry by entry. -/
def castTerms (K : Type u) [CommRing K] (L : List (∀ c, MMSpace ℤ m n p c)) :
    List (∀ c, MMSpace K m n p c) :=
  L.map fun x c a ↦ ((x c a : ℤ) : K)

@[simp] theorem castTerms_length (K : Type u) [CommRing K]
    (L : List (∀ c, MMSpace ℤ m n p c)) : (castTerms K L).length = L.length := by
  simp [castTerms]

/-- Casting a list sum of integers termwise into a commutative ring. -/
private theorem cast_list_sum_map {K : Type u} [CommRing K] {α : Type*}
    (l : List α) (f : α → ℤ) :
    (((l.map f).sum : ℤ) : K) = (l.map fun x ↦ ((f x : ℤ) : K)).sum := by
  induction l with
  | nil => simp
  | cons a t ih => simp [ih]

/-- The coefficient table of a cast integer term table is the cast of the integer coefficient
table: the whole finite verification stays inside `ℤ`. -/
theorem coefficient_castTerms (K : Type u) [CommRing K]
    (L : List (∀ c, MMSpace ℤ m n p c)) (a : ∀ c, MMIndex m n p c) :
    coefficient K (castTerms K L) a = ((coefficient ℤ L a : ℤ) : K) := by
  simp only [coefficient]
  rw [cast_list_sum_map (K := K), castTerms, List.map_map]
  exact congrArg List.sum (List.map_congr_left fun x _ ↦ by simp [prod_leg])

/-- **The `Int`-certificate one-shot, decomposition form.** -/
theorem decomposition_of_intCoefficient {K : Type u} [CommRing K]
    (L : List (∀ c, MMSpace ℤ m n p c))
    (h : ∀ a, coefficient ℤ L a = if MMCompatible a then 1 else 0) :
    matrixMultiplication (K := K) m n p =
      ((castTerms K L).map (pure (K := K))).sum := by
  refine decomposition_of_coefficient _ fun a ↦ ?_
  rw [coefficient_castTerms, h a]
  split <;> simp

/-- **The `Int`-certificate one-shot.**  One integer table, checked once over `ℤ`, certifies
`R(⟨m,n,p⟩) ≤ r` over every commutative ring. -/
theorem rankLE_of_intCoefficient {K : Type u} [CommRing K] {r : ℕ}
    (L : List (∀ c, MMSpace ℤ m n p c)) (hlen : L.length ≤ r)
    (h : ∀ a, coefficient ℤ L a = if MMCompatible a then 1 else 0) :
    RankLE r (matrixMultiplication (K := K) m n p) := by
  refine rankLE_of_coefficient (castTerms K L) (by simpa using hlen) fun a ↦ ?_
  rw [coefficient_castTerms, h a]
  split <;> simp

/-! ## The characteristic-two parity layer -/

/-- **The characteristic-two one-shot.**  If the coefficient table of a term list is the image
of a natural-number count `N`, and `N` is odd exactly on the support of `⟨m,n,p⟩`, then the
terms decompose `⟨m,n,p⟩` over any commutative ring in which `2 = 0`. -/
theorem decomposition_of_natCoefficient_mod_two {K : Type u} [CommRing K] (h2 : (2 : K) = 0)
    (L : List (∀ c, MMSpace K m n p c)) (N : (∀ c, MMIndex m n p c) → ℕ)
    (hN : ∀ a, coefficient K L a = ((N a : ℕ) : K))
    (h : ∀ a, N a % 2 = if MMCompatible a then 1 else 0) :
    matrixMultiplication (K := K) m n p = (L.map (pure (K := K))).sum := by
  refine decomposition_of_coefficient L fun a ↦ ?_
  have hd : ((N a : ℕ) : K) = ((N a % 2 : ℕ) : K) := by
    conv_lhs => rw [← Nat.div_add_mod (N a) 2]
    push_cast
    rw [h2, zero_mul, zero_add]
  rw [hN a, hd, h a]
  split <;> simp

/-- Rank-certificate form of `decomposition_of_natCoefficient_mod_two`. -/
theorem rankLE_of_natCoefficient_mod_two {K : Type u} [CommRing K] (h2 : (2 : K) = 0) {r : ℕ}
    (L : List (∀ c, MMSpace K m n p c)) (hlen : L.length ≤ r)
    (N : (∀ c, MMIndex m n p c) → ℕ)
    (hN : ∀ a, coefficient K L a = ((N a : ℕ) : K))
    (h : ∀ a, N a % 2 = if MMCompatible a then 1 else 0) :
    RankLE r (matrixMultiplication (K := K) m n p) := by
  rw [decomposition_of_natCoefficient_mod_two h2 L N hN h]
  exact (RankLE.list_sum_pure (K := K) L).mono hlen

end MMCertificate

end AlgebraicComplexity
