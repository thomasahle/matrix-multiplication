/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication
import AlgebraicComplexity.MatrixMultiplication.RankComplexity
import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.LinearAlgebra.Pi

/-!
# Bilinear algorithms and the tensor-rank correspondence

This module proves the semantic bridge between bilinear algorithms and constructive tensor
rank, following Definitions 2.2--2.4 and Fact 2.9 of He and Williams's CS 6810 lecture notes
(<https://www.cs.cornell.edu/courses/cs6810/2023fa/Matrix.pdf>); see the reference theorem
ladder in `DESIGN.md`.

## Objects

* `CoordinateBilinearMap K ι κ μ`: `K`-bilinear maps `(ι → K) → (κ → K) → (μ → K)` between
  standard coordinate spaces on index types `ι`, `κ`, `μ` (Definition 2.2).
* `bilinearMapOfCoeff` and `coeffOfBilinearMap`: the correspondence between such bilinear maps
  and coefficient arrays `c : ι → κ → μ → K`; over finite index types with decidable equality
  the two constructions are mutually inverse (Definition 2.3).
* `BilinearIndex ι κ μ` and `coeffTensor c`: the leg-indexed family placing `ι`, `κ`, `μ` on
  the `X`, `Y`, `Z` tensor legs, and the abstract three-legged tensor whose standard
  coordinates (through `Tensor.standardCoordinateEquiv`) are exactly the array `c`.
* `BilinearAlgorithm K ι κ μ r`: a length-`r` bilinear algorithm (Definition 2.4), given by
  coefficient vectors of linear forms `f i : ι → K` and `g i : κ → K` on the two inputs and
  output vectors `w i : μ → K`, for each of the `r` multiplications `i : Fin r`.
* `BilinearAlgorithm.Computes`: the relation "algorithm `A` computes the bilinear map `B`";
  it says that every output coordinate `B x y m` equals the algorithm's arithmetic
  `∑ i, A.w i m * (∑ a, A.f i a * x a) * (∑ b, A.g i b * y b)`.

## Main results

* `BilinearAlgorithm.computes_iff_tensor_eq`: `A` computes the bilinear map of the coefficient
  array `c` if and only if the sum of the `r` pure tensors `f i ⊗ g i ⊗ w i` equals
  `coeffTensor c`.
* `rankLE_coeffTensor_iff_exists_computes` (Fact 2.9): `Tensor.RankLE r (coeffTensor c)` holds
  if and only if some length-`r` bilinear algorithm computes `bilinearMapOfCoeff c`.  Both
  directions are constructive: an algorithm is literally a list of `r` pure tensors, and a
  list of at most `r` pure tensors is zero-padded to an algorithm of length exactly `r`.
* `matrixMultiplication_rankLE_iff_exists_algorithm`: the specialization to matrix
  multiplication.  A length-`r` bilinear algorithm for the `(m, n, p)` matrix-product map
  exists if and only if `Tensor.RankLE r (matrixMultiplication K m n p)`.
* `exists_matrixProductMap_algorithm`: the defining `m * n * p`-term decomposition yields the
  elementary matrix-multiplication algorithm, a tiny regression client of the bridge.
* `BilinearAlgorithm.exists_straightline_of_computes`: the bridge into the arithmetic-cost
  model of `MatrixMultiplication/RankComplexity.lean`.  An algorithm computing `B` compiles to
  a straight-line program on the inputs `ι ⊕ κ` that evaluates `B` using at most `r` nonscalar
  multiplications and `O(r · (|ι| + |κ| + |μ|))` operations in total.

## Conventions

Everything works over an arbitrary commutative semiring.  Linear forms are represented by
their coefficient vectors and applied by the explicit dot product `∑ a, f a * x a`.
Decidability hypotheses appear only in statements mentioning `coeffOfBilinearMap`, whose
definition evaluates on standard basis vectors; all other proofs use classical choice
locally, so the main correspondence theorems carry only finiteness hypotheses.
The output leg of the matrix-product map follows the `Z`-leg convention of
`matrixMultiplication`: the output of `matrixProductMap` is indexed by `Fin p × Fin m`, and
its value at `(k, i)` is the `(i, k)` entry `∑ j, x (i, j) * y (j, k)` of the matrix product.
This is the indexing for which the coordinate tensor of the matrix-product map is exactly
`matrixMultiplication K m n p`.

## Layer placement and non-goals

This file belongs to the matrix-multiplication theory layer: it sits on the coordinate bridge
`Tensor/Coordinates.lean` and the rank calculus `Tensor/Rank.lean`, and specializes to the
tensor from `AlgebraicComplexity/MatrixMultiplication.lean`.  It also imports the
Mathlib-only straight-line-program module `MatrixMultiplication/RankComplexity.lean`, which
supplies the arithmetic cost model; the import direction is one-way, so there is no cycle.
Only the one-step compilation of an algorithm is claimed here; the recursion that turns it into
an asymptotic statement lives one module up, in
`MatrixMultiplication/RankComplexityRecursion.lean`, which imports this file and proves the
forward half of Proposition 2.7 of the notes as
`exists_straightline_matrixProduct_of_omega_lt`: over a field, every `τ > ω` admits
straight-line programs for the `n × n` product of total cost `O(n^τ)`.  The converse — that a
circuit family of cost `O(n^τ)` forces a rank bound, and hence that the two definitions of the
exponent agree — remains future work; `RankComplexityRecursion.lean` documents in its own
non-goals what such an argument would have to supply.
-/

namespace AlgebraicComplexity

open Tensor

universe u v

/-- `K`-bilinear maps between the standard coordinate spaces on index types `ι`, `κ`, `μ`:
curried linear maps `(ι → K) →ₗ (κ → K) →ₗ (μ → K)`.  This is the semantic notion of a
bilinear map computed by a bilinear algorithm (notes, Definition 2.2). -/
abbrev CoordinateBilinearMap (K : Type u) [CommSemiring K] (ι κ μ : Type v) :=
  (ι → K) →ₗ[K] (κ → K) →ₗ[K] (μ → K)

/-- The three-legged index family of a coefficient array: `ι` on the `X` leg, `κ` on the `Y`
leg, and `μ` on the `Z` leg. -/
abbrev BilinearIndex (ι κ μ : Type v) : Leg → Type v
  | .X => ι
  | .Y => κ
  | .Z => μ

instance {ι κ μ : Type v} [Finite ι] [Finite κ] [Finite μ] (c : Leg) :
    Finite (BilinearIndex ι κ μ c) := by
  cases c <;> infer_instance

/-- A length-`r` bilinear algorithm (notes, Definition 2.4).  For each of the `r`
multiplications `i : Fin r` it records the coefficient vector `f i` of a linear form in the
first input, the coefficient vector `g i` of a linear form in the second input, and the
output vector `w i` distributing the product to the output coordinates.  The raw data needs
no algebraic structure; the semantics live in `BilinearAlgorithm.Computes`. -/
structure BilinearAlgorithm (K : Type u) (ι κ μ : Type v) (r : ℕ) where
  /-- Coefficient vectors of the linear forms applied to the first input. -/
  f : Fin r → ι → K
  /-- Coefficient vectors of the linear forms applied to the second input. -/
  g : Fin r → κ → K
  /-- Output vectors distributing each product to the output coordinates. -/
  w : Fin r → μ → K

section BilinearMaps

variable {K : Type u} [CommSemiring K] {ι κ μ : Type v}

/-- The bilinear map of a coefficient array `c`: it sends inputs `x`, `y` to the output whose
`m`-th coordinate is `∑ i, ∑ j, c i j m * x i * y j` (notes, Definition 2.3). -/
def bilinearMapOfCoeff [Fintype ι] [Fintype κ] (c : ι → κ → μ → K) :
    CoordinateBilinearMap K ι κ μ :=
  LinearMap.mk₂ K (fun x y m => ∑ i, ∑ j, c i j m * x i * y j)
    (fun x₁ x₂ y => funext fun m => by
      simp only [Pi.add_apply, mul_add, add_mul, Finset.sum_add_distrib])
    (fun t x y => funext fun m => by
      simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring)
    (fun x y₁ y₂ => funext fun m => by
      simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib])
    (fun t x y => funext fun m => by
      simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring)

/-- Coordinate formula defining the bilinear map of a coefficient array. -/
@[simp] theorem bilinearMapOfCoeff_apply [Fintype ι] [Fintype κ]
    (c : ι → κ → μ → K) (x : ι → K) (y : κ → K) (m : μ) :
    bilinearMapOfCoeff c x y m = ∑ i, ∑ j, c i j m * x i * y j := rfl

/-- The coefficient array of a bilinear map, read off by evaluating on the standard basis
vectors of the two input spaces. -/
def coeffOfBilinearMap [DecidableEq ι] [DecidableEq κ]
    (B : CoordinateBilinearMap K ι κ μ) : ι → κ → μ → K :=
  fun i j m => B (Pi.single i 1) (Pi.single j 1) m

/-- Reading coefficients back from the bilinear map of a coefficient array recovers the
array. -/
@[simp] theorem coeffOfBilinearMap_bilinearMapOfCoeff
    [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] (c : ι → κ → μ → K) :
    coeffOfBilinearMap (bilinearMapOfCoeff c) = c := by
  funext i j m
  simp [coeffOfBilinearMap, Pi.single_apply]

/-- A bilinear map between finite coordinate spaces is the bilinear map of its coefficient
array.

Proof sketch: both sides are bilinear, so by linearity in each input (`LinearMap.pi_ext`) it
suffices to compare them on scaled standard basis vectors, where the defining double sum of
`bilinearMapOfCoeff` collapses to the single matching coefficient. -/
@[simp] theorem bilinearMapOfCoeff_coeffOfBilinearMap
    [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (B : CoordinateBilinearMap K ι κ μ) :
    bilinearMapOfCoeff (coeffOfBilinearMap B) = B := by
  refine LinearMap.pi_ext fun i x => ?_
  refine LinearMap.pi_ext fun j y => ?_
  funext m
  have hx : (Pi.single i x : ι → K) = x • (Pi.single i 1 : ι → K) := by
    rw [← Pi.single_smul, smul_eq_mul, mul_one]
  have hy : (Pi.single j y : κ → K) = y • (Pi.single j 1 : κ → K) := by
    rw [← Pi.single_smul, smul_eq_mul, mul_one]
  simp only [hx, hy, map_smul, LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul]
  simp [coeffOfBilinearMap, Pi.single_apply]

end BilinearMaps

section CoefficientTensor

variable {K : Type u} [CommSemiring K] {ι κ μ : Type v}

/-- The abstract three-legged tensor of a coefficient array: the element of
`Tensor3 K (CoordinateSpace K (BilinearIndex ι κ μ))` whose standard coordinates are exactly
`c`.  This is the trilinear tensor associated to the bilinear map `bilinearMapOfCoeff c`. -/
noncomputable def coeffTensor [Finite ι] [Finite κ] [Finite μ] (c : ι → κ → μ → K) :
    Tensor3 K (CoordinateSpace K (BilinearIndex ι κ μ)) :=
  (standardCoordinateEquiv (K := K) (κ := BilinearIndex ι κ μ)).symm
    (fun a => c (a .X) (a .Y) (a .Z))

/-- The standard coordinates of `coeffTensor c` are the entries of `c`. -/
@[simp] theorem standardCoordinateEquiv_coeffTensor [Finite ι] [Finite κ] [Finite μ]
    (c : ι → κ → μ → K) (a : ∀ i, BilinearIndex ι κ μ i) :
    standardCoordinateEquiv (K := K) (κ := BilinearIndex ι κ μ) (coeffTensor c) a =
      c (a .X) (a .Y) (a .Z) := by
  simp [coeffTensor]

end CoefficientTensor

namespace BilinearAlgorithm

variable {K : Type u} {ι κ μ : Type v} {r : ℕ}

/-- The `i`-th rank-one term of an algorithm, as a leg-indexed family of coordinate
vectors: `f i` on the `X` leg, `g i` on the `Y` leg, `w i` on the `Z` leg. -/
def term (A : BilinearAlgorithm K ι κ μ r) (i : Fin r) :
    ∀ c, CoordinateSpace K (BilinearIndex ι κ μ) c :=
  ofLegs (V := CoordinateSpace K (BilinearIndex ι κ μ)) (A.f i) (A.g i) (A.w i)

/-- The `X`-leg component of a rank-one algorithm term is its first linear form. -/
@[simp] theorem term_X (A : BilinearAlgorithm K ι κ μ r) (i : Fin r) :
    A.term i .X = A.f i := rfl

/-- The `Y`-leg component of a rank-one algorithm term is its second linear form. -/
@[simp] theorem term_Y (A : BilinearAlgorithm K ι κ μ r) (i : Fin r) :
    A.term i .Y = A.g i := rfl

/-- The `Z`-leg component of a rank-one algorithm term is its output vector. -/
@[simp] theorem term_Z (A : BilinearAlgorithm K ι κ μ r) (i : Fin r) :
    A.term i .Z = A.w i := rfl

variable [CommSemiring K]

/-- The algorithm `A` computes the bilinear map `B`: for all inputs `x`, `y` and every output
coordinate `m`, the semantic value `B x y m` equals the algorithm's arithmetic, namely the sum
over the `r` multiplications of `w i m` times the two linear forms applied to the inputs. -/
def Computes [Fintype ι] [Fintype κ] (A : BilinearAlgorithm K ι κ μ r)
    (B : CoordinateBilinearMap K ι κ μ) : Prop :=
  ∀ (x : ι → K) (y : κ → K) (m : μ),
    B x y m = ∑ i, A.w i m * (∑ a, A.f i a * x a) * (∑ b, A.g i b * y b)

/-- The rank-decomposition tensor of an algorithm: the sum of its `r` pure tensors
`f i ⊗ g i ⊗ w i`. -/
noncomputable def tensor (A : BilinearAlgorithm K ι κ μ r) :
    Tensor3 K (CoordinateSpace K (BilinearIndex ι κ μ)) :=
  ∑ i, Tensor.pure (K := K) (A.term i)

/-- Coordinate formula for the rank-decomposition tensor of an algorithm. -/
theorem standardCoordinateEquiv_tensor [Finite ι] [Finite κ] [Finite μ]
    (A : BilinearAlgorithm K ι κ μ r) (a : ∀ c, BilinearIndex ι κ μ c) :
    standardCoordinateEquiv (K := K) (κ := BilinearIndex ι κ μ) A.tensor a =
      ∑ i, A.f i (a .X) * A.g i (a .Y) * A.w i (a .Z) := by
  simp only [tensor, map_sum, Finset.sum_apply, standardCoordinateEquiv_pure, prod_leg,
    term_X, term_Y, term_Z]

/-- An algorithm of length `r` is by definition a rank-`r` certificate for its tensor. -/
theorem tensor_rankLE (A : BilinearAlgorithm K ι κ μ r) : RankLE r A.tensor := by
  simpa [tensor] using
    RankLE.fintype_sum_pure (K := K)
      (V := CoordinateSpace K (BilinearIndex ι κ μ)) (x := A.term)

/-- Computing the bilinear map of a coefficient array is equivalent to the entrywise
coefficient identity `c i j m = ∑ t, w t m * f t i * g t j`.

Proof sketch: evaluating the computation equation on standard basis vectors collapses both
double sums and yields the coefficient identity.  Conversely, substituting the identity into
the defining double sum of `bilinearMapOfCoeff`, exchanging the three finite sums, and
refactoring the two inner sums as products of linear forms recovers the computation
equation for arbitrary inputs. -/
theorem computes_iff_coeff [Fintype ι] [Fintype κ]
    (A : BilinearAlgorithm K ι κ μ r) (c : ι → κ → μ → K) :
    A.Computes (bilinearMapOfCoeff c) ↔
      ∀ (i : ι) (j : κ) (m : μ), c i j m = ∑ t, A.w t m * A.f t i * A.g t j := by
  classical
  constructor
  · intro h i j m
    have h1 := h (Pi.single i 1) (Pi.single j 1) m
    simpa [Pi.single_apply] using h1
  · intro h x y m
    calc bilinearMapOfCoeff c x y m
        = ∑ i, ∑ j, ∑ t, A.w t m * A.f t i * A.g t j * x i * y j := by
          simp only [bilinearMapOfCoeff_apply]
          exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by
            rw [h i j m, Finset.sum_mul, Finset.sum_mul]
      _ = ∑ i, ∑ t, ∑ j, A.w t m * A.f t i * A.g t j * x i * y j :=
          Finset.sum_congr rfl fun i _ => Finset.sum_comm
      _ = ∑ t, ∑ i, ∑ j, A.w t m * A.f t i * A.g t j * x i * y j := Finset.sum_comm
      _ = ∑ t, A.w t m * (∑ a, A.f t a * x a) * (∑ b, A.g t b * y b) := by
          refine Finset.sum_congr rfl fun t _ => Eq.symm ?_
          simp only [Finset.mul_sum, Finset.sum_mul]
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun a _ =>
            Finset.sum_congr rfl fun b _ => by ring

/-- Fact 2.9, tensor form: an algorithm computes the bilinear map of the coefficient array
`c` if and only if its rank-decomposition tensor is `coeffTensor c`.

Proof sketch: by `computes_iff_coeff`, computing the map is the entrywise coefficient
identity, and by `standardCoordinate_ext` the tensor equation is the same identity read
through the standard coordinate equivalence, one output coordinate at a time. -/
theorem computes_iff_tensor_eq [Fintype ι] [Fintype κ] [Finite μ]
    (A : BilinearAlgorithm K ι κ μ r) (c : ι → κ → μ → K) :
    A.Computes (bilinearMapOfCoeff c) ↔ A.tensor = coeffTensor c := by
  rw [computes_iff_coeff]
  constructor
  · intro h
    apply standardCoordinate_ext
    intro a
    rw [standardCoordinateEquiv_tensor, standardCoordinateEquiv_coeffTensor,
      h (a .X) (a .Y) (a .Z)]
    exact Finset.sum_congr rfl fun t _ => by ring
  · intro h i j m
    have ha : standardCoordinateEquiv (K := K) (κ := BilinearIndex ι κ μ) A.tensor
          (ofLegs (V := BilinearIndex ι κ μ) i j m) =
        standardCoordinateEquiv (K := K) (κ := BilinearIndex ι κ μ) (coeffTensor c)
          (ofLegs (V := BilinearIndex ι κ μ) i j m) := by rw [h]
    rw [standardCoordinateEquiv_tensor, standardCoordinateEquiv_coeffTensor] at ha
    simp only [ofLegs_X, ofLegs_Y, ofLegs_Z] at ha
    rw [← ha]
    exact Finset.sum_congr rfl fun t _ => by ring

/-- An algorithm computing the bilinear map of a coefficient array certifies the rank bound
`Tensor.RankLE r (coeffTensor c)`. -/
theorem Computes.rankLE_coeffTensor [Fintype ι] [Fintype κ] [Finite μ]
    {A : BilinearAlgorithm K ι κ μ r} {c : ι → κ → μ → K}
    (hA : A.Computes (bilinearMapOfCoeff c)) : RankLE r (coeffTensor c) := by
  rw [← (A.computes_iff_tensor_eq c).mp hA]
  exact A.tensor_rankLE

/-- Read a length-`r` bilinear algorithm off a list of at most `r` leg-indexed rank-one
terms, padding the missing multiplications with zero forms. -/
def ofTermList (terms : List (∀ c, CoordinateSpace K (BilinearIndex ι κ μ) c)) (r : ℕ) :
    BilinearAlgorithm K ι κ μ r where
  f i := terms.getD (i : ℕ) 0 .X
  g i := terms.getD (i : ℕ) 0 .Y
  w i := terms.getD (i : ℕ) 0 .Z

/-- The rank-one terms of `ofTermList` are the list entries, padded by zero. -/
theorem term_ofTermList (terms : List (∀ c, CoordinateSpace K (BilinearIndex ι κ μ) c))
    (r : ℕ) (i : Fin r) :
    (ofTermList terms r).term i = terms.getD (i : ℕ) 0 := by
  funext c
  cases c <;> rfl

end BilinearAlgorithm

section RankCorrespondence

variable {K : Type u} [CommSemiring K] {ι κ μ : Type v}

/-- Summing the image of a list under a map killing the padding element equals the sum over
`Fin r` of padded list accesses, for any `r` at least the list length.  This is the
bookkeeping that turns a rank certificate of at most `r` terms into an algorithm of length
exactly `r`. -/
private theorem list_map_sum_eq_sum_getD {α : Type*} {M : Type*} [AddCommMonoid M]
    (F : α → M) (z : α) (hz : F z = 0) :
    ∀ (l : List α) (r : ℕ), l.length ≤ r →
      (l.map F).sum = ∑ i : Fin r, F (l.getD (i : ℕ) z)
  | [], r, _ => by simp [hz]
  | a :: l, 0, h => by simp at h
  | a :: l, r + 1, h => by
      rw [Fin.sum_univ_succ, List.map_cons, List.sum_cons]
      simp only [Fin.val_zero, List.getD_cons_zero, Fin.val_succ, List.getD_cons_succ]
      rw [list_map_sum_eq_sum_getD F z hz l r (Nat.le_of_succ_le_succ (by simpa using h))]

namespace BilinearAlgorithm

/-- The rank-decomposition tensor of a zero-padded algorithm is the sum of the pure tensors
of the underlying list.  The direction is: the algorithm reconstructs the list's tensor. -/
theorem tensor_ofTermList (terms : List (∀ c, CoordinateSpace K (BilinearIndex ι κ μ) c))
    (r : ℕ) (h : terms.length ≤ r) :
    (ofTermList (K := K) terms r).tensor = (terms.map (Tensor.pure (K := K))).sum := by
  have hterm : (ofTermList (K := K) terms r).tensor =
      ∑ i : Fin r, Tensor.pure (K := K) (terms.getD (i : ℕ) 0) := by
    simp only [tensor, term_ofTermList]
  rw [hterm]
  exact (list_map_sum_eq_sum_getD (Tensor.pure (K := K)) 0
    ((PiTensorProduct.tprod K).map_coord_zero Leg.X rfl) terms r h).symm

end BilinearAlgorithm

/-- From a rank-`r` certificate for `coeffTensor c`, zero-padding the certificate's list of
pure terms produces a length-`r` bilinear algorithm computing `bilinearMapOfCoeff c`. -/
theorem exists_computes_of_rankLE [Fintype ι] [Fintype κ] [Finite μ]
    {c : ι → κ → μ → K} {r : ℕ} (h : RankLE r (coeffTensor c)) :
    ∃ A : BilinearAlgorithm K ι κ μ r, A.Computes (bilinearMapOfCoeff c) := by
  obtain ⟨terms, hlen, hsum⟩ := h
  refine ⟨BilinearAlgorithm.ofTermList terms r, ?_⟩
  rw [BilinearAlgorithm.computes_iff_tensor_eq,
    BilinearAlgorithm.tensor_ofTermList terms r hlen, ← hsum]

/-- **Fact 2.9.** A coefficient tensor satisfies the constructive rank bound
`Tensor.RankLE r` if and only if some length-`r` bilinear algorithm computes its bilinear
map.

Proof sketch: an algorithm is a list of `r` rank-one terms whose sum has the coordinates
demanded by `computes_iff_tensor_eq`, and conversely a certificate list of at most `r` pure
tensors is zero-padded by `ofTermList` to an algorithm of length exactly `r` with the same
tensor. -/
theorem rankLE_coeffTensor_iff_exists_computes [Fintype ι] [Fintype κ] [Finite μ]
    (c : ι → κ → μ → K) (r : ℕ) :
    RankLE r (coeffTensor c) ↔
      ∃ A : BilinearAlgorithm K ι κ μ r, A.Computes (bilinearMapOfCoeff c) := by
  constructor
  · exact exists_computes_of_rankLE
  · rintro ⟨A, hA⟩
    exact hA.rankLE_coeffTensor

/-- Fact 2.9 for an arbitrary bilinear map `B` between finite coordinate spaces: a length-`r`
algorithm computing `B` exists if and only if the coefficient tensor read off from `B` has
rank at most `r`. -/
theorem exists_computes_iff_rankLE_coeffTensor [Fintype ι] [Fintype κ] [Finite μ]
    [DecidableEq ι] [DecidableEq κ] (B : CoordinateBilinearMap K ι κ μ) (r : ℕ) :
    (∃ A : BilinearAlgorithm K ι κ μ r, A.Computes B) ↔
      RankLE r (coeffTensor (coeffOfBilinearMap B)) := by
  rw [rankLE_coeffTensor_iff_exists_computes, bilinearMapOfCoeff_coeffOfBilinearMap]

end RankCorrespondence

section MatrixMultiplicationBridge

variable {K : Type u} [CommSemiring K]

/-- The coefficient array of the `(m, n, p)` matrix-product map: the entry at row-column
indices `a = (i, j)`, `b = (j', k)`, `z = (k', i')` is `1` exactly when the inner indices
chain, `j = j'`, `k = k'`, `i = i'`, matching `MMCompatible`. -/
def mmCoeff (m n p : ℕ) :
    (Fin m × Fin n) → (Fin n × Fin p) → (Fin p × Fin m) → K :=
  fun a b z => if a.2 = b.1 ∧ b.2 = z.1 ∧ z.2 = a.1 then 1 else 0

/-- The coefficient tensor of the matrix-product coefficient array is the
matrix-multiplication tensor.  Both sides have standard coordinates `1` on compatible index
triples and `0` elsewhere. -/
theorem coeffTensor_mmCoeff (m n p : ℕ) :
    coeffTensor (mmCoeff (K := K) m n p) = matrixMultiplication (K := K) m n p := by
  apply standardCoordinate_ext
  intro a
  rw [standardCoordinateEquiv_coeffTensor, standardCoordinateEquiv_matrixMultiplication]
  rfl

/-- The `(m, n, p)` matrix-product map on coordinate spaces.  The inputs are an `m × n`
matrix `x` and an `n × p` matrix `y` in row-column coordinates; the output is indexed by the
`Z`-leg convention `Fin p × Fin m` of `matrixMultiplication`, and its value at `(k, i)` is
the matrix-product entry `∑ j, x (i, j) * y (j, k)`. -/
def matrixProductMap (m n p : ℕ) :
    CoordinateBilinearMap K (Fin m × Fin n) (Fin n × Fin p) (Fin p × Fin m) :=
  LinearMap.mk₂ K (fun x y z => ∑ j, x (z.2, j) * y (j, z.1))
    (fun x₁ x₂ y => funext fun z => by
      simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib])
    (fun t x y => funext fun z => by
      simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc])
    (fun x y₁ y₂ => funext fun z => by
      simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib])
    (fun t x y => funext fun z => by
      simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring)

/-- Coordinate formula defining the matrix-product map. -/
@[simp] theorem matrixProductMap_apply (m n p : ℕ)
    (x : Fin m × Fin n → K) (y : Fin n × Fin p → K) (z : Fin p × Fin m) :
    matrixProductMap (K := K) m n p x y z = ∑ j, x (z.2, j) * y (j, z.1) := rfl

/-- The matrix-product map is the bilinear map of the coefficient array `mmCoeff`.

Proof sketch: expanding the defining double sum of `bilinearMapOfCoeff` over the two pair
index types, the indicator coefficient collapses three of the four coordinate sums and
leaves exactly the inner-dimension sum of the matrix product. -/
theorem matrixProductMap_eq_bilinearMapOfCoeff (m n p : ℕ) :
    matrixProductMap (K := K) m n p = bilinearMapOfCoeff (mmCoeff (K := K) m n p) := by
  refine LinearMap.ext fun x => LinearMap.ext fun y => funext fun z => Eq.symm ?_
  simp only [bilinearMapOfCoeff_apply, mmCoeff, matrixProductMap_apply]
  simp [Fintype.sum_prod_type, ite_and, ite_mul, Finset.sum_ite_eq,
    Finset.sum_ite_eq']

/-- **The bilinear-algorithm characterization of matrix-multiplication rank.**  A length-`r`
bilinear algorithm computing the `(m, n, p)` matrix-product map exists if and only if the
matrix-multiplication tensor satisfies the constructive rank bound `Tensor.RankLE r`.

Proof sketch: rewrite the matrix-product map as the bilinear map of `mmCoeff` and the
matrix-multiplication tensor as its coefficient tensor, then apply Fact 2.9
(`rankLE_coeffTensor_iff_exists_computes`). -/
theorem matrixMultiplication_rankLE_iff_exists_algorithm (m n p r : ℕ) :
    RankLE r (matrixMultiplication (K := K) m n p) ↔
      ∃ A : BilinearAlgorithm K (Fin m × Fin n) (Fin n × Fin p) (Fin p × Fin m) r,
        A.Computes (matrixProductMap (K := K) m n p) := by
  rw [← coeffTensor_mmCoeff (K := K) m n p, matrixProductMap_eq_bilinearMapOfCoeff]
  exact rankLE_coeffTensor_iff_exists_computes (mmCoeff (K := K) m n p) r

/-- The defining `m * n * p`-term decomposition of the matrix-multiplication tensor yields
the elementary matrix-multiplication algorithm.  This is a tiny regression client of the
bilinear-algorithm bridge. -/
theorem exists_matrixProductMap_algorithm (m n p : ℕ) :
    ∃ A : BilinearAlgorithm K (Fin m × Fin n) (Fin n × Fin p) (Fin p × Fin m) (m * n * p),
      A.Computes (matrixProductMap (K := K) m n p) :=
  (matrixMultiplication_rankLE_iff_exists_algorithm m n p (m * n * p)).mp
    (matrixMultiplication_rankLE m n p)

end MatrixMultiplicationBridge

section StraightlineBridge

variable {K : Type u} [CommSemiring K] {ι κ μ : Type v} {r : ℕ}

/-- **Compilation of a bilinear algorithm into a straight-line program.**  A length-`r`
bilinear algorithm computing a bilinear map `B` compiles to a straight-line program on the
disjoint union `ι ⊕ κ` of the two input index types that evaluates `B` on every output
coordinate simultaneously, using at most `r` nonscalar multiplications and at most
`r * (2 * (|ι| + |κ| + |μ|) + 1)` operations in total.

This is the semantic bridge from this module's algorithm data to the arithmetic-complexity
model of `MatrixMultiplication/RankComplexity.lean`: combined with
`matrixMultiplication_rankLE_iff_exists_algorithm`, a rank-`r` decomposition of
`matrixMultiplication K m n p` yields a circuit for the matrix product with `r` nonscalar
multiplications.  Only one recursion step is claimed here; iterating it is
`RankComplexityRecursion.exists_straightline_matrixProduct_of_omega_lt`.  The converse
direction — circuits implying rank bounds, and hence the equality of the circuit-complexity and
tensor-rank definitions of `omega` — remains future work.

Proof sketch: feed the algorithm's coefficient vectors `A.f`, `A.g`, `A.w` to
`exists_straightline_bilinear`.  Its evaluation identity groups the product as
`w t m * (F t * G t)` while `BilinearAlgorithm.Computes` groups it as `w t m * F t * G t`, so
the two agree termwise by associativity. -/
theorem BilinearAlgorithm.exists_straightline_of_computes
    [Fintype ι] [Fintype κ] [Fintype μ]
    {A : BilinearAlgorithm K ι κ μ r} {B : CoordinateBilinearMap K ι κ μ}
    (hA : A.Computes B) :
    ∃ p : Straightline K μ (ι ⊕ κ),
      (∀ (x : ι → K) (y : κ → K) (m : μ), p.eval (Sum.elim x y) m = B x y m)
        ∧ p.nonscalarMuls ≤ r
        ∧ p.totalOps ≤
            r * (2 * (Fintype.card ι + Fintype.card κ + Fintype.card μ) + 1) := by
  obtain ⟨p, heval, hmuls, hops⟩ :=
    exists_straightline_bilinear (K := K) (μ := μ) r A.f A.g A.w
  refine ⟨p, fun x y m ↦ ?_, hmuls, hops⟩
  rw [heval, hA]
  exact Finset.sum_congr rfl fun t _ ↦ (mul_assoc _ _ _).symm

end StraightlineBridge

end AlgebraicComplexity
