/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.BilinearAlgorithm
import AlgebraicComplexity.MatrixMultiplication.Exponent
import Mathlib.Algebra.Algebra.ZMod
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.RingTheory.Algebraic.Integral

/-!
# The exponent of matrix multiplication and change of scalars

How does `omega K` depend on `K`?  This file proves the two classical comparison theorems.

**Base change.**  A rank decomposition of `⟨m,n,p⟩` has coefficients in `K` and satisfies
polynomial identities with coefficients `0` and `1`, so its image under any ring homomorphism
`K →+* L` is a rank decomposition over `L`.  Hence rank can only drop along a ring homomorphism and

```text
omega L ≤ omega K        for every ring homomorphism K →+* L        (`omega_le_of_ringHom`).
```

In particular `omega K ≤ omega ℤ` for every commutative ring, and `omega K ≤ omega ℕ` for every
commutative semiring: the integers are the hardest case.

**Descent along an algebraic extension.**  In the other direction, let `E / F` be an algebraic
extension of fields and suppose `⟨n,n,n⟩` has rank at most `r` over `E`.  The finitely many
coefficients of a decomposition generate a finite extension `L / F`, of degree `d` say, and the
decomposition lives over `L`.  A decomposition of *any* tensor with coefficients in `F` over `L`
descends to one over `F` at the cost of a factor `d²`: writing the first two vectors of each term
in an `F`-basis `b` of `L` and applying an `F`-linear functional `φ : L → F` with `φ 1 = 1` to
the identity `c = ∑ₜ fₜ gₜ wₜ` gives

```text
c  =  ∑ₜ ∑ₐ ∑ₐ' (fₜ)ₐ · (gₜ)ₐ' · φ (wₜ · bₐ · bₐ'),
```

which is `r · d · d` rank-one terms over `F` (`exists_computes_of_finiteDimensional`).  The
factor does not depend on the tensor, so it is paid once for every tensor power:
`R_F(⟨nᵏ,nᵏ,nᵏ⟩) ≤ d² · rᵏ`, and taking `k`-th roots gives `n ^ omega F ≤ r`
(`rpow_omega_le_of_rankLE_of_isAlgebraic`).  Therefore

```text
omega F ≤ omega E        for every algebraic field extension E / F   (`omega_le_of_isAlgebraic`),
```

and with base change `omega E = omega F`: the exponent is invariant under algebraic extensions.
No separability or characteristic hypothesis is needed.

## Main results

* `rankLE_matrixMultiplication_of_ringHom`, `omega_le_of_ringHom`: base change.
* `omega_le_omega_int`, `omega_le_omega_nat`: the universal upper bounds.
* `BilinearAlgorithm.exists_computes_of_finiteDimensional`: descent of a bilinear algorithm
  along a finite field extension, with length multiplied by the square of the degree.
* `rankLE_matrixMultiplication_pow_of_isAlgebraic`: `R_F(⟨nᵏ,nᵏ,nᵏ⟩) ≤ rᵏ · d · d`.
* `omega_le_of_isAlgebraic`, `omega_eq_of_isAlgebraic`: invariance under algebraic extensions.
* `omega_algebraicClosure`: `omega (AlgebraicClosure F) = omega F`.
* `omega_eq_omega_zmod_of_finite`: all finite fields of characteristic `p` have the exponent of
  `ZMod p`.

## Scope

The full classical statement is that `omega` depends only on the characteristic.  What is missing
here for that is the transcendental case, `omega F ≤ omega E` for an arbitrary field extension,
which needs a specialization argument (a decomposition over `E` is a point of a variety defined
over `F`, and a nonempty variety has a point over the algebraic closure of `F`).  It is not proved
in this file.

## References

* P. Bürgisser, M. Clausen, M. A. Shokrollahi, *Algebraic Complexity Theory*, Springer 1997,
  §15.3, p. 383: the exponent is unchanged under scalar extension.
* A. Schönhage, *Partial and total matrix multiplication*, SIAM J. Comput. 10 (1981): the exponent
  depends only on the characteristic.  The literature cites this as Theorem 2.8 of that paper;
  the numbering was not checked against the paper for this file.
* The descent argument follows `Arithmetic/FieldDescent.lean` of
  <https://github.com/selanavot/matrix-multiplication-all-fields>, which is where the factor-`d²`
  functional trick is taken from; that development is vendored under `ThirdParty/OAI/`, and this
  file restates the argument for this repository's `BilinearAlgorithm`, `RankLE` and `omega`
  without importing it.
-/

namespace AlgebraicComplexity

open Tensor Module

universe u u' v

/-! ### Base change along a ring homomorphism -/

section BaseChange

variable {K : Type u} {L : Type u'} [CommSemiring K] [CommSemiring L]

namespace BilinearAlgorithm

variable {ι κ μ : Type v} {r : ℕ}

/-- The algorithm obtained by applying a map to every coefficient. -/
def mapCoeff (φ : K → L) (A : BilinearAlgorithm K ι κ μ r) : BilinearAlgorithm L ι κ μ r where
  f t i := φ (A.f t i)
  g t j := φ (A.g t j)
  w t m := φ (A.w t m)

/-- The image of an algorithm under a ring homomorphism computes the image of the bilinear map:
the defining identities `c i j m = ∑ t, w t m * f t i * g t j` are preserved. -/
theorem Computes.mapCoeff [Fintype ι] [Fintype κ] (φ : K →+* L)
    {A : BilinearAlgorithm K ι κ μ r} {c : ι → κ → μ → K}
    (h : A.Computes (bilinearMapOfCoeff c)) :
    (A.mapCoeff φ).Computes (bilinearMapOfCoeff fun i j m ↦ φ (c i j m)) := by
  rw [computes_iff_coeff] at h ⊢
  intro i j m
  rw [h i j m, map_sum]
  simp [BilinearAlgorithm.mapCoeff]

end BilinearAlgorithm

/-- The matrix-product coefficient array has entries `0` and `1`, so every ring homomorphism maps
it to itself. -/
theorem map_mmCoeff (φ : K →+* L) (m n p : ℕ) :
    (fun a b z ↦ φ (mmCoeff (K := K) m n p a b z)) = mmCoeff (K := L) m n p := by
  funext a b z
  unfold mmCoeff
  split_ifs <;> simp

/-- **Rank of matrix multiplication does not increase along a ring homomorphism.** -/
theorem rankLE_matrixMultiplication_of_ringHom (φ : K →+* L) {m n p r : ℕ}
    (h : RankLE r (matrixMultiplication (K := K) m n p)) :
    RankLE r (matrixMultiplication (K := L) m n p) := by
  rw [matrixMultiplication_rankLE_iff_exists_algorithm] at h ⊢
  obtain ⟨A, hA⟩ := h
  rw [matrixProductMap_eq_bilinearMapOfCoeff] at hA ⊢
  refine ⟨A.mapCoeff φ, ?_⟩
  rw [← map_mmCoeff φ]
  exact hA.mapCoeff φ

/-- The square rank sequence over the target of a ring homomorphism is bounded by the one over
its source. -/
theorem squareMatrixRankSequence_le_of_ringHom (φ : K →+* L) (n : ℕ) :
    squareMatrixRankSequence L n ≤ squareMatrixRankSequence K n :=
  rank_le_iff.mpr (rankLE_matrixMultiplication_of_ringHom φ (rank_spec _))

/-- A polynomial rank bound transfers along a ring homomorphism. -/
theorem matrixExponentLE_of_ringHom (φ : K →+* L) {τ : ℝ} (h : MatrixExponentLE K τ) :
    MatrixExponentLE L τ := by
  obtain ⟨hτ, C, hC, hb⟩ := h
  exact ⟨hτ, C, hC, fun n hn ↦
    (Nat.cast_le.mpr (squareMatrixRankSequence_le_of_ringHom φ n)).trans (hb n hn)⟩

/-- **Base change.**  The exponent does not increase along a ring homomorphism: `omega L ≤ omega K`
whenever there is a ring homomorphism `K →+* L`. -/
theorem omega_le_of_ringHom (φ : K →+* L) : omega L ≤ omega K := by
  refine le_of_forall_pos_le_add fun ε hε ↦ ?_
  exact omega_le L (matrixExponentLE_of_ringHom φ
    (matrixExponentLE_of_omega_lt K (lt_add_of_pos_right _ hε)))

/-- Base change for an algebra: `omega L ≤ omega K` when `L` is a `K`-algebra. -/
theorem omega_le_of_algebra (K : Type u) (L : Type u') [CommSemiring K] [CommSemiring L]
    [Algebra K L] : omega L ≤ omega K :=
  omega_le_of_ringHom (algebraMap K L)

/-- The natural numbers are the hardest commutative semiring: `omega K ≤ omega ℕ`. -/
theorem omega_le_omega_nat (K : Type u) [CommSemiring K] : omega K ≤ omega ℕ :=
  omega_le_of_ringHom (Nat.castRingHom K)

/-- The integers are the hardest commutative ring: `omega K ≤ omega ℤ`. -/
theorem omega_le_omega_int (K : Type u) [CommRing K] : omega K ≤ omega ℤ :=
  omega_le_of_ringHom (Int.castRingHom K)

end BaseChange

/-! ### Descent along a finite extension -/

section FiniteDescent

variable {F : Type u} {L : Type u'} [Field F] [Field L] [Algebra F L]

/-- **Descent of a bilinear algorithm along a finite field extension.**

Let `L / F` be a finite extension of degree `d`, and let `c` be a coefficient array over `F`.
A bilinear algorithm of length `r` over `L` computing the base change of `c` yields a bilinear
algorithm of length `r · d · d` over `F` computing `c`.

The new algorithm is indexed by a term `t` and two basis indices `a`, `a'`: its linear forms are
the `a`-th coordinate of `f t` and the `a'`-th coordinate of `g t` in an `F`-basis `b` of `L`, and
its output vector is `φ (w t · b a · b a')` for an `F`-linear functional `φ` with `φ 1 = 1`. -/
theorem BilinearAlgorithm.exists_computes_of_finiteDimensional [FiniteDimensional F L]
    {ι κ μ : Type v} [Fintype ι] [Fintype κ] {r : ℕ}
    (c : ι → κ → μ → F) (A : BilinearAlgorithm L ι κ μ r)
    (hA : A.Computes (bilinearMapOfCoeff fun i j m ↦ algebraMap F L (c i j m))) :
    ∃ A' : BilinearAlgorithm F ι κ μ (r * finrank F L * finrank F L),
      A'.Computes (bilinearMapOfCoeff c) := by
  classical
  set d := finrank F L with hd
  let b : Basis (Fin d) F L := finBasis F L
  obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_eq_one F (one_ne_zero : (1 : L) ≠ 0)
  let e : Fin (r * d * d) ≃ (Fin r × Fin d) × Fin d :=
    finProdFinEquiv.symm.trans (Equiv.prodCongr finProdFinEquiv.symm (Equiv.refl _))
  refine ⟨⟨fun s i ↦ b.repr (A.f (e s).1.1 i) (e s).1.2,
    fun s j ↦ b.repr (A.g (e s).1.1 j) (e s).2,
    fun s m ↦ φ (A.w (e s).1.1 m * b (e s).1.2 * b (e s).2)⟩, ?_⟩
  rw [computes_iff_coeff] at hA ⊢
  intro i j m
  have hc : c i j m = φ (algebraMap F L (c i j m)) := by
    rw [Algebra.algebraMap_eq_smul_one, map_smul, hφ, smul_eq_mul, mul_one]
  rw [hc, hA i j m, map_sum, ← e.symm.sum_comp]
  simp only [Equiv.apply_symm_apply, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun t _ ↦ ?_
  have hterm : A.w t m * A.f t i * A.g t j =
      ∑ a, ∑ a', (b.repr (A.f t i) a * b.repr (A.g t j) a') • (A.w t m * b a * b a') := by
    conv_lhs => rw [← b.sum_repr (A.f t i), ← b.sum_repr (A.g t j)]
    simp only [Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ ↦ Finset.sum_congr rfl fun a' _ ↦ ?_
    simp only [Algebra.smul_def, map_mul]
    ring
  rw [hterm, map_sum]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun a' _ ↦ ?_
  rw [map_smul, smul_eq_mul]
  ring

end FiniteDescent

/-! ### Descent along an algebraic extension -/

section AlgebraicDescent

variable {F : Type u} {E : Type u'} [Field F] [Field E] [Algebra F E] [Algebra.IsAlgebraic F E]

/-- A bilinear algorithm over an algebraic extension `E / F` that computes the base change of a
coefficient array over `F` already lives over a finite intermediate extension: the one generated
by its finitely many coefficients. -/
theorem BilinearAlgorithm.exists_intermediateField_computes
    {ι κ μ : Type v} [Fintype ι] [Fintype κ] [Finite μ] {r : ℕ}
    (c : ι → κ → μ → F) (A : BilinearAlgorithm E ι κ μ r)
    (hA : A.Computes (bilinearMapOfCoeff fun i j m ↦ algebraMap F E (c i j m))) :
    ∃ L : IntermediateField F E, FiniteDimensional F L ∧
      ∃ A' : BilinearAlgorithm L ι κ μ r,
        A'.Computes (bilinearMapOfCoeff fun i j m ↦ algebraMap F L (c i j m)) := by
  classical
  let S : Set E := (Set.range fun q : Fin r × ι ↦ A.f q.1 q.2) ∪
    (Set.range fun q : Fin r × κ ↦ A.g q.1 q.2) ∪ (Set.range fun q : Fin r × μ ↦ A.w q.1 q.2)
  have hSfin : S.Finite :=
    ((Set.finite_range _).union (Set.finite_range _)).union (Set.finite_range _)
  haveI : Finite S := hSfin.to_subtype
  have hfin : FiniteDimensional F (IntermediateField.adjoin F S) :=
    IntermediateField.finiteDimensional_adjoin fun x _ ↦ Algebra.IsIntegral.isIntegral x
  have hS : S ⊆ IntermediateField.adjoin F S := IntermediateField.subset_adjoin F S
  have hf : ∀ t i, A.f t i ∈ IntermediateField.adjoin F S := fun t i ↦
    hS (Or.inl (Or.inl ⟨(t, i), rfl⟩))
  have hg : ∀ t j, A.g t j ∈ IntermediateField.adjoin F S := fun t j ↦
    hS (Or.inl (Or.inr ⟨(t, j), rfl⟩))
  have hw : ∀ t m, A.w t m ∈ IntermediateField.adjoin F S := fun t m ↦
    hS (Or.inr ⟨(t, m), rfl⟩)
  refine ⟨IntermediateField.adjoin F S, hfin,
    ⟨fun t i ↦ ⟨A.f t i, hf t i⟩, fun t j ↦ ⟨A.g t j, hg t j⟩, fun t m ↦ ⟨A.w t m, hw t m⟩⟩, ?_⟩
  rw [computes_iff_coeff] at hA ⊢
  intro i j m
  apply Subtype.ext
  have h := hA i j m
  simpa using h

/-- **Powers of a decomposition over an algebraic extension descend with a bounded overhead.**

If `⟨n,n,n⟩` has rank at most `r` over an algebraic extension `E` of `F`, then there is a degree
`d ≥ 1` such that `⟨nᵏ,nᵏ,nᵏ⟩` has rank at most `rᵏ · d · d` over `F` for every `k`.  The degree
is that of the finite extension generated by one decomposition of `⟨n,n,n⟩`; it does not grow with
`k`, because the powers of that decomposition have coefficients in the same finite extension. -/
theorem rankLE_matrixMultiplication_pow_of_isAlgebraic {n r : ℕ}
    (h : RankLE r (matrixMultiplication (K := E) n n n)) :
    ∃ d : ℕ, 0 < d ∧ ∀ k : ℕ,
      RankLE (r ^ k * d * d) (matrixMultiplication (K := F) (n ^ k) (n ^ k) (n ^ k)) := by
  obtain ⟨A, hA⟩ := (matrixMultiplication_rankLE_iff_exists_algorithm (K := E) n n n r).mp h
  rw [matrixProductMap_eq_bilinearMapOfCoeff, ← map_mmCoeff (algebraMap F E)] at hA
  obtain ⟨L, hfin, A', hA'⟩ :=
    BilinearAlgorithm.exists_intermediateField_computes (mmCoeff (K := F) n n n) A hA
  have hL : RankLE r (matrixMultiplication (K := L) n n n) := by
    refine (matrixMultiplication_rankLE_iff_exists_algorithm (K := L) n n n r).mpr ⟨A', ?_⟩
    rw [matrixProductMap_eq_bilinearMapOfCoeff, ← map_mmCoeff (algebraMap F L)]
    exact hA'
  refine ⟨finrank F L, Module.finrank_pos, fun k ↦ ?_⟩
  obtain ⟨B, hB⟩ := (matrixMultiplication_rankLE_iff_exists_algorithm (K := L)
    (n ^ k) (n ^ k) (n ^ k) (r ^ k)).mp (hL.matrixMultiplication_pow k)
  rw [matrixProductMap_eq_bilinearMapOfCoeff, ← map_mmCoeff (algebraMap F L)] at hB
  obtain ⟨B', hB'⟩ := BilinearAlgorithm.exists_computes_of_finiteDimensional
    (mmCoeff (K := F) (n ^ k) (n ^ k) (n ^ k)) B hB
  refine (matrixMultiplication_rankLE_iff_exists_algorithm (K := F)
    (n ^ k) (n ^ k) (n ^ k) _).mpr ⟨B', ?_⟩
  rw [matrixProductMap_eq_bilinearMapOfCoeff]
  exact hB'

/-- If `aᵏ ≤ C · bᵏ` for every `k`, then `a ≤ b`: a constant factor does not survive `k`-th
roots. -/
theorem le_of_forall_pow_le_mul_pow {a b C : ℝ} (hb : 0 < b)
    (h : ∀ k : ℕ, a ^ k ≤ C * b ^ k) : a ≤ b := by
  by_contra hlt
  have hratio : 1 < a / b := (one_lt_div hb).mpr (not_le.mp hlt)
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt C hratio
  have hbk : 0 < b ^ k := pow_pos hb k
  have h1 : (a / b) ^ k ≤ C := by
    rw [div_pow, div_le_iff₀ hbk]
    exact h k
  exact absurd hk (not_lt.mpr h1)

/-- **A rank certificate over an algebraic extension bounds the exponent of the base field**:
if `⟨n,n,n⟩` has rank at most `r` over an algebraic extension of `F`, then `n ^ omega F ≤ r`. -/
theorem rpow_omega_le_of_rankLE_of_isAlgebraic {n r : ℕ} (hn : 1 < n) (hr : 1 ≤ r)
    (h : RankLE r (matrixMultiplication (K := E) n n n)) :
    (n : ℝ) ^ omega F ≤ r := by
  obtain ⟨d, hd, hpow⟩ := rankLE_matrixMultiplication_pow_of_isAlgebraic (F := F) h
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  refine le_of_forall_pow_le_mul_pow (C := (d : ℝ) * d) hr0 fun k ↦ ?_
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp only [pow_zero, mul_one]
    nlinarith
  have hq : 1 < n ^ k := Nat.one_lt_pow hk.ne' hn
  have hR : 1 ≤ r ^ k * d * d :=
    Nat.succ_le_of_lt (Nat.mul_pos (Nat.mul_pos (pow_pos hr k) hd) hd)
  have h1 := rpow_omega_le_rank_of_rankLE F hq hR (hpow k)
  calc ((n : ℝ) ^ omega F) ^ k = ((n ^ k : ℕ) : ℝ) ^ omega F := by
        rw [Nat.cast_pow, ← Real.rpow_natCast, ← Real.rpow_mul hn0, mul_comm,
          Real.rpow_mul hn0, Real.rpow_natCast]
    _ ≤ ((r ^ k * d * d : ℕ) : ℝ) := h1
    _ = (d : ℝ) * d * (r : ℝ) ^ k := by push_cast; ring

/-- **Descent.**  The exponent does not increase when passing from an algebraic extension to the
base field: `omega F ≤ omega E` for every algebraic field extension `E / F`. -/
theorem omega_le_of_isAlgebraic (F : Type u) (E : Type u') [Field F] [Field E] [Algebra F E]
    [Algebra.IsAlgebraic F E] : omega F ≤ omega E := by
  refine le_of_forall_pos_le_add fun ε hε ↦ ?_
  obtain ⟨-, C, hC, hb⟩ :=
    matrixExponentLE_of_omega_lt E (lt_add_of_pos_right (omega E) (half_pos hε))
  obtain ⟨n, hn2, hnC⟩ : ∃ n : ℕ, 2 ≤ n ∧ C ≤ (n : ℝ) ^ (ε / 2) := by
    have htend := (tendsto_rpow_atTop (half_pos hε)).comp tendsto_natCast_atTop_atTop
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (htend.eventually_ge_atTop C)
    exact ⟨max N 2, le_max_right _ _, hN _ (le_max_left _ _)⟩
  have hn1 : 1 < n := by omega
  have hnR : (1 : ℝ) < n := by exact_mod_cast hn1
  have hn0 : (0 : ℝ) < n := zero_lt_one.trans hnR
  have hr1 : 1 ≤ squareMatrixRankSequence E n :=
    (Nat.one_le_pow 2 n (by omega)).trans (square_le_squareMatrixRankSequence E n)
  have h1 : (n : ℝ) ^ omega F ≤ squareMatrixRankSequence E n :=
    rpow_omega_le_of_rankLE_of_isAlgebraic hn1 hr1 (rank_spec _)
  have h2 : (squareMatrixRankSequence E n : ℝ) ≤ (n : ℝ) ^ (omega E + ε) := by
    calc (squareMatrixRankSequence E n : ℝ) ≤ C * (n : ℝ) ^ (omega E + ε / 2) := hb n (by omega)
      _ ≤ (n : ℝ) ^ (ε / 2) * (n : ℝ) ^ (omega E + ε / 2) :=
        mul_le_mul_of_nonneg_right hnC (Real.rpow_nonneg hn0.le _)
      _ = (n : ℝ) ^ (omega E + ε) := by
        rw [← Real.rpow_add hn0]
        congr 1
        ring
  exact (Real.rpow_le_rpow_left_iff hnR).mp (h1.trans h2)

/-- **The exponent is invariant under algebraic field extensions.** -/
theorem omega_eq_of_isAlgebraic (F : Type u) (E : Type u') [Field F] [Field E] [Algebra F E]
    [Algebra.IsAlgebraic F E] : omega E = omega F :=
  le_antisymm (omega_le_of_algebra F E) (omega_le_of_isAlgebraic F E)

end AlgebraicDescent

/-! ### Consequences -/

section Consequences

/-- A field and its algebraic closure have the same exponent. -/
theorem omega_algebraicClosure (F : Type u) [Field F] : omega (AlgebraicClosure F) = omega F :=
  omega_eq_of_isAlgebraic F (AlgebraicClosure F)

/-- To bound the exponent over every field it suffices to bound it over algebraically closed
fields. -/
theorem omega_le_of_forall_isAlgClosed {τ : ℝ}
    (h : ∀ (E : Type u) [Field E] [IsAlgClosed E], omega E ≤ τ) (F : Type u) [Field F] :
    omega F ≤ τ :=
  (omega_algebraicClosure F).symm.le.trans (h (AlgebraicClosure F))

/-- All finite fields of characteristic `p` have the same exponent as the prime field. -/
theorem omega_eq_omega_zmod_of_finite (p : ℕ) [Fact p.Prime] (K : Type u) [Field K] [CharP K p]
    [Finite K] : omega K = omega (ZMod p) := by
  letI : Algebra (ZMod p) K := ZMod.algebra K p
  haveI : Module.Finite (ZMod p) K := Module.Finite.of_finite
  haveI : Algebra.IsAlgebraic (ZMod p) K := Algebra.IsAlgebraic.of_finite (ZMod p) K
  exact omega_eq_of_isAlgebraic (ZMod p) K

end Consequences

end AlgebraicComplexity
