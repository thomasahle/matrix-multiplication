/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication
import AlgebraicComplexity.Tensor.Concise
import AlgebraicComplexity.Tensor.KoszulFlattening
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# The Koszul flattening of `⟨2,2,2⟩`

This is the flagship client of `Tensor/KoszulFlattening.lean`: an explicit, kernel-checked
computation of the `p = 1` Koszul flattening of the `2 × 2` matrix-multiplication tensor, and the
lower bound it certifies.

## Main results

For the first Koszul flattening

```text
  Φ : (⋀^1 K^4) ⊗ (K^4)*  →  (⋀^2 K^4) ⊗ K^4
```

of `⟨2,2,2⟩`:

* `koszulTwoArg` and `koszulTwoTest`: sixteen explicit arguments of `Φ` and sixteen explicit
  functionals on its target;
* `koszulTwoTest_koszulFlattening`: they form a biorthogonal system,
  `test s (Φ (arg t)) = if s = t then 1 else 0`;
* `linearIndependent_koszulFlattening_two`: hence the sixteen values `Φ (arg t)` are linearly
  independent, so `Φ` has rank at least `16`;
* `finrank_mmSpace_two_X`: the `X` leg of `⟨2,2,2⟩` has dimension `4`;
* `six_le_rank_matrixMultiplication_two_koszul`: consequently `rank ⟨2,2,2⟩ ≥ 6` over every
  field, because a rank-`r` certificate caps the number of independent values of `Φ` at
  `r * binom(4-1, 1) = 3r`, and `3 * 5 = 15 < 16`.

## The certificate

The `X`, `Y`, `Z` legs of `⟨2,2,2⟩` are all `4`-dimensional, with standard bases indexed by
`(i,j)`, `(j,k)` and `(k,i)` in `Fin 2 × Fin 2`.  For an index pair
`t = ((i₀,j₀),(j₁,k₁))` put

```text
  arg t := (e^X_{i₀j₀}) ⊗ (e^Y_{j₁k₁})*   ∈  (⋀^1 V_X) ⊗ V_Y*.
```

Unwinding the definition of the matrix-multiplication tensor, the `Y` contraction against
`(e^Y_{j₁k₁})*` keeps only the summands with `(j,k) = (j₁,k₁)`, so

```text
  Φ (arg t) = ∑_{i} (e^X_{i j₁} ∧ e^X_{i₀ j₀}) ⊗ e^Z_{k₁ i}.
```

Against this family we test with the `16` functionals

```text
  test s := ⟨(e^X_{a+1, c})* ∧ (e^X_{a b})*, (e^Z_{d, a+1})*⟩,   s = ((a,b),(c,d)),
```

where `a + 1` is the *other* row index in `Fin 2` and the first factor is the standard pairing
of `⋀^2 (V_X)*` with `⋀^2 V_X` (`exteriorPower.alternatingMapToDual`, a `2 × 2` determinant).
The `Z`-functional selects the summand `i = a + 1`, and in the remaining `2 × 2` determinant the
entry `(e^X_{ab})*(e^X_{a+1, j₁})` vanishes because `a ≠ a + 1` in `Fin 2`.  What survives is
exactly `[c = j₁] · [(a,b) = (i₀,j₀)] · [d = k₁]`, i.e. `test s (Φ (arg t)) = [s = t]`.  A
biorthogonal system is linearly independent, so the `16` vectors `Φ (arg t)` are independent,
i.e. `Φ` has rank at least `16` (in fact exactly `16`: its source has dimension `16`).

This strictly beats the classical flattening bound: the `X`-flattening of `⟨2,2,2⟩` has rank `4`,
and `Tensor/Concise.lean` therefore certifies only `rank ≥ 4`.  That the classical flattening
really is the `p = 0` case of the Koszul one is `Tensor.contractX_eq_sliceY` below.

## Three independent routes to `rank ⟨2,2,2⟩`

1. *substitution / row-kill* — `Examples/BlaeserLowerBound.lean` reaches `6`; the `5` and `6` of
   `Examples/SmallMatrixLowerBounds.lean` are its one- and two-kill specializations, not a
   separate argument;
2. *Koszul flattening* — this file, `6` again, and the point is that a single flattening-style
   invariant already gets there;
3. *trilinear substitution with sandwich normalization* — `Examples/WinogradLowerBound.lean`, the
   exact value `7`, the only route that reaches it.

## Scope: rank, not yet border rank

The Landsberg–Ottaviani theorem this construction belongs to is about **border** rank:
`borderRank ⟨n,n,n⟩ ≥ 2n² − n`, whose `n = 2` case is `borderRank ⟨2,2,2⟩ ≥ 6`.  The file is
named for that destination, but what is proved here is the *exact-rank* bound.  The missing step
is **not** in this file: everything below (the flattening, the explicit `16 × 16` biorthogonal
system, the arithmetic) is exactly what the border argument needs.  What is missing is a
`K[ε]`-module generation lemma inside the reusable layer; the obstruction is documented in full
in the module doc of `AlgebraicComplexity/Tensor/KoszulFlattening.lean`.  When that lemma lands,
`six_le_rank_matrixMultiplication_two_koszul` upgrades to the border statement with no change to
the certificate below.

## Source

J. M. Landsberg and G. Ottaviani, *New lower bounds for the border rank of matrix
multiplication*, Theory of Computing **11** (2015), 285–298 (arXiv:1112.6007).

## Layer placement

Layer 3 (`AlgebraicComplexity/MatrixMultiplication/`): it names a matrix-multiplication tensor
and a numerical bound, so it may not live in the tensor layer.  It imports
`AlgebraicComplexity.MatrixMultiplication`, the Koszul flattening leaf, and `Tensor/Concise` —
the last only to host `Tensor.contractX_eq_sliceY`, the bridge that identifies the `p = 0` Koszul
slice with the classical contraction.  `Tensor/KoszulFlattening.lean` deliberately does not
import `Tensor/Concise` (its bound is independent of conciseness), so the bridge cannot live
there; a two-declaration leaf `Tensor/KoszulFlatteningConcise.lean` would be its proper home once
the umbrella may be extended.
-/

namespace AlgebraicComplexity

open Tensor

universe u

variable {K : Type u} [Field K]

/-- Every leg space of a matrix-multiplication tensor is finite dimensional. -/
instance mmSpaceFiniteDimensional {m n p : ℕ} (i : Leg) :
    FiniteDimensional K (MMSpace K m n p i) := by
  cases i <;> infer_instance

/-! ### A functional on a tensor product -/

section PairDual

variable {M : Type*} {N : Type*} [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]

/-- The linear functional `m ⊗ n ↦ φ m * h n` on `M ⊗ N` determined by functionals on the two
factors. -/
noncomputable def pairDual (φ : Module.Dual K M) (h : Module.Dual K N) :
    Module.Dual K (TensorProduct K M N) :=
  TensorProduct.dualDistrib K M N (φ ⊗ₜ[K] h)

/-- Value of `pairDual` on an elementary tensor. -/
@[simp] theorem pairDual_tmul (φ : Module.Dual K M) (h : Module.Dual K N)
    (m : M) (n : N) : pairDual φ h (m ⊗ₜ[K] n) = φ m * h n :=
  TensorProduct.dualDistrib_apply φ h m n

end PairDual

/-! ### The `p = 0` Koszul slice is the classical contraction

`Tensor/KoszulFlattening.lean` states in prose that for `p = 0` the Koszul flattening is the
classical `X`-flattening, but proves no bridge, because it deliberately does not import
`Tensor/Concise.lean`.  This is that bridge; it is homed here, the first file that imports both.
-/

section KoszulSlice

variable {V : Leg → Type u} [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]

/-- The classical `X`-retaining contraction is the `Z`-contraction of the Koszul `Y`-slice: for a
`Y`-covector `fy` and a `Z`-covector `fz`,

```text
  contractX fy fz T  =  (id ⊗ fz) (sliceY fy T)   in   V_X ⊗ K ≅ V_X.
```

This is the precise content of the `p = 0` remark in the module doc of
`Tensor/KoszulFlattening.lean`: `sliceY` retains the whole `Z` leg, and contracting that leg
against `fz` recovers `contractX`.

Proof sketch: both sides are linear in `T`, so it suffices to check them on pure tensors, where
each is `fy (x .Y) * fz (x .Z) • x .X` after reassociating the scalars. -/
theorem Tensor.contractX_eq_sliceY (fy : V .Y →ₗ[K] K) (fz : V .Z →ₗ[K] K) (T : Tensor3 K V) :
    contractX fy fz T =
      TensorProduct.rid K (V .X) (LinearMap.lTensor (V .X) fz (sliceY fy T)) := by
  refine PiTensorProduct.induction_on T ?_ ?_
  · intro a x
    simp [smul_smul, mul_assoc]
  · intro T₁ T₂ h₁ h₂
    simp [h₁, h₂]

end KoszulSlice

/-! ### The explicit `⟨2,2,2⟩` certificate -/

/-- Index type of the `16` test arguments and test functionals: an `X`-coordinate paired with a
`Y`-coordinate. -/
abbrev KoszulTwoIndex := (Fin 2 × Fin 2) × (Fin 2 × Fin 2)

/-- The test argument `e^X_{i₀j₀} ⊗ (e^Y_{j₁k₁})*` of the first Koszul flattening of `⟨2,2,2⟩`,
indexed by `t = ((i₀,j₀),(j₁,k₁))`. -/
noncomputable def koszulTwoArg (t : KoszulTwoIndex) :
    TensorProduct K (⋀[K]^1 (MMSpace K 2 2 2 .X)) (Module.Dual K (MMSpace K 2 2 2 .Y)) :=
  (exteriorPower.ιMulti K 1 ![(Pi.single t.1 1 : MMSpace K 2 2 2 .X)]) ⊗ₜ[K]
    LinearMap.proj (R := K) t.2

/-- The test functional dual to `koszulTwoArg`, indexed by `s = ((a,b),(c,d))`: the `⋀²`-pairing
against `(e^X_{a+1,c})* ∧ (e^X_{a,b})*` tensored with the `Z`-coordinate `(e^Z_{d,a+1})*`.
Here `a + 1` is the row index of `Fin 2` other than `a`. -/
noncomputable def koszulTwoTest (s : KoszulTwoIndex) :
    Module.Dual K
      (TensorProduct K (⋀[K]^2 (MMSpace K 2 2 2 .X)) (MMSpace K 2 2 2 .Z)) :=
  pairDual
    (exteriorPower.alternatingMapToDual K (MMSpace K 2 2 2 .X) 2
      ![LinearMap.proj (R := K) (s.1.1 + 1, s.2.1), LinearMap.proj (R := K) s.1])
    (LinearMap.proj (R := K) (s.2.2, s.1.1 + 1))

/-- Summing a two-coordinate Kronecker delta selects its unique indexed value. -/
private theorem sum_pair_indicator
    {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (target : α × β) (f : α → β → K) :
    (∑ x, ∑ y, (if target = (x, y) then 1 else 0) * f x y) =
      f target.1 target.2 := by
  classical
  calc
    _ = ∑ y, (if target = (target.1, y) then 1 else 0) * f target.1 y := by
      apply Finset.sum_eq_single target.1
      · intro x _ hx
        simp [Prod.ext_iff, hx, eq_comm]
      · simp
    _ = (if target = (target.1, target.2) then 1 else 0) *
        f target.1 target.2 := by
      apply Finset.sum_eq_single target.2
      · intro y _ hy
        simp [Prod.ext_iff, hy, eq_comm]
      · simp
    _ = f target.1 target.2 := by simp

/-- A Kronecker delta on a pair with one fixed coordinate either selects one summand or vanishes. -/
private theorem sum_fixed_pair_indicator
    {α β : Type*} [DecidableEq α] [Fintype β] [DecidableEq β]
    (left targetLeft : α) (targetRight : β) (f : β → K) :
    (∑ x, f x * (if (left, targetRight) = (targetLeft, x) then 1 else 0)) =
      if left = targetLeft then f targetRight else 0 := by
  by_cases h : left = targetLeft
  · subst targetLeft
    simp
  · simp [h]

/-- Reading off the second entry of a two-element vector built with `Fin.cons`. -/
private theorem fin_cons_one {α : Type*} (x y : α) :
    (Fin.cons x ![y] : Fin 2 → α) 1 = y := rfl

/-- **The certificate.**  The test functionals and the images of the test arguments form a
biorthogonal system for the first Koszul flattening of `⟨2,2,2⟩`:
`test s (Φ (arg t)) = 1` when `s = t` and `0` otherwise.

Proof sketch: expand `⟨2,2,2⟩` as the sum of its eight pure summands and evaluate.  The `Y`
covector `(e^Y_{j₁k₁})*` keeps only the summands with `(j,k) = (j₁,k₁)`, leaving
`∑_i (e^X_{i j₁} ∧ e^X_{i₀ j₀}) ⊗ e^Z_{k₁ i}`; the `Z` covector `(e^Z_{d,a+1})*` keeps only
`i = a + 1` (and forces `d = k₁`); and the `⋀²` pairing is the `2 × 2` determinant
`(e^X_{a+1,c})*(u) · (e^X_{ab})*(v) − (e^X_{ab})*(u) · (e^X_{a+1,c})*(v)` whose second product
vanishes because `a ≠ a + 1` in `Fin 2`.  What survives is `[c = j₁]·[(a,b) = (i₀,j₀)]`.  Since
coordinate projections are Kronecker deltas, `simp` collapses the three finite sums symbolically;
the only residual finite fact is that adding one has no fixed point in `Fin 2`. -/
theorem koszulTwoTest_koszulFlattening (s t : KoszulTwoIndex) :
    koszulTwoTest (K := K) s
        (koszulFlattening 1 (matrixMultiplication (K := K) 2 2 2) (koszulTwoArg t)) =
      if s = t then 1 else 0 := by
  classical
  obtain ⟨⟨a, b⟩, ⟨c, d⟩⟩ := s
  obtain ⟨⟨i₀, j₀⟩, ⟨j₁, k₁⟩⟩ := t
  rw [matrixMultiplication, map_sum, LinearMap.sum_apply, map_sum]
  simp only [koszulTwoArg, koszulTwoTest, mmTermOfTriple, mmTerm,
    koszulFlattening_pure_tmul, wedgeLeft_apply_ιMulti, map_smul, smul_eq_mul,
    pairDual_tmul, exteriorPower.alternatingMapToDual_apply_ιMulti, Matrix.det_fin_two,
    Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Fin.cons_zero,
    fin_cons_one, LinearMap.proj_apply, Pi.single_apply,
    Fintype.sum_prod_type]
  simp_rw [sum_pair_indicator]
  rw [sum_fixed_pair_indicator]
  simp only [Prod.ext_iff]
  by_cases hd : d = k₁ <;>
    by_cases hab : a = i₀ ∧ b = j₀ <;>
      by_cases hc : c = j₁ <;> simp [hd, hab, hc]

/-- The sixteen values `Φ (arg t)` of the first Koszul flattening of `⟨2,2,2⟩` are linearly
independent.

Proof sketch: assemble the sixteen test functionals into one linear map into the coordinate
space `KoszulTwoIndex → K`.  By `koszulTwoTest_koszulFlattening` it carries the family
`t ↦ Φ (arg t)` to the standard basis `t ↦ Pi.single t 1`, which is linearly independent, and a
family whose image under a linear map is independent is itself independent.

Going through the coordinate space is deliberate: applying a biorthogonality criterion directly
in `⋀^2 V_X ⊗ V_Z` would force Lean to reconcile that space's `AddCommMonoid`/`AddCommGroup`
instance diamond, which is prohibitively slow. -/
theorem linearIndependent_koszulFlattening_two :
    LinearIndependent K fun t : KoszulTwoIndex ↦
      koszulFlattening 1 (matrixMultiplication (K := K) 2 2 2) (koszulTwoArg t) := by
  classical
  have hstd : LinearIndependent K fun t : KoszulTwoIndex ↦
      (Pi.single t 1 : KoszulTwoIndex → K) := by
    refine LinearIndependent.of_pairwise_dual_eq_zero_one _
      (fun s ↦ LinearMap.proj (R := K) s) ?_ ?_
    · intro s t hst
      simp [hst]
    · intro s
      simp
  have hEq : (fun t : KoszulTwoIndex ↦
      (LinearMap.pi (fun s : KoszulTwoIndex ↦ koszulTwoTest (K := K) s))
        (koszulFlattening 1 (matrixMultiplication (K := K) 2 2 2) (koszulTwoArg t))) =
      fun t : KoszulTwoIndex ↦ (Pi.single t 1 : KoszulTwoIndex → K) := by
    funext t
    funext s
    simp only [LinearMap.pi_apply, Pi.single_apply]
    exact koszulTwoTest_koszulFlattening s t
  refine LinearIndependent.of_comp
    (LinearMap.pi (fun s : KoszulTwoIndex ↦ koszulTwoTest (K := K) s)) ?_
  rw [Function.comp_def, hEq]
  exact hstd

/-- The `X` leg of `⟨2,2,2⟩` is four dimensional. -/
theorem finrank_mmSpace_two_X :
    Module.finrank K (MMSpace K 2 2 2 .X) = 4 := by
  show Module.finrank K (Fin 2 × Fin 2 → K) = 4
  rw [Module.finrank_pi K]
  simp

/-- **The Landsberg–Ottaviani bound at `n = 2`, in its exact-rank form.**  Over every field,
`rank ⟨2,2,2⟩ ≥ 6`.

Proof sketch: the `p = 1` Koszul flattening of `⟨2,2,2⟩` has `16` linearly independent values
(`linearIndependent_koszulFlattening_two`), while a rank-`r` certificate caps that number at
`r * binom (4 - 1, 1) = 3r` (`RankLE.card_le_of_linearIndependent_koszulFlattening`).  Since
`3 * 5 = 15 < 16`, no rank certificate of length five exists. -/
theorem six_le_rank_matrixMultiplication_two_koszul :
    6 ≤ rank (matrixMultiplication (K := K) 2 2 2) := by
  have hcard : Fintype.card KoszulTwoIndex = 16 := by decide
  have h5 : 5 < rank (matrixMultiplication (K := K) 2 2 2) := by
    refine lt_rank_of_linearIndependent_koszulFlattening (r := 5) (p := 1)
      koszulTwoArg linearIndependent_koszulFlattening_two ?_
    rw [finrank_mmSpace_two_X, hcard]
    norm_num
  omega

end AlgebraicComplexity
