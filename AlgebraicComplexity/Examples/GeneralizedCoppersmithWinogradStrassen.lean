/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/
import AlgebraicComplexity.Examples.GeneralizedCoppersmithWinograd
import AlgebraicComplexity.Tensor.StrassenEquations

/-!
# The border-rank dichotomy for generalized Coppersmith--Winograd tensors

Layer 4 (`AlgebraicComplexity/Examples/`).  This file turns the computation recorded in the module
doc of `Examples/GeneralizedCoppersmithWinogradBorderRank.lean` into a theorem: the family
`CW_q^σ` of [AlmanVassilevskaWilliams2018, Definition 3.1] has *minimal* border rank `q + 2` only
if the twisting permutation `σ` is an involution.

## The slices

In the coordinates of Definition 3.1 the `Z`-slices of `CW_q^σ` are

```text
M_{z_0} = E_{0,q+1} + E_{q+1,0} + ∑_i E_{i,σ i},   M_{z_i} = E_{i,0} + E_{0,i},
M_{z_{q+1}} = E_{0,0},
```

so `M_{z_0}` is the permutation matrix of `π = (0 ↦ q+1, q+1 ↦ 0, i ↦ σ i)`
(`genCWSlicePerm`), in particular invertible with inverse the permutation matrix of `π⁻¹`
(`genCWSliceZeroInv`).  The tensor is therefore 1-generic and Strassen's equations apply.  The
normalized slices `A_z = M_{z_0}⁻¹ M_z` are

```text
A_{z_0} = 1,   A_{z_i} = E_{σ i, 0} + E_{q+1, i},   A_{z_{q+1}} = E_{q+1, 0},
```

(`genCWNormalizedSlice_zero`, `genCWNormalizedSlice_middle`, `genCWNormalizedSlice_last`), whence

```text
A_{z_i} A_{z_j} = [i = σ j] · E_{q+1,0},      A_{z_i} A_{z_{q+1}} = A_{z_{q+1}} A_{z_i} = 0,
```

so that `[A_{z_i}, A_{z_j}] = ([i = σ j] − [j = σ i]) · E_{q+1,0}` and *all* commutators vanish
exactly when `σ` is an involution.

## Main results

* `genCW_normalizedSlices_commute_of_involutive`: the positive half.  For an involutive `σ` all
  normalized slices commute — consistent with `genCW_borderRankLE_refl`, which proves
  `R̲(CW_q^{id}) ≤ q + 2` for the identity permutation.
* `not_borderRankLE_genCW_of_not_involutive`: the negative half.  If `σ` is *not* an involution,
  then `CW_q^σ` has **no** border-rank certificate of size `q + 2`, over any nontrivial
  commutative ring.
* `borderRank_genCW_ge_of_not_involutive`: the numerical form, `R̲(CW_q^σ) ≥ q + 3`.
* `not_borderRankLE_genCW_threeCycle`: the smallest concrete instance, a three-cycle at `q = 3`.

Together with border-rank conciseness (`R̲ ≥ q + 2`, `Tensor/BorderConcise.lean`) this is a genuine
dichotomy for AVW's family: minimal border rank is possible only in the involutive case.

## Position in the library

Layer 4.  It imports `Examples/GeneralizedCoppersmithWinograd.lean` for the tensor and its
coefficient table, and the layer-1 `Tensor/StrassenEquations.lean` for the equations themselves.
Nothing here is imported by a lower layer.

## References

* [AlmanVassilevskaWilliams2018] J. Alman and V. Vassilevska Williams, *Limits on all known (and
  some unknown) approaches to matrix multiplication*, arXiv:1810.08671; Definition 3.1.
* [Strassen1983] V. Strassen, *Rank and optimal computation of generic tensors*, Linear Algebra
  Appl. 52/53 (1983) 645--685.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor

universe u v

/-! ## The permutation underlying the `z_0`-slice -/

section Perm

variable {μ : Type v}

/-- The permutation `π = (0 ↦ q+1, q+1 ↦ 0, i ↦ σ i)` of the coordinate set of `CW_q^σ`.  The
`z_0`-slice of `CW_q^σ` is its permutation matrix. -/
def genCWSlicePerm (σ : Equiv.Perm μ) : Equiv.Perm (GenCWIndex μ) where
  toFun a := match a with
    | .zero => .last
    | .middle i => .middle (σ i)
    | .last => .zero
  invFun a := match a with
    | .zero => .last
    | .middle i => .middle (σ.symm i)
    | .last => .zero
  left_inv a := by cases a <;> simp
  right_inv a := by cases a <;> simp

@[simp] theorem genCWSlicePerm_zero (σ : Equiv.Perm μ) :
    genCWSlicePerm σ (GenCWIndex.zero : GenCWIndex μ) = .last := rfl

@[simp] theorem genCWSlicePerm_middle (σ : Equiv.Perm μ) (i : μ) :
    genCWSlicePerm σ (GenCWIndex.middle i) = .middle (σ i) := rfl

@[simp] theorem genCWSlicePerm_last (σ : Equiv.Perm μ) :
    genCWSlicePerm σ (GenCWIndex.last : GenCWIndex μ) = .zero := rfl

@[simp] theorem genCWSlicePerm_symm_zero (σ : Equiv.Perm μ) :
    (genCWSlicePerm σ).symm (GenCWIndex.zero : GenCWIndex μ) = .last := rfl

@[simp] theorem genCWSlicePerm_symm_middle (σ : Equiv.Perm μ) (i : μ) :
    (genCWSlicePerm σ).symm (GenCWIndex.middle i) = .middle (σ.symm i) := rfl

@[simp] theorem genCWSlicePerm_symm_last (σ : Equiv.Perm μ) :
    (genCWSlicePerm σ).symm (GenCWIndex.last : GenCWIndex μ) = .zero := rfl

end Perm

/-! ## The `Z`-slices of `CW_q^σ` -/

variable {K : Type u} [CommRing K] {μ : Type v} [Fintype μ] [DecidableEq μ]

/-- The `Z`-slices of `CW_q^σ` in the coordinates of AVW Definition 3.1. -/
noncomputable def genCWSlice (K : Type u) [CommRing K] {μ : Type v} [Fintype μ] [DecidableEq μ]
    (σ : Equiv.Perm μ) (z : GenCWIndex μ) : Matrix (GenCWIndex μ) (GenCWIndex μ) K :=
  zSliceMatrix (κ := GenCWIndexFamily μ) (Equiv.refl _) (genCW K μ σ) z

/-- Entries of the `Z`-slices are the coefficients of AVW's displayed support. -/
theorem genCWSlice_apply (σ : Equiv.Perm μ) (z p q : GenCWIndex μ) :
    genCWSlice K σ z p q = if GenCWSupport σ (ofLegs p q z) then 1 else 0 := by
  classical
  rw [genCWSlice, zSliceMatrix_apply]
  exact standardCoordinateEquiv_genCW (K := K) σ _

/-- `M_{z_0}` is the permutation matrix of `π = (0 ↦ q+1, q+1 ↦ 0, i ↦ σ i)`. -/
theorem genCWSlice_zero_apply (σ : Equiv.Perm μ) (p q : GenCWIndex μ) :
    genCWSlice K σ (GenCWIndex.zero) p q = if q = genCWSlicePerm σ p then 1 else 0 := by
  rw [genCWSlice_apply]
  refine if_congr ?_ rfl rfl
  cases p <;> cases q <;> simp [GenCWSupport, eq_comm]

/-- `M_{z_i} = E_{i,0} + E_{0,i}` for a middle coordinate `i`. -/
theorem genCWSlice_middle_apply (σ : Equiv.Perm μ) (i : μ) (p q : GenCWIndex μ) :
    genCWSlice K σ (GenCWIndex.middle i) p q =
      if (p = .middle i ∧ q = .zero) ∨ (p = .zero ∧ q = .middle i) then 1 else 0 := by
  rw [genCWSlice_apply]
  refine if_congr ?_ rfl rfl
  cases p <;> cases q <;> simp [GenCWSupport, eq_comm]

/-- `M_{z_{q+1}} = E_{0,0}`. -/
theorem genCWSlice_last_apply (σ : Equiv.Perm μ) (p q : GenCWIndex μ) :
    genCWSlice K σ (GenCWIndex.last) p q =
      if p = .zero ∧ q = .zero then 1 else 0 := by
  rw [genCWSlice_apply]
  refine if_congr ?_ rfl rfl
  cases p <;> cases q <;> simp [GenCWSupport, eq_comm]

/-! ## Inverting the `z_0`-slice -/

/-- The inverse of `M_{z_0}`: the permutation matrix of `π⁻¹`. -/
noncomputable def genCWSliceZeroInv (K : Type u) [CommRing K] {μ : Type v} [Fintype μ]
    [DecidableEq μ] (σ : Equiv.Perm μ) : Matrix (GenCWIndex μ) (GenCWIndex μ) K :=
  Matrix.of fun p q ↦ if q = (genCWSlicePerm σ).symm p then 1 else 0

/-- `M_{z_0} · M_{z_0}⁻¹ = 1`. -/
theorem genCWSlice_zero_mul_inv (σ : Equiv.Perm μ) :
    genCWSlice K σ (GenCWIndex.zero) * genCWSliceZeroInv K σ = 1 := by
  classical
  ext p r
  rw [Matrix.mul_apply]
  simp only [genCWSlice_zero_apply, genCWSliceZeroInv, Matrix.of_apply, ite_mul, zero_mul,
    one_mul]
  rw [Finset.sum_ite_eq' Finset.univ (genCWSlicePerm σ p)
    fun q ↦ if r = (genCWSlicePerm σ).symm q then (1 : K) else 0]
  simp [Matrix.one_apply, eq_comm]

/-! ## The normalized slices -/

/-- The normalized `Z`-slices `A_z = M_{z_0}⁻¹ M_z` of `CW_q^σ`. -/
noncomputable def genCWNormalizedSlice (K : Type u) [CommRing K] {μ : Type v} [Fintype μ]
    [DecidableEq μ] (σ : Equiv.Perm μ) (z : GenCWIndex μ) :
    Matrix (GenCWIndex μ) (GenCWIndex μ) K :=
  genCWSliceZeroInv K σ * genCWSlice K σ z

/-- Entries of the normalized slices: left multiplication by the inverse permutation matrix
permutes the rows. -/
theorem genCWNormalizedSlice_apply (σ : Equiv.Perm μ) (z p r : GenCWIndex μ) :
    genCWNormalizedSlice K σ z p r = genCWSlice K σ z ((genCWSlicePerm σ).symm p) r := by
  classical
  rw [genCWNormalizedSlice, Matrix.mul_apply]
  simp only [genCWSliceZeroInv, Matrix.of_apply, ite_mul, zero_mul, one_mul]
  simp

/-- `A_{z_0} = 1`. -/
theorem genCWNormalizedSlice_zero (σ : Equiv.Perm μ) :
    genCWNormalizedSlice K σ (GenCWIndex.zero) = 1 := by
  ext p r
  rw [genCWNormalizedSlice_apply, genCWSlice_zero_apply]
  simp [Matrix.one_apply, eq_comm]

/-- `A_{z_{q+1}} = E_{q+1,0}`. -/
theorem genCWNormalizedSlice_last (σ : Equiv.Perm μ) :
    genCWNormalizedSlice K σ (GenCWIndex.last) =
      Matrix.single (GenCWIndex.last) (GenCWIndex.zero) (1 : K) := by
  ext p r
  rw [genCWNormalizedSlice_apply, genCWSlice_last_apply]
  cases p <;> simp [Matrix.single, eq_comm]

/-- `A_{z_i} = E_{σ i, 0} + E_{q+1, i}`: this is the computation recorded in the module doc of
`Examples/GeneralizedCoppersmithWinogradBorderRank.lean`, verified here against the definition of
`genCW`. -/
theorem genCWNormalizedSlice_middle (σ : Equiv.Perm μ) (i : μ) :
    genCWNormalizedSlice K σ (GenCWIndex.middle i) =
      Matrix.single (GenCWIndex.middle (σ i)) (GenCWIndex.zero) (1 : K) +
        Matrix.single (GenCWIndex.last) (GenCWIndex.middle i) (1 : K) := by
  ext p r
  rw [genCWNormalizedSlice_apply, genCWSlice_middle_apply]
  cases p <;> cases r <;> simp [Matrix.single, eq_comm, Equiv.eq_symm_apply]

/-! ## Products of normalized slices -/

/-- `A_{z_i} A_{z_j} = [i = σ j] · E_{q+1,0}`. -/
theorem genCWNormalizedSlice_middle_mul (σ : Equiv.Perm μ) (i j : μ) :
    genCWNormalizedSlice K σ (GenCWIndex.middle i) *
        genCWNormalizedSlice K σ (GenCWIndex.middle j) =
      if i = σ j then Matrix.single (GenCWIndex.last) (GenCWIndex.zero) (1 : K) else 0 := by
  classical
  rw [genCWNormalizedSlice_middle, genCWNormalizedSlice_middle]
  by_cases hij : i = σ j
  · subst hij
    simp [add_mul, mul_add]
  · simp [add_mul, mul_add, hij]

/-- `A_{z_i} A_{z_{q+1}} = 0`. -/
theorem genCWNormalizedSlice_middle_mul_last (σ : Equiv.Perm μ) (i : μ) :
    genCWNormalizedSlice K σ (GenCWIndex.middle i) *
        genCWNormalizedSlice K σ (GenCWIndex.last) = (0 : Matrix _ _ K) := by
  rw [genCWNormalizedSlice_middle, genCWNormalizedSlice_last]
  simp [add_mul]

/-- `A_{z_{q+1}} A_{z_i} = 0`. -/
theorem genCWNormalizedSlice_last_mul_middle (σ : Equiv.Perm μ) (i : μ) :
    genCWNormalizedSlice K σ (GenCWIndex.last) *
        genCWNormalizedSlice K σ (GenCWIndex.middle i) = (0 : Matrix _ _ K) := by
  rw [genCWNormalizedSlice_middle, genCWNormalizedSlice_last]
  simp [mul_add]

/-- `A_{z_{q+1}} A_{z_{q+1}} = 0`. -/
theorem genCWNormalizedSlice_last_mul_last (σ : Equiv.Perm μ) :
    genCWNormalizedSlice K σ (GenCWIndex.last) *
        genCWNormalizedSlice K σ (GenCWIndex.last) = (0 : Matrix _ _ K) := by
  rw [genCWNormalizedSlice_last]
  simp

/-! ## The dichotomy -/

/-- **The positive half.**  For an involutive `σ` every pair of normalized slices of `CW_q^σ`
commutes: Strassen's equations pose no obstruction, consistently with
`genCW_borderRankLE_refl`, which certifies `R̲(CW_q^{id}) ≤ q + 2`.

Proof sketch: `A_{z_0} = 1` commutes with everything, the products involving `A_{z_{q+1}}` all
vanish, and `A_{z_i} A_{z_j} = [i = σ j] · E_{q+1,0}` is symmetric in `i, j` precisely because
`i = σ j ↔ j = σ i` for an involution. -/
theorem genCW_normalizedSlices_commute_of_involutive (σ : Equiv.Perm μ)
    (hσ : Function.Involutive σ) (z w : GenCWIndex μ) :
    genCWNormalizedSlice K σ z * genCWNormalizedSlice K σ w =
      genCWNormalizedSlice K σ w * genCWNormalizedSlice K σ z := by
  cases z with
  | zero => rw [genCWNormalizedSlice_zero, one_mul, mul_one]
  | last =>
      cases w with
      | zero => rw [genCWNormalizedSlice_zero, one_mul, mul_one]
      | last => rfl
      | middle j =>
          rw [genCWNormalizedSlice_last_mul_middle, genCWNormalizedSlice_middle_mul_last]
  | middle i =>
      cases w with
      | zero => rw [genCWNormalizedSlice_zero, one_mul, mul_one]
      | last =>
          rw [genCWNormalizedSlice_middle_mul_last, genCWNormalizedSlice_last_mul_middle]
      | middle j =>
          rw [genCWNormalizedSlice_middle_mul, genCWNormalizedSlice_middle_mul]
          have h : (i = σ j) ↔ (j = σ i) := by
            constructor
            · rintro rfl; rw [hσ]
            · rintro rfl; rw [hσ]
          by_cases hij : i = σ j
          · rw [if_pos hij, if_pos (h.mp hij)]
          · rw [if_neg hij, if_neg (fun hji ↦ hij (h.mpr hji))]

/-- **The negative half: Strassen's equations rule out minimal border rank for a non-involutive
twist.**  If `σ (σ i) ≠ i` for some middle coordinate `i`, then `CW_q^σ` has no border-rank
certificate of size `q + 2` over any nontrivial commutative ring.

Proof sketch: the `z_0`-slice is a permutation matrix, hence invertible, so Strassen's equations
(`Tensor.normalizedSlices_commute_of_borderRankLE`) would force all normalized slices to commute.
But `A_{z_i} A_{z_{σ i}} = 0` while `A_{z_{σ i}} A_{z_i} = E_{q+1,0} ≠ 0`, because
`σ i = σ i` while `i ≠ σ (σ i)`. -/
theorem not_borderRankLE_genCW_of_not_involutive [Nontrivial K] (σ : Equiv.Perm μ)
    (hσ : ∃ i, σ (σ i) ≠ i) :
    ¬ BorderRankLE (Fintype.card μ + 2) (genCW K μ σ) := by
  classical
  obtain ⟨i, hi⟩ := hσ
  have hcard : Fintype.card (GenCWIndexFamily μ Leg.X) = Fintype.card μ + 2 :=
    GenCWIndex.card μ
  intro hb
  have hb' : BorderRankLE (Fintype.card (GenCWIndexFamily μ Leg.X)) (genCW K μ σ) := by
    rwa [hcard]
  have hcomm := Tensor.normalizedSlices_commute_of_borderRankLE
    (κ := GenCWIndexFamily μ) (Equiv.refl _) hb'
    (z₀ := GenCWIndex.zero) (Q := genCWSliceZeroInv K σ)
    (genCWSlice_zero_mul_inv σ) (GenCWIndex.middle i) (GenCWIndex.middle (σ i))
  have hcomm' : genCWNormalizedSlice K σ (GenCWIndex.middle i) *
      genCWNormalizedSlice K σ (GenCWIndex.middle (σ i)) =
      genCWNormalizedSlice K σ (GenCWIndex.middle (σ i)) *
        genCWNormalizedSlice K σ (GenCWIndex.middle i) := hcomm
  rw [genCWNormalizedSlice_middle_mul, genCWNormalizedSlice_middle_mul,
    if_neg (fun h ↦ hi h.symm), if_pos rfl] at hcomm'
  have hentry := congrArg
    (fun M : Matrix (GenCWIndex μ) (GenCWIndex μ) K ↦ M GenCWIndex.last GenCWIndex.zero) hcomm'
  simp at hentry

/-- **The numerical dichotomy.**  A non-involutive twist forces `R̲(CW_q^σ) ≥ q + 3`, so the
border rank of `CW_q^σ` is *not* the minimal value `q + 2` allowed by conciseness. -/
theorem borderRank_genCW_ge_of_not_involutive [Nontrivial K] (σ : Equiv.Perm μ)
    (hσ : ∃ i, σ (σ i) ≠ i) :
    Fintype.card μ + 3 ≤ Tensor.borderRank (genCW K μ σ) := by
  by_contra hle
  have hb : Tensor.borderRank (genCW K μ σ) ≤ Fintype.card μ + 2 := by omega
  exact not_borderRankLE_genCW_of_not_involutive σ hσ (Tensor.borderRank_le_iff.mp hb)

/-- **The smallest concrete instance.**  At `q = 3` the three-cycle `(0 1 2)` already destroys
minimal border rank: `CW_3^{(0 1 2)}` has no five-term border-rank certificate over `ℚ`, whereas
`CW_3^{id}` does (`genCW_borderRankLE_refl`). -/
theorem not_borderRankLE_genCW_threeCycle :
    ¬ BorderRankLE 5 (genCW ℚ (Fin 3) (Equiv.swap 0 1 * Equiv.swap 1 2)) := by
  have hcard : (5 : ℕ) = Fintype.card (Fin 3) + 2 := by simp
  rw [hcard]
  refine not_borderRankLE_genCW_of_not_involutive _ ⟨0, ?_⟩
  decide

end AlgebraicComplexity.Examples
