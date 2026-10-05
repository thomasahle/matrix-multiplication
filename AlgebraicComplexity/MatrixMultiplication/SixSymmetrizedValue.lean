/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.TauValueDirectSum
import AlgebraicComplexity.MatrixMultiplication
import AlgebraicComplexity.MatrixMultiplication.CyclicValueTensor
import AlgebraicComplexity.MatrixMultiplication.CyclicProductPowerCoherence
import AlgebraicComplexity.Tensor.DegenerationPermutation

/-!
# The six-symmetrized value `V^{(6)}` and its comparison with `V^{(3)}` and `V^{(nrot)}`

Layer 3 (`AlgebraicComplexity/MatrixMultiplication/`).  This module formalizes the
*six-symmetrized value* introduced in

> R. Duan, H. Wu and R. Zhou, *Faster Matrix Multiplication via Asymmetric Hashing*,
> arXiv:2210.10173v5, **§2.2 (Definition 2.6, "Values")** (`[DuanWuZhou2022]`),

together with the comparison laws between the three values that paper uses.

## The three values, and what they are here

`[DuanWuZhou2022]` §2.2 defines, for a leg-permutation action written `T^rot` (the cyclic
rotation) and `T^swap` (the transposition of the `X` and `Y` legs),

* `sym₃(T) = T ⊗ T^rot ⊗ T^{rot rot}` and `sym₆(T) = sym₃(T) ⊗ sym₃(T)^swap`;
* `V^{(3)}_τ(T) = limsup_n max { (∑ (a b c)^τ)^{1/(3n)} : sym₃(T)^{⊗n} ⊵ ⊕ ⟨a,b,c⟩ }`;
* `V^{(6)}_τ(T)`, the same with `sym₃` replaced by `sym₆` and `3n` by `6n`;
* `V^{(nrot)}_τ(T)` (§4, `def:non-rot`), the same with no symmetrization at all and exponent
  `1/n`.

In this repository `V^{(nrot)}` is `AlgebraicComplexity.tauValue` and `V^{(3)}` is
`AlgebraicComplexity.degenerationValue`.  Rather than introduce a *third* value formalism, this
module observes that all three are one and the same supremum applied to different sources:

`V^{(3)}_τ(T) = V^{(nrot)}_τ(sym₃ T)^{1/3}` and `V^{(6)}_τ(T) = V^{(nrot)}_τ(sym₆ T)^{1/6}`,

and simply *defines* `threeValue` and `sixValue` that way.  `symThree` and `symSix` are plain
iterated external products of leg permutations of `T` — a façade over `Tensor.external` and
`Tensor.permute`, exactly as `CyclicTypedLeaf.cyclicProduct` is a façade over
`RationalTypedLeaf.product`/`permute`; no new structure is introduced.  Two coherence results tie
the façade back to the existing API:

* `cyclicPowerProduct_eq_symThree_power` — the repository's existing three-orientation source
  `cyclicPowerProduct K T k` *is* `symThree K (T^{⊗k})`, definitionally;
* `degenerationValue_le_threeValue` / `threeValue_le_degenerationValue` — `threeValue` and the
  repository's `degenerationValue` are the same number.

`symSix K T` is by construction the product of `T` over **all six** leg permutations:
`symSix_eq_sixOrientationProduct` displays it as
`T ⊗ T^c ⊗ T^{c²} ⊗ T^s ⊗ T^{cs} ⊗ T^{c²s}`, and `{1, c, c², s, cs, c²s}` exhausts `Perm Leg` —
formally, `Tensor.orientation_eq_six`.

## Principal results

* `symThree`, `symSix`, `swapXY`, `swapXZ` — the definitions, `Tensor.orientation_eq_six`, and
  `symSix_eq_sixOrientationProduct`.
* `HasTauWeight.permute` — a weighted extraction survives **any** permutation of the three legs.
  This is the one genuinely new ingredient; it rests on `Tensor.PolynomialDegenerates.permute`
  from `Tensor/DegenerationPermutation.lean`.  Only the two generator cases
  `HasTauWeight.permute_cycle` and `HasTauWeight.permute_xzy` touch the matrix-multiplication
  direct sum; `orientation_eq_six` lifts them to the whole symmetric group, and the named
  corollaries `HasTauWeight.permute_cycle_symm` / `permute_swapXY` are instances of the general
  statement.
* `tauValue_pow_three_le_tauValue_symThree`, `tauValue_symThree_pow_two_le_tauValue_symSix` and
  their normalized forms `tauValue_le_threeValue`, `threeValue_le_sixValue`.  **These are the two
  inequalities `V^{(6)} ≥ V^{(3)} ≥ V^{(nrot)}`.**  `[DuanWuZhou2022]` states the first (§2.2,
  "`V^{(6)}_τ(T) ≥ V^{(3)}_τ(T)` holds for any tensor `T`") but **never states the second**, even
  though §6.3 needs it: the global bound there is expressed through `V^{(6)}` while the table
  supplies a `V^{(nrot)}` bound for the component `T_{0,2,2}` and a `V^{(3)}` bound for
  `T_{1,1,2}`.  Both are proved here; both are consequences of supermultiplicativity together
  with invariance of the value under leg permutations.
* `Isomorphic.symSix_of_swapSymmetric`, `sixValue_eq_threeValue_of_swapSymmetric` —
  `[DuanWuZhou2022]` `component_value.tex` l.245 asserts, without proof, that
  `V^{(3)}(𝒯) = V^{(6)}(𝒯)` "because `𝒯` is symmetric about X and Y variables, i.e.
  `sym₃(𝒯)^{⊗2} ≅ sym₆(𝒯)`".  The assertion is **correct**, but it needs a hypothesis the prose
  leaves implicit and a step the prose omits.  See the section below.

## Watchlist item 10: what `sym₃(𝒯)^{⊗2} ≅ sym₆(𝒯)` really requires

Write the leg-permutation action as `T^π`, so that `sym₃(T) = ⨂_{π ∈ A₃} T^π` and
`sym₆(T) = ⨂_{π ∈ S₃} T^π`.  Then `sym₃(T)^swap = ⨂_{π ∈ A₃} T^{πs}`, and the hypothesis
"`𝒯` is symmetric about X and Y" must be read as a genuine legwise **isomorphism**
`𝒯 ≅ 𝒯^s` (`Isomorphic T (Tensor.permute swapXY T)`), not as a syntactic coincidence.  From it
one gets `T^{πs} ≅ T^{sπs}`, and conjugation by the transposition `s` *inverts* the three-cycle,
so the three factors of `sym₃(T)^swap` are the three factors of `sym₃(T)` **in the reversed
cyclic order**.  Restoring the order costs one application of the external-product commutation
`Tensor.map_external_swap_right`.  That reordering is exactly the step the paper's "i.e." hides,
and it is where a leg-permutation error would live.  `Isomorphic.symSix_of_swapSymmetric` proves
the corrected statement, and `sixValue_eq_threeValue_of_swapSymmetric` derives the value
identity; the `≤` half of the identity is *not* an instance of the general
`V^{(6)} ≥ V^{(3)}` law but of the subsequence comparison `V^{(6)}` sees only the even powers of
`sym₃`.

## Non-goals

Nothing here is about a named tensor, a distribution, or a numerical bound.  The restricted
splitting powers `T^{⊗n}[α̃]` that carry these values between levels of `[DuanWuZhou2022]`'s
recursion live in `Tensor/RestrictedSplittingPower.lean`.
-/

namespace AlgebraicComplexity

open Tensor

universe u v w

/-! ## The `X`–`Y` transposition of legs -/

namespace Tensor

/-- The orientation `(Y, X, Z)`: the transposition of the `X` and `Y` legs.

This is the leg permutation underlying `[DuanWuZhou2022]`'s swapping operation `T^swap`
(§2.1): `T^swap = ∑ a_{i,j,k} x_j y_i z_k`.  `Tensor/Leg.lean` already names the cyclic rotation
`cycle` and the `Y`–`Z` transposition `xzy`; together with `swapXY` they generate all six
orientations. -/
def swapXY : Orientation where
  toFun
    | .X => .Y
    | .Y => .X
    | .Z => .Z
  invFun
    | .X => .Y
    | .Y => .X
    | .Z => .Z
  left_inv c := by cases c <;> rfl
  right_inv c := by cases c <;> rfl

@[simp] theorem swapXY_X : swapXY Leg.X = Leg.Y := rfl
@[simp] theorem swapXY_Y : swapXY Leg.Y = Leg.X := rfl
@[simp] theorem swapXY_Z : swapXY Leg.Z = Leg.Z := rfl
@[simp] theorem swapXY_symm_X : swapXY.symm Leg.X = Leg.Y := rfl
@[simp] theorem swapXY_symm_Y : swapXY.symm Leg.Y = Leg.X := rfl
@[simp] theorem swapXY_symm_Z : swapXY.symm Leg.Z = Leg.Z := rfl

/-- The orientation `(Z, Y, X)`: the transposition of the `X` and `Z` legs.

`xzy`, `swapXY` and `swapXZ` are the three transpositions of `Leg`; together with `cycle`,
`cycle.symm` and the identity they exhaust `Orientation` (`orientation_eq_six`).  This one is
named only because that exhaustion has to list it. -/
def swapXZ : Orientation where
  toFun
    | .X => .Z
    | .Y => .Y
    | .Z => .X
  invFun
    | .X => .Z
    | .Y => .Y
    | .Z => .X
  left_inv c := by cases c <;> rfl
  right_inv c := by cases c <;> rfl

@[simp] theorem swapXZ_X : swapXZ Leg.X = Leg.Z := rfl
@[simp] theorem swapXZ_Y : swapXZ Leg.Y = Leg.Y := rfl
@[simp] theorem swapXZ_Z : swapXZ Leg.Z = Leg.X := rfl
@[simp] theorem swapXZ_symm_X : swapXZ.symm Leg.X = Leg.Z := rfl
@[simp] theorem swapXZ_symm_Y : swapXZ.symm Leg.Y = Leg.Y := rfl
@[simp] theorem swapXZ_symm_Z : swapXZ.symm Leg.Z = Leg.X := rfl

/-- The `X`–`Y` transposition is the composite `xzy` then `cycle`.  This factorization is what
lets the two-generator permutation lemmas below cover the swap. -/
theorem xzy_trans_cycle : xzy.trans cycle = swapXY := by
  ext c; cases c <;> rfl

/-- Applying the cyclic rotation twice is the inverse rotation. -/
theorem cycle_trans_cycle : cycle.trans cycle = cycle.symm := by
  ext c; cases c <;> rfl

/-- **Conjugating the three-cycle by the `X`–`Y` transposition inverts it**, in the composite
form needed below: rotating and then swapping is the same as swapping and then rotating
backwards. -/
theorem cycle_trans_swapXY : cycle.trans swapXY = swapXY.trans cycle.symm := by
  ext c; cases c <;> rfl

/-- The inverse form of `cycle_trans_swapXY`. -/
theorem cycle_symm_trans_swapXY : cycle.symm.trans swapXY = swapXY.trans cycle := by
  ext c; cases c <;> rfl

/-- The `X`–`Z` transposition is the composite `swapXY` then `cycle`, hence `xzy` then `cycle`
twice.  This is what puts the last orientation within reach of the two generators. -/
theorem swapXY_trans_cycle : swapXY.trans cycle = swapXZ := by
  ext c; cases c <;> rfl

/-- **The six named orientations exhaust `Perm Leg`.**

`symSix_eq_sixOrientationProduct` displays `sym₆` as a product over `{1, c, c², s, cs, c²s}`; that
list is complete precisely because of this lemma, and it is also what upgrades the two-generator
permutation lemmas below into a statement about an *arbitrary* leg permutation.

The proof is a case analysis on the three images `e X`, `e Y`, `e Z`: injectivity kills the
twenty-one branches with a repeat, and each of the six surviving branches determines `e`
pointwise. -/
theorem orientation_eq_six (e : Orientation) :
    e = Equiv.refl Leg ∨ e = cycle ∨ e = cycle.symm ∨ e = xzy ∨ e = swapXY ∨ e = swapXZ := by
  have hext : ∀ f : Orientation,
      e Leg.X = f Leg.X → e Leg.Y = f Leg.Y → e Leg.Z = f Leg.Z → e = f := by
    intro f hx hy hz
    ext c
    cases c
    · exact hx
    · exact hy
    · exact hz
  have hne : ∀ {a b : Leg}, a ≠ b → e a ≠ e b := fun hab h ↦ hab (e.injective h)
  cases hx : e Leg.X <;> cases hy : e Leg.Y <;> cases hz : e Leg.Z <;>
    first
      | exact absurd (hx.trans hy.symm) (hne (by decide))
      | exact absurd (hx.trans hz.symm) (hne (by decide))
      | exact absurd (hy.trans hz.symm) (hne (by decide))
      | exact Or.inl (hext _ hx hy hz)
      | exact Or.inr (Or.inl (hext _ hx hy hz))
      | exact Or.inr (Or.inr (Or.inl (hext _ hx hy hz)))
      | exact Or.inr (Or.inr (Or.inr (Or.inl (hext _ hx hy hz))))
      | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (hext _ hx hy hz)))))
      | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (hext _ hx hy hz)))))

variable {K : Type u} [CommSemiring K]
variable {V : Leg → Type v} [∀ c, AddCommMonoid (V c)] [∀ c, Module K (V c)]

/-- Permuting by a composite orientation is permuting twice. -/
theorem permute_apply_trans (e₁ e₂ : Orientation) (T : Tensor3 K V) :
    Tensor.permute (K := K) (V := V) (e₁.trans e₂) T =
      Tensor.permute e₂ (Tensor.permute e₁ T) := by
  rw [← permute_trans]
  rfl

/-- **Rotating after transposing `Y` and `Z` is the `X`–`Y` transposition.**

As with `Isomorphic.permute_cycle_cycle`, the two ambient leg families are propositionally but
not definitionally equal — `xzy.symm (cycle.symm c)` and `swapXY.symm c` agree only after a case
analysis on `c` — so the statement is an explicit legwise isomorphism rather than an equation. -/
theorem Isomorphic.permute_cycle_xzy (T : Tensor3 K V) :
    Isomorphic (Tensor.permute cycle (Tensor.permute xzy T))
      (Tensor.permute swapXY T) := by
  let f : ∀ c, V (xzy.symm (cycle.symm c)) ≃ₗ[K] V (swapXY.symm c) := by
    intro c
    cases c <;> exact LinearEquiv.refl K _
  refine ⟨f, ?_⟩
  change Tensor.map (fun c ↦ (f c).toLinearMap)
      (Tensor.permute cycle (Tensor.permute xzy T)) = Tensor.permute swapXY T
  refine PiTensorProduct.induction_on T ?_ ?_
  · intro a x
    simp only [map_smul, Tensor.permute_pure, Tensor.map_pure]
    congr 2
    funext c
    cases c <;> rfl
  · intro T₁ T₂ h₁ h₂
    simp only [map_add, h₁, h₂]

/-- **Rotating after the `X`–`Y` transposition is the `X`–`Z` transposition.**

The companion of `Isomorphic.permute_cycle_xzy` for the remaining transposition, and for the same
reason an isomorphism rather than an equation: `swapXY.symm (cycle.symm c)` and `swapXZ.symm c`
agree only after a case analysis on `c`. -/
theorem Isomorphic.permute_cycle_swapXY (T : Tensor3 K V) :
    Isomorphic (Tensor.permute cycle (Tensor.permute swapXY T))
      (Tensor.permute swapXZ T) := by
  let f : ∀ c, V (swapXY.symm (cycle.symm c)) ≃ₗ[K] V (swapXZ.symm c) := by
    intro c
    cases c <;> exact LinearEquiv.refl K _
  refine ⟨f, ?_⟩
  change Tensor.map (fun c ↦ (f c).toLinearMap)
      (Tensor.permute cycle (Tensor.permute swapXY T)) = Tensor.permute swapXZ T
  refine PiTensorProduct.induction_on T ?_ ?_
  · intro a x
    simp only [map_smul, Tensor.permute_pure, Tensor.map_pure]
    congr 2
    funext c
    cases c <;> rfl
  · intro T₁ T₂ h₁ h₂
    simp only [map_add, h₁, h₂]

/-- Equal orientations give isomorphic permuted tensors.  The two ambient leg families are
propositionally equal, so this cannot be an `Eq`; `subst` on the orientation makes it trivial. -/
theorem Isomorphic.permute_congr {e f : Orientation} (h : e = f) (T : Tensor3 K V) :
    Isomorphic (Tensor.permute e T) (Tensor.permute f T) := by
  subst h
  exact Isomorphic.refl _

/-- Reordering the last two factors of a left-associated triple external product is a legwise
isomorphism.  This is the bundled form of `Tensor.map_external_swap_right`. -/
theorem Isomorphic.external_swap_right {U W : Leg → Type*}
    [∀ i, AddCommMonoid (U i)] [∀ i, Module K (U i)]
    [∀ i, AddCommMonoid (W i)] [∀ i, Module K (W i)]
    (R : Tensor3 K U) (T : Tensor3 K V) (S : Tensor3 K W) :
    Isomorphic (Tensor.external (Tensor.external R T) S)
      (Tensor.external (Tensor.external R S) T) :=
  ⟨fun c ↦ externalSwapRightEquiv (K := K) (U := U) (V := V) (W := W) c, by
    simpa [PiTensorProduct.congr] using map_external_swap_right R T S⟩

end Tensor

/-! ## The three- and six-orientation symmetrizations -/

section Symmetrization

variable (K : Type u) [CommSemiring K]
variable {V : Leg → Type v} [∀ c, AddCommMonoid (V c)] [∀ c, Module K (V c)]

/-- **The three-symmetrization `sym₃(T) = T ⊗ T^rot ⊗ T^{rot rot}`**
(`[DuanWuZhou2022]`, §2.1).

Only the leg roles are rotated; no power is taken.  The repository's existing three-orientation
source `cyclicPowerProduct K T k` is `symThree K (T^{⊗k})` (see
`cyclicPowerProduct_eq_symThree_power`). -/
noncomputable def symThree (T : Tensor3 K V) :=
  Tensor.external (Tensor.external T (Tensor.permute cycle T)) (Tensor.permute cycle.symm T)

/-- **The six-symmetrization `sym₆(T) = sym₃(T) ⊗ sym₃(T)^swap`**
(`[DuanWuZhou2022]`, §2.1).  New in that paper; earlier laser analyses only use `sym₃`. -/
noncomputable def symSix (T : Tensor3 K V) :=
  Tensor.external (symThree K T) (Tensor.permute Tensor.swapXY (symThree K T))

/-- The repository's three-orientation source is the three-symmetrization of the power. -/
theorem cyclicPowerProduct_eq_symThree_power (T : Tensor3 K V) (k : ℕ) :
    cyclicPowerProduct K T k = symThree K (Tensor.power T k) := rfl

/-- **`sym₆(T)` is the product of `T` over all six leg permutations.**

The six displayed orientations are `1`, `c`, `c⁻¹`, `s`, `c·s`, `c⁻¹·s` where `c = cycle` and
`s = swapXY`; these are exactly the six elements of `Perm Leg`.  The identity is an equation, not
merely an isomorphism: permuting an external product is computed factorwise
(`Tensor.permute_external`) and composing two permutations is one permutation
(`Tensor.permute_apply_trans`). -/
theorem symSix_eq_sixOrientationProduct (T : Tensor3 K V) :
    symSix K T =
      Tensor.external (symThree K T)
        (Tensor.external
          (Tensor.external (Tensor.permute Tensor.swapXY T)
            (Tensor.permute (cycle.trans Tensor.swapXY) T))
          (Tensor.permute (cycle.symm.trans Tensor.swapXY) T)) := by
  unfold symSix symThree
  rw [Tensor.permute_external, Tensor.permute_external, Tensor.permute_apply_trans,
    Tensor.permute_apply_trans]
  rfl

end Symmetrization

/-! ## Leg permutations act on weighted extractions -/

section Permutation

variable {K : Type u} [CommSemiring K]
variable {V : Leg → Type v} [∀ c, AddCommMonoid (V c)] [∀ c, Module K (V c)]

variable (K) in
/-- Rotating the three legs of a matrix-multiplication tensor rotates its three dimensions. -/
theorem isomorphic_permute_cycle_matrixMultiplication (m n p : ℕ) :
    Isomorphic (Tensor.permute cycle (matrixMultiplication (K := K) m n p))
      (matrixMultiplication (K := K) p m n) :=
  ⟨fun c ↦ mmCycleLegEquiv (K := K) m n p c, by
    simpa [mmCycleEquiv, PiTensorProduct.congr] using
      mmCycleEquiv_matrixMultiplication (K := K) m n p⟩

variable (K) in
/-- Transposing the `Y` and `Z` legs of a matrix-multiplication tensor transposes its first two
dimensions. -/
theorem isomorphic_permute_xzy_matrixMultiplication (m n p : ℕ) :
    Isomorphic (Tensor.permute xzy (matrixMultiplication (K := K) m n p))
      (matrixMultiplication (K := K) n m p) :=
  ⟨fun c ↦ mmSwapYZLegEquiv (K := K) m n p c, by
    simpa [mmSwapYZEquiv, PiTensorProduct.congr] using
      mmSwapYZEquiv_matrixMultiplication (K := K) m n p⟩

variable (K) in
/-- Rotating the legs of a finite direct sum of matrix-multiplication tensors rotates every
summand's dimensions. -/
theorem isomorphic_permute_cycle_matrixMultiplicationDirectSum {ι : Type w} [Fintype ι]
    (m n p : ι → ℕ) :
    Isomorphic (Tensor.permute cycle (matrixMultiplicationDirectSum K m n p))
      (matrixMultiplicationDirectSum K p m n) := by
  unfold matrixMultiplicationDirectSum
  rw [Tensor.permute_indexedDirectSum]
  exact Tensor.Isomorphic.indexedDirectSum
    (fun i ↦ isomorphic_permute_cycle_matrixMultiplication K (m i) (n i) (p i))

variable (K) in
/-- Transposing the `Y` and `Z` legs of a finite direct sum of matrix-multiplication tensors
transposes every summand's first two dimensions. -/
theorem isomorphic_permute_xzy_matrixMultiplicationDirectSum {ι : Type w} [Fintype ι]
    (m n p : ι → ℕ) :
    Isomorphic (Tensor.permute xzy (matrixMultiplicationDirectSum K m n p))
      (matrixMultiplicationDirectSum K n m p) := by
  unfold matrixMultiplicationDirectSum
  rw [Tensor.permute_indexedDirectSum]
  exact Tensor.Isomorphic.indexedDirectSum
    (fun i ↦ isomorphic_permute_xzy_matrixMultiplication K (m i) (n i) (p i))

/-- The volume power sum is unchanged by rotating the three dimension families. -/
theorem matrixMultiplicationVolumePowerSum_rotate {ι : Type w} [Fintype ι]
    (m n p : ι → ℕ) (τ : ℝ) :
    matrixMultiplicationVolumePowerSum p m n τ =
      matrixMultiplicationVolumePowerSum m n p τ := by
  unfold matrixMultiplicationVolumePowerSum matrixMultiplicationVolume
  exact Finset.sum_congr rfl fun i _ ↦ by
    rw [show p i * m i * n i = m i * n i * p i by ring]

/-- The volume power sum is unchanged by transposing the first two dimension families. -/
theorem matrixMultiplicationVolumePowerSum_swap {ι : Type w} [Fintype ι]
    (m n p : ι → ℕ) (τ : ℝ) :
    matrixMultiplicationVolumePowerSum n m p τ =
      matrixMultiplicationVolumePowerSum m n p τ := by
  unfold matrixMultiplicationVolumePowerSum matrixMultiplicationVolume
  exact Finset.sum_congr rfl fun i _ ↦ by
    rw [show n i * m i * p i = m i * n i * p i by ring]

/-- A weighted extraction survives the cyclic rotation of the three legs. -/
theorem HasTauWeight.permute_cycle {X : Tensor3 K V} {τ value : ℝ}
    (h : HasTauWeight K X τ value) :
    HasTauWeight K (Tensor.permute cycle X) τ value := by
  obtain ⟨copies, m, n, p, hm, hn, hp, hdeg, hval⟩ := h
  refine ⟨copies, p, m, n, hp, hm, hn, ?_, ?_⟩
  · exact (hdeg.permute cycle).trans (Tensor.PolynomialDegenerates.of_restricts
      (isomorphic_permute_cycle_matrixMultiplicationDirectSum K m n p).restricts)
  · rw [matrixMultiplicationVolumePowerSum_rotate]
    exact hval

/-- A weighted extraction survives the transposition of the `Y` and `Z` legs. -/
theorem HasTauWeight.permute_xzy {X : Tensor3 K V} {τ value : ℝ}
    (h : HasTauWeight K X τ value) :
    HasTauWeight K (Tensor.permute xzy X) τ value := by
  obtain ⟨copies, m, n, p, hm, hn, hp, hdeg, hval⟩ := h
  refine ⟨copies, n, m, p, hn, hm, hp, ?_, ?_⟩
  · exact (hdeg.permute xzy).trans (Tensor.PolynomialDegenerates.of_restricts
      (isomorphic_permute_xzy_matrixMultiplicationDirectSum K m n p).restricts)
  · rw [matrixMultiplicationVolumePowerSum_swap]
    exact hval

/-- **A weighted extraction survives any permutation of the three legs.**

The two preceding lemmas are the only places where the matrix-multiplication direct sum is
actually re-indexed: `permute_cycle` rotates the three dimension families and `permute_xzy`
transposes the first two.  `Tensor.orientation_eq_six` reduces an arbitrary orientation to
composites of those two, and every remaining step is the dependent-reindexing bookkeeping of
`Tensor.Isomorphic.permute_cycle_cycle` / `permute_cycle_xzy` / `permute_cycle_swapXY`.

Stating the invariance for a general `e : Equiv.Perm Leg` is what makes the `V^{(6)}` comparisons
below a statement about the symmetric group rather than about four hand-picked cases. -/
theorem HasTauWeight.permute {X : Tensor3 K V} {τ value : ℝ} (e : Orientation)
    (h : HasTauWeight K X τ value) :
    HasTauWeight K (Tensor.permute e X) τ value := by
  have hswapXY : HasTauWeight K (Tensor.permute Tensor.swapXY X) τ value :=
    h.permute_xzy.permute_cycle.of_restricts
      (Tensor.Isomorphic.permute_cycle_xzy X).symm.restricts
  rcases Tensor.orientation_eq_six e with rfl | rfl | rfl | rfl | rfl | rfl
  · simp only [Tensor.permute_refl]
    exact h
  · exact h.permute_cycle
  · exact h.permute_cycle.permute_cycle.of_restricts
      (Tensor.Isomorphic.permute_cycle_cycle X).symm.restricts
  · exact h.permute_xzy
  · exact hswapXY
  · exact hswapXY.permute_cycle.of_restricts
      (Tensor.Isomorphic.permute_cycle_swapXY X).symm.restricts

/-- A weighted extraction survives the inverse cyclic rotation of the three legs. -/
theorem HasTauWeight.permute_cycle_symm {X : Tensor3 K V} {τ value : ℝ}
    (h : HasTauWeight K X τ value) :
    HasTauWeight K (Tensor.permute cycle.symm X) τ value :=
  h.permute cycle.symm

/-- **A weighted extraction survives the `X`–`Y` transposition of legs.**  This is the case
`[DuanWuZhou2022]` needs to compare `V^{(6)}` with `V^{(3)}`. -/
theorem HasTauWeight.permute_swapXY {X : Tensor3 K V} {τ value : ℝ}
    (h : HasTauWeight K X τ value) :
    HasTauWeight K (Tensor.permute Tensor.swapXY X) τ value :=
  h.permute Tensor.swapXY

end Permutation

/-! ## Weighted extractions of the symmetrizations -/

section Weights

variable {K : Type u} [CommSemiring K]
variable {V : Leg → Type v} [∀ c, AddCommMonoid (V c)] [∀ c, Module K (V c)]

/-- **A weight `v` for `X` is a weight `v³` for `sym₃(X)`.**

Proof sketch: the two rotated factors carry the same weight as `X` itself
(`HasTauWeight.permute_cycle`, `HasTauWeight.permute_cycle_symm`), and weights multiply under
external products. -/
theorem HasTauWeight.symThree_pow_three {X : Tensor3 K V} {τ value : ℝ}
    (h : HasTauWeight K X τ value) (hvalue : 0 ≤ value) :
    HasTauWeight K (symThree K X) τ (value ^ 3) := by
  have h1 := h.external h.permute_cycle hvalue hvalue
  have h2 := h1.external h.permute_cycle_symm (by positivity) hvalue
  have hpow : value * value * value = value ^ 3 := by ring
  rw [hpow] at h2
  exact h2

/-- **A weight `w` for `sym₃(X)` is a weight `w²` for `sym₆(X)`.**

Proof sketch: `sym₆(X) = sym₃(X) ⊗ sym₃(X)^swap`, the swapped factor carries the same weight
(`HasTauWeight.permute_swapXY`), and weights multiply. -/
theorem HasTauWeight.symSix_pow_two {X : Tensor3 K V} {τ value : ℝ}
    (h : HasTauWeight K (symThree K X) τ value) (hvalue : 0 ≤ value) :
    HasTauWeight K (symSix K X) τ (value ^ 2) := by
  have h2 := h.external h.permute_swapXY hvalue hvalue
  have hpow : value * value = value ^ 2 := by ring
  rw [hpow] at h2
  exact h2

end Weights

/-! ## The comparison laws -/

section Comparison

variable {K : Type u} [CommSemiring K]
variable {V : Leg → Type v} [∀ c, AddCommMonoid (V c)] [∀ c, Module K (V c)]

/-- Commuting a natural power past a real power on a nonnegative base. -/
private theorem rpow_pow_comm {S : ℝ} (hS : 0 ≤ S) (k : ℕ) (x : ℝ) :
    (S ^ x) ^ k = (S ^ k) ^ x := by
  rw [← Real.rpow_natCast (S ^ x) k, ← Real.rpow_natCast S k, ← Real.rpow_mul hS,
    ← Real.rpow_mul hS, mul_comm]

/-- **The supremum of a nonempty set of positive reals whose `k`th powers are bounded by `B`.**

Both conclusions are needed downstream: the supremum is strictly positive (so that a real power
of it can be manipulated), and its `k`th power is still below `B`. -/
private theorem csSup_pos_and_pow_le {A : Set ℝ} {B : ℝ} {k : ℕ} (hk : 0 < k) (hne : A.Nonempty)
    (hpos : ∀ x ∈ A, 0 < x) (hB : ∀ x ∈ A, x ^ k ≤ B) : 0 < sSup A ∧ sSup A ^ k ≤ B := by
  obtain ⟨x₀, hx₀⟩ := hne
  have hB0 : 0 ≤ B := le_trans (pow_nonneg (hpos x₀ hx₀).le k) (hB x₀ hx₀)
  have hle : ∀ x ∈ A, x ≤ B ^ ((k : ℝ)⁻¹) := by
    intro x hx
    have hstep := Real.rpow_le_rpow (pow_nonneg (hpos x hx).le k) (hB x hx)
      (by positivity : (0 : ℝ) ≤ ((k : ℝ))⁻¹)
    rwa [Real.pow_rpow_inv_natCast (hpos x hx).le hk.ne'] at hstep
  have hbdd : BddAbove A := ⟨B ^ ((k : ℝ)⁻¹), hle⟩
  have hposSup : 0 < sSup A := lt_of_lt_of_le (hpos x₀ hx₀) (le_csSup hbdd hx₀)
  refine ⟨hposSup, ?_⟩
  have hsup : sSup A ≤ B ^ ((k : ℝ)⁻¹) := csSup_le ⟨x₀, hx₀⟩ hle
  have hfinal := pow_le_pow_left₀ hposSup.le hsup k
  rwa [Real.rpow_inv_natCast_pow hB0 hk.ne'] at hfinal

/-- **Every value certificate of `T` gives the cube of its weight for `sym₃(T)`.**

Proof sketch: the certificate is a weighted extraction of `T^{⊗N}`; cubing it through
`HasTauWeight.symThree` gives a weighted extraction of `sym₃(T^{⊗N})`, which is the `N`th power
of `sym₃(T)` up to the canonical reassociation
`Isomorphic.cyclicPowerProduct_positive`.  Reading the resulting weight back through
`le_tauValue_of_hasTauWeight` gives the `N`th root of `S³`, which is the cube of the `N`th root
of `S`. -/
theorem TauValueCertificate.term_pow_three_le_tauValue_symThree {T : Tensor3 K V}
    (certificate : TauValueCertificate K T) (τ : ℝ)
    (hbounded : BddAbove (tauValueValues K (symThree K T) τ)) :
    certificate.term τ ^ 3 ≤ tauValue K (symThree K T) τ := by
  obtain ⟨n, hn⟩ : ∃ n, certificate.power = n + 1 :=
    ⟨certificate.power - 1, by have := certificate.power_pos; omega⟩
  set S := matrixMultiplicationVolumePowerSum certificate.xSize certificate.ySize
    certificate.zSize τ with hS
  have hSpos : 0 < S := matrixMultiplicationVolumePowerSum_pos certificate.copies_pos
    certificate.xSize_pos certificate.ySize_pos certificate.zSize_pos τ
  have hweight : HasTauWeight K (Tensor.power T certificate.power) τ S :=
    certificate.hasTauWeight τ
  have hthree : HasTauWeight K (symThree K (Tensor.power T certificate.power)) τ (S ^ 3) :=
    hweight.symThree_pow_three hSpos.le
  have hres : Restricts (Tensor.power (symThree K T) certificate.power)
      (symThree K (Tensor.power T certificate.power)) := by
    rw [hn]
    exact (Isomorphic.cyclicPowerProduct_positive T n).symm.restricts
  have hpower : HasTauWeight K (Tensor.power (symThree K T) certificate.power) τ (S ^ 3) :=
    hthree.of_restricts hres
  have hread := le_tauValue_of_hasTauWeight certificate.power_pos (by positivity) hpower hbounded
  calc certificate.term τ ^ 3
      = (S ^ (((certificate.power : ℕ) : ℝ)⁻¹)) ^ 3 := rfl
    _ = (S ^ 3) ^ (((certificate.power : ℕ) : ℝ)⁻¹) := rpow_pow_comm hSpos.le 3 _
    _ ≤ tauValue K (symThree K T) τ := hread

/-- **Every value certificate of `sym₃(T)` gives the square of its weight for `sym₆(T)`.** -/
theorem TauValueCertificate.term_pow_two_le_tauValue_symSix {T : Tensor3 K V}
    (certificate : TauValueCertificate K (symThree K T)) (τ : ℝ)
    (hbounded : BddAbove (tauValueValues K (symSix K T) τ)) :
    certificate.term τ ^ 2 ≤ tauValue K (symSix K T) τ := by
  obtain ⟨n, hn⟩ : ∃ n, certificate.power = n + 1 :=
    ⟨certificate.power - 1, by have := certificate.power_pos; omega⟩
  set S := matrixMultiplicationVolumePowerSum certificate.xSize certificate.ySize
    certificate.zSize τ with hS
  have hSpos : 0 < S := matrixMultiplicationVolumePowerSum_pos certificate.copies_pos
    certificate.xSize_pos certificate.ySize_pos certificate.zSize_pos τ
  have hweight : HasTauWeight K (Tensor.power (symThree K T) certificate.power) τ S :=
    certificate.hasTauWeight τ
  -- The swapped copy carries the same weight, and the two multiply.
  have hprod := hweight.external hweight.permute_swapXY hSpos.le hSpos.le
  -- `sym₆(T)^{⊗N}` restricts onto that external product.
  have hres : Restricts (Tensor.power (symSix K T) certificate.power)
      (Tensor.external (Tensor.power (symThree K T) certificate.power)
        (Tensor.permute Tensor.swapXY (Tensor.power (symThree K T) certificate.power))) := by
    rw [hn]
    refine ((Tensor.Isomorphic.power_external_positive (symThree K T)
      (Tensor.permute Tensor.swapXY (symThree K T)) n).trans ?_).restricts
    exact (Tensor.Isomorphic.refl _).external
      (Tensor.Isomorphic.power_permute_positive_unbundled (symThree K T) n Tensor.swapXY)
  have hpower : HasTauWeight K (Tensor.power (symSix K T) certificate.power) τ (S * S) :=
    hprod.of_restricts hres
  have hsq : S * S = S ^ 2 := by ring
  rw [hsq] at hpower
  have hread := le_tauValue_of_hasTauWeight certificate.power_pos (by positivity) hpower hbounded
  calc certificate.term τ ^ 2
      = (S ^ (((certificate.power : ℕ) : ℝ)⁻¹)) ^ 2 := rfl
    _ = (S ^ 2) ^ (((certificate.power : ℕ) : ℝ)⁻¹) := rpow_pow_comm hSpos.le 2 _
    _ ≤ tauValue K (symSix K T) τ := hread

/-- **`V^{(nrot)}_τ(T)³ ≤ V^{(nrot)}_τ(sym₃ T)`** — the unnormalized form of `V^{(3)} ≥
`V^{(nrot)}`. -/
theorem tauValue_pos_and_pow_three_le_tauValue_symThree {T : Tensor3 K V} {τ : ℝ}
    (hne : (tauValueValues K T τ).Nonempty)
    (hbounded : BddAbove (tauValueValues K (symThree K T) τ)) :
    0 < tauValue K T τ ∧ tauValue K T τ ^ 3 ≤ tauValue K (symThree K T) τ := by
  refine csSup_pos_and_pow_le (by norm_num) hne ?_ ?_
  · rintro x ⟨c, rfl⟩
    exact c.term_pos τ
  · rintro x ⟨c, rfl⟩
    exact c.term_pow_three_le_tauValue_symThree τ hbounded

/-- **`V^{(nrot)}_τ(T)³ ≤ V^{(nrot)}_τ(sym₃ T)`.** -/
theorem tauValue_pow_three_le_tauValue_symThree {T : Tensor3 K V} {τ : ℝ}
    (hne : (tauValueValues K T τ).Nonempty)
    (hbounded : BddAbove (tauValueValues K (symThree K T) τ)) :
    tauValue K T τ ^ 3 ≤ tauValue K (symThree K T) τ :=
  (tauValue_pos_and_pow_three_le_tauValue_symThree hne hbounded).2

/-- **`V^{(nrot)}_τ(sym₃ T)² ≤ V^{(nrot)}_τ(sym₆ T)`** — the unnormalized form of
`V^{(6)} ≥ V^{(3)}` (`[DuanWuZhou2022]`, §2.2). -/
theorem tauValue_symThree_pos_and_pow_two_le_tauValue_symSix {T : Tensor3 K V} {τ : ℝ}
    (hne : (tauValueValues K (symThree K T) τ).Nonempty)
    (hbounded : BddAbove (tauValueValues K (symSix K T) τ)) :
    0 < tauValue K (symThree K T) τ ∧
      tauValue K (symThree K T) τ ^ 2 ≤ tauValue K (symSix K T) τ := by
  refine csSup_pos_and_pow_le (by norm_num) hne ?_ ?_
  · rintro x ⟨c, rfl⟩
    exact c.term_pos τ
  · rintro x ⟨c, rfl⟩
    exact c.term_pow_two_le_tauValue_symSix τ hbounded

/-- **`V^{(nrot)}_τ(sym₃ T)² ≤ V^{(nrot)}_τ(sym₆ T)`.** -/
theorem tauValue_symThree_pow_two_le_tauValue_symSix {T : Tensor3 K V} {τ : ℝ}
    (hne : (tauValueValues K (symThree K T) τ).Nonempty)
    (hbounded : BddAbove (tauValueValues K (symSix K T) τ)) :
    tauValue K (symThree K T) τ ^ 2 ≤ tauValue K (symSix K T) τ :=
  (tauValue_symThree_pos_and_pow_two_le_tauValue_symSix hne hbounded).2

end Comparison

/-! ## The named values -/

section NamedValues

variable (K : Type u) [CommSemiring K]
variable {V : Leg → Type v} [∀ c, AddCommMonoid (V c)] [∀ c, Module K (V c)]

/-- **`V^{(3)}_τ(T)`, the three-symmetrized value** of `[DuanWuZhou2022]` §2.2, written as the
cube root of the unsymmetrized value of `sym₃(T)`.

This is the same number as the repository's `degenerationValue`; see
`degenerationValue_le_threeValue` and `threeValue_le_degenerationValue`. -/
noncomputable def threeValue (T : Tensor3 K V) (τ : ℝ) : ℝ :=
  tauValue K (symThree K T) τ ^ ((3 : ℝ)⁻¹)

/-- **`V^{(6)}_τ(T)`, the six-symmetrized value** of `[DuanWuZhou2022]` §2.2, written as the sixth
root of the unsymmetrized value of `sym₆(T)`. -/
noncomputable def sixValue (T : Tensor3 K V) (τ : ℝ) : ℝ :=
  tauValue K (symSix K T) τ ^ ((6 : ℝ)⁻¹)

end NamedValues

section NamedValueLaws

variable {K : Type u} [CommSemiring K]
variable {V : Leg → Type v} [∀ c, AddCommMonoid (V c)] [∀ c, Module K (V c)]

/-- Turn a `k`th-power comparison into the `k`th-root comparison. -/
private theorem le_rpow_inv_of_pow_le {x B : ℝ} {k : ℕ} (hk : k ≠ 0) (hx : 0 ≤ x)
    (h : x ^ k ≤ B) : x ≤ B ^ (((k : ℕ) : ℝ)⁻¹) := by
  have hstep := Real.rpow_le_rpow (pow_nonneg hx k) h
    (by positivity : (0 : ℝ) ≤ (((k : ℕ) : ℝ))⁻¹)
  rwa [Real.pow_rpow_inv_natCast hx hk] at hstep

/-- **`V^{(3)}_τ(T) ≥ V^{(nrot)}_τ(T)`.**

`[DuanWuZhou2022]` uses this in §6.3 — the global bound is stated through `V^{(6)}`, while the
parameter table supplies a *non-rotational* value for the component `T_{0,2,2}` — but never
states it.  It is the cube-root form of `tauValue_pow_three_le_tauValue_symThree`, and its
mathematical content is supermultiplicativity of the value under external products together with
invariance of the value under leg permutations.

Proof sketch: the three factors of `sym₃(T)` are `T` and its two rotations, each of which carries
every weighted extraction of `T`; multiplying the three weights gives `V^{(nrot)}(T)³` for
`sym₃(T)`, and taking cube roots is monotone. -/
theorem tauValue_le_threeValue {T : Tensor3 K V} {τ : ℝ}
    (hne : (tauValueValues K T τ).Nonempty)
    (hbounded : BddAbove (tauValueValues K (symThree K T) τ)) :
    tauValue K T τ ≤ threeValue K T τ := by
  obtain ⟨hpos, hcube⟩ := tauValue_pos_and_pow_three_le_tauValue_symThree hne hbounded
  have hstep := le_rpow_inv_of_pow_le (k := 3) (by norm_num) hpos.le hcube
  unfold threeValue
  rw [show ((3 : ℝ))⁻¹ = (((3 : ℕ) : ℝ))⁻¹ by norm_num]
  exact hstep

/-- **`V^{(6)}_τ(T) ≥ V^{(3)}_τ(T)`** (`[DuanWuZhou2022]`, §2.2, stated there without proof).

Proof sketch: `sym₆(T) = sym₃(T) ⊗ sym₃(T)^swap`, both factors carry every weighted extraction of
`sym₃(T)`, so `V^{(nrot)}(sym₆ T) ≥ V^{(nrot)}(sym₃ T)²`; taking sixth roots turns the square into
the cube root. -/
theorem threeValue_le_sixValue {T : Tensor3 K V} {τ : ℝ}
    (hne : (tauValueValues K (symThree K T) τ).Nonempty)
    (hbounded : BddAbove (tauValueValues K (symSix K T) τ)) :
    threeValue K T τ ≤ sixValue K T τ := by
  obtain ⟨hpos, hsq⟩ := tauValue_symThree_pos_and_pow_two_le_tauValue_symSix hne hbounded
  have hmono := Real.rpow_le_rpow (pow_nonneg hpos.le 2) hsq
    (by norm_num : (0 : ℝ) ≤ (6 : ℝ)⁻¹)
  have hrw : (tauValue K (symThree K T) τ ^ 2) ^ ((6 : ℝ)⁻¹) = threeValue K T τ := by
    unfold threeValue
    rw [← Real.rpow_natCast (tauValue K (symThree K T) τ) 2, ← Real.rpow_mul hpos.le]
    congr 1
    norm_num
  rw [hrw] at hmono
  exact hmono

end NamedValueLaws

/-! ## Watchlist item 10: `X`–`Y` symmetric tensors -/

section SwapSymmetric

variable {K : Type u} [CommSemiring K]
variable {V : Leg → Type v} [∀ c, AddCommMonoid (V c)] [∀ c, Module K (V c)]

/-- **For an `X`–`Y` symmetric tensor, swapping the legs of `sym₃(T)` recovers `sym₃(T)`.**

This is the content the paper's "i.e." in `component_value.tex` l.245 elides.  Proof sketch:
permuting an external product is factorwise, so `sym₃(T)^s` has factors `T^s`, `T^{cs}` and
`T^{c⁻¹s}`.  The hypothesis `T ≅ T^s` transports the first to `T`; for the other two, the
composite orientation identities `c·s = s·c⁻¹` and `c⁻¹·s = s·c` (`Tensor.cycle_trans_swapXY`,
`Tensor.cycle_symm_trans_swapXY` — conjugation by a transposition inverts the three-cycle)
rewrite them as `(T^s)^{c⁻¹}` and `(T^s)^c`, which the hypothesis transports to `T^{c⁻¹}` and
`T^c`.  The resulting product has the two rotations in the **reversed** order, and one
application of `Tensor.Isomorphic.external_swap_right` restores it. -/
theorem Isomorphic.permute_swapXY_symThree {T : Tensor3 K V}
    (hswap : Isomorphic T (Tensor.permute Tensor.swapXY T)) :
    Isomorphic (Tensor.permute Tensor.swapXY (symThree K T)) (symThree K T) := by
  have hA : Isomorphic (Tensor.permute Tensor.swapXY T) T := hswap.symm
  have h2 : Isomorphic (Tensor.permute Tensor.swapXY (Tensor.permute cycle T))
      (Tensor.permute cycle.symm T) :=
    (((Tensor.Isomorphic.of_eq
          (Tensor.permute_apply_trans cycle Tensor.swapXY T).symm).trans
        (Tensor.Isomorphic.permute_congr Tensor.cycle_trans_swapXY T)).trans
      (Tensor.Isomorphic.of_eq
        (Tensor.permute_apply_trans Tensor.swapXY cycle.symm T))).trans
      (hA.permute_legs cycle.symm)
  have h3 : Isomorphic (Tensor.permute Tensor.swapXY (Tensor.permute cycle.symm T))
      (Tensor.permute cycle T) :=
    (((Tensor.Isomorphic.of_eq
          (Tensor.permute_apply_trans cycle.symm Tensor.swapXY T).symm).trans
        (Tensor.Isomorphic.permute_congr Tensor.cycle_symm_trans_swapXY T)).trans
      (Tensor.Isomorphic.of_eq
        (Tensor.permute_apply_trans Tensor.swapXY cycle T))).trans
      (hA.permute_legs cycle)
  have hexp : Tensor.permute Tensor.swapXY (symThree K T) =
      Tensor.external
        (Tensor.external (Tensor.permute Tensor.swapXY T)
          (Tensor.permute Tensor.swapXY (Tensor.permute cycle T)))
        (Tensor.permute Tensor.swapXY (Tensor.permute cycle.symm T)) := by
    unfold symThree
    rw [Tensor.permute_external, Tensor.permute_external]
  rw [hexp]
  exact ((hA.external h2).external h3).trans
    (Tensor.Isomorphic.external_swap_right T (Tensor.permute cycle.symm T)
      (Tensor.permute cycle T))

/-- **`sym₆(T) ≅ sym₃(T)^{⊗2}` for an `X`–`Y` symmetric tensor** (`[DuanWuZhou2022]`,
`component_value.tex` l.245).

The paper asserts this without proof and without naming the hypothesis; the hypothesis is a
genuine legwise isomorphism `T ≅ T^swap`, and the proof is
`Isomorphic.permute_swapXY_symThree`. -/
theorem Isomorphic.symSix_of_swapSymmetric {T : Tensor3 K V}
    (hswap : Isomorphic T (Tensor.permute Tensor.swapXY T)) :
    Isomorphic (symSix K T) (Tensor.external (symThree K T) (symThree K T)) :=
  (Tensor.Isomorphic.refl (symThree K T)).external
    (Isomorphic.permute_swapXY_symThree hswap)

/-- **Every value certificate of `sym₆(T)` is a value certificate of `sym₃(T)` at twice the
length, for an `X`–`Y` symmetric `T`.**

Proof sketch: `sym₃(T)^{⊗2N}` is `(sym₃(T) ⊗ sym₃(T))^{⊗N}`, which is `sym₆(T)^{⊗N}` by
`Isomorphic.symSix_of_swapSymmetric`; the extraction data is copied unchanged. -/
noncomputable def TauValueCertificate.ofSymSixOfSwapSymmetric {T : Tensor3 K V}
    (hswap : Isomorphic T (Tensor.permute Tensor.swapXY T))
    (certificate : TauValueCertificate K (symSix K T)) :
    TauValueCertificate K (symThree K T) where
  power := certificate.power + certificate.power
  copies := certificate.copies
  xSize := certificate.xSize
  ySize := certificate.ySize
  zSize := certificate.zSize
  power_pos := by have := certificate.power_pos; omega
  copies_pos := certificate.copies_pos
  xSize_pos := certificate.xSize_pos
  ySize_pos := certificate.ySize_pos
  zSize_pos := certificate.zSize_pos
  degenerates := by
    refine Tensor.PolynomialDegenerates.trans
      (Tensor.PolynomialDegenerates.of_restricts ?_) certificate.degenerates
    obtain ⟨n, hn⟩ : ∃ n, certificate.power = n + 1 :=
      ⟨certificate.power - 1, by have := certificate.power_pos; omega⟩
    rw [hn]
    refine Tensor.Isomorphic.restricts ?_
    refine (Tensor.isomorphic_external_power (symThree K T) (n + 1) (n + 1)).symm.trans ?_
    refine (Tensor.Isomorphic.power_external_positive (symThree K T) (symThree K T) n).symm.trans ?_
    exact ((Isomorphic.symSix_of_swapSymmetric hswap).symm).power (n + 1)

/-- **`V^{(6)}_τ(sym₆ T)` is at most the square of `V^{(nrot)}_τ(sym₃ T)` for `X`–`Y` symmetric
`T`.**  This is the half of `V^{(3)} = V^{(6)}` that is *not* an instance of the general
comparison law: `V^{(6)}` reads only the even powers of `sym₃(T)`, hence sees a subfamily of the
certificates `V^{(3)}` reads. -/
theorem tauValue_symSix_le_pow_two_of_swapSymmetric {T : Tensor3 K V} {τ : ℝ}
    (hswap : Isomorphic T (Tensor.permute Tensor.swapXY T))
    (hne : (tauValueValues K (symSix K T) τ).Nonempty)
    (hbounded : BddAbove (tauValueValues K (symThree K T) τ)) :
    tauValue K (symSix K T) τ ≤ tauValue K (symThree K T) τ ^ 2 := by
  refine csSup_le hne ?_
  rintro x ⟨c, rfl⟩
  set d := TauValueCertificate.ofSymSixOfSwapSymmetric hswap c with hd
  have hdle : d.term τ ≤ tauValue K (symThree K T) τ := d.le_tauValue hbounded
  set S := matrixMultiplicationVolumePowerSum c.xSize c.ySize c.zSize τ with hS
  have hSpos : 0 < S := matrixMultiplicationVolumePowerSum_pos c.copies_pos c.xSize_pos
    c.ySize_pos c.zSize_pos τ
  have hterm : c.term τ = d.term τ ^ 2 := by
    show S ^ (((c.power : ℕ) : ℝ)⁻¹) = (S ^ (((c.power + c.power : ℕ) : ℝ)⁻¹)) ^ 2
    rw [← Real.rpow_natCast (S ^ (((c.power + c.power : ℕ) : ℝ)⁻¹)) 2, ← Real.rpow_mul hSpos.le]
    congr 1
    have hpos : (0 : ℝ) < ((c.power : ℕ) : ℝ) := by
      exact_mod_cast c.power_pos
    push_cast
    field_simp
    ring
  rw [hterm]
  exact pow_le_pow_left₀ (d.term_pos τ).le hdle 2

/-- **`V^{(3)}_τ(T) = V^{(6)}_τ(T)` for an `X`–`Y` symmetric tensor** (`[DuanWuZhou2022]`,
`component_value.tex` l.245).  The paper's assertion is correct; the hypothesis it leaves implicit
is the legwise isomorphism `T ≅ T^swap`. -/
theorem sixValue_eq_threeValue_of_swapSymmetric {T : Tensor3 K V} {τ : ℝ}
    (hswap : Isomorphic T (Tensor.permute Tensor.swapXY T))
    (hne3 : (tauValueValues K (symThree K T) τ).Nonempty)
    (hne6 : (tauValueValues K (symSix K T) τ).Nonempty)
    (hbounded3 : BddAbove (tauValueValues K (symThree K T) τ))
    (hbounded6 : BddAbove (tauValueValues K (symSix K T) τ)) :
    sixValue K T τ = threeValue K T τ := by
  refine le_antisymm ?_ (threeValue_le_sixValue hne3 hbounded6)
  obtain ⟨hpos3, -⟩ := tauValue_symThree_pos_and_pow_two_le_tauValue_symSix hne3 hbounded6
  have hle := tauValue_symSix_le_pow_two_of_swapSymmetric hswap hne6 hbounded3
  have hnonneg6 : 0 ≤ tauValue K (symSix K T) τ := by
    obtain ⟨x, c, rfl⟩ := hne6
    exact (c.term_pos τ).le.trans (c.le_tauValue hbounded6)
  have hmono := Real.rpow_le_rpow hnonneg6 hle (by norm_num : (0 : ℝ) ≤ (6 : ℝ)⁻¹)
  have hrw : (tauValue K (symThree K T) τ ^ 2) ^ ((6 : ℝ)⁻¹) = threeValue K T τ := by
    unfold threeValue
    rw [← Real.rpow_natCast (tauValue K (symThree K T) τ) 2, ← Real.rpow_mul hpos3.le]
    congr 1
    norm_num
  rw [hrw] at hmono
  exact hmono

end SwapSymmetric

/-! ## The bridge to the repository's `V^{(3)}` -/

section DegenerationValueBridge

variable {K : Type u} [CommSemiring K]
variable {V : Leg → Type v} [∀ c, AddCommMonoid (V c)] [∀ c, Module K (V c)]

/-- A cyclic polynomial-degeneration certificate of `T` is a value certificate of `sym₃(T)` of the
same length. -/
noncomputable def CyclicDegenerationCertificate.toTauValueCertificateSymThree {T : Tensor3 K V}
    {τ : ℝ} (certificate : CyclicDegenerationCertificate K T τ) :
    TauValueCertificate K (symThree K T) where
  power := certificate.power
  copies := certificate.copies
  xSize := certificate.xSize
  ySize := certificate.ySize
  zSize := certificate.zSize
  power_pos := certificate.power_pos
  copies_pos := certificate.copies_pos
  xSize_pos := certificate.xSize_pos
  ySize_pos := certificate.ySize_pos
  zSize_pos := certificate.zSize_pos
  degenerates := by
    refine Tensor.PolynomialDegenerates.trans
      (Tensor.PolynomialDegenerates.of_restricts ?_) certificate.extraction
    obtain ⟨n, hn⟩ : ∃ n, certificate.power = n + 1 :=
      ⟨certificate.power - 1, by have := certificate.power_pos; omega⟩
    rw [hn]
    exact (Isomorphic.cyclicPowerProduct_positive T n).symm.restricts

/-- A value certificate of `sym₃(T)` is a cyclic polynomial-degeneration certificate of `T` of the
same length. -/
noncomputable def TauValueCertificate.toCyclicDegenerationCertificate {T : Tensor3 K V}
    (certificate : TauValueCertificate K (symThree K T)) (τ : ℝ) :
    CyclicDegenerationCertificate K T τ where
  power := certificate.power
  copies := certificate.copies
  xSize := certificate.xSize
  ySize := certificate.ySize
  zSize := certificate.zSize
  power_pos := certificate.power_pos
  copies_pos := certificate.copies_pos
  xSize_pos := certificate.xSize_pos
  ySize_pos := certificate.ySize_pos
  zSize_pos := certificate.zSize_pos
  extraction := by
    show Tensor.PolynomialDegenerates (cyclicPowerProduct K T certificate.power) _
    refine Tensor.PolynomialDegenerates.trans
      (Tensor.PolynomialDegenerates.of_restricts ?_) certificate.degenerates
    obtain ⟨n, hn⟩ : ∃ n, certificate.power = n + 1 :=
      ⟨certificate.power - 1, by have := certificate.power_pos; omega⟩
    rw [hn]
    exact (Isomorphic.cyclicPowerProduct_positive T n).restricts

/-- The cyclic term is the cube root of the corresponding unsymmetrized term. -/
private theorem cyclic_term_eq_rpow {S : ℝ} (hS : 0 < S) {k : ℕ} (hk : 0 < k) :
    S ^ (((3 * k : ℕ) : ℝ)⁻¹) = (S ^ (((k : ℕ) : ℝ)⁻¹)) ^ ((3 : ℝ)⁻¹) := by
  rw [← Real.rpow_mul hS.le]
  congr 1
  have hpos : (0 : ℝ) < ((k : ℕ) : ℝ) := by exact_mod_cast hk
  push_cast
  field_simp

/-- **`V^{(3)}_τ(T) ≤ threeValue K T τ`** — the repository's cyclic degeneration value is bounded
by the cube root of the unsymmetrized value of `sym₃(T)`. -/
theorem degenerationValue_le_threeValue {T : Tensor3 K V} {τ : ℝ}
    (hne : (degenerationValueValues K T τ).Nonempty)
    (hbounded : BddAbove (tauValueValues K (symThree K T) τ)) :
    degenerationValue K T τ ≤ threeValue K T τ := by
  refine csSup_le hne ?_
  rintro x ⟨c, rfl⟩
  set d := CyclicDegenerationCertificate.toTauValueCertificateSymThree c with hd
  have hdle : d.term τ ≤ tauValue K (symThree K T) τ := d.le_tauValue hbounded
  set S := matrixMultiplicationVolumePowerSum c.xSize c.ySize c.zSize τ with hS
  have hSpos : 0 < S := matrixMultiplicationVolumePowerSum_pos c.copies_pos c.xSize_pos
    c.ySize_pos c.zSize_pos τ
  have hterm : CyclicExtractionCertificate.term (K := K) c = d.term τ ^ ((3 : ℝ)⁻¹) :=
    cyclic_term_eq_rpow hSpos c.power_pos
  rw [hterm]
  exact Real.rpow_le_rpow (d.term_pos τ).le hdle (by norm_num)

/-- **`threeValue K T τ ≤ V^{(3)}_τ(T)`** — the reverse comparison; together with
`degenerationValue_le_threeValue` it identifies `threeValue` with the repository's existing
three-symmetrized value. -/
theorem threeValue_le_degenerationValue {T : Tensor3 K V} {τ : ℝ}
    (hne : (tauValueValues K (symThree K T) τ).Nonempty)
    (hbounded : BddAbove (degenerationValueValues K T τ)) :
    threeValue K T τ ≤ degenerationValue K T τ := by
  obtain ⟨x₀, c₀, hx₀⟩ := hne
  have hdegpos : 0 < degenerationValue K T τ := by
    refine lt_of_lt_of_le ?_ (CyclicDegenerationCertificate.le_degenerationValue K (c₀.toCyclicDegenerationCertificate τ) hbounded)
    exact CyclicExtractionCertificate.term_pos K _
  have hcube : ∀ u ∈ tauValueValues K (symThree K T) τ, u ≤ degenerationValue K T τ ^ 3 := by
    rintro u ⟨c, rfl⟩
    set S := matrixMultiplicationVolumePowerSum c.xSize c.ySize c.zSize τ with hS
    have hSpos : 0 < S := matrixMultiplicationVolumePowerSum_pos c.copies_pos c.xSize_pos
      c.ySize_pos c.zSize_pos τ
    have hle : CyclicExtractionCertificate.term (K := K) (c.toCyclicDegenerationCertificate τ) ≤
        degenerationValue K T τ :=
      CyclicDegenerationCertificate.le_degenerationValue K
        (c.toCyclicDegenerationCertificate τ) hbounded
    have hterm : CyclicExtractionCertificate.term (K := K) (c.toCyclicDegenerationCertificate τ) =
        c.term τ ^ ((3 : ℝ)⁻¹) := cyclic_term_eq_rpow hSpos c.power_pos
    rw [hterm] at hle
    have hpow := pow_le_pow_left₀ (Real.rpow_nonneg (c.term_pos τ).le _) hle 3
    rwa [show ((3 : ℝ))⁻¹ = (((3 : ℕ) : ℝ))⁻¹ by norm_num,
      Real.rpow_inv_natCast_pow (c.term_pos τ).le (by norm_num)] at hpow
  have hsup : tauValue K (symThree K T) τ ≤ degenerationValue K T τ ^ 3 :=
    csSup_le ⟨x₀, c₀, hx₀⟩ hcube
  have hmono := Real.rpow_le_rpow (le_trans (le_of_lt (c₀.term_pos τ))
    (by rw [hx₀]; exact le_csSup ⟨degenerationValue K T τ ^ 3, hcube⟩ ⟨c₀, hx₀⟩)) hsup
    (by norm_num : (0 : ℝ) ≤ (3 : ℝ)⁻¹)
  unfold threeValue
  rwa [show ((3 : ℝ))⁻¹ = (((3 : ℕ) : ℝ))⁻¹ by norm_num,
    Real.pow_rpow_inv_natCast hdegpos.le (by norm_num)] at hmono

end DegenerationValueBridge

end AlgebraicComplexity
