/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.GroupTensorBarrier
import AlgebraicComplexity.Examples.GeneralizedCoppersmithWinogradBarrier
import AlgebraicComplexity.Tensor.MonomialIndependence

/-!
# The group-tensor degeneration into generalized Coppersmith--Winograd tensors

This file is the first half of milestone **M** of `BARRIER_FRAMEWORK.md`: **Theorem 7.2** of
[AlmanVassilevskaWilliams2018], in the coefficient-table form the barrier program needs, together
with the asymptotic-independence-number inequality that theorem buys.

## References

* [AlmanVassilevskaWilliams2018] J. Alman and V. Vassilevska Williams,
  *Limits on all known (and some unknown) approaches to matrix multiplication*, arXiv:1810.08671.
  All numbered results below (`Definition 3.1`, `Corollary 4.2`, `Theorem 7.2`, ...) refer to it,
  and "AVW" abbreviates it, matching the sibling modules and `BARRIER_FRAMEWORK.md`.

## What is already in the tree, and what is added here

`Examples/GeneralizedCoppersmithWinograd.lean` already proves Theorem 7.2 for the *multiplicative*
presentation `T_G = ∑_{a,b} x_a y_b z_{ab}`: `groupTensorMul_monomialDegenerates_isGeneralizedCW`
exhibits AVW's weights `avwWeight` and identifies the leading term with a generalized
Coppersmith--Winograd tensor of parameter `|G| - 2`.  That statement is about *abstract tensors*.

Two things it deliberately does not do, and this file does:

1. **The symmetric presentation.**  The repository's primary group tensor is
   `Tensor.groupTensor K G = ∑_{a,b} x_a y_b z_{(ab)⁻¹}`, whose coefficient table is
   `Tensor.groupCoefficients` --- the table that every `Ī` and `ω_g^{coord}` statement of
   `Examples/GroupTensorBarrier.lean` is about.  Monomial degeneration is basis dependent, so the
   multiplicative certificate does not transport, and
   `groupTensor_polynomialDegeneratesAt_generalizedCW` could only record the weaker basis-free
   conclusion `PolynomialDegeneratesAt 2`.  Here AVW's weights are transported *by hand* to the
   symmetric presentation (`avwSymWeight`: `α` on `X` and `Y`, and `c ↦ 2 - α(c⁻¹)` on `Z`), which
   restores a genuine **monomial** certificate for `groupTensor K G`
   (`groupTensor_monomialDegenerates_isGeneralizedCW`).
2. **The coefficient-table form, hence the barrier consequence.**  `Ī` is a function of a
   coefficient table, so the abstract statement of Theorem 7.2 has no `Ī` content on its own.  The
   explicit minimum-weight identification `minimumWeightPart_avwSymWeight` says that the
   minimum-weight part of `groupCoefficients K G` for the weights `avwSymWeight g` and threshold
   `2` *is* the generalized Coppersmith--Winograd table `gcwTable` of
   `Examples/GeneralizedCoppersmithWinogradBarrier.lean`, up to a legwise renaming of variables.
   AVW Corollary 4.2 (`Tensor.asymptoticIndependenceNumber_minimumWeightPart_le`) then gives the
   inequality Theorem 7.2 buys:

   `Ī(CW_{|G|-2}^{σ_g}) ≤ Ī(T_G)`,  `σ_g(h) = h⁻¹ g`.

## AVW's weights in the symmetric presentation

AVW fix `g ≠ 1` and use the integer weights `α(x_1) = β(y_1) = γ(z_1) = 0`,
`α(x_g) = β(y_g) = -γ(z_g) = 2`, and `α(x_h) = β(y_h) = -γ(z_h) = 1` otherwise, on the terms
`x_a y_b z_{ab}`.  In the symmetric presentation the `Z` variable of the term `x_a y_b` is
`(ab)⁻¹` rather than `ab`, so the `Z` weight is composed with inversion; shifting it by the
constant `2` to land in `ℕ` (the repository's certificates carry `ℕ` weights, see
`BARRIER_FRAMEWORK.md` §2.1) gives

`w_X = w_Y = α`,  `w_Z(c) = 2 - α(c⁻¹)`,  threshold `d = 2`.

On a support triple `(a, b, (ab)⁻¹)` the total weight is `α(a) + α(b) + (2 - α(ab))`, which is
literally AVW's total weight on `x_a y_b z_{ab}`, so all the arithmetic of
`Examples/GeneralizedCoppersmithWinograd.lean` (`avwAlpha_mul_le`, `avwAlpha_add_eq_iff`,
`monomialTotalWeight_avwTriple_eq_two_iff`) is reused verbatim; nothing is reproved.

## Deviation from the letter of the paper

* AVW state Theorem 7.2 as "`T_G` degenerates to a generalized CW tensor of parameter `|G| - 2`",
  with no permutation named.  The permutation is not arbitrary: it is `σ_g(h) = h⁻¹ g` on the
  middle block `G \ {1, g}` (`avwPerm`), and the results below name it.  For `G` abelian --- AVW's
  stated hypothesis at the point of use --- `σ_g` is an involution.  Nothing here needs
  commutativity, so the hypothesis is dropped: every statement holds for an arbitrary finite
  group, exactly as `Examples/GeneralizedCoppersmithWinograd.lean` already found.
* The target is a *member of the generalized family* `CW_q^σ` of AVW Definition 3.1, **not** the
  standard `CW_q`; `CW_q` is the member with `σ = 1` (`coppersmithWinograd_isGeneralizedCW`), and
  `σ_g = 1` only when `h⁻¹g = h` for every `h ∉ {1, g}`, i.e. only for very small `G`.  The border
  rank of `CW_q^σ` is not claimed for `σ ≠ 1`; see the non-goals of
  `Examples/GeneralizedCoppersmithWinograd.lean`.
* AVW's Theorem 7.2 has no independence-number content; the consequence recorded here is their
  Corollary 4.2 applied to it, which is how Section 7 uses the theorem.

## The basis-dependence witness

`BARRIER_FRAMEWORK.md` §6 asks for the `ℚ` witness that `I` is not an isomorphism invariant.  It is
**already proved**, in `Tensor/IndependenceNumber.lean`, as
`Tensor.HadamardWitness.independenceNumber_not_isomorphism_invariant`: the table of `⟨2⟩` has
`I = 2`, the legwise change of basis `[[1, 1], [1, -1]]` produces the table `1 + s_a s_b s_c`, and
that table has `I = 1`.  It is not restated here.

What §1 of the framework asserts but the tree does not yet prove is the *identification* of that
transformed table: it is `2·T_{C₂}`.  The last section closes exactly that gap
(`hadamardCoefficients_eq_smul_groupCoefficients`) and re-derives `I = 1` from the group-theoretic
computation `independenceNumber_groupCoefficients_zmod_two` instead of from the bespoke sign
argument, so the two independent computations are on the record as agreeing.

## Layer placement

Layer 4, a paper client under `AlgebraicComplexity/Examples/`.  It imports only lower layers and
two sibling clients (`Examples/GroupTensorBarrier.lean`, milestone **L**, and
`Examples/GeneralizedCoppersmithWinogradBarrier.lean`, milestone **K**), plus the layer-1
minimum-weight machinery `Tensor/MonomialIndependence.lean` (milestone **C**).  Nothing here is
imported by a lower layer.

## Not attempted

AVW Theorems 7.3 and 7.4 (a *lower* bound `Ī(CW_q^σ) ≥ (q+2)^{2/f(q)}` from a symmetric
single-tensor zeroing out of `CW_q^{⊗n}`, parametric in `q`) are research-scale and are recorded as
open in `BARRIER_FRAMEWORK.md` §6, milestone **M**.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor Tensor.MonomialIndependence

universe u v

/-! ## AVW's weights transported to the symmetric presentation -/

section Weights

variable {K : Type u} [CommSemiring K] {G : Type v} [Group G] [Fintype G] [DecidableEq G]

/-- AVW's monomial weights on the **symmetric** presentation `T_G = ∑_{a,b} x_a y_b z_{(ab)⁻¹}`:
`α` on the `X` and `Y` legs and `c ↦ 2 - α(c⁻¹)` on the `Z` leg, where `α = avwAlpha g` is the
weight function of `Examples/GeneralizedCoppersmithWinograd.lean`.

This is `avwWeight` composed with inversion on the `Z` leg, which is exactly the change of variable
between the multiplicative and the symmetric presentation of the group tensor. -/
def avwSymWeight (g : G) : ∀ c, GroupIndex G c → ℕ
  | .X => avwAlpha g
  | .Y => avwAlpha g
  | .Z => fun h ↦ 2 - avwAlpha g h⁻¹

omit [Fintype G] in
@[simp] theorem avwSymWeight_X (g a : G) : avwSymWeight g .X a = avwAlpha g a := rfl

omit [Fintype G] in
@[simp] theorem avwSymWeight_Y (g a : G) : avwSymWeight g .Y a = avwAlpha g a := rfl

omit [Fintype G] in
@[simp] theorem avwSymWeight_Z (g a : G) : avwSymWeight g .Z a = 2 - avwAlpha g a⁻¹ := rfl

omit [Fintype G] in
/-- A triple of the support of the symmetric group table has the same total weight as the
corresponding term `x_a y_b z_{ab}` of the multiplicative presentation, because
`(ab)⁻¹ ↦ ab` under the inversion built into `avwSymWeight`. -/
theorem monomialTotalWeight_avwSymWeight (g : G) {p : ∀ c, GroupIndex G c}
    (h : p .X * p .Y * p .Z = 1) :
    monomialTotalWeight (avwSymWeight g) p =
      monomialTotalWeight (avwWeight g) (avwTriple (p .X, p .Y)) := by
  have hz : (p .Z)⁻¹ = p .X * p .Y := (eq_inv_of_mul_eq_one_left h).symm
  rw [monomialTotalWeight_avwTriple]
  show avwSymWeight g .X (p .X) + avwSymWeight g .Y (p .Y) + avwSymWeight g .Z (p .Z) = _
  rw [avwSymWeight_X, avwSymWeight_Y, avwSymWeight_Z, hz]

omit [Fintype G] in
/-- Every term of the symmetric group table has total weight at least `2`, so `2` is a legitimate
threshold for the minimum-weight certificate.  This is `two_le_monomialTotalWeight_avwTriple`. -/
theorem two_le_monomialTotalWeight_avwSymWeight (g : G) {p : ∀ c, GroupIndex G c}
    (h : p .X * p .Y * p .Z = 1) : 2 ≤ monomialTotalWeight (avwSymWeight g) p := by
  rw [monomialTotalWeight_avwSymWeight g h]
  exact two_le_monomialTotalWeight_avwTriple g _

omit [Fintype G] in
/-- The terms of the symmetric group table of minimal total weight are exactly AVW's surviving
terms: `a = 1`, or `b = 1`, or `a ∉ {1, g}` and `ab = g`.  This is
`monomialTotalWeight_avwTriple_eq_two_iff`. -/
theorem monomialTotalWeight_avwSymWeight_eq_two_iff {g : G} (hg : g ≠ 1)
    {p : ∀ c, GroupIndex G c} (h : p .X * p .Y * p .Z = 1) :
    monomialTotalWeight (avwSymWeight g) p = 2 ↔
      (p .X = 1 ∨ p .Y = 1 ∨ (p .X ≠ 1 ∧ p .X ≠ g ∧ p .X * p .Y = g)) := by
  rw [monomialTotalWeight_avwSymWeight g h]
  exact monomialTotalWeight_avwTriple_eq_two_iff hg _ _

omit [Fintype G] in
/-- A term of the symmetric group table with a nonzero coefficient satisfies `abc = 1`.  Stated
without `Nontrivial K`, unlike `groupCoefficients_ne_zero_iff`: only this direction is needed and
it holds over every commutative semiring. -/
theorem mul_eq_one_of_groupCoefficients_ne_zero {p : ∀ c, GroupIndex G c}
    (h : groupCoefficients K G p ≠ 0) : p .X * p .Y * p .Z = 1 := by
  by_contra hc
  exact h (by rw [groupCoefficients_apply, if_neg hc])

end Weights

/-! ## The legwise renaming onto the generalized Coppersmith--Winograd index set -/

section Renaming

variable {G : Type v} [Group G] [Fintype G] [DecidableEq G]

omit [Fintype G] in
/-- `avwIndexEquiv` sends exactly the identity to the distinguished coordinate `0`. -/
theorem avwIndexEquiv_eq_zero_iff {g : G} (hg : g ≠ 1) (a : G) :
    avwIndexEquiv hg a = .zero ↔ a = 1 := by
  rw [← avwIndexEquiv_one hg, Equiv.apply_eq_iff_eq]

omit [Fintype G] in
/-- `avwIndexEquiv` sends exactly `g` to the distinguished coordinate `q + 1`. -/
theorem avwIndexEquiv_eq_last_iff {g : G} (hg : g ≠ 1) (a : G) :
    avwIndexEquiv hg a = .last ↔ a = g := by
  rw [← avwIndexEquiv_self hg, Equiv.apply_eq_iff_eq]

omit [Fintype G] in
/-- `avwIndexEquiv` sends a middle group element to the corresponding middle coordinate. -/
theorem avwIndexEquiv_eq_middle_iff {g : G} (hg : g ≠ 1) (a : G) (i : AVWMid g) :
    avwIndexEquiv hg a = .middle i ↔ a = i.1 := by
  rw [← avwIndexEquiv_mid hg i, Equiv.apply_eq_iff_eq]

/-- The legwise renaming of AVW Theorem 7.2 in the symmetric presentation: on the `X` and `Y` legs
it is `avwIndexEquiv` (`1 ↦ 0`, `g ↦ q + 1`, everything else a middle coordinate), and on the `Z`
leg it is inversion followed by `avwIndexEquiv` and the transposition of the two distinguished
coordinates.

The inversion is the difference from `avwLegEquiv` of `Examples/GeneralizedCoppersmithWinograd.lean`
and is exactly the change of variable between the two presentations of the group tensor; the
transposition is AVW's own, the surviving `Z` index `1` playing the role of `q + 1` and the
surviving `Z` index `g⁻¹` playing the role of `0`. -/
def avwSymLegEquiv {g : G} (hg : g ≠ 1) :
    ∀ c, GroupIndex G c ≃ GenCWIndexFamily (AVWMid g) c
  | .X => avwIndexEquiv hg
  | .Y => avwIndexEquiv hg
  | .Z => (Equiv.inv G).trans ((avwIndexEquiv hg).trans (Equiv.swap .zero .last))

omit [Fintype G] in
@[simp] theorem avwSymLegEquiv_X {g : G} (hg : g ≠ 1) (a : G) :
    avwSymLegEquiv hg .X a = avwIndexEquiv hg a := rfl

omit [Fintype G] in
@[simp] theorem avwSymLegEquiv_Y {g : G} (hg : g ≠ 1) (a : G) :
    avwSymLegEquiv hg .Y a = avwIndexEquiv hg a := rfl

omit [Fintype G] in
@[simp] theorem avwSymLegEquiv_Z {g : G} (hg : g ≠ 1) (a : G) :
    avwSymLegEquiv hg .Z a = Equiv.swap .zero .last (avwIndexEquiv hg a⁻¹) := rfl

omit [Fintype G] in
/-- On the `Z` leg the coordinate `0` is hit exactly by `g⁻¹`. -/
theorem avwSymLegEquiv_Z_eq_zero_iff {g : G} (hg : g ≠ 1) (a : G) :
    avwSymLegEquiv hg .Z a = .zero ↔ a = g⁻¹ := by
  rw [avwSymLegEquiv_Z, Equiv.apply_eq_iff_eq_symm_apply, Equiv.symm_swap,
    Equiv.swap_apply_left, avwIndexEquiv_eq_last_iff, inv_eq_iff_eq_inv]

omit [Fintype G] in
/-- On the `Z` leg the coordinate `q + 1` is hit exactly by the identity. -/
theorem avwSymLegEquiv_Z_eq_last_iff {g : G} (hg : g ≠ 1) (a : G) :
    avwSymLegEquiv hg .Z a = .last ↔ a = 1 := by
  rw [avwSymLegEquiv_Z, Equiv.apply_eq_iff_eq_symm_apply, Equiv.symm_swap,
    Equiv.swap_apply_right, avwIndexEquiv_eq_zero_iff, inv_eq_one]

omit [Fintype G] in
/-- On the `Z` leg the middle coordinate `i` is hit exactly by `i⁻¹`. -/
theorem avwSymLegEquiv_Z_eq_middle_iff {g : G} (hg : g ≠ 1) (a : G) (i : AVWMid g) :
    avwSymLegEquiv hg .Z a = .middle i ↔ a = (i.1)⁻¹ := by
  rw [avwSymLegEquiv_Z, Equiv.apply_eq_iff_eq_symm_apply, Equiv.symm_swap,
    GenCWIndex.swap_middle, avwIndexEquiv_eq_middle_iff, inv_eq_iff_eq_inv]

end Renaming

/-! ## The minimum-weight part is the generalized Coppersmith--Winograd table -/

section Identification

variable {K : Type u} [CommSemiring K] {G : Type v} [Group G] [Fintype G] [DecidableEq G]

omit [Fintype G] in
/-- **The combinatorial core of AVW Theorem 7.2.**  Under the legwise renaming `avwSymLegEquiv`,
the triples of `T_G` that both occur and have minimal total weight `2` are exactly the `3q + 3`
triples of the generalized Coppersmith--Winograd support of parameter `q = |G| - 2` with
permutation `σ_g(h) = h⁻¹ g`.

Proof sketch: for a triple with `abc = 1` the weight condition is
`monomialTotalWeight_avwSymWeight_eq_two_iff`, i.e. AVW's trichotomy `a = 1`, `b = 1`, or
`a ∉ {1, g}` with `ab = g`.  Splitting the free variable of each branch into `1`, `g` and the rest
produces the six displayed families of `GenCWSupport`; conversely each of the six families
determines `a`, `b`, `c` outright through the inversion lemmas of the previous section, and both
`abc = 1` and the trichotomy are then immediate. -/
theorem genCWSupport_avwSymLegEquiv_iff {g : G} (hg : g ≠ 1) (p : ∀ c, GroupIndex G c) :
    GenCWSupport (avwPerm g) (fun c ↦ avwSymLegEquiv hg c (p c)) ↔
      (p .X * p .Y * p .Z = 1 ∧ monomialTotalWeight (avwSymWeight g) p = 2) := by
  constructor
  · rintro (⟨hx, hy, hz⟩ | ⟨hx, hy, hz⟩ | ⟨hx, hy, hz⟩ | ⟨i, hx, hy, hz⟩ | ⟨i, hx, hy, hz⟩ |
      ⟨i, hx, hy, hz⟩) <;>
      simp only [avwSymLegEquiv_X, avwSymLegEquiv_Y, avwIndexEquiv_eq_zero_iff,
        avwIndexEquiv_eq_last_iff, avwIndexEquiv_eq_middle_iff, avwSymLegEquiv_Z_eq_zero_iff,
        avwSymLegEquiv_Z_eq_last_iff, avwSymLegEquiv_Z_eq_middle_iff, avwPerm_coe] at hx hy hz
    · have hprod : p .X * p .Y * p .Z = 1 := by rw [hx, hy, hz]; group
      exact ⟨hprod, (monomialTotalWeight_avwSymWeight_eq_two_iff hg hprod).mpr (Or.inl hx)⟩
    · have hprod : p .X * p .Y * p .Z = 1 := by rw [hx, hy, hz]; group
      exact ⟨hprod, (monomialTotalWeight_avwSymWeight_eq_two_iff hg hprod).mpr (Or.inl hx)⟩
    · have hprod : p .X * p .Y * p .Z = 1 := by rw [hx, hy, hz]; group
      exact ⟨hprod, (monomialTotalWeight_avwSymWeight_eq_two_iff hg hprod).mpr
        (Or.inr (Or.inl hy))⟩
    · have hprod : p .X * p .Y * p .Z = 1 := by rw [hx, hy, hz]; group
      refine ⟨hprod, (monomialTotalWeight_avwSymWeight_eq_two_iff hg hprod).mpr
        (Or.inr (Or.inr ⟨?_, ?_, ?_⟩))⟩
      · rw [hx]; exact i.2.1
      · rw [hx]; exact i.2.2
      · rw [hx, hy]; group
    · have hprod : p .X * p .Y * p .Z = 1 := by rw [hx, hy, hz]; group
      exact ⟨hprod, (monomialTotalWeight_avwSymWeight_eq_two_iff hg hprod).mpr
        (Or.inr (Or.inl hy))⟩
    · have hprod : p .X * p .Y * p .Z = 1 := by rw [hx, hy, hz]; group
      exact ⟨hprod, (monomialTotalWeight_avwSymWeight_eq_two_iff hg hprod).mpr (Or.inl hx)⟩
  · rintro ⟨hprod, hw⟩
    have hz : p .Z = (p .X * p .Y)⁻¹ := eq_inv_of_mul_eq_one_right hprod
    simp only [GenCWSupport, avwSymLegEquiv_X, avwSymLegEquiv_Y, avwIndexEquiv_eq_zero_iff,
      avwIndexEquiv_eq_last_iff, avwIndexEquiv_eq_middle_iff, avwSymLegEquiv_Z_eq_zero_iff,
      avwSymLegEquiv_Z_eq_last_iff, avwSymLegEquiv_Z_eq_middle_iff, avwPerm_coe]
    rcases (monomialTotalWeight_avwSymWeight_eq_two_iff hg hprod).mp hw with
      ha | hb | ⟨ha1, hag, hab⟩
    · -- `a = 1`; split on `b`
      by_cases hb1 : p .Y = 1
      · exact Or.inl ⟨ha, hb1, by rw [hz, ha, hb1]; group⟩
      by_cases hbg : p .Y = g
      · exact Or.inr (Or.inl ⟨ha, hbg, by rw [hz, ha, hbg]; group⟩)
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          ⟨⟨p .Y, hb1, hbg⟩, ha, rfl, by rw [hz, ha]; group⟩))))
    · -- `b = 1`; split on `a`
      by_cases ha1 : p .X = 1
      · exact Or.inl ⟨ha1, hb, by rw [hz, ha1, hb]; group⟩
      by_cases hag : p .X = g
      · exact Or.inr (Or.inr (Or.inl ⟨hag, hb, by rw [hz, hag, hb]; group⟩))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
          ⟨⟨p .X, ha1, hag⟩, rfl, hb, by rw [hz, hb]; group⟩))))
    · -- `a ∉ {1, g}` and `ab = g`
      have hb1 : p .Y ≠ 1 := by
        rintro hc
        exact hag (by rw [← hab, hc, mul_one])
      have hbg : p .Y ≠ g := by
        rintro hc
        rw [hc] at hab
        exact ha1 (by simpa using hab)
      refine Or.inr (Or.inr (Or.inr (Or.inl ⟨⟨p .X, ha1, hag⟩, rfl, ?_, ?_⟩)))
      · show p .Y = (p .X)⁻¹ * g
        rw [← hab]; group
      · rw [hz, hab]

/-- **AVW Theorem 7.2, coefficient-table form.**  The minimum-weight part of the coefficient table
of the symmetric group tensor `T_G`, for AVW's weights `avwSymWeight g` and threshold `2`, is the
coefficient table of the generalized Coppersmith--Winograd tensor of parameter `|G| - 2` with
permutation `σ_g(h) = h⁻¹ g`, read through the legwise renaming `avwSymLegEquiv`.

Both sides are `0`/`1` tables, so this is exactly `genCWSupport_avwSymLegEquiv_iff`. -/
theorem minimumWeightPart_avwSymWeight {g : G} (hg : g ≠ 1) :
    minimumWeightPart (avwSymWeight g) 2 (groupCoefficients K G) =
      coordinateRelabel (fun c ↦ (avwSymLegEquiv hg c).symm)
        (gcwTable K (AVWMid g) (avwPerm g)) := by
  funext p
  rw [coordinateRelabel_apply]
  have hs : (fun c ↦ ((avwSymLegEquiv hg c).symm).symm (p c)) =
      fun c ↦ avwSymLegEquiv hg c (p c) := by
    funext c
    rw [Equiv.symm_symm]
  rw [hs, gcwTable_apply]
  show (if monomialTotalWeight (avwSymWeight g) p = 2 then groupCoefficients K G p else 0) = _
  by_cases hprod : p .X * p .Y * p .Z = 1
  · rw [groupCoefficients_of_mul_eq_one hprod]
    refine if_congr ?_ rfl rfl
    rw [genCWSupport_avwSymLegEquiv_iff hg]
    exact ⟨fun h ↦ ⟨hprod, h⟩, fun h ↦ h.2⟩
  · rw [groupCoefficients_apply, if_neg hprod, ite_self,
      if_neg (fun hc ↦ hprod ((genCWSupport_avwSymLegEquiv_iff hg p).mp hc).1)]

end Identification

/-! ## The monomial degeneration of the symmetric group tensor -/

section Degeneration

variable {K : Type u} [CommSemiring K] {G : Type v} [Group G] [Fintype G] [DecidableEq G]

/-- The minimum-weight part of `T_G` presents a generalized Coppersmith--Winograd tensor on the
middle block `G \ {1, g}`. -/
theorem isomorphic_coordinateTensor_minimumWeightPart_genCW {g : G} (hg : g ≠ 1) :
    Isomorphic (coordinateTensor (minimumWeightPart (avwSymWeight g) 2 (groupCoefficients K G)))
      (genCW K (AVWMid g) (avwPerm g)) := by
  rw [minimumWeightPart_avwSymWeight hg]
  have h := (Isomorphic.coordinateTensor_coordinateRelabel
    (fun c ↦ (avwSymLegEquiv hg c).symm) (gcwTable K (AVWMid g) (avwPerm g))).symm
  rwa [coordinateTensor_gcwTable] at h

/-- **AVW Theorem 7.2 for the symmetric presentation, explicit form.**  For a finite group `G` and
any `g ≠ 1`, the repository's group tensor `T_G = ∑_{a,b} x_a y_b z_{(ab)⁻¹}` *monomially*
degenerates to a generalized Coppersmith--Winograd tensor of parameter `|G| - 2`.

This strengthens `groupTensor_polynomialDegeneratesAt_generalizedCW` of
`Examples/GeneralizedCoppersmithWinograd.lean`, which could only record the basis-free conclusion
`PolynomialDegeneratesAt 2` because it obtained the certificate for the multiplicative presentation
and transported it along a relabelling.  Here the weights are written down in the symmetric
presentation directly (`avwSymWeight`), so the certificate is monomial on the nose.

Proof sketch: `monomialDegenerates_coordinateTensor_minimumWeightPart` turns the weight bound
`two_le_monomialTotalWeight_avwSymWeight` into the certificate, `coordinateTensor_groupCoefficients`
identifies the source with `groupTensor K G`,
`isomorphic_coordinateTensor_minimumWeightPart_genCW` identifies the leading term with `CW^{σ_g}` on
the middle block `G \ {1, g}`, and `genCW_isomorphic_congr` transports that along any bijection
`G \ {1, g} ≃ Fin (|G| - 2)`, which exists by `card_AVWMid`. -/
theorem groupTensor_monomialDegenerates_isGeneralizedCW {g : G} (hg : g ≠ 1) :
    MonomialDegenerates (groupTensor K G)
        (coordinateTensor (minimumWeightPart (avwSymWeight g) 2 (groupCoefficients K G))) ∧
      IsGeneralizedCW K (Fintype.card G - 2)
        (coordinateTensor (minimumWeightPart (avwSymWeight g) 2 (groupCoefficients K G))) := by
  classical
  constructor
  · have h := monomialDegenerates_coordinateTensor_minimumWeightPart (avwSymWeight g) 2
      (groupCoefficients K G)
      (fun p hp ↦ two_le_monomialTotalWeight_avwSymWeight g
        (mul_eq_one_of_groupCoefficients_ne_zero hp))
    rwa [coordinateTensor_groupCoefficients] at h
  · let ε : AVWMid g ≃ Fin (Fintype.card G - 2) := Fintype.equivFinOfCardEq (card_AVWMid hg)
    exact ⟨Equiv.permCongr ε (avwPerm g),
      (isomorphic_coordinateTensor_minimumWeightPart_genCW hg).trans
        (genCW_isomorphic_congr ε (avwPerm g))⟩

/-- **AVW Theorem 7.2 for the symmetric presentation.**  For every finite group with at least two
elements, the group tensor `T_G` monomially degenerates to a generalized Coppersmith--Winograd
tensor of parameter `|G| - 2`. -/
theorem exists_groupTensor_monomialDegenerates_isGeneralizedCW [Nontrivial G] :
    ∃ T : Tensor3 K (GroupSpace K G),
      MonomialDegenerates (groupTensor K G) T ∧
        IsGeneralizedCW K (Fintype.card G - 2) T := by
  obtain ⟨g, hg⟩ := exists_ne (1 : G)
  exact ⟨_, groupTensor_monomialDegenerates_isGeneralizedCW hg⟩

end Degeneration

/-! ## The consequence for the asymptotic independence number -/

section Consequence

variable {K : Type u} [CommSemiring K] [NoZeroDivisors K] [Nontrivial K]
variable {G : Type v} [Group G] [Fintype G] [DecidableEq G]

/-- **AVW Theorem 7.2 combined with Corollary 4.2.**  The asymptotic independence number of the
generalized Coppersmith--Winograd table of parameter `|G| - 2` and permutation `σ_g(h) = h⁻¹ g` is
at most that of the group table:

`Ī(CW_{|G|-2}^{σ_g}) ≤ Ī(T_G)`.

This is the inequality that Theorem 7.2 exists to buy, and it is the only form in which a monomial
degeneration can feed the independence number: the corresponding finite statement
`I(CW_{|G|-2}^{σ_g}) ≤ I(T_G)` is **false in general** and is never claimed (see the "deliberately
not proved" section of `Tensor/MonomialIndependence.lean`).

Proof sketch: `Tensor.asymptoticIndependenceNumber_minimumWeightPart_le` (AVW Corollary 4.2) bounds
`Ī` of the minimum-weight part by `Ī` of the table; `minimumWeightPart_avwSymWeight` identifies that
minimum-weight part with a legwise renaming of `gcwTable`, and `Ī` is invariant under legwise
renamings (`Tensor.asymptoticIndependenceNumber_coordinateRelabel`). -/
theorem asymptoticIndependenceNumber_gcwTable_le_groupCoefficients {g : G} (hg : g ≠ 1) :
    asymptoticIndependenceNumber (gcwTable K (AVWMid g) (avwPerm g)) ≤
      asymptoticIndependenceNumber (groupCoefficients K G) := by
  have h := asymptoticIndependenceNumber_minimumWeightPart_le (A := groupCoefficients K G)
    (avwSymWeight g) 2
    (fun p hp ↦ two_le_monomialTotalWeight_avwSymWeight g
      (mul_eq_one_of_groupCoefficients_ne_zero hp))
  rwa [minimumWeightPart_avwSymWeight hg, asymptoticIndependenceNumber_coordinateRelabel] at h

/-- The finite independence number of the generalized Coppersmith--Winograd table is bounded by the
*asymptotic* independence number of the group table.  The finite-to-finite comparison is
unavailable, so this is the sharpest statement of its kind. -/
theorem independenceNumber_gcwTable_le_asymptoticIndependenceNumber_groupCoefficients
    {g : G} (hg : g ≠ 1) :
    (independenceNumber (gcwTable K (AVWMid g) (avwPerm g)) : ℝ) ≤
      asymptoticIndependenceNumber (groupCoefficients K G) :=
  (independenceNumber_le_asymptoticIndependenceNumber _).trans
    (asymptoticIndependenceNumber_gcwTable_le_groupCoefficients hg)

/-- The parameter of the target really is `|G| - 2`: the middle block `G \ {1, g}` has that many
elements, so the target table has `|G|` variables on each leg. -/
theorem card_genCWIndex_avwMid {g : G} (hg : g ≠ 1) :
    Fintype.card (GenCWIndex (AVWMid g)) = Fintype.card G := by
  rw [GenCWIndex.card, card_AVWMid hg]
  have : 2 ≤ Fintype.card G := by
    have h1 : 1 < Fintype.card G := Fintype.one_lt_card_iff_nontrivial.mpr
      ⟨⟨g, 1, hg⟩⟩
    omega
  omega

end Consequence

section SawinConsequence

variable {K : Type u} [Field K] {G : Type v} [Group G] [Fintype G] [DecidableEq G]

/-- **A conditional barrier for one member of the generalized Coppersmith--Winograd family.**
Conditionally on Sawin's theorem for `G` (`SawinBound`, a named proof obligation --- never an
axiom, see `Examples/GroupTensorBarrier.lean`), the generalized Coppersmith--Winograd table of
parameter `|G| - 2` and permutation `σ_g(h) = h⁻¹ g` satisfies `Ī ≤ δ·|G|` for some `δ < 1`, that
is, `Ī` is bounded away from the number `|G| = q + 2` of variables per leg.

Proof sketch: `asymptoticIndependenceNumber_groupCoefficients_le_of_sawinBound` (AVW Corollary 6.1)
bounds `Ī(T_G)`, and `asymptoticIndependenceNumber_gcwTable_le_groupCoefficients` transfers the
bound along the degeneration of Theorem 7.2. -/
theorem asymptoticIndependenceNumber_gcwTable_le_of_sawinBound {g : G} (hg : g ≠ 1)
    (h : SawinBound G) :
    ∃ δ : ℝ, δ < 1 ∧ 1 ≤ δ * Fintype.card G ∧
      asymptoticIndependenceNumber (gcwTable K (AVWMid g) (avwPerm g)) ≤
        δ * Fintype.card G := by
  obtain ⟨δ, hδ, h1, hb⟩ :=
    asymptoticIndependenceNumber_groupCoefficients_le_of_sawinBound (K := K) h
  exact ⟨δ, hδ, h1, (asymptoticIndependenceNumber_gcwTable_le_groupCoefficients hg).trans hb⟩

end SawinConsequence

/-! ## The basis-dependence witness, identified with the group tensor of `C₂`

`BARRIER_FRAMEWORK.md` §1 says: over `ℚ`, the table of `⟨2⟩` has `I = 2`, while its image under the
legwise change of basis `[[1, 1], [1, -1]]` "is `2·T_{C₂}`", whose four support triples pairwise
share a coordinate, so `I = 1`.

Everything except the identification `2·T_{C₂}` is already proved in `Tensor/IndependenceNumber.lean`
(`Tensor.HadamardWitness.independenceNumber_not_isomorphism_invariant`, with the legwise isomorphism
`isomorphic_coordinateTensor_hadamardCoefficients` and the two computations
`independenceNumber_diagonalCoefficients_fin_two = 2` and
`independenceNumber_hadamardCoefficients = 1`); it is not restated here.  This section proves the
identification itself and re-derives `I = 1` from it, so that the sign argument of the tensor layer
and the tri-coloured sum-free computation of `Examples/GroupTensorBarrier.lean` are on the record as
agreeing. -/

section BasisDependence

/-- The two-element group as the index set of the basis-dependence witness. -/
def hadamardGroupEquiv : Multiplicative (ZMod 2) ≃ Fin 2 where
  toFun a := Multiplicative.toAdd a
  invFun i := Multiplicative.ofAdd i
  left_inv := by decide
  right_inv := by decide

/-- The support condition of `T_{C₂}` read through `hadamardGroupEquiv`: a triple of `Fin 2`
indices lies in the support exactly when the number of index-`1` entries is even.  A finite check
over the eight triples. -/
theorem hadamardGroupEquiv_symm_mul_eq_one_iff (a b c : Fin 2) :
    hadamardGroupEquiv.symm a * hadamardGroupEquiv.symm b * hadamardGroupEquiv.symm c = 1 ↔
      a + b + c = 0 := by
  revert a b c
  decide

/-- **The transformed table of the basis-dependence witness is `2·T_{C₂}`.**  This is the
identification asserted in `BARRIER_FRAMEWORK.md` §1: the image of the table of `⟨2⟩` under the
legwise change of basis `[[1, 1], [1, -1]]` is twice the coefficient table of the group tensor of
the two-element group.

Proof sketch: `1 + s_a s_b s_c` is `2` when the number of index-`1` entries is even and `0`
otherwise, and in `C₂` written additively that parity condition is `a + b + c = 0`, which is the
support condition `a·b·c = 1` of `groupCoefficients`.  Both sides are then checked on the eight
triples. -/
theorem hadamardCoefficients_eq_smul_groupCoefficients :
    Tensor.HadamardWitness.hadamardCoefficients =
      (2 : ℚ) • coordinateRelabel (fun _ : Leg ↦ hadamardGroupEquiv)
        (groupCoefficients ℚ (Multiplicative (ZMod 2))) := by
  funext p
  have hsupp : coordinateRelabel (fun _ : Leg ↦ hadamardGroupEquiv)
      (groupCoefficients ℚ (Multiplicative (ZMod 2))) p =
      if p .X + p .Y + p .Z = 0 then 1 else 0 := by
    rw [coordinateRelabel_apply, groupCoefficients_apply]
    simp only [hadamardGroupEquiv_symm_mul_eq_one_iff]
  have hcase : ∀ i : Leg, p i = 0 ∨ p i = 1 := by
    intro i
    omega
  rw [Pi.smul_apply, hsupp, smul_eq_mul]
  rcases hcase .X with hx | hx <;> rcases hcase .Y with hy | hy <;> rcases hcase .Z with hz | hz <;>
    norm_num [Tensor.HadamardWitness.hadamardCoefficients,
      Tensor.HadamardWitness.signCoefficient, hx, hy, hz] <;>
    decide

/-- **The witness table has independence number one, computed through the group tensor.**  An
independent second proof of `Tensor.HadamardWitness.independenceNumber_hadamardCoefficients`: the
table is `2·T_{C₂}` by `hadamardCoefficients_eq_smul_groupCoefficients`, scaling by the unit `2`
does not move the independence number, renaming variables does not move it either, and
`independenceNumber_groupCoefficients_zmod_two` evaluates `I(T_{C₂}) = 1` --- which is AVW Lemma 6.1
together with the tri-coloured sum-free number of `C₂`. -/
theorem independenceNumber_hadamardCoefficients_via_groupTensor :
    independenceNumber Tensor.HadamardWitness.hadamardCoefficients = 1 := by
  rw [hadamardCoefficients_eq_smul_groupCoefficients,
    Tensor.independenceNumber_smul_of_isUnit (by norm_num : IsUnit (2 : ℚ)),
    independenceNumber_coordinateRelabel, independenceNumber_groupCoefficients_zmod_two]

end BasisDependence

end AlgebraicComplexity.Examples
