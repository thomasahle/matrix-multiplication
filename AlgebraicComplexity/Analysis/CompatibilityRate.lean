/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Analysis.CompatibilityRateCore
import AlgebraicComplexity.Analysis.ProportionalMultinomial
import AlgebraicComplexity.Combinatorics.CompatibleSplitCount

/-!
# The Duan--Wu--Zhou compatibility rate `ᾱ_p` and the hole-fraction bound

Layer 2 (`AlgebraicComplexity/Analysis/`).  This module turns the exact counts of
`Combinatorics/CompatibleSplitCount.lean` into

> R. Duan, H. Wu and R. Zhou, *Faster Matrix Multiplication via Asymmetric Hashing*,
> arXiv:2210.10173v5, **§6.2 (`global_value.tex`)**: `lemma:pcomp_g`'s closed form for `ᾱ_p`,
> and the modulus arithmetic of `claim:hole_frac_low` (`[DuanWuZhou2022]`).

## `p_comp` and `ᾱ_p`

`p_comp` is DWZ's *combination loss* probability: the fraction of the typical small Z-blocks of a
large block `Z_K` that are compatible with one fixed large triple through `Z_K`.  Here it is
`compatibleFraction`, an exact rational, and `lemma:pcomp_g`'s computation of it is
`compatibleFraction_eq_prod_div_prod`: a product of multinomial coefficients over the requirement
cells divided by a product over the Z-indices.

`ᾱ_p = lim p_comp^{1/n}` is `compatibilityRate`.  Its logarithm is the normalized difference of
two conditional-entropy masses, and `compatibilityRateLog_eq_dwz` puts it in the paper's displayed
shape

`log₂ ᾱ_p = ∑_{i = 0 ∨ j = 0} α(i,j,k) H(α̃_{i,j,k}) + ∑_k α(+,+,k) H(α̃^avg_{+,+,k})`
`             − ∑_k α_Z(k) H(α̃^avg_{*,*,k})`,

which is DWZ's

`ᾱ_p = 2^{H(α_Z) − H(γ)} ∏_{i = 0 ∨ j = 0} 2^{α(i,j,k) H(α̃_{i,j,k})} ∏_k 2^{α(+,+,k) H(α̃^avg_{+,+,k})}`

once the entropy chain rule `H(γ) − H(α_Z) = ∑_k α_Z(k) H(α̃^avg_{*,*,k})` is applied to the
typicalness distribution `γ`.  The exact finite counterpart of that chain rule is proved:
it is `CompatibleSplit.SplitRequirements.multinomial_eq_mul_prod_rows` applied to
`typicalType`, whose first marginal is `α_Z` and whose rows are the `α̃^avg_{*,*,k}`.

## The hole-fraction bound

`claim:hole_frac_low` fixes a retained triple and a useful small Z-block and bounds the
probability that the block is a hole by `N_α · p_comp / (N_Z · M) ≤ 1/8`.  Two things are proved
here:

* `card_matchableCompatible_eq_mul_compatibleFraction` — the competitor count *is*
  `(N_α / N_Z) · p_comp` exactly, with no `o(n)`; this is the pair count of
  `CompatibleSplit.SplitRequirements.card_matchableCompatible_mul_card_typicalSet` restated as a
  rational identity.
* `eight_mul_card_matchableCompatible_le` and `holeFraction_le` — the modulus arithmetic:
  DWZ's second branch `M ≥ 8 · N_α · p_comp / N_Z` is exactly `8 · (competitor count) ≤ M`, and it
  gives a hole fraction at most `1/8`, hence a non-hole fraction at least `7/8`.

## Non-goals

The union bound over the competitors — the step that converts the competitor *count* into a hole
*probability* using the per-pair conditional independence of
`Combinatorics/HashingConditionalIndependence.lean` — is assembly work belonging to the global
value theorem (stage M-DWZ6) and is not done here.  What this module fixes is the number that the
modulus must dominate.

The asymptotic statement `p_comp = ᾱ_p^{n + o(n)}` is likewise not proved here: the
zero-tolerant method-of-types estimates that it needs (a compatibility profile has structurally
zero rows at every interior component) are not available in the layer this module may import.  The
exact product formula and the closed-form rate are stated so that the asymptotic step is a purely
mechanical application of those estimates once they are in place.

## Naming

`compatibilityRate` is DWZ's `ᾱ_p`; DWZ's *combination loss* is its reciprocal.  Neither is the
repository's existing `combinationLoss` (`Probability/TwoLetter.lean`), which is DWZ's *hash
loss* — see the naming paragraph of `Combinatorics/CompatibleSplitCount.lean`.
-/

namespace AlgebraicComplexity.CompatibleSplit

open AlgebraicComplexity.WordType
open scoped BigOperators

universe u v w

variable {C : Type u} {L : Type v} {Z : Type w}

namespace SplitRequirements

variable [Fintype C] [DecidableEq C] [Fintype L] [DecidableEq L] [Fintype Z] [DecidableEq Z]
variable (S : SplitRequirements C L Z)

/-! ### `p_comp` as an exact rational -/

variable {n : ℕ}

/-- DWZ's `p_comp`: the fraction of the typical small blocks of `Z_K` that are compatible with a
fixed large triple through `Z_K`.  Exact, with no `o(n)`. -/
noncomputable def compatibleFraction (comp : Fin n → C) (K : Fin n → Z) : ℚ :=
  ((S.compatibleSet comp).card : ℚ) / ((S.typicalSet K).card : ℚ)

variable {S}

/-- **`lemma:pcomp_g`, exactly.**  `p_comp` is the product of the multinomial coefficients of the
requirement cells — the boundary cells `S_{i,j,k}` with `i = 0` or `j = 0`, and the pooled cells
`S_{+,+,k}` — divided by the product over Z-indices of the multinomial coefficients of the average
splits on `S_{*,*,k}`. -/
theorem compatibleFraction_eq_prod_div_prod {αType : C → ℕ} (h : S.RefinesType αType)
    (comp : Fin n → C) (hcomp : multiplicity comp = αType) :
    S.compatibleFraction comp (S.zIndex ∘ comp) =
      (∏ r : C ⊕ Z, (Nat.multinomial Finset.univ fun l ↦ S.compatibleType (r, l) : ℚ)) /
        ∏ z : Z, (Nat.multinomial Finset.univ fun l ↦ S.typicalType (z, l) : ℚ) := by
  rw [compatibleFraction, card_compatibleSet_eq_prod h comp hcomp,
    card_typicalSet_eq_prod h comp hcomp]
  push_cast
  rfl

/-! ### The hole-fraction bound -/

/-- The competitor count of `claim:hole_frac_low` is exactly `(N_α / N_Z) · p_comp`: the number of
large triples through `Z_K` compatible with a fixed typical small block equals the number of large
triples through `Z_K` times `p_comp`.

Proof sketch: this is the pair count
`card_matchableCompatible_mul_card_typicalSet` divided by the (positive) number of typical
blocks. -/
theorem card_matchableCompatible_eq_mul_compatibleFraction {αType : C → ℕ} {K : Fin n → Z}
    {comp₀ : Fin n → C} (hcomp₀ : comp₀ ∈ S.matchable αType K)
    {w : Fin n → L} (hw : w ∈ S.typicalSet K) (htyp : 0 < (S.typicalSet K).card) :
    ((S.matchableCompatible αType K w).card : ℚ) =
      ((S.matchable αType K).card : ℚ) * S.compatibleFraction comp₀ K := by
  have hpair := card_matchableCompatible_mul_card_typicalSet hcomp₀ hw
  have hcast : ((S.matchableCompatible αType K w).card : ℚ) * ((S.typicalSet K).card : ℚ) =
      ((S.matchable αType K).card : ℚ) * ((S.compatibleSet comp₀).card : ℚ) := by
    exact_mod_cast congrArg (fun m : ℕ ↦ (m : ℚ)) hpair
  have hne : ((S.typicalSet K).card : ℚ) ≠ 0 := by
    simp only [ne_eq, Nat.cast_eq_zero]
    omega
  rw [compatibleFraction]
  field_simp
  linarith [hcast]

/-- **The modulus condition of `M_0`'s second branch.**  DWZ take
`M ≥ M_0 ≥ 8 · N_α · p_comp / N_Z`; in exact form that hypothesis says
`8 · N_α · |compatible blocks| ≤ M · N_Z · |T_K|`, and it forces `8` times the competitor count to
be at most `M`. -/
theorem eight_mul_card_matchableCompatible_le {αType : C → ℕ} {K : Fin n → Z} {M : ℕ}
    {comp₀ : Fin n → C} (hcomp₀ : comp₀ ∈ S.matchable αType K)
    {w : Fin n → L} (hw : w ∈ S.typicalSet K) (htyp : 0 < (S.typicalSet K).card)
    (hmod : 8 * ((S.matchable αType K).card * (S.compatibleSet comp₀).card) ≤
      M * (S.typicalSet K).card) :
    8 * (S.matchableCompatible αType K w).card ≤ M := by
  have hpair := card_matchableCompatible_mul_card_typicalSet hcomp₀ hw
  have hstep : 8 * (S.matchableCompatible αType K w).card * (S.typicalSet K).card ≤
      M * (S.typicalSet K).card := by
    calc 8 * (S.matchableCompatible αType K w).card * (S.typicalSet K).card
        = 8 * ((S.matchableCompatible αType K w).card * (S.typicalSet K).card) := by ring
      _ = 8 * ((S.matchable αType K).card * (S.compatibleSet comp₀).card) := by rw [hpair]
      _ ≤ M * (S.typicalSet K).card := hmod
  exact Nat.le_of_mul_le_mul_right hstep htyp

/-- **`claim:hole_frac_low`'s arithmetic.**  Once the modulus dominates eight times the competitor
count, the union bound over competitors gives a hole probability at most `1/8`, hence a non-hole
fraction at least `7/8`.  The union bound itself — the per-pair `1/M` conditional collision mass
of `Combinatorics/HashingConditionalIndependence.lean` — is applied by the global value theorem;
what is fixed here is the number being summed. -/
theorem holeFraction_le {V M : ℕ} (hM : 8 * V ≤ M) (hMpos : 0 < M) :
    (V : ℚ) / (M : ℚ) ≤ 1 / 8 := by
  have hMQ : (0 : ℚ) < (M : ℚ) := by exact_mod_cast hMpos
  have h8 : ((8 * V : ℕ) : ℚ) ≤ ((M : ℕ) : ℚ) := by exact_mod_cast hM
  push_cast at h8
  rw [div_le_iff₀ hMQ]
  linarith

/-- The non-hole fraction of `claim:hole_frac_low`: at least `7/8`. -/
theorem seven_eighths_le_one_sub_holeFraction {V M : ℕ} (hM : 8 * V ≤ M) (hMpos : 0 < M) :
    (7 : ℚ) / 8 ≤ 1 - (V : ℚ) / (M : ℚ) := by
  have := holeFraction_le hM hMpos
  linarith

end SplitRequirements

end AlgebraicComplexity.CompatibleSplit
