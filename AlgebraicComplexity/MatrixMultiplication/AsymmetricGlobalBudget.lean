/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.RestrictedSplittingShuffle
import AlgebraicComplexity.Analysis.CompatibilityRate
import AlgebraicComplexity.Combinatorics.MarkedTwoLegHashingExtraction

/-!
# The budget arithmetic of the Duan--Wu--Zhou global analysis

Layer 3 (`AlgebraicComplexity/MatrixMultiplication/`).  This module supplies the two *numerical*
inputs that the asymmetric global value theorem needs and that the preceding stages deliberately
left to their client:

> R. Duan, H. Wu and R. Zhou, *Faster Matrix Multiplication via Asymmetric Hashing*,
> arXiv:2210.10173v5, **§5 (`hole_lemma.tex`)** and **§6.2 (`global_value.tex`)**
> (`[DuanWuZhou2022]`).

## 1. The Hole Lemma's copy budget

`MatrixMultiplication/RestrictedSplittingShuffle.lean` proves the Hole Lemma in its
division-free finite form: broken copies repair to one intact copy as soon as

`|available| · ∏_t |holes t| < |available| ^ (number of copies)`.

`[DuanWuZhou2022]` state the hypothesis instead as `∑_t η_t ≥ Nℓ + 1`, where `η_t` is the fraction
of available small Z-blocks that survive in copy `t`.  Its module docstring records that the
passage between the two forms is the pair of *client-side* estimates

* `∏_t (1 − η_t) ≤ e^{−∑_t η_t}` (`prod_one_sub_le_exp_neg_sum`), and
* `|available| ≤ (2^{ℓ−1} + 1)^N ≤ 2^{Nℓ}` (`card_availableWord_le_two_pow_mul`),

because only a concrete component knows the alphabet size.  Both are proved here, and
`holeBudget_of_etaSum` assembles them: DWZ's hypothesis implies the finite one, with room to
spare — `2^{Nℓ} ≤ e^{Nℓ}`, so `∑ η ≥ Nℓ + 1` even leaves a factor `e^{−1}`.

`claim:hole_frac_low` supplies `η_t ≥ 7/8` uniformly, and
`holeBudget_of_eight_mul_card_le` is the resulting integer criterion: `8·(Nℓ + 1) ≤ 7·s` copies
suffice.  This is `[DuanWuZhou2022]`'s `cor:hole_lemma` count `s' = ⌊∑ η/(Nℓ+2)⌋` in the direction
a client actually uses it.

## 2. The two-branch modulus `M₀`

`[DuanWuZhou2022]`'s `claim:hole_frac_low` takes

`M₀ = 8 · max(N_triple / N_X, N_α · p_comp / N_Z)`

and the whole point of the maximum is that its two arguments are consumed by *different* layers:

| branch | consumer | statement |
| --- | --- | --- |
| `N_triple / N_X` | affine hashing | `MarkedTwoLegHashingExtraction.quarter_of_eight_mul_legFiber_le` |
| `N_α · p_comp / N_Z` | combination loss | `CompatibleSplit.SplitRequirements.eight_mul_card_matchableCompatible_le` |

Neither layer may compute the other's branch — the hashing module says so explicitly, and the
compatibility-rate module knows nothing about seeds.  `globalModulusBound` is therefore introduced
here, at the first level that sees both, and `quarter_of_globalModulusBound` /
`eight_mul_le_of_globalModulusBound` are the two projections.  Recording the *maximum* rather than
two separate hypotheses is what makes the `min` of `eq:numeric_conclusion_g` appear:
`N_α / max(a, b) = min(N_α/a, N_α/b)`, which is `AsymmetricGlobalValue.lean`'s `copyRate_eq_min`.

The constant is `8`, not `[DuanWuZhou2022]`'s displayed `4`: on this repository's exact
per-target union-bound route two legs contribute `2d` competitor proxies and the `3/4` survival
theorem needs `4·(2d) ≤ M`.  That is source-correction item 19, and it agrees with
`[DuanWuZhou2022]`'s own `M₀`.

## Non-goals

The asymptotic identification `p_comp = ᾱ_p^{n + o(n)}` is *not* proved here (see the named gap in
`Analysis/CompatibilityRate.lean`); nothing in this module needs it, because the budget
inequalities are exact finite statements about cardinalities.
-/

namespace AlgebraicComplexity

open Tensor
open scoped BigOperators

universe u v w

namespace AsymmetricGlobal

/-! ## The available-block count -/

section AvailableCount

variable {I : Type w} [Fintype I] [DecidableEq I]

/-- The available small blocks of a restricted-splitting power are among all block words, so
there are at most `|alphabet| ^ (n + 1)` of them. -/
theorem card_availableWord_le_pow (n : ℕ) (α : I → ℕ) :
    Fintype.card (AvailableWord I n α) ≤ Fintype.card I ^ (n + 1) := by
  classical
  refine (Fintype.card_subtype_le _).trans (le_of_eq ?_)
  calc Fintype.card (PositiveWord I n) = Fintype.card (Fin (n + 1) → I) :=
        Fintype.card_congr (positiveWordEquiv I n)
    _ = Fintype.card I ^ (n + 1) := by rw [Fintype.card_fun, Fintype.card_fin]

/-- `2^{ℓ−1} + 1 ≤ 2^ℓ` for `ℓ ≥ 1`: the level-`ℓ` Z-alphabet of `[DuanWuZhou2022]` has
`2^{ℓ−1} + 1` letters and therefore fits in `ℓ` bits. -/
theorem succ_two_pow_pred_le_two_pow {l : ℕ} (hl : 0 < l) : 2 ^ (l - 1) + 1 ≤ 2 ^ l := by
  obtain ⟨m, rfl⟩ : ∃ m, l = m + 1 := ⟨l - 1, by omega⟩
  have h : 1 ≤ 2 ^ m := Nat.one_le_two_pow
  have hsucc : 2 ^ (m + 1) = 2 ^ m * 2 := pow_succ 2 m
  simp only [Nat.add_sub_cancel]
  omega

/-- **`[DuanWuZhou2022]`'s block count, `hole_lemma.tex` l.130.**  With an alphabet of at most
`2^ℓ` letters there are at most `2^{ℓ(n+1)}` available small blocks on `n + 1` positions.  At the
paper's level-`ℓ` alphabet size `2^{ℓ−1} + 1` and word length `N` this is the displayed
`(2^{ℓ−1}+1)^N ≤ 2^{Nℓ}`. -/
theorem card_availableWord_le_two_pow_mul {l : ℕ} (hI : Fintype.card I ≤ 2 ^ l)
    (n : ℕ) (α : I → ℕ) :
    Fintype.card (AvailableWord I n α) ≤ 2 ^ (l * (n + 1)) := by
  refine (card_availableWord_le_pow n α).trans ?_
  calc Fintype.card I ^ (n + 1) ≤ (2 ^ l) ^ (n + 1) :=
        Nat.pow_le_pow_left hI (n + 1)
    _ = 2 ^ (l * (n + 1)) := by rw [← pow_mul]

/-- The level-`ℓ` form of the previous bound, with `[DuanWuZhou2022]`'s own alphabet size. -/
theorem card_availableWord_le_two_pow_mul_of_level {l : ℕ} (hl : 0 < l)
    (hI : Fintype.card I ≤ 2 ^ (l - 1) + 1) (n : ℕ) (α : I → ℕ) :
    Fintype.card (AvailableWord I n α) ≤ 2 ^ (l * (n + 1)) :=
  card_availableWord_le_two_pow_mul (hI.trans (succ_two_pow_pred_le_two_pow hl)) n α

/-- **Anti-vacuity.**  A split distribution with the right total mass really is realized: the
available blocks are nonempty whenever `∑ α = n + 1`.

Without this the whole Hole Lemma budget would be vacuously satisfiable, which is the failure mode
the campaign flagged for the available-block alphabet. -/
theorem card_availableWord_pos (n : ℕ) (α : I → ℕ) (hα : ∑ i, α i = n + 1) :
    0 < Fintype.card (AvailableWord I n α) := by
  classical
  have hmem : α ∈ WordType.types I (n + 1) := WordType.mem_types.mpr hα
  obtain ⟨word, hword⟩ := WordType.typeClass_nonempty α hmem
  have htype : WordType.multiplicity word = α := WordType.mem_typeClass.mp hword
  refine Fintype.card_pos_iff.mpr ⟨⟨(positiveWordEquiv I n).symm word, ?_⟩⟩
  rw [Equiv.apply_symm_apply]
  exact htype

end AvailableCount

/-! ## The exponential estimate -/

section Exponential

variable {ι : Type*} [Fintype ι]

/-- `∏_t (1 − η_t) ≤ e^{−∑_t η_t}`: the standard estimate behind `[DuanWuZhou2022]`'s passage
from the survival fractions `η_t` to a union bound. -/
theorem prod_one_sub_le_exp_neg_sum (η : ι → ℝ) (hη : ∀ t, 0 ≤ 1 - η t) :
    ∏ t, (1 - η t) ≤ Real.exp (-∑ t, η t) := by
  have hexp : Real.exp (-∑ t, η t) = ∏ t, Real.exp (-η t) := by
    rw [← Real.exp_sum]
    congr 1
    simp
  rw [hexp]
  refine Finset.prod_le_prod (fun t _ ↦ hη t) fun t _ ↦ ?_
  have h := Real.add_one_le_exp (-η t)
  linarith

end Exponential

/-! ## The Hole Lemma's copy budget -/

section Budget

variable {A : Type*} [Fintype A] {ι : Type*} [Fintype ι]

/-- **`[DuanWuZhou2022]`'s Hole Lemma hypothesis implies the finite one.**

If each broken copy destroys at most a `1 − η_t` fraction of the available blocks, the available
blocks fit in `L` bits, and `∑_t η_t ≥ L + 1`, then

`|available| · ∏_t |holes t| < |available| ^ (number of copies)`,

which is exactly the hypothesis of `Combinatorics.exists_shuffles_avoiding` and hence of
`Tensor.Restricts.indexedDirectSum_restrictedSplittingHoleRepair`.

Proof sketch: bound `∏_t |holes t| ≤ (∏_t (1 − η_t)) · |available|^s` factorwise, then
`∏ (1 − η_t) ≤ e^{−∑ η_t} ≤ e^{−(L+1)}`, and finally `|available| ≤ 2^L ≤ e^L`, so the surviving
factor is `|available| · e^{−(L+1)} ≤ e^{−1} < 1`.  The paper's threshold is therefore not tight:
it has an entire factor `e^{−1}` of slack. -/
theorem holeBudget_of_etaSum (holes : ι → Finset A) (η : ι → ℝ) (L : ℕ)
    (hpos : 0 < Fintype.card A) (hbound : Fintype.card A ≤ 2 ^ L)
    (hholes : ∀ t, ((holes t).card : ℝ) ≤ (1 - η t) * (Fintype.card A : ℝ))
    (hsum : (L : ℝ) + 1 ≤ ∑ t, η t) :
    Fintype.card A * ∏ t, (holes t).card < Fintype.card A ^ Fintype.card ι := by
  classical
  have hMpos : (0 : ℝ) < (Fintype.card A : ℝ) := by exact_mod_cast hpos
  -- Every survival fraction is at most one, because the hole counts are nonnegative.
  have hη : ∀ t, 0 ≤ 1 - η t := by
    intro t
    by_contra hcontra
    have hneg : (1 - η t) * (Fintype.card A : ℝ) < 0 :=
      mul_neg_of_neg_of_pos (not_le.mp hcontra) hMpos
    have hlt := (hholes t).trans_lt hneg
    have hnn : (0 : ℝ) ≤ ((holes t).card : ℝ) := Nat.cast_nonneg _
    linarith
  -- The product of the hole counts, factorwise.
  have hprod : (∏ t, ((holes t).card : ℝ)) ≤
      (∏ t, (1 - η t)) * (Fintype.card A : ℝ) ^ Fintype.card ι := by
    calc (∏ t, ((holes t).card : ℝ)) ≤ ∏ t, ((1 - η t) * (Fintype.card A : ℝ)) :=
          Finset.prod_le_prod (fun t _ ↦ Nat.cast_nonneg _) fun t _ ↦ hholes t
      _ = (∏ t, (1 - η t)) * (Fintype.card A : ℝ) ^ Fintype.card ι := by
          rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]
  -- The exponential estimate.
  have hexp : (∏ t, (1 - η t)) ≤ Real.exp (-((L : ℝ) + 1)) := by
    refine (prod_one_sub_le_exp_neg_sum η hη).trans ?_
    exact Real.exp_le_exp.mpr (by linarith)
  -- `|available| ≤ 2 ^ L ≤ e ^ L`.
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by
    have := Real.add_one_le_exp (1 : ℝ)
    linarith
  have hMexp : (Fintype.card A : ℝ) ≤ Real.exp (L : ℝ) := by
    have hcast : (Fintype.card A : ℝ) ≤ ((2 ^ L : ℕ) : ℝ) := by exact_mod_cast hbound
    push_cast at hcast
    refine hcast.trans ?_
    calc (2 : ℝ) ^ L ≤ Real.exp 1 ^ L := pow_le_pow_left₀ (by norm_num) htwo L
      _ = Real.exp (L : ℝ) := Real.exp_one_pow L
  -- The surviving factor is below one.
  have hsmall : (Fintype.card A : ℝ) * Real.exp (-((L : ℝ) + 1)) < 1 := by
    have hstep : (Fintype.card A : ℝ) * Real.exp (-((L : ℝ) + 1)) ≤
        Real.exp (L : ℝ) * Real.exp (-((L : ℝ) + 1)) :=
      mul_le_mul_of_nonneg_right hMexp (Real.exp_pos _).le
    have hcollapse : Real.exp (L : ℝ) * Real.exp (-((L : ℝ) + 1)) = Real.exp (-1 : ℝ) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have hlt : Real.exp (-1 : ℝ) < 1 := by
      have h := Real.exp_lt_exp.mpr (by norm_num : (-1 : ℝ) < 0)
      rwa [Real.exp_zero] at h
    rw [hcollapse] at hstep
    linarith
  -- Assemble, in the reals, then cast back.
  have hkey : (Fintype.card A : ℝ) * ∏ t, ((holes t).card : ℝ) <
      (Fintype.card A : ℝ) ^ Fintype.card ι := by
    have hpow : (0 : ℝ) < (Fintype.card A : ℝ) ^ Fintype.card ι := pow_pos hMpos _
    calc (Fintype.card A : ℝ) * ∏ t, ((holes t).card : ℝ)
        ≤ (Fintype.card A : ℝ) *
            ((∏ t, (1 - η t)) * (Fintype.card A : ℝ) ^ Fintype.card ι) :=
          mul_le_mul_of_nonneg_left hprod hMpos.le
      _ ≤ (Fintype.card A : ℝ) *
            (Real.exp (-((L : ℝ) + 1)) * (Fintype.card A : ℝ) ^ Fintype.card ι) := by
          refine mul_le_mul_of_nonneg_left ?_ hMpos.le
          exact mul_le_mul_of_nonneg_right hexp hpow.le
      _ = ((Fintype.card A : ℝ) * Real.exp (-((L : ℝ) + 1))) *
            (Fintype.card A : ℝ) ^ Fintype.card ι := by ring
      _ < 1 * (Fintype.card A : ℝ) ^ Fintype.card ι :=
          mul_lt_mul_of_pos_right hsmall hpow
      _ = (Fintype.card A : ℝ) ^ Fintype.card ι := one_mul _
  have hcast : ((Fintype.card A * ∏ t, (holes t).card : ℕ) : ℝ) <
      ((Fintype.card A ^ Fintype.card ι : ℕ) : ℝ) := by
    push_cast
    exact hkey
  exact_mod_cast hcast

/-- **The `7/8` form of the copy budget** (`[DuanWuZhou2022]`, `claim:hole_frac_low` and
`cor:hole_lemma`).

`claim:hole_frac_low` bounds the hole fraction of every broken copy by `1/8`, i.e. `η_t ≥ 7/8`
uniformly.  With `s` copies the paper's threshold `∑ η_t ≥ L + 1` then reads `8(L+1) ≤ 7s`, and
that is the only arithmetic a client has to check.

The hypothesis on the holes is stated in the exact integer form `8 · |holes t| ≤ |available|`
delivered by `Analysis/CompatibilityRate.seven_eighths_le_one_sub_holeFraction`. -/
theorem holeBudget_of_eight_mul_card_le (holes : ι → Finset A) (L : ℕ)
    (hpos : 0 < Fintype.card A) (hbound : Fintype.card A ≤ 2 ^ L)
    (hholes : ∀ t, 8 * (holes t).card ≤ Fintype.card A)
    (hcopies : 8 * (L + 1) ≤ 7 * Fintype.card ι) :
    Fintype.card A * ∏ t, (holes t).card < Fintype.card A ^ Fintype.card ι := by
  refine holeBudget_of_etaSum holes (fun _ ↦ (7 : ℝ) / 8) L hpos hbound ?_ ?_
  · intro t
    have h : (8 : ℝ) * ((holes t).card : ℝ) ≤ (Fintype.card A : ℝ) := by
      exact_mod_cast hholes t
    have : (1 : ℝ) - 7 / 8 = 1 / 8 := by norm_num
    rw [this]
    linarith
  · have hcard : (8 : ℝ) * ((L : ℝ) + 1) ≤ 7 * (Fintype.card ι : ℝ) := by
      have : ((8 * (L + 1) : ℕ) : ℝ) ≤ ((7 * Fintype.card ι : ℕ) : ℝ) := by
        exact_mod_cast hcopies
      push_cast at this
      linarith
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    linarith

end Budget

/-! ## The assembled Hole Lemma for restricted-splitting powers -/

section Repair

variable {K : Type u} [CommSemiring K]
variable {A : Leg → Type w}
variable [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]
variable {V : ∀ c, A c → Type (max u v)}
variable [∀ c a, AddCommMonoid (V c a)] [∀ c a, Module K (V c a)]

open Tensor

/-- **`[DuanWuZhou2022]`'s Hole Lemma, in the form its own §6 uses.**

`s` copies of the restricted-splitting power `T^{⊗(n+1)}[α̃]`, each missing at most an eighth of
the available small Z-blocks, degenerate onto one intact copy as soon as `8(ℓ(n+1) + 1) ≤ 7s`,
provided the Z-alphabet has at most `2^ℓ` letters.

This is the composition of `holeBudget_of_eight_mul_card_le` with the committed repair theorem
`Tensor.Restricts.indexedDirectSum_restrictedSplittingHoleRepair`; the two numeric facts the
latter's docstring defers to its client are supplied above. -/
theorem restrictedSplittingHoleRepair_of_eight_mul_card_le
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (P : PartitionedTensor (K := K) (A := A) V) (n : ℕ) (α : A Leg.Z → ℕ)
    (holes : ι → Finset (AvailableWord (A Leg.Z) n α))
    (l : ℕ) (hl : Fintype.card (A Leg.Z) ≤ 2 ^ l)
    (hpos : 0 < Fintype.card (AvailableWord (A Leg.Z) n α))
    (hholes : ∀ t, 8 * (holes t).card ≤ Fintype.card (AvailableWord (A Leg.Z) n α))
    (hcopies : 8 * (l * (n + 1) + 1) ≤ 7 * Fintype.card ι) :
    Restricts
      (Tensor.indexedDirectSum
        (V := fun _ : ι ↦ PartitionedSpace K (PositivePowerBlockSpace K V n))
        fun t ↦ ((P.restrictedSplittingPower n (SplitRestriction.ofLeg Leg.Z α)).holeSelect
          Leg.Z fun word ↦ word ∈ (holes t).image Subtype.val).realize)
      (P.restrictedSplittingPower n (SplitRestriction.ofLeg Leg.Z α)).realize :=
  Tensor.Restricts.indexedDirectSum_restrictedSplittingHoleRepair P n α holes
    (holeBudget_of_eight_mul_card_le holes (l * (n + 1)) hpos
      (card_availableWord_le_two_pow_mul hl n α) hholes hcopies)

end Repair

/-! ## The two-branch modulus `M₀` -/

section Modulus

/-- **`[DuanWuZhou2022]`'s modulus `M₀ = 8 · max(N_triple/N_X, N_α·p_comp/N_Z)`**, in exact
integer form: `hashBranch` is a bound on the ambient X- and Y-leg fibers of a marked triple
(the paper's `N_triple / N_X`) and `combinationBranch` is the number of retained large triples
compatible with a fixed typical small Z-block (the paper's `N_α · p_comp / N_Z`, which
`Analysis/CompatibilityRate.card_matchableCompatible_eq_mul_compatibleFraction` computes exactly).

Keeping the maximum as one number rather than two hypotheses is deliberate: it is what makes the
`min` of `eq:numeric_conclusion_g` a theorem instead of a definition. -/
def globalModulusBound (hashBranch combinationBranch : ℕ) : ℕ :=
  8 * max hashBranch combinationBranch

@[simp] theorem globalModulusBound_eq (hashBranch combinationBranch : ℕ) :
    globalModulusBound hashBranch combinationBranch = 8 * max hashBranch combinationBranch := rfl

theorem eight_mul_hashBranch_le_globalModulusBound (hashBranch combinationBranch : ℕ) :
    8 * hashBranch ≤ globalModulusBound hashBranch combinationBranch := by
  simp only [globalModulusBound]
  exact Nat.mul_le_mul_left 8 (le_max_left _ _)

theorem eight_mul_combinationBranch_le_globalModulusBound (hashBranch combinationBranch : ℕ) :
    8 * combinationBranch ≤ globalModulusBound hashBranch combinationBranch := by
  simp only [globalModulusBound]
  exact Nat.mul_le_mul_left 8 (le_max_right _ _)

variable {R : Type u} [Field R] [Fintype R]
variable {ι : Type v} [Fintype ι] {target : R}

open ProgressionHash ProgressionHash.LegalTriple

/-- **First branch.**  A modulus dominating `M₀` discharges the union-bound hypothesis of the
marked two-leg (asymmetric) hashing theorem of `Combinatorics/MarkedTwoLegHashingExtraction.lean`.

This is `quarter_of_eight_mul_legFiber_le` with `d := hashBranch`; the second branch of the maximum
is simply discarded, which is the precise sense in which the hashing layer "never computes a
modulus". -/
theorem quarter_of_globalModulusBound
    (ambient marked : Finset (LegalTriple R ι target))
    (hashBranch combinationBranch : ℕ)
    (hX : ∀ triple ∈ marked, (legFiber ambient triple .X).card ≤ hashBranch)
    (hY : ∀ triple ∈ marked, (legFiber ambient triple .Y).card ≤ hashBranch)
    (hmodulus : globalModulusBound hashBranch combinationBranch ≤ Fintype.card R) :
    ∀ triple ∈ marked,
      4 * (xyCompetitorYIndices ambient triple).card ≤ Fintype.card R :=
  quarter_of_eight_mul_legFiber_le ambient marked hashBranch hX hY
    ((eight_mul_hashBranch_le_globalModulusBound hashBranch combinationBranch).trans hmodulus)

/-- **Second branch.**  The same modulus dominates eight times the combination-loss competitor
count, which is `claim:hole_frac_low`'s hypothesis and hence, through
`Analysis/CompatibilityRate.holeFraction_le`, the `1/8` hole fraction consumed by
`holeBudget_of_eight_mul_card_le`. -/
theorem eight_mul_le_of_globalModulusBound
    (hashBranch combinationBranch M : ℕ)
    (hmodulus : globalModulusBound hashBranch combinationBranch ≤ M) :
    8 * combinationBranch ≤ M :=
  (eight_mul_combinationBranch_le_globalModulusBound hashBranch combinationBranch).trans hmodulus

/-- **Both branches at once**, in the shape the global value theorem instantiates: one modulus
hypothesis, two consequences drawn in two different layers. -/
theorem globalModulusBound_branches
    (ambient marked : Finset (LegalTriple R ι target))
    (hashBranch combinationBranch : ℕ)
    (hX : ∀ triple ∈ marked, (legFiber ambient triple .X).card ≤ hashBranch)
    (hY : ∀ triple ∈ marked, (legFiber ambient triple .Y).card ≤ hashBranch)
    (hmodulus : globalModulusBound hashBranch combinationBranch ≤ Fintype.card R) :
    (∀ triple ∈ marked,
        4 * (xyCompetitorYIndices ambient triple).card ≤ Fintype.card R) ∧
      8 * combinationBranch ≤ Fintype.card R :=
  ⟨quarter_of_globalModulusBound ambient marked hashBranch combinationBranch hX hY hmodulus,
    eight_mul_le_of_globalModulusBound hashBranch combinationBranch _ hmodulus⟩

end Modulus

/-! ## The combination-loss branch, in `[DuanWuZhou2022]`'s own quantities

The second branch of `M₀` is stated above as an abstract count.  The theorem below identifies it
with the paper's `N_α · p_comp / N_Z` by routing through
`Analysis/CompatibilityRate.eight_mul_card_matchableCompatible_le`, so that a client may supply
either form. -/

section CombinationBranch

open CompatibleSplit

variable {C : Type u} {L : Type v} {Z : Type w}
variable [Fintype C] [DecidableEq C] [Fintype L] [DecidableEq L] [Fintype Z] [DecidableEq Z]
variable {S : SplitRequirements C L Z} {n : ℕ}

/-- The combination-loss branch of `M₀`, spelled with `[DuanWuZhou2022]`'s quantities: if the
modulus dominates `8 · N_α · p_comp / N_Z` in the exact division-free form, then it dominates eight
times the competitor count of `claim:hole_frac_low`, and the hole fraction of the fixed typical
block is at most `1/8`. -/
theorem holeFraction_le_of_modulus {αType : C → ℕ} {K : Fin n → Z} {M : ℕ}
    {comp₀ : Fin n → C} (hcomp₀ : comp₀ ∈ S.matchable αType K)
    {w : Fin n → L} (hw : w ∈ S.typicalSet K) (htyp : 0 < (S.typicalSet K).card)
    (hMpos : 0 < M)
    (hmod : 8 * ((S.matchable αType K).card * (S.compatibleSet comp₀).card) ≤
      M * (S.typicalSet K).card) :
    (((S.matchableCompatible αType K w).card : ℚ)) / (M : ℚ) ≤ 1 / 8 :=
  SplitRequirements.holeFraction_le
    (SplitRequirements.eight_mul_card_matchableCompatible_le hcomp₀ hw htyp hmod) hMpos

end CombinationBranch

end AsymmetricGlobal

end AlgebraicComplexity
