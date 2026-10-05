/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Tensor.AsymptoticIndependenceNumber
import AlgebraicComplexity.Tensor.AsymptoticInvariant
import AlgebraicComplexity.Tensor.AsymptoticRank
import AlgebraicComplexity.Tensor.SliceRank

/-!
# Asymptotic slice rank

The **asymptotic slice rank** of a three-legged tensor is

```text
S̃(T) := limsup_n S(T^{⊗n})^{1/n},
```

the exponential growth rate of the slice ranks of the canonical tensor powers.  It is the
invariant behind the strongest known barrier against the *universal method* for matrix
multiplication:

> J. Alman, *Limits on the Universal Method for Matrix Multiplication*, Ph.D. thesis (MIT, 2019),
> Chapter 5, and *Limits on the Universal Method for Matrix Multiplication*, CCC 2019.

## Definitions

* `sliceRankPowerSequence T n = S(T^{⊗n})`, the slice-rank sequence of the canonical powers,
  in the style of `rankPowerSequence` of `Tensor/AsymptoticRank.lean`.
* `asymptoticSliceRank T = Growth.exponentialRate (sliceRankPowerSequence T)`.

## Why this is a `limsup` and not a Fekete limit

`Tensor/AsymptoticInvariant.lean` builds asymptotic rank and asymptotic subrank through Fekete's
lemma: rank is submultiplicative under external products and subrank is supermultiplicative, so in
both cases `μ(T^{⊗n})^{1/n}` converges and the limit is an infimum resp. a supremum of the roots.
**Slice rank is neither.**  The thesis records the failure explicitly (§5.1): `S(CW_5) = 3`, yet
`S(CW_5^{⊗n}) ≥ 5.15^{n-o(n)}`, so `S(A ⊗ B) > S(A) · S(B)` happens.  Consequently
`Growth.submultiplicativeLimit` must *not* be used here, and no theorem of this file may assume
convergence of the roots.

`Growth.exponentialRate a = inf {ρ ≥ 0 | ∃ C > 0, ∀ n, a n ≤ C · ρ^n}` is exactly the `limsup` of
the roots `a n ^ (1/n)` for a sequence with at least one exponential bound, and it is the only
form used below: upper bounds are produced by exhibiting an exponential bound
(`asymptoticSliceRank_le_of_pow`), lower bounds by exhibiting a geometric lower bound
(`le_asymptoticSliceRank_of_pow_le`).  Every slice-rank sequence does have an exponential bound,
since `S(T^{⊗n}) ≤ max_c S_c(T)^n` (`sliceRankPowerSequence_exponentialBound`), so the infimum is
over a nonempty set.

## Main results

* `sliceRank_power_le_maxSliceRankAlong_pow` and `asymptoticSliceRank_le_maxSliceRankAlong`:
  `S(T^{⊗n}) ≤ (max_c S_c T)^n`, hence `S̃(T) ≤ max_c S_c(T)`.  This is the upper half of thesis
  Corollary 5.1 and the reason the single-leg slice ranks of `Tensor/SliceRank.lean` are needed.
* `asymptoticSliceRank_le_asymptoticRank`: `S̃(T) ≤ R̃(T)`.
* `asymptoticSliceRank_power_le_pow`: `S̃(T^{⊗n}) ≤ S̃(T)^n`, the half of the power law that a
  `limsup` gives for free (passing to the subsequence of multiples of `n`).  The reverse
  inequality is *not* available: it is the failure of submultiplicativity discussed above.
* `asymptoticSliceRank_restricts_le` and `asymptoticSliceRank_isomorphic`: monotonicity under
  exact restriction and invariance under legwise isomorphism.
* `sliceRank_power_diagonalTensor` and `asymptoticSliceRank_diagonalTensor` (thesis Proposition
  5.2): `S(⟨q⟩^{⊗n}) = q^n`, hence `S̃(⟨q⟩) = S(⟨q⟩) = q`.
* `asymptoticSubrank_le_asymptoticSliceRank`: `Q̃(T) ≤ S̃(T)`, completing the comparison chain
  `Q̃ ≤ S̃ ≤ R̃` that `Tensor/AsymptoticInvariant.lean` lists as a non-goal.
* `asymptoticIndependenceNumber_le_asymptoticSliceRank`: `Ī(T) ≤ S̃(coordinateTensor T)`, the
  coordinate-level form used by the Alman--Vassilevska Williams barrier framework.

## Non-goals

Monotonicity of slice rank under polynomial degeneration (thesis Proposition 5.1, i.e.
[TaoSawin2016, Corollary 2]) is deliberately *not* proved here; it needs the Zariski-closedness of
the "slice rank at most `r`" locus rather than a certificate manipulation, and is the subject of a
separate module.  Once available it upgrades `asymptoticSliceRank_restricts_le` to degeneration
monotonicity.

## References

* J. Alman, *Limits on the Universal Method for Matrix Multiplication*, Ph.D. thesis, MIT, 2019,
  §5.1--5.2 (Lemma 5.1, Propositions 5.1 and 5.2, Corollary 5.1).
* T. Tao and W. Sawin, *Notes on the "slice rank" of tensors*, blog post, 2016.
-/

namespace AlgebraicComplexity.Tensor

open Growth

universe u v w

section Definition

variable {K : Type u} [CommSemiring K]
variable {V : Leg → Type v} [∀ c, AddCommMonoid (V c)] [∀ c, Module K (V c)]
variable {W : Leg → Type w} [∀ c, AddCommMonoid (W c)] [∀ c, Module K (W c)]

/-- The slice-rank sequence of the canonical tensor powers of `T`. -/
noncomputable def sliceRankPowerSequence (T : Tensor3 K V) (n : ℕ) : ℕ :=
  sliceRank (power T n)

/-- **Asymptotic slice rank** `S̃(T)`: the exponential growth rate of the slice ranks of the
canonical tensor powers, that is `limsup_n S(T^{⊗n})^{1/n}`.

Slice rank is not submultiplicative under tensor products, so --- unlike `asymptoticRank` and
`asymptoticSubrank` --- this is genuinely a `limsup` and Fekete's lemma does not apply; see the
module documentation. -/
noncomputable def asymptoticSliceRank (T : Tensor3 K V) : ℝ :=
  Growth.exponentialRate (sliceRankPowerSequence T)

/-- The largest single-leg slice rank of a tensor power is bounded by the corresponding power of
the largest single-leg slice rank.

Proof sketch: induction on the exponent.  `max_c S_c` is submultiplicative under external products
(`maxSliceRankAlong_external_le`) and invariant under legwise isomorphism, and
`isomorphic_external_power` splits `T^{⊗(n+1)}` as `T^{⊗n} ⊠ T^{⊗1}`.  The base case uses
`rank (T^{⊗0}) ≤ 1`. -/
theorem maxSliceRankAlong_power_le (T : Tensor3 K V) (n : ℕ) :
    maxSliceRankAlong (power T n) ≤ maxSliceRankAlong T ^ n := by
  induction n with
  | zero =>
      have h := (maxSliceRankAlong_le_rank (power T 0)).trans (rank_power_le T 0)
      simpa using h
  | succ n ih =>
      have hone : maxSliceRankAlong (power T 1) = maxSliceRankAlong T := by
        refine maxSliceRankAlong_isomorphic ?_
        rw [power_one_eq_powerOne]
        exact (Isomorphic.powerOneTransport T).symm
      calc maxSliceRankAlong (power T (n + 1))
          = maxSliceRankAlong (Tensor.external (power T n) (power T 1)) :=
            (maxSliceRankAlong_isomorphic (isomorphic_external_power T n 1)).symm
        _ ≤ maxSliceRankAlong (power T n) * maxSliceRankAlong (power T 1) :=
            maxSliceRankAlong_external_le _ _
        _ ≤ maxSliceRankAlong T ^ n * maxSliceRankAlong T := by
            rw [hone]
            exact Nat.mul_le_mul_right _ ih
        _ = maxSliceRankAlong T ^ (n + 1) := (pow_succ _ _).symm

/-- **The geometric bound for the slice ranks of tensor powers**: `S(T^{⊗n}) ≤ (max_c S_c T)^n`.
This is the upper half of thesis Corollary 5.1, and the reason a slice-rank sequence always admits
an exponential bound even though slice rank itself is not submultiplicative. -/
theorem sliceRank_power_le_maxSliceRankAlong_pow (T : Tensor3 K V) (n : ℕ) :
    sliceRank (power T n) ≤ maxSliceRankAlong T ^ n :=
  (sliceRank_le_maxSliceRankAlong _).trans (maxSliceRankAlong_power_le T n)

/-- The slice-rank sequence of the tensor powers of `T` admits the exponential bound
`max_c S_c(T)`. -/
theorem sliceRankPowerSequence_exponentialBound (T : Tensor3 K V) :
    ExponentialBound (sliceRankPowerSequence T) (maxSliceRankAlong T : ℝ) :=
  ExponentialBound.of_le_pow _ _ (sliceRank_power_le_maxSliceRankAlong_pow T)

/-- The slice-rank sequence of the tensor powers of `T` has at least one exponential bound, so the
infimum defining `asymptoticSliceRank` is taken over a nonempty set. -/
theorem exists_exponentialBound_sliceRankPowerSequence (T : Tensor3 K V) :
    ∃ ρ, ExponentialBound (sliceRankPowerSequence T) ρ :=
  ⟨_, sliceRankPowerSequence_exponentialBound T⟩

theorem asymptoticSliceRank_nonneg (T : Tensor3 K V) : 0 ≤ asymptoticSliceRank T :=
  exponentialRate_nonneg _

/-- Any exponential bound on the slice ranks of tensor powers bounds asymptotic slice rank. -/
theorem asymptoticSliceRank_le {T : Tensor3 K V} {ρ : ℝ}
    (h : ExponentialBound (sliceRankPowerSequence T) ρ) : asymptoticSliceRank T ≤ ρ :=
  exponentialRate_le h

/-- A geometric upper bound `S(T^{⊗n}) ≤ r^n` bounds asymptotic slice rank by `r`. -/
theorem asymptoticSliceRank_le_of_pow {T : Tensor3 K V} {r : ℕ}
    (h : ∀ n, sliceRank (power T n) ≤ r ^ n) : asymptoticSliceRank T ≤ (r : ℝ) :=
  asymptoticSliceRank_le (ExponentialBound.of_le_pow _ _ h)

/-- A geometric lower bound `b^n ≤ S(T^{⊗n})` bounds asymptotic slice rank from below. -/
theorem le_asymptoticSliceRank_of_pow_le {T : Tensor3 K V} {b : ℝ}
    (h : ∀ n, b ^ n ≤ sliceRankPowerSequence T n) : b ≤ asymptoticSliceRank T :=
  le_exponentialRate_of_pow_le (exists_exponentialBound_sliceRankPowerSequence T) h

/-- **`S̃(T) ≤ max_c S_c(T)`** (thesis Corollary 5.1, upper half). -/
theorem asymptoticSliceRank_le_maxSliceRankAlong (T : Tensor3 K V) :
    asymptoticSliceRank T ≤ (maxSliceRankAlong T : ℝ) :=
  asymptoticSliceRank_le (sliceRankPowerSequence_exponentialBound T)

/-- At every power, slice rank is bounded by ordinary rank. -/
theorem sliceRankPowerSequence_le_rankPowerSequence (T : Tensor3 K V) (n : ℕ) :
    sliceRankPowerSequence T n ≤ rankPowerSequence T n :=
  sliceRank_le_rank (power T n)

/-- **`S̃(T) ≤ R̃(T)`**: asymptotic slice rank never exceeds asymptotic rank. -/
theorem asymptoticSliceRank_le_asymptoticRank (T : Tensor3 K V) :
    asymptoticSliceRank T ≤ asymptoticRank T :=
  exponentialRate_mono (sliceRankPowerSequence_le_rankPowerSequence T)
    ⟨_, rank_exponentialBound T⟩

/-- Asymptotic slice rank never exceeds ordinary tensor rank. -/
theorem asymptoticSliceRank_le_rank (T : Tensor3 K V) : asymptoticSliceRank T ≤ (rank T : ℝ) :=
  (asymptoticSliceRank_le_asymptoticRank T).trans (asymptoticRank_le_rank T)

/-- Exact restriction decreases the slice rank of every tensor power. -/
theorem sliceRankPowerSequence_restricts_le {T : Tensor3 K V} {S : Tensor3 K W}
    (h : Restricts T S) (n : ℕ) : sliceRankPowerSequence S n ≤ sliceRankPowerSequence T n :=
  sliceRank_restricts_le (h.power n)

/-- **Asymptotic slice rank is monotone under exact restriction**: the source `T` of the
restriction has the larger asymptotic slice rank. -/
theorem asymptoticSliceRank_restricts_le {T : Tensor3 K V} {S : Tensor3 K W}
    (h : Restricts T S) : asymptoticSliceRank S ≤ asymptoticSliceRank T :=
  exponentialRate_mono (sliceRankPowerSequence_restricts_le h)
    (exists_exponentialBound_sliceRankPowerSequence T)

/-- Legwise isomorphic tensors have equal asymptotic slice rank. -/
theorem asymptoticSliceRank_isomorphic {T : Tensor3 K V} {S : Tensor3 K W}
    (h : Isomorphic T S) : asymptoticSliceRank T = asymptoticSliceRank S :=
  le_antisymm (asymptoticSliceRank_restricts_le h.symm.restricts)
    (asymptoticSliceRank_restricts_le h.restricts)

end Definition

/-! ## The diagonal tensor

`⟨q⟩ = ∑_{i<q} e_i ⊗ e_i ⊗ e_i` has slice rank `q` (Tao's lemma, `sliceRank_diagonalTensor`) and
asymptotic slice rank `q` as well: the powers of `⟨q⟩` restrict onto `⟨q^n⟩`, which forces
`S(⟨q⟩^{⊗n}) ≥ q^n`, while `R(⟨q⟩^{⊗n}) ≤ q^n` bounds it from above. -/

section Diagonal

variable {K : Type u} [Field K]

/-- **The slice rank of every power of a diagonal tensor**: `S(⟨q⟩^{⊗n}) = q^n`.  This is the
power law behind thesis Proposition 5.2 and the only place where slice rank of a tensor power is
computed exactly.

Proof sketch: the upper bound is `S(⟨q⟩^{⊗n}) ≤ R(⟨q⟩^{⊗n}) ≤ R(⟨q⟩)^n = q^n`, using
`rank_diagonalTensor`.  For the lower bound, `⟨q⟩^{⊗n}` restricts onto `⟨q^n⟩`
(`Restricts.power_diagonalTensor`, after reindexing `ι` by `Fin q`), so Tao's diagonal bound
`card_le_sliceRank_of_restricts_diagonalTensor` gives `q^n ≤ S(⟨q⟩^{⊗n})`. -/
theorem sliceRank_power_diagonalTensor (ι : Type w) [Fintype ι] [DecidableEq ι] (n : ℕ) :
    sliceRank (power (diagonalTensor K ι) n) = Fintype.card ι ^ n := by
  classical
  refine le_antisymm ?_ ?_
  · calc sliceRank (power (diagonalTensor K ι) n)
        ≤ rank (power (diagonalTensor K ι) n) := sliceRank_le_rank _
      _ ≤ rank (diagonalTensor K ι) ^ n := rank_power_le _ n
      _ = Fintype.card ι ^ n := by rw [rank_diagonalTensor]
  · have hfin : Restricts (diagonalTensor K ι) (diagonalTensor K (Fin (Fintype.card ι))) :=
      (Isomorphic.diagonalTensor_congr (K := K) (Fintype.equivFin ι)).restricts
    simpa using card_le_sliceRank_of_restricts_diagonalTensor
      (ι := Fin (Fintype.card ι ^ n)) (hfin.power_diagonalTensor n)

/-- **Thesis Proposition 5.2** ([Tao16, Lemma 1]): the diagonal tensor on a finite index type has
asymptotic slice rank equal to its size, `S̃(⟨q⟩) = S(⟨q⟩) = q`.

Proof sketch: the slice ranks of the powers are exactly `q^n`
(`sliceRank_power_diagonalTensor`), which is both an exponential upper bound with base `q` and a
geometric lower bound with base `q`. -/
theorem asymptoticSliceRank_diagonalTensor (ι : Type w) [Fintype ι] [DecidableEq ι] :
    asymptoticSliceRank (diagonalTensor K ι) = (Fintype.card ι : ℝ) := by
  refine le_antisymm ?_ ?_
  · exact asymptoticSliceRank_le_of_pow (r := Fintype.card ι) fun n ↦
      (sliceRank_power_diagonalTensor ι n).le
  · refine le_asymptoticSliceRank_of_pow_le fun n ↦ le_of_eq ?_
    rw [sliceRankPowerSequence, sliceRank_power_diagonalTensor, Nat.cast_pow]

end Diagonal

/-! ## Comparison with the asymptotic subrank

`Q̃ ≤ S̃ ≤ R̃` is the barrier chain of the Alman--Vassilevska Williams framework.  The left
inequality is not a pointwise comparison of the two definitions --- `Q̃` is a supremum of roots and
`S̃` an infimum of admissible exponential bases --- so it is proved by showing that *every*
admissible base for the slice-rank sequence already dominates every single subrank root, which uses
supermultiplicativity of the subrank along tensor powers. -/

section SubrankComparison

variable {K : Type u} [Field K]
variable {V : Leg → Type (max u v)} [∀ c, AddCommMonoid (V c)] [∀ c, Module K (V c)]

/-- **Supermultiplicativity of the subrank along tensor powers**:
`Q(T^{⊗n})^k ≤ Q(T^{⊗(k·n)})`.

Proof sketch: `T^{⊗n}` restricts onto the diagonal tensor of size `Q(T^{⊗n})`, so its `k`th power
restricts onto the diagonal of size `Q(T^{⊗n})^k`; the `k`th power of `T^{⊗n}` is legwise
isomorphic to `T^{⊗(k·n)}`. -/
theorem subrank_power_pow_le (T : Tensor3 K V) (n k : ℕ) :
    subrank (power T n) ^ k ≤ subrank (power T (k * n)) := by
  have hrestr : Restricts (power T (k * n))
      (diagonalTensor K (Fin (subrank (power T n) ^ k))) :=
    (Isomorphic.power_power T n k).symm.restricts.trans
      ((restricts_diagonalTensor_subrank (power T n)).power_diagonalTensor k)
  exact le_subrank_of_restricts hrestr

/-- Every admissible exponential base for the slice-rank sequence of the tensor powers of `T`
already dominates each individual subrank of a power: `Q(T^{⊗n}) ≤ ρ^n`.

Proof sketch: restrict the exponential bound to the multiples of `n`, which turns it into an
exponential bound with base `ρ^n` for `k ↦ S(T^{⊗(k·n)})`; supermultiplicativity of the subrank
(`subrank_power_pow_le`) together with `Q ≤ S` supplies the geometric lower bound
`Q(T^{⊗n})^k ≤ S(T^{⊗(k·n)})`, and `Growth.ExponentialBound.base_le_of_pow_le` concludes. -/
theorem subrank_power_le_pow_of_exponentialBound {T : Tensor3 K V} {ρ : ℝ}
    (hρ : ExponentialBound (sliceRankPowerSequence T) ρ) (n : ℕ) :
    ((subrank (power T n) : ℕ) : ℝ) ≤ ρ ^ n := by
  obtain ⟨hρ0, C, hC, hbound⟩ := hρ
  have hsub : ExponentialBound (fun k ↦ sliceRankPowerSequence T (k * n)) (ρ ^ n) := by
    refine ⟨pow_nonneg hρ0 n, C, hC, fun k ↦ ?_⟩
    have h := hbound (k * n)
    rwa [pow_mul'] at h
  refine ExponentialBound.base_le_of_pow_le hsub fun k ↦ ?_
  have h : subrank (power T n) ^ k ≤ sliceRankPowerSequence T (k * n) :=
    (subrank_power_pow_le T n k).trans (subrank_le_sliceRank _)
  exact_mod_cast h

/-- **`Q̃(T) ≤ S̃(T)`**: the asymptotic subrank never exceeds the asymptotic slice rank.  Together
with `asymptoticSliceRank_le_asymptoticRank` this is the barrier chain `Q̃ ≤ S̃ ≤ R̃`.

Proof sketch: `S̃(T)` is an infimum over the admissible exponential bases `ρ` of the slice-rank
sequence, so it suffices to bound `Q̃(T)` by each such `ρ`.  `Q̃(T)` is the supremum of the roots
`Q(T^{⊗n})^{1/n}`, and `subrank_power_le_pow_of_exponentialBound` gives `Q(T^{⊗n}) ≤ ρ^n`, whose
`n`th root is `ρ`. -/
theorem asymptoticSubrank_le_asymptoticSliceRank (T : Tensor3 K V) :
    asymptoticSubrank T ≤ asymptoticSliceRank T := by
  rw [asymptoticSliceRank, Growth.exponentialRate]
  refine le_csInf ⟨_, sliceRankPowerSequence_exponentialBound T⟩ fun ρ hρ ↦ ?_
  have hρ' : ExponentialBound (sliceRankPowerSequence T) ρ := hρ
  refine asymptoticSuperInvariant_le (subrankInvariant.{u, v} K) T fun n hn ↦ ?_
  calc ((subrank (power T n) : ℕ) : ℝ) ^ ((n : ℝ)⁻¹)
      ≤ (ρ ^ n) ^ ((n : ℝ)⁻¹) := by
        refine Real.rpow_le_rpow (by positivity) ?_ (by positivity)
        exact subrank_power_le_pow_of_exponentialBound hρ' n
    _ = ρ := Real.pow_rpow_inv_natCast hρ'.1 (by omega)

end SubrankComparison

/-! ## Comparison with the asymptotic independence number

The independence number of a coefficient table is a basis-dependent lower bound for the subrank of
the tensor it defines, so the previous section transports to `Ī`. -/

section IndependenceComparison

variable {K : Type u} [Field K] {κ : Leg → Type v}
variable [∀ i, Fintype (κ i)] [∀ i, DecidableEq (κ i)]

/-- **`Ī(T) ≤ S̃(coordinateTensor T)`**: the asymptotic independence number of a coefficient table
never exceeds the asymptotic slice rank of the tensor it defines.

Proof sketch: through `asymptoticIndependenceNumber_eq_exponentialRate` both sides are
constant-tolerant exponential rates of natural sequences, so the pointwise comparison
`I(T^{⊗n}) ≤ Q((coordinateTensor T)^{⊗n}) ≤ S((coordinateTensor T)^{⊗n})` suffices; the
exponential bound required of the dominating sequence is
`sliceRankPowerSequence_exponentialBound`. -/
theorem asymptoticIndependenceNumber_le_asymptoticSliceRank (T : (∀ i, κ i) → K) :
    asymptoticIndependenceNumber T ≤ asymptoticSliceRank (coordinateTensor T) := by
  rw [asymptoticIndependenceNumber_eq_exponentialRate, asymptoticSliceRank]
  refine exponentialRate_mono (fun n ↦ ?_)
    (exists_exponentialBound_sliceRankPowerSequence (coordinateTensor T))
  exact (independenceNumber_coordinatePower_le_subrank T n).trans (subrank_le_sliceRank _)

end IndependenceComparison

/-! ## The power law

`S̃(T^{⊗n}) ≤ S̃(T)^n` is the half of `S̃(T^{⊗n}) = S̃(T)^n` that holds for a `limsup` with no
input at all: the slice ranks of the powers of `T^{⊗n}` form the subsequence of the multiples of
`n` of the slice ranks of the powers of `T`, and a `limsup` along a subsequence is no larger.  The
reverse inequality would say that `S` is supermultiplicative along powers, which is exactly what
fails for slice rank (§5.1 of the thesis: `S(CW_5) = 3` but `S(CW_5^{⊗n}) ≥ 5.15^{n-o(n)}` --- that
example makes `S̃` *larger* than `S`, and is not a counterexample to the direction proved here). -/

section PowerLaw

variable {K : Type u} [CommSemiring K]
variable {V : Leg → Type v} [∀ c, AddCommMonoid (V c)] [∀ c, Module K (V c)]

/-- **`S̃(T^{⊗n}) ≤ S̃(T)^n`.**  This is the submultiplicativity input of the barrier Theorem 5.1 of
[Alman2019] (its `S̃(T^{⊗n}) ≤ S̃(T)^n` step), and the only half of the power law available.

Proof sketch: for `n = 0` the tensor `T^{⊗0}` has rank at most one, so all of *its* powers have
slice rank at most one.  For `n ≥ 1`, suppose `S̃(T)^n < S̃(T^{⊗n}) =: b` and put
`ρ₀ = b^{1/n} > S̃(T)`.  Since `S̃(T)` is the infimum of the admissible exponential bases of
`k ↦ S(T^{⊗k})`, some admissible base `ρ` satisfies `ρ < ρ₀`.  Reading its bound at the multiples
of `n` and identifying `(T^{⊗n})^{⊗k}` with `T^{⊗(k·n)}` (`Isomorphic.power_power`) makes `ρ^n` an
admissible base for the powers of `T^{⊗n}`, so `b ≤ ρ^n < ρ₀^n = b`, a contradiction. -/
theorem asymptoticSliceRank_power_le_pow (T : Tensor3 K V) (n : ℕ) :
    asymptoticSliceRank (power T n) ≤ asymptoticSliceRank T ^ n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have hrank : rank (power T 0) ≤ 1 := by simpa using rank_power_le T 0
    have h : asymptoticSliceRank (power T 0) ≤ ((1 : ℕ) : ℝ) := by
      refine asymptoticSliceRank_le_of_pow (r := 1) fun k ↦ ?_
      calc sliceRank (power (power T 0) k) ≤ rank (power (power T 0) k) := sliceRank_le_rank _
        _ ≤ rank (power T 0) ^ k := rank_power_le _ k
        _ ≤ 1 ^ k := Nat.pow_le_pow_left hrank k
    simpa using h
  · by_contra hcon
    rw [not_le] at hcon
    set b : ℝ := asymptoticSliceRank (power T n) with hbdef
    have hb : 0 ≤ b := asymptoticSliceRank_nonneg _
    set ρ₀ : ℝ := b ^ ((n : ℝ)⁻¹) with hρ₀def
    have hρ₀pow : ρ₀ ^ n = b := Real.rpow_inv_natCast_pow hb (by omega)
    have hlt : asymptoticSliceRank T < ρ₀ := by
      refine lt_of_pow_lt_pow_left₀ n (Real.rpow_nonneg hb _) ?_
      rw [hρ₀pow]
      exact hcon
    have hnonempty : Set.Nonempty {r : ℝ | ExponentialBound (sliceRankPowerSequence T) r} :=
      ⟨_, sliceRankPowerSequence_exponentialBound T⟩
    have hlt' : sInf {r : ℝ | ExponentialBound (sliceRankPowerSequence T) r} < ρ₀ := hlt
    obtain ⟨ρ, hρmem, hρlt⟩ := exists_lt_of_csInf_lt hnonempty hlt'
    have hρ : ExponentialBound (sliceRankPowerSequence T) ρ := hρmem
    obtain ⟨hρ0, C, hC, hbound⟩ := hρ
    have hpow : ExponentialBound (sliceRankPowerSequence (power T n)) (ρ ^ n) := by
      refine ⟨pow_nonneg hρ0 n, C, hC, fun k ↦ ?_⟩
      have hiso : sliceRankPowerSequence (power T n) k = sliceRankPowerSequence T (k * n) := by
        rw [sliceRankPowerSequence, sliceRankPowerSequence]
        exact sliceRank_isomorphic (Isomorphic.power_power T n k)
      have h := hbound (k * n)
      rw [pow_mul'] at h
      rw [hiso]
      exact h
    have hble : b ≤ ρ ^ n := asymptoticSliceRank_le hpow
    have hstrict : ρ ^ n < ρ₀ ^ n := by
      refine pow_lt_pow_left₀ hρlt hρ0 (by omega)
    rw [hρ₀pow] at hstrict
    linarith

end PowerLaw

end AlgebraicComplexity.Tensor
