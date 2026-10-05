/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.RectangularCertificate
import AlgebraicComplexity.MatrixMultiplication.RectangularHuangPan
import AlgebraicComplexity.MatrixMultiplication.Transpose

/-!
# The three-parameter rectangular exponent `ω(r, s, t)`

`MatrixMultiplication/RectangularExponent.lean` defines the two-parameter exponent
`rectangularOmega K κ = ω(1, κ, 1) = ω(1, 1, κ)`.  Huang and Pan (*Fast rectangular matrix
multiplication and applications*, J. Complexity 14 (1998), §2, p. 262) work with the full
three-parameter exponent `ω(r, s, t)` of the products `⟨n^r, n^s, n^t⟩`, and their §8.3 bounds are
genuinely three-parameter: they estimate `ω(t, 1, r)` for `r > 1 > t > 0`.  This module defines
that exponent and proves its elementary theory together with Huang--Pan's Theorem 8.1.

## Convention

`generalRectangularOmega K a b c` is the least admissible polynomial exponent of the rank sequence

`n ↦ rank ⟨⌈n^a⌉, ⌈n^b⌉, ⌈n^c⌉⟩`,

with the three dimensions in the same order as the arguments of
`AlgebraicComplexity.matrixMultiplication`, i.e. `⟨m, n, p⟩` is the `m × n` by `n × p` product.
This is exactly Huang--Pan's `ω(a, b, c)`, and each dimension uses the *same* rounding function
`rectangularMiddleDimension x n = ⌈(n : ℝ)^x⌉₊` already used by the two-parameter file.

`rectangularOmegaThree K t r := generalRectangularOmega K t 1 r` is Huang--Pan's `ω(t, 1, r)`, the
exponent of `⟨n^t, n, n^r⟩`.  Note the *leg order*: the normalized dimension `n` is the **middle**
one, so `rectangularOmegaThree K t 1 = rectangularOmega K t` requires the transposition
`⟨m,n,p⟩ ↦ ⟨n,m,p⟩` of `MatrixMultiplication/Transpose.lean`, while
`rectangularOmegaThree K 1 r = rectangularOmega K r` is the cyclic identification
`rectangularMatrixRankSequence_eq_rank_outer` of `MatrixMultiplication/RectangularCertificate.lean`.

As everywhere in this development the `ε` of the paper statements is absorbed by the infimum:
`generalRectangularOmega` is an `sInf` of *admissible* exponents (`Growth.PolynomialBound`), so
`ω(a,b,c) ≤ τ` is exactly the assertion that `rank ⟨⌈n^a⌉, ⌈n^b⌉, ⌈n^c⌉⟩ = O(n^(τ + ε))` for every
`ε > 0`.  Huang--Pan's `+ ε` therefore never appears in a statement below.

## Principal results

* `generalRectangularOmega_add_le`: the **product law**, and the engine of this module.  Because
  all three legs are powers of the *same* `n`, the external product of two families is again a
  family at the same scale, with the leg exponents *added*:
  `ω(a₁+a₂, b₁+b₂, c₁+c₂) ≤ ω(a₁,b₁,c₁) + ω(a₂,b₂,c₂)`, over every commutative semiring, with no
  rounding loss at all (`rectangularMiddleDimension_add_le_mul` is exact).  The two-parameter
  splitting law of `RectangularInterpolation.lean` needs the substitution `n ↦ ⌈n^θ⌉` because it
  keeps the outer dimensions equal to `n`; here that substitution is instead the separate
  homogeneity law;
* `generalRectangularOmega_smul`: **homogeneity**, Huang--Pan p. 262: `ω(θa, θb, θc) = θ·ω(a,b,c)`
  for `θ > 0` and `a, b, c ≥ 0`.  Both inequalities come from the single scaling estimate
  `generalRectangularOmega_scale_le`, applied to `θ` and to `θ⁻¹`.  Its consequence
  `generalRectangularOmega_eq_smul_rectangularOmegaThree` is Huang--Pan's remark that it suffices
  to estimate the normalized slice: `ω(a,b,c) = b·ω(a/b, 1, c/b)` for `b > 0`;
* `generalRectangularOmega_swapYZ`, `generalRectangularOmega_reverse`,
  `generalRectangularOmega_cycle`: **Huang--Pan (2.7)**, `ω` is invariant under all six
  permutations of its arguments.  In the normalized slice this is
  `rectangularOmegaThree_comm : ω(t,1,r) = ω(r,1,t)`;
* `rectangularOmegaThree_square`, `rectangularOmegaThree_right_one`,
  `rectangularOmegaThree_left_one`: `ω(1,1,1) = ω`, `ω(t,1,1) = ω(t)` and `ω(1,1,r) = ω(r)`,
  identifying the two-parameter theory as the two axes of the new one;
* `max_le_generalRectangularOmega`: **Huang--Pan (2.8)**, the information lower bound
  `max(a+b, b+c, c+a) ≤ ω(a,b,c)` over a field, one flattening per pair of legs.  In the slice:
  `max (t+1) (max (1+r) (r+t)) ≤ ω(t,1,r)`;
* `generalRectangularOmega_le_add`: the elementary upper bound `ω(a,b,c) ≤ a + b + c`;
* `rectangularOmegaThree_le_add_one_of_eq_two` and
  `rectangularOmegaThree_le_interpolation_of_eq_two`: **Huang--Pan Theorem 8.1 / (8.2), p. 281**,
  in witnessed form over an arbitrary commutative semiring, and
  `rectangularOmegaThree_le_huangPan_low` / `rectangularOmegaThree_le_huangPan_high` at the
  witness `κ₀ = α = rectangularAlpha F` over a field;
* `rectangularOmegaThree_rectangularAlpha`: the client.  Over a field, for every `r ≥ 1`,
  `ω(α, 1, r) = r + 1` **exactly**: Theorem 8.1 gives `≤` and (2.8) gives `≥`.  At `r = 1` this
  reads `ω(α, 1, 1) = 2`.  Since `Examples/CoppersmithRectangular1982.lean` proves
  `α ≥ 2 log 2 / (5 log 5) > 0.1722`, this is a nonvacuous exact value of a three-parameter
  exponent at an irrational point;
* `lt_rectangularOmegaThree_of_lt`: the recorded *negative* result.  Theorem 8.1's first branch
  `ω(t,1,r) ≤ r + 1` is false whenever `r < t`, since (2.8) gives `ω(t,1,r) ≥ 1 + t > 1 + r`.  The
  hypothesis `1 ≤ r` in both branches is therefore not an artefact of the proof.

## Layer placement and strategy

Layer 3, a leaf downstream of `RectangularCertificate.lean`, `RectangularHuangPan.lean` (hence of
`RectangularInterpolation.lean` and `RectangularExponent.lean`) and `Transpose.lean`.  It adds no
Mathlib dependency.

The design deliberately introduces the *fully general* `generalRectangularOmega K a b c` rather
than only the slice `ω(t, 1, r)`.  Two of the required laws are not statable in the slice:
homogeneity moves the middle exponent away from `1`, and the symmetry (2.7) permutes the middle
exponent into an outer position.  Fixing the middle exponent at `1` would have forced both to be
recorded as non-goals; with the general definition both are theorems, and the slice is a `def`
on top of them.

## What is *not* claimed

* Nothing below improves any *numerical* bound.  Theorem 8.1 is a consequence of the two-parameter
  theory (through `rectangularOmega_rectangularAlpha`, `rectangularOmega_one` and `omega`), and its
  strength is exactly the strength of `α` and `ω`.
* The `ω(t, 1, r) ≤ f(r, t)` bound of Huang--Pan (7.3), p. 280 — their own §7 construction in its
  three-parameter form — is not here.  The two-parameter §7 bound `f(r)` itself *is*: it is
  `Examples.huangPan_fullTensor_rectangularOmega_le` and its `r ≤ 1` companion
  (`Examples/CoppersmithWinogradRectangularHuangPan.lean`).  What (7.3) adds over `f(r)` is a
  second free exponent, which the schedule of that client currently fixes at `1`.
* No lower bound beyond the flattening bound (2.8) is claimed.

## References

* X. Huang and V. Y. Pan, *Fast rectangular matrix multiplication and applications*,
  J. Complexity 14 (1998), 257--299.  §2, p. 262: the notation `ω(r,s,t)`, the symmetry (2.7),
  the homogeneity equation `ω(ar,as,at) = a·ω(r,s,t)` and the information lower bound (2.8).
  §8.3, Theorem 8.1 and (8.2), pp. 281--283: the two-branch upper bound on `ω(t,1,r)`.
* D. Coppersmith, *Rapid multiplication of rectangular matrices*, SIAM J. Comput. 11 (1982): the
  source of `α > 0`, which is what makes Theorem 8.1 nonvacuous.
-/

namespace AlgebraicComplexity

open Tensor Growth

universe u

/-! ## Rank is invariant under permuting the three matrix dimensions

`MatrixMultiplication/Transpose.lean` transports rank *certificates* along the six dimension
orders.  Since every order is reachable in both directions, the induced statements about `rank`
itself are equalities.  These three lemmas are the only place where the permutation certificates
are used below. -/

section RankPermutation

variable {K : Type u} [CommSemiring K]

/-- Transposing the first two dimensions preserves rank: `rank ⟨m,n,p⟩ = rank ⟨n,m,p⟩`. -/
theorem rank_matrixMultiplication_swapYZ (m n p : ℕ) :
    rank (matrixMultiplication (K := K) m n p) = rank (matrixMultiplication (K := K) n m p) :=
  le_antisymm
    (rank_le_iff.mpr
      (rank_spec (matrixMultiplication (K := K) n m p)).matrixMultiplication_swapYZ)
    (rank_le_iff.mpr
      (rank_spec (matrixMultiplication (K := K) m n p)).matrixMultiplication_swapYZ)

/-- Reversing the dimension triple preserves rank: `rank ⟨m,n,p⟩ = rank ⟨p,n,m⟩`.  This is the
rank form of `(A·B)ᵀ = Bᵀ·Aᵀ`. -/
theorem rank_matrixMultiplication_reverse (m n p : ℕ) :
    rank (matrixMultiplication (K := K) m n p) = rank (matrixMultiplication (K := K) p n m) :=
  le_antisymm
    (rank_le_iff.mpr
      (rank_spec (matrixMultiplication (K := K) p n m)).matrixMultiplication_reverse)
    (rank_le_iff.mpr
      (rank_spec (matrixMultiplication (K := K) m n p)).matrixMultiplication_reverse)

/-- Cyclically rotating the dimension triple preserves rank: `rank ⟨m,n,p⟩ = rank ⟨p,m,n⟩`. -/
theorem rank_matrixMultiplication_cycle (m n p : ℕ) :
    rank (matrixMultiplication (K := K) m n p) = rank (matrixMultiplication (K := K) p m n) :=
  le_antisymm
    (rank_le_iff.mpr
      ((rank_spec (matrixMultiplication (K := K) p m n)).matrixMultiplication_cycle
        |>.matrixMultiplication_cycle))
    (rank_le_iff.mpr
      (rank_spec (matrixMultiplication (K := K) m n p)).matrixMultiplication_cycle)

end RankPermutation

/-! ## Dimension bookkeeping

Two exact (rounding-loss-free) estimates about `rectangularMiddleDimension`.  The first is the
whole content of the product law, the second of the scaling law. -/

/-- **Additivity of leg exponents**: `⌈n^(a+b)⌉ ≤ ⌈n^a⌉ · ⌈n^b⌉`, with no rounding loss.

Proof sketch: the right-hand side is a natural number, so `Nat.ceil_le` reduces the claim to
`n^(a+b) = n^a · n^b ≤ ⌈n^a⌉ · ⌈n^b⌉`, which is `Nat.le_ceil` in each factor. -/
theorem rectangularMiddleDimension_add_le_mul (a b : ℝ) {n : ℕ} (hn : 1 ≤ n) :
    rectangularMiddleDimension (a + b) n ≤
      rectangularMiddleDimension a n * rectangularMiddleDimension b n := by
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < (n : ℝ) := zero_lt_one.trans_le hn1
  apply Nat.ceil_le.mpr
  calc
    (n : ℝ) ^ (a + b) = (n : ℝ) ^ a * (n : ℝ) ^ b := Real.rpow_add hnpos a b
    _ ≤ (rectangularMiddleDimension a n : ℝ) * (rectangularMiddleDimension b n : ℝ) :=
      mul_le_mul (rpow_le_rectangularMiddleDimension a n)
        (rpow_le_rectangularMiddleDimension b n) (Real.rpow_nonneg hnpos.le b)
        (Nat.cast_nonneg _)
    _ = ((rectangularMiddleDimension a n * rectangularMiddleDimension b n : ℕ) : ℝ) := by
      push_cast; ring

/-- **Substituting `n ↦ ⌈n^θ⌉` multiplies leg exponents**: `⌈n^(θ·κ)⌉ ≤ ⌈⌈n^θ⌉^κ⌉` for `κ ≥ 0`,
with no rounding loss and no hypothesis on `θ` or `n`.

Proof sketch: `n^(θκ) = (n^θ)^κ ≤ ⌈n^θ⌉^κ` by monotonicity of `x ↦ x^κ` for `κ ≥ 0`, and then
`Nat.le_ceil` and `Nat.ceil_le`. -/
theorem rectangularMiddleDimension_comp_le {κ : ℝ} (hκ : 0 ≤ κ) (θ : ℝ) (n : ℕ) :
    rectangularMiddleDimension (θ * κ) n ≤
      rectangularMiddleDimension κ (rectangularMiddleDimension θ n) := by
  apply Nat.ceil_le.mpr
  calc
    (n : ℝ) ^ (θ * κ) = ((n : ℝ) ^ θ) ^ κ := Real.rpow_mul (Nat.cast_nonneg n) θ κ
    _ ≤ ((rectangularMiddleDimension θ n : ℕ) : ℝ) ^ κ :=
      Real.rpow_le_rpow (Real.rpow_nonneg (Nat.cast_nonneg n) θ)
        (rpow_le_rectangularMiddleDimension θ n) hκ
    _ ≤ _ := rpow_le_rectangularMiddleDimension κ _

variable (K : Type u) [CommSemiring K]

/-! ## The three-parameter exponent -/

/-- Ordinary ranks of the general rectangular matrix-multiplication tensors
`⟨⌈n^a⌉, ⌈n^b⌉, ⌈n^c⌉⟩` over `K`.  This is the rank sequence whose polynomial exponent is
Huang--Pan's `ω(a, b, c)`. -/
noncomputable def generalRectangularRankSequence (a b c : ℝ) (n : ℕ) : ℕ :=
  rank (matrixMultiplication (K := K) (rectangularMiddleDimension a n)
    (rectangularMiddleDimension b n) (rectangularMiddleDimension c n))

/-- `τ` is a polynomial upper bound for the `(a,b,c)`-rectangular ranks over `K`. -/
abbrev GeneralRectangularExponentLE (a b c τ : ℝ) : Prop :=
  PolynomialBound (generalRectangularRankSequence K a b c) τ

/-- **Huang--Pan's three-parameter exponent `ω(a, b, c)`** (§2, p. 262): the least real `τ` such
that `rank ⟨⌈n^a⌉, ⌈n^b⌉, ⌈n^c⌉⟩ ≤ C·n^τ` for some constant `C` and all positive `n`. -/
noncomputable def generalRectangularOmega (a b c : ℝ) : ℝ :=
  polynomialExponent (generalRectangularRankSequence K a b c)

/-- **Huang--Pan's `ω(t, 1, r)`** (§8.3, p. 281): the exponent of the products `⟨n^t, n, n^r⟩`,
the normalized slice of `generalRectangularOmega` on which Theorem 8.1 is stated. -/
noncomputable def rectangularOmegaThree (t r : ℝ) : ℝ :=
  generalRectangularOmega K t 1 r

theorem rectangularOmegaThree_def (t r : ℝ) :
    rectangularOmegaThree K t r = generalRectangularOmega K t 1 r := rfl

/-- The unfolded form of the definition, with the middle dimension displayed as `n` itself. -/
theorem rectangularOmegaThree_eq (t r : ℝ) :
    rectangularOmegaThree K t r =
      polynomialExponent (fun n : ℕ ↦ rank (matrixMultiplication (K := K)
        (rectangularMiddleDimension t n) n (rectangularMiddleDimension r n))) := by
  unfold rectangularOmegaThree generalRectangularOmega
  congr 1
  funext n
  unfold generalRectangularRankSequence
  rw [rectangularMiddleDimension_one]

theorem generalRectangularOmega_nonneg (a b c : ℝ) : 0 ≤ generalRectangularOmega K a b c :=
  polynomialExponent_nonneg _

theorem rectangularOmegaThree_nonneg (t r : ℝ) : 0 ≤ rectangularOmegaThree K t r :=
  generalRectangularOmega_nonneg K t 1 r

/-- A concrete polynomial rank bound gives an upper bound on the three-parameter exponent. -/
theorem generalRectangularOmega_le {a b c τ : ℝ} (h : GeneralRectangularExponentLE K a b c τ) :
    generalRectangularOmega K a b c ≤ τ :=
  polynomialExponent_le h

/-! ## The elementary upper bound `ω(a,b,c) ≤ a + b + c` -/

/-- The defining `⌈n^a⌉·⌈n^b⌉·⌈n^c⌉`-term decomposition bounds each rank. -/
theorem generalRectangularRankSequence_le_mul (a b c : ℝ) (n : ℕ) :
    generalRectangularRankSequence K a b c n ≤
      rectangularMiddleDimension a n * rectangularMiddleDimension b n *
        rectangularMiddleDimension c n :=
  rank_le_iff.mpr (matrixMultiplication_rankLE (K := K) _ _ _)

/-- Rounding a single leg up costs at most a factor two, uniformly in the sign of the exponent. -/
private theorem middle_le_two_mul_rpow_max (x : ℝ) {n : ℕ} (hn : 1 ≤ n) :
    (rectangularMiddleDimension x n : ℝ) ≤ 2 * (n : ℝ) ^ max x 0 :=
  le_trans (by exact_mod_cast rectangularMiddleDimension_mono hn (le_max_left x 0))
    (rectangularMiddleDimension_le_two_mul_rpow (le_max_right x 0) hn)

/-- The elementary algorithm gives the polynomial bound `max a 0 + max b 0 + max c 0` for every
triple of real exponents, with constant `8` absorbing the three ceilings. -/
theorem generalRectangularExponentLE_add_max (a b c : ℝ) :
    GeneralRectangularExponentLE K a b c (max a 0 + max b 0 + max c 0) := by
  have ha := le_max_right a (0 : ℝ)
  have hb := le_max_right b (0 : ℝ)
  have hc := le_max_right c (0 : ℝ)
  refine ⟨by linarith, 8, by norm_num, ?_⟩
  intro n hn
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < (n : ℝ) := zero_lt_one.trans_le hn1
  calc
    (generalRectangularRankSequence K a b c n : ℝ)
        ≤ ((rectangularMiddleDimension a n * rectangularMiddleDimension b n *
              rectangularMiddleDimension c n : ℕ) : ℝ) := by
          exact_mod_cast generalRectangularRankSequence_le_mul K a b c n
    _ = (rectangularMiddleDimension a n : ℝ) * (rectangularMiddleDimension b n : ℝ) *
          (rectangularMiddleDimension c n : ℝ) := by push_cast; ring
    _ ≤ (2 * (n : ℝ) ^ max a 0) * (2 * (n : ℝ) ^ max b 0) * (2 * (n : ℝ) ^ max c 0) := by
          gcongr <;> exact middle_le_two_mul_rpow_max _ hn
    _ = 8 * ((n : ℝ) ^ max a 0 * (n : ℝ) ^ max b 0 * (n : ℝ) ^ max c 0) := by ring
    _ = 8 * (n : ℝ) ^ (max a 0 + max b 0 + max c 0) := by
          rw [← Real.rpow_add hnpos, ← Real.rpow_add hnpos]

/-- Every general rectangular rank sequence admits some polynomial bound; this nonemptiness makes
the defining infimum well behaved for every triple of real exponents. -/
theorem generalRectangularExponentLE_exists (a b c : ℝ) :
    ∃ τ, GeneralRectangularExponentLE K a b c τ :=
  ⟨_, generalRectangularExponentLE_add_max K a b c⟩

/-- **The elementary upper bound** `ω(a,b,c) ≤ a + b + c` for nonnegative exponents, over every
commutative semiring. -/
theorem generalRectangularOmega_le_add {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    generalRectangularOmega K a b c ≤ a + b + c := by
  have h := generalRectangularOmega_le K (generalRectangularExponentLE_add_max K a b c)
  rwa [max_eq_left ha, max_eq_left hb, max_eq_left hc] at h

/-- Slice form: `ω(t, 1, r) ≤ t + 1 + r` for `t, r ≥ 0`. -/
theorem rectangularOmegaThree_le_add {t r : ℝ} (ht : 0 ≤ t) (hr : 0 ≤ r) :
    rectangularOmegaThree K t r ≤ t + 1 + r :=
  generalRectangularOmega_le_add K ht zero_le_one hr

/-- Every real exponent strictly above `ω(a,b,c)` is an admissible uniform polynomial rank bound.
This is the usable upper-closure property of the defining infimum, and the device by which
Huang--Pan's `+ ε` is absorbed throughout this file. -/
theorem generalRectangularExponentLE_of_lt {a b c τ : ℝ}
    (hτ : generalRectangularOmega K a b c < τ) :
    GeneralRectangularExponentLE K a b c τ := by
  have hnonempty :
      Set.Nonempty {σ : ℝ | PolynomialBound (generalRectangularRankSequence K a b c) σ} :=
    generalRectangularExponentLE_exists K a b c
  obtain ⟨σ, hσ, hστ⟩ := exists_lt_of_csInf_lt hnonempty hτ
  exact hσ.mono_exponent hστ.le

/-! ## Monotonicity in each parameter -/

/-- For fixed positive `n`, enlarging any leg exponent enlarges the rank: the wider tensor
restricts onto the narrower one by dropping coordinates. -/
theorem generalRectangularRankSequence_mono {a a' b b' c c' : ℝ}
    (ha : a ≤ a') (hb : b ≤ b') (hc : c ≤ c') {n : ℕ} (hn : 1 ≤ n) :
    generalRectangularRankSequence K a b c n ≤ generalRectangularRankSequence K a' b' c' n :=
  rank_restricts_le
    (matrixMultiplication_restricts (K := K) (rectangularMiddleDimension_mono hn ha)
      (rectangularMiddleDimension_mono hn hb) (rectangularMiddleDimension_mono hn hc))

/-- **Monotonicity**: `ω(a,b,c)` is monotone in each of its three arguments, over every
commutative semiring. -/
theorem generalRectangularOmega_mono {a a' b b' c c' : ℝ}
    (ha : a ≤ a') (hb : b ≤ b') (hc : c ≤ c') :
    generalRectangularOmega K a b c ≤ generalRectangularOmega K a' b' c' :=
  Growth.polynomialExponent_mono
    (fun _ hn ↦ generalRectangularRankSequence_mono K ha hb hc hn)
    (generalRectangularExponentLE_exists K a' b' c')

/-- Slice form: `ω(t, 1, r)` is monotone in `t` and in `r`. -/
theorem rectangularOmegaThree_mono {t t' r r' : ℝ} (ht : t ≤ t') (hr : r ≤ r') :
    rectangularOmegaThree K t r ≤ rectangularOmegaThree K t' r' :=
  generalRectangularOmega_mono K ht le_rfl hr

/-! ## Huang--Pan (2.7): symmetry in the three parameters -/

/-- Transposing the first two parameters preserves the rank sequence. -/
theorem generalRectangularRankSequence_swapYZ (a b c : ℝ) (n : ℕ) :
    generalRectangularRankSequence K a b c n = generalRectangularRankSequence K b a c n := by
  unfold generalRectangularRankSequence
  exact rank_matrixMultiplication_swapYZ _ _ _

/-- Reversing the parameter triple preserves the rank sequence. -/
theorem generalRectangularRankSequence_reverse (a b c : ℝ) (n : ℕ) :
    generalRectangularRankSequence K a b c n = generalRectangularRankSequence K c b a n := by
  unfold generalRectangularRankSequence
  exact rank_matrixMultiplication_reverse _ _ _

/-- Cyclically rotating the parameter triple preserves the rank sequence. -/
theorem generalRectangularRankSequence_cycle (a b c : ℝ) (n : ℕ) :
    generalRectangularRankSequence K a b c n = generalRectangularRankSequence K c a b n := by
  unfold generalRectangularRankSequence
  exact rank_matrixMultiplication_cycle _ _ _

/-- **Huang--Pan (2.7)**, transposition generator: `ω(a,b,c) = ω(b,a,c)`. -/
theorem generalRectangularOmega_swapYZ (a b c : ℝ) :
    generalRectangularOmega K a b c = generalRectangularOmega K b a c := by
  unfold generalRectangularOmega
  congr 1
  funext n
  exact generalRectangularRankSequence_swapYZ K a b c n

/-- **Huang--Pan (2.7)**, reversal: `ω(a,b,c) = ω(c,b,a)`. -/
theorem generalRectangularOmega_reverse (a b c : ℝ) :
    generalRectangularOmega K a b c = generalRectangularOmega K c b a := by
  unfold generalRectangularOmega
  congr 1
  funext n
  exact generalRectangularRankSequence_reverse K a b c n

/-- **Huang--Pan (2.7)**, rotation generator: `ω(a,b,c) = ω(c,a,b)`.  Together with
`generalRectangularOmega_swapYZ` this gives invariance under all six permutations, which is
exactly (2.7). -/
theorem generalRectangularOmega_cycle (a b c : ℝ) :
    generalRectangularOmega K a b c = generalRectangularOmega K c a b := by
  unfold generalRectangularOmega
  congr 1
  funext n
  exact generalRectangularRankSequence_cycle K a b c n

/-- **Huang--Pan (2.7) in the normalized slice**: `ω(t,1,r) = ω(r,1,t)`, the symmetry in the two
outer parameters. -/
theorem rectangularOmegaThree_comm (t r : ℝ) :
    rectangularOmegaThree K t r = rectangularOmegaThree K r t :=
  generalRectangularOmega_reverse K t 1 r

/-! ## The two axes: reduction to the two-parameter exponent -/

/-- At `(1,1,1)` the general rank sequence is the square one. -/
theorem generalRectangularRankSequence_one_one_one :
    generalRectangularRankSequence K 1 1 1 = squareMatrixRankSequence K := by
  funext n
  unfold generalRectangularRankSequence squareMatrixRankSequence
  rw [rectangularMiddleDimension_one]

/-- `ω(1,1,1) = ω`, an equality of the defining infima. -/
theorem generalRectangularOmega_square : generalRectangularOmega K 1 1 1 = omega K := by
  unfold generalRectangularOmega omega matrixMultiplicationExponent
  rw [generalRectangularRankSequence_one_one_one]

/-- At `(1,1,c)` the general rank sequence is the two-parameter one, in Huang--Pan's
outer-dimension normalization `ω(1,1,κ)`; the identification is
`rectangularMatrixRankSequence_eq_rank_outer`. -/
theorem generalRectangularRankSequence_outer (c : ℝ) :
    generalRectangularRankSequence K 1 1 c = rectangularMatrixRankSequence K c := by
  funext n
  unfold generalRectangularRankSequence
  rw [rectangularMiddleDimension_one, ← rectangularMatrixRankSequence_eq_rank_outer]

/-- `ω(1,1,κ) = ω(κ)`: the two-parameter exponent read off the third axis. -/
theorem generalRectangularOmega_outer (c : ℝ) :
    generalRectangularOmega K 1 1 c = rectangularOmega K c := by
  unfold generalRectangularOmega rectangularOmega rectangularMatrixMultiplicationExponent
  rw [generalRectangularRankSequence_outer]

/-- At `(1,b,1)` the general rank sequence is literally the two-parameter one. -/
theorem generalRectangularRankSequence_middle (b : ℝ) :
    generalRectangularRankSequence K 1 b 1 = rectangularMatrixRankSequence K b := by
  funext n
  unfold generalRectangularRankSequence rectangularMatrixRankSequence
  rw [rectangularMiddleDimension_one]

/-- `ω(1,κ,1) = ω(κ)`: the two-parameter exponent read off the middle axis. -/
theorem generalRectangularOmega_middle (b : ℝ) :
    generalRectangularOmega K 1 b 1 = rectangularOmega K b := by
  unfold generalRectangularOmega rectangularOmega rectangularMatrixMultiplicationExponent
  rw [generalRectangularRankSequence_middle]

/-- **`ω(1,1,1) = ω`** in the slice notation: the diagonal point of the three-parameter exponent
is the square matrix-multiplication exponent. -/
theorem rectangularOmegaThree_square : rectangularOmegaThree K 1 1 = omega K :=
  generalRectangularOmega_square K

/-- **`ω(1,1,r) = ω(r)`**: fixing the first parameter at `1` recovers the two-parameter exponent.
This is the cyclic identification, `rectangularMatrixRankSequence_eq_rank_outer`. -/
theorem rectangularOmegaThree_left_one (r : ℝ) :
    rectangularOmegaThree K 1 r = rectangularOmega K r :=
  generalRectangularOmega_outer K r

/-- **`ω(t,1,1) = ω(t)`**: fixing the last parameter at `1` recovers the two-parameter exponent.
Here the middle exponent must be moved into an outer position, which needs the transposition of
`MatrixMultiplication/Transpose.lean`. -/
theorem rectangularOmegaThree_right_one (t : ℝ) :
    rectangularOmegaThree K t 1 = rectangularOmega K t := by
  rw [rectangularOmegaThree_def, generalRectangularOmega_swapYZ, generalRectangularOmega_middle]

/-! ## The product law

Because all three legs are powers of the *same* `n`, the external product of two families at scale
`n` is a family at scale `n` whose leg exponents are the sums.  This is the engine of the whole
module, and unlike the two-parameter split of `RectangularInterpolation.lean` it loses nothing:
neither a rounding factor nor a constraint on the signs of the exponents. -/

/-- **Product law for general rectangular ranks.**  For `n ≥ 1`,

`rank ⟨⌈n^(a₁+a₂)⌉, ⌈n^(b₁+b₂)⌉, ⌈n^(c₁+c₂)⌉⟩ ≤ rank ⟨⌈n^a₁⌉,…⟩ · rank ⟨⌈n^a₂⌉,…⟩`,

over every commutative semiring and for arbitrary real exponents.

Proof sketch: `Tensor.RankLE.matrixMultiplication_mul` multiplies the two rank decompositions into
one for `⟨⌈n^a₁⌉·⌈n^a₂⌉, ⌈n^b₁⌉·⌈n^b₂⌉, ⌈n^c₁⌉·⌈n^c₂⌉⟩`, and
`rectangularMiddleDimension_add_le_mul` says the target fits inside it in each of the three
dimensions, so `matrixMultiplication_restricts` transports the certificate. -/
theorem generalRectangularRankSequence_mul_le
    (a₁ b₁ c₁ a₂ b₂ c₂ : ℝ) {n : ℕ} (hn : 1 ≤ n) :
    generalRectangularRankSequence K (a₁ + a₂) (b₁ + b₂) (c₁ + c₂) n ≤
      generalRectangularRankSequence K a₁ b₁ c₁ n *
        generalRectangularRankSequence K a₂ b₂ c₂ n :=
  rank_le_iff.mpr
    (((rank_spec _).matrixMultiplication_mul (rank_spec _)).of_restricts
      (matrixMultiplication_restricts (K := K)
        (rectangularMiddleDimension_add_le_mul a₁ a₂ hn)
        (rectangularMiddleDimension_add_le_mul b₁ b₂ hn)
        (rectangularMiddleDimension_add_le_mul c₁ c₂ hn)))

/-- **Product law for admissible exponents.**  Admissible exponents add along the product law,
with the two polynomial-bound constants simply multiplying: no rounding is paid. -/
theorem generalRectangularExponentLE_mul {a₁ b₁ c₁ a₂ b₂ c₂ τ₁ τ₂ : ℝ}
    (h₁ : GeneralRectangularExponentLE K a₁ b₁ c₁ τ₁)
    (h₂ : GeneralRectangularExponentLE K a₂ b₂ c₂ τ₂) :
    GeneralRectangularExponentLE K (a₁ + a₂) (b₁ + b₂) (c₁ + c₂) (τ₁ + τ₂) := by
  obtain ⟨hτ₁, C₁, hC₁, hb₁⟩ := h₁
  obtain ⟨hτ₂, C₂, hC₂, hb₂⟩ := h₂
  refine ⟨by linarith, C₁ * C₂, by positivity, ?_⟩
  intro n hn
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < (n : ℝ) := zero_lt_one.trans_le hn1
  calc
    (generalRectangularRankSequence K (a₁ + a₂) (b₁ + b₂) (c₁ + c₂) n : ℝ)
        ≤ ((generalRectangularRankSequence K a₁ b₁ c₁ n *
              generalRectangularRankSequence K a₂ b₂ c₂ n : ℕ) : ℝ) := by
          exact_mod_cast generalRectangularRankSequence_mul_le K a₁ b₁ c₁ a₂ b₂ c₂ hn
    _ = (generalRectangularRankSequence K a₁ b₁ c₁ n : ℝ) *
          (generalRectangularRankSequence K a₂ b₂ c₂ n : ℝ) := by push_cast; ring
    _ ≤ (C₁ * (n : ℝ) ^ τ₁) * (C₂ * (n : ℝ) ^ τ₂) :=
      mul_le_mul (hb₁ n hn) (hb₂ n hn) (Nat.cast_nonneg _) (by positivity)
    _ = (C₁ * C₂) * ((n : ℝ) ^ τ₁ * (n : ℝ) ^ τ₂) := by ring
    _ = (C₁ * C₂) * (n : ℝ) ^ (τ₁ + τ₂) := by rw [← Real.rpow_add hnpos]

/-- **Subadditivity of the three-parameter exponent under addition of leg exponents**:

`ω(a₁+a₂, b₁+b₂, c₁+c₂) ≤ ω(a₁,b₁,c₁) + ω(a₂,b₂,c₂)`,

over every commutative semiring and for arbitrary real exponents.  Every upper bound of §8.3
below is an instance of this law together with the elementary bound and homogeneity. -/
theorem generalRectangularOmega_add_le (a₁ b₁ c₁ a₂ b₂ c₂ : ℝ) :
    generalRectangularOmega K (a₁ + a₂) (b₁ + b₂) (c₁ + c₂) ≤
      generalRectangularOmega K a₁ b₁ c₁ + generalRectangularOmega K a₂ b₂ c₂ := by
  apply le_of_forall_pos_le_add
  intro ε hε
  have hadm := generalRectangularExponentLE_mul K
    (generalRectangularExponentLE_of_lt K
      (show generalRectangularOmega K a₁ b₁ c₁ < generalRectangularOmega K a₁ b₁ c₁ + ε / 2 by
        linarith))
    (generalRectangularExponentLE_of_lt K
      (show generalRectangularOmega K a₂ b₂ c₂ < generalRectangularOmega K a₂ b₂ c₂ + ε / 2 by
        linarith))
  have hle := generalRectangularOmega_le K hadm
  linarith

/-! ## Homogeneity (Huang--Pan, p. 262) -/

/-- Substituting `n ↦ ⌈n^θ⌉` multiplies every leg exponent by `θ`, at the level of rank
sequences. -/
theorem generalRectangularRankSequence_scale_le {a b c : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (θ : ℝ) (n : ℕ) :
    generalRectangularRankSequence K (θ * a) (θ * b) (θ * c) n ≤
      generalRectangularRankSequence K a b c (rectangularMiddleDimension θ n) :=
  rank_restricts_le
    (matrixMultiplication_restricts (K := K) (rectangularMiddleDimension_comp_le ha θ n)
      (rectangularMiddleDimension_comp_le hb θ n) (rectangularMiddleDimension_comp_le hc θ n))

/-- Substituting `n ↦ ⌈n^θ⌉` multiplies every admissible exponent by `θ`, for `θ ≥ 0`.  The single
rounding factor `2^τ` is absorbed into the polynomial-bound constant. -/
theorem generalRectangularExponentLE_scale {a b c τ θ : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hθ : 0 ≤ θ)
    (h : GeneralRectangularExponentLE K a b c τ) :
    GeneralRectangularExponentLE K (θ * a) (θ * b) (θ * c) (θ * τ) := by
  obtain ⟨hτ, C, hC, hbound⟩ := h
  refine ⟨mul_nonneg hθ hτ, C * 2 ^ τ, by positivity, ?_⟩
  intro n hn
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < (n : ℝ) := zero_lt_one.trans_le hn1
  have hm : 1 ≤ rectangularMiddleDimension θ n := rectangularMiddleDimension_pos θ hn
  calc
    (generalRectangularRankSequence K (θ * a) (θ * b) (θ * c) n : ℝ)
        ≤ (generalRectangularRankSequence K a b c (rectangularMiddleDimension θ n) : ℝ) := by
          exact_mod_cast generalRectangularRankSequence_scale_le K ha hb hc θ n
    _ ≤ C * ((rectangularMiddleDimension θ n : ℕ) : ℝ) ^ τ := hbound _ hm
    _ ≤ C * (2 * (n : ℝ) ^ θ) ^ τ :=
      mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (Nat.cast_nonneg _)
          (rectangularMiddleDimension_le_two_mul_rpow hθ hn) hτ) hC.le
    _ = C * (2 ^ τ * ((n : ℝ) ^ θ) ^ τ) := by
      rw [Real.mul_rpow (by norm_num) (Real.rpow_nonneg hnpos.le θ)]
    _ = C * 2 ^ τ * (n : ℝ) ^ (θ * τ) := by rw [← Real.rpow_mul hnpos.le]; ring

/-- **Scaling inequality**: `ω(θa, θb, θc) ≤ θ·ω(a,b,c)` for `θ ≥ 0` and `a, b, c ≥ 0`, over every
commutative semiring.  This one inequality gives homogeneity, by applying it to `θ` and to `θ⁻¹`;
it is also all that Theorem 8.1 needs. -/
theorem generalRectangularOmega_scale_le {a b c θ : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hθ : 0 ≤ θ) :
    generalRectangularOmega K (θ * a) (θ * b) (θ * c) ≤ θ * generalRectangularOmega K a b c := by
  apply le_of_forall_pos_le_add
  intro ε hε
  have hpos : (0 : ℝ) < θ + 1 := by linarith
  have hδ : (0 : ℝ) < ε / (θ + 1) := by positivity
  have hadm := generalRectangularExponentLE_scale K ha hb hc hθ
    (generalRectangularExponentLE_of_lt K
      (show generalRectangularOmega K a b c <
          generalRectangularOmega K a b c + ε / (θ + 1) by linarith))
  have hle := generalRectangularOmega_le K hadm
  have hsmall : θ * (ε / (θ + 1)) ≤ ε := by
    rw [mul_comm, div_mul_eq_mul_div, div_le_iff₀ hpos]
    nlinarith
  nlinarith [hle, hsmall]

/-- **Homogeneity** (Huang--Pan, §2, p. 262): `ω(θa, θb, θc) = θ·ω(a,b,c)` for `θ > 0` and
nonnegative `a, b, c`, over every commutative semiring.

Proof sketch: `generalRectangularOmega_scale_le` gives `≤` directly, and gives `≥` after being
applied at the scaled triple with the reciprocal factor `θ⁻¹`, which returns the original
triple. -/
theorem generalRectangularOmega_smul {a b c θ : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hθ : 0 < θ) :
    generalRectangularOmega K (θ * a) (θ * b) (θ * c) = θ * generalRectangularOmega K a b c := by
  refine le_antisymm (generalRectangularOmega_scale_le K ha hb hc hθ.le) ?_
  have h := generalRectangularOmega_scale_le K (a := θ * a) (b := θ * b) (c := θ * c)
    (θ := θ⁻¹) (by positivity) (by positivity) (by positivity) (by positivity)
  rw [show θ⁻¹ * (θ * a) = a by field_simp, show θ⁻¹ * (θ * b) = b by field_simp,
    show θ⁻¹ * (θ * c) = c by field_simp] at h
  have h' := mul_le_mul_of_nonneg_left h hθ.le
  rw [← mul_assoc, mul_inv_cancel₀ hθ.ne', one_mul] at h'
  exact h'

/-- **Reduction to the normalized slice** (Huang--Pan, p. 262: "it suffices to estimate any one of
the six latter exponents"): for `b > 0` and `a, c ≥ 0`,

`ω(a, b, c) = b · ω(a/b, 1, c/b)`.

This is the exact sense in which the two-parameter family `rectangularOmegaThree` determines the
whole three-parameter exponent, and the reason a fixed middle exponent is no loss of generality. -/
theorem generalRectangularOmega_eq_smul_rectangularOmegaThree
    {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 < b) (hc : 0 ≤ c) :
    generalRectangularOmega K a b c = b * rectangularOmegaThree K (a / b) (c / b) := by
  have h := generalRectangularOmega_smul K (a := a / b) (b := 1) (c := c / b) (θ := b)
    (by positivity) zero_le_one (by positivity) hb
  rw [show b * (a / b) = a by field_simp, show b * (1 : ℝ) = b by ring,
    show b * (c / b) = c by field_simp] at h
  exact h

/-! ## Huang--Pan Theorem 8.1 (§8.3, p. 281), in witnessed form

Both branches hold over an arbitrary commutative semiring once a witness `κ₀` with
`ω(κ₀) = 2` is supplied; the classical statements are the case `κ₀ = α`, available over a field
from `rectangularOmega_rectangularAlpha`.  Both branches require `r ≥ 1`, which is Huang--Pan's
standing assumption `r > 1 > t > 0` in §8.3, and which `lt_rectangularOmegaThree_of_lt` shows to be
necessary. -/

/-- **Huang--Pan Theorem 8.1, first branch** (§8.3, (8.2), p. 281), in witnessed form.  If
`ω(t) = 2` then for every `r ≥ 1`

`ω(t, 1, r) ≤ r + 1`.

Huang--Pan's derivation is `M(n^t, n, n^r) ≤ n^(r-1)·M(n, n, n^t) = n^(r-1)·O(n^(2+ε))`; here that
is the product law at the splitting `(t, 1, r) = (t, 1, 1) + (0, 0, r-1)`, the first summand being
`ω(t,1,1) = ω(t) = 2` and the second the elementary bound `ω(0,0,r-1) ≤ r-1`.  The `+ ε` of the
paper is absorbed by the infimum. -/
theorem rectangularOmegaThree_le_add_one_of_eq_two {t r : ℝ}
    (hbase : rectangularOmega K t = 2) (hr : 1 ≤ r) :
    rectangularOmegaThree K t r ≤ r + 1 := by
  have hsplit := generalRectangularOmega_add_le K t 1 1 0 0 (r - 1)
  rw [add_zero, add_zero, show (1 : ℝ) + (r - 1) = r by ring] at hsplit
  have h1 : generalRectangularOmega K t 1 1 = 2 := by
    rw [generalRectangularOmega_swapYZ, generalRectangularOmega_middle, hbase]
  have h2 : generalRectangularOmega K 0 0 (r - 1) ≤ r - 1 := by
    have h := generalRectangularOmega_le_add K (a := (0 : ℝ)) (b := (0 : ℝ)) (c := r - 1)
      le_rfl le_rfl (by linarith)
    linarith
  rw [rectangularOmegaThree_def]
  linarith

/-- **Huang--Pan Theorem 8.1, second branch** (§8.3, (8.2) and its proof, pp. 281--283), in
witnessed form.  If `0 ≤ κ₀ < 1` and `ω(κ₀) = 2`, then for `κ₀ ≤ t ≤ 1` and `r ≥ 1`

`ω(t, 1, r) ≤ (r·(1 - κ₀) + (1 - t) + (ω - 1)·(t - κ₀)) / (1 - κ₀)`.

Proof, following Huang--Pan p. 283 verbatim.  Put `θ = (t - κ₀)/(1 - κ₀)` and
`β = (1 - t)/(1 - κ₀)`, so that `θ + β = 1` and `β·κ₀ + θ = t`.  By (2.7),
`ω(t,1,r) = ω(r,1,t)`, and the product law at

`(r, 1, t) = (r - θ, β, β·κ₀) + (θ, θ, θ)`,
`(r - θ, β, β·κ₀) = (r - θ - β, 0, 0) + (β, β, β·κ₀)`

reduces the claim to three estimates: the elementary bound `ω(r-θ-β, 0, 0) ≤ r - θ - β`, legal
because `r - θ - β = r - 1 ≥ 0` — this is exactly where `r ≥ 1` is used; the scaling bound
`ω(β, β, β·κ₀) ≤ β·ω(1,1,κ₀) = 2β`; and the scaling bound `ω(θ,θ,θ) ≤ θ·ω`.  Their sum is
`r - θ + β + θ·ω`, which is the displayed right-hand side. -/
theorem rectangularOmegaThree_le_interpolation_of_eq_two {t r κ₀ : ℝ}
    (hκ₀ : 0 ≤ κ₀) (hκ₀one : κ₀ < 1) (hbase : rectangularOmega K κ₀ = 2)
    (hle : κ₀ ≤ t) (ht1 : t ≤ 1) (hr : 1 ≤ r) :
    rectangularOmegaThree K t r ≤
      (r * (1 - κ₀) + (1 - t) + (omega K - 1) * (t - κ₀)) / (1 - κ₀) := by
  have hden : (0 : ℝ) < 1 - κ₀ := by linarith
  obtain ⟨θ, hθ⟩ : ∃ θ : ℝ, θ = (t - κ₀) / (1 - κ₀) := ⟨_, rfl⟩
  obtain ⟨β, hβ⟩ : ∃ β : ℝ, β = (1 - t) / (1 - κ₀) := ⟨_, rfl⟩
  have hθ0 : 0 ≤ θ := by rw [hθ]; exact div_nonneg (by linarith) hden.le
  have hβ0 : 0 ≤ β := by rw [hβ]; exact div_nonneg (by linarith) hden.le
  have hsum : θ + β = 1 := by
    have hcollect : θ + β = ((t - κ₀) + (1 - t)) / (1 - κ₀) := by rw [hθ, hβ]; ring
    rw [hcollect, show (t - κ₀) + (1 - t) = 1 - κ₀ by ring, div_self hden.ne']
  have hmix : β * κ₀ + θ = t := by
    have hcollect : β * κ₀ + θ = ((1 - t) * κ₀ + (t - κ₀)) / (1 - κ₀) := by
      rw [hθ, hβ]; ring
    rw [hcollect, show (1 - t) * κ₀ + (t - κ₀) = t * (1 - κ₀) by ring, mul_div_assoc,
      div_self hden.ne', mul_one]
  -- The two applications of the product law.
  have hstep1 := generalRectangularOmega_add_le K (r - θ) β (β * κ₀) θ θ θ
  rw [show r - θ + θ = r by ring, show β + θ = (1 : ℝ) by linarith, hmix] at hstep1
  have hstep2 := generalRectangularOmega_add_le K (r - θ - β) 0 0 β β (β * κ₀)
  rw [show r - θ - β + β = r - θ by ring, zero_add, zero_add] at hstep2
  -- The three estimates.
  have h3 : generalRectangularOmega K (r - θ - β) 0 0 ≤ r - θ - β := by
    have h := generalRectangularOmega_le_add K (a := r - θ - β) (b := (0 : ℝ)) (c := (0 : ℝ))
      (by linarith) le_rfl le_rfl
    linarith
  have h4 : generalRectangularOmega K β β (β * κ₀) ≤ β * 2 := by
    have h := generalRectangularOmega_scale_le K (a := (1 : ℝ)) (b := (1 : ℝ)) (c := κ₀)
      zero_le_one zero_le_one hκ₀ hβ0
    simp only [mul_one] at h
    rwa [generalRectangularOmega_outer, hbase] at h
  have h5 : generalRectangularOmega K θ θ θ ≤ θ * omega K := by
    have h := generalRectangularOmega_scale_le K (a := (1 : ℝ)) (b := (1 : ℝ)) (c := (1 : ℝ))
      zero_le_one zero_le_one zero_le_one hθ0
    simp only [mul_one] at h
    rwa [generalRectangularOmega_square] at h
  -- Assemble, using (2.7) to read `ω(t,1,r)` as `ω(r,1,t)`.
  have hsym : rectangularOmegaThree K t r = generalRectangularOmega K r 1 t := by
    rw [rectangularOmegaThree_def, generalRectangularOmega_reverse]
  have hfinal : r - θ - β + β * 2 + θ * omega K =
      (r * (1 - κ₀) + (1 - t) + (omega K - 1) * (t - κ₀)) / (1 - κ₀) := by
    rw [hθ, hβ]
    field_simp
    ring
  rw [hsym]
  linarith

/-! ## Flattening lower bounds: Huang--Pan (2.8), over a field -/

section FieldLowerBound

variable (F : Type u) [Field F]

/-- Flattening on the `X` leg gives `a + b ≤ ω(a,b,c)` (Huang--Pan (2.8), first term). -/
theorem add_le_generalRectangularOmega_XY (a b c : ℝ) :
    a + b ≤ generalRectangularOmega F a b c := by
  apply le_polynomialExponent_of_rpow_le (generalRectangularExponentLE_exists F a b c)
  intro n hn
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < (n : ℝ) := zero_lt_one.trans_le hn1
  have hflat : rectangularMiddleDimension a n * rectangularMiddleDimension b n ≤
      generalRectangularRankSequence F a b c n :=
    matrixMultiplication_rank_lower_X (K := F) (rectangularMiddleDimension_pos c hn)
      (rank_spec _)
  calc
    (n : ℝ) ^ (a + b) = (n : ℝ) ^ a * (n : ℝ) ^ b := Real.rpow_add hnpos a b
    _ ≤ (rectangularMiddleDimension a n : ℝ) * (rectangularMiddleDimension b n : ℝ) :=
      mul_le_mul (rpow_le_rectangularMiddleDimension a n)
        (rpow_le_rectangularMiddleDimension b n) (Real.rpow_nonneg hnpos.le b)
        (Nat.cast_nonneg _)
    _ = ((rectangularMiddleDimension a n * rectangularMiddleDimension b n : ℕ) : ℝ) := by
      push_cast; ring
    _ ≤ (generalRectangularRankSequence F a b c n : ℝ) := by exact_mod_cast hflat

/-- Flattening on the `Y` leg gives `b + c ≤ ω(a,b,c)` (Huang--Pan (2.8), second term). -/
theorem add_le_generalRectangularOmega_YZ (a b c : ℝ) :
    b + c ≤ generalRectangularOmega F a b c := by
  have h := add_le_generalRectangularOmega_XY F b c a
  rwa [generalRectangularOmega_cycle F b c a] at h

/-- Flattening on the `Z` leg gives `c + a ≤ ω(a,b,c)` (Huang--Pan (2.8), third term). -/
theorem add_le_generalRectangularOmega_ZX (a b c : ℝ) :
    c + a ≤ generalRectangularOmega F a b c := by
  have h := add_le_generalRectangularOmega_XY F c a b
  rwa [generalRectangularOmega_cycle F c a b, generalRectangularOmega_cycle F b c a] at h

/-- **Huang--Pan (2.8)** (§2, p. 262), the information lower bound

`max(a+b, b+c, c+a) ≤ ω(a,b,c)`,

over a field.  There is no hypothesis on the exponents: even for negative ones each leg dimension
is at least `1` at positive `n`, so the concise flattenings still apply. -/
theorem max_le_generalRectangularOmega (a b c : ℝ) :
    max (a + b) (max (b + c) (c + a)) ≤ generalRectangularOmega F a b c :=
  max_le (add_le_generalRectangularOmega_XY F a b c)
    (max_le (add_le_generalRectangularOmega_YZ F a b c)
      (add_le_generalRectangularOmega_ZX F a b c))

/-- **Huang--Pan (2.8) in the normalized slice**: `max(t+1, 1+r, r+t) ≤ ω(t, 1, r)`. -/
theorem max_le_rectangularOmegaThree (t r : ℝ) :
    max (t + 1) (max (1 + r) (r + t)) ≤ rectangularOmegaThree F t r :=
  max_le_generalRectangularOmega F t 1 r

/-- The binding constraint for the first parameter: `t + 1 ≤ ω(t, 1, r)`. -/
theorem add_one_le_rectangularOmegaThree_left (t r : ℝ) :
    t + 1 ≤ rectangularOmegaThree F t r :=
  add_le_generalRectangularOmega_XY F t 1 r

/-- The binding constraint for the second parameter: `1 + r ≤ ω(t, 1, r)`. -/
theorem one_add_le_rectangularOmegaThree_right (t r : ℝ) :
    1 + r ≤ rectangularOmegaThree F t r :=
  add_le_generalRectangularOmega_YZ F t 1 r

/-- **A negative result, recorded deliberately.**  The first branch of Huang--Pan Theorem 8.1,
`ω(t, 1, r) ≤ r + 1`, is *false* whenever `r < t`, over any field: the information bound (2.8)
gives `ω(t, 1, r) ≥ 1 + t > 1 + r`.  So the hypothesis `1 ≤ r` in
`rectangularOmegaThree_le_add_one_of_eq_two` — Huang--Pan's standing `r > 1 > t > 0` in §8.3 — is
not an artefact of the proof: any weakening allowing `r < t ≤ α` would be inconsistent. -/
theorem lt_rectangularOmegaThree_of_lt {t r : ℝ} (h : r < t) :
    r + 1 < rectangularOmegaThree F t r :=
  lt_of_lt_of_le (by linarith) (add_one_le_rectangularOmegaThree_left F t r)

end FieldLowerBound

/-! ## Theorem 8.1 at the dual exponent `α`, and an exact three-parameter value -/

section FieldHuangPan

variable (F : Type u) [Field F]

/-- **Huang--Pan Theorem 8.1, first branch at the classical witness** (§8.3, (8.2), p. 281): for
`t ≤ α` and `r ≥ 1`,

`ω(t, 1, r) ≤ r + 1`.

Over a field the interval is closed at `α` because the supremum defining `α` is attained
(`rectangularOmega_rectangularAlpha`), which is what `rectangularOmega_huangPan_eq_two`
records. -/
theorem rectangularOmegaThree_le_huangPan_low {t r : ℝ}
    (ht : t ≤ rectangularAlpha F) (hr : 1 ≤ r) :
    rectangularOmegaThree F t r ≤ r + 1 :=
  rectangularOmegaThree_le_add_one_of_eq_two F (rectangularOmega_huangPan_eq_two F ht) hr

/-- **Huang--Pan Theorem 8.1, second branch at the classical witness** (§8.3, (8.2) and (8.3),
pp. 281--283): for `α < 1`, `α ≤ t ≤ 1` and `r ≥ 1`,

`ω(t, 1, r) ≤ (r·(1 - α) + (1 - t) + (ω - 1)·(t - α)) / (1 - α)`,

which is Huang--Pan's function `g(r, α < t ≤ 1)` of (8.3).  With
`Examples/CoppersmithRectangular1982.lean`'s `α ≥ 2 log 2/(5 log 5) > 0.1722` this is a
nonvacuous statement, and at `t = α` it degenerates to the first branch `r + 1`. -/
theorem rectangularOmegaThree_le_huangPan_high (hα : rectangularAlpha F < 1) {t r : ℝ}
    (hle : rectangularAlpha F ≤ t) (ht1 : t ≤ 1) (hr : 1 ≤ r) :
    rectangularOmegaThree F t r ≤
      (r * (1 - rectangularAlpha F) + (1 - t) +
        (omega F - 1) * (t - rectangularAlpha F)) / (1 - rectangularAlpha F) :=
  rectangularOmegaThree_le_interpolation_of_eq_two F (rectangularAlpha_nonneg F) hα
    (rectangularOmega_rectangularAlpha F) hle ht1 hr

/-- **The client: an exact three-parameter value.**  Over a field, for every `r ≥ 1`,

`ω(α, 1, r) = r + 1`.

The upper bound is Theorem 8.1's first branch at `t = α`; the lower bound is the flattening term
`1 + r` of (2.8), which dominates the other two terms `α + 1` and `r + α` because `α ≤ 1 ≤ r`.
This is a genuine three-parameter statement: it is not `ω(κ) = 2` for any `κ`, and by
`Examples/CoppersmithRectangular1982.lean` the point `α` is a nonzero — in fact irrational —
first coordinate. -/
theorem rectangularOmegaThree_rectangularAlpha {r : ℝ} (hr : 1 ≤ r) :
    rectangularOmegaThree F (rectangularAlpha F) r = r + 1 :=
  le_antisymm (rectangularOmegaThree_le_huangPan_low F le_rfl hr)
    (by
      have h := one_add_le_rectangularOmegaThree_right F (rectangularAlpha F) r
      linarith)

/-- The client at `r = 1`: over a field, `ω(α, 1, 1) = 2`.  Equivalently, an `n^α × n` by
`n × n` product costs `n^(2 + ε)`; this is `ω(α) = 2` transported to the third leg, and the
smallest instance of `rectangularOmegaThree_rectangularAlpha`. -/
theorem rectangularOmegaThree_rectangularAlpha_one :
    rectangularOmegaThree F (rectangularAlpha F) 1 = 2 := by
  have h := rectangularOmegaThree_rectangularAlpha F (r := 1) le_rfl
  linarith

end FieldHuangPan

end AlgebraicComplexity
