/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Tensor.AsymptoticRank
import AlgebraicComplexity.Tensor.DirectSumPowerCoherence
import AlgebraicComplexity.Tensor.PowerZeroUnit

/-!
# The calculus of asymptotic tensor rank

`Tensor/AsymptoticRank.lean` defines `asymptoticRank` and proves the laws that need only one
tensor: monotonicity under restriction and the inequality `R̃(T)^n ≤ R̃(T^{⊗n})`.  This file adds
the structural laws that relate the asymptotic ranks of *different* tensors, namely

* `asymptoticRank_external_le`: `R̃(T ⊠ S) ≤ R̃(T) · R̃(S)`;
* `asymptoticRank_directSum_le`: `R̃(T ⊕ S) ≤ R̃(T) + R̃(S)`.

The one-tensor power law `asymptoticRank_power_eq` lives with the definition in
`Tensor/AsymptoticRank.lean`.

Together with monotonicity under degeneration
(`asymptoticRank_polynomialDegenerates_le` of `Tensor/PolynomialInterpolation.lean`) these are the
rules by which a degeneration into a direct sum of simpler tensors is turned into an asymptotic
rank estimate.

## Implementation notes

`Growth.ExponentialBound` tolerates a fixed multiplicative constant, which makes the three laws
above provable without ever extracting an `n`th root: an admissible base for the ranks of the
powers of the compound tensor is assembled from admissible bases for the constituents, and the
resulting inequality between bases is pushed to the infima by continuity
(`le_of_forall_gt_le`).

The tensor-only Pascal coherence used by the direct-sum proof lives in
`Tensor/DirectSumPowerCoherence.lean`, shared with constructive finite extraction.  This module
adds only the rank estimates and limiting argument.

The direct-sum law is the only one that needs a genuine combinatorial expansion.  Rather than
decomposing `(A ⊕ B)^{⊗n}` into its `2^n` word blocks, the proof carries the mixed prefix
`A^{⊗k} ⊠ B^{⊗m}` through an induction on `n`
(`rank_external_power_directSum_le`); at each step distributivity splits one factor `A ⊕ B` and
the two halves are absorbed into the prefix.  The binomial coefficients never appear explicitly:
they are produced by the algebraic identity `α^k β^m (α + β)^{n+1}
= α^{k+1} β^m (α + β)^n + α^k β^{m+1} (α + β)^n`.

## References

* V. Strassen, *Relative bilinear complexity and matrix multiplication*, J. reine angew. Math.
  375/376 (1987), 406--443.
* J. Alman and B. Li, *Asymptotic rank speedup theorems, revisited*, arXiv:2605.21738
  ([AlmanLi2026]), §4.
-/

namespace AlgebraicComplexity.Tensor

open Growth Filter Topology

universe u v w z

variable {K : Type u} [CommSemiring K]
variable {U : Leg → Type z} [∀ c, AddCommMonoid (U c)] [∀ c, Module K (U c)]
variable {V : Leg → Type v} [∀ c, AddCommMonoid (V c)] [∀ c, Module K (V c)]
variable {W : Leg → Type w} [∀ c, AddCommMonoid (W c)] [∀ c, Module K (W c)]

/-! ## Structural isomorphisms of external products

Commutativity below, together with the last-two-factor transposition and the middle-four
interchange imported from `Tensor/Product.lean`, is what makes the canonical tensor powers of a
product and of a direct sum computable.  The unit laws for the zeroth power come from
`Tensor/PowerZeroUnit.lean`. -/

namespace Isomorphic

/-- Swapping the two factors of an external product is a legwise isomorphism. -/
theorem external_comm (T : Tensor3 K V) (S : Tensor3 K W) :
    Isomorphic (Tensor.external T S) (Tensor.external S T) := by
  refine ⟨fun c ↦ TensorProduct.comm K (V c) (W c), ?_⟩
  simpa [PiTensorProduct.congr] using map_external_comm T S

/-- Canonical tensor powers distribute over external products:
`(T ⊠ S)^{⊗n} ≅ T^{⊗n} ⊠ S^{⊗n}`.

Proof sketch: induct on `n`.  At a successor, split off one factor on both sides and apply the
middle-four interchange to move the new `T` next to `T^{⊗n}` and the new `S` next to `S^{⊗n}`. -/
theorem power_external (T : Tensor3 K V) (S : Tensor3 K W) (n : ℕ) :
    Isomorphic (Tensor.power (Tensor.external T S) n)
      (Tensor.external (Tensor.power T n) (Tensor.power S n)) := by
  induction n with
  | zero =>
      exact ((Isomorphic.powerZero (Tensor.external T S) S).trans
        (powerZeroExternalLeft T (Tensor.power S 0)).symm)
  | succ n ih =>
      refine ((isomorphic_external_power (Tensor.external T S) n 1).symm.trans ?_)
      refine (ih.external (power_one (Tensor.external T S))).trans ?_
      refine (external_interchange (Tensor.power T n) (Tensor.power S n) T S).trans ?_
      exact (((Isomorphic.refl (Tensor.power T n)).external (power_one T).symm).trans
          (isomorphic_external_power T n 1)).external
        (((Isomorphic.refl (Tensor.power S n)).external (power_one S).symm).trans
          (isomorphic_external_power S n 1))

end Isomorphic

/-! ## The asymptotic rank of an external product -/

/-- **Submultiplicativity of asymptotic rank**, `R̃(T ⊠ S) ≤ R̃(T) · R̃(S)`.

Proof sketch: `Isomorphic.power_external` turns rank submultiplicativity on each power into the
pointwise bound `R((T ⊠ S)^{⊗n}) ≤ R(T^{⊗n}) · R(S^{⊗n})`, and `Growth.ExponentialBound.mul`
multiplies two admissible bases.  Both bases are then decreased to the corresponding asymptotic
ranks. -/
theorem asymptoticRank_external_le (T : Tensor3 K V) (S : Tensor3 K W) :
    asymptoticRank (external T S) ≤ asymptoticRank T * asymptoticRank S := by
  have key : ∀ α, asymptoticRank T < α → ∀ β, asymptoticRank S < β →
      asymptoticRank (external T S) ≤ α * β := by
    intro α hα β hβ
    refine asymptoticRank_le (ExponentialBound.of_le ?_ (ExponentialBound.mul
      (rankPower_exponentialBound_of_asymptoticRank_lt hα)
      (rankPower_exponentialBound_of_asymptoticRank_lt hβ)))
    intro n
    show rank (power (external T S) n) ≤ rank (power T n) * rank (power S n)
    rw [rank_isomorphic (Isomorphic.power_external T S n)]
    exact rank_external_le _ _
  refine le_of_forall_gt_le (g := fun x : ℝ ↦ x * asymptoticRank S) (by fun_prop) ?_
  intro α hα
  exact le_of_forall_gt_le (g := fun x : ℝ ↦ α * x) (by fun_prop) (key α hα)

/-! ## The asymptotic rank of a direct sum -/


/-- **The binomial estimate for powers of a direct sum.**  If `α` and `β` are admissible
exponential bases for the ranks of the powers of `A` and of `B`, with constants `CA` and `CB`,
then `α + β` is an admissible base for the ranks of the powers of `A ⊕ B`, with constant
`CA · CB` --- uniformly in a mixed prefix `A^{⊗k} ⊠ B^{⊗m}`.

Proof sketch: induct on `n`, keeping `k` and `m` universally quantified.  At a successor,
`Isomorphic.external_power_succ` exposes one factor `A ⊕ B`, distributivity splits it, and the two
halves are absorbed into the prefix by `Isomorphic.externalPrefix_absorb_left` and
`Isomorphic.externalPrefix_absorb_right`.  The induction hypothesis then produces
`α^{k+1} β^m (α+β)^n + α^k β^{m+1} (α+β)^n = α^k β^m (α+β)^{n+1}`. -/
theorem rank_external_power_directSum_le
    (A : Tensor3 K V) (B : Tensor3 K W) {α β CA CB : ℝ}
    (hα : 0 ≤ α) (hCA : 0 ≤ CA)
    (hA : ∀ k, ((rank (power A k) : ℕ) : ℝ) ≤ CA * α ^ k)
    (hB : ∀ m, ((rank (power B m) : ℕ) : ℝ) ≤ CB * β ^ m)
    (n k m : ℕ) :
    ((rank (external (external (power A k) (power B m))
        (power (directSum A B) n)) : ℕ) : ℝ)
      ≤ CA * CB * α ^ k * β ^ m * (α + β) ^ n := by
  induction n generalizing k m with
  | zero =>
      rw [rank_isomorphic (Isomorphic.powerZeroExternalRight
        (external (power A k) (power B m)) (directSum A B))]
      calc ((rank (external (power A k) (power B m)) : ℕ) : ℝ)
          ≤ ((rank (power A k) * rank (power B m) : ℕ) : ℝ) := by
            exact_mod_cast rank_external_le (power A k) (power B m)
        _ = ((rank (power A k) : ℕ) : ℝ) * ((rank (power B m) : ℕ) : ℝ) := by push_cast; ring
        _ ≤ (CA * α ^ k) * (CB * β ^ m) :=
            mul_le_mul (hA k) (hB m) (by positivity) (by positivity)
        _ = CA * CB * α ^ k * β ^ m * (α + β) ^ 0 := by ring
  | succ n ih =>
      have hsum := rank_directSum_le
        (external (external (external (power A k) (power B m))
          (power (directSum A B) n)) A)
        (external (external (external (power A k) (power B m))
          (power (directSum A B) n)) B)
      rw [rank_isomorphic (Isomorphic.externalPrefix_absorb_left A B (directSum A B) k m n),
        rank_isomorphic (Isomorphic.externalPrefix_absorb_right A B (directSum A B) k m n)] at hsum
      rw [rank_isomorphic (Isomorphic.external_power_succ
          (external (power A k) (power B m)) (directSum A B) n),
        rank_isomorphic (Isomorphic.external_directSum
          (external (external (power A k) (power B m)) (power (directSum A B) n)) A B)]
      have hcast : ((rank (directSum
              (external (external (external (power A k) (power B m))
                (power (directSum A B) n)) A)
              (external (external (external (power A k) (power B m))
                (power (directSum A B) n)) B)) : ℕ) : ℝ)
            ≤ ((rank (external (external (power A (k + 1)) (power B m))
                (power (directSum A B) n)) : ℕ) : ℝ) +
              ((rank (external (external (power A k) (power B (m + 1)))
                (power (directSum A B) n)) : ℕ) : ℝ) := by
        exact_mod_cast hsum
      have hring : CA * CB * α ^ (k + 1) * β ^ m * (α + β) ^ n +
          CA * CB * α ^ k * β ^ (m + 1) * (α + β) ^ n =
          CA * CB * α ^ k * β ^ m * (α + β) ^ (n + 1) := by ring
      linarith [ih (k + 1) m, ih k (m + 1)]

/-- **Subadditivity of asymptotic rank**, `R̃(A ⊕ B) ≤ R̃(A) + R̃(B)`.

Proof sketch: `rank_external_power_directSum_le` at the empty prefix `k = m = 0` shows that
`α + β` is an admissible exponential base for the ranks of the powers of `A ⊕ B` whenever `α` and
`β` are admissible for `A` and `B`; both bases are then decreased to the corresponding asymptotic
ranks. -/
theorem asymptoticRank_directSum_le (A : Tensor3 K V) (B : Tensor3 K W) :
    asymptoticRank (directSum A B) ≤ asymptoticRank A + asymptoticRank B := by
  have key : ∀ α, asymptoticRank A < α → ∀ β, asymptoticRank B < β →
      asymptoticRank (directSum A B) ≤ α + β := by
    intro α hα β hβ
    obtain ⟨hα0, CA, hCA, hAb⟩ := rankPower_exponentialBound_of_asymptoticRank_lt hα
    obtain ⟨hβ0, CB, hCB, hBb⟩ := rankPower_exponentialBound_of_asymptoticRank_lt hβ
    refine asymptoticRank_le ⟨by positivity, CA * CB, by positivity, fun n ↦ ?_⟩
    have hiso : Isomorphic
        (external (external (power A 0) (power B 0)) (power (directSum A B) n))
        (power (directSum A B) n) :=
      ((Isomorphic.powerZeroExternalLeft A (power B 0)).external
          (Isomorphic.refl (power (directSum A B) n))).trans
        (Isomorphic.powerZeroExternalLeft B (power (directSum A B) n))
    have h := rank_external_power_directSum_le A B hα0 hCA.le hAb hBb n 0 0
    rw [rank_isomorphic hiso] at h
    simpa [rankPowerSequence] using h
  refine le_of_forall_gt_le (g := fun x : ℝ ↦ x + asymptoticRank B) (by fun_prop) ?_
  intro α hα
  exact le_of_forall_gt_le (g := fun x : ℝ ↦ α + x) (by fun_prop) (key α hα)

/-! ## Distributing a direct-sum factor of a product

The two rules below are the form in which the direct-sum law is used when a tensor is known only
through a degeneration into a direct sum: the factor to be expanded may sit on either side of an
external product. -/

/-- Expanding a direct-sum factor on the right of an external product. -/
theorem asymptoticRank_external_directSum_le (X : Tensor3 K U) (A : Tensor3 K V)
    (B : Tensor3 K W) :
    asymptoticRank (external X (directSum A B)) ≤
      asymptoticRank (external X A) + asymptoticRank (external X B) :=
  (asymptoticRank_isomorphic (Isomorphic.external_directSum X A B)).le.trans
    (asymptoticRank_directSum_le _ _)

/-- Expanding a direct-sum factor on the left of an external product. -/
theorem asymptoticRank_directSum_external_le (A : Tensor3 K V) (B : Tensor3 K W)
    (X : Tensor3 K U) :
    asymptoticRank (external (directSum A B) X) ≤
      asymptoticRank (external A X) + asymptoticRank (external B X) := by
  rw [asymptoticRank_isomorphic (Isomorphic.external_comm (directSum A B) X),
    asymptoticRank_isomorphic (Isomorphic.external_comm A X),
    asymptoticRank_isomorphic (Isomorphic.external_comm B X)]
  exact asymptoticRank_external_directSum_le X A B

/-! ## Triple products and the expansion of a triple product of direct sums

The Strassen-calculus estimate for a tensor known through a degeneration into a direct sum uses
one product of three direct sums.  Expanding it needs the two distributivity rules above together
with the associator and the transposition of the last two factors. -/

/-- Submultiplicativity of asymptotic rank for a right-associated triple external product. -/
theorem asymptoticRank_external3_le (X : Tensor3 K U) (Y : Tensor3 K V) (Z : Tensor3 K W) :
    asymptoticRank (external X (external Y Z)) ≤
      asymptoticRank X * asymptoticRank Y * asymptoticRank Z := by
  refine (asymptoticRank_external_le X (external Y Z)).trans ?_
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left (asymptoticRank_external_le Y Z) (asymptoticRank_nonneg X)

/-- Expanding the leftmost factor of a left-associated triple product, after reassociating. -/
private theorem asymptoticRank_external_assoc_directSum_le
    {V₁ W₁ V₂ V₃ : Leg → Type*}
    [∀ c, AddCommMonoid (V₁ c)] [∀ c, Module K (V₁ c)]
    [∀ c, AddCommMonoid (W₁ c)] [∀ c, Module K (W₁ c)]
    [∀ c, AddCommMonoid (V₂ c)] [∀ c, Module K (V₂ c)]
    [∀ c, AddCommMonoid (V₃ c)] [∀ c, Module K (V₃ c)]
    (U₁ : Tensor3 K V₁) (M₁ : Tensor3 K W₁) (Y : Tensor3 K V₂) (Z : Tensor3 K V₃) :
    asymptoticRank (external (external (directSum U₁ M₁) Y) Z) ≤
      asymptoticRank (external U₁ (external Y Z)) +
        asymptoticRank (external M₁ (external Y Z)) := by
  rw [asymptoticRank_isomorphic (Isomorphic.external_assoc (directSum U₁ M₁) Y Z)]
  exact asymptoticRank_directSum_external_le U₁ M₁ (external Y Z)

/-- Expanding the two direct-sum factors of a left-associated triple product whose last factor is
arbitrary. -/
private theorem asymptoticRank_external2_directSum_le
    {V₁ W₁ V₂ W₂ V₃ : Leg → Type*}
    [∀ c, AddCommMonoid (V₁ c)] [∀ c, Module K (V₁ c)]
    [∀ c, AddCommMonoid (W₁ c)] [∀ c, Module K (W₁ c)]
    [∀ c, AddCommMonoid (V₂ c)] [∀ c, Module K (V₂ c)]
    [∀ c, AddCommMonoid (W₂ c)] [∀ c, Module K (W₂ c)]
    [∀ c, AddCommMonoid (V₃ c)] [∀ c, Module K (V₃ c)]
    (U₁ : Tensor3 K V₁) (M₁ : Tensor3 K W₁) (U₂ : Tensor3 K V₂) (M₂ : Tensor3 K W₂)
    (Z : Tensor3 K V₃) :
    asymptoticRank (external (external (directSum U₁ M₁) (directSum U₂ M₂)) Z) ≤
      (asymptoticRank (external U₁ (external Z U₂)) +
          asymptoticRank (external M₁ (external Z U₂))) +
        (asymptoticRank (external U₁ (external Z M₂)) +
          asymptoticRank (external M₁ (external Z M₂))) := by
  rw [asymptoticRank_isomorphic
    (Isomorphic.external_swapRight (directSum U₁ M₁) (directSum U₂ M₂) Z)]
  refine (asymptoticRank_external_directSum_le
    (external (directSum U₁ M₁) Z) U₂ M₂).trans ?_
  exact add_le_add (asymptoticRank_external_assoc_directSum_le U₁ M₁ Z U₂)
    (asymptoticRank_external_assoc_directSum_le U₁ M₁ Z M₂)

/-- **The eight-term expansion of a triple external product of binary direct sums.**

`(U₁ ⊕ M₁) ⊠ (U₂ ⊕ M₂) ⊠ (U₃ ⊕ M₃)` has asymptotic rank at most the sum of the asymptotic ranks
of the eight products `c₁ ⊠ (c₃ ⊠ c₂)` with `cᵢ ∈ {Uᵢ, Mᵢ}`.  The factors are listed in the order
in which the expansion produces them; asymptotic rank is invariant under reordering, so a client
may permute them freely. -/
theorem asymptoticRank_external3_directSum_le
    {V₁ W₁ V₂ W₂ V₃ W₃ : Leg → Type*}
    [∀ c, AddCommMonoid (V₁ c)] [∀ c, Module K (V₁ c)]
    [∀ c, AddCommMonoid (W₁ c)] [∀ c, Module K (W₁ c)]
    [∀ c, AddCommMonoid (V₂ c)] [∀ c, Module K (V₂ c)]
    [∀ c, AddCommMonoid (W₂ c)] [∀ c, Module K (W₂ c)]
    [∀ c, AddCommMonoid (V₃ c)] [∀ c, Module K (V₃ c)]
    [∀ c, AddCommMonoid (W₃ c)] [∀ c, Module K (W₃ c)]
    (U₁ : Tensor3 K V₁) (M₁ : Tensor3 K W₁) (U₂ : Tensor3 K V₂) (M₂ : Tensor3 K W₂)
    (U₃ : Tensor3 K V₃) (M₃ : Tensor3 K W₃) :
    asymptoticRank (external (external (directSum U₁ M₁) (directSum U₂ M₂))
        (directSum U₃ M₃)) ≤
      ((asymptoticRank (external U₁ (external U₃ U₂)) +
          asymptoticRank (external M₁ (external U₃ U₂))) +
        (asymptoticRank (external U₁ (external U₃ M₂)) +
          asymptoticRank (external M₁ (external U₃ M₂)))) +
      ((asymptoticRank (external U₁ (external M₃ U₂)) +
          asymptoticRank (external M₁ (external M₃ U₂))) +
        (asymptoticRank (external U₁ (external M₃ M₂)) +
          asymptoticRank (external M₁ (external M₃ M₂)))) :=
  (asymptoticRank_external_directSum_le
      (external (directSum U₁ M₁) (directSum U₂ M₂)) U₃ M₃).trans
    (add_le_add (asymptoticRank_external2_directSum_le U₁ M₁ U₂ M₂ U₃)
      (asymptoticRank_external2_directSum_le U₁ M₁ U₂ M₂ M₃))

end AlgebraicComplexity.Tensor
