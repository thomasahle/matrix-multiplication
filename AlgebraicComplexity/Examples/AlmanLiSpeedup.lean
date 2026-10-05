/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.AsymptoticRank
import AlgebraicComplexity.Tensor.PolynomialInterpolation

/-!
# A duality-free three-direction asymptotic-rank speedup

Alman and Li ([AlmanLi2026], Proposition 4.4) prove: if a tensor `T` admits the three
degenerations

```text
T ⊴ ⟨r⟩ ⊕ ⟨s,1,1⟩,   T ⊴ ⟨r⟩ ⊕ ⟨1,s,1⟩,   T ⊴ ⟨r⟩ ⊕ ⟨1,1,s⟩,
```

then `R̃(T) ≤ r + s^(ω/3)`.  Their proof is a *Strassen calculus* argument: it evaluates a point
`φ` of the asymptotic spectrum on all three relations, uses `min_i s^{θ_i} ≤ s^{(θ₁+θ₂+θ₃)/3}
≤ s^{ω/3}`, and returns to asymptotic rank through **Strassen's duality theorem**
`R̃(T) = max_φ φ(T)`.

This file proves what the *primal* rules of the asymptotic-rank calculus give, namely

```text
R̃(T)³ ≤ r³ + 3·r²·s + 3·r·s² + s^ω.
```

## Why the primal bound is weaker, and why that is unavoidable

Cubing the published bound gives `(r + s^{ω/3})³ = r³ + 3r²s^{ω/3} + 3rs^{2ω/3} + s^ω`, so the
theorem below is genuinely weaker in the three middle groups of terms; it is still a strict
improvement on the bound `R̃(T) ≤ r + s` that a single relation gives, because `s^ω < s³`.

The gap is not an artifact of the proof.  Tensoring the three relations gives
`T^{⊗3} ⊴ A₁ ⊠ A₂ ⊠ A₃` with `Aᵢ = ⟨r⟩ ⊕ Mᵢ`, and the primal calculus can only bound
`R̃(A₁ ⊠ A₂ ⊠ A₃)` by the sum of the asymptotic ranks of the eight expansion terms.  Seven of
those terms contain at most two of the three matrix-multiplication factors, and their asymptotic
ranks are genuinely as large as the estimate says: by [Str88, Proposition 4.3] the asymptotic rank
of `⟨m,n,p⟩` is `max{m^{θ₁} n^{θ₂} p^{θ₃} : (θ₁,θ₂,θ₃) ∈ Δ_MM}`, so for instance
`R̃⟨s,1,1⟩ = s`, not `s^{ω/3}` (conciseness alone forces `R̃⟨1,1,s⟩ ≥ s`; see the module
documentation of `MatrixMultiplication/AsymptoticRank.lean`).  Consequently
`R̃(A₁ ⊠ A₂ ⊠ A₃) = max_φ ∏ᵢ (r + s^{θᵢ})`, whose maximizing spectral point spends the budget
`θ₁ + θ₂ + θ₃ ≤ ω` unevenly, whereas the published bound needs the *minimum* over the three
directions at each single spectral point.  A product of the three relations averages where the
duality argument minimizes, and no rearrangement of the primal expansion recovers the difference.

Reaching `r + s^{ω/3}` therefore requires Strassen's duality theorem, which this repository does
not have; see `DESIGN.md` and the roadmap entry for `Tensor/StrassenDuality.lean`.

## References

* J. Alman and B. Li, *Asymptotic rank speedup theorems, revisited*, arXiv:2605.21738
  ([AlmanLi2026]), Proposition 4.4.
* V. Strassen, *The asymptotic spectrum of tensors*, J. reine angew. Math. 384 (1988), 102--152
  ([Strassen1988]), Proposition 4.3 and Theorem 3.8.
-/

namespace AlgebraicComplexity

open Tensor

universe u v w

variable {K : Type u} [CommSemiring K]

/-- Three separate asymptotic-rank bounds multiply along a right-associated triple external
product. -/
private theorem asymptoticRank_external3_le_of_le
    {V₁ V₂ V₃ : Leg → Type*}
    [∀ c, AddCommMonoid (V₁ c)] [∀ c, Module K (V₁ c)]
    [∀ c, AddCommMonoid (V₂ c)] [∀ c, Module K (V₂ c)]
    [∀ c, AddCommMonoid (V₃ c)] [∀ c, Module K (V₃ c)]
    {X : Tensor3 K V₁} {Y : Tensor3 K V₂} {Z : Tensor3 K V₃} {a b c : ℝ}
    (hX : asymptoticRank X ≤ a) (hY : asymptoticRank Y ≤ b) (hZ : asymptoticRank Z ≤ c)
    (ha : 0 ≤ a) (hb : 0 ≤ b) :
    asymptoticRank (external X (external Y Z)) ≤ a * b * c := by
  refine (asymptoticRank_external3_le X Y Z).trans ?_
  exact mul_le_mul (mul_le_mul hX hY (asymptoticRank_nonneg Y) ha) hZ
    (asymptoticRank_nonneg Z) (mul_nonneg ha hb)

/-- **A duality-free three-direction speedup theorem.**

If `T` is a degeneration of `U ⊕ ⟨s,1,1⟩`, of `U ⊕ ⟨1,s,1⟩`, and of `U ⊕ ⟨1,1,s⟩` for one tensor
`U` of asymptotic rank at most `r`, then

```text
R̃(T)³ ≤ r³ + 3·r²·s + 3·r·s² + s^ω.
```

The hypothesis `1 ≤ R(T^{⊗j})` says that no tensor power of `T` vanishes; it is what makes
`R̃(T)³ ≤ R̃(T^{⊗3})` available.

Proof sketch: multiplying the three degenerations gives
`T^{⊗3} ⊴ (U ⊕ ⟨s,1,1⟩) ⊠ (U ⊕ ⟨1,s,1⟩) ⊠ (U ⊕ ⟨1,1,s⟩)`.  Monotonicity of asymptotic rank under
degeneration and `asymptoticRank_external3_directSum_le` reduce the right-hand side to the eight
expansion terms.  Seven of them are bounded by products of `r` and `s` through
submultiplicativity, using `R⟨s,1,1⟩ ≤ s`; the eighth is the product of the three
matrix-multiplication factors, which is `⟨s,s,s⟩` and contributes `s^ω` by
`asymptoticRank_matrixMultiplication_le_rpow_omega`.

Compared with [AlmanLi2026, Proposition 4.4], which uses Strassen duality to obtain
`R̃(T) ≤ r + s^(ω/3)`, the three middle groups of terms carry `s`, `s²` instead of `s^(ω/3)`,
`s^(2ω/3)`; see the module documentation. -/
theorem asymptoticRank_pow_three_le_of_matrixMultiplication_directSum_degenerations
    {V : Leg → Type v} [∀ c, AddCommMonoid (V c)] [∀ c, Module K (V c)]
    {V' : Leg → Type w} [∀ c, AddCommMonoid (V' c)] [∀ c, Module K (V' c)]
    {T : Tensor3 K V} {U : Tensor3 K V'} {r : ℝ} {s : ℕ}
    (hs : 1 ≤ s)
    (hone : ∀ j, 1 ≤ rank (power T j))
    (hU : asymptoticRank U ≤ r)
    (h₁ : PolynomialDegenerates (directSum U (matrixMultiplication (K := K) s 1 1)) T)
    (h₂ : PolynomialDegenerates (directSum U (matrixMultiplication (K := K) 1 s 1)) T)
    (h₃ : PolynomialDegenerates (directSum U (matrixMultiplication (K := K) 1 1 s)) T) :
    asymptoticRank T ^ 3 ≤
      r ^ 3 + 3 * r ^ 2 * (s : ℝ) + 3 * r * (s : ℝ) ^ 2 + (s : ℝ) ^ omega K := by
  have hr0 : 0 ≤ r := le_trans (asymptoticRank_nonneg U) hU
  have hs0 : (0 : ℝ) ≤ (s : ℝ) := by positivity
  have hmm : ∀ a b c : ℕ,
      asymptoticRank (matrixMultiplication (K := K) a b c) ≤ ((a * b * c : ℕ) : ℝ) := by
    intro a b c
    refine (asymptoticRank_le_rank _).trans ?_
    exact_mod_cast rank_le_iff.mpr (matrixMultiplication_rankLE a b c)
  have hM₁ : asymptoticRank (matrixMultiplication (K := K) s 1 1) ≤ (s : ℝ) := by
    simpa using hmm s 1 1
  have hM₂ : asymptoticRank (matrixMultiplication (K := K) 1 s 1) ≤ (s : ℝ) := by
    simpa using hmm 1 s 1
  have hM₃ : asymptoticRank (matrixMultiplication (K := K) 1 1 s) ≤ (s : ℝ) := by
    simpa using hmm 1 1 s
  have hiso3 : Isomorphic (Tensor.power T 3) (external (external T T) T) :=
    (isomorphic_external_power T 2 1).symm.trans
      ((((isomorphic_external_power T 1 1).symm.trans
        ((Isomorphic.power_one T).external (Isomorphic.power_one T))).external
          (Isomorphic.power_one T)))
  have hstep : asymptoticRank (Tensor.power T 3) ≤
      asymptoticRank (external
        (external (directSum U (matrixMultiplication (K := K) s 1 1))
          (directSum U (matrixMultiplication (K := K) 1 s 1)))
        (directSum U (matrixMultiplication (K := K) 1 1 s))) := by
    rw [asymptoticRank_isomorphic hiso3]
    exact asymptoticRank_polynomialDegenerates_le ((h₁.external h₂).external h₃)
  have hleaf8 : asymptoticRank (external (matrixMultiplication (K := K) s 1 1)
      (external (matrixMultiplication (K := K) 1 1 s)
        (matrixMultiplication (K := K) 1 s 1))) ≤ (s : ℝ) ^ omega K := by
    have hiso : Isomorphic
        (external (matrixMultiplication (K := K) s 1 1)
          (external (matrixMultiplication (K := K) 1 1 s)
            (matrixMultiplication (K := K) 1 s 1)))
        (matrixMultiplication (K := K) s s s) :=
      (((Isomorphic.refl (matrixMultiplication (K := K) s 1 1)).external
          (Tensor.Isomorphic.matrixMultiplication_external 1 1 s 1 s 1)).trans
        (Tensor.Isomorphic.matrixMultiplication_external s 1 1 (1 * 1) (1 * s) (s * 1))).trans
        (Tensor.Isomorphic.matrixMultiplication_congr (by ring) (by ring) (by ring))
    rw [asymptoticRank_isomorphic hiso]
    exact asymptoticRank_matrixMultiplication_le_rpow_omega hs
  refine (asymptoticRank_pow_le_asymptoticRank_power T hone 3).trans
    (hstep.trans ((asymptoticRank_external3_directSum_le U
      (matrixMultiplication (K := K) s 1 1) U (matrixMultiplication (K := K) 1 s 1) U
      (matrixMultiplication (K := K) 1 1 s)).trans ?_))
  refine le_trans (add_le_add
    (add_le_add
      (add_le_add (asymptoticRank_external3_le_of_le hU hU hU hr0 hr0)
        (asymptoticRank_external3_le_of_le hM₁ hU hU hs0 hr0))
      (add_le_add (asymptoticRank_external3_le_of_le hU hU hM₂ hr0 hr0)
        (asymptoticRank_external3_le_of_le hM₁ hU hM₂ hs0 hr0)))
    (add_le_add
      (add_le_add (asymptoticRank_external3_le_of_le hU hM₃ hU hr0 hs0)
        (asymptoticRank_external3_le_of_le hM₁ hM₃ hU hs0 hs0))
      (add_le_add (asymptoticRank_external3_le_of_le hU hM₃ hM₂ hr0 hs0) hleaf8))) ?_
  exact le_of_eq (by ring)

end AlgebraicComplexity
