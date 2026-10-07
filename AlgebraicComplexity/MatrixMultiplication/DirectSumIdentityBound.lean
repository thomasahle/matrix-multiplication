/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.AsymptoticSum
import AlgebraicComplexity.MatrixMultiplication.DirectSumIdentity

/-!
# The exponent bounds of the direct-sum identity

`MatrixMultiplication/DirectSumIdentity.lean` proves [AlmanLi2026, Theorem 7.3]:

```text
⟨N·M⟩ ⊕ ⟨p,1,q⟩   ⊵   ⟨N,1,M⟩ ⊕ ⊕_{α,β} ⟨1, n α · m β, 1⟩,     N = ∑ (n α + 1),  M = ∑ (m β + 1).
```

The source has rank at most `N·M + p·q`, so the target has border rank at most `N·M + p·q`, and
the asymptotic sum inequality turns that into an inequality for `ω`:

```text
(N·M)^(ω/3) + ∑_{α,β} (n α · m β)^(ω/3)  ≤  N·M + p·q.
```

At `p = q = 1` this is Schönhage's inequality `((n+1)(m+1))^(ω/3) + (nm)^(ω/3) ≤ (n+1)(m+1) + 1`
for **all** `n, m ≥ 1`.  `Examples/Schonhage.lean` proves the instance `n = m = 2` from an
explicit ten-term certificate and reads off `ω < 2.6`; the instance `n = m = 3`,
`16^(ω/3) + 9^(ω/3) ≤ 17`, is the one Schönhage optimized, and gives `ω < 2.55` here
(`omega_lt_of_schonhage_four`; the exact root is `2.5479…`).

## Main results

* `rankLE_dsSource`, `borderRankLE_directSum_slices`: the rank of the source and the border rank
  of the target.
* `restricts_directSum_slices_option`: the target as one indexed direct sum of
  matrix-multiplication tensors, the shape the asymptotic sum inequality consumes.
* `directSumIdentity_asymptoticSum`: the inequality for `ω`.
* `schonhage_asymptoticSum_general`: Schönhage's inequality for all `n, m ≥ 1`.
* `omega_lt_of_schonhage_four`: `ω < 2.55`.

## References

* J. Alman and B. Li, *Asymptotic rank speedup theorems, revisited*, arXiv:2605.21738
  ([AlmanLi2026]), Theorem 7.3, p. 29.
* A. Schönhage, *Partial and total matrix multiplication*, SIAM J. Comput. 10 (1981)
  ([Schonhage1981]), Lemma 6.1 and the bound `ω < 2.548` derived from it.
-/

namespace AlgebraicComplexity

open Tensor Module

universe u

section Bound

variable (K : Type u) [Field K] {p q : ℕ} (n : Fin p → ℕ) (m : Fin q → ℕ)

/-- The source `⟨N·M⟩ ⊕ ⟨p,1,q⟩` in standard coordinates is a sum of `N·M + p·q` pure tensors. -/
theorem rankLE_dsSource :
    RankLE ((∑ a, (n a + 1)) * (∑ b, (m b + 1)) + p * q) (dsSource K n m) := by
  classical
  have h1 := RankLE.fintype_sum_pure (K := K) (V := CoordinateSpace K (DSIndex n m))
    (fun e : DSRow n × DSCol m ↦ ofLegs (V := CoordinateSpace K (DSIndex n m))
      (Pi.single (Sum.inl e) 1 : (DSRow n × DSCol m) ⊕ Fin p → K)
      (Pi.single (Sum.inl e) 1 : (DSRow n × DSCol m) ⊕ Fin q → K)
      (Pi.single (Sum.inl e) 1 : (DSRow n × DSCol m) ⊕ (Fin q × Fin p) → K))
  have h2 := RankLE.fintype_sum_pure (K := K) (V := CoordinateSpace K (DSIndex n m))
    (fun ab : Fin p × Fin q ↦ ofLegs (V := CoordinateSpace K (DSIndex n m))
      (Pi.single (Sum.inr ab.1) 1 : (DSRow n × DSCol m) ⊕ Fin p → K)
      (Pi.single (Sum.inr ab.2) 1 : (DSRow n × DSCol m) ⊕ Fin q → K)
      (Pi.single (Sum.inr (ab.2, ab.1)) 1 : (DSRow n × DSCol m) ⊕ (Fin q × Fin p) → K))
  have h := h1.add h2
  have hcard : Fintype.card (DSRow n × DSCol m) + Fintype.card (Fin p × Fin q) =
      (∑ a, (n a + 1)) * (∑ b, (m b + 1)) + p * q := by
    simp [Fintype.card_sigma]
  rw [hcard, Fintype.sum_prod_type (f := fun ab : Fin p × Fin q ↦ _)] at h
  exact h

/-- The target of the direct-sum identity has border rank at most `N·M + p·q`. -/
theorem borderRankLE_directSum_slices :
    BorderRankLE ((∑ a, (n a + 1)) * (∑ b, (m b + 1)) + p * q)
      (Tensor.directSum (matrixMultiplication (K := K) (∑ a, (n a + 1)) 1 (∑ b, (m b + 1)))
        (matrixMultiplicationDirectSum K (fun _ : Fin p × Fin q ↦ 1) (fun ab ↦ n ab.1 * m ab.2)
          (fun _ ↦ 1))) :=
  (rankLE_dsSource K n m).border_of_polynomialDegenerates (polynomialDegenerates_dsSource K n m)

/-- First dimensions of the target, indexed by `none` for `⟨N,1,M⟩` and `some (α, β)` for the
slice `⟨1, n α · m β, 1⟩`. -/
abbrev dsOptM {p : ℕ} (q : ℕ) (n : Fin p → ℕ) : Option (Fin p × Fin q) → ℕ
  | none => ∑ a, (n a + 1)
  | some _ => 1

/-- Middle dimensions of the target. -/
abbrev dsOptN : Option (Fin p × Fin q) → ℕ
  | none => 1
  | some ab => n ab.1 * m ab.2

/-- Last dimensions of the target. -/
abbrev dsOptP (p : ℕ) {q : ℕ} (m : Fin q → ℕ) : Option (Fin p × Fin q) → ℕ
  | none => ∑ b, (m b + 1)
  | some _ => 1

/-- The target `⟨N,1,M⟩ ⊕ ⊕_{α,β} ⟨1, n α · m β, 1⟩`, a binary direct sum whose second summand
is an indexed direct sum, restricts onto the single indexed direct sum over
`Option (Fin p × Fin q)`. -/
theorem restricts_directSum_slices_option :
    Restricts
      (Tensor.directSum (matrixMultiplication (K := K) (∑ a, (n a + 1)) 1 (∑ b, (m b + 1)))
        (matrixMultiplicationDirectSum K (fun _ : Fin p × Fin q ↦ 1) (fun ab ↦ n ab.1 * m ab.2)
          (fun _ ↦ 1)))
      (matrixMultiplicationDirectSum K (dsOptM q n) (dsOptN n m) (dsOptP p m)) := by
  classical
  let VO : Option (Fin p × Fin q) → Leg → Type u :=
    fun o ↦ MMSpace K (dsOptM q n o) (dsOptN n m o) (dsOptP p m o)
  let FN : ∀ c, MMSpace K (∑ a, (n a + 1)) 1 (∑ b, (m b + 1)) c →ₗ[K]
      IndexedDirectSumSpace K VO c := fun c ↦ indexedInclude (K := K) (V := VO) none c
  let FS := indexedFoldMap (K := K)
    (V := fun ab : Fin p × Fin q ↦ MMSpace K 1 (n ab.1 * m ab.2) 1)
    (fun ab c ↦ indexedInclude (K := K) (V := VO) (some ab) c)
  refine ⟨fun c ↦ LinearMap.coprod (FN c) (FS c), ?_⟩
  have hL : ∀ X : Tensor3 K (MMSpace K (∑ a, (n a + 1)) 1 (∑ b, (m b + 1))),
      Tensor.map (fun c ↦ LinearMap.coprod (FN c) (FS c))
        (Tensor.map (Tensor.includeLeft (K := K)
          (W := MMDirectSumSpace K (fun _ : Fin p × Fin q ↦ 1) (fun ab ↦ n ab.1 * m ab.2)
            (fun _ ↦ 1))) X) = Tensor.map FN X := by
    intro X
    rw [← LinearMap.comp_apply, ← Tensor.map_comp]
    refine congrArg (fun G ↦ Tensor.map G X) (funext fun c ↦ LinearMap.ext fun x ↦ ?_)
    simp
  have hR : ∀ X : Tensor3 K (MMDirectSumSpace K (fun _ : Fin p × Fin q ↦ 1)
        (fun ab ↦ n ab.1 * m ab.2) (fun _ ↦ 1)),
      Tensor.map (fun c ↦ LinearMap.coprod (FN c) (FS c))
        (Tensor.map (Tensor.includeRight (K := K)
          (V := MMSpace K (∑ a, (n a + 1)) 1 (∑ b, (m b + 1)))) X) = Tensor.map FS X := by
    intro X
    rw [← LinearMap.comp_apply, ← Tensor.map_comp]
    refine congrArg (fun G ↦ Tensor.map G X) (funext fun c ↦ LinearMap.ext fun x ↦ ?_)
    simp
  rw [Tensor.directSum, map_add, hL, hR, matrixMultiplicationDirectSum]
  simp only [FS]
  rw [map_indexedFoldMap_indexedDirectSum, matrixMultiplicationDirectSum, indexedDirectSum,
    Fintype.sum_option]

/-- **The exponent inequality of the direct-sum identity.**

For block sizes `n α + 1 ≥ 2` and `m β + 1 ≥ 2`, with `N = ∑ (n α + 1)` and `M = ∑ (m β + 1)`,

```text
(N·M)^(ω/3) + ∑_{α,β} (n α · m β)^(ω/3)  ≤  N·M + p·q.
```
-/
theorem directSumIdentity_asymptoticSum (hp : 0 < p) (hq : 0 < q)
    (hn : ∀ a, 0 < n a) (hm : ∀ b, 0 < m b) :
    ((((∑ a, (n a + 1)) * ∑ b, (m b + 1) : ℕ) : ℝ)) ^ (omega K / 3) +
        ∑ a, ∑ b, ((n a * m b : ℕ) : ℝ) ^ (omega K / 3) ≤
      (((∑ a, (n a + 1)) * (∑ b, (m b + 1)) + p * q : ℕ) : ℝ) := by
  have hN : 0 < ∑ a, (n a + 1) :=
    Finset.sum_pos (fun a _ ↦ Nat.succ_pos _) ⟨⟨0, hp⟩, Finset.mem_univ _⟩
  have hM : 0 < ∑ b, (m b + 1) :=
    Finset.sum_pos (fun b _ ↦ Nat.succ_pos _) ⟨⟨0, hq⟩, Finset.mem_univ _⟩
  have h := asymptoticSum_le_of_borderRankLE (ι := Option (Fin p × Fin q)) K
    (dsOptM q n) (dsOptN n m) (dsOptP p m) (borderRankLE_directSum_slices K n m)
    (fun o ↦ by cases o <;> simp [dsOptM, hN])
    (fun o ↦ by
      cases o with
      | none => simp [dsOptN]
      | some ab => simpa [dsOptN] using Nat.mul_pos (hn ab.1) (hm ab.2))
    (fun o ↦ by cases o <;> simp [dsOptP, hM])
    (PolynomialDegenerates.of_restricts (restricts_directSum_slices_option K n m))
  simp only [asymptoticSum, matrixMultiplicationVolumePowerSum, matrixMultiplicationVolume,
    Fintype.sum_option, Fintype.sum_prod_type, mul_one, one_mul] at h
  exact h

/-- **Schönhage's inequality for all sizes** ([Schonhage1981], from Lemma 6.1): for `n, m ≥ 1`,

```text
((n+1)(m+1))^(ω/3) + (n·m)^(ω/3)  ≤  (n+1)(m+1) + 1.
```
-/
theorem schonhage_asymptoticSum_general {n m : ℕ} (hn : 0 < n) (hm : 0 < m) :
    (((n + 1) * (m + 1) : ℕ) : ℝ) ^ (omega K / 3) + ((n * m : ℕ) : ℝ) ^ (omega K / 3) ≤
      (((n + 1) * (m + 1) + 1 : ℕ) : ℝ) := by
  have h := directSumIdentity_asymptoticSum K (p := 1) (q := 1) (fun _ ↦ n) (fun _ ↦ m)
    one_pos one_pos (fun _ ↦ hn) (fun _ ↦ hm)
  simpa using h

private theorem sixteen_rpow_gt : (211 / 20 : ℝ) < (16 : ℝ) ^ (17 / 20 : ℝ) := by
  have h : (211 / 20 : ℝ) < (((16 : ℝ) ^ 17) ^ ((20 : ℝ)⁻¹)) := by
    rw [Real.lt_rpow_inv_iff_of_pos (by norm_num) (by positivity) (by norm_num)]
    norm_num
  convert h using 1
  rw [← Real.rpow_natCast]
  rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 16)]
  congr 2

private theorem nine_rpow_gt : (647 / 100 : ℝ) < (9 : ℝ) ^ (17 / 20 : ℝ) := by
  have h : (647 / 100 : ℝ) < (((9 : ℝ) ^ 17) ^ ((20 : ℝ)⁻¹)) := by
    rw [Real.lt_rpow_inv_iff_of_pos (by norm_num) (by positivity) (by norm_num)]
    norm_num
  convert h using 1
  rw [← Real.rpow_natCast]
  rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 9)]
  congr 2

/-- **`ω < 2.55`** from Schönhage's `⟨4,1,4⟩ ⊕ ⟨1,9,1⟩`, of border rank at most `17`
([Schonhage1981]; the exact root of `16^(ω/3) + 9^(ω/3) = 17` is `2.5479…`). -/
theorem omega_lt_of_schonhage_four : omega K < 51 / 20 := by
  by_contra hnot
  have hexponent : (17 / 20 : ℝ) ≤ omega K / 3 := by
    have : (51 / 20 : ℝ) ≤ omega K := le_of_not_gt hnot
    linarith
  have h16 : (16 : ℝ) ^ (17 / 20 : ℝ) ≤ (16 : ℝ) ^ (omega K / 3) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) hexponent
  have h9 : (9 : ℝ) ^ (17 / 20 : ℝ) ≤ (9 : ℝ) ^ (omega K / 3) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) hexponent
  have hbound := schonhage_asymptoticSum_general K (n := 3) (m := 3) (by norm_num) (by norm_num)
  norm_num at hbound
  linarith [sixteen_rpow_gt, nine_rpow_gt]

end Bound

end AlgebraicComplexity
