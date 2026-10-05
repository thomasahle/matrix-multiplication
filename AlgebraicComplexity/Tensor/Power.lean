/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Tensor.BorderRank
import Mathlib.LinearAlgebra.TensorPower.Basic

/-!
# Tensor powers

The ambient space on each leg of the `n`th power is Mathlib's canonical `TensorPower`. Products
of powers are transported through `TensorPower.mulEquiv`, so downstream results do not depend on
an arbitrary parenthesization of iterated binary tensor products. The file also proves transport,
restriction, degeneration, rank, and border-rank laws for these canonical powers.
-/

namespace AlgebraicComplexity.Tensor

universe u v w

variable {K : Type u} [CommSemiring K]
variable {V : Leg → Type v}
variable [∀ i, AddCommMonoid (V i)] [∀ i, Module K (V i)]
variable {W : Leg → Type w}
variable [∀ i, AddCommMonoid (W i)] [∀ i, Module K (W i)]

/-- The leg spaces of the `n`th tensor power. -/
abbrev PowerSpace (K : Type u) [CommSemiring K] (V : Leg → Type v)
    [∀ i, AddCommMonoid (V i)] [∀ i, Module K (V i)] (n : ℕ) (c : Leg) :=
  TensorPower K n (V c)

/-- Canonically concatenate two tensor powers on one leg. -/
def powerMulEquiv (n m : ℕ) (c : Leg) :
    TensorProduct K (PowerSpace K V n c) (PowerSpace K V m c) ≃ₗ[K]
      PowerSpace K V (n + m) c :=
  TensorPower.mulEquiv

/-- Multiply two three-legged tensors whose corresponding legs are tensor powers. -/
def powerMul (n m : ℕ)
    (T : Tensor3 K (PowerSpace K V n))
    (S : Tensor3 K (PowerSpace K V m)) :
    Tensor3 K (PowerSpace K V (n + m)) :=
  map (fun c ↦ (powerMulEquiv (K := K) (V := V) n m c).toLinearMap) (external T S)

/-- Multiplying the zero tensor on the left gives the zero tensor. -/
@[simp] theorem powerMul_zero_left (n m : ℕ)
    (S : Tensor3 K (PowerSpace K V m)) :
    powerMul n m (0 : Tensor3 K (PowerSpace K V n)) S = 0 := by
  simp [powerMul]

/-- Multiplying by the zero tensor on the right gives the zero tensor. -/
@[simp] theorem powerMul_zero_right (n m : ℕ)
    (T : Tensor3 K (PowerSpace K V n)) :
    powerMul n m T (0 : Tensor3 K (PowerSpace K V m)) = 0 := by
  simp [powerMul]

/-- Canonical multiplication of tensor powers is additive in the left factor. -/
theorem powerMul_add_left (n m : ℕ)
    (T₁ T₂ : Tensor3 K (PowerSpace K V n))
    (S : Tensor3 K (PowerSpace K V m)) :
    powerMul n m (T₁ + T₂) S = powerMul n m T₁ S + powerMul n m T₂ S := by
  unfold powerMul
  rw [external_add_left]
  exact LinearMap.map_add _ _ _

/-- Canonical multiplication of tensor powers is additive in the right factor. -/
theorem powerMul_add_right (n m : ℕ)
    (T : Tensor3 K (PowerSpace K V n))
    (S₁ S₂ : Tensor3 K (PowerSpace K V m)) :
    powerMul n m T (S₁ + S₂) = powerMul n m T S₁ + powerMul n m T S₂ := by
  unfold powerMul
  rw [external_add_right]
  exact LinearMap.map_add _ _ _

/-- Scalars pull out of the left factor of a canonical tensor-power multiplication. -/
theorem powerMul_smul_left (n m : ℕ) (a : K)
    (T : Tensor3 K (PowerSpace K V n))
    (S : Tensor3 K (PowerSpace K V m)) :
    powerMul n m (a • T) S = a • powerMul n m T S := by
  unfold powerMul
  rw [external_smul_left]
  exact LinearMap.map_smul _ _ _

/-- Scalars pull out of the right factor of a canonical tensor-power multiplication. -/
theorem powerMul_smul_right (n m : ℕ) (a : K)
    (T : Tensor3 K (PowerSpace K V n))
    (S : Tensor3 K (PowerSpace K V m)) :
    powerMul n m T (a • S) = a • powerMul n m T S := by
  unfold powerMul
  rw [external_smul_right]
  exact LinearMap.map_smul _ _ _

/-- Canonical multiplication of tensor powers distributes over two finite sums. -/
theorem powerMul_sum_sum {I J : Type*} [Fintype I] [Fintype J] (n m : ℕ)
    (T : I → Tensor3 K (PowerSpace K V n))
    (S : J → Tensor3 K (PowerSpace K V m)) :
    powerMul n m (∑ i, T i) (∑ j, S j) =
      ∑ i, ∑ j, powerMul n m (T i) (S j) := by
  unfold powerMul
  rw [external_sum_sum, map_sum]
  simp_rw [map_sum]

/-- The canonical identification of a first tensor power with its underlying module. -/
def powerOneEquiv (c : Leg) : PowerSpace K V 1 c ≃ₗ[K] V c :=
  PiTensorProduct.subsingletonEquiv 0

/-- Regard an ordinary tensor as a tensor with first-power leg spaces. -/
def powerOne (T : Tensor3 K V) : Tensor3 K (PowerSpace K V 1) :=
  map (fun c ↦ (powerOneEquiv (K := K) (V := V) c).symm.toLinearMap) T

/-- Transport to first-power spaces commutes with finite sums. -/
theorem powerOne_sum {I : Type*} [Fintype I] (T : I → Tensor3 K V) :
    powerOne (∑ i, T i) = ∑ i, powerOne (T i) := by
  unfold powerOne
  rw [map_sum]

/-- The scalar unit in the zeroth tensor power of each leg. -/
def powerUnit : ∀ c, PowerSpace K V 0 c :=
  fun c ↦ PiTensorProduct.tprod K (@Fin.elim0 (V c))

/-- Canonical equivalence between zeroth powers, independent of their underlying modules. -/
noncomputable def powerZeroEquiv (c : Leg) :
    PowerSpace K V 0 c ≃ₗ[K] PowerSpace K W 0 c :=
  PiTensorProduct.congr (fun i : Fin 0 ↦ Fin.elim0 i)

/-- The external tensor power of a three-legged tensor. -/
def power (T : Tensor3 K V) : (n : ℕ) → Tensor3 K (PowerSpace K V n)
  | 0 => pure (K := K) (powerUnit (K := K) (V := V))
  | n + 1 => powerMul n 1 (power T n) (powerOne T)

/-- The zeroth tensor power is the pure tensor of scalar units, by definition. -/
@[simp] theorem power_zero (T : Tensor3 K V) :
    power T 0 = pure (K := K) (powerUnit (K := K) (V := V)) := rfl

/-- The `(n + 1)`st tensor power is the `n`th power multiplied by one more first-power copy,
by definition. -/
@[simp] theorem power_succ (T : Tensor3 K V) (n : ℕ) :
    power T (n + 1) = powerMul n 1 (power T n) (powerOne T) := rfl

/-- The canonical first tensor power is exactly the transported first-power tensor. -/
theorem power_one_eq_powerOne (T : Tensor3 K V) : power T 1 = powerOne T := by
  change powerMul 0 1 (power T 0) (powerOne T) = powerOne T
  unfold powerMul
  rw [power_zero]
  refine PiTensorProduct.induction_on (powerOne T) ?_ ?_
  · intro a x
    rw [external_smul_right, LinearMap.map_smul]
    congr 1
    rw [external_pure, map_pure]
    congr 1
    funext c
    simpa [powerMulEquiv, powerUnit, TensorPower.gMul_def,
      TensorPower.gOne_def] using
      (TensorPower.one_mul (R := K) (M := V c) (x c))
  · intro S₁ S₂ h₁ h₂
    simp only [LinearMap.map_add, h₁, h₂]

namespace Isomorphic

/-- Zeroth powers of tensors with arbitrary ambient leg spaces are canonically isomorphic. -/
theorem powerZero (T : Tensor3 K V) (S : Tensor3 K W) :
    Isomorphic (Tensor.power T 0) (Tensor.power S 0) := by
  refine ⟨powerZeroEquiv (K := K) (V := V) (W := W), ?_⟩
  simp only [power_zero, PiTensorProduct.congr_tprod, powerZeroEquiv]
  congr 1
  funext c
  unfold powerUnit
  rw [PiTensorProduct.congr_tprod]
  congr 1
  funext i
  exact Fin.elim0 i

/-- Transporting a tensor to first-power leg spaces is a legwise isomorphism.  The source is the
ordinary tensor `T` and the target is `Tensor.powerOne T`; the leg equivalences are the inverses
of the canonical identifications `powerOneEquiv`. -/
theorem powerOneTransport (T : Tensor3 K V) :
    Isomorphic T (Tensor.powerOne T) :=
  Isomorphic.map T (fun c ↦ (powerOneEquiv (K := K) (V := V) c).symm)

/-- Canonical multiplication of tensor powers is a legwise isomorphism away from the external
product.  The source is `Tensor.external T S`, whose legs are binary tensor products of powers,
and the target is `Tensor.powerMul n m T S`, whose legs are single `(n + m)`th powers; the leg
equivalences are the concatenations `powerMulEquiv`. -/
theorem external_powerMul (n m : ℕ)
    (T : Tensor3 K (PowerSpace K V n)) (S : Tensor3 K (PowerSpace K V m)) :
    Isomorphic (Tensor.external T S) (Tensor.powerMul n m T S) :=
  Isomorphic.map _ (powerMulEquiv (K := K) (V := V) n m)

/-- Isomorphic tensors remain isomorphic after transport to their canonical first-power spaces.

Proof sketch: conjugate the given legwise isomorphism by the canonical transports from each tensor
to its first-power representation. -/
theorem powerOne {T : Tensor3 K V} {S : Tensor3 K W} (h : Isomorphic T S) :
    Isomorphic (Tensor.powerOne T) (Tensor.powerOne S) :=
  (Isomorphic.powerOneTransport T).symm.trans
    (h.trans (Isomorphic.powerOneTransport S))

/-- Legwise tensor isomorphism is preserved by every canonical tensor power.

Proof sketch: induct on the exponent.  Zeroth powers are canonically isomorphic.  At a successor,
take the external product of the induction hypothesis with the first-power isomorphism and
conjugate by the canonical `powerMul` equivalences on the source and target. -/
theorem power {T : Tensor3 K V} {S : Tensor3 K W} (h : Isomorphic T S) (n : ℕ) :
    Isomorphic (Tensor.power T n) (Tensor.power S n) := by
  induction n with
  | zero => exact Isomorphic.powerZero T S
  | succ n ih =>
      exact (Isomorphic.external_powerMul n 1 (Tensor.power T n)
          (Tensor.powerOne T)).symm.trans
        ((ih.external h.powerOne).trans
          (Isomorphic.external_powerMul n 1 (Tensor.power S n)
            (Tensor.powerOne S)))

end Isomorphic

namespace Restricts

/-- Exact restrictions remain exact after transporting both tensors to first-power spaces.

Proof sketch: conjugate the given restriction by the transport isomorphisms
`Isomorphic.powerOneTransport`, running the source transport backwards. -/
theorem powerOne {T : Tensor3 K V} {S : Tensor3 K W} (h : Restricts T S) :
    Restricts (Tensor.powerOne T) (Tensor.powerOne S) :=
  (Isomorphic.powerOneTransport T).symm.restricts.trans
    (h.trans (Isomorphic.powerOneTransport S).restricts)

/-- Exact restrictions are compatible with every canonical tensor power.

Proof sketch: induct on `n`.  The zeroth powers are isomorphic for arbitrary ambient spaces, and
the inductive step restricts the external product of the `n`th powers with the first powers and
then conjugates by `Isomorphic.external_powerMul` on both sides. -/
theorem power {T : Tensor3 K V} {S : Tensor3 K W} (h : Restricts T S) (n : ℕ) :
    Restricts (Tensor.power T n) (Tensor.power S n) := by
  induction n with
  | zero => exact (Isomorphic.powerZero T S).restricts
  | succ n ih =>
      have hExternal := ih.external h.powerOne
      exact (Isomorphic.external_powerMul n 1 (Tensor.power T n)
          (Tensor.powerOne T)).symm.restricts.trans
        (hExternal.trans (Isomorphic.external_powerMul n 1 (Tensor.power S n)
          (Tensor.powerOne S)).restricts)

end Restricts

namespace PolynomialDegenerates

/-- Polynomial degenerations remain polynomial after transporting to first-power spaces.

Proof sketch: the transport isomorphisms `Isomorphic.powerOneTransport` are exact restrictions,
hence degree-zero degenerations; compose them around the given degeneration. -/
theorem powerOne {T : Tensor3 K V} {S : Tensor3 K W} (h : PolynomialDegenerates T S) :
    PolynomialDegenerates (Tensor.powerOne T) (Tensor.powerOne S) :=
  (PolynomialDegenerates.of_restricts
      (Isomorphic.powerOneTransport T).symm.restricts).trans
    (h.trans (PolynomialDegenerates.of_restricts
      (Isomorphic.powerOneTransport S).restricts))

/-- Polynomial degenerations are compatible with every canonical tensor power.

Proof sketch: induct on `n`.  The zeroth powers are isomorphic for arbitrary ambient spaces, and
the inductive step degenerates the external product of the `n`th powers with the first powers and
then conjugates by the exact isomorphisms `Isomorphic.external_powerMul` on both sides. -/
theorem power {T : Tensor3 K V} {S : Tensor3 K W}
    (h : PolynomialDegenerates T S) (n : ℕ) :
    PolynomialDegenerates (Tensor.power T n) (Tensor.power S n) := by
  induction n with
  | zero =>
      exact PolynomialDegenerates.of_restricts (Isomorphic.powerZero T S).restricts
  | succ n ih =>
      have hExternal := ih.external h.powerOne
      exact (PolynomialDegenerates.of_restricts (Isomorphic.external_powerMul n 1
            (Tensor.power T n) (Tensor.powerOne T)).symm.restricts).trans
        (hExternal.trans (PolynomialDegenerates.of_restricts
          (Isomorphic.external_powerMul n 1
            (Tensor.power S n) (Tensor.powerOne S)).restricts))

end PolynomialDegenerates

namespace PolynomialDegeneratesAt

/-- Degree-aware polynomial degenerations remain degree-aware after transporting both tensors to
their canonical first-power spaces. -/
theorem powerOne {d : ℕ} {T : Tensor3 K V} {S : Tensor3 K W}
    (h : PolynomialDegeneratesAt d T S) :
    PolynomialDegeneratesAt d (Tensor.powerOne T) (Tensor.powerOne S) := by
  have hpre : PolynomialDegeneratesAt 0 (Tensor.powerOne T) T :=
    PolynomialDegeneratesAt.of_restricts (Isomorphic.powerOneTransport T).symm.restricts
  have hpost : PolynomialDegeneratesAt 0 S (Tensor.powerOne S) :=
    PolynomialDegeneratesAt.of_restricts (Isomorphic.powerOneTransport S).restricts
  simpa using (hpre.trans h).trans hpost

/-- The `n`th canonical tensor power of a degree-`d` degeneration has displayed leading degree
`n * d`. -/
theorem power {d : ℕ} {T : Tensor3 K V} {S : Tensor3 K W}
    (h : PolynomialDegeneratesAt d T S) (n : ℕ) :
    PolynomialDegeneratesAt (n * d) (Tensor.power T n) (Tensor.power S n) := by
  induction n with
  | zero =>
      simpa using PolynomialDegeneratesAt.of_restricts (Isomorphic.powerZero T S).restricts
  | succ n ih =>
      have hExternal := ih.external h.powerOne
      have hpre := PolynomialDegeneratesAt.of_restricts
        (Isomorphic.external_powerMul n 1
          (Tensor.power T n) (Tensor.powerOne T)).symm.restricts
      have hpost := PolynomialDegeneratesAt.of_restricts
        (Isomorphic.external_powerMul n 1
          (Tensor.power S n) (Tensor.powerOne S)).restricts
      simpa [Nat.succ_mul] using (hpre.trans hExternal).trans hpost

end PolynomialDegeneratesAt

namespace RankLE

/-- Rank upper bounds multiply under canonical multiplication of tensor powers. -/
theorem powerMul {n m r s : ℕ}
    {T : Tensor3 K (PowerSpace K V n)}
    {S : Tensor3 K (PowerSpace K V m)}
    (hT : RankLE r T) (hS : RankLE s S) :
    RankLE (r * s) (Tensor.powerMul n m T S) := by
  exact (hT.external hS).map
    (fun c ↦ (powerMulEquiv (K := K) (V := V) n m c).toLinearMap)

/-- Transporting a tensor to first-power leg spaces preserves a rank certificate. -/
theorem powerOne {r : ℕ} {T : Tensor3 K V} (h : RankLE r T) :
    RankLE r (Tensor.powerOne T) := by
  exact h.map (fun c ↦ (powerOneEquiv (K := K) (V := V) c).symm.toLinearMap)

/-- A rank-`r` certificate tensors to a rank-`r^n` certificate for every power. -/
theorem power {r : ℕ} {T : Tensor3 K V} (h : RankLE r T) (n : ℕ) :
    RankLE (r ^ n) (Tensor.power T n) := by
  induction n with
  | zero =>
      simpa using RankLE.pure_tensor (K := K)
        (V := PowerSpace K V 0) (powerUnit (K := K) (V := V))
  | succ n ih =>
      simpa [pow_succ] using ih.powerMul h.powerOne

end RankLE

namespace BorderRankLE

/-- Border-rank upper bounds multiply under canonical multiplication of tensor powers. -/
theorem powerMul {n m r s : ℕ}
    {T : Tensor3 K (PowerSpace K V n)}
    {S : Tensor3 K (PowerSpace K V m)}
    (hT : BorderRankLE r T) (hS : BorderRankLE s S) :
    BorderRankLE (r * s) (Tensor.powerMul n m T S) := by
  exact BorderRankLE.map (hT.external hS)
    (fun c ↦ (powerMulEquiv (K := K) (V := V) n m c).toLinearMap)

/-- Transporting a tensor to first-power leg spaces preserves a border-rank certificate. -/
theorem powerOne {r : ℕ} {T : Tensor3 K V} (h : BorderRankLE r T) :
    BorderRankLE r (Tensor.powerOne T) := by
  exact h.map (fun c ↦ (powerOneEquiv (K := K) (V := V) c).symm.toLinearMap)

/-- A border-rank-`r` certificate tensors to a border-rank-`r^n` certificate for every power. -/
theorem power {r : ℕ} {T : Tensor3 K V} (h : BorderRankLE r T) (n : ℕ) :
    BorderRankLE (r ^ n) (Tensor.power T n) := by
  induction n with
  | zero =>
      exact (RankLE.pure_tensor (K := K)
        (V := PowerSpace K V 0) (powerUnit (K := K) (V := V))).toBorderRankLE
  | succ n ih =>
      simpa [pow_succ] using ih.powerMul h.powerOne

end BorderRankLE

/-- Ordinary tensor rank is submultiplicative under canonical powers:
`rank (power T n) ≤ rank T ^ n`. -/
theorem rank_power_le (T : Tensor3 K V) (n : ℕ) :
    rank (power T n) ≤ rank T ^ n :=
  rank_le_iff.mpr ((rank_spec T).power n)

/-- Border rank is submultiplicative under canonical powers:
`borderRank (power T n) ≤ borderRank T ^ n`. -/
theorem borderRank_power_le (T : Tensor3 K V) (n : ℕ) :
    borderRank (power T n) ≤ borderRank T ^ n :=
  borderRank_le_iff.mpr ((borderRank_spec T).power n)

/-- **The first tensor power has the border rank of the tensor itself.**

Proof sketch: `power_one_eq_powerOne` identifies the first power with the canonical first-power
transport, and border rank is invariant under the resulting legwise linear isomorphism. -/
theorem borderRank_power_one (T : Tensor3 K V) :
    borderRank (power T 1) = borderRank T := by
  rw [power_one_eq_powerOne]
  exact borderRank_isomorphic (Isomorphic.powerOneTransport T).symm

end AlgebraicComplexity.Tensor
