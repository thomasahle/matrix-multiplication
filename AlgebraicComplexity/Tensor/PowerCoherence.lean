/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Tensor.Power

/-!
# Coherence of canonical tensor powers

`Tensor.power (Tensor.power T m) n` and `Tensor.power T (n * m)` have canonically equivalent
leg spaces.  This module constructs the equivalence recursively from Mathlib's
`TensorPower.mulEquiv`; no bases or finite-dimensional hypotheses are used.

The accompanying coherence theorem identifies the two tensor elements themselves.  It is kept
separate from `Power.lean` because proving the coherence laws requires substantially more imports
and elaboration than merely defining powers.

The additive companion, `isomorphic_external_power : T^{⊗m} ⊠ T^{⊗n} ≅ T^{⊗(m+n)}`, is proved at
the end of the file; it is what makes a numerical invariant multiplicative along the power sequence.
-/

namespace AlgebraicComplexity.Tensor

universe u v

variable {K : Type u} [CommSemiring K]
variable {V : Leg → Type v}
variable [∀ c, AddCommMonoid (V c)] [∀ c, Module K (V c)]

/-- Reassociate the degree of a tensor power along a natural-number equality. -/
def powerCastEquiv {a b : ℕ} (h : a = b) (c : Leg) :
    PowerSpace K V a c ≃ₗ[K] PowerSpace K V b c :=
  TensorPower.cast K (V c) h

@[simp] theorem powerMul_pure {n m : ℕ}
    (x : ∀ c, PowerSpace K V n c) (y : ∀ c, PowerSpace K V m c) :
    powerMul n m (pure (K := K) x) (pure (K := K) y) =
      pure (K := K) (fun c ↦
        powerMulEquiv (K := K) (V := V) n m c (x c ⊗ₜ[K] y c)) := by
  simp [powerMul]

/-- Mapping by a composite family of leg equivalences is successive mapping. -/
theorem map_linearEquiv_trans
    {A B C : Leg → Type*}
    [∀ c, AddCommMonoid (A c)] [∀ c, Module K (A c)]
    [∀ c, AddCommMonoid (B c)] [∀ c, Module K (B c)]
    [∀ c, AddCommMonoid (C c)] [∀ c, Module K (C c)]
    (f : ∀ c, A c ≃ₗ[K] B c) (g : ∀ c, B c ≃ₗ[K] C c)
    (T : Tensor3 K A) :
    map (fun c ↦ ((f c).trans (g c)).toLinearMap) T =
      map (fun c ↦ (g c).toLinearMap) (map (fun c ↦ (f c).toLinearMap) T) := by
  change map (fun c ↦ (g c).toLinearMap ∘ₗ (f c).toLinearMap) T = _
  exact LinearMap.congr_fun (PiTensorProduct.map_comp
    (fun c ↦ (g c).toLinearMap) (fun c ↦ (f c).toLinearMap)) T

/-- Unpacking immediately after canonical power multiplication recovers the external product. -/
theorem map_powerMulEquiv_symm_powerMul {n m : ℕ}
    (T : Tensor3 K (PowerSpace K V n))
    (S : Tensor3 K (PowerSpace K V m)) :
    map (fun c ↦
      (powerMulEquiv (K := K) (V := V) n m c).symm.toLinearMap)
        (powerMul n m T S) = external T S := by
  simpa [powerMul, PiTensorProduct.congr] using
    (LinearEquiv.symm_apply_apply
      (PiTensorProduct.congr (powerMulEquiv (K := K) (V := V) n m))
      (external T S))

/-- Mapping a first-power transport back to its underlying leg spaces is the identity. -/
theorem map_powerOneEquiv_powerOne (T : Tensor3 K V) :
    map (fun c ↦ (powerOneEquiv (K := K) (V := V) c).toLinearMap) (powerOne T) = T := by
  simpa [powerOne, PiTensorProduct.congr] using
    (LinearEquiv.apply_symm_apply
      (PiTensorProduct.congr (powerOneEquiv (K := K) (V := V))) T)

/-- The canonical degree-zero tensor is a right unit for `powerMul`, after transporting the
degree along `n + 0 = n`. -/
theorem map_powerMul_powerUnit_right {n : ℕ}
    (T : Tensor3 K (PowerSpace K V n)) :
    map (fun c ↦
      (powerCastEquiv (K := K) (V := V) (Nat.add_zero n) c).toLinearMap)
        (powerMul n 0 T (pure (K := K) (powerUnit (K := K) (V := V)))) = T := by
  refine PiTensorProduct.induction_on T ?_ ?_
  · intro a x
    rw [powerMul_smul_left, LinearMap.map_smul, powerMul_pure, map_pure]
    congr 1
    congr 1
    funext c
    simpa [powerCastEquiv, powerMulEquiv, powerUnit, TensorPower.gMul_def,
      TensorPower.gOne_def] using
      (TensorPower.mul_one (R := K) (M := V c) (x c))
  · intro T₁ T₂ h₁ h₂
    simp only [powerMul_add_left, LinearMap.map_add, h₁, h₂]

/-- Canonical tensor powers commute with transport along equality of their exponents. -/
theorem map_powerCast_power (T : Tensor3 K V) {a b : ℕ} (h : a = b) :
    map (fun c ↦ (powerCastEquiv (K := K) (V := V) h c).toLinearMap) (power T a) =
      power T b := by
  subst b
  simp [powerCastEquiv]

/-- Leg equivalence implementing associativity of three consecutive tensor-power blocks. -/
def powerAssocEquiv (n m r : ℕ) (c : Leg) :
    PowerSpace K V ((n + m) + r) c ≃ₗ[K] PowerSpace K V (n + (m + r)) c :=
  powerCastEquiv (K := K) (V := V) (Nat.add_assoc n m r) c

private theorem map_powerMul_assoc_pure {n m r : ℕ}
    (x : ∀ c, PowerSpace K V n c)
    (y : ∀ c, PowerSpace K V m c)
    (z : ∀ c, PowerSpace K V r c) :
    map (fun c ↦ (powerAssocEquiv (K := K) (V := V) n m r c).toLinearMap)
        (powerMul (n + m) r (powerMul n m (pure (K := K) x) (pure (K := K) y))
          (pure (K := K) z)) =
      powerMul n (m + r) (pure (K := K) x)
        (powerMul m r (pure (K := K) y) (pure (K := K) z)) := by
  simp only [powerMul_pure, map_pure]
  congr 1
  funext c
  simpa [powerAssocEquiv, powerCastEquiv, powerMulEquiv, TensorPower.gMul_def] using
    (TensorPower.mul_assoc (R := K) (M := V c) (x c) (y c) (z c))

/-- `powerMul` is associative up to the canonical equality of its degree indices. -/
theorem map_powerMul_assoc {n m r : ℕ}
    (T : Tensor3 K (PowerSpace K V n))
    (S : Tensor3 K (PowerSpace K V m))
    (U : Tensor3 K (PowerSpace K V r)) :
    map (fun c ↦ (powerAssocEquiv (K := K) (V := V) n m r c).toLinearMap)
        (powerMul (n + m) r (powerMul n m T S) U) =
      powerMul n (m + r) T (powerMul m r S U) := by
  refine PiTensorProduct.induction_on T ?_ ?_
  · intro a x
    refine PiTensorProduct.induction_on S ?_ ?_
    · intro b y
      refine PiTensorProduct.induction_on U ?_ ?_
      · intro d z
        simpa only [powerMul_smul_left, powerMul_smul_right, LinearMap.map_smul,
          smul_smul, mul_assoc, mul_comm, mul_left_comm] using
          congrArg (fun Q ↦ (a * b * d) • Q)
            (map_powerMul_assoc_pure (K := K) (V := V) x y z)
      · intro U₁ U₂ h₁ h₂
        simp only [powerMul_add_right, LinearMap.map_add, h₁, h₂]
    · intro S₁ S₂ h₁ h₂
      simp only [powerMul_add_right, powerMul_add_left, LinearMap.map_add, h₁, h₂]
  · intro T₁ T₂ h₁ h₂
    simp only [powerMul_add_left, LinearMap.map_add, h₁, h₂]

/-- Concatenating the canonical `n`th and `m`th powers gives the canonical `(n + m)`th power. -/
theorem powerMul_power (T : Tensor3 K V) (n m : ℕ) :
    powerMul n m (power T n) (power T m) = power T (n + m) := by
  induction m with
  | zero =>
      simpa [power_zero, powerCastEquiv] using
        (map_powerMul_powerUnit_right (K := K) (V := V) (power T n))
  | succ m ih =>
      have h := map_powerMul_assoc (K := K) (V := V)
        (power T n) (power T m) (powerOne T)
      rw [ih] at h
      calc
        powerMul n (m + 1) (power T n) (power T (m + 1)) =
            powerMul n (m + 1) (power T n)
              (powerMul m 1 (power T m) (powerOne T)) := by rw [power_succ]
        _ = powerMul (n + m) 1 (power T (n + m)) (powerOne T) := by
          simpa [powerAssocEquiv, powerCastEquiv] using h.symm
        _ = power T ((n + m) + 1) := (power_succ T (n + m)).symm
        _ = power T (n + (m + 1)) := rfl

/-- Canonically flatten an outer `n`-fold tensor power of inner `m`-fold tensor powers into an
`(n * m)`-fold tensor power. -/
noncomputable def powerFlattenEquiv (m : ℕ) :
    (n : ℕ) → (c : Leg) →
      PowerSpace K (PowerSpace K V m) n c ≃ₗ[K] PowerSpace K V (n * m) c
  | 0, c =>
      (powerZeroEquiv (K := K) (V := PowerSpace K V m) (W := V) c).trans
        (powerCastEquiv (K := K) (V := V) (Nat.zero_mul m).symm c)
  | n + 1, c =>
      (powerMulEquiv (K := K) (V := PowerSpace K V m) n 1 c).symm.trans
        ((TensorProduct.congr
          (powerFlattenEquiv m n c)
          (powerOneEquiv (K := K) (V := PowerSpace K V m) c)).trans
        ((powerMulEquiv (K := K) (V := V) (n * m) m c).trans
          (powerCastEquiv (K := K) (V := V) (Nat.succ_mul n m).symm c)))

theorem powerFlattenEquiv_zero (m : ℕ) (c : Leg) :
    powerFlattenEquiv (K := K) (V := V) m 0 c =
      (powerZeroEquiv (K := K) (V := PowerSpace K V m) (W := V) c).trans
        (powerCastEquiv (K := K) (V := V) (Nat.zero_mul m).symm c) :=
  rfl

theorem powerFlattenEquiv_succ (m n : ℕ) (c : Leg) :
    powerFlattenEquiv (K := K) (V := V) m (n + 1) c =
      (powerMulEquiv (K := K) (V := PowerSpace K V m) n 1 c).symm.trans
        ((TensorProduct.congr
          (powerFlattenEquiv (K := K) (V := V) m n c)
          (powerOneEquiv (K := K) (V := PowerSpace K V m) c)).trans
        ((powerMulEquiv (K := K) (V := V) (n * m) m c).trans
          (powerCastEquiv (K := K) (V := V) (Nat.succ_mul n m).symm c))) :=
  rfl

/-- Recursive computation rule for flattening a canonical outer multiplication step. -/
theorem map_powerFlattenEquiv_powerMul (m n : ℕ)
    (T : Tensor3 K (PowerSpace K (PowerSpace K V m) n))
    (S : Tensor3 K (PowerSpace K (PowerSpace K V m) 1)) :
    map (fun c ↦ (powerFlattenEquiv (K := K) (V := V) m (n + 1) c).toLinearMap)
        (powerMul n 1 T S) =
      map (fun c ↦
        (powerCastEquiv (K := K) (V := V) (Nat.succ_mul n m).symm c).toLinearMap)
        (powerMul (n * m) m
          (map (fun c ↦
            (powerFlattenEquiv (K := K) (V := V) m n c).toLinearMap) T)
          (map (fun c ↦
            (powerOneEquiv (K := K) (V := PowerSpace K V m) c).toLinearMap) S)) := by
  simp_rw [powerFlattenEquiv_succ]
  rw [map_linearEquiv_trans, map_linearEquiv_trans, map_linearEquiv_trans,
    map_powerMulEquiv_symm_powerMul]
  change
    map (fun c ↦
      (powerCastEquiv (K := K) (V := V) (Nat.succ_mul n m).symm c).toLinearMap)
      (map (fun c ↦
        (powerMulEquiv (K := K) (V := V) (n * m) m c).toLinearMap)
        (map (fun c ↦ TensorProduct.map
          (powerFlattenEquiv (K := K) (V := V) m n c).toLinearMap
          (powerOneEquiv (K := K) (V := PowerSpace K V m) c).toLinearMap)
          (external T S))) = _
  rw [map_external]
  rfl

private theorem map_powerZeroEquiv_power_zero
    {A B : Leg → Type*}
    [∀ c, AddCommMonoid (A c)] [∀ c, Module K (A c)]
    [∀ c, AddCommMonoid (B c)] [∀ c, Module K (B c)]
    (T : Tensor3 K A) (S : Tensor3 K B) :
    map (fun c ↦
      (powerZeroEquiv (K := K) (V := A) (W := B) c).toLinearMap) (power T 0) =
      power S 0 := by
  simp only [power_zero, map_pure]
  congr 1
  funext c
  unfold powerUnit powerZeroEquiv
  change
    PiTensorProduct.congr (fun i : Fin 0 ↦ Fin.elim0 i)
        (PiTensorProduct.tprod K (@Fin.elim0 (A c))) =
      PiTensorProduct.tprod K (@Fin.elim0 (B c))
  rw [PiTensorProduct.congr_tprod]
  congr 1
  funext i
  exact Fin.elim0 i

/-- Flattening carries a power of a power to the single canonical power with product exponent. -/
theorem map_powerFlattenEquiv_power (T : Tensor3 K V) (m n : ℕ) :
    map (fun c ↦ (powerFlattenEquiv (K := K) (V := V) m n c).toLinearMap)
        (power (power T m) n) =
      power T (n * m) := by
  induction n with
  | zero =>
      simp_rw [powerFlattenEquiv_zero]
      rw [map_linearEquiv_trans, map_powerZeroEquiv_power_zero]
      exact map_powerCast_power (K := K) (V := V) T (Nat.zero_mul m).symm
  | succ n ih =>
      rw [power_succ, map_powerFlattenEquiv_powerMul, ih,
        map_powerOneEquiv_powerOne, powerMul_power]
      exact map_powerCast_power (K := K) (V := V) T (Nat.succ_mul n m).symm

/-! ## Powers concatenate

An external product of two powers of the same tensor is again a power.  `Tensor/Power.lean`
provides the isomorphism between an external product and its concatenated form, and
`powerMul_power` above identifies the concatenation of the `m`th and `n`th powers with the
`(m + n)`th power.  This is the input that turns external multiplicativity of a numerical invariant
into multiplicativity along the power sequence in `Tensor/AsymptoticInvariant.lean`. -/

/-- The external product of the `m`th and `n`th canonical tensor powers of `T` is legwise
isomorphic to the `(m + n)`th power.  The source is `external (power T m) (power T n)`, whose legs
are binary tensor products of powers, and the target is `power T (m + n)`.

Proof sketch: `Isomorphic.external_powerMul` concatenates the leg spaces, and `powerMul_power`
identifies the concatenated tensor with the canonical `(m + n)`th power. -/
theorem isomorphic_external_power (T : Tensor3 K V) (m n : ℕ) :
    Isomorphic (external (power T m) (power T n)) (power T (m + n)) := by
  have h := Isomorphic.external_powerMul (K := K) (V := V) m n (power T m) (power T n)
  rwa [powerMul_power] at h

namespace Isomorphic

/-- The canonical first tensor power is legwise isomorphic to the tensor itself. -/
theorem power_one (T : Tensor3 K V) : Isomorphic (Tensor.power T 1) T := by
  rw [power_one_eq_powerOne]
  exact (Isomorphic.powerOneTransport T).symm

/-- Powers whose exponents are equal are canonically isomorphic by reindexing. -/
theorem power_congr (T : Tensor3 K V) {a b : ℕ} (h : a = b) :
    Isomorphic (Tensor.power T a) (Tensor.power T b) :=
  ⟨powerCastEquiv (K := K) (V := V) h,
    map_powerCast_power (K := K) (V := V) T h⟩

/-- A canonical power of a canonical power is canonically isomorphic to the power with product
exponent. -/
theorem power_power (T : Tensor3 K V) (m n : ℕ) :
    Isomorphic (Tensor.power (Tensor.power T m) n) (Tensor.power T (n * m)) :=
  ⟨powerFlattenEquiv (K := K) (V := V) m n,
    map_powerFlattenEquiv_power (K := K) (V := V) T m n⟩

/-- Commuted-exponent form of `power_power`, convenient when the inner block length is written
first in a paper. -/
theorem power_power_mul_comm (T : Tensor3 K V) (m n : ℕ) :
    Isomorphic (Tensor.power (Tensor.power T m) n) (Tensor.power T (m * n)) :=
  (power_power T m n).trans (power_congr T (Nat.mul_comm n m))

end Isomorphic

end AlgebraicComplexity.Tensor
