/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.WholeConstituentLaserVolumeAssembly

/-!
# Lossless power lift for a finite rectangular extraction

This is a small but useful asymptotic adapter.  A single finite restriction of `T ^ stride` to
identical rectangular matrix-multiplication tensors can be tensored with itself repeatedly.  The
result is a `SubexponentialLaserVolumeSequence` with no counting loss: copy counts and all three
matrix dimensions are ordinary natural powers.

Keeping this construction here, rather than reproving it in each concrete CW client, has two
benefits.  First, a finite semantic certificate can be checked independently of asymptotic
bookkeeping.  Second, the only nontrivial finite input to the asymptotic theorem remains an
actual `WholeConstituentLaserVolumeStage`; no opaque ``there exists a sequence'' premise is
introduced.
-/

namespace AlgebraicComplexity

open Tensor

universe u v w

section

variable (K : Type u) [CommSemiring K]
variable {Source : Leg → Type v}
variable [∀ c, AddCommMonoid (Source c)] [∀ c, Module K (Source c)]

namespace WholeConstituentLaserVolumeStage

/-- Reindex a finite stage to the canonical `Fin copies` output index.

Normalizing the index is important for iterated products: an arbitrary `Nonempty` stage can hide
an index type in a fresh universe, whereas products of `Fin` types stay in `Type 0`. -/
noncomputable def toFin
    {T : Tensor3 K Source} {copies xSize ySize zSize : ℕ}
    (stage : WholeConstituentLaserVolumeStage K T copies xSize ySize zSize) :
    WholeConstituentLaserVolumeStage K T copies xSize ySize zSize where
  I := Fin copies
  card_I := by simp
  source_restricts := by
    letI := stage.fintypeI
    let leaf := matrixMultiplication (K := K) xSize ySize zSize
    let e : stage.I ≃ Fin copies := Fintype.equivFinOfCardEq stage.card_I
    have hreindex : Restricts
        (Tensor.indexedDirectSum (fun _ : stage.I ↦ leaf))
        (Tensor.indexedDirectSum (fun _ : Fin copies ↦ leaf)) :=
      Tensor.Restricts.indexedDirectSum_const_equiv (K := K) e leaf
    exact stage.source_restricts.trans (by
      simpa only [matrixMultiplicationDirectSum, leaf] using hreindex)

/-- Positive powers of one finite stage, indexed by the number of repetitions.

The `Nonempty` wrapper keeps the recursive construction independent of arbitrary choices of
finite index equivalences.  The zeroth power is intentionally not needed: the theorem below only
uses the positive case, while the induction starts at one copy of the supplied stage.
-/
theorem exists_power_succ
    {T : Tensor3 K Source} {stride copies xSize ySize zSize : ℕ}
    (stage : WholeConstituentLaserVolumeStage K (Tensor.power T stride)
      copies xSize ySize zSize) :
    ∀ r : ℕ, Nonempty
      (WholeConstituentLaserVolumeStage.{u, max u v, 0} K
        (Tensor.power T (stride * (r + 1)))
        (copies ^ (r + 1)) (xSize ^ (r + 1)) (ySize ^ (r + 1)) (zSize ^ (r + 1))) := by
  intro r
  induction r with
  | zero =>
      refine ⟨?_⟩
      have hstride : stride * (0 + 1) = stride := by simp
      have hcopy : copies ^ (0 + 1) = copies := by simp
      have hx : xSize ^ (0 + 1) = xSize := by simp
      have hy : ySize ^ (0 + 1) = ySize := by simp
      have hz : zSize ^ (0 + 1) = zSize := by simp
      rw [hstride, hcopy, hx, hy, hz]
      exact WholeConstituentLaserVolumeStage.toFin (K := K) stage
  | succ r ih =>
      rcases ih with ⟨previous⟩
      let next := WholeConstituentLaserVolumeStage.toFin (K := K)
        (stage := WholeConstituentLaserVolumeStage.powerAdd (K := K) previous
          (WholeConstituentLaserVolumeStage.toFin (K := K) stage))
      refine ⟨?_⟩
      have hstride : stride * (Nat.succ r + 1) = stride * (r + 1) + stride := by
        simp [Nat.succ_eq_add_one, Nat.mul_add, Nat.mul_two, Nat.add_assoc]
      have hcopy : copies ^ (Nat.succ r + 1) = copies ^ (r + 1) * copies := by
        simp [Nat.succ_eq_add_one, Nat.add_assoc, pow_succ]
      have hx : xSize ^ (Nat.succ r + 1) = xSize ^ (r + 1) * xSize := by
        simp [Nat.succ_eq_add_one, Nat.add_assoc, pow_succ]
      have hy : ySize ^ (Nat.succ r + 1) = ySize ^ (r + 1) * ySize := by
        simp [Nat.succ_eq_add_one, Nat.add_assoc, pow_succ]
      have hz : zSize ^ (Nat.succ r + 1) = zSize ^ (r + 1) * zSize := by
        simp [Nat.succ_eq_add_one, Nat.add_assoc, pow_succ]
      rw [hstride, hcopy, hx, hy, hz]
      exact next

/-- Every positive repetition count admits the corresponding powered finite stage.

Proof sketch: write `r` as `(r - 1) + 1`, apply `exists_power_succ`, and transport across the
resulting natural-number equality. -/
theorem exists_power_of_pos
    {T : Tensor3 K Source} {stride copies xSize ySize zSize : ℕ}
    (stage : WholeConstituentLaserVolumeStage K (Tensor.power T stride)
      copies xSize ySize zSize)
    {r : ℕ} (hr : 0 < r) :
    Nonempty
      (WholeConstituentLaserVolumeStage.{u, max u v, 0} K
        (Tensor.power T (stride * r))
        (copies ^ r) (xSize ^ r) (ySize ^ r) (zSize ^ r)) := by
  obtain ⟨s⟩ := exists_power_succ (K := K) stage (r - 1)
  have hsub : r - 1 + 1 = r := Nat.sub_add_cancel hr
  rw [hsub] at s
  exact ⟨s⟩

end WholeConstituentLaserVolumeStage

namespace WholeConstituentLaserVolumeSequenceData

/-- Turn one finite whole-constituent stage into a lossless sequence.

The declared bases are the finite copy count and the rectangular volume.  The loss is the
constant one sequence, so all asymptotic estimates reduce to exact power identities. -/
noncomputable def ofFiniteStage
    {T : Tensor3 K Source} {stride copies xSize ySize zSize : ℕ}
    (stage : WholeConstituentLaserVolumeStage K (Tensor.power T stride)
      copies xSize ySize zSize)
    (hstride : 0 < stride) (hcopy : 0 < copies)
    (hx : 0 < xSize) (hy : 0 < ySize) (hz : 0 < zSize) :
    WholeConstituentLaserVolumeSequenceData K T stride
      (copies : ℝ) ((xSize * ySize * zSize : ℕ) : ℝ) where
  stride_pos := hstride
  copyBase_pos := by exact_mod_cast hcopy
  volumeBase_pos := by exact_mod_cast Nat.mul_pos (Nat.mul_pos hx hy) hz
  loss := fun _ ↦ 1
  count := fun r ↦ copies ^ r
  xSize := fun r ↦ xSize ^ r
  ySize := fun r ↦ ySize ^ r
  zSize := fun r ↦ zSize ^ r
  loss_subexponential := Growth.Subexponential.const (by norm_num)
  loss_pos := fun r _ ↦ by norm_num
  count_pos := fun r _ ↦ pow_pos hcopy r
  xSize_pos := fun r _ ↦ pow_pos hx r
  ySize_pos := fun r _ ↦ pow_pos hy r
  zSize_pos := fun r _ ↦ pow_pos hz r
  stage := fun r hr ↦ Classical.choice
    (WholeConstituentLaserVolumeStage.exists_power_of_pos (K := K) stage hr)
  copy_growth := by
    intro r hr
    simpa only [one_mul, Nat.cast_pow] using (le_refl ((copies : ℝ) ^ r))
  volume_growth := by
    intro r hr
    simpa only [Nat.cast_mul, Nat.cast_pow, mul_pow] using
      (le_refl (((xSize : ℝ) ^ r) * ((ySize : ℝ) ^ r) * ((zSize : ℝ) ^ r)))

end WholeConstituentLaserVolumeSequenceData

end

end AlgebraicComplexity
