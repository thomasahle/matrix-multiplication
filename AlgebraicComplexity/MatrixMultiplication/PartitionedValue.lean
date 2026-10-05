/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.ExponentDefs
import AlgebraicComplexity.Probability.SupportDistribution
import AlgebraicComplexity.Tensor.Degeneration
import AlgebraicComplexity.Tensor.Partitioned

/-!
# Matrix-multiplication data and numerical values for partitioned tensors

This lightweight module records constituent-wise matrix-multiplication degeneration certificates
and their entropy/volume expression.  It contains no laser extraction or Schönhage soundness
theorem.  Those semantic conclusions live in `MatrixMultiplication/PartitionedLaser.lean`.

The separation lets finite partition constructions expose what each constituent computes without
importing the asymptotic proof used by a later hashing client.
-/

namespace AlgebraicComplexity

open Tensor

universe u v w

variable (K : Type u) [CommSemiring K]
variable {A : Leg → Type w} [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]
variable {V : ∀ c, A c → Type v}
variable [∀ c a, AddCommMonoid (V c a)] [∀ c a, Module K (V c a)]

/-- A certificate identifying every supported constituent of a partitioned tensor with a
rectangular matrix-multiplication tensor, constructively up to polynomial degeneration. -/
structure PartitionedMMCertificate
    (P : PartitionedTensor (K := K) (A := A) V) where
  m : P.support → ℕ
  n : P.support → ℕ
  p : P.support → ℕ
  m_pos : ∀ s, 0 < m s
  n_pos : ∀ s, 0 < n s
  p_pos : ∀ s, 0 < p s
  degenerates : ∀ s : P.support,
    PolynomialDegenerates (P.constituent s.1)
      (matrixMultiplication (K := K) (m s) (n s) (p s))

namespace PartitionedMMCertificate

variable {K}
variable {P : PartitionedTensor (K := K) (A := A) V}

/-- Volume `m n p` of a certified constituent. -/
def volume (C : PartitionedMMCertificate K P) (s : P.support) : ℕ :=
  C.m s * C.n s * C.p s

/-- Every certified constituent has positive matrix-multiplication volume. -/
theorem volume_pos (C : PartitionedMMCertificate K P) (s : P.support) :
    0 < C.volume s := by
  exact Nat.mul_pos (Nat.mul_pos (C.m_pos s) (C.n_pos s)) (C.p_pos s)

end PartitionedMMCertificate

/-- The support-level logarithmic laser value for a distribution and a positive constituent-volume
function.  This definition is useful before a concrete partitioned-tensor realization has been
chosen. -/
noncomputable def supportLaserLogValue
    {support : Finset (BlockAddress A)}
    (μ : SupportDistribution support) (volume : support → ℕ) : ℝ :=
  μ.minimumMarginalEntropy +
    (omega K / 3) * μ.expectedLogNat volume

/-- Logarithmic value delivered by a support distribution in the zero-combination-loss case.
The first term counts independent constituents; the second is their expected logarithmic
matrix-multiplication volume, scaled by `ω/3`. -/
noncomputable def partitionedLaserLogValue
    {P : PartitionedTensor (K := K) (A := A) V}
    (C : PartitionedMMCertificate K P)
    (μ : SupportDistribution P.support) : ℝ :=
  supportLaserLogValue K μ C.volume

end AlgebraicComplexity
