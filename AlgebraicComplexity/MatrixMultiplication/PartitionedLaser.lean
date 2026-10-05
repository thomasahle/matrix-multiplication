/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.Laser
import AlgebraicComplexity.MatrixMultiplication.PartitionedValue

/-!
# Matrix-multiplication constituents of partitioned tensors

This module states the reusable semantic interface between partitioned tensors and the
combinatorial tight-support laser theorem.  It does not postulate that theorem: the final
`TightSupportLaserConclusion` is a proposition that a hashing/typical-sequence development can
prove from Schönhage's asymptotic sum inequality.  The probabilistic input is a
`SupportDistribution` on the tensor's block support, provided by the probability-layer module
`Probability/SupportDistribution.lean` as a finite probability vector on the support.

The constituent certificate and numerical entropy/volume expression are re-exported from the
lower `PartitionedValue.lean` leaf.  Keeping the semantic interface independent of any particular
CW power or numerical optimizer makes the eventual combinatorial proof reusable by classical and
future laser-method clients.
-/

namespace AlgebraicComplexity

open Tensor

universe u v w

section Semiring

variable (K : Type u) [CommSemiring K]
variable {A : Leg → Type w} [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]
variable {V : ∀ c, A c → Type v}
variable [∀ c a, AddCommMonoid (V c a)] [∀ c a, Module K (V c a)]

/-- Combinatorial extraction obligation for the tight-support method.  It asks the eventual
hashing/typical-sequence theorem to achieve the entropy-and-volume value as an actual sequence of
finite direct-sum degenerations.  Schönhage's inequality is intentionally not part of this
definition. -/
def TightSupportLaserExtraction
    (P : PartitionedTensor (K := K) (A := A) V) : Prop :=
  IsTightSupport P.support →
    ∀ (C : PartitionedMMCertificate K P) (μ : SupportDistribution P.support),
      μ.IsMaximumEntropy →
        HasLaserExtractionRate K P.realize (partitionedLaserLogValue K C μ)

/-- Exact proof obligation supplied by the tight-support hashing theorem for one partitioned
tensor.  Tightness, maximum entropy in the marginal fiber, and the constituent degeneration
certificates are explicit in the statement's data. -/
def TightSupportLaserConclusion
    (P : PartitionedTensor (K := K) (A := A) V) : Prop :=
  IsTightSupport P.support →
    ∀ (C : PartitionedMMCertificate K P) (μ : SupportDistribution P.support),
      μ.IsMaximumEntropy →
        partitionedLaserLogValue K C μ ≤ Real.log (borderRank P.realize)

end Semiring

section Field

variable (K : Type u) [Field K]
variable {A : Leg → Type w} [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]
variable {V : ∀ c, A c → Type v}
variable [∀ c a, AddCommMonoid (V c a)] [∀ c a, Module K (V c a)]

/-- The tight-support conclusion factors cleanly into its combinatorial extraction theorem and
Schönhage's asymptotic sum inequality. -/
theorem tightSupportLaserConclusion_of_extraction
    {P : PartitionedTensor (K := K) (A := A) V}
    (hextract : TightSupportLaserExtraction K P) :
    TightSupportLaserConclusion K P := by
  intro htight C μ hmax
  exact (hextract htight C μ hmax).le_log_borderRank K

end Field

end AlgebraicComplexity
