/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.TwoLetterAggregateInterface
import AlgebraicComplexity.Probability.DyadicCoupling

/-!
# Dyadic certificate adapters for two-letter tensor interfaces

This leaf module connects exact dyadic joint tables to the matrix-multiplication layer's
two-letter aggregate-interface API.  The underlying numerator algebra and real coupling theorem
remain in `Probability.DyadicCoupling`; only the tensor-interface interpretation lives here.

The principal results cover both certificate patterns used by recursive laser analyses:

* exact row and column marginals give a genuine `ProbabilityVector.IsCoupling`; and
* the weaker exact sum of row and column marginals gives
  `ProbabilityVector.HasAggregateInterface`, even when the two marginals differ.

The final `32`/`48` corollary matches the current certificate format, while all semantic theorems
are generic in the two dyadic precisions.
-/

namespace AlgebraicComplexity

namespace DyadicMassData.HasAggregateMarginal

variable {I : Type*} [Fintype I] [DecidableEq I]
variable {bits extra : ℕ} {joint : DyadicMassData (I × I)}
variable {base : DyadicMassData I}

/-- A denominator-cleared aggregate marginal checksum becomes the real pointwise aggregate
interface required by two-letter tensor assembly.

Proof sketch: exact dyadic scatter-add commutes with real pushforward.  After putting the two
pushforward weights over their common `2^(bits+extra)` denominator, the stored aggregate numerator
identity reduces the sum to twice the `bits`-precision base weight. -/
theorem toReal_hasAggregateInterface
    (h : DyadicMassData.HasAggregateMarginal extra joint base)
    (hjoint : joint.IsProbability (bits + extra))
    (hbase : base.IsProbability bits) :
    ProbabilityVector.HasAggregateInterface
      ((joint.toProbabilityVector (bits + extra) hjoint).pushforward Prod.fst)
      ((joint.toProbabilityVector (bits + extra) hjoint).pushforward Prod.snd)
      (base.toProbabilityVector bits hbase) := by
  intro i
  rw [DyadicMassData.toProbabilityVector_pushforward,
    DyadicMassData.toProbabilityVector_pushforward]
  simp only [DyadicMassData.toProbabilityVector_weight]
  have hnaturals := h i
  have hreals :
      ((joint.pushforward Prod.fst).numerator i : ℝ) +
          ((joint.pushforward Prod.snd).numerator i : ℝ) =
        2 * ((base.numerator i : ℝ) * dyadicDenominator extra) := by
    exact_mod_cast hnaturals
  rw [← add_div, hreals]
  simp only [dyadicDenominator, pow_add]
  push_cast
  field_simp

/-- A normalized base row plus the aggregate row-and-column checksum is a complete exact
aggregate-interface certificate: it also determines normalization of the wider joint table. -/
theorem exists_toReal_hasAggregateInterface
    (h : DyadicMassData.HasAggregateMarginal extra joint base)
    (hbase : base.IsProbability bits) :
    ∃ hjoint : joint.IsProbability (bits + extra),
      ProbabilityVector.HasAggregateInterface
        ((joint.toProbabilityVector (bits + extra) hjoint).pushforward Prod.fst)
        ((joint.toProbabilityVector (bits + extra) hjoint).pushforward Prod.snd)
        (base.toProbabilityVector bits hbase) := by
  let hjoint : joint.IsProbability (bits + extra) := h.joint_isProbability hbase
  exact ⟨hjoint, h.toReal_hasAggregateInterface hjoint hbase⟩

end DyadicMassData.HasAggregateMarginal

namespace DyadicMassData.HasMarginals

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- Generic exact self-coupling certificate.  The marginal table may use any dyadic precision
`bits`; the joint table then uses `bits + extra`. -/
theorem exists_selfCoupling
    {bits extra : ℕ} {joint : DyadicMassData (I × I)} {base : DyadicMassData I}
    (h : DyadicMassData.HasMarginals extra joint base base)
    (hbase : base.IsProbability bits) :
    ∃ hjoint : joint.IsProbability (bits + extra),
      (joint.toProbabilityVector (bits + extra) hjoint).IsCoupling
        (base.toProbabilityVector bits hbase)
        (base.toProbabilityVector bits hbase) := by
  let hjoint : joint.IsProbability (bits + extra) := h.joint_isProbability hbase
  exact ⟨hjoint, h.toReal_isCoupling hbase hbase⟩

/-- Generic exact self-coupling certificates satisfy the probability-level aggregate interface
used by the two-letter tensor assembly theorem. -/
theorem exists_aggregateInterface
    {bits extra : ℕ} {joint : DyadicMassData (I × I)} {base : DyadicMassData I}
    (h : DyadicMassData.HasMarginals extra joint base base)
    (hbase : base.IsProbability bits) :
    ∃ hjoint : joint.IsProbability (bits + extra),
      ProbabilityVector.HasAggregateInterface
        ((joint.toProbabilityVector (bits + extra) hjoint).pushforward Prod.fst)
        ((joint.toProbabilityVector (bits + extra) hjoint).pushforward Prod.snd)
        (base.toProbabilityVector bits hbase) := by
  rcases h.exists_selfCoupling hbase with ⟨hjoint, hcoupling⟩
  refine ⟨hjoint, hcoupling.aggregateInterface_marginals ?_⟩
  exact ProbabilityVector.hasAggregateInterface_self
    (base.toProbabilityVector bits hbase)

/-- Current-certificate specialization: a 48-bit joint table whose row and column sums are the
16-bit rescalings of one 32-bit law is an exact self-coupling of that law. -/
theorem exists_b48_selfCoupling_of_b32_marginals
    {joint : DyadicMassData (I × I)} {base : DyadicMassData I}
    (h : DyadicMassData.HasMarginals 16 joint base base)
    (hbase : base.IsProbability 32) :
    ∃ hjoint : joint.IsProbability 48,
      (joint.toProbabilityVector 48 hjoint).IsCoupling
        (base.toProbabilityVector 32 hbase)
        (base.toProbabilityVector 32 hbase) := by
  simpa using h.exists_selfCoupling hbase

/-- The same 32/48 marginal checksum supplies the aggregate-interface law consumed by
`TwoLetterAggregateInterface`. -/
theorem exists_b48_aggregateInterface_of_b32_marginals
    {joint : DyadicMassData (I × I)} {base : DyadicMassData I}
    (h : DyadicMassData.HasMarginals 16 joint base base)
    (hbase : base.IsProbability 32) :
    ∃ hjoint : joint.IsProbability 48,
      ProbabilityVector.HasAggregateInterface
        ((joint.toProbabilityVector 48 hjoint).pushforward Prod.fst)
        ((joint.toProbabilityVector 48 hjoint).pushforward Prod.snd)
        (base.toProbabilityVector 32 hbase) := by
  simpa using h.exists_aggregateInterface hbase

end DyadicMassData.HasMarginals

end AlgebraicComplexity
