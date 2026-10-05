import AlgebraicComplexity.Probability.Entropy
import AlgebraicComplexity.Tensor.Partitioned
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-!
# Probability distributions on finite tensor supports

Type distributions and their leg marginals are the information-theoretic input to laser-method
arguments.  This module defines them for an arbitrary finite tensor support, independently of
matrix multiplication or any optimizer.

A distribution on a finite support of block addresses is *identified* with a
`ProbabilityVector` on the support's coercion to a type: `SupportDistribution support` is an
abbreviation for `ProbabilityVector ↥support`.  The generic finite probability API therefore
applies directly.  In particular the total mass, nonnegativity, extensionality, Shannon entropy
(`ProbabilityVector.entropy`, from `Probability/Entropy.lean`), and expectation
(`ProbabilityVector.expectation`, from `Probability/Finite.lean`) are reused rather than
duplicated.  What this file adds is the support-specific structure: the three leg marginals of a
distribution on block addresses, their entropies and bottleneck entropy, expected logarithmic
constituent sizes, equality of marginals, and the maximum-entropy predicate used by tight-support
laser theorems.

Layer placement: this is a layer-2 probability module.  It imports the layer-1 tensor module
`Tensor/Partitioned.lean` only for the `BlockAddress` index type; no tensor algebra is used.  The
declarations keep their historical full names inside the `AlgebraicComplexity.Tensor` namespace
because this API originated in the retired tensor-layer module `Tensor/Support.lean`, whose
bespoke distribution structure this reuse replaces.  Relative to that module, the duplicate
constants `SupportDistribution.entropy` and `SupportDistribution.expectation` no longer exist:
dot notation on a support distribution now resolves them to `ProbabilityVector.entropy` and
`ProbabilityVector.expectation`, which have definitionally the same values.
-/

namespace AlgebraicComplexity.Tensor

universe w

variable {A : Leg → Type w} [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]

/-- A probability distribution carried by a finite tensor support, namely a finite probability
vector indexed by the elements of the support.  Nonnegative weights summing to one, entropy, and
expectation are all inherited from `ProbabilityVector`. -/
abbrev SupportDistribution (support : Finset (BlockAddress A)) :=
  ProbabilityVector ↥support

namespace SupportDistribution

variable {support : Finset (BlockAddress A)}

omit [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)] in
/-- A support distribution is determined by its weight function; positivity and normalization
proofs carry no additional data.  This restates `ProbabilityVector.ext` under its historical
name. -/
theorem ext {μ ν : SupportDistribution support} (h : μ.weight = ν.weight) : μ = ν :=
  ProbabilityVector.ext h

/-- The marginal probability of block `a` on leg `c`. -/
noncomputable def marginal (μ : SupportDistribution support) (c : Leg) (a : A c) : ℝ :=
  ∑ s : support, if s.1 c = a then μ.weight s else 0

omit [∀ c, Fintype (A c)] in
/-- Every marginal probability is nonnegative. -/
theorem marginal_nonneg (μ : SupportDistribution support) (c : Leg) (a : A c) :
    0 ≤ μ.marginal c a := by
  classical
  apply Finset.sum_nonneg
  intro s hs
  split <;> simp_all [μ.nonneg]

/-- Every leg marginal is itself a probability distribution. -/
theorem sum_marginal (μ : SupportDistribution support) (c : Leg) :
    ∑ a, μ.marginal c a = 1 := by
  classical
  calc
    ∑ a, μ.marginal c a =
        ∑ s : support, ∑ a, if s.1 c = a then μ.weight s else 0 := by
      unfold marginal
      rw [Finset.sum_comm]
    _ = ∑ s : support, μ.weight s := by simp
    _ = 1 := μ.total

/-- A support marginal is the weight function of the corresponding deterministic pushforward. -/
theorem marginal_eq_pushforward_weight
    (μ : SupportDistribution support) (c : Leg) (a : A c) :
    μ.marginal c a =
      (μ.pushforward (fun s : support ↦ s.1 c)).weight a := by
  rw [ProbabilityVector.pushforward_weight]
  rfl

/-- Shannon entropy in nats of one leg marginal.  `Real.negMulLog` gives the continuous
convention `0 log 0 = 0`. -/
noncomputable def marginalEntropy (μ : SupportDistribution support) (c : Leg) : ℝ :=
  ∑ a, Real.negMulLog (μ.marginal c a)

/-- Expected logarithm of a positive-integer size attached to each constituent, via the reused
`ProbabilityVector.expectation`. -/
noncomputable def expectedLogNat (μ : SupportDistribution support) (size : support → ℕ) : ℝ :=
  μ.expectation fun s ↦ Real.log (size s)

/-- The bottleneck entropy among the three leg marginals. -/
noncomputable def minimumMarginalEntropy (μ : SupportDistribution support) : ℝ :=
  min (μ.marginalEntropy .X) (min (μ.marginalEntropy .Y) (μ.marginalEntropy .Z))

/-- Two support distributions lie in the same marginal fiber when their three one-leg
marginals agree pointwise. -/
def SameMarginals (μ ν : SupportDistribution support) : Prop :=
  ∀ c a, μ.marginal c a = ν.marginal c a

/-- Equality of all three support marginals is equivalent to equality of the three deterministic
pushforward probability vectors. -/
theorem sameMarginals_iff_pushforwards
    (μ ν : SupportDistribution support) :
    μ.SameMarginals ν ↔
      ∀ c, μ.pushforward (fun s : support ↦ s.1 c) =
        ν.pushforward (fun s : support ↦ s.1 c) := by
  constructor
  · intro h c
    apply ProbabilityVector.ext
    funext a
    rw [← marginal_eq_pushforward_weight, ← marginal_eq_pushforward_weight]
    exact h c a
  · intro h c a
    rw [marginal_eq_pushforward_weight, marginal_eq_pushforward_weight, h c]

omit [∀ c, Fintype (A c)] in
/-- Sharing marginals is reflexive. -/
@[refl] theorem sameMarginals_refl (μ : SupportDistribution support) :
    μ.SameMarginals μ := by
  intro c a
  rfl

omit [∀ c, Fintype (A c)] in
/-- Sharing marginals is symmetric. -/
theorem SameMarginals.symm {μ ν : SupportDistribution support}
    (h : μ.SameMarginals ν) : ν.SameMarginals μ := by
  intro c a
  exact (h c a).symm

omit [∀ c, Fintype (A c)] in
/-- Sharing marginals is transitive. -/
theorem SameMarginals.trans {μ ν ξ : SupportDistribution support}
    (hμν : μ.SameMarginals ν) (hνξ : ν.SameMarginals ξ) :
    μ.SameMarginals ξ := by
  intro c a
  exact (hμν c a).trans (hνξ c a)

/-- A support distribution has maximum entropy in its marginal fiber.  This is the exact
optimizer-independent hypothesis used by tight-support laser theorems.  Entropy here is the
reused `ProbabilityVector.entropy` in nats. -/
def IsMaximumEntropy (μ : SupportDistribution support) : Prop :=
  ∀ ν : SupportDistribution support, μ.SameMarginals ν → ν.entropy ≤ μ.entropy

omit [∀ c, Fintype (A c)] in
/-- A distribution uniquely determined by its marginals is automatically a maximum-entropy
representative of its marginal fiber. -/
theorem isMaximumEntropy_of_unique (μ : SupportDistribution support)
    (hunique : ∀ ν : SupportDistribution support, μ.SameMarginals ν → ν = μ) :
    μ.IsMaximumEntropy := by
  intro ν hν
  rw [hunique ν hν]

end SupportDistribution

end AlgebraicComplexity.Tensor
