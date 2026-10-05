import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Finite maximum-entropy dual certificates

For any finite probability distribution `p` and any real score function `u`, the Gibbs
distribution proportional to `exp (u a)` gives

`H(p) ≤ log (∑ a, exp (u a)) - ∑ a, p a * u a`.

Specializing the score to a sum of three coordinate potentials gives a finite maximum-entropy
dual bound.  This module proves the certificate-soundness direction only; equality between the
primal maximum and the infimum over potentials is deliberately not needed.

The development is independent of tensors and matrix multiplication.  Its old public names under
`MatrixMultiplication.EntropyDual` are re-exported by the compatibility module at the former path.
-/

open scoped BigOperators

noncomputable section

namespace AlgebraicComplexity.MaximumEntropyDual

variable {A B X Y Z : Type*}

/-- Shannon entropy in nats.  `Real.negMulLog 0 = 0`. -/
def entropy [Fintype A] (p : A → ℝ) : ℝ :=
  ∑ a, Real.negMulLog (p a)

/-- Cross entropy in nats. -/
def crossEntropy [Fintype A] (p q : A → ℝ) : ℝ :=
  ∑ a, -(p a * Real.log (q a))

/-- The pointwise form of Gibbs' inequality, including the case `p = 0`. -/
lemma entropyTerm_le_crossEntropy_add {p q : ℝ} (hp : 0 ≤ p) (hq : 0 < q) :
    Real.negMulLog p ≤ -(p * Real.log q) + q - p := by
  rcases hp.eq_or_lt with rfl | hp
  · simpa [Real.negMulLog] using hq.le
  · have hlog := Real.log_le_sub_one_of_pos (div_pos hq hp)
    rw [Real.log_div hq.ne' hp.ne'] at hlog
    have hm := mul_le_mul_of_nonneg_left hlog hp.le
    have hratio : p * (q / p - 1) = q - p := by
      field_simp [hp.ne']
    rw [hratio] at hm
    rw [Real.negMulLog]
    nlinarith

/-- Gibbs' inequality for finite probability vectors. -/
theorem entropy_le_crossEntropy [Fintype A]
    (p q : A → ℝ) (hp : ∀ a, 0 ≤ p a) (hq : ∀ a, 0 < q a)
    (hpsum : ∑ a, p a = 1) (hqsum : ∑ a, q a = 1) :
    entropy p ≤ crossEntropy p q := by
  rw [entropy, crossEntropy]
  calc
    ∑ a, Real.negMulLog (p a) ≤
        ∑ a, (-(p a * Real.log (q a)) + q a - p a) :=
      Finset.sum_le_sum fun a _ ↦ entropyTerm_le_crossEntropy_add (hp a) (hq a)
    _ = ∑ a, -(p a * Real.log (q a)) := by
      rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, hqsum, hpsum]
      ring

/-- Partition function of a finite exponential family. -/
def partition [Fintype A] (score : A → ℝ) : ℝ :=
  ∑ a, Real.exp (score a)

lemma partition_pos [Fintype A] [Nonempty A] (score : A → ℝ) :
    0 < partition score := by
  rw [partition]
  exact Finset.sum_pos (fun a _ ↦ Real.exp_pos (score a)) Finset.univ_nonempty

/-- The Gibbs distribution associated to an arbitrary score function. -/
def gibbs [Fintype A] (score : A → ℝ) (a : A) : ℝ :=
  Real.exp (score a) / partition score

lemma gibbs_pos [Fintype A] [Nonempty A] (score : A → ℝ) (a : A) :
    0 < gibbs score a :=
  div_pos (Real.exp_pos _) (partition_pos score)

lemma sum_gibbs [Fintype A] [Nonempty A] (score : A → ℝ) :
    ∑ a, gibbs score a = 1 := by
  simp_rw [gibbs, div_eq_mul_inv]
  rw [← Finset.sum_mul, partition]
  exact mul_inv_cancel₀ (partition_pos score).ne'

lemma log_gibbs [Fintype A] [Nonempty A] (score : A → ℝ) (a : A) :
    Real.log (gibbs score a) = score a - Real.log (partition score) := by
  rw [gibbs, Real.log_div (Real.exp_ne_zero _) (partition_pos score).ne', Real.log_exp]

/-- The finite exponential-family dual bound in natural logarithms. -/
theorem entropy_le_logPartition_sub_expectation [Fintype A] [Nonempty A]
    (p : A → ℝ) (score : A → ℝ) (hp : ∀ a, 0 ≤ p a)
    (hpsum : ∑ a, p a = 1) :
    entropy p ≤ Real.log (partition score) - ∑ a, p a * score a := by
  calc
    entropy p ≤ crossEntropy p (gibbs score) :=
      entropy_le_crossEntropy p (gibbs score) hp (gibbs_pos score) hpsum (sum_gibbs score)
    _ = Real.log (partition score) - ∑ a, p a * score a := by
      rw [crossEntropy]
      simp_rw [log_gibbs]
      calc
        ∑ a, -(p a * (score a - Real.log (partition score))) =
            ∑ a, (p a * Real.log (partition score) - p a * score a) := by
          apply Finset.sum_congr rfl
          intro a _
          ring
        _ = Real.log (partition score) - ∑ a, p a * score a := by
          rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hpsum]
          ring

/-- Push a finite mass vector forward along a coordinate map. -/
def marginal [Fintype A] [Fintype B] [DecidableEq B]
    (coord : A → B) (p : A → ℝ) (b : B) : ℝ :=
  ∑ a, if coord a = b then p a else 0

/-- Expectations of coordinate potentials depend only on the corresponding marginal. -/
theorem sum_potential_marginal [Fintype A] [Fintype B] [DecidableEq B]
    (coord : A → B) (p : A → ℝ) (u : B → ℝ) :
    ∑ b, u b * marginal coord p b = ∑ a, p a * u (coord a) := by
  simp_rw [marginal, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  simp [mul_ite, mul_comm]

/-- A score that is a sum of three coordinate potentials. -/
def coordinateScore (coordX : A → X) (coordY : A → Y) (coordZ : A → Z)
    (uX : X → ℝ) (uY : Y → ℝ) (uZ : Z → ℝ) (a : A) : ℝ :=
  uX (coordX a) + uY (coordY a) + uZ (coordZ a)

/-- The coordinate-score expectation is exactly the three marginal pairings. -/
theorem coordinateScore_expectation
    [Fintype A] [Fintype X] [Fintype Y] [Fintype Z]
    [DecidableEq X] [DecidableEq Y] [DecidableEq Z]
    (coordX : A → X) (coordY : A → Y) (coordZ : A → Z)
    (p : A → ℝ) (uX : X → ℝ) (uY : Y → ℝ) (uZ : Z → ℝ) :
    ∑ a, p a * coordinateScore coordX coordY coordZ uX uY uZ a =
      (∑ x, uX x * marginal coordX p x) +
      (∑ y, uY y * marginal coordY p y) +
      (∑ z, uZ z * marginal coordZ p z) := by
  simp_rw [coordinateScore, mul_add, Finset.sum_add_distrib]
  rw [sum_potential_marginal, sum_potential_marginal, sum_potential_marginal]

/-- Shannon entropy measured in bits. -/
def entropyBits [Fintype A] (p : A → ℝ) : ℝ :=
  entropy p / Real.log 2

/-- Base-two partition function, implemented through the natural exponential. -/
def partitionTwo [Fintype A] (score : A → ℝ) : ℝ :=
  partition fun a ↦ Real.log 2 * score a

/-- The maximum-entropy dual expression in bits. -/
def coordinateDualBits
    [Fintype A] [Fintype X] [Fintype Y] [Fintype Z]
    [DecidableEq X] [DecidableEq Y] [DecidableEq Z]
    (coordX : A → X) (coordY : A → Y) (coordZ : A → Z)
    (p : A → ℝ) (uX : X → ℝ) (uY : Y → ℝ) (uZ : Z → ℝ) : ℝ :=
  Real.log (partitionTwo (coordinateScore coordX coordY coordZ uX uY uZ)) / Real.log 2 -
    ((∑ x, uX x * marginal coordX p x) +
     (∑ y, uY y * marginal coordY p y) +
     (∑ z, uZ z * marginal coordZ p z))

/-- The coordinate-potential upper-bound direction, in base two and with three marginals. -/
theorem entropyBits_le_coordinateDual
    [Fintype A] [Nonempty A] [Fintype X] [Fintype Y] [Fintype Z]
    [DecidableEq X] [DecidableEq Y] [DecidableEq Z]
    (coordX : A → X) (coordY : A → Y) (coordZ : A → Z)
    (p : A → ℝ) (uX : X → ℝ) (uY : Y → ℝ) (uZ : Z → ℝ)
    (hp : ∀ a, 0 ≤ p a) (hpsum : ∑ a, p a = 1) :
    entropyBits p ≤ coordinateDualBits coordX coordY coordZ p uX uY uZ := by
  have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hdual := entropy_le_logPartition_sub_expectation p
    (fun a ↦ Real.log 2 * coordinateScore coordX coordY coordZ uX uY uZ a) hp hpsum
  have hexpect : ∑ a, p a * coordinateScore coordX coordY coordZ uX uY uZ a =
      (∑ x, uX x * marginal coordX p x) +
      (∑ y, uY y * marginal coordY p y) +
      (∑ z, uZ z * marginal coordZ p z) :=
    coordinateScore_expectation coordX coordY coordZ p uX uY uZ
  have hscaled :
      ∑ a, p a * (Real.log 2 * coordinateScore coordX coordY coordZ uX uY uZ a) =
        Real.log 2 * ∑ a, p a * coordinateScore coordX coordY coordZ uX uY uZ a := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    ring
  rw [entropyBits, coordinateDualBits, partitionTwo]
  apply (div_le_iff₀ hlogTwo).2
  rw [hscaled, hexpect] at hdual
  calc
    entropy p ≤
        Real.log (partition fun a ↦
          Real.log 2 * coordinateScore coordX coordY coordZ uX uY uZ a) -
          Real.log 2 *
            ((∑ x, uX x * marginal coordX p x) +
             (∑ y, uY y * marginal coordY p y) +
             (∑ z, uZ z * marginal coordZ p z)) := hdual
    _ = (Real.log (partition fun a ↦
          Real.log 2 * coordinateScore coordX coordY coordZ uX uY uZ a) / Real.log 2 -
          ((∑ x, uX x * marginal coordX p x) +
           (∑ y, uY y * marginal coordY p y) +
           (∑ z, uZ z * marginal coordZ p z))) * Real.log 2 := by
      field_simp [hlogTwo.ne']

/-- A finite probability vector. -/
def IsProbability [Fintype A] (p : A → ℝ) : Prop :=
  (∀ a, 0 ≤ p a) ∧ ∑ a, p a = 1

/-- Equality of all three coordinate marginals. -/
def SameMarginals
    [Fintype A] [Fintype X] [Fintype Y] [Fintype Z]
    [DecidableEq X] [DecidableEq Y] [DecidableEq Z]
    (coordX : A → X) (coordY : A → Y) (coordZ : A → Z)
    (p q : A → ℝ) : Prop :=
  marginal coordX p = marginal coordX q ∧
  marginal coordY p = marginal coordY q ∧
  marginal coordZ p = marginal coordZ q

/-- The supremum of entropy over distributions with the reference marginals. -/
def maximumEntropyBits
    [Fintype A] [Fintype X] [Fintype Y] [Fintype Z]
    [DecidableEq X] [DecidableEq Y] [DecidableEq Z]
    (coordX : A → X) (coordY : A → Y) (coordZ : A → Z)
    (reference : A → ℝ) : ℝ :=
  sSup {h : ℝ | ∃ p : A → ℝ,
    IsProbability p ∧ SameMarginals coordX coordY coordZ p reference ∧ h = entropyBits p}

lemma coordinateDualBits_eq_of_sameMarginals
    [Fintype A] [Fintype X] [Fintype Y] [Fintype Z]
    [DecidableEq X] [DecidableEq Y] [DecidableEq Z]
    (coordX : A → X) (coordY : A → Y) (coordZ : A → Z)
    (p q : A → ℝ) (uX : X → ℝ) (uY : Y → ℝ) (uZ : Z → ℝ)
    (h : SameMarginals coordX coordY coordZ p q) :
    coordinateDualBits coordX coordY coordZ p uX uY uZ =
      coordinateDualBits coordX coordY coordZ q uX uY uZ := by
  rcases h with ⟨hX, hY, hZ⟩
  simp only [coordinateDualBits]
  rw [hX, hY, hZ]

/-- The maximum-entropy upper bound, stated with an actual supremum. -/
theorem maximumEntropyBits_le_coordinateDual
    [Fintype A] [Nonempty A] [Fintype X] [Fintype Y] [Fintype Z]
    [DecidableEq X] [DecidableEq Y] [DecidableEq Z]
    (coordX : A → X) (coordY : A → Y) (coordZ : A → Z)
    (reference : A → ℝ) (uX : X → ℝ) (uY : Y → ℝ) (uZ : Z → ℝ)
    (href : IsProbability reference) :
    maximumEntropyBits coordX coordY coordZ reference ≤
      coordinateDualBits coordX coordY coordZ reference uX uY uZ := by
  apply csSup_le
  · refine ⟨entropyBits reference, reference, href, ?_, rfl⟩
    exact ⟨rfl, rfl, rfl⟩
  · intro h hh
    rcases hh with ⟨p, hp, hmarg, rfl⟩
    exact (entropyBits_le_coordinateDual coordX coordY coordZ p uX uY uZ hp.1 hp.2).trans_eq
      (coordinateDualBits_eq_of_sameMarginals coordX coordY coordZ p reference uX uY uZ hmarg)

/-- The entropy gap between the maximum distribution with fixed marginals and the supplied one. -/
def combinationLossBits
    [Fintype A] [Fintype X] [Fintype Y] [Fintype Z]
    [DecidableEq X] [DecidableEq Y] [DecidableEq Z]
    (coordX : A → X) (coordY : A → Y) (coordZ : A → Z)
    (reference : A → ℝ) : ℝ :=
  maximumEntropyBits coordX coordY coordZ reference - entropyBits reference

/-- Arbitrary coordinate potentials conservatively upper-bound the fixed-marginal entropy gap. -/
theorem combinationLossBits_le_dualGap
    [Fintype A] [Nonempty A] [Fintype X] [Fintype Y] [Fintype Z]
    [DecidableEq X] [DecidableEq Y] [DecidableEq Z]
    (coordX : A → X) (coordY : A → Y) (coordZ : A → Z)
    (reference : A → ℝ) (uX : X → ℝ) (uY : Y → ℝ) (uZ : Z → ℝ)
    (href : IsProbability reference) :
    combinationLossBits coordX coordY coordZ reference ≤
      coordinateDualBits coordX coordY coordZ reference uX uY uZ - entropyBits reference := by
  exact sub_le_sub_right
    (maximumEntropyBits_le_coordinateDual coordX coordY coordZ reference uX uY uZ href) _

/-- Subtracting the entropy of the supplied distribution gives the combination-loss certificate. -/
theorem combinationLoss_le_of_maxEntropy_le {maximumEntropy dual suppliedEntropy : ℝ}
    (h : maximumEntropy ≤ dual) :
    maximumEntropy - suppliedEntropy ≤ dual - suppliedEntropy := by
  linarith

end AlgebraicComplexity.MaximumEntropyDual
