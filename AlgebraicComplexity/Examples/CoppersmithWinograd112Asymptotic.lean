/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Analysis.ProportionalMultinomial
import AlgebraicComplexity.Examples.CoppersmithWinograd112GlobalCounting
import AlgebraicComplexity.MatrixMultiplication.CyclicProductPowerCoherence

/-!
# Asymptotic value of the exceptional CW `112` constituent

This file turns the exact finite shared-Z extraction into the symmetrized asymptotic value used
in the tensor-square Coppersmith--Winograd argument.  The fixed input is a positive integral
profile `(L,L,G,G)`; repetition `k` uses the proportional profile
`(Lk,Lk,Gk,Gk)`.  The finite theorem supplies equal square matrix-multiplication tensors, while
the method of types and the Behrend bound absorb every polynomial and square-root-exponential
loss.

The public bases below deliberately remain in reusable method-of-types form.  Later lemmas
identify their logarithms with the familiar expression

`(2 - H₂(μ,μ,1-2μ) + ω(2-2μ) log₂ q) / 3`,

where `μ = L / (2(L+G))`.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor

universe u

/-- Number of copies of `T₁₁₂` in one un-oriented proportional word. -/
abbrev cw112CyclicStride (L G : ℕ) : ℕ := 2 * (L + G)

/-- Exponential base of either balanced binary side-marginal type class. -/
noncomputable def cw112SideEntropyBase (L G : ℕ) : ℝ :=
  WordType.proportionalEntropyBase (cw112SideMarginalType L G)

/-- Exponential base of the ternary Z-marginal type class `(L,L,2G)`. -/
noncomputable def cw112ZEntropyBase (L G : ℕ) : ℝ :=
  WordType.proportionalEntropyBase (cw112ZMarginalType L G)

/-- Copy-count base left after two side marginals are hashed and one shared Z marginal is
grouped. -/
noncomputable def cw112CyclicCopyBase (L G : ℕ) : ℝ :=
  cw112SideEntropyBase L G ^ 2 / cw112ZEntropyBase L G

/-- Rectangular-volume base of the square output from one proportional `112` repetition. -/
noncomputable def cw112CyclicVolumeBase (q L G : ℕ) : ℝ :=
  (q : ℝ) ^ (3 * (4 * G + 2 * L))

/-- Common square side extracted at proportional repetition `k`. -/
abbrev cw112AsymptoticSquareSide (q L G k : ℕ) : ℕ :=
  q ^ ((4 * G + 2 * L) * k)

/-- Explicit subexponential loss collecting the two side method-of-types losses, the Z marginal
upper loss, the constant finite-counting factor, and the Behrend square-root exponential. -/
noncomputable def cw112CyclicLoss (L G k : ℕ) : ℝ :=
  8192 * WordType.proportionalMultinomialLoss
      (cw112SideMarginalType L G) k ^ 2 *
    WordType.proportionalMultinomialUpperLoss
      (cw112ZMarginalType L G) k *
    Real.exp ((8 * (8 + 4 * (L + G)) : ℕ) *
      √(((k + 1 : ℕ) : ℝ)))

/-- Scaling `(L,G)` by `k` is exactly `WordType.proportionalCounts` for the binary side
marginal. -/
theorem cw112SideMarginalType_mul (L G k : ℕ) :
    cw112SideMarginalType (L * k) (G * k) =
      WordType.proportionalCounts (cw112SideMarginalType L G) k := by
  funext s
  cases s <;>
    simp [cw112SideMarginalType, WordType.proportionalCounts, Nat.add_mul]

/-- Scaling `(L,G)` by `k` is exactly `WordType.proportionalCounts` for the ternary Z
marginal. -/
theorem cw112ZMarginalType_mul (L G k : ℕ) :
    cw112ZMarginalType (L * k) (G * k) =
      WordType.proportionalCounts (cw112ZMarginalType L G) k := by
  funext z
  cases z <;>
    simp [cw112ZMarginalType, WordType.proportionalCounts, Nat.mul_assoc]

/-- The proportional word length agrees with the fixed cyclic stride. -/
theorem cw112CyclicStride_mul (L G k : ℕ) :
    2 * (L * k + G * k) = cw112CyclicStride L G * k := by
  simp only [cw112CyclicStride]
  ring

/-- Exact side-marginal cardinality in proportional method-of-types notation. -/
theorem card_cw112SideMarginalTypeClass_mul
    {L G k : ℕ} (hL : 0 < L) (hk : 0 < k) :
    (WordType.typeClass (cw112TypeDepth (L * k) (G * k) + 1)
      (cw112SideMarginalType (L * k) (G * k))).card =
        Nat.multinomial Finset.univ
          (WordType.proportionalCounts (cw112SideMarginalType L G) k) := by
  have hscaled : 0 < L * k + G * k := by positivity
  rw [WordType.card_typeClass_eq_multinomial _ (by
    simpa only [cw112MarginalType] using
      (cw112MarginalType_mem_types hscaled .X))]
  rw [cw112SideMarginalType_mul]

/-- Exact Z-marginal cardinality in proportional method-of-types notation. -/
theorem card_cw112ZMarginalTypeClass_mul
    {L G k : ℕ} (hL : 0 < L) (hk : 0 < k) :
    (WordType.typeClass (cw112TypeDepth (L * k) (G * k) + 1)
      (cw112ZMarginalType (L * k) (G * k))).card =
        Nat.multinomial Finset.univ
          (WordType.proportionalCounts (cw112ZMarginalType L G) k) := by
  have hscaled : 0 < L * k + G * k := by positivity
  rw [WordType.card_typeClass_eq_multinomial _ (by
    simpa only [cw112MarginalType] using
      (cw112MarginalType_mem_types hscaled .Z))]
  rw [cw112ZMarginalType_mul]

/-- Both marginal method-of-types bases are strictly positive. -/
theorem cw112MarginalEntropyBases_pos (L G : ℕ) :
    0 < cw112SideEntropyBase L G ∧ 0 < cw112ZEntropyBase L G := by
  have hfactorial (d : ℕ) : 0 < WordType.factorialEntropyTerm d := by
    cases d with
    | zero => simp [WordType.factorialEntropyTerm]
    | succ d =>
        unfold WordType.factorialEntropyTerm
        positivity
  have hside : 0 < cw112SideEntropyBase L G := by
    unfold cw112SideEntropyBase WordType.proportionalEntropyBase
    exact div_pos (hfactorial _)
      (Finset.prod_pos fun i _ ↦ hfactorial _)
  have hz : 0 < cw112ZEntropyBase L G := by
    unfold cw112ZEntropyBase WordType.proportionalEntropyBase
    exact div_pos (hfactorial _)
      (Finset.prod_pos fun i _ ↦ hfactorial _)
  exact ⟨hside, hz⟩

/-- All cyclic asymptotic bases are positive for positive `q`. -/
theorem cw112CyclicBases_pos
    {q L G : ℕ} (hq : 0 < q) :
    0 < cw112CyclicCopyBase L G ∧
      0 < cw112CyclicVolumeBase q L G := by
  obtain ⟨hside, hz⟩ := cw112MarginalEntropyBases_pos L G
  constructor
  · unfold cw112CyclicCopyBase
    positivity
  · unfold cw112CyclicVolumeBase
    positivity

/-- The explicit finite `112` loss is subexponential in the proportional repetition. -/
theorem cw112CyclicLoss_subexponential (L G : ℕ) :
    Growth.Subexponential (cw112CyclicLoss L G) := by
  have hside :=
    WordType.proportionalMultinomialLoss_subexponential
      (cw112SideMarginalType L G)
  have hz :=
    WordType.proportionalMultinomialUpperLoss_subexponential
      (cw112ZMarginalType L G)
  have hexp := Growth.Subexponential.exp_mul_sqrt_succ
    (a := (8 * (8 + 4 * (L + G)) : ℕ)) (by positivity)
  have hproduct := (hside.mul hside).mul hz |>.mul hexp
  convert hproduct.const_mul (show (0 : ℝ) ≤ 8192 by norm_num) using 1
  funext k
  unfold cw112CyclicLoss
  push_cast
  ring

/-- The explicit loss is strictly positive at every positive repetition. -/
theorem cw112CyclicLoss_pos
    {L G k : ℕ} (hL : 0 < L) (hG : 0 < G) (hk : 0 < k) :
    0 < cw112CyclicLoss L G k := by
  unfold cw112CyclicLoss WordType.proportionalMultinomialLoss
    WordType.proportionalMultinomialUpperLoss WordType.profileMass
  have hside : 0 < ∏ i, (cw112SideMarginalType L G i : ℝ) := by
    apply Finset.prod_pos
    intro i _
    cases i <;> simp [cw112SideMarginalType]
    all_goals positivity
  have hzMass : 0 < ∑ i, cw112ZMarginalType L G i := by
    apply Finset.sum_pos
    · intro i _
      cases i <;> simp [cw112ZMarginalType]
      all_goals positivity
    · exact ⟨CW112ZBlock.firstCorner, Finset.mem_univ _⟩
  positivity

section FiniteData

variable (K : Type u) [CommRing K]

/-- Prime-field output selected for one positive proportional repetition.

The structure retains only numerical data and the final semantic degeneration.  Hash seeds,
progression-free sets, occupied Z fibers, and C-tensor antidiagonals have all been eliminated by
`CoppersmithWinograd112GlobalCounting`. -/
structure CW112PrimeExtractionData (q L G k : ℕ) where
  modulus : ℕ
  copies : ℕ
  modulus_prime : modulus.Prime
  modulus_lower : 8 * cw112XYFiberSize (L * k) (G * k) < modulus
  modulus_upper : modulus ≤ 16 * cw112XYFiberSize (L * k) (G * k)
  count_bound :
    9 * (cw112TypeWords (L * k) (G * k)).card ^ 2 *
        rothNumberNat (modulus / 2) ^ 2 ≤
      32 * modulus ^ 4 *
        (WordType.typeClass (cw112TypeDepth (L * k) (G * k) + 1)
          (cw112ZMarginalType (L * k) (G * k))).card * copies
  degenerates :
    PolynomialDegenerates
      (cw112PowerCyclicProduct K q (L * k) (G * k))
      (matrixMultiplicationDirectSum (ι := Fin copies) K
        (fun _ ↦ cw112FiniteLeafSquareSide q (L * k) (G * k))
        (fun _ ↦ cw112FiniteLeafSquareSide q (L * k) (G * k))
        (fun _ ↦ cw112FiniteLeafSquareSide q (L * k) (G * k)))
  copies_pos : 0 < copies

/-- Every positive proportional repetition has prime-field finite extraction data. -/
theorem exists_cw112PrimeExtractionData
    {q L G k : ℕ} (hL : 0 < L) (hk : 0 < k) :
    Nonempty (CW112PrimeExtractionData K q L G k) := by
  have hscaled : 0 < L * k + G * k := by positivity
  obtain ⟨M, copies, hprime, hlower, hupper, hcount, hdeg⟩ :=
    exists_prime_cw112_flatSquareFamily_with_marginal_count
      K q hscaled
  have hd : 0 < cw112XYFiberSize (L * k) (G * k) := by
    rw [cw112XYFiberSize_eq_choose_sq hscaled]
    have hchoose : 0 < Nat.choose (L * k + G * k) (L * k) :=
      Nat.choose_pos (Nat.le_add_right (L * k) (G * k))
    positivity
  have hM : 3 ≤ M := by omega
  have hhalf : 0 < M / 2 := by omega
  have hrothReal :
      (((M / 2 : ℕ) : ℝ)) *
          Real.exp (-4 * √(Real.log (((M / 2 : ℕ) : ℝ)))) ≤
        (rothNumberNat (M / 2) : ℝ) :=
    Behrend.roth_lower_bound
  have hroth : 0 < rothNumberNat (M / 2) := by
    have hpositive :
        0 < (((M / 2 : ℕ) : ℝ)) *
          Real.exp (-4 * √(Real.log (((M / 2 : ℕ) : ℝ)))) := by
      exact mul_pos (by exact_mod_cast hhalf) (Real.exp_pos _)
    exact_mod_cast lt_of_lt_of_le hpositive hrothReal
  have hwords : 0 < (cw112TypeWords (L * k) (G * k)).card :=
    Finset.card_pos.mpr (cw112TypeWords_nonempty hscaled)
  have hcopies : 0 < copies := by
    by_contra hnot
    have hzero : copies = 0 := Nat.eq_zero_of_not_pos hnot
    rw [hzero] at hcount
    simp only [mul_zero] at hcount
    have hleft :
        0 < 9 * (cw112TypeWords (L * k) (G * k)).card ^ 2 *
          rothNumberNat (M / 2) ^ 2 := by positivity
    omega
  exact ⟨⟨M, copies, hprime, hlower, hupper, hcount, hdeg, hcopies⟩⟩

/-- Canonically chosen finite extraction data.  Its proof argument is propositionally irrelevant,
so downstream sequence functions do not depend on a choice of positivity proof. -/
noncomputable def cw112PrimeExtractionData
    (q L G k : ℕ) (hL : 0 < L) (hk : 0 < k) :
    CW112PrimeExtractionData K q L G k :=
  Classical.choice (exists_cw112PrimeExtractionData K hL hk)

/-- Copy-count sequence used by the cyclic asymptotic extraction.  The irrelevant zero index is
assigned one copy; all semantic and growth fields are required only at positive repetitions. -/
noncomputable def cw112AsymptoticCopies
    (q L G : ℕ) (hL : 0 < L) (k : ℕ) : ℕ :=
  if hk : 0 < k then (cw112PrimeExtractionData K q L G k hL hk).copies else 1

@[simp] theorem cw112AsymptoticCopies_of_pos
    (q L G : ℕ) (hL : 0 < L) {k : ℕ} (hk : 0 < k) :
    cw112AsymptoticCopies K q L G hL k =
      (cw112PrimeExtractionData K q L G k hL hk).copies := by
  simp only [cw112AsymptoticCopies, dif_pos hk]

/-- Every positive entry of the chosen copy-count sequence is nonzero. -/
theorem cw112AsymptoticCopies_pos
    (q L G : ℕ) (hL : 0 < L) {k : ℕ} (hk : 0 < k) :
    0 < cw112AsymptoticCopies K q L G hL k := by
  rw [cw112AsymptoticCopies_of_pos K q L G hL hk]
  exact (cw112PrimeExtractionData K q L G k hL hk).copies_pos

/-- The square-root exponential lost to the progression-free set is bounded uniformly by the
explicit term in `cw112CyclicLoss`.

Proof sketch: the X/Y competitor fiber is a square of a binomial coefficient and hence at most
`2^(stride*k)`.  Bertrand gives `M ≤ 16d`, so `M/2 ≤ 8·2^(stride*k)`.  Taking logarithms and using
the coarse bounds `log 8 ≤ 8` and `log 2 ≤ 2` gives a linear function of `k`; its square root is
at most `(8 + 4(L+G)) sqrt(k+1)`. -/
theorem cw112_behrendExponent_le
    {L G k M : ℕ} (hL : 0 < L) (hk : 0 < k) (hM : 3 ≤ M)
    (hupper : M ≤ 16 * cw112XYFiberSize (L * k) (G * k)) :
    Real.exp (8 * √(Real.log (((M / 2 : ℕ) : ℝ)))) ≤
      Real.exp (((8 * (8 + 4 * (L + G)) : ℕ) : ℝ) *
        √(((k + 1 : ℕ) : ℝ))) := by
  have hscaled : 0 < L * k + G * k := by positivity
  have hdUpper :
      cw112XYFiberSize (L * k) (G * k) ≤
        2 ^ (cw112CyclicStride L G * k) := by
    rw [cw112XYFiberSize_eq_choose_sq hscaled]
    calc
      Nat.choose (L * k + G * k) (L * k) ^ 2 ≤
          (2 ^ (L * k + G * k)) ^ 2 :=
        Nat.pow_le_pow_left (Nat.choose_le_two_pow _ _) 2
      _ = 2 ^ (cw112CyclicStride L G * k) := by
        rw [← pow_mul]
        congr 1
        simp only [cw112CyclicStride]
        ring
  have hhalfPos : 0 < M / 2 := by omega
  have hhalfUpperNat :
      M / 2 ≤ 8 * 2 ^ (cw112CyclicStride L G * k) := by
    have hM' := hupper.trans (Nat.mul_le_mul_left 16 hdUpper)
    omega
  have hhalfUpper :
      (((M / 2 : ℕ) : ℝ)) ≤
        ((8 * 2 ^ (cw112CyclicStride L G * k) : ℕ) : ℝ) := by
    exact_mod_cast hhalfUpperNat
  have hlog8 : Real.log (8 : ℝ) ≤ 8 :=
    (Real.log_le_sub_one_of_pos (by norm_num)).trans (by norm_num)
  have hlog2 : Real.log (2 : ℝ) ≤ 2 :=
    (Real.log_le_sub_one_of_pos (by norm_num)).trans (by norm_num)
  let A : ℝ := (8 + 4 * (L + G) : ℕ)
  have hlog :
      Real.log (((M / 2 : ℕ) : ℝ)) ≤ A * ((k + 1 : ℕ) : ℝ) := by
    calc
      Real.log (((M / 2 : ℕ) : ℝ)) ≤
          Real.log ((8 * 2 ^ (cw112CyclicStride L G * k) : ℕ) : ℝ) :=
        Real.log_le_log (by exact_mod_cast hhalfPos) hhalfUpper
      _ = Real.log (8 : ℝ) +
          ((cw112CyclicStride L G * k : ℕ) : ℝ) * Real.log (2 : ℝ) := by
        norm_num only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow]
        rw [Real.log_mul (by norm_num) (pow_ne_zero _ (by norm_num)), Real.log_pow]
        simp only [cw112CyclicStride]
        push_cast
        ring
      _ ≤ 8 + ((cw112CyclicStride L G * k : ℕ) : ℝ) * 2 :=
        add_le_add hlog8
          (mul_le_mul_of_nonneg_left hlog2 (Nat.cast_nonneg _))
      _ ≤ A * ((k + 1 : ℕ) : ℝ) := by
        dsimp [A, cw112CyclicStride]
        push_cast
        nlinarith [Nat.cast_nonneg (α := ℝ) k,
          Nat.cast_nonneg (α := ℝ) L, Nat.cast_nonneg (α := ℝ) G]
  have hA : 1 ≤ A := by
    dsimp [A]
    exact_mod_cast (show 1 ≤ 8 + 4 * (L + G) by omega)
  have hsqrt :
      √(Real.log (((M / 2 : ℕ) : ℝ))) ≤
        A * √(((k + 1 : ℕ) : ℝ)) := by
    calc
      √(Real.log (((M / 2 : ℕ) : ℝ))) ≤
          √(A * ((k + 1 : ℕ) : ℝ)) := Real.sqrt_le_sqrt hlog
      _ = √A * √(((k + 1 : ℕ) : ℝ)) := by
        rw [Real.sqrt_mul (by positivity : 0 ≤ A)]
      _ ≤ A * √(((k + 1 : ℕ) : ℝ)) := by
        exact mul_le_mul_of_nonneg_right
          (Real.sqrt_le_self_iff.mpr (Or.inr hA)) (Real.sqrt_nonneg _)
  apply Real.exp_le_exp.mpr
  have := mul_le_mul_of_nonneg_left hsqrt (show (0 : ℝ) ≤ 8 by norm_num)
  dsimp [A] at this ⊢
  push_cast at this ⊢
  nlinarith

/-- Division-free finite counting reduced to its three asymptotically meaningful factors.

If `P` is the balanced side-marginal type-class size, `Z` is the shared-Z type-class size, and
`C` is the extracted square count, then

`P² · exp(-8 sqrt(log(M/2))) ≤ 8192 · Z · C`.

Proof sketch: Behrend gives `|B| ≥ (M/3) exp(-4 sqrt(log(M/2)))`.  Substitute this twice in the
exact hashing count.  The joint type-class size is exactly `P·d`, while Bertrand gives `M≤16d`;
cancelling the positive factors `M²` and `d²` leaves the displayed inequality. -/
theorem cw112_sideSq_mul_behrend_le
    {q L G k : ℕ} (hL : 0 < L) (hk : 0 < k) :
    let data := cw112PrimeExtractionData K q L G k hL hk
    let P := (WordType.typeClass (cw112TypeDepth (L * k) (G * k) + 1)
      (cw112SideMarginalType (L * k) (G * k))).card
    let Z := (WordType.typeClass (cw112TypeDepth (L * k) (G * k) + 1)
      (cw112ZMarginalType (L * k) (G * k))).card
    (P : ℝ) ^ 2 *
        Real.exp (-8 * √(Real.log (((data.modulus / 2 : ℕ) : ℝ)))) ≤
      8192 * (Z : ℝ) * (data.copies : ℝ) := by
  dsimp only
  let data := cw112PrimeExtractionData K q L G k hL hk
  let M := data.modulus
  let copies := data.copies
  let d := cw112XYFiberSize (L * k) (G * k)
  let S := (cw112TypeWords (L * k) (G * k)).card
  let P := (WordType.typeClass (cw112TypeDepth (L * k) (G * k) + 1)
    (cw112SideMarginalType (L * k) (G * k))).card
  let Z := (WordType.typeClass (cw112TypeDepth (L * k) (G * k) + 1)
    (cw112ZMarginalType (L * k) (G * k))).card
  have hscaled : 0 < L * k + G * k := by positivity
  have hd : 0 < d := by
    dsimp [d]
    rw [cw112XYFiberSize_eq_choose_sq hscaled]
    have hchoose : 0 < Nat.choose (L * k + G * k) (L * k) :=
      Nat.choose_pos (Nat.le_add_right (L * k) (G * k))
    positivity
  have hM : 3 ≤ M := by
    have := data.modulus_lower
    dsimp [M, d] at this ⊢
    omega
  have hhalf : 0 < M / 2 := by omega
  have hSPNat : P * d = S := by
    simpa only [P, d, S] using cw112XYMarginalCard_mul_fiberSize hscaled
  have hSP : (P : ℝ) * (d : ℝ) = (S : ℝ) := by
    exact_mod_cast hSPNat
  have hhalfLowerNat : M ≤ 3 * (M / 2) := by omega
  have hhalfLower : (M : ℝ) / 3 ≤ ((M / 2 : ℕ) : ℝ) := by
    rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 3)]
    exact_mod_cast (by simpa [Nat.mul_comm] using hhalfLowerNat)
  have hroth : (((M / 2 : ℕ) : ℝ)) *
      Real.exp (-4 * √(Real.log (((M / 2 : ℕ) : ℝ)))) ≤
        (rothNumberNat (M / 2) : ℝ) := Behrend.roth_lower_bound
  have hrothLower :
      (M : ℝ) / 3 *
          Real.exp (-4 * √(Real.log (((M / 2 : ℕ) : ℝ)))) ≤
        (rothNumberNat (M / 2) : ℝ) := by
    exact (mul_le_mul_of_nonneg_right hhalfLower (Real.exp_nonneg _)).trans hroth
  have hcountReal :
      9 * (S : ℝ) ^ 2 * (rothNumberNat (M / 2) : ℝ) ^ 2 ≤
        32 * (M : ℝ) ^ 4 * (Z : ℝ) * (copies : ℝ) := by
    exact_mod_cast data.count_bound
  have hexpSq :
      Real.exp (-4 * √(Real.log (((M / 2 : ℕ) : ℝ)))) ^ 2 =
        Real.exp (-8 * √(Real.log (((M / 2 : ℕ) : ℝ)))) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hraw :
      (P : ℝ) ^ 2 * (d : ℝ) ^ 2 * (M : ℝ) ^ 2 *
          Real.exp (-8 * √(Real.log (((M / 2 : ℕ) : ℝ)))) ≤
        32 * (M : ℝ) ^ 4 * (Z : ℝ) * (copies : ℝ) := by
    calc
      _ = 9 * (S : ℝ) ^ 2 *
          ((M : ℝ) / 3 *
            Real.exp (-4 * √(Real.log (((M / 2 : ℕ) : ℝ))))) ^ 2 := by
        rw [← hSP, ← hexpSq]
        ring
      _ ≤ 9 * (S : ℝ) ^ 2 * (rothNumberNat (M / 2) : ℝ) ^ 2 := by
        gcongr
      _ ≤ _ := hcountReal
  have hcancelM :
      (P : ℝ) ^ 2 * (d : ℝ) ^ 2 *
          Real.exp (-8 * √(Real.log (((M / 2 : ℕ) : ℝ)))) ≤
        32 * (M : ℝ) ^ 2 * (Z : ℝ) * (copies : ℝ) := by
    apply (mul_le_mul_iff_left₀ (show 0 < (M : ℝ) ^ 2 by positivity)).mp
    calc
      ((P : ℝ) ^ 2 * (d : ℝ) ^ 2 *
          Real.exp (-8 * √(Real.log (((M / 2 : ℕ) : ℝ))))) * (M : ℝ) ^ 2 =
        (P : ℝ) ^ 2 * (d : ℝ) ^ 2 * (M : ℝ) ^ 2 *
          Real.exp (-8 * √(Real.log (((M / 2 : ℕ) : ℝ)))) := by ring
      _ ≤ 32 * (M : ℝ) ^ 4 * (Z : ℝ) * (copies : ℝ) := hraw
      _ = (32 * (M : ℝ) ^ 2 * (Z : ℝ) * (copies : ℝ)) *
          (M : ℝ) ^ 2 := by ring
  have hMupper : (M : ℝ) ≤ 16 * (d : ℝ) := by
    exact_mod_cast data.modulus_upper
  have hwithUpper :
      (P : ℝ) ^ 2 * (d : ℝ) ^ 2 *
          Real.exp (-8 * √(Real.log (((M / 2 : ℕ) : ℝ)))) ≤
        8192 * (d : ℝ) ^ 2 * (Z : ℝ) * (copies : ℝ) := by
    apply hcancelM.trans
    calc
      32 * (M : ℝ) ^ 2 * (Z : ℝ) * (copies : ℝ) ≤
          32 * (16 * (d : ℝ)) ^ 2 * (Z : ℝ) * (copies : ℝ) := by
        gcongr
      _ = _ := by ring
  apply (mul_le_mul_iff_left₀ (show 0 < (d : ℝ) ^ 2 by positivity)).mp
  calc
    ((P : ℝ) ^ 2 *
        Real.exp (-8 * √(Real.log (((M / 2 : ℕ) : ℝ)))) * (d : ℝ) ^ 2) =
      (P : ℝ) ^ 2 * (d : ℝ) ^ 2 *
        Real.exp (-8 * √(Real.log (((M / 2 : ℕ) : ℝ)))) := by ring
    _ ≤ 8192 * (d : ℝ) ^ 2 * (Z : ℝ) * (copies : ℝ) := hwithUpper
    _ = (8192 * (Z : ℝ) * (copies : ℝ)) * (d : ℝ) ^ 2 := by ring

/-- The chosen finite extraction realizes the declared copy base up to
`cw112CyclicLoss`.

This is the complete proportional counting theorem for the exceptional constituent.  It combines
the exact finite extraction, the lower method-of-types estimate for each of the two balanced side
marginals, the upper estimate for the shared Z marginal, and the proved Behrend exponent bound. -/
theorem cw112CyclicCopyBase_pow_le_loss_mul_copies
    {q L G k : ℕ} (hL : 0 < L) (hG : 0 < G) (hk : 0 < k) :
    cw112CyclicCopyBase L G ^ k ≤
      cw112CyclicLoss L G k *
        (cw112AsymptoticCopies K q L G hL k : ℝ) := by
  letI : Nonempty CW112Side := ⟨.first⟩
  letI : Nonempty CW112ZBlock := ⟨.firstCorner⟩
  let data := cw112PrimeExtractionData K q L G k hL hk
  let M := data.modulus
  let copies := data.copies
  let P := (WordType.typeClass (cw112TypeDepth (L * k) (G * k) + 1)
    (cw112SideMarginalType (L * k) (G * k))).card
  let Z := (WordType.typeClass (cw112TypeDepth (L * k) (G * k) + 1)
    (cw112ZMarginalType (L * k) (G * k))).card
  let sideLoss := WordType.proportionalMultinomialLoss
    (cw112SideMarginalType L G) k
  let zLoss := WordType.proportionalMultinomialUpperLoss
    (cw112ZMarginalType L G) k
  let bigExponent : ℝ := ((8 * (8 + 4 * (L + G)) : ℕ) : ℝ) *
    √(((k + 1 : ℕ) : ℝ))
  have hsideProfile : ∀ i, 0 < cw112SideMarginalType L G i := by
    intro i
    cases i <;> simp [cw112SideMarginalType]
    all_goals omega
  have hzProfile : ∀ i, 0 < cw112ZMarginalType L G i := by
    intro i
    cases i <;> simp [cw112ZMarginalType]
    all_goals omega
  have hside :=
    WordType.proportionalEntropyBase_pow_le_loss_mul_multinomial
      (cw112SideMarginalType L G) k hsideProfile hk
  rw [← card_cw112SideMarginalTypeClass_mul hL hk] at hside
  change cw112SideEntropyBase L G ^ k ≤ sideLoss * (P : ℝ) at hside
  have hz :=
    WordType.multinomial_le_upperLoss_mul_proportionalEntropyBase_pow
      (cw112ZMarginalType L G) k hzProfile hk
  rw [← card_cw112ZMarginalTypeClass_mul hL hk] at hz
  change (Z : ℝ) ≤ zLoss * cw112ZEntropyBase L G ^ k at hz
  have hfinite := cw112_sideSq_mul_behrend_le K (q := q) (G := G) hL hk
  change (P : ℝ) ^ 2 *
      Real.exp (-8 * √(Real.log (((M / 2 : ℕ) : ℝ)))) ≤
    8192 * (Z : ℝ) * (copies : ℝ) at hfinite
  have hd : 0 < cw112XYFiberSize (L * k) (G * k) := by
    have hscaled : 0 < L * k + G * k := by positivity
    rw [cw112XYFiberSize_eq_choose_sq hscaled]
    have hchoose : 0 < Nat.choose (L * k + G * k) (L * k) :=
      Nat.choose_pos (Nat.le_add_right (L * k) (G * k))
    positivity
  have hM : 3 ≤ M := by
    have hlower := data.modulus_lower
    dsimp [M] at hlower ⊢
    omega
  have hexpUpper :
      Real.exp (8 * √(Real.log (((M / 2 : ℕ) : ℝ)))) ≤
        Real.exp bigExponent := by
    simpa only [bigExponent, M] using
      (cw112_behrendExponent_le hL hk hM data.modulus_upper)
  have hexpCancel :
      Real.exp (8 * √(Real.log (((M / 2 : ℕ) : ℝ)))) *
          Real.exp (-8 * √(Real.log (((M / 2 : ℕ) : ℝ)))) = 1 := by
    rw [← Real.exp_add]
    convert Real.exp_zero using 1
    ring
  have hP :
      (P : ℝ) ^ 2 ≤
        8192 * (Z : ℝ) * (copies : ℝ) * Real.exp bigExponent := by
    calc
      (P : ℝ) ^ 2 =
          Real.exp (8 * √(Real.log (((M / 2 : ℕ) : ℝ)))) *
            ((P : ℝ) ^ 2 *
              Real.exp (-8 * √(Real.log (((M / 2 : ℕ) : ℝ))))) := by
        rw [show Real.exp (8 * √(Real.log (((M / 2 : ℕ) : ℝ)))) *
            ((P : ℝ) ^ 2 *
              Real.exp (-8 * √(Real.log (((M / 2 : ℕ) : ℝ))))) =
            (P : ℝ) ^ 2 *
              (Real.exp (8 * √(Real.log (((M / 2 : ℕ) : ℝ)))) *
                Real.exp (-8 * √(Real.log (((M / 2 : ℕ) : ℝ))))) by ring,
          hexpCancel, mul_one]
      _ ≤ Real.exp (8 * √(Real.log (((M / 2 : ℕ) : ℝ)))) *
          (8192 * (Z : ℝ) * (copies : ℝ)) := by gcongr
      _ ≤ Real.exp bigExponent *
          (8192 * (Z : ℝ) * (copies : ℝ)) := by gcongr
      _ = _ := by ring
  have hsideSq :
      (cw112SideEntropyBase L G ^ 2) ^ k ≤
        sideLoss ^ 2 * (P : ℝ) ^ 2 := by
    calc
      (cw112SideEntropyBase L G ^ 2) ^ k =
          (cw112SideEntropyBase L G ^ k) ^ 2 := by
        simp only [pow_two, mul_pow]
      _ ≤ (sideLoss * (P : ℝ)) ^ 2 := by
        simpa only [pow_two] using
          (mul_self_le_mul_self
            (pow_nonneg (cw112MarginalEntropyBases_pos L G).1.le k) hside)
      _ = sideLoss ^ 2 * (P : ℝ) ^ 2 := by ring
  have hraw :
      (cw112SideEntropyBase L G ^ 2) ^ k ≤
        cw112CyclicLoss L G k * cw112ZEntropyBase L G ^ k *
          (copies : ℝ) := by
    calc
      _ ≤ sideLoss ^ 2 * (P : ℝ) ^ 2 := hsideSq
      _ ≤ sideLoss ^ 2 *
          (8192 * (Z : ℝ) * (copies : ℝ) * Real.exp bigExponent) := by
        gcongr
      _ ≤ sideLoss ^ 2 *
          (8192 * (zLoss * cw112ZEntropyBase L G ^ k) *
            (copies : ℝ) * Real.exp bigExponent) := by
        gcongr
      _ = cw112CyclicLoss L G k * cw112ZEntropyBase L G ^ k *
          (copies : ℝ) := by
        unfold cw112CyclicLoss
        dsimp [sideLoss, zLoss, bigExponent]
        push_cast
        ring
  have hzBase := (cw112MarginalEntropyBases_pos L G).2
  have hproduct :
      cw112CyclicCopyBase L G ^ k * cw112ZEntropyBase L G ^ k =
        (cw112SideEntropyBase L G ^ 2) ^ k := by
    unfold cw112CyclicCopyBase
    rw [div_pow]
    field_simp [hzBase.ne']
  rw [cw112AsymptoticCopies_of_pos K q L G hL hk]
  change cw112CyclicCopyBase L G ^ k ≤
    cw112CyclicLoss L G k * (copies : ℝ)
  apply (mul_le_mul_iff_left₀ (pow_pos hzBase k)).mp
  calc
    cw112CyclicCopyBase L G ^ k * cw112ZEntropyBase L G ^ k =
        (cw112SideEntropyBase L G ^ 2) ^ k := hproduct
    _ ≤ cw112CyclicLoss L G k * cw112ZEntropyBase L G ^ k *
        (copies : ℝ) := hraw
    _ = (cw112CyclicLoss L G k * (copies : ℝ)) *
        cw112ZEntropyBase L G ^ k := by ring

/-- The chosen finite witness has exactly the source exponent and square side required by the
cyclic asymptotic sequence.

Proof sketch: proportional multiplicities give word length `2(L+G)k`, and the finite square side
`q^(4Gk+2Lk)` is `q^((4G+2L)k)`.  After these arithmetic rewrites, the statement is precisely the
degeneration stored in `CW112PrimeExtractionData`. -/
theorem cw112Asymptotic_degenerates
    {q L G k : ℕ} (hL : 0 < L) (hk : 0 < k) :
    PolynomialDegenerates
      (cyclicPowerProduct K (cw112PartitionedTensor K q).realize
        (cw112CyclicStride L G * k))
      (matrixMultiplicationDirectSum
        (ι := Fin (cw112AsymptoticCopies K q L G hL k)) K
        (fun _ ↦ cw112AsymptoticSquareSide q L G k)
        (fun _ ↦ cw112AsymptoticSquareSide q L G k)
        (fun _ ↦ cw112AsymptoticSquareSide q L G k)) := by
  let data := cw112PrimeExtractionData K q L G k hL hk
  have h := data.degenerates
  have hscaled : 0 < L * k + G * k := by positivity
  have hdepth :
      cw112TypeDepth (L * k) (G * k) + 1 =
        cw112CyclicStride L G * k := by
    rw [cw112TypeDepth_add_one hscaled]
    exact cw112CyclicStride_mul L G k
  have hside :
      cw112FiniteLeafSquareSide q (L * k) (G * k) =
        cw112AsymptoticSquareSide q L G k := by
    unfold cw112FiniteLeafSquareSide cw112AsymptoticSquareSide
    congr 1
    ring
  have hsource : Restricts
      (cyclicPowerProduct K (cw112PartitionedTensor K q).realize
        (cw112CyclicStride L G * k))
      (cw112PowerCyclicProduct K q (L * k) (G * k)) := by
    have hiso := Tensor.Isomorphic.cyclicPowerProduct_congr
      (K := K) (cw112PartitionedTensor K q).realize hdepth
    simpa only [cw112PowerCyclicProduct, cyclicPowerProduct] using
      hiso.symm.restricts
  have hcopies :
      cw112AsymptoticCopies K q L G hL k = data.copies := by
    rw [cw112AsymptoticCopies_of_pos K q L G hL hk]
  have houtput : Restricts
      (matrixMultiplicationDirectSum (ι := Fin data.copies) K
        (fun _ ↦ cw112FiniteLeafSquareSide q (L * k) (G * k))
        (fun _ ↦ cw112FiniteLeafSquareSide q (L * k) (G * k))
        (fun _ ↦ cw112FiniteLeafSquareSide q (L * k) (G * k)))
      (matrixMultiplicationDirectSum
        (ι := Fin (cw112AsymptoticCopies K q L G hL k)) K
        (fun _ ↦ cw112AsymptoticSquareSide q L G k)
        (fun _ ↦ cw112AsymptoticSquareSide q L G k)
        (fun _ ↦ cw112AsymptoticSquareSide q L G k)) := by
    unfold matrixMultiplicationDirectSum
    exact Tensor.Restricts.indexedDirectSum_equiv (K := K)
      (finCongr hcopies.symm)
      (fun _ ↦ (Tensor.Isomorphic.matrixMultiplication_congr (K := K)
        hside hside hside).restricts)
  exact (PolynomialDegenerates.of_restricts hsource).trans
    (h.trans (PolynomialDegenerates.of_restricts houtput))

end FiniteData

end AlgebraicComplexity.Examples
