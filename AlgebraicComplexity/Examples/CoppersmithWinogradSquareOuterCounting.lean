/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinogradSquareEntropy
import Mathlib.Combinatorics.Additive.AP.Three.Behrend
import Mathlib.NumberTheory.Bertrand

/-!
# Outer counting for the Coppersmith--Winograd square

This module isolates the part of the CW-square asymptotic argument that depends only on the
fifteen-address outer partition.  It defines the visible five-coordinate marginal entropy base,
gives its symbolic weighted-log formula for numerical clients, proves the exact equal-fiber
identities used to size an affine-hashing field, and derives the finite Behrend/hash estimate
relating a marginal type class to the number of isolated outer survivors.

Nothing here mentions the exceptional `(112)` leaf, matrix-multiplication dimensions,
Schönhage's inequality, or a numerical parameter choice.  The modern symmetric value proof and
the older flattened-inner proof therefore share this boundary without importing one another.

Primary source: Don Coppersmith and Shmuel Winograd, *Matrix Multiplication via Arithmetic
Progressions*, Journal of Symbolic Computation 9(3), 251--280 (1990), Sections 6--7,
DOI 10.1016/S0747-7171(08)80013-2.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor
open scoped BigOperators

universe u

/-! ## Outer marginal and exact fiber scale -/

/-- Primitive five-coordinate marginal profile of the symmetric CW-square joint type. -/
abbrev cwSquareBaseMarginal (a b c d : ℕ) : Fin 5 → ℕ :=
  cwSquareMarginalType a b c d 1

/-- Exponential method-of-types base of the common outer marginal. -/
noncomputable def cwSquareOuterEntropyBase (a b c d : ℕ) : ℝ :=
  WordType.proportionalEntropyBase (cwSquareBaseMarginal a b c d)

/-- The logarithm of the outer entropy base is the weighted logarithm of the five marginal
ratios.

In conventional notation, if `A_i` are the five entries of `cwSquareBaseMarginal` and
`N = cwSquareStride a b c d`, this says

```text
log outerBase = sum_i A_i log (N / A_i).
```

Proof sketch: `WordType.log_proportionalEntropyBase` identifies the logarithm with `N` times
the Shannon entropy of the normalized integral profile.  Positivity permits expanding each
`negMulLog (A_i/N)` as `(A_i/N) log (N/A_i)`; distributing `N` through the finite sum cancels
the denominator.  Numerical CW clients should specialize this theorem rather than re-expand the
five entropy terms independently. -/
theorem log_cwSquareOuterEntropyBase
    {a b c d : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    Real.log (cwSquareOuterEntropyBase a b c d) =
      ∑ i, (cwSquareBaseMarginal a b c d i : ℝ) *
        Real.log ((cwSquareStride a b c d : ℝ) /
          (cwSquareBaseMarginal a b c d i : ℝ)) := by
  classical
  have hentry : ∀ i, 0 < cwSquareBaseMarginal a b c d i := by
    intro i
    fin_cases i <;>
      simp [cwSquareBaseMarginal, cwSquareMarginalType] <;> omega
  have hstride : 0 < cwSquareStride a b c d := by
    unfold cwSquareStride
    positivity
  have hmass : WordType.profileMass (cwSquareBaseMarginal a b c d) =
      cwSquareStride a b c d := by
    simpa only [cwSquareBaseMarginal, WordType.profileMass, Nat.mul_one] using
      sum_cwSquareMarginalType a b c d 1
  have hterm (i : Fin 5) :
      ((cwSquareStride a b c d : ℕ) : ℝ) *
          Real.negMulLog
            ((cwSquareBaseMarginal a b c d i : ℝ) /
              (cwSquareStride a b c d : ℝ)) =
        (cwSquareBaseMarginal a b c d i : ℝ) *
          Real.log ((cwSquareStride a b c d : ℝ) /
            (cwSquareBaseMarginal a b c d i : ℝ)) := by
    rw [Real.negMulLog_eq_neg]
    change ((cwSquareStride a b c d : ℕ) : ℝ) *
        (-(((cwSquareBaseMarginal a b c d i : ℕ) : ℝ) /
          ((cwSquareStride a b c d : ℕ) : ℝ) *
          Real.log (((cwSquareBaseMarginal a b c d i : ℕ) : ℝ) /
            ((cwSquareStride a b c d : ℕ) : ℝ)))) = _
    rw [Real.log_div
        (by exact_mod_cast (hentry i).ne') (by exact_mod_cast hstride.ne'),
      Real.log_div
        (by exact_mod_cast hstride.ne') (by exact_mod_cast (hentry i).ne')]
    field_simp [show ((cwSquareStride a b c d : ℕ) : ℝ) ≠ 0 by
      exact_mod_cast hstride.ne']
    ring
  rw [cwSquareOuterEntropyBase,
    WordType.log_proportionalEntropyBase _ hentry]
  unfold WordType.profileEntropyNats
  rw [hmass, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ ↦ hterm i

/-- The displayed marginal at repetition `k` is exactly the proportional scaling of the
primitive marginal. -/
theorem cwSquareMarginalType_eq_proportionalCounts (a b c d k : ℕ) :
    cwSquareMarginalType a b c d k =
      WordType.proportionalCounts (cwSquareBaseMarginal a b c d) k := by
  funext i
  fin_cases i <;>
    simp [cwSquareBaseMarginal, cwSquareMarginalType,
      WordType.proportionalCounts, Nat.add_mul]

/-- The outer marginal type class has the expected proportional multinomial cardinality. -/
theorem card_cwSquareMarginalTypeClass_eq_multinomial
    {a b c d k : ℕ} (hstride : 0 < cwSquareStride a b c d) (hk : 0 < k) :
    (WordType.typeClass (cwSquareDepth a b c d k + 1)
      (cwSquareMarginalType a b c d k)).card =
        Nat.multinomial Finset.univ
          (WordType.proportionalCounts (cwSquareBaseMarginal a b c d) k) := by
  rw [WordType.card_typeClass_eq_multinomial _
    (cwSquareMarginalType_mem_types hstride hk)]
  rw [cwSquareMarginalType_eq_proportionalCounts]

/-- The common ambient source-word fiber is nonempty for every positive profile.

Proof sketch: the marked joint type class is nonempty and lies inside the ambient family.  The
exact equal-fiber factorization writes the positive ambient cardinality as the marginal
type-class cardinality times `cwSquareAmbientFiberSize`; hence the latter cannot vanish. -/
theorem cwSquareAmbientFiberSize_pos
    {a b c d k : ℕ} (hstride : 0 < cwSquareStride a b c d) (hk : 0 < k) :
    0 < cwSquareAmbientFiberSize a b c d k := by
  classical
  have hambient : (cwSquareAmbientWords a b c d k).Nonempty :=
    (cwSquareMarkedWords_nonempty hstride hk).mono
      (cwSquareMarkedWords_subset_ambientWords a b c d k)
  obtain ⟨targetFunction, htargetFunction⟩ :=
    WordType.typeClass_nonempty (cwSquareMarginalType a b c d k)
      (cwSquareMarginalType_mem_types hstride hk)
  let target : PositiveWord (Fin 5) (cwSquareDepth a b c d k) :=
    (positiveWordEquiv (Fin 5) (cwSquareDepth a b c d k)).symm targetFunction
  have htarget : positiveWordEquiv (Fin 5) (cwSquareDepth a b c d k) target ∈
      WordType.typeClass (cwSquareDepth a b c d k + 1)
        (cwSquareMarginalType a b c d k) := by
    simpa only [target, Equiv.apply_symm_apply] using htargetFunction
  have hfactor := cwSquareMarginalCard_mul_ambientFiber
    a b c d k .X target htarget
  have hfiber := card_cwSquareAmbient_sourceWordLegFiber
    hstride hk .X target htarget
  rw [hfiber] at hfactor
  have hambientCard : 0 < (cwSquareAmbientWords a b c d k).card :=
    Finset.card_pos.mpr hambient
  have hproductPos : 0 <
      (WordType.typeClass (cwSquareDepth a b c d k + 1)
        (cwSquareMarginalType a b c d k)).card *
          cwSquareAmbientFiberSize a b c d k := by
    rw [hfactor]
    exact hambientCard
  exact pos_of_mul_pos_right hproductPos (Nat.zero_le _)

/-- The common ambient source-word fiber gives an exact factorization of the ambient family.

This packages `cwSquareMarginalCard_mul_ambientFiber` independently of a chosen target word.  It is
the square-construction analogue of the identity
`#(marginal words) * #(one fiber) = #(joint words)`.

Proof sketch: choose any word of the prescribed marginal type, apply the equal-fiber theorem, and
replace the chosen fiber cardinality by `cwSquareAmbientFiberSize`. -/
theorem cwSquareMarginalCard_mul_ambientFiberSize
    {a b c d k : ℕ} (hstride : 0 < cwSquareStride a b c d) (hk : 0 < k) :
    (WordType.typeClass (cwSquareDepth a b c d k + 1)
        (cwSquareMarginalType a b c d k)).card *
      cwSquareAmbientFiberSize a b c d k =
        (cwSquareAmbientWords a b c d k).card := by
  classical
  obtain ⟨targetFunction, htargetFunction⟩ :=
    WordType.typeClass_nonempty (cwSquareMarginalType a b c d k)
      (cwSquareMarginalType_mem_types hstride hk)
  let target : PositiveWord (Fin 5) (cwSquareDepth a b c d k) :=
    (positiveWordEquiv (Fin 5) (cwSquareDepth a b c d k)).symm targetFunction
  have htarget : positiveWordEquiv (Fin 5) (cwSquareDepth a b c d k) target ∈
      WordType.typeClass (cwSquareDepth a b c d k + 1)
        (cwSquareMarginalType a b c d k) := by
    simpa only [target, Equiv.apply_symm_apply] using htargetFunction
  have hfactor := cwSquareMarginalCard_mul_ambientFiber
    a b c d k .X target htarget
  rw [card_cwSquareAmbient_sourceWordLegFiber hstride hk .X target htarget] at hfactor
  exact hfactor

/-- There are fifteen coarse support letters in the CW-square partition. -/
theorem fintypeCard_cwSquareSupport : Fintype.card CWSquareSupport = 15 := by
  simpa using card_cwSquareSupport

/-- The common ambient fiber is no larger than the set of all words on the fifteen-letter square
support.

This coarse bound is used only to control the logarithm of the hashing modulus.  Its exponential
base is ultimately absorbed into a square-root-exponential, hence subexponential, loss. -/
theorem cwSquareAmbientFiberSize_le_supportWords
    {a b c d k : ℕ} (hstride : 0 < cwSquareStride a b c d) (hk : 0 < k) :
    cwSquareAmbientFiberSize a b c d k ≤
      15 ^ (cwSquareStride a b c d * k) := by
  calc
    cwSquareAmbientFiberSize a b c d k ≤
        (cwSquareAmbientWords a b c d k).card := Nat.div_le_self _ _
    _ ≤ Fintype.card
        (PositiveWord CWSquareSupport (cwSquareDepth a b c d k)) :=
      Finset.card_le_univ _
    _ = Fintype.card
        (Fin (cwSquareDepth a b c d k + 1) → CWSquareSupport) :=
      Fintype.card_congr
        (positiveWordEquiv CWSquareSupport (cwSquareDepth a b c d k))
    _ = Fintype.card CWSquareSupport ^ (cwSquareDepth a b c d k + 1) := by
      rw [Fintype.card_fun, Fintype.card_fin]
    _ = 15 ^ (cwSquareStride a b c d * k) := by
      rw [fintypeCard_cwSquareSupport, cwSquareDepth_add_one hstride hk]

/-- A modulus at least five distinguishes the five coarse degree labels in `ZMod M`. -/
theorem cwSquareFieldValue_zmod_injective {M : ℕ} (hM : 5 ≤ M) :
    Function.Injective (cwSquareFieldValue (R := ZMod M)) := by
  intro i j hij
  apply Fin.ext
  exact CharP.natCast_injOn_Iio (R := ZMod M) M
    (i.isLt.trans_le hM) (j.isLt.trans_le hM) hij

/-! ## Explicit finite losses -/

/-- Coefficient of the square-root hashing loss.  The deliberately generous constants come from
bounding `log (M / 2)` after Bertrand's postulate by the size of the fifteen-letter ambient word
space. -/
def cwSquareHashExponentCoefficient (a b c d : ℕ) : ℕ :=
  4 * (12 + 15 * cwSquareStride a b c d)

/-- The number of isolated outer copies recovers the full marginal entropy rate up to the explicit
maximum-entropy and Behrend losses.

This is the quantitative outer half of the limiting CW-square argument.  It is deliberately
stated before using Schönhage's inequality, so the finite combinatorial count can be reused by
other laser-method clients.

Proof sketch: exact equal-fiber counting and the maximum-entropy estimate give
`P * fiber ≤ outerLoss * S`.  Behrend supplies roughly
`(M/2) * exp (-4 * sqrt (log (M/2)))` progression-free values, while the hashing theorem compares
`3 * S * |B|` with `4 * M² * outerCopies`.  Bertrand bounds `M` by `24 * fiber`; cancelling the
positive modulus and fiber leaves the displayed estimate. -/
theorem cwSquareMarginalCard_le_hashLoss_mul_outerCopies
    {a b c d k M outerCopies : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) (hk : 0 < k)
    (hlower : 12 * cwSquareAmbientFiberSize a b c d k < M)
    (hupper : M ≤ 24 * cwSquareAmbientFiberSize a b c d k)
    (hcount : 3 * (cwSquareMarkedWords a b c d k).card * rothNumberNat (M / 2) ≤
      4 * (M * M) * outerCopies) :
    ((WordType.typeClass (cwSquareDepth a b c d k + 1)
        (cwSquareMarginalType a b c d k)).card : ℝ) ≤
      96 * cwSquareOuterTypeLoss a b c d k *
        Real.exp (cwSquareHashExponentCoefficient a b c d *
          √(((k + 1 : ℕ) : ℝ))) *
        outerCopies := by
  let P := (WordType.typeClass (cwSquareDepth a b c d k + 1)
    (cwSquareMarginalType a b c d k)).card
  let fiber := cwSquareAmbientFiberSize a b c d k
  let S := (cwSquareMarkedWords a b c d k).card
  let decay : ℝ := Real.exp (-4 * √(Real.log (((M / 2 : ℕ) : ℝ))))
  have hstride : 0 < cwSquareStride a b c d := by
    unfold cwSquareStride
    positivity
  have hfiberPos : 0 < fiber := cwSquareAmbientFiberSize_pos hstride hk
  have hM : 3 ≤ M := by omega
  have hhalfPos : 0 < M / 2 := by omega
  have hfactorNat : P * fiber = (cwSquareAmbientWords a b c d k).card := by
    simpa [P, fiber] using cwSquareMarginalCard_mul_ambientFiberSize hstride hk
  have hfactor : (P : ℝ) * (fiber : ℝ) =
      ((cwSquareAmbientWords a b c d k).card : ℝ) := by
    exact_mod_cast hfactorNat
  have houter := card_cwSquareAmbientWords_le_outerTypeLoss_mul_markedWords
    ha hb hc hd hk
  have houterLossPos : 0 < cwSquareOuterTypeLoss a b c d k :=
    cwSquareOuterTypeLoss_pos a b c d k
  have hPS : (P : ℝ) * (fiber : ℝ) ≤
      cwSquareOuterTypeLoss a b c d k * (S : ℝ) := by
    rw [hfactor]
    simpa [S] using houter
  have hfiberUpper : fiber ≤ 15 ^ (cwSquareStride a b c d * k) := by
    exact cwSquareAmbientFiberSize_le_supportWords hstride hk
  have hhalfUpperNat : M / 2 ≤ 12 * 15 ^ (cwSquareStride a b c d * k) := by
    omega
  have hhalfUpper : (((M / 2 : ℕ) : ℝ)) ≤
      ((12 * 15 ^ (cwSquareStride a b c d * k) : ℕ) : ℝ) := by
    exact_mod_cast hhalfUpperNat
  have hhalfLowerNat : M ≤ 3 * (M / 2) := by omega
  have hhalfLower : (M : ℝ) / 3 ≤ ((M / 2 : ℕ) : ℝ) := by
    rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 3)]
    exact_mod_cast (by simpa [Nat.mul_comm] using hhalfLowerNat)
  have hlog12 : Real.log (12 : ℝ) ≤ 12 :=
    (Real.log_le_sub_one_of_pos (by norm_num)).trans (by norm_num)
  have hlog15 : Real.log (15 : ℝ) ≤ 15 :=
    (Real.log_le_sub_one_of_pos (by norm_num)).trans (by norm_num)
  have hlogHalf : Real.log (((M / 2 : ℕ) : ℝ)) ≤
      12 + 15 * (cwSquareStride a b c d : ℝ) * (k : ℝ) := by
    calc
      Real.log (((M / 2 : ℕ) : ℝ)) ≤
          Real.log (((12 * 15 ^ (cwSquareStride a b c d * k) : ℕ) : ℝ)) :=
        Real.log_le_log (by exact_mod_cast hhalfPos) hhalfUpper
      _ = Real.log (12 : ℝ) +
          ((cwSquareStride a b c d * k : ℕ) : ℝ) * Real.log (15 : ℝ) := by
        norm_num only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow]
        rw [Real.log_mul (by norm_num) (pow_ne_zero _ (by norm_num)), Real.log_pow]
        push_cast
        ring
      _ ≤ 12 + ((cwSquareStride a b c d * k : ℕ) : ℝ) * 15 :=
        add_le_add hlog12
          (mul_le_mul_of_nonneg_left hlog15 (Nat.cast_nonneg _))
      _ = 12 + 15 * (cwSquareStride a b c d : ℝ) * (k : ℝ) := by
        push_cast
        ring
  have hsqrtHalf : √(Real.log (((M / 2 : ℕ) : ℝ))) ≤
      (12 + 15 * (cwSquareStride a b c d : ℝ)) *
        √(((k + 1 : ℕ) : ℝ)) := by
    calc
      √(Real.log (((M / 2 : ℕ) : ℝ))) ≤
          √(12 + 15 * (cwSquareStride a b c d : ℝ) * (k : ℝ)) :=
        Real.sqrt_le_sqrt hlogHalf
      _ ≤ (12 + 15 * (cwSquareStride a b c d : ℝ)) *
          √(((k + 1 : ℕ) : ℝ)) := by
        apply Real.sqrt_le_iff.mpr
        constructor
        · positivity
        · have hsquare := Real.sq_sqrt
              (show 0 ≤ (((k + 1 : ℕ) : ℝ)) by positivity)
          rw [mul_pow, hsquare]
          push_cast
          have hs : 0 ≤ (cwSquareStride a b c d : ℝ) := by positivity
          have hkReal : 0 ≤ (k : ℝ) := by positivity
          have hfirst :
              12 + 15 * (cwSquareStride a b c d : ℝ) * (k : ℝ) ≤
                (12 + 15 * (cwSquareStride a b c d : ℝ)) * ((k : ℝ) + 1) := by
            nlinarith
          exact hfirst.trans (by
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            nlinarith)
  have hsqrtExponent :
      4 * √(Real.log (((M / 2 : ℕ) : ℝ))) ≤
        (cwSquareHashExponentCoefficient a b c d : ℝ) *
          √(((k + 1 : ℕ) : ℝ)) := by
    calc
      _ ≤ 4 * ((12 + 15 * (cwSquareStride a b c d : ℝ)) *
          √(((k + 1 : ℕ) : ℝ))) :=
        mul_le_mul_of_nonneg_left hsqrtHalf (by norm_num)
      _ = _ := by
        unfold cwSquareHashExponentCoefficient
        push_cast
        ring
  have hdecayPos : 0 < decay := by
    unfold decay
    exact Real.exp_pos _
  have hroth : (((M / 2 : ℕ) : ℝ)) * decay ≤
      (rothNumberNat (M / 2) : ℝ) := by
    simpa only [decay] using (Behrend.roth_lower_bound (N := M / 2))
  have hcountReal : 3 * (S : ℝ) * (rothNumberNat (M / 2) : ℝ) ≤
      4 * ((M : ℝ) * (M : ℝ)) * (outerCopies : ℝ) := by
    exact_mod_cast hcount
  have hrothScaled :
      3 * (S : ℝ) * (((M / 2 : ℕ) : ℝ) * decay) ≤
        3 * (S : ℝ) * (rothNumberNat (M / 2) : ℝ) :=
    mul_le_mul_of_nonneg_left hroth
      (mul_nonneg (by norm_num) (Nat.cast_nonneg S))
  have hhalfScaled :
      3 * (S : ℝ) * ((M : ℝ) / 3 * decay) ≤
        3 * (S : ℝ) * (((M / 2 : ℕ) : ℝ) * decay) := by
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right hhalfLower hdecayPos.le)
      (mul_nonneg (by norm_num) (Nat.cast_nonneg S))
  have hraw :
      (P : ℝ) * (fiber : ℝ) * (M : ℝ) * decay ≤
        cwSquareOuterTypeLoss a b c d k *
          (4 * ((M : ℝ) * (M : ℝ)) * (outerCopies : ℝ)) := by
    calc
      _ = 3 * ((P : ℝ) * (fiber : ℝ)) *
          ((M : ℝ) / 3 * decay) := by ring
      _ ≤ 3 * (cwSquareOuterTypeLoss a b c d k * (S : ℝ)) *
          ((M : ℝ) / 3 * decay) := by
        apply mul_le_mul_of_nonneg_right
        · exact mul_le_mul_of_nonneg_left hPS (by norm_num)
        · positivity
      _ = cwSquareOuterTypeLoss a b c d k *
          (3 * (S : ℝ) * ((M : ℝ) / 3 * decay)) := by ring
      _ ≤ cwSquareOuterTypeLoss a b c d k *
          (3 * (S : ℝ) * (((M / 2 : ℕ) : ℝ) * decay)) := by
        exact mul_le_mul_of_nonneg_left hhalfScaled houterLossPos.le
      _ ≤ cwSquareOuterTypeLoss a b c d k *
          (3 * (S : ℝ) * (rothNumberNat (M / 2) : ℝ)) := by
        exact mul_le_mul_of_nonneg_left hrothScaled houterLossPos.le
      _ ≤ _ := by
        exact mul_le_mul_of_nonneg_left hcountReal
          houterLossPos.le
  have hcancelM :
      (P : ℝ) * (fiber : ℝ) * decay ≤
        4 * cwSquareOuterTypeLoss a b c d k * (M : ℝ) *
          (outerCopies : ℝ) := by
    apply (mul_le_mul_iff_left₀ (show 0 < (M : ℝ) by positivity)).mp
    calc
      _ = (P : ℝ) * (fiber : ℝ) * (M : ℝ) * decay := by ring
      _ ≤ cwSquareOuterTypeLoss a b c d k *
          (4 * ((M : ℝ) * (M : ℝ)) * (outerCopies : ℝ)) := hraw
      _ = (4 * cwSquareOuterTypeLoss a b c d k * (M : ℝ) *
          (outerCopies : ℝ)) * (M : ℝ) := by ring
  have hMupper : (M : ℝ) ≤ 24 * (fiber : ℝ) := by exact_mod_cast hupper
  have hwithUpper :
      (P : ℝ) * (fiber : ℝ) * decay ≤
        96 * cwSquareOuterTypeLoss a b c d k * (fiber : ℝ) *
          (outerCopies : ℝ) := by
    apply hcancelM.trans
    calc
      4 * cwSquareOuterTypeLoss a b c d k * (M : ℝ) * (outerCopies : ℝ) ≤
          4 * cwSquareOuterTypeLoss a b c d k * (24 * (fiber : ℝ)) *
            (outerCopies : ℝ) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact mul_le_mul_of_nonneg_left hMupper
          (mul_nonneg (by norm_num) houterLossPos.le)
      _ = _ := by ring
  have hcancelFiber :
      (P : ℝ) * decay ≤
        96 * cwSquareOuterTypeLoss a b c d k * (outerCopies : ℝ) := by
    apply (mul_le_mul_iff_left₀
      (show 0 < (fiber : ℝ) by exact_mod_cast hfiberPos)).mp
    calc
      _ = (P : ℝ) * (fiber : ℝ) * decay := by ring
      _ ≤ 96 * cwSquareOuterTypeLoss a b c d k * (fiber : ℝ) *
          (outerCopies : ℝ) := hwithUpper
      _ = (96 * cwSquareOuterTypeLoss a b c d k * (outerCopies : ℝ)) *
          (fiber : ℝ) := by ring
  have hexpCancel :
      Real.exp (4 * √(Real.log (((M / 2 : ℕ) : ℝ)))) *
          decay = 1 := by
    unfold decay
    rw [← Real.exp_add]
    rw [show 4 * √(Real.log (((M / 2 : ℕ) : ℝ))) +
        -4 * √(Real.log (((M / 2 : ℕ) : ℝ))) = 0 by ring, Real.exp_zero]
  calc
    (P : ℝ) = Real.exp (4 * √(Real.log (((M / 2 : ℕ) : ℝ)))) *
        ((P : ℝ) * decay) := by
      symm
      calc
        Real.exp (4 * √(Real.log (((M / 2 : ℕ) : ℝ)))) *
            ((P : ℝ) * decay) =
          (Real.exp (4 * √(Real.log (((M / 2 : ℕ) : ℝ)))) * decay) *
            (P : ℝ) := by ring
        _ = 1 * (P : ℝ) := by rw [hexpCancel]
        _ = (P : ℝ) := one_mul _
    _ ≤ Real.exp (4 * √(Real.log (((M / 2 : ℕ) : ℝ)))) *
        (96 * cwSquareOuterTypeLoss a b c d k * (outerCopies : ℝ)) := by
      exact mul_le_mul_of_nonneg_left hcancelFiber (Real.exp_pos _).le
    _ ≤ Real.exp (cwSquareHashExponentCoefficient a b c d *
          √(((k + 1 : ℕ) : ℝ))) *
        (96 * cwSquareOuterTypeLoss a b c d k * (outerCopies : ℝ)) := by
      exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hsqrtExponent)
        (mul_nonneg
          (mul_nonneg (by norm_num) houterLossPos.le)
          (Nat.cast_nonneg outerCopies))
    _ = _ := by ring

end AlgebraicComplexity.Examples
