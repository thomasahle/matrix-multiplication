/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoFineCellSurjective
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoFineCellEntropy
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoFinePairSum

set_option autoImplicit false

/-!
# Every zero-coordinate cell `(0, 4-k, k)` and its mirror, in one statement

Layer 4 (`AlgebraicComplexity/Examples/`).
`Examples/DuanWuZhouLevelTwoFineCellSurjective.lean` and
`Examples/DuanWuZhouLevelTwoFineCellEntropy.lean` do the `(0,2,2)` cell of `[duan2023faster]`
section 6.3 with the zero coordinate on `X` and the coarse degree hard-wired to `2`.  Nothing in
either argument uses either restriction, and this module carries both as parameters:

* the zero leg is any `zero ≠ Leg.Z` --- `alphatilde` is carried on `Z`, so the zero coordinate
  may
  sit on `X` or on `Y` but not on the split leg itself;
* the coarse `Z` degree is any `k : Fin 5`, and the third leg's degree is then forced to `4 - k`.

So the cells `(0,4,0)`, `(0,3,1)`, `(0,2,2)`, `(0,1,3)`, `(0,0,4)` and their `Y`-zero mirrors
`(4,0,0)`, `(3,0,1)`, `(2,0,2)`, `(1,0,3)` are all instances of one theorem.  `(2,2,0)` is **not**:
its zero coordinate is on `Z`, which is the split leg, and it is the one non-uniform cell.

## What is genuinely leg-dependent

Only one thing: `dwz63CellOnes zero` counts middles at `firstLiveLeg zero`, while `alphatilde`
sits on `Z`.  For `zero = .Y` those coincide (`firstLiveLeg .Y = .Z`) and image 87's
`dwz63_cellPower_cellOnes_eq_alphaSum_of_firstLive` applies; for `zero = .X` the profile is at
`secondLiveLeg .X = .Z` and image 92's `dwz63_cellPower_cellOnes_eq_alphaSum_of_secondLive`
applies, crossing the two live legs by `dwz63_middleCount_liveLegs_eq`.
`dwz63_cellPower_cellOnes_eq_alphaSum` below is the two-case dispatch, and it is the only place in
this module where the legs are split.

The witness letter is supported for **every** `Z` pair and for **every** zero leg, with no degree
hypothesis: the forced third digit is `2` minus the `Z` digit at each of the two sub-positions, so
each triple sums to `2` by construction.  The degree hypothesis enters only where the address must
coarsen to the *fixed* target.

Primary source: Ran Duan, Hongxun Wu and Renfei Zhou, *Faster Matrix Multiplication via Asymmetric
Hashing*, arXiv:2210.10173, `global_value.tex` section 6.3 and `lem:non-rot-values`.

Exact source lines: `papers/sources/2210.10173/global_value.tex:332-378` (§6.3),
`papers/sources/2210.10173/second_power.tex:144-158` (`lem:non-rot-values`).
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor MoreAsymmetryCompatibility
open scoped BigOperators

universe u

/-! ## The third leg, and the pair complement -/

/-- **The live leg that is not the split leg `Z`.**  At `zero = .Z` the value is `.Z` itself, which
no theorem below uses: every statement carries `zero ≠ Leg.Z`. -/
def dwz63ThirdLeg : Leg → Leg
  | .X => .Y
  | .Y => .X
  | .Z => .Z

/-- The sub-position-wise degree complement of a fine letter. -/
def dwz63PairComplement (p : PositiveWord CWBlock 1) : PositiveWord CWBlock 1 :=
  ((dwz63BlockComplement p.1, dwz63BlockComplement p.2) : PositiveWord CWBlock 1)

/-- **The complement inverts the coarse degree.**  Stated over `CWBlock × CWBlock` so that
`decide` applies; `PositiveWord CWBlock 1` unfolds to it. -/
theorem dwz63_squareBlockDegree_pairComplement (a b : CWBlock) :
    cwSquareBlockDegree (dwz63PairComplement ((a, b) : PositiveWord CWBlock 1)) =
      4 - cwSquareBlockDegree ((a, b) : PositiveWord CWBlock 1) := by
  cases a <;> cases b <;> decide

/-- The complement preserves the middle-digit count, hence the one-slice exponent. -/
theorem dwz63_wordMiddleCount_pairComplement (a b : CWBlock) :
    cwWordMiddleCount 1 (dwz63PairComplement ((a, b) : PositiveWord CWBlock 1)) =
      cwWordMiddleCount 1 ((a, b) : PositiveWord CWBlock 1) := by
  cases a <;> cases b <;> decide

variable (K : Type u) [CommRing K] (q : ℕ)

/-! ## The forced fine letter, in either zero frame -/

/-- **The fine letter forced by a `Z` pair, with the zero coordinate on `zero`.** -/
def dwz63ZeroFineLetterAddress (zero : Leg) (p : PositiveWord CWBlock 1) :
    BlockAddress (fun _ : Leg ↦ PositiveWord CWBlock 1) :=
  match zero with
  | .X => ofLegs (positiveWordConst CWBlock.zero 1) (dwz63PairComplement p) p
  | .Y => ofLegs (dwz63PairComplement p) (positiveWordConst CWBlock.zero 1) p
  | .Z => ofLegs (dwz63PairComplement p) p (positiveWordConst CWBlock.zero 1)

/-- **The forced letter is supported, in every frame and for every `Z` pair.** -/
theorem dwz63ZeroFineLetterAddress_mem (zero : Leg) (p : PositiveWord CWBlock 1) :
    dwz63ZeroFineLetterAddress zero p ∈
      ((cwPartitionedTensor K q).positivePower 1).support := by
  classical
  rw [(cwPartitionedTensor K q).positivePower_support_eq_image_positiveSupportWordBlockAddress 1]
  have hmemX : ∀ a : CWBlock,
      cwBlockAddress CWBlock.zero (dwz63BlockComplement a) a ∈ cwBlockSupport := by
    intro a; cases a <;> decide
  have hmemY : ∀ a : CWBlock,
      cwBlockAddress (dwz63BlockComplement a) CWBlock.zero a ∈ cwBlockSupport := by
    intro a; cases a <;> decide
  have hmemZ : ∀ a : CWBlock,
      cwBlockAddress (dwz63BlockComplement a) a CWBlock.zero ∈ cwBlockSupport := by
    intro a; cases a <;> decide
  cases zero
  · refine Finset.mem_image.mpr
      ⟨(⟨_, hmemX p.1⟩, ⟨_, hmemX p.2⟩), Finset.mem_univ _, ?_⟩
    funext c; cases c <;> rfl
  · refine Finset.mem_image.mpr
      ⟨(⟨_, hmemY p.1⟩, ⟨_, hmemY p.2⟩), Finset.mem_univ _, ?_⟩
    funext c; cases c <;> rfl
  · refine Finset.mem_image.mpr
      ⟨(⟨_, hmemZ p.1⟩, ⟨_, hmemZ p.2⟩), Finset.mem_univ _, ?_⟩
    funext c; cases c <;> rfl

/-- The forced letter, as an element of the fine support. -/
def dwz63ZeroFineLetter (zero : Leg) (p : PositiveWord CWBlock 1) :
    ((cwPartitionedTensor K q).positivePower 1).support :=
  ⟨dwz63ZeroFineLetterAddress zero p, dwz63ZeroFineLetterAddress_mem K q zero p⟩

/-! ## The coarse target of the cell `(0, 4-k, k)` and its mirror -/

/-- **The coarse address of the cell**: degree `0` on the zero leg, `k` on the split leg `Z`, and
the forced `4 - k` on the third leg. -/
def dwz63ZeroCellTarget (zero : Leg) (k : Fin 5) (n : ℕ) :
    BlockAddress (fun _ : Leg ↦ PositiveWord (Fin 5) n) :=
  match zero with
  | .X => ofLegs (positiveWordConst (0 : Fin 5) n) (positiveWordConst (4 - k) n)
      (positiveWordConst k n)
  | .Y => ofLegs (positiveWordConst (4 - k) n) (positiveWordConst (0 : Fin 5) n)
      (positiveWordConst k n)
  | .Z => ofLegs (positiveWordConst (4 - k) n) (positiveWordConst k n)
      (positiveWordConst (0 : Fin 5) n)

@[simp] theorem dwz63ZeroCellTarget_self (zero : Leg) (k : Fin 5) (n : ℕ) :
    dwz63ZeroCellTarget zero k n zero = positiveWordConst (0 : Fin 5) n := by
  cases zero <;> rfl

/-! ## The witness address -/

/-- **The witness address of a `Z` word**, letterwise the forced fine letter. -/
noncomputable def dwz63ZeroFineWitness (zero : Leg) (n : ℕ)
    (zw : Fin (n + 1) → PositiveWord CWBlock 1) :
    BlockAddress (fun _ : Leg ↦ PositiveWord (PositiveWord CWBlock 1) n) :=
  positiveSupportWordBlockAddress ((cwPartitionedTensor K q).positivePower 1).support n
    ((positiveWordEquiv ((cwPartitionedTensor K q).positivePower 1).support n).symm
      (fun i ↦ dwz63ZeroFineLetter K q zero (zw i)))

theorem dwz63_zeroFineWitness_equiv (zero : Leg) (n : ℕ)
    (zw : Fin (n + 1) → PositiveWord CWBlock 1) (c : Leg) :
    positiveWordEquiv (PositiveWord CWBlock 1) n (dwz63ZeroFineWitness K q zero n zw c) =
      fun i ↦ dwz63ZeroFineLetterAddress zero (zw i) c := by
  rw [dwz63ZeroFineWitness,
    positiveWordEquiv_positiveSupportWordBlockAddress_recursive
      ((cwPartitionedTensor K q).positivePower 1).support n _ c,
    Equiv.apply_symm_apply]
  rfl

/-- The witness is trivial on the zero leg. -/
theorem dwz63_zeroFineWitness_zero (zero : Leg) (n : ℕ)
    (zw : Fin (n + 1) → PositiveWord CWBlock 1) :
    dwz63ZeroFineWitness K q zero n zw zero =
      positiveWordConst (positiveWordConst CWBlock.zero 1) n := by
  refine (positiveWordEquiv (PositiveWord CWBlock 1) n).injective ?_
  rw [dwz63_zeroFineWitness_equiv, positiveWordEquiv_const]
  funext i
  cases zero <;> rfl

/-- The witness carries the given word on the split leg `Z`, provided the zero leg is not `Z`. -/
theorem dwz63_zeroFineWitness_Z (zero : Leg) (hzero : zero ≠ Leg.Z) (n : ℕ)
    (zw : Fin (n + 1) → PositiveWord CWBlock 1) :
    positiveWordEquiv (PositiveWord CWBlock 1) n
      (dwz63ZeroFineWitness K q zero n zw Leg.Z) = zw := by
  rw [dwz63_zeroFineWitness_equiv]
  funext i
  cases zero
  · rfl
  · rfl
  · exact absurd rfl hzero

theorem dwz63_zeroFineWitness_mem (zero : Leg) (n : ℕ)
    (zw : Fin (n + 1) → PositiveWord CWBlock 1) :
    dwz63ZeroFineWitness K q zero n zw ∈
      (((cwPartitionedTensor K q).positivePower 1).positivePower n).support := by
  classical
  rw [((cwPartitionedTensor K q).positivePower
    1).positivePower_support_eq_image_positiveSupportWordBlockAddress n]
  exact Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩

/-- The witness coarsens to the cell's target, provided every occurring `Z` letter has coarse
degree `k`. -/
theorem dwz63_zeroFineWitness_coarsens (zero : Leg) (hzero : zero ≠ Leg.Z) (k : Fin 5) (n : ℕ)
    (zw : Fin (n + 1) → PositiveWord CWBlock 1)
    (hdeg : ∀ i, cwSquareBlockDegree (zw i) = k) (c : Leg) :
    positiveWordMap (cwSquareDegreeMap c) n (dwz63ZeroFineWitness K q zero n zw c) =
      dwz63ZeroCellTarget zero k n c := by
  have hzeroPair : cwSquareBlockDegree (positiveWordConst CWBlock.zero 1) = (0 : Fin 5) := by
    decide
  have hcomp : ∀ i, cwSquareBlockDegree (dwz63PairComplement (zw i)) = 4 - k := by
    intro i
    have h := dwz63_squareBlockDegree_pairComplement (zw i).1 (zw i).2
    rw [show (((zw i).1, (zw i).2) : PositiveWord CWBlock 1) = zw i from rfl] at h
    rw [h, hdeg i]
  refine (positiveWordEquiv (Fin 5) n).injective ?_
  rw [positiveWordEquiv_map, dwz63_zeroFineWitness_equiv]
  cases zero
  · cases c
    · rw [show dwz63ZeroCellTarget Leg.X k n Leg.X = positiveWordConst (0 : Fin 5) n from rfl,
        positiveWordEquiv_const]
      funext i; exact hzeroPair
    · rw [show dwz63ZeroCellTarget Leg.X k n Leg.Y = positiveWordConst (4 - k) n from rfl,
        positiveWordEquiv_const]
      funext i; exact hcomp i
    · rw [show dwz63ZeroCellTarget Leg.X k n Leg.Z = positiveWordConst k n from rfl,
        positiveWordEquiv_const]
      funext i; exact hdeg i
  · cases c
    · rw [show dwz63ZeroCellTarget Leg.Y k n Leg.X = positiveWordConst (4 - k) n from rfl,
        positiveWordEquiv_const]
      funext i; exact hcomp i
    · rw [show dwz63ZeroCellTarget Leg.Y k n Leg.Y = positiveWordConst (0 : Fin 5) n from rfl,
        positiveWordEquiv_const]
      funext i; exact hzeroPair
    · rw [show dwz63ZeroCellTarget Leg.Y k n Leg.Z = positiveWordConst k n from rfl,
        positiveWordEquiv_const]
      funext i; exact hdeg i
  · exact absurd rfl hzero

/-! ## Surjectivity, for every zero-coordinate cell -/

/-- **The `alphatilde`-typical type class injects into the fibre of the cell `(0, 4-k, k)`**, in
either zero frame.  The `(0,2,2)` case with `zero = .X` is
`dwz63_card_typeClass_le_zeroXFineCellSupport`
(`Examples/DuanWuZhouLevelTwoFineCellSurjective.lean`), which is now a one-line instance. -/
theorem dwz63_card_typeClass_le_zeroFineCellSupport (zero : Leg) (hzero : zero ≠ Leg.Z)
    (k : Fin 5) (n : ℕ) (alphaTilde : PositiveWord CWBlock 1 → ℕ)
    (halpha : ∀ p : PositiveWord CWBlock 1, alphaTilde p ≠ 0 → cwSquareBlockDegree p = k) :
    (WordType.typeClass (n + 1) alphaTilde).card ≤
      (((cwPartitionedTensor K q).positivePower 1).segmentedLocalizedSplittingPower
        cwSquareDegreeMap n 1 (fun _ ↦ 0)
        (SegmentedSplitRestriction.ofLeg
          (A := fun _ : Leg ↦ PositiveWord CWBlock 1) Leg.Z (fun _ ↦ alphaTilde))
        (dwz63ZeroCellTarget zero k n)).support.card := by
  classical
  refine Finset.card_le_card_of_injOn (dwz63ZeroFineWitness K q zero n) ?_ ?_
  · intro zw hzw
    have hzwFinset : zw ∈ WordType.typeClass (n + 1) alphaTilde := by simpa using hzw
    have htype : WordType.multiplicity zw = alphaTilde := WordType.mem_typeClass.mp hzwFinset
    have hdeg : ∀ i, cwSquareBlockDegree (zw i) = k := by
      intro i
      refine halpha (zw i) ?_
      rw [← htype]
      exact WordType.multiplicity_apply_ne_zero zw i
    have hmem : dwz63ZeroFineWitness K q zero n zw ∈
        (((cwPartitionedTensor K q).positivePower 1).segmentedLocalizedSplittingPower
          cwSquareDegreeMap n 1 (fun _ ↦ 0)
          (SegmentedSplitRestriction.ofLeg
            (A := fun _ : Leg ↦ PositiveWord CWBlock 1) Leg.Z (fun _ ↦ alphaTilde))
          (dwz63ZeroCellTarget zero k n)).support := by
      rw [dwz63_mem_cellPower_support_iff]
      refine ⟨dwz63_zeroFineWitness_mem K q zero n zw,
        fun c ↦ dwz63_zeroFineWitness_coarsens K q zero hzero k n zw hdeg c, ?_⟩
      rw [dwz63_zeroFineWitness_Z K q zero hzero n zw]
      exact htype
    simpa using hmem
  · intro zw _ zw' _ heq
    have h := congrArg
      (fun s ↦ positiveWordEquiv (PositiveWord CWBlock 1) n (s Leg.Z)) heq
    rw [dwz63_zeroFineWitness_Z K q zero hzero n zw,
      dwz63_zeroFineWitness_Z K q zero hzero n zw'] at h
    exact h

/-! ## `huniform` in either frame -/

/-- **`huniform` for either zero frame.**  The two-case dispatch onto image 87's
`…_of_firstLive` (`zero = .Y`, where `firstLiveLeg .Y = .Z`) and image 92's `…_of_secondLive`
(`zero = .X`, where `secondLiveLeg .X = .Z`). -/
theorem dwz63_cellPower_cellOnes_eq_alphaSum (zero : Leg) (hzero : zero ≠ Leg.Z) (n : ℕ)
    (α : PositiveWord CWBlock 1 → ℕ)
    (target : BlockAddress (fun _ : Leg ↦ PositiveWord (Fin 5) n))
    (htarget : target zero = positiveWordConst (0 : Fin 5) n)
    (s : BlockAddress (fun _ : Leg ↦ PositiveWord (PositiveWord CWBlock 1) n))
    (hs : s ∈ (((cwPartitionedTensor K q).positivePower 1).segmentedLocalizedSplittingPower
        cwSquareDegreeMap n 1 (fun _ ↦ 0)
        (SegmentedSplitRestriction.ofLeg
          (A := fun _ : Leg ↦ PositiveWord CWBlock 1) Leg.Z (fun _ ↦ α)) target).support) :
    dwz63CellOnes zero n s = ∑ p : PositiveWord CWBlock 1, α p * cwWordMiddleCount 1 p := by
  cases zero
  · exact dwz63_cellPower_cellOnes_eq_alphaSum_of_secondLive K q n Leg.X rfl α target htarget s hs
  · exact dwz63_cellPower_cellOnes_eq_alphaSum_of_firstLive K q n Leg.Y rfl α target s hs
  · exact absurd rfl hzero

/-! ## The eventual weight, for every zero-coordinate cell -/

/-- **Every zero-coordinate cell `(0, 4-k, k)` and its mirror attains the entropy rate of its
split profile, eventually.**

The parameterised form of `dwz63_exists_zeroXFineCellWeight`
(`Examples/DuanWuZhouLevelTwoFineCellEntropy.lean`), which is the case `zero = .X`, `k = 2`. -/
theorem dwz63_exists_zeroFineCellWeight (zero : Leg) (hzero : zero ≠ Leg.Z) (k : Fin 5)
    (hq : 0 < q)
    (a : PositiveWord CWBlock 1 → ℕ)
    (hmass : 0 < WordType.profileMass a)
    (ha : ∀ p : PositiveWord CWBlock 1, a p ≠ 0 → cwSquareBlockDegree p = k)
    (τ : ℝ) (hτ : 0 ≤ τ)
    {lowerBase : ℝ} (hlower : 0 < lowerBase)
    (hlt : lowerBase <
      (2 : ℝ) ^ ((WordType.profileMass a : ℝ) * WordType.profileEntropyBits a)) :
    ∃ N : ℕ, ∀ j : ℕ, N ≤ j → ∀ n : ℕ, n + 1 = WordType.profileMass a * j →
      HasTauWeight K
        ((((cwPartitionedTensor K q).positivePower 1).segmentedLocalizedSplittingPower
          cwSquareDegreeMap n 1 (fun _ ↦ 0)
          (SegmentedSplitRestriction.ofLeg
            (A := fun _ : Leg ↦ PositiveWord CWBlock 1) Leg.Z
            (fun _ ↦ WordType.proportionalCounts a j))
          (dwz63ZeroCellTarget zero k n)).realize) τ
        ((lowerBase ^ j *
          ((q ^ (∑ p : PositiveWord CWBlock 1,
            WordType.proportionalCounts a j p * cwWordMiddleCount 1 p) : ℕ) : ℝ)) ^ τ) := by
  classical
  obtain ⟨cutoff, hcutoff⟩ :=
    WordType.exists_cutoff_forall_pow_le_card_proportionalTypeClass a hmass hlower hlt
  refine ⟨cutoff, fun j hj n hn ↦ ?_⟩
  set αj : PositiveWord CWBlock 1 → ℕ := WordType.proportionalCounts a j with hαj
  set target := dwz63ZeroCellTarget zero k n with htargetDef
  set cell := ((cwPartitionedTensor K q).positivePower 1).segmentedLocalizedSplittingPower
    cwSquareDegreeMap n 1 (fun _ ↦ 0)
    (SegmentedSplitRestriction.ofLeg
      (A := fun _ : Leg ↦ PositiveWord CWBlock 1) Leg.Z (fun _ ↦ αj)) target with hcellDef
  set ones := ∑ p : PositiveWord CWBlock 1, αj p * cwWordMiddleCount 1 p with honesDef
  have hαjdeg : ∀ p : PositiveWord CWBlock 1, αj p ≠ 0 → cwSquareBlockDegree p = k := by
    intro p hp
    refine ha p ?_
    intro hzeroval
    rw [hαj, WordType.proportionalCounts, hzeroval, Nat.zero_mul] at hp
    exact hp rfl
  have hclass : lowerBase ^ j ≤
      (((WordType.typeClass (WordType.profileMass a * j) αj).card : ℕ) : ℝ) := hcutoff j hj
  have hinj : (WordType.typeClass (n + 1) αj).card ≤ cell.support.card := by
    rw [hcellDef, htargetDef]
    exact dwz63_card_typeClass_le_zeroFineCellSupport K q zero hzero k n αj hαjdeg
  have hfibre : lowerBase ^ j ≤ ((cell.support.card : ℕ) : ℝ) := by
    refine hclass.trans ?_
    have hle : (WordType.typeClass (WordType.profileMass a * j) αj).card ≤ cell.support.card :=
      by
      rw [← hn]; exact hinj
    exact Nat.cast_le.mpr hle
  have hpos : 0 < ((cell.support.card : ℕ) : ℝ) :=
    lt_of_lt_of_le (pow_pos hlower j) hfibre
  have hne : cell.support.Nonempty := Finset.card_pos.mp (Nat.cast_pos.mp hpos)
  have htargetZero : target zero = positiveWordConst (0 : Fin 5) n := by
    rw [htargetDef, dwz63ZeroCellTarget_self]
  have hzeroLeg : ∀ s ∈ cell.support,
      s zero = positiveWordConst (positiveWordConst CWBlock.zero 1) n := by
    intro s hs
    refine dwz63_cellPower_zeroLeg_eq_const K q n zero αj target htargetZero s ?_
    rw [hcellDef] at hs; exact hs
  have hones : ∀ s ∈ cell.support, dwz63CellOnes zero n s = ones := by
    intro s hs
    refine dwz63_cellPower_cellOnes_eq_alphaSum K q zero hzero n αj target htargetZero s ?_
    rw [hcellDef] at hs; exact hs
  have hweight := dwz63_hasTauWeight_fineCellPower K q zero n ones τ
    (segmentedLocalizedKeep cwSquareDegreeMap (fun _ : Fin (n + 1) ↦ (0 : Fin 1))
      (SegmentedSplitRestriction.ofLeg
        (A := fun _ : Leg ↦ PositiveWord CWBlock 1) Leg.Z (fun _ ↦ αj)) target)
    hq hne hzeroLeg hones
  refine hweight.mono ?_
  refine Real.rpow_le_rpow (by positivity) ?_ hτ
  rw [Nat.cast_mul]
  exact mul_le_mul_of_nonneg_right hfibre (by positivity)

end AlgebraicComplexity.Examples
