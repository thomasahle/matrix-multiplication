/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoFineConfiguration

/-!
# Compatibility targets induced by a Duan--Wu--Zhou fine configuration

`DuanWuZhouLevelTwoFineConfiguration.lean` exposes the unresolved thirty-six-entry fine count
table and proves that its `Z` pushforward refines the committed section 6.3 split rows.  This file
performs the next, purely structural step: it pushes the same table to all exact coarse cells and
to the positive pooled `Y` and `Z` compatibility cells.

The three boundary fields of `CompatibilityTargets PUnit 1` are proved letter by letter.  Each
fine letter is an ordered pair of genuine base Coppersmith--Winograd support addresses, so at each
of its two positions the three digits sum to two.  A zero coarse coordinate therefore makes the
other two complete-split words pointwise complements.  No value of the fine count table is used in
that argument, and no satisfying table is selected here.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor MoreAsymmetryCompatibility

noncomputable section

/-! ## Fine pushforwards -/

/-- Coarse compatibility index occupied by a depth-one fine letter. -/
def dwz63FineCoarseIndex (letter : CWDepthOneFineLetter) : CoarseIndex PUnit :=
  dwz63CoarseIndex (dwz63FineComponent letter)

private def dwz63FinePushforward
    {Cell : Type*} [DecidableEq Cell]
    (fineCount : CWDepthOneFineLetter → ℕ) (k : ℕ)
    (cellOf : CWDepthOneFineLetter → Cell) (cell : Cell)
    (c : Leg) (word : SplitWord 1) : ℕ :=
  ∑ letter,
    if cellOf letter = cell ∧ dwz63FineSplit c letter = word then
      fineCount letter * k
    else 0

/-- Exact complete-split profile at an arbitrary coarse section 6.3 index. -/
def dwz63FineExactProfile
    (fineCount : CWDepthOneFineLetter → ℕ) (k : ℕ)
    (q : CoarseIndex PUnit) (c : Leg) (word : SplitWord 1) : ℕ :=
  dwz63FinePushforward fineCount k dwz63FineCoarseIndex q c word

/-- Positive pooled `Y` profile induced by the fine table. -/
def dwz63FineYPooledProfile
    (fineCount : CWDepthOneFineLetter → ℕ) (k : ℕ)
    (part : PUnit) (y : ℕ) (word : SplitWord 1) : ℕ :=
  dwz63FinePushforward fineCount k
    (fun letter ↦ yCompatibilityCell (dwz63FineCoarseIndex letter))
    (.pooled part y) .Y word

/-- Positive pooled `Z` profile induced by the fine table. -/
def dwz63FineZPooledProfile
    (fineCount : CWDepthOneFineLetter → ℕ) (k : ℕ)
    (part : PUnit) (z : ℕ) (word : SplitWord 1) : ℕ :=
  dwz63FinePushforward fineCount k
    (fun letter ↦ zCompatibilityCell (dwz63FineCoarseIndex letter))
    (.pooled part z) .Z word

/-! ## Pointwise fine support geometry -/

/-- The three fine digits of a depth-one letter sum to two at each of its two positions. -/
theorem dwz63FineSplit_isFineLegal (letter : CWDepthOneFineLetter)
    (position : Fin 2) :
    (dwz63FineSplit .X letter position : ℕ) +
        (dwz63FineSplit .Y letter position : ℕ) +
      (dwz63FineSplit .Z letter position : ℕ) = 2 := by
  fin_cases position
  · simpa [dwz63FineSplit, cwDepthOneLegWord, cwDepthOneRawAddress, sum_leg] using
      cwBlockSupport_digit_sum letter.1.1 letter.1.2
  · simpa [dwz63FineSplit, cwDepthOneLegWord, cwDepthOneRawAddress, sum_leg] using
      cwBlockSupport_digit_sum letter.2.1 letter.2.2

/-- On a fine letter with zero coarse `Z` coordinate, its `Y` split word complements its `X`
split word. -/
theorem dwz63FineSplit_y_eq_complement_x_of_z_eq_zero
    (letter : CWDepthOneFineLetter)
    (hz : (dwz63FineCoarseIndex letter).z = 0) :
    dwz63FineSplit .Y letter = complementSplitWord (dwz63FineSplit .X letter) := by
  have hzWeight : splitWordWeight (dwz63FineSplit .Z letter) = 0 := by
    calc
      splitWordWeight (dwz63FineSplit .Z letter) =
          (dwz63LegIndex .Z (dwz63FineComponent letter) : ℕ) :=
        splitWordWeight_dwz63FineSplit .Z letter
      _ = (dwz63FineCoarseIndex letter).z := by rfl
      _ = 0 := hz
  have hzWord : dwz63FineSplit .Z letter = 0 :=
    CompatibilityModel.splitWord_eq_zero_of_weight_eq_zero _ hzWeight
  funext position
  exact splitDigit_eq_rev_of_legal_of_right_eq_zero
    (dwz63FineSplit .X letter position)
    (dwz63FineSplit .Y letter position)
    (dwz63FineSplit .Z letter position)
    (dwz63FineSplit_isFineLegal letter position)
    (congrFun hzWord position)

/-- On a fine letter with zero coarse `Y` coordinate, its `Z` split word complements its `X`
split word. -/
theorem dwz63FineSplit_z_eq_complement_x_of_y_eq_zero
    (letter : CWDepthOneFineLetter)
    (hy : (dwz63FineCoarseIndex letter).y = 0) :
    dwz63FineSplit .Z letter = complementSplitWord (dwz63FineSplit .X letter) := by
  have hyWeight : splitWordWeight (dwz63FineSplit .Y letter) = 0 := by
    calc
      splitWordWeight (dwz63FineSplit .Y letter) =
          (dwz63LegIndex .Y (dwz63FineComponent letter) : ℕ) :=
        splitWordWeight_dwz63FineSplit .Y letter
      _ = (dwz63FineCoarseIndex letter).y := by rfl
      _ = 0 := hy
  have hyWord : dwz63FineSplit .Y letter = 0 :=
    CompatibilityModel.splitWord_eq_zero_of_weight_eq_zero _ hyWeight
  funext position
  exact splitDigit_eq_rev_of_legal_of_right_eq_zero
    (dwz63FineSplit .X letter position)
    (dwz63FineSplit .Z letter position)
    (dwz63FineSplit .Y letter position)
    (by simpa [add_assoc, add_left_comm, add_comm] using
      dwz63FineSplit_isFineLegal letter position)
    (congrFun hyWord position)

/-- On a fine letter with zero coarse `X` coordinate, its `Z` split word complements its `Y`
split word. -/
theorem dwz63FineSplit_z_eq_complement_y_of_x_eq_zero
    (letter : CWDepthOneFineLetter)
    (hx : (dwz63FineCoarseIndex letter).x = 0) :
    dwz63FineSplit .Z letter = complementSplitWord (dwz63FineSplit .Y letter) := by
  have hxWeight : splitWordWeight (dwz63FineSplit .X letter) = 0 := by
    calc
      splitWordWeight (dwz63FineSplit .X letter) =
          (dwz63LegIndex .X (dwz63FineComponent letter) : ℕ) :=
        splitWordWeight_dwz63FineSplit .X letter
      _ = (dwz63FineCoarseIndex letter).x := by rfl
      _ = 0 := hx
  have hxWord : dwz63FineSplit .X letter = 0 :=
    CompatibilityModel.splitWord_eq_zero_of_weight_eq_zero _ hxWeight
  funext position
  exact splitDigit_eq_rev_of_legal_of_right_eq_zero
    (dwz63FineSplit .Y letter position)
    (dwz63FineSplit .Z letter position)
    (dwz63FineSplit .X letter position)
    (by simpa [add_assoc, add_left_comm, add_comm] using
      dwz63FineSplit_isFineLegal letter position)
    (congrFun hxWord position)

private theorem dwz63FinePushforward_complement
    {Cell : Type*} [DecidableEq Cell]
    (fineCount : CWDepthOneFineLetter → ℕ) (k : ℕ)
    (cellOf : CWDepthOneFineLetter → Cell) (cell : Cell)
    (left right : Leg)
    (hcomplement : ∀ letter, cellOf letter = cell →
      dwz63FineSplit right letter = complementSplitWord (dwz63FineSplit left letter))
    (word : SplitWord 1) :
    dwz63FinePushforward fineCount k cellOf cell right word =
      dwz63FinePushforward fineCount k cellOf cell left (complementSplitWord word) := by
  unfold dwz63FinePushforward
  apply Finset.sum_congr rfl
  intro letter _
  by_cases hcell : cellOf letter = cell
  · have hword :
        dwz63FineSplit right letter = word ↔
          dwz63FineSplit left letter = complementSplitWord word := by
      have hrelation := hcomplement letter hcell
      constructor
      · intro hright
        calc
          dwz63FineSplit left letter =
              complementSplitWord (complementSplitWord (dwz63FineSplit left letter)) :=
            (complementSplitWord_complementSplitWord _).symm
          _ = complementSplitWord (dwz63FineSplit right letter) :=
            congrArg complementSplitWord hrelation.symm
          _ = complementSplitWord word := congrArg complementSplitWord hright
      · intro hleft
        calc
          dwz63FineSplit right letter =
              complementSplitWord (dwz63FineSplit left letter) := hrelation
          _ = complementSplitWord (complementSplitWord word) :=
            congrArg complementSplitWord hleft
          _ = word := complementSplitWord_complementSplitWord word
    simp only [hcell, true_and, hword]
  · simp [hcell]

/-! ## Target package and component identifications -/

/-- The five compatibility tables induced by a fine count table.  The boundary laws depend only
on actual CW support geometry, so this constructor requires no numerical hypothesis. -/
def dwz63FineCompatibilityTargets
    (fineCount : CWDepthOneFineLetter → ℕ) (k : ℕ) :
    CompatibilityTargets PUnit 1 where
  xExact q word := dwz63FineExactProfile fineCount k q .X word
  yExact q word := dwz63FineExactProfile fineCount k q .Y word
  zExact q word := dwz63FineExactProfile fineCount k q .Z word
  yPooled := dwz63FineYPooledProfile fineCount k
  zPooled := dwz63FineZPooledProfile fineCount k
  yBoundary q hz word := by
    apply dwz63FinePushforward_complement fineCount k dwz63FineCoarseIndex q .X .Y
    · intro letter hq
      apply dwz63FineSplit_y_eq_complement_x_of_z_eq_zero letter
      rw [hq]
      exact hz
  zBoundaryOfX q hy word := by
    apply dwz63FinePushforward_complement fineCount k dwz63FineCoarseIndex q .X .Z
    · intro letter hq
      apply dwz63FineSplit_z_eq_complement_x_of_y_eq_zero letter
      rw [hq]
      exact hy
  zBoundaryOfY q hx word := by
    apply dwz63FinePushforward_complement fineCount k dwz63FineCoarseIndex q .Y .Z
    · intro letter hq
      apply dwz63FineSplit_z_eq_complement_y_of_x_eq_zero letter
      rw [hq]
      exact hx

/-- At the coarse index of a section 6.3 component, arbitrary-index exact pooling is the
component-local profile from the fine-configuration module. -/
theorem dwz63FineExactProfile_dwz63CoarseIndex
    (fineCount : CWDepthOneFineLetter → ℕ) (k : ℕ)
    (component : Fin 15) (c : Leg) (word : SplitWord 1) :
    dwz63FineExactProfile fineCount k (dwz63CoarseIndex component) c word =
      dwz63FineComponentLegExact fineCount k component c word := by
  unfold dwz63FineExactProfile dwz63FinePushforward
    dwz63FineComponentLegExact
  apply Finset.sum_congr rfl
  intro letter _
  by_cases hcomponent : dwz63FineComponent letter = component
  · simp [dwz63FineCoarseIndex, hcomponent]
  · have hcoarse :
        dwz63FineCoarseIndex letter ≠ dwz63CoarseIndex component := by
      intro h
      apply hcomponent
      exact dwz63CoarseIndex_injective h
    rw [if_neg (fun h ↦ hcoarse h.1), if_neg (fun h ↦ hcomponent h.1)]

@[simp] theorem dwz63FineCompatibilityTargets_xExact_dwz63CoarseIndex
    (fineCount : CWDepthOneFineLetter → ℕ) (k : ℕ)
    (component : Fin 15) (word : SplitWord 1) :
    (dwz63FineCompatibilityTargets fineCount k).xExact
        (dwz63CoarseIndex component) word =
      dwz63FineXExact fineCount k component word :=
  dwz63FineExactProfile_dwz63CoarseIndex fineCount k component .X word

@[simp] theorem dwz63FineCompatibilityTargets_yExact_dwz63CoarseIndex
    (fineCount : CWDepthOneFineLetter → ℕ) (k : ℕ)
    (component : Fin 15) (word : SplitWord 1) :
    (dwz63FineCompatibilityTargets fineCount k).yExact
        (dwz63CoarseIndex component) word =
      dwz63FineYExact fineCount k component word :=
  dwz63FineExactProfile_dwz63CoarseIndex fineCount k component .Y word

@[simp] theorem dwz63FineCompatibilityTargets_zExact_dwz63CoarseIndex
    (fineCount : CWDepthOneFineLetter → ℕ) (k : ℕ)
    (component : Fin 15) (word : SplitWord 1) :
    (dwz63FineCompatibilityTargets fineCount k).zExact
        (dwz63CoarseIndex component) word =
      dwz63FineZExact fineCount k component word :=
  dwz63FineExactProfile_dwz63CoarseIndex fineCount k component .Z word

/-- Under the one named fine-configuration premise, the target package's exact `Z` table is the
already committed section 6.3 table on every supported component. -/
theorem dwz63FineCompatibilityTargets_zExact_eq_dwz63ZExact
    {fineCount : CWDepthOneFineLetter → ℕ}
    (hconfiguration : Dwz63FineConfiguration fineCount)
    (k : ℕ) (component : Fin 15) (word : SplitWord 1) :
    (dwz63FineCompatibilityTargets fineCount k).zExact
        (dwz63CoarseIndex component) word =
      dwz63ZExact k (dwz63CoarseIndex component) word := by
  rw [dwz63FineCompatibilityTargets_zExact_dwz63CoarseIndex,
    dwz63FineZExact_eq_dwz63ZExact hconfiguration]

end

end AlgebraicComplexity.Examples
