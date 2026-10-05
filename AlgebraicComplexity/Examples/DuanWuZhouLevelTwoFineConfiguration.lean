/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinogradDepthOneRateBarrier
import AlgebraicComplexity.Examples.CoppersmithWinogradTotalWeightLevelTwoSquare
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoCompatibilityTargets

/-!
# Parameterized fine configurations for the Duan--Wu--Zhou level-two split

The section 6.3 compatibility table fixes the `Z` split of each of the fifteen coarse
Coppersmith--Winograd square constituents, but it does not record how the remaining multiplicity
inside a coarse `Z`-word fibre is divided among the ordered pairs of the six base CW addresses.
There are thirty-six such fine letters.  This file exposes that missing choice as one explicit
client datum; it does not choose any of its values.

`Dwz63FineConfiguration fineCount` says exactly that the pushforward of an author-supplied
thirty-six-entry table along `(coarse component, left Z digit)` is the committed table
`dwz63SplitCount`.  The component and complete-split maps are derived from the actual CW square
support.  Scaling and the equality with the already committed `dwz63ZExact` table are then proved
without any additional numerical premise.

The `X` and `Y` component profiles defined here retain the author choice.  A later client packages
them, together with the fixed `Z` profile and the mechanically induced pooled tables, into
`CompatibilityTargets PUnit 1`.  In particular, this module is a data boundary, not a certificate
emitter and not an optimizer.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor MoreAsymmetryCompatibility

noncomputable section

/-! ## The thirty-six-letter fine alphabet and its coarse component -/

/-- Every ordered pair of supported base CW addresses represents a source address of the
uncoarsened square. -/
theorem cwDepthOneRawAddress_mem_cwSquareRawSupport
    (letter : CWDepthOneFineLetter) :
    cwDepthOneRawAddress letter ∈ cwSquareRawSupport := by
  rw [cwSquareRawSupport]
  apply Finset.mem_map.mpr
  exact ⟨(letter.1.1, letter.2.1),
    Finset.mem_product.mpr ⟨letter.1.2, letter.2.2⟩, rfl⟩

/-- The coarse shape of every fine letter lies in the fifteen-address square support. -/
theorem cwDepthOneCoarseShape_mem_cwSquareSupport
    (letter : CWDepthOneFineLetter) :
    cwDepthOneCoarseShape letter ∈ cwSquareSupport := by
  rw [cwSquareSupport]
  exact Finset.mem_image.mpr
    ⟨cwDepthOneRawAddress letter,
      cwDepthOneRawAddress_mem_cwSquareRawSupport letter, rfl⟩

/-- The unique section 6.3 component containing a depth-one fine letter. -/
def dwz63FineComponent (letter : CWDepthOneFineLetter) : Fin 15 :=
  dwz63CellEquiv.symm
    ⟨cwDepthOneCoarseShape letter,
      cwDepthOneCoarseShape_mem_cwSquareSupport letter⟩

/-- Recovering the coarse address of `dwz63FineComponent` returns the letter's actual shape. -/
@[simp] theorem dwz63Cell_dwz63FineComponent (letter : CWDepthOneFineLetter) :
    dwz63Cell (dwz63FineComponent letter) = cwDepthOneCoarseShape letter := by
  unfold dwz63FineComponent
  exact congrArg Subtype.val
    (dwz63CellEquiv.apply_symm_apply
      (⟨cwDepthOneCoarseShape letter,
        cwDepthOneCoarseShape_mem_cwSquareSupport letter⟩ : CWSquareSupport))

/-- The complete depth-one split word carried by one leg of a fine letter. -/
def dwz63FineSplit (c : Leg) (letter : CWDepthOneFineLetter) : SplitWord 1 :=
  cwChunkSplitWord 1 (cwDepthOneLegWord c letter)

/-- The weight of a fine leg word is the corresponding coordinate of its section 6.3 component. -/
theorem splitWordWeight_dwz63FineSplit (c : Leg) (letter : CWDepthOneFineLetter) :
    splitWordWeight (dwz63FineSplit c letter) =
      (dwz63LegIndex c (dwz63FineComponent letter) : ℕ) := by
  calc
    splitWordWeight (dwz63FineSplit c letter) =
        (cwChunkCoarseDigit 1 (cwDepthOneLegWord c letter) : ℕ) := rfl
    _ = (cwSquareBlockDegree (cwDepthOneLegWord c letter) : ℕ) := by
      exact congrArg Fin.val
        (cwChunkCoarseDigit_one_eq_cwSquareBlockDegree
          (cwDepthOneLegWord c letter))
    _ = (cwDepthOneCoarseShape letter c : ℕ) := rfl
    _ = (dwz63Cell (dwz63FineComponent letter) c : ℕ) := by
      exact congrArg Fin.val (congrFun (dwz63Cell_dwz63FineComponent letter) c).symm
    _ = (dwz63LegIndex c (dwz63FineComponent letter) : ℕ) := by
      cases c <;> rfl

/-! ## The exact author-data boundary -/

/-- Count the fine letters of one coarse component with a prescribed left `Z` digit. -/
def dwz63FineZLeftCount (fineCount : CWDepthOneFineLetter → ℕ)
    (component : Fin 15) (left : Fin 3) : ℕ :=
  ∑ letter,
    if dwz63FineComponent letter = component ∧ dwz63FineSplit .Z letter 0 = left then
      fineCount letter
    else 0

/-- One fine configuration refines the committed section 6.3 `Z` split table.

This is the sole data-facing premise: it is forty-five exact natural-number equalities on a
thirty-six-entry table.  It intentionally does not select a satisfying table. -/
def Dwz63FineConfiguration (fineCount : CWDepthOneFineLetter → ℕ) : Prop :=
  ∀ component left,
    dwz63FineZLeftCount fineCount component left = dwz63SplitCount component left

/-- Proportional repetition of a fine count table. -/
def dwz63FineCountScale (fineCount : CWDepthOneFineLetter → ℕ) (k : ℕ) :
    CWDepthOneFineLetter → ℕ :=
  fun letter ↦ fineCount letter * k

/-- The named fine-configuration equations scale by the same repetition factor as the section
6.3 split table. -/
theorem dwz63FineZLeftCount_scale
    {fineCount : CWDepthOneFineLetter → ℕ}
    (hconfiguration : Dwz63FineConfiguration fineCount)
    (k : ℕ) (component : Fin 15) (left : Fin 3) :
    dwz63FineZLeftCount (dwz63FineCountScale fineCount k) component left =
      dwz63SplitCount component left * k := by
  rw [← hconfiguration component left]
  unfold dwz63FineZLeftCount dwz63FineCountScale
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro letter _
  by_cases hcell :
      dwz63FineComponent letter = component ∧ dwz63FineSplit .Z letter 0 = left <;>
    simp [hcell]

/-! ## Exact fine profiles on one coarse component -/

/-- Exact complete-split profile of one leg inside one coarse component. -/
def dwz63FineComponentLegExact (fineCount : CWDepthOneFineLetter → ℕ) (k : ℕ)
    (component : Fin 15) (c : Leg) (word : SplitWord 1) : ℕ :=
  ∑ letter,
    if dwz63FineComponent letter = component ∧ dwz63FineSplit c letter = word then
      fineCount letter * k
    else 0

/-- The exact `X` profile induced by an author-supplied fine configuration. -/
def dwz63FineXExact (fineCount : CWDepthOneFineLetter → ℕ) (k : ℕ)
    (component : Fin 15) (word : SplitWord 1) : ℕ :=
  dwz63FineComponentLegExact fineCount k component .X word

/-- The exact `Y` profile induced by an author-supplied fine configuration. -/
def dwz63FineYExact (fineCount : CWDepthOneFineLetter → ℕ) (k : ℕ)
    (component : Fin 15) (word : SplitWord 1) : ℕ :=
  dwz63FineComponentLegExact fineCount k component .Y word

/-- The exact `Z` profile induced by an author-supplied fine configuration. -/
def dwz63FineZExact (fineCount : CWDepthOneFineLetter → ℕ) (k : ℕ)
    (component : Fin 15) (word : SplitWord 1) : ℕ :=
  dwz63FineComponentLegExact fineCount k component .Z word

private theorem dwz63FineZExact_of_weight
    {fineCount : CWDepthOneFineLetter → ℕ}
    (hconfiguration : Dwz63FineConfiguration fineCount)
    (k : ℕ) (component : Fin 15) (word : SplitWord 1)
    (hweight : splitWordWeight word = (dwz63ZIndex component : ℕ)) :
    dwz63FineZExact fineCount k component word =
      dwz63SplitCount component (word 0) * k := by
  rw [← dwz63FineZLeftCount_scale hconfiguration k component (word 0)]
  unfold dwz63FineZExact dwz63FineComponentLegExact dwz63FineZLeftCount
  apply Finset.sum_congr rfl
  intro letter _
  by_cases hcomponent : dwz63FineComponent letter = component
  · have hfineWeight :
        splitWordWeight (dwz63FineSplit .Z letter) = (dwz63ZIndex component : ℕ) := by
      rw [splitWordWeight_dwz63FineSplit, hcomponent]
      rfl
    have hwordIff :
        dwz63FineSplit .Z letter = word ↔ dwz63FineSplit .Z letter 0 = word 0 := by
      constructor
      · exact fun h ↦ congrFun h 0
      · intro hleft
        exact splitWord_one_eq_of_left_of_weight hleft
          (hfineWeight.trans hweight.symm)
    simp [hcomponent, hwordIff, dwz63FineCountScale]
  · simp [hcomponent]

private theorem dwz63FineZExact_of_weight_ne
    (fineCount : CWDepthOneFineLetter → ℕ) (k : ℕ)
    (component : Fin 15) (word : SplitWord 1)
    (hweight : splitWordWeight word ≠ (dwz63ZIndex component : ℕ)) :
    dwz63FineZExact fineCount k component word = 0 := by
  unfold dwz63FineZExact dwz63FineComponentLegExact
  apply Finset.sum_eq_zero
  intro letter _
  by_cases hcomponent : dwz63FineComponent letter = component
  · have hne : dwz63FineSplit .Z letter ≠ word := by
      intro hword
      apply hweight
      calc
        splitWordWeight word = splitWordWeight (dwz63FineSplit .Z letter) :=
          congrArg splitWordWeight hword.symm
        _ = (dwz63LegIndex .Z (dwz63FineComponent letter) : ℕ) :=
          splitWordWeight_dwz63FineSplit .Z letter
        _ = (dwz63ZIndex component : ℕ) := by
          simp only [dwz63LegIndex, hcomponent]
    simp [hcomponent, hne]
  · simp [hcomponent]

/-- The fine table's `Z` profile is exactly the already committed section 6.3 target at the
corresponding coarse index.  Thus the parameterized fine configuration extends, rather than
replaces, the accepted `Z` tranche. -/
theorem dwz63FineZExact_eq_dwz63ZExact
    {fineCount : CWDepthOneFineLetter → ℕ}
    (hconfiguration : Dwz63FineConfiguration fineCount)
    (k : ℕ) (component : Fin 15) (word : SplitWord 1) :
    dwz63FineZExact fineCount k component word =
      dwz63ZExact k (dwz63CoarseIndex component) word := by
  rw [dwz63ZExact]
  simp_rw [dwz63SplitRow_dwz63CoarseIndex]
  change dwz63FineZExact fineCount k component word =
    dwz63LiftSplitRow (dwz63ZIndex component : ℕ)
      (fun left ↦ dwz63SplitCount component left * k) word
  by_cases hweight : splitWordWeight word = (dwz63ZIndex component : ℕ)
  · rw [dwz63FineZExact_of_weight hconfiguration k component word hweight,
      dwz63LiftSplitRow_of_weight hweight]
  · rw [dwz63FineZExact_of_weight_ne fineCount k component word hweight,
      dwz63LiftSplitRow_of_weight_ne hweight]

end

end AlgebraicComplexity.Examples
