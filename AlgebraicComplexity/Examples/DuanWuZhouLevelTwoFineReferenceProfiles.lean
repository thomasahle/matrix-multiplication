/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinogradTotalWeightExtractionClients
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoFineTargetSupport
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoSupportBridge

/-!
# Duan--Wu--Zhou fine targets at a marked reference word

The marked hashing family fixes the empirical multiplicity of the fifteen coarse square
components.  A fine configuration refines that component type by thirty-six ordered square
letters.  This file proves that the total-weight pushforward forgets precisely that refinement:
at a marked reference word, its exact `X`/`Y` profiles and pooled `Y`/`Z` profiles are the five
tables of `dwz63FineCompatibilityTargets`.

The proof is a finite pushforward calculation.  No hash rate, survivor count, extraction theorem,
or numerical choice of the fine configuration occurs here.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor MoreAsymmetryCompatibility

noncomputable section

private def dwz63FineReferenceAddress (n : ℕ)
    (word : Fin (n + 1) → Fin 15) :
    BlockAddress (fun _c ↦ PositiveWord (CWCoarseDigit 1) n) :=
  PartitionHashEncoding.supportWordAddress
    (A := fun _ : Leg ↦ Fin 5) (support := cwSquareSupport)
    n (dwz63WordEquiv n word)

@[simp] private theorem dwz63FineReferenceAddress_symbol
    (n : ℕ) (word : Fin (n + 1) → Fin 15)
    (c : Leg) (sample : Fin (n + 1)) :
    positiveWordEquiv (CWCoarseDigit 1) n
        (dwz63FineReferenceAddress n word c) sample =
      dwz63LegIndex c (word sample) := by
  unfold dwz63FineReferenceAddress
  change positiveWordEquiv (Fin 5) n
      (PartitionHashEncoding.supportWordAddress n (dwz63WordEquiv n word) c) sample = _
  have h := congrFun
    (PartitionHashEncoding.positiveWordEquiv_supportWordAddress
      (A := fun _ : Leg ↦ Fin 5) (support := cwSquareSupport)
      n (dwz63WordEquiv n word) c) sample
  rw [positiveWordEquiv_dwz63WordEquiv] at h
  rw [h]
  cases c <;> rfl

@[simp] private theorem dwz63FineReferenceAddress_coarse
    (n : ℕ) (word : Fin (n + 1) → Fin 15)
    (sample : Fin (n + 1)) :
    (cwTotalWeightFeatureCompatibilityModel 1 n (fun _ ↦ PUnit.unit)).coarse
        (dwz63FineReferenceAddress n word) sample =
      dwz63CoarseIndex (word sample) := by
  apply CoarseIndex.ext
  · rfl
  · exact congrArg Fin.val
      (dwz63FineReferenceAddress_symbol n word .X sample)
  · exact congrArg Fin.val
      (dwz63FineReferenceAddress_symbol n word .Y sample)
  · exact congrArg Fin.val
      (dwz63FineReferenceAddress_symbol n word .Z sample)

private theorem dwz63FinePushedProfile_eq_componentMass
    {Cell : Type*} [DecidableEq Cell]
    (fineCount : CWDepthOneFineLetter → ℕ) (k : ℕ)
    (cellOf : Fin 15 → Cell) (cell : Cell) (c : Leg)
    (symbol : CWCoarseDigit 1) :
    WordType.mappedType (cwSplitWordTotalDigit 1)
        (fun split ↦ ∑ letter,
          if cellOf (dwz63FineComponent letter) = cell ∧
              dwz63FineSplit c letter = split then
            fineCount letter * k
          else 0)
        symbol =
      WordType.mappedType
        (fun component ↦ (cellOf component, dwz63LegIndex c component))
        (dwz63FineComponentMass (dwz63FineCountScale fineCount k))
        (cell, symbol) := by
  classical
  have hleft :
      WordType.mappedType (cwSplitWordTotalDigit 1)
          (fun split ↦ ∑ letter,
            if cellOf (dwz63FineComponent letter) = cell ∧
                dwz63FineSplit c letter = split then
              fineCount letter * k
            else 0)
          symbol =
        ∑ letter,
          if cellOf (dwz63FineComponent letter) = cell ∧
              dwz63LegIndex c (dwz63FineComponent letter) = symbol then
            fineCount letter * k
          else 0 := by
    rw [WordType.mappedType_eq_sum_ite]
    calc
      (∑ split,
          if cwSplitWordTotalDigit 1 split = symbol then
            ∑ letter,
              if cellOf (dwz63FineComponent letter) = cell ∧
                  dwz63FineSplit c letter = split then
                fineCount letter * k
              else 0
          else 0) =
          ∑ split, ∑ letter,
            if cwSplitWordTotalDigit 1 split = symbol ∧
                cellOf (dwz63FineComponent letter) = cell ∧
                dwz63FineSplit c letter = split then
              fineCount letter * k
            else 0 := by
          apply Finset.sum_congr rfl
          intro split _
          by_cases hsymbol : cwSplitWordTotalDigit 1 split = symbol <;>
            simp [hsymbol]
      _ = ∑ letter, ∑ split,
            if cwSplitWordTotalDigit 1 split = symbol ∧
                cellOf (dwz63FineComponent letter) = cell ∧
                dwz63FineSplit c letter = split then
              fineCount letter * k
            else 0 := Finset.sum_comm
      _ = _ := by
          apply Finset.sum_congr rfl
          intro letter _
          rw [Finset.sum_eq_single (dwz63FineSplit c letter)]
          · simp only [cwSplitWordTotalDigit_dwz63FineSplit, and_true]
            by_cases hcell : cellOf (dwz63FineComponent letter) = cell <;>
              by_cases hsymbol :
                dwz63LegIndex c (dwz63FineComponent letter) = symbol <;>
              simp [hcell, hsymbol]
          · intro split _ hsplit
            rw [if_neg]
            exact fun h ↦ hsplit h.2.2.symm
          · simp
  have hright :
      WordType.mappedType
          (fun component ↦ (cellOf component, dwz63LegIndex c component))
          (dwz63FineComponentMass (dwz63FineCountScale fineCount k))
          (cell, symbol) =
        ∑ letter,
          if cellOf (dwz63FineComponent letter) = cell ∧
              dwz63LegIndex c (dwz63FineComponent letter) = symbol then
            fineCount letter * k
          else 0 := by
    rw [WordType.mappedType_eq_sum_ite]
    unfold dwz63FineComponentMass dwz63FineCountScale
    calc
      (∑ component,
          if (cellOf component, dwz63LegIndex c component) = (cell, symbol) then
            ∑ letter,
              if dwz63FineComponent letter = component then fineCount letter * k else 0
          else 0) =
          ∑ component, ∑ letter,
            if (cellOf component, dwz63LegIndex c component) = (cell, symbol) ∧
                dwz63FineComponent letter = component then
              fineCount letter * k
            else 0 := by
          apply Finset.sum_congr rfl
          intro component _
          by_cases htarget :
              (cellOf component, dwz63LegIndex c component) = (cell, symbol) <;>
            simp [htarget]
      _ = ∑ letter, ∑ component,
            if (cellOf component, dwz63LegIndex c component) = (cell, symbol) ∧
                dwz63FineComponent letter = component then
              fineCount letter * k
            else 0 := Finset.sum_comm
      _ = _ := by
          apply Finset.sum_congr rfl
          intro letter _
          rw [Finset.sum_eq_single (dwz63FineComponent letter)]
          · simp [Prod.ext_iff]
          · intro component _ hcomponent
            rw [if_neg]
            exact fun h ↦ hcomponent h.2.symm
          · simp
  exact hleft.trans hright.symm

private theorem dwz63CellMultiplicity_eq_jointMultiplicity
    {samples : ℕ} {Cell Symbol : Type*}
    [DecidableEq Cell] [DecidableEq Symbol]
    (cellOf : Fin samples → Cell) (word : Fin samples → Symbol)
    (cell : Cell) (symbol : Symbol) :
    cellMultiplicity cellOf word cell symbol =
      WordType.multiplicity (fun position ↦ (cellOf position, word position))
        (cell, symbol) := by
  classical
  unfold cellMultiplicity WordType.multiplicity
  congr 1
  ext position
  simp [Prod.ext_iff]

private theorem dwz63FineReference_cellMultiplicity
    {Cell : Type*} [DecidableEq Cell]
    (n : ℕ) (word : Fin (n + 1) → Fin 15)
    (cellOf : CoarseIndex PUnit → Cell) (c : Leg)
    (cell : Cell) (symbol : CWCoarseDigit 1) :
    let model := cwTotalWeightFeatureCompatibilityModel 1 n (fun _ ↦ PUnit.unit)
    cellMultiplicity
        (fun sample ↦ cellOf (model.coarse (dwz63FineReferenceAddress n word) sample))
        (model.symbols c (dwz63FineReferenceAddress n word c)) cell symbol =
      WordType.mappedType
        (fun component ↦ (cellOf (dwz63CoarseIndex component),
          dwz63LegIndex c component))
        (WordType.multiplicity word) (cell, symbol) := by
  classical
  dsimp only
  rw [dwz63CellMultiplicity_eq_jointMultiplicity]
  have hjoint :
      (fun sample ↦
        (cellOf
            ((cwTotalWeightFeatureCompatibilityModel 1 n
              (fun _ ↦ PUnit.unit)).coarse
                (dwz63FineReferenceAddress n word) sample),
          (cwTotalWeightFeatureCompatibilityModel 1 n
            (fun _ ↦ PUnit.unit)).symbols c
              (dwz63FineReferenceAddress n word c) sample)) =
        (fun component ↦
          (cellOf (dwz63CoarseIndex component), dwz63LegIndex c component)) ∘ word := by
    funext sample
    simp only [Function.comp_apply, dwz63FineReferenceAddress_coarse,
      cwTotalWeightFeatureCompatibilityModel_symbols,
      dwz63FineReferenceAddress_symbol]
  rw [hjoint, WordType.multiplicity_comp_eq_mappedType]

private theorem dwz63FineReference_profile
    {Cell : Type*} [DecidableEq Cell]
    {fineCount : CWDepthOneFineLetter → ℕ}
    (hconfiguration : Dwz63FineConfiguration fineCount)
    (k n : ℕ) (word : Fin (n + 1) → Fin 15)
    (hword : WordType.multiplicity word =
      WordType.proportionalCounts dwz63Alpha (200000000 * k))
    (cellOf : CoarseIndex PUnit → Cell) (c : Leg)
    (cell : Cell) (symbol : CWCoarseDigit 1) :
    let model := cwTotalWeightFeatureCompatibilityModel 1 n (fun _ ↦ PUnit.unit)
    cellMultiplicity
        (fun sample ↦ cellOf (model.coarse (dwz63FineReferenceAddress n word) sample))
        (model.symbols c (dwz63FineReferenceAddress n word c)) cell symbol =
      WordType.mappedType (cwSplitWordTotalDigit 1)
        (fun split ↦ ∑ letter,
          if cellOf (dwz63FineCoarseIndex letter) = cell ∧
              dwz63FineSplit c letter = split then
            fineCount letter * k
          else 0)
        symbol := by
  dsimp only
  rw [dwz63FineReference_cellMultiplicity, hword]
  have hmass :
      WordType.proportionalCounts dwz63Alpha (200000000 * k) =
        dwz63FineComponentMass (dwz63FineCountScale fineCount k) := by
    funext component
    exact (dwz63FineComponentMass_scale_eq_proportionalCounts
      hconfiguration k component).symm
  rw [hmass]
  exact (dwz63FinePushedProfile_eq_componentMass
    fineCount k (cellOf ∘ dwz63CoarseIndex) cell c symbol).symm

private theorem dwz63FineExactProfile_eq_sum
    (fineCount : CWDepthOneFineLetter → ℕ) (k : ℕ)
    (cell : CoarseIndex PUnit) (c : Leg) (split : SplitWord 1) :
    dwz63FineExactProfile fineCount k cell c split =
      ∑ letter,
        if dwz63FineCoarseIndex letter = cell ∧ dwz63FineSplit c letter = split then
          fineCount letter * k
        else 0 :=
  rfl

private theorem dwz63FineYPooledProfile_eq_sum
    (fineCount : CWDepthOneFineLetter → ℕ) (k : ℕ)
    (part : PUnit) (y : ℕ) (split : SplitWord 1) :
    dwz63FineYPooledProfile fineCount k part y split =
      ∑ letter,
        if yCompatibilityCell (dwz63FineCoarseIndex letter) = .pooled part y ∧
            dwz63FineSplit .Y letter = split then
          fineCount letter * k
        else 0 :=
  rfl

private theorem dwz63FineZPooledProfile_eq_sum
    (fineCount : CWDepthOneFineLetter → ℕ) (k : ℕ)
    (part : PUnit) (z : ℕ) (split : SplitWord 1) :
    dwz63FineZPooledProfile fineCount k part z split =
      ∑ letter,
        if zCompatibilityCell (dwz63FineCoarseIndex letter) = .pooled part z ∧
            dwz63FineSplit .Z letter = split then
          fineCount letter * k
        else 0 :=
  rfl

/-- A component word with the marked section 6.3 type supplies all four reference profiles of the
fine compatibility targets. -/
theorem dwz63FineReferenceProfiles_of_componentWord
    {fineCount : CWDepthOneFineLetter → ℕ}
    (hconfiguration : Dwz63FineConfiguration fineCount)
    (k n : ℕ) (word : Fin (n + 1) → Fin 15)
    (hword : word ∈ WordType.typeClass (n + 1)
      (WordType.proportionalCounts dwz63Alpha (200000000 * k))) :
    CWTotalWeightReferenceProfiles 1 n (fun _ ↦ PUnit.unit)
      (dwz63FineCompatibilityTargets fineCount k)
      (dwz63FineReferenceAddress n word) := by
  have hmultiplicity := WordType.mem_typeClass.mp hword
  refine
    { matchesX := ?_
      matchesY := ?_
      pooledY := ?_
      pooledZ := ?_ }
  · intro cell symbol
    change _ = WordType.mappedType (cwSplitWordTotalDigit 1)
      (dwz63FineExactProfile fineCount k cell .X) symbol
    rw [show dwz63FineExactProfile fineCount k cell .X =
      (fun split ↦ ∑ letter,
        if dwz63FineCoarseIndex letter = cell ∧
            dwz63FineSplit .X letter = split then
          fineCount letter * k
        else 0) from funext
          (dwz63FineExactProfile_eq_sum fineCount k cell .X)]
    exact dwz63FineReference_profile hconfiguration k n word hmultiplicity
      (fun q ↦ q) .X cell symbol
  · intro cell symbol
    change _ = WordType.mappedType (cwSplitWordTotalDigit 1)
      (dwz63FineExactProfile fineCount k cell .Y) symbol
    rw [show dwz63FineExactProfile fineCount k cell .Y =
      (fun split ↦ ∑ letter,
        if dwz63FineCoarseIndex letter = cell ∧
            dwz63FineSplit .Y letter = split then
          fineCount letter * k
        else 0) from funext
          (dwz63FineExactProfile_eq_sum fineCount k cell .Y)]
    exact dwz63FineReference_profile hconfiguration k n word hmultiplicity
      (fun q ↦ q) .Y cell symbol
  · intro part y symbol
    change _ = WordType.mappedType (cwSplitWordTotalDigit 1)
      (dwz63FineYPooledProfile fineCount k part y) symbol
    rw [show dwz63FineYPooledProfile fineCount k part y =
      (fun split ↦ ∑ letter,
        if yCompatibilityCell (dwz63FineCoarseIndex letter) = .pooled part y ∧
            dwz63FineSplit .Y letter = split then
          fineCount letter * k
        else 0) from funext
          (dwz63FineYPooledProfile_eq_sum fineCount k part y)]
    exact dwz63FineReference_profile hconfiguration k n word hmultiplicity
      yCompatibilityCell .Y (.pooled part y) symbol
  · intro part z symbol
    change _ = WordType.mappedType (cwSplitWordTotalDigit 1)
      (dwz63FineZPooledProfile fineCount k part z) symbol
    rw [show dwz63FineZPooledProfile fineCount k part z =
      (fun split ↦ ∑ letter,
        if zCompatibilityCell (dwz63FineCoarseIndex letter) = .pooled part z ∧
            dwz63FineSplit .Z letter = split then
          fineCount letter * k
        else 0) from funext
          (dwz63FineZPooledProfile_eq_sum fineCount k part z)]
    exact dwz63FineReference_profile hconfiguration k n word hmultiplicity
      zCompatibilityCell .Z (.pooled part z) symbol

/-- Every member of the marked hashing family supplies the fine targets' four reference-profile
equations. -/
theorem dwz63FineReferenceProfiles_of_mem_dwz63MarkedWords
    {fineCount : CWDepthOneFineLetter → ℕ}
    (hconfiguration : Dwz63FineConfiguration fineCount)
    (k n : ℕ) (referenceWord : PositiveWord CWSquareSupport n)
    (hreferenceWord : referenceWord ∈ dwz63MarkedWords n
      (WordType.proportionalCounts dwz63Alpha (200000000 * k))) :
    CWTotalWeightReferenceProfiles 1 n (fun _ ↦ PUnit.unit)
      (dwz63FineCompatibilityTargets fineCount k)
      (PartitionHashEncoding.supportWordAddress
        (A := fun _ : Leg ↦ Fin 5) (support := cwSquareSupport)
        n referenceWord) := by
  let word := (dwz63WordEquiv n).symm referenceWord
  have hword : word ∈ WordType.typeClass (n + 1)
      (WordType.proportionalCounts dwz63Alpha (200000000 * k)) := by
    apply (mem_dwz63MarkedWords_dwz63WordEquiv n _ word).mp
    simpa [word] using hreferenceWord
  have hprofiles :=
    dwz63FineReferenceProfiles_of_componentWord hconfiguration k n word hword
  simpa [dwz63FineReferenceAddress, word] using hprofiles

end

end AlgebraicComplexity.Examples
