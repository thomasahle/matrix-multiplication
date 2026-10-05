/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.SplitRequirementsBoundaryReflection
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoFiniteSplit
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoStepOneCompatiblePosition

/-!
# The finite DWZ instance of reflected-boundary compatibility

This applies the shared count constructor to [duan2023faster], section 6.1,
`papers/sources/2210.10173/global_value.tex:63-71`, claim
`lemma:triple_implies_compatible`, with the section 6.3 finite-decoded split record
(lines 332-378). The support and keep rules are the actual Step-1 rules of lines 52-61.

Following the proof at lines 68-70, first take typicalness from the Z rule. For a boundary
cell use the retained Y word when X has index zero, or the retained X word when Y has index
zero. Retained-leg uniqueness identifies its component word; the native zero-component
support equations give pointwise reflection. The shared constructor cancels that reflection.

The only construction-specific work is identifying these actual words and support equations.
This does not assume or call the existing literal compatibility theorem. It proves a
consequence for surviving addresses, not their existence, full finite Checks, or a new bound.
-/

set_option autoImplicit false

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor CompatibleSplit

universe u

noncomputable section

variable {n : Nat}

/-- A surviving Step-1 address is compatible for the finite-decoded DWZ split record.
The retained X/Y uniqueness and native support hypotheses are exactly the paper's inputs. -/
theorem dwz63FiniteSplitPair_stepOneCut_isCompatible (K : Type u) [CommRing K]
    {retained : Finset (BlockAddress fun _ : Leg ↦ PositiveWord (Fin 5) n)} (a₀ : retained)
    (s : Nat)
    (hX : Set.InjOn (fun g : BlockAddress fun _ : Leg ↦ PositiveWord (Fin 5) n ↦ g Leg.X)
      (retained : Set (BlockAddress fun _ : Leg ↦ PositiveWord (Fin 5) n)))
    (hY : Set.InjOn (fun g : BlockAddress fun _ : Leg ↦ PositiveWord (Fin 5) n ↦ g Leg.Y)
      (retained : Set (BlockAddress fun _ : Leg ↦ PositiveWord (Fin 5) n)))
    (addr : BlockAddress fun _ : Leg ↦ PositiveWord (PositiveWord CWBlock 1) n)
    (haddr : addr ∈ (dwz63FineStepOneCut K n retained a₀ s).support) :
    (dwz63FiniteSplitPair s).IsCompatible
      (dwz63CellWordOfAddress
        (coarsenBlockAddress (fun c ↦ positiveWordMap (cwSquareDegreeMap c) n) addr))
      (positiveWordEquiv (PositiveWord CWBlock 1) n (addr Leg.Z)) := by
  classical
  rw [dwz63FiniteSplitPair_eq]
  obtain ⟨hpre, hkeep⟩ :=
    (PartitionedTensor.mem_select_support (dwz63PreimageFine K n retained)
      (dwz63FineStepOneKeep retained a₀ s) addr).mp haddr
  obtain ⟨hsup, hret⟩ := (mem_dwz63PreimageFine_support K n retained addr).mp hpre
  have hidx : ∀ (c : Leg) (i : Fin (n + 1)),
      dwz63Cell (dwz63CellWordOfAddress
          (coarsenBlockAddress (fun c ↦ positiveWordMap (cwSquareDegreeMap c) n) addr) i) c =
        cwSquareBlockDegree (positiveWordEquiv (PositiveWord CWBlock 1) n (addr c) i) :=
    fun c i ↦ congrFun (dwz63_cell_cellWordOfAddress K addr hsup i) c
  have htyp : (dwz63SplitPair s).IsTypical
      ((dwz63SplitPair s).zIndex ∘ dwz63CellWordOfAddress
        (coarsenBlockAddress (fun c ↦ positiveWordMap (cwSquareDegreeMap c) n) addr))
      (positiveWordEquiv (PositiveWord CWBlock 1) n (addr Leg.Z)) := by
    have hword : ((dwz63SplitPair s).zIndex ∘ dwz63CellWordOfAddress
        (coarsenBlockAddress (fun c ↦ positiveWordMap (cwSquareDegreeMap c) n) addr)) =
        fun i ↦ cwSquareBlockDegree
          (positiveWordEquiv (PositiveWord CWBlock 1) n (addr Leg.Z) i) :=
      funext fun i ↦ hidx Leg.Z i
    rw [hword]
    exact hkeep Leg.Z
  apply (dwz63SplitPair s).isCompatible_of_reflectedBoundary _ _
    cwSquareComplementLetter cwSquareComplementLetter_involutive htyp
  intro t ht
  rcases dwz63_boundary_index_zero t ht with hx | hy
  · refine ⟨positiveWordEquiv (PositiveWord CWBlock 1) n (addr Leg.Y), ?_, ?_⟩
    · have htriple : (dwz63TripleOfLegWord retained a₀ Leg.Y
          (positiveWordMap (cwSquareDegreeMap Leg.Y) n (addr Leg.Y)) :
            BlockAddress fun _ : Leg ↦ PositiveWord (Fin 5) n) =
          coarsenBlockAddress (fun c ↦ positiveWordMap (cwSquareDegreeMap c) n) addr :=
        congrArg Subtype.val (dwz63_tripleOfLegWord_eq a₀ Leg.Y hY
          (a := ⟨coarsenBlockAddress (fun c ↦ positiveWordMap (cwSquareDegreeMap c) n) addr,
            hret⟩) rfl)
      have hky := hkeep Leg.Y t hx
      rwa [htriple] at hky
    · intro i hi
      have hzero : cwSquareBlockDegree
          (positiveWordEquiv (PositiveWord CWBlock 1) n (addr Leg.X) i) = 0 := by
        rw [← hidx Leg.X i, hi]
        exact hx
      exact cwSquare_fineY_eq_complement_of_zeroX
        (fun c ↦ positiveWordEquiv (PositiveWord CWBlock 1) n (addr c) i)
        (dwz63_fineLetterAddress_mem_cwSquareRawSupport K addr hsup i) hzero
  · refine ⟨positiveWordEquiv (PositiveWord CWBlock 1) n (addr Leg.X), ?_, ?_⟩
    · have htriple : (dwz63TripleOfLegWord retained a₀ Leg.X
          (positiveWordMap (cwSquareDegreeMap Leg.X) n (addr Leg.X)) :
            BlockAddress fun _ : Leg ↦ PositiveWord (Fin 5) n) =
          coarsenBlockAddress (fun c ↦ positiveWordMap (cwSquareDegreeMap c) n) addr :=
        congrArg Subtype.val (dwz63_tripleOfLegWord_eq a₀ Leg.X hX
          (a := ⟨coarsenBlockAddress (fun c ↦ positiveWordMap (cwSquareDegreeMap c) n) addr,
            hret⟩) rfl)
      have hkx := hkeep Leg.X t hy
      rwa [htriple] at hkx
    · intro i hi
      have hzero : cwSquareBlockDegree
          (positiveWordEquiv (PositiveWord CWBlock 1) n (addr Leg.Y) i) = 0 := by
        rw [← hidx Leg.Y i, hi]
        exact hy
      exact cwSquare_fineX_eq_complement_of_zeroY
        (fun c ↦ positiveWordEquiv (PositiveWord CWBlock 1) n (addr c) i)
        (dwz63_fineLetterAddress_mem_cwSquareRawSupport K addr hsup i) hzero

end

end AlgebraicComplexity.Examples
