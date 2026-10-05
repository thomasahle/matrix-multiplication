/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoStepOneCutGroupedSum
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoSeedInputs

set_option autoImplicit false

/-!
# The standard-form leaf's own blocks survive Additional Zeroing-Out Step 1

Layer 4 (`AlgebraicComplexity/Examples/`).  One theorem, `dwz63_stepOneKeep_of_leafAvailable`: an
address of the fine double power that lies over a retained triple and whose fine `Z`-word has the
prescribed per-component split profile satisfies all three rules of Additional Zeroing-Out Step 1
(`[duan2023faster]`, section 6.1 `sec:global-algo`,
`papers/sources/2210.10173/global_value.tex:52-61`).

## Which paper statement this is

It is the **converse reading of the displayed chain at `global_value.tex:70`**, inside the proof of
`lemma:triple_implies_compatible` (`:63-72`).  The paper writes, on a component with `j = 0`,

> As `j = 0` and `Î + Ĵ + K̂ = (2^{ℓ-1}, …, 2^{ℓ-1})`, we necessarily have that
> `split(K̂, S_{i,0,k})(k') = split(Î, S_{i,0,k})(2^{ℓ-1} - k')`.  (`:70`)

The paper reads this chain left to right, deducing the `K̂`-split from the retained `X̂`-rule.
The
identity is an equality, so on such a component the `Î`-split and the `K̂`-split determine each
other; read right to left it says that a block whose `K̂`-split is `splres_{i,0,k}` has
`split(Î, S_{i,0,k}) = splres^{(X)}_{i,0,k}`, which is exactly the `X̂` zeroing rule of `:57`.
The
`i = 0` half is the paper's "Due to symmetry" (`:70`) and uses the mirror complementarity.  The
`Ẑ`
rule of `:54` is `item:split-match` (`:47`), which the prescribed profile gives directly.

The hypothesis `havail` is the standard-form leaf's own defining condition: the target tensor of
`:99`,

> `𝒯^* ≝ ⨂_{i+j+k = 2^ℓ} T_{i,j,k}^{⊗ n α(i,j,k)}[splres_{i,j,k}]`,  (`:99`)

is a restricted-splitting power, and `:102` records that it "exactly matches
`def:standard_form_tensor` with parameters `⟨n α(i,j,k), i, j, k, α̃_{i,j,k}⟩`"; its
`Z`-blocks are
by construction those with split profile `α̃_{i,j,k}` on the positions of component `(i,j,k)`.  At
the section 6.3 instance (`:332-378`) the fifteen components and their `α̃` are `dwz63Alpha` and
`dwz63AlphaTilde`, and `havail` is `SegmentedAvailableWord`'s membership condition.

**Disclosed deviation.** The paper never states this converse as a separate claim --- it does not
need to, because it constructs `𝒯^{(2)}|_{X_I,Y_J,Z_K}` as a sub-object of `𝒯^{(1)}` and so
never
has to re-enter the cut.  In the Lean development the leaf is characterised by its own `Keeps`
predicate and the containment must be proved; the proof used here is the paper's `:70` identity and
nothing else.  This is recorded on the board.

Primary source `[duan2023faster]`: Ran Duan, Hongxun Wu and Renfei Zhou, *Faster Matrix
Multiplication via Asymmetric Hashing*, arXiv:2210.10173, section 6.1 `sec:global-algo`,
`papers/sources/2210.10173/global_value.tex:47, 52-61, 63-72, 98-102`, instantiated at section 6.3
(`:332-378`).
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor CompatibleSplit

universe u

noncomputable section

variable {n : ℕ}

/-- **N4: the leaf's own blocks survive Step 1.**

An address of the fine double power lying over the retained triple `a`, whose fine `Z`-word has the
component-wise split profile `alphaTilde` prescribed by the standard-form leaf (`:99`, `:102`),
satisfies all three zeroing rules of Additional Zeroing-Out Step 1 (`:52-61`).

Proof sketch, one rule at a time.  The `Ẑ` rule (`:54` via `item:split-match` `:47`) is
typicalness,
which the prescribed profile gives through `isUseful_of_segmentedAvailableWord` and the committed
refinement chain `usefulSet ⊆ compatibleSet ⊆ typicalSet`; the large `Z`-index word is the fine
`Z`-degree word by `dwz63_cell_cellWordOfAddress` at `Leg.Z`.  The `X̂` rule (`:55-57`) is the
identity at `:70` read right to left: on a component with `dwz63YIndex t = 0` the fine `Y`-letter
has degree zero at every position of the segment, so the fine `X`-letter is the letterwise
complement of the fine `Z`-letter (image 137); the segment distribution therefore reflects along
that involution (`segmentMultiplicity_comp_involutive`), and the prescribed `Z`-profile becomes
`dwz63SplresReflected`.  The `Ŷ` rule (`:58-60`) is the paper's "Due to symmetry" half, with image
139's mirror complementarity.  `hX` and `hY` are the paper's "`X_I` (if retained) is in a unique
triple" (`:55`, `:58`), used through `dwz63_tripleOfLegWord_eq`. -/
theorem dwz63_stepOneKeep_of_leafAvailable (K : Type u) [CommRing K]
    {retained : Finset (BlockAddress fun _ : Leg ↦ PositiveWord (Fin 5) n)} (a₀ : retained)
    (s : ℕ)
    (hX : Set.InjOn (fun g : BlockAddress fun _ : Leg ↦ PositiveWord (Fin 5) n ↦ g Leg.X)
      (retained : Set (BlockAddress fun _ : Leg ↦ PositiveWord (Fin 5) n)))
    (hY : Set.InjOn (fun g : BlockAddress fun _ : Leg ↦ PositiveWord (Fin 5) n ↦ g Leg.Y)
      (retained : Set (BlockAddress fun _ : Leg ↦ PositiveWord (Fin 5) n)))
    {alphaTilde : Fin 15 → PositiveWord CWBlock 1 → ℕ}
    (hS : (dwz63SplitPair s).splitCount = alphaTilde)
    (a : retained)
    (x : BlockAddress fun _ : Leg ↦ PositiveWord (PositiveWord CWBlock 1) n)
    (hpow : x ∈ (dwz63FineDoublePower K n).support)
    (hcoarse : coarsenBlockAddress (fun c ↦ positiveWordMap (cwSquareDegreeMap c) n) x =
      (a : BlockAddress fun _ : Leg ↦ PositiveWord (Fin 5) n))
    (havail : ∀ t, segmentMultiplicity
      (dwz63CellWordOfAddress (a : BlockAddress fun _ : Leg ↦ PositiveWord (Fin 5) n))
      (positiveWordEquiv (PositiveWord CWBlock 1) n (x Leg.Z)) t = alphaTilde t) :
    ∀ c, dwz63FineStepOneKeep retained a₀ s c (x c) := by
  classical
  -- the component word of the triple is the one read off the address (`:32`)
  have hcomp : dwz63CellWordOfAddress
      (a : BlockAddress fun _ : Leg ↦ PositiveWord (Fin 5) n) =
      dwz63CellWordOfAddress
        (coarsenBlockAddress (fun c ↦ positiveWordMap (cwSquareDegreeMap c) n) x) := by
    rw [hcoarse]
  have hidx : ∀ (c : Leg) (i : Fin (n + 1)),
      dwz63Cell (dwz63CellWordOfAddress
          (a : BlockAddress fun _ : Leg ↦ PositiveWord (Fin 5) n) i) c =
        cwSquareBlockDegree (positiveWordEquiv (PositiveWord CWBlock 1) n (x c) i) := by
    intro c i
    rw [hcomp]
    exact congrFun (dwz63_cell_cellWordOfAddress K x hpow i) c
  -- the `:70` identity, in the form both boundary halves need
  have key : ∀ (c₀ : Leg) (t : Fin 15),
      (∀ i, dwz63CellWordOfAddress
            (a : BlockAddress fun _ : Leg ↦ PositiveWord (Fin 5) n) i = t →
          positiveWordEquiv (PositiveWord CWBlock 1) n (x c₀) i =
            cwSquareComplementLetter
              (positiveWordEquiv (PositiveWord CWBlock 1) n (x Leg.Z) i)) →
      segmentMultiplicity
          (dwz63CellWordOfAddress (a : BlockAddress fun _ : Leg ↦ PositiveWord (Fin 5) n))
          (positiveWordEquiv (PositiveWord CWBlock 1) n (x c₀)) t =
        dwz63SplresReflected s t := by
    intro c₀ t hcompl
    have hrefl := segmentMultiplicity_comp_involutive
      (dwz63CellWordOfAddress (a : BlockAddress fun _ : Leg ↦ PositiveWord (Fin 5) n))
      (positiveWordEquiv (PositiveWord CWBlock 1) n (x c₀))
      (positiveWordEquiv (PositiveWord CWBlock 1) n (x Leg.Z)) t
      cwSquareComplementLetter cwSquareComplementLetter_involutive hcompl
    funext p
    rw [hrefl, havail t, ← hS]
    rfl
  intro c
  cases c with
  | X =>
      show ∀ t : Fin 15, dwz63YIndex t = 0 → _
      intro t ht
      have htriple : (dwz63TripleOfLegWord retained a₀ Leg.X
          (positiveWordMap (cwSquareDegreeMap Leg.X) n (x Leg.X)) :
            BlockAddress fun _ : Leg ↦ PositiveWord (Fin 5) n) =
          (a : BlockAddress fun _ : Leg ↦ PositiveWord (Fin 5) n) :=
        congrArg Subtype.val
          (dwz63_tripleOfLegWord_eq a₀ Leg.X hX (a := a) (congrFun hcoarse Leg.X).symm)
      rw [htriple]
      refine key Leg.X t ?_
      intro i hi
      have hzero : cwSquareBlockDegree
          (positiveWordEquiv (PositiveWord CWBlock 1) n (x Leg.Y) i) = 0 := by
        rw [← hidx Leg.Y i, hi]
        exact ht
      exact cwSquare_fineX_eq_complement_of_zeroY
        (fun c ↦ positiveWordEquiv (PositiveWord CWBlock 1) n (x c) i)
        (dwz63_fineLetterAddress_mem_cwSquareRawSupport K x hpow i) hzero
  | Y =>
      show ∀ t : Fin 15, dwz63XIndex t = 0 → _
      intro t ht
      have htriple : (dwz63TripleOfLegWord retained a₀ Leg.Y
          (positiveWordMap (cwSquareDegreeMap Leg.Y) n (x Leg.Y)) :
            BlockAddress fun _ : Leg ↦ PositiveWord (Fin 5) n) =
          (a : BlockAddress fun _ : Leg ↦ PositiveWord (Fin 5) n) :=
        congrArg Subtype.val
          (dwz63_tripleOfLegWord_eq a₀ Leg.Y hY (a := a) (congrFun hcoarse Leg.Y).symm)
      rw [htriple]
      refine key Leg.Y t ?_
      intro i hi
      have hzero : cwSquareBlockDegree
          (positiveWordEquiv (PositiveWord CWBlock 1) n (x Leg.X) i) = 0 := by
        rw [← hidx Leg.X i, hi]
        exact ht
      exact cwSquare_fineY_eq_complement_of_zeroX
        (fun c ↦ positiveWordEquiv (PositiveWord CWBlock 1) n (x c) i)
        (dwz63_fineLetterAddress_mem_cwSquareRawSupport K x hpow i) hzero
  | Z =>
      show (dwz63SplitPair s).IsTypical _ _
      have huseful : (dwz63SplitPair s).IsUseful
          (dwz63CellWordOfAddress (a : BlockAddress fun _ : Leg ↦ PositiveWord (Fin 5) n))
          (positiveWordEquiv (PositiveWord CWBlock 1) n (x Leg.Z)) :=
        isUseful_of_segmentedAvailableWord (dwz63SplitPair s)
          (dwz63CellWordOfAddress (a : BlockAddress fun _ : Leg ↦ PositiveWord (Fin 5) n))
          alphaTilde hS ⟨x Leg.Z, havail⟩
      have htyp := (dwz63SplitPair s).mem_typicalSet.1
        ((dwz63SplitPair s).mem_typicalSet_of_mem_compatibleSet
          ((dwz63SplitPair s).mem_compatibleSet_of_mem_usefulSet
            ((dwz63SplitPair s).mem_usefulSet.2 huseful)))
      have hword : (dwz63SplitPair s).zIndex ∘
          dwz63CellWordOfAddress (a : BlockAddress fun _ : Leg ↦ PositiveWord (Fin 5) n) =
          fun i ↦ cwSquareBlockDegree
            (positiveWordEquiv (PositiveWord CWBlock 1) n (x Leg.Z) i) :=
        funext fun i ↦ hidx Leg.Z i
      rw [hword] at htyp
      exact htyp

end

end AlgebraicComplexity.Examples
