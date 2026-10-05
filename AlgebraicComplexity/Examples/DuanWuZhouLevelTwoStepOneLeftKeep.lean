/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoLeftPairBridge
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoStepOneCompatibleCut
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoHoleIntegrationAvailability
import AlgebraicComplexity.Combinatorics.CompatibleSplitCount

set_option autoImplicit false

/-!
# Additional Zeroing-Out Step 1 in the paper's own alphabet

Layer 4 (`AlgebraicComplexity/Examples/`).  `[duan2023faster]`, section 6.1 `sec:global-algo`,
states Step 1 (`papers/sources/2210.10173/global_value.tex:52-61`) with `split`, which by `:35` is
the distribution of the **left** level-one digit `K̂_{2t-1}`.  The tree's
`dwz63FineStepOneKeep` (`Examples/DuanWuZhouLevelTwoStepOneKeep.lean`) states the same three rules
with full **pair** distributions.

`dwz63FineStepOneLeftKeep` below is the paper's reading, letter for letter, and
`dwz63_fineStepOneKeep_of_leftKeep` / `dwz63_fineStepOneLeftKeep_of_keep` prove the two readings
agree on every address of the reachable fine ambient.  So the paper's `𝒯^{(1)}` and the tree's
are
the same tensor, and `dwz63_stepOneCut_isCompatible` applies to the paper's object.

## Why they agree, and where the support comes from

`:35` says it: "for those `t ∈ S`, we always have `K̂_{2t} = k - K̂_{2t-1}`".  Image 155's
`dwz63_segmentMultiplicity_eq_iff_leftDegree` turns that into an iff, given that the observed and
the prescribed profile are both supported on one level-two degree.  Those support facts are proved
here, at the entry point, for each of the three rules:

* the **aggregate `IsTypical` rows** (`item:split-match`, `:47`) --- `dwz63_typicalType_zDegree`:
  the row of `typicalType` at `k` is the `zIndex`-fibre sum of the split table
  (`mappedType_prodMap_id_apply`), and every summand is supported on the degree `dwz63ZIndex c = k`
  by `dwz63_joinedAlphaTilde_zDegree`.  The observed row is supported by construction: the
  segmentation of the `.Z` rule *is* the fine `Z`-degree word.
* the **boundary component rows** (`item:average`, `:48`) --- `dwz63_boundary_index_sum` gives
  `i + k = 4` on a `j = 0` component and `j + k = 4` on an `i = 0` one, and
  `dwz63_cwSquareComplementLetter_degree_add` gives `deg p + deg (2 - p) = 4`; together the
  reflected target `dwz63SplresReflected` (`:56`, `:59`) is supported on the component's own `X`-
  (resp. `Y`-) degree.
* the **observed `X`/`Y` words** --- image 143's `dwz63_cell_cellWordOfAddress` reads the component
  of a position off the *supported* fine address, so on the segment of component `t` the fine
  `X`-letter has degree `dwz63XIndex t`.  This is why the transfer is stated on
  `(dwz63PreimageFine K n retained).support` rather than for arbitrary words.

Primary source `[duan2023faster]`: Ran Duan, Hongxun Wu and Renfei Zhou, *Faster Matrix
Multiplication via Asymmetric Hashing*, arXiv:2210.10173, section 6.1 `sec:global-algo`,
`papers/sources/2210.10173/global_value.tex:32, 35, 44-50, 52-61`.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor CompatibleSplit WordType
open scoped BigOperators

universe u

noncomputable section

variable {n : ℕ}

/-! ## The three support facts (`global_value.tex:35, 47, 48`) -/

/-- **The aggregate row at `k` is supported on level-two degree `k`** (C2's obligation (i)).

`typicalType` pools the split table over the `zIndex` fibre of `k` (`item:split-match`, `:47`), and
every table row is supported on its own `Z`-degree by `dwz63_joinedAlphaTilde_zDegree`. -/
theorem dwz63_typicalType_zDegree (s : ℕ) (k : Fin 5) (p : PositiveWord CWBlock 1)
    (h : (dwz63SplitPair s).typicalType (k, p) ≠ 0) : cwSquareBlockDegree p = k := by
  classical
  rw [SplitRequirements.typicalType, SplitRequirements.mappedType_prodMap_id_apply] at h
  obtain ⟨c, hc, hne⟩ : ∃ c ∈ letterFiber (dwz63SplitPair s).zIndex k,
      (dwz63SplitPair s).usefulType (c, p) ≠ 0 := by
    by_contra hall
    refine h (Finset.sum_eq_zero fun c hc ↦ ?_)
    by_contra hne
    exact hall ⟨c, hc, hne⟩
  have hz : dwz63ZIndex c = k := mem_letterFiber.mp hc
  rw [← hz]
  exact dwz63_joinedAlphaTilde_zDegree s c p hne

/-- **`deg p + deg (2 - p) = 4`**, the level-two form of the paper's reflection `2^{ℓ-1} - i'`
(`global_value.tex:56, 59`). -/
theorem dwz63_cwSquareComplementLetter_degree_add (p : PositiveWord CWBlock 1) :
    (cwSquareBlockDegree p).val + (cwSquareBlockDegree (cwSquareComplementLetter p)).val = 4 := by
  obtain ⟨a, b⟩ := p
  have ha := cwBlockDegree_cwBlockComplement a
  have hb := cwBlockDegree_cwBlockComplement b
  show cwBlockDegree a + cwBlockDegree b +
    (cwBlockDegree (cwBlockComplement a) + cwBlockDegree (cwBlockComplement b)) = 4
  omega

/-- **The boundary components' index arithmetic** (`global_value.tex:48`): on `j = 0` the `X`- and
`Z`-indices sum to `2^ℓ = 4`, and on `i = 0` the `Y`- and `Z`-indices do. -/
theorem dwz63_boundary_index_sum (t : Fin 15) :
    (dwz63YIndex t = 0 → (dwz63XIndex t).val + (dwz63ZIndex t).val = 4) ∧
      (dwz63XIndex t = 0 → (dwz63YIndex t).val + (dwz63ZIndex t).val = 4) := by
  revert t
  decide

/-! ## Step 1, as the paper states it (`global_value.tex:52-61`) -/

/-- **Additional Zeroing-Out Step 1 with the paper's `split`.**

Identical to `dwz63FineStepOneKeep` except that every distribution is pushed forward along
`dwz63FineLeftDegree`, so each rule compares *left-digit* distributions --- which is what `:35`
defines `split` to be, and what `:54`, `:57` and `:60` compare. -/
def dwz63FineStepOneLeftKeep
    (retained : Finset (BlockAddress fun _ : Leg ↦ PositiveWord (Fin 5) n)) (a₀ : retained)
    (s : ℕ) : ∀ _c : Leg, PositiveWord (PositiveWord CWBlock 1) n → Prop :=
  fun c₀ w ↦
    match c₀ with
    | Leg.Z =>
        ∀ k : Fin 5, mappedType dwz63FineLeftDegree
            (segmentMultiplicity
              (fun i ↦ cwSquareBlockDegree (positiveWordEquiv (PositiveWord CWBlock 1) n w i))
              (positiveWordEquiv (PositiveWord CWBlock 1) n w) k) =
          mappedType dwz63FineLeftDegree (fun p ↦ (dwz63SplitPair s).typicalType (k, p))
    | Leg.X =>
        ∀ t : Fin 15, dwz63YIndex t = 0 →
          mappedType dwz63FineLeftDegree
              (segmentMultiplicity
                (dwz63CellWordOfAddress
                  (dwz63TripleOfLegWord retained a₀ Leg.X
                    (positiveWordMap (cwSquareDegreeMap Leg.X) n w) :
                    BlockAddress fun _ : Leg ↦ PositiveWord (Fin 5) n))
                (positiveWordEquiv (PositiveWord CWBlock 1) n w) t) =
            mappedType dwz63FineLeftDegree (dwz63SplresReflected s t)
    | Leg.Y =>
        ∀ t : Fin 15, dwz63XIndex t = 0 →
          mappedType dwz63FineLeftDegree
              (segmentMultiplicity
                (dwz63CellWordOfAddress
                  (dwz63TripleOfLegWord retained a₀ Leg.Y
                    (positiveWordMap (cwSquareDegreeMap Leg.Y) n w) :
                    BlockAddress fun _ : Leg ↦ PositiveWord (Fin 5) n))
                (positiveWordEquiv (PositiveWord CWBlock 1) n w) t) =
            mappedType dwz63FineLeftDegree (dwz63SplresReflected s t)

/-! ## The two readings of Step 1 agree on the reachable ambient -/

section Transfer

variable {K : Type u} [CommRing K]
variable {retained : Finset (BlockAddress fun _ : Leg ↦ PositiveWord (Fin 5) n)}

/-- **The reflected target is supported on the component's own `X`- or `Y`-degree.**

`dwz63SplresReflected` (`global_value.tex:56, 59`) is the split table read through the reflection
`2^{ℓ-1} - ·`; its support therefore sits at `4 - dwz63ZIndex t`, which on a `j = 0` component is
`dwz63XIndex t` and on an `i = 0` component is `dwz63YIndex t` (`dwz63_boundary_index_sum`). -/
theorem dwz63_splresReflected_degree (s : ℕ) (t : Fin 15) (p : PositiveWord CWBlock 1)
    (h : dwz63SplresReflected s t p ≠ 0) :
    (cwSquareBlockDegree p).val + (dwz63ZIndex t).val = 4 := by
  have hz : cwSquareBlockDegree (cwSquareComplementLetter p) = dwz63ZIndex t :=
    dwz63_joinedAlphaTilde_zDegree s t (cwSquareComplementLetter p) h
  have hsum := dwz63_cwSquareComplementLetter_degree_add p
  rw [hz] at hsum
  exact hsum

/-- **Step 1 as the paper states it implies Step 1 as the tree states it**, on the reachable fine
ambient (`global_value.tex:35, 52-61`).

Proof sketch: each of the three rules is an instance of image 155's
`dwz63_segmentMultiplicity_eq_iff_leftDegree`.  The `.Z` rule's segmentation is the fine `Z`-degree
word, so its observed support is definitional and its prescribed support is
`dwz63_typicalType_zDegree`; the `.X` and `.Y` rules read their component off the supported fine
address through `dwz63_cell_cellWordOfAddress`, and their prescribed support is
`dwz63_splresReflected_degree` combined with `dwz63_boundary_index_sum`. -/
theorem dwz63_fineStepOneKeep_of_leftKeep (K : Type u) [CommRing K] (a₀ : retained) (s : ℕ)
    (hX : Set.InjOn (fun g : BlockAddress fun _ : Leg ↦ PositiveWord (Fin 5) n ↦ g Leg.X)
      (retained : Set (BlockAddress fun _ : Leg ↦ PositiveWord (Fin 5) n)))
    (hY : Set.InjOn (fun g : BlockAddress fun _ : Leg ↦ PositiveWord (Fin 5) n ↦ g Leg.Y)
      (retained : Set (BlockAddress fun _ : Leg ↦ PositiveWord (Fin 5) n)))
    (x : BlockAddress fun _ : Leg ↦ PositiveWord (PositiveWord CWBlock 1) n)
    (hx : x ∈ (dwz63PreimageFine K n retained).support)
    (h : ∀ c, dwz63FineStepOneLeftKeep retained a₀ s c (x c)) :
    ∀ c, dwz63FineStepOneKeep retained a₀ s c (x c) := by
  classical
  obtain ⟨hpow, hret⟩ := (mem_dwz63PreimageFine_support K n retained x).mp hx
  have hidx : ∀ (c : Leg) (i : Fin (n + 1)),
      dwz63Cell (dwz63CellWordOfAddress
          (coarsenBlockAddress (fun c ↦ positiveWordMap (cwSquareDegreeMap c) n) x) i) c =
        cwSquareBlockDegree (positiveWordEquiv (PositiveWord CWBlock 1) n (x c) i) :=
    fun c i ↦ congrFun (dwz63_cell_cellWordOfAddress K x hpow i) c
  intro c
  cases c with
  | X =>
      show ∀ t : Fin 15, dwz63YIndex t = 0 → _
      intro t ht
      have htriple : (dwz63TripleOfLegWord retained a₀ Leg.X
          (positiveWordMap (cwSquareDegreeMap Leg.X) n (x Leg.X)) :
            BlockAddress fun _ : Leg ↦ PositiveWord (Fin 5) n) =
          coarsenBlockAddress (fun c ↦ positiveWordMap (cwSquareDegreeMap c) n) x :=
        congrArg Subtype.val (dwz63_tripleOfLegWord_eq a₀ Leg.X hX
          (a := (⟨_, hret⟩ : retained)) rfl)
      have hleft := h Leg.X t ht
      rw [htriple] at hleft ⊢
      refine (dwz63_segmentMultiplicity_eq_iff_leftDegree (k := dwz63XIndex t) _ _ t _ ?_ ?_).mpr
        hleft
      · intro i hi
        rw [← hidx Leg.X i, hi]
        rfl
      · intro p hp
        have h1 := dwz63_splresReflected_degree s t p hp
        have h2 := (dwz63_boundary_index_sum t).1 ht
        exact Fin.ext (by omega)
  | Y =>
      show ∀ t : Fin 15, dwz63XIndex t = 0 → _
      intro t ht
      have htriple : (dwz63TripleOfLegWord retained a₀ Leg.Y
          (positiveWordMap (cwSquareDegreeMap Leg.Y) n (x Leg.Y)) :
            BlockAddress fun _ : Leg ↦ PositiveWord (Fin 5) n) =
          coarsenBlockAddress (fun c ↦ positiveWordMap (cwSquareDegreeMap c) n) x :=
        congrArg Subtype.val (dwz63_tripleOfLegWord_eq a₀ Leg.Y hY
          (a := (⟨_, hret⟩ : retained)) rfl)
      have hleft := h Leg.Y t ht
      rw [htriple] at hleft ⊢
      refine (dwz63_segmentMultiplicity_eq_iff_leftDegree (k := dwz63YIndex t) _ _ t _ ?_ ?_).mpr
        hleft
      · intro i hi
        rw [← hidx Leg.Y i, hi]
        rfl
      · intro p hp
        have h1 := dwz63_splresReflected_degree s t p hp
        have h2 := (dwz63_boundary_index_sum t).2 ht
        exact Fin.ext (by omega)
  | Z =>
      show (dwz63SplitPair s).IsTypical _ _
      show WordType.multiplicity (WordType.jointWord _ _) = _
      funext q
      obtain ⟨k, p⟩ := q
      rw [multiplicity_jointWord_eq_segmentMultiplicity]
      have hk := (dwz63_segmentMultiplicity_eq_iff_leftDegree (k := k)
        (fun i ↦ cwSquareBlockDegree (positiveWordEquiv (PositiveWord CWBlock 1) n (x Leg.Z) i))
        (positiveWordEquiv (PositiveWord CWBlock 1) n (x Leg.Z)) k
        (fun p ↦ (dwz63SplitPair s).typicalType (k, p))
        (fun i hi ↦ hi) (fun p hp ↦ dwz63_typicalType_zDegree s k p hp)).mpr (h Leg.Z k)
      exact congrFun hk p

/-- **The converse**: the tree's Step 1 implies the paper's, with no hypothesis.  Pushing an exact
profile equality forward along `dwz63FineLeftDegree` is `congrArg`. -/
theorem dwz63_fineStepOneLeftKeep_of_keep (a₀ : retained) (s : ℕ)
    (x : BlockAddress fun _ : Leg ↦ PositiveWord (PositiveWord CWBlock 1) n)
    (h : ∀ c, dwz63FineStepOneKeep retained a₀ s c (x c)) :
    ∀ c, dwz63FineStepOneLeftKeep retained a₀ s c (x c) := by
  classical
  intro c
  cases c with
  | X =>
      show ∀ t : Fin 15, dwz63YIndex t = 0 → _
      intro t ht
      exact congrArg (fun u ↦ mappedType dwz63FineLeftDegree u) (h Leg.X t ht)
  | Y =>
      show ∀ t : Fin 15, dwz63XIndex t = 0 → _
      intro t ht
      exact congrArg (fun u ↦ mappedType dwz63FineLeftDegree u) (h Leg.Y t ht)
  | Z =>
      show ∀ k : Fin 5, _
      intro k
      have hz : (dwz63SplitPair s).IsTypical _ _ := h Leg.Z
      refine congrArg (fun u ↦ mappedType dwz63FineLeftDegree u) ?_
      funext p
      rw [← multiplicity_jointWord_eq_segmentMultiplicity]
      exact congrFun hz (k, p)

/-- **`lemma:triple_implies_compatible`'s conclusion in the paper's own alphabet.**

`def:global-compatible` (`global_value.tex:44-50`) compares `split(K̂, ·)`, the left-digit
distribution (`:35`).  Image 143's `dwz63_stepOneCut_isCompatible` concludes compatibility for the
pair-valued record `dwz63SplitPair s`; pushing that forward along `dwz63FineLeftDegree` with the
committed `isCompatible_of_letterPushforward` and image 123's
`dwz63_splitPair_letterPushforward` gives the same conclusion for `dwz63Split s`, whose split table
is the paper's `α̃` read at the left digit. -/
theorem dwz63_stepOneCut_isCompatible_left (K : Type u) [CommRing K] (a₀ : retained) (s : ℕ)
    (hX : Set.InjOn (fun g : BlockAddress fun _ : Leg ↦ PositiveWord (Fin 5) n ↦ g Leg.X)
      (retained : Set (BlockAddress fun _ : Leg ↦ PositiveWord (Fin 5) n)))
    (hY : Set.InjOn (fun g : BlockAddress fun _ : Leg ↦ PositiveWord (Fin 5) n ↦ g Leg.Y)
      (retained : Set (BlockAddress fun _ : Leg ↦ PositiveWord (Fin 5) n)))
    (addr : BlockAddress fun _ : Leg ↦ PositiveWord (PositiveWord CWBlock 1) n)
    (haddr : addr ∈ (dwz63FineStepOneCut K n retained a₀ s).support) :
    (dwz63Split s).IsCompatible
      (dwz63CellWordOfAddress
        (coarsenBlockAddress (fun c ↦ positiveWordMap (cwSquareDegreeMap c) n) addr))
      (dwz63FineLeftDegree ∘
        positiveWordEquiv (PositiveWord CWBlock 1) n (addr Leg.Z)) :=
  SplitRequirements.isCompatible_of_letterPushforward (dwz63SplitPair s) (dwz63Split s)
    dwz63FineLeftDegree
    (dwz63SplitPair_zIndex s) (dwz63SplitPair_boundary s)
    (dwz63_splitPair_letterPushforward s)
    (dwz63_stepOneCut_isCompatible K a₀ s hX hY addr haddr)

end Transfer

end

end AlgebraicComplexity.Examples
