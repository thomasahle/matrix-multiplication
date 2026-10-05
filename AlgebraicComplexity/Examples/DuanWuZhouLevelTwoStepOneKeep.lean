/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoFineComplementaryLetter
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoSplitAlphabetBridge
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoPreimageAmbient

set_option autoImplicit false

/-!
# Additional Zeroing-Out Step 1

Layer 4 (`AlgebraicComplexity/Examples/`).  This module transcribes **Additional Zeroing-Out
Step 1** of `[duan2023faster]` (`papers/sources/2210.10173/global_value.tex:32-73`) at level
`ℓ = 2`, where `2 ^ ℓ = 4` and `2 ^ (ℓ-1) = 2`.  The tree never formalised this step; its
absence is
what made the `.Z` isolation's hole family degree-determined (image 131).

## The paper's objects, and their names here

`global_value.tex:32`: "For each level-`ℓ` component `(i,j,k)`, we use `S_{i,j,k}` to denote the
set
of positions `t ∈ [n]` where `(I_t, J_t, K_t) = (i,j,k)`.  Moreover, `S_{*,*,k}` denotes the set
of
positions `t` with `K_t = k`."  Here a large triple is a `BlockAddress (fun _ ↦ PositiveWord
(Fin 5) n)`, its component at a position is the cell index of that position's coarse square
address, and `dwz63CellWordOfAddress` is the word `t ↦ (I_t, J_t, K_t)` of component indices.  So
`S_{i,j,k}` is the fibre of `dwz63CellWordOfAddress` over `(i,j,k)` and `S_{*,*,k}` the fibre of
`dwz63ZIndex ∘ dwz63CellWordOfAddress` over `k`; both are expressed by `segmentMultiplicity`.

`global_value.tex:35`: `split_k(K̂, S)` is "the distribution of `K̂_{2t-1}` over all `t ∈ S`",
with
the remark that for `t ∈ S` one always has `K̂_{2t} = k - K̂_{2t-1}`.  At level two a small
letter
is a pair of `CWBlock`s (`PositiveWord CWBlock 1`), `K̂_{2t-1}` is its left digit and `K̂_{2t}`
its
right, and the remark says the right digit is determined on `S ⊆ S_{*,*,k}`.  The pair-valued and
left-digit-valued distributions therefore carry the same information on such an `S`, and the pair
spelling is the one the hole side already uses; the letter pushforward between the two is image
123's `dwz63_splitPair_letterPushforward`.

## The three rules

`dwz63FineStepOneKeep` is one legwise `keep`, one conjunct per leg, quoting `global_value.tex`:

* leg `.Z` --- ":54  For each `Z_K̂`, we check `item:split-match` and zero out `Z_K̂` if the
  condition is not satisfied", where `item:split-match` (`:47`) is "For each `k ∈ {0,…,2^ℓ}`,
  `split(K̂, S_{*,*,k}) = α̃_{*,*,k}`".  Formalised as `(dwz63SplitPair s).IsTypical` at the
  `Z`-degree word read off the fine word itself, which is `CompatibleSplitCountDefs.lean:145`'s
  transcription of exactly that condition.  **Legwise in `.Z`** because `S_{*,*,k}` is read off the
  `Z`-word alone.
* leg `.X` --- ":55  For each `X_Î ∈ X_I`, since `X_I` (if retained) is in a unique triple
  `(X_I, Y_J, Z_K)`, we can define the set `S_{i,j,k}` w.r.t. that triple.  For all components
  `(i,0,k)` … `:57  If for any `(i,0,k)`, `split(Î, S_{i,0,k}) ≠ splres^{(X)}_{i,0,k}`, we then
  zero out this `X_Î`."  The lookup "`X_I` is in a unique triple" is `dwz63TripleOfLegWord`, the
  same `dite` the committed `dwz63PlainCoarseGroup` (`…PlainGroupedStage.lean:102`) uses, and
  `splres^{(X)}_{i,0,k}(i') := splres_{i,0,k}(2^{ℓ-1} - i')` (`:56`) is `dwz63SplresReflected`.
  **Legwise in `.X`**, given the uniqueness the paper invokes.
* leg `.Y` --- ":58-60", the symmetric rule over the components `(0,j,k)`, with
  `splres^{(Y)}_{0,j,k}(j') := splres_{0,j,k}(2^{ℓ-1} - j')` (`:59`).

The paper's `2^{ℓ-1} - i'` is, at level two and on a fine *pair*, the letterwise
`cwSquareComplementLetter` of image 137: on a `j = 0` component `Î_s + Ĵ_s + K̂_s = 2` with
`Ĵ_s = 0`, so `Î_s = 2 - K̂_s` at both small positions.  That identity is the one the paper uses
at
`:70` to prove `lemma:triple_implies_compatible`, which is the next increment (N3).

## Why the cut is free

`global_value.tex:52-61` zeroes out *one leg's small block at a time*, so the keep is legwise and
`PartitionedTensor.select_support_isProjectionClosed_univ`
(`Tensor/PartitionedGroupingBoxes.lean:60`) plus `Restricts.partitionedProjectionClosed`
(`Tensor/PartitionedExtraction.lean:117`) give the restriction with **no** hypothesis --- the
two-line pattern of `…PlainMarginalAmbient.lean:101-110`.  This is why Step 1 is not the
per-address cut image 77 declined.

## Disclosures

* The paper's `split` (`:35`) is the **left**-digit distribution; the three rules here compare full
  **pair** distributions.  `:35`'s own parenthetical --- "for those `t ∈ S`, we always have
  `K̂_{2t} = k - K̂_{2t-1}`" --- says these are the same condition on the sets `split` is applied
  to, and that equivalence is proved in `Examples/DuanWuZhouLevelTwoLeftPairBridge.lean` and
  transferred to these three rules by `dwz63_fineStepOneKeep_of_leftKeep` /
  `dwz63_fineStepOneLeftKeep_of_keep` (`Examples/DuanWuZhouLevelTwoStepOneLeftKeep.lean`).
* Lean's positive words are indexed by `Fin (n + 1)`, so the paper's `n` positions appear as
  `n + 1` here, and the paper's small positions `2t-1, 2t` are the two `CWBlock` components of one
  `PositiveWord CWBlock 1` letter rather than two separate indices.
* `dwz63TripleOfLegWord` is total: on a leg word no retained triple carries it returns the fallback
  `a₀`.  The paper's "if retained" (`:55`) is the corresponding side condition, and the fallback
  is
  unreachable on the reachable ambient.

Primary source `[duan2023faster]`: Ran Duan, Hongxun Wu and Renfei Zhou, *Faster Matrix
Multiplication via Asymmetric Hashing*, arXiv:2210.10173, section 6.1 `sec:global-algo`,
`global_value.tex:32-73`.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor CompatibleSplit

universe u v

noncomputable section

variable {n : ℕ}

/-! ## The component word of a large triple (`global_value.tex:32`) -/

/-- **`t ↦ (I_t, J_t, K_t)`**, the level-`ℓ` component word of a large triple.

`global_value.tex:32` uses it to define `S_{i,j,k}`, the positions carrying component `(i,j,k)`;
here `S_{i,j,k}` is the fibre of this word over `i`, so the paper's `split(·, S_{i,j,k})` is a
`segmentMultiplicity` against it. -/
def dwz63CellWordOfAddress
    (g : BlockAddress fun _ : Leg ↦ PositiveWord (Fin 5) n) : Fin (n + 1) → Fin 15 :=
  fun i ↦ dwz63CellIndex fun c ↦ positiveWordEquiv (Fin 5) n (g c) i

/-! ## "`X_I` (if retained) is in a unique triple" (`global_value.tex:55`) -/

/-- **The retained triple carrying a given coarse leg word.**

`global_value.tex:55`: "since `X_I` (if retained) is in a unique triple `(X_I, Y_J, Z_K)`, we can
define the set `S_{i,j,k}` w.r.t. that triple".  This is that lookup, and it is the same `dite` the
committed `dwz63PlainCoarseGroup` (`…PlainGroupedStage.lean:102`) performs on the `.X` leg; the
hash's leg-injectivity certificates (`hX`, `hY`) are what make it *the* triple, exactly as the
paper's parenthesis says.  Off the retained leg words the value is the fallback `a₀`, which the
ambient never reaches. -/
def dwz63TripleOfLegWord
    (retained : Finset (BlockAddress fun _ : Leg ↦ PositiveWord (Fin 5) n)) (a₀ : retained)
    (c₀ : Leg) (lw : PositiveWord (Fin 5) n) : retained := by
  classical
  exact if h : ∃ g : retained,
      (g : BlockAddress fun _ : Leg ↦ PositiveWord (Fin 5) n) c₀ = lw then h.choose else a₀

/-! ## `splres^{(X)}` and `splres^{(Y)}` (`global_value.tex:56,59`) -/

/-- **The reflected split distribution.**

`global_value.tex:56`: `splres^{(X)}_{i,0,k}(i') := splres_{i,0,k}(2^{ℓ-1} - i')`, and `:59` the
same for `Y`.  At level two a small letter is a pair and `2^{ℓ-1} - ·` acts on both digits, which
is `cwSquareComplementLetter` (image 137); `:70` is where the paper uses that this reflection is an
involution matching `Î_s = 2 - K̂_s`. -/
def dwz63SplresReflected (s : ℕ) (t : Fin 15) (p : PositiveWord CWBlock 1) : ℕ :=
  (dwz63SplitPair s).splitCount t (cwSquareComplementLetter p)

/-! ## The three rules, as one legwise keep (`global_value.tex:52-61`) -/

/-- **Additional Zeroing-Out Step 1**, as a legwise `keep`.

One conjunct per leg, each quoted in the module docstring:

* `.Z` is `global_value.tex:54` via `item:split-match` (`:47`);
* `.X` is `global_value.tex:55-57`;
* `.Y` is `global_value.tex:58-60`.

Every conjunct depends on that leg's fine word alone --- which is what the paper's phrasing "for
each `Z_K̂` … for each `X_Î` … for each `Y_Ĵ`" says, and what makes the cut
projection-closed. -/
def dwz63FineStepOneKeep
    (retained : Finset (BlockAddress fun _ : Leg ↦ PositiveWord (Fin 5) n)) (a₀ : retained)
    (s : ℕ) : ∀ _c : Leg, PositiveWord (PositiveWord CWBlock 1) n → Prop :=
  fun c₀ w ↦
    match c₀ with
    | Leg.Z =>
        (dwz63SplitPair s).IsTypical
          (fun i ↦ cwSquareBlockDegree (positiveWordEquiv (PositiveWord CWBlock 1) n w i))
          (positiveWordEquiv (PositiveWord CWBlock 1) n w)
    | Leg.X =>
        ∀ t : Fin 15, dwz63YIndex t = 0 →
          segmentMultiplicity
            (dwz63CellWordOfAddress
              (dwz63TripleOfLegWord retained a₀ Leg.X
                (positiveWordMap (cwSquareDegreeMap Leg.X) n w) :
                BlockAddress fun _ : Leg ↦ PositiveWord (Fin 5) n))
            (positiveWordEquiv (PositiveWord CWBlock 1) n w) t = dwz63SplresReflected s t
    | Leg.Y =>
        ∀ t : Fin 15, dwz63XIndex t = 0 →
          segmentMultiplicity
            (dwz63CellWordOfAddress
              (dwz63TripleOfLegWord retained a₀ Leg.Y
                (positiveWordMap (cwSquareDegreeMap Leg.Y) n w) :
                BlockAddress fun _ : Leg ↦ PositiveWord (Fin 5) n))
            (positiveWordEquiv (PositiveWord CWBlock 1) n w) t = dwz63SplresReflected s t

noncomputable instance dwz63FineStepOneKeepDecidable
    (retained : Finset (BlockAddress fun _ : Leg ↦ PositiveWord (Fin 5) n)) (a₀ : retained)
    (s : ℕ) (c₀ : Leg) (w : PositiveWord (PositiveWord CWBlock 1) n) :
    Decidable (dwz63FineStepOneKeep retained a₀ s c₀ w) :=
  Classical.dec _

/-! ## The cut, and the restriction it is free to make -/

section Cut

variable {K : Type u} [CommRing K]

/-- **`𝒯^{(1)}`**, the tensor after Additional Zeroing-Out Step 1 (`global_value.tex:72-73`), at
the section 6.3 preimage ambient. -/
def dwz63FineStepOneCut (K : Type u) [CommRing K] (n : ℕ)
    (retained : Finset (BlockAddress fun _ : Leg ↦ PositiveWord (Fin 5) n)) (a₀ : retained)
    (s : ℕ) :=
  (dwz63PreimageFine K n retained).select (dwz63FineStepOneKeep retained a₀ s)

/-- **Step 1 costs nothing.**

`global_value.tex:52-61` zeroes out one leg's small blocks at a time, so the keep is legwise and
`select_support_isProjectionClosed_univ` + `partitionedProjectionClosed` give the restriction with
no hypothesis at all --- the two-line pattern of `…PlainMarginalAmbient.lean:101-110`. -/
theorem dwz63_restricts_preimageFine_stepOne (K : Type u) [CommRing K] (n : ℕ)
    (retained : Finset (BlockAddress fun _ : Leg ↦ PositiveWord (Fin 5) n)) (a₀ : retained)
    (s : ℕ) :
    Restricts (dwz63PreimageFine K n retained).realize
      (dwz63FineStepOneCut K n retained a₀ s).realize :=
  Tensor.Restricts.partitionedProjectionClosed
    (dwz63PreimageFine K n retained)
    (dwz63FineStepOneCut K n retained a₀ s).support Finset.univ
    (PartitionedTensor.select_support_isProjectionClosed_univ
      (dwz63PreimageFine K n retained) (dwz63FineStepOneKeep retained a₀ s))

end Cut

end

end AlgebraicComplexity.Examples
