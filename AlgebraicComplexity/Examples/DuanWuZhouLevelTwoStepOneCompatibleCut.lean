/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoStepOneCompatiblePosition
import AlgebraicComplexity.MatrixMultiplication.SegmentMultiplicityJointWord

set_option autoImplicit false

/-!
# `lemma:triple_implies_compatible`, assembled over the Step-1 cut

Layer 4 (`AlgebraicComplexity/Examples/`).  This module proves, at level `ℓ = 2`, the claim
`lemma:triple_implies_compatible` of `[duan2023faster]`, section 6.1 `sec:global-algo`
(`papers/sources/2210.10173/global_value.tex:63-71`):

>  After Additional Zeroing-Out Step 1, a remaining small block `Z_K̂ ∈ Z_K` can form a triple
> with
>  remaining `X_Î ∈ X_I`, `Y_Ĵ ∈ Y_J` only when `Z_K̂` is compatible with triple `(X_I, Y_J,
> Z_K)`.
> (`:65`)

"Can form a triple with remaining `X_Î`, `Y_Ĵ`" is, in the tensor spelling, membership of the
whole
fine address in `dwz63FineStepOneCut` (`Examples/DuanWuZhouLevelTwoStepOneKeep.lean`, the paper's
`𝒯^{(1)}` of `:72`): all three legs survived the three zeroing rules of `:52-61`.  "Compatible"
is
`def:global-compatible` (`:44-50`), which the tree transcribes as
`SplitRequirements.IsCompatible = BoundaryMatched ∧ IsTypical`
(`Combinatorics/CompatibleSplitCountDefs.lean:122`, with `:117` and `:112`), and the large triple
of a fine address is its coarsening, whose component word is `dwz63CellWordOfAddress` (`:32`).

## The paper's proof, step by step

`:68` "first notice that after Additional Zeroing-Out Step 1, all `Z_K̂` that are not zeroed out
satisfy `item:split-match` (`:47`)".  That is the `.Z` conjunct of `dwz63FineStepOneKeep`
(`:54`), and it is `IsTypical` on the nose once the large `Z`-index word of the triple is
identified with the degree word read off the fine `Z`-word.  That identification is
`dwz63_cell_cellWordOfAddress` at leg `Z`, which rests on image 139's
`dwz63_coarseDegree_at_position` (`:32`) and the per-position support extraction.

`:68` "Hence, if `Z_K̂` is not compatible … it must be that for some `(i,j,k)` with `i = 0` or
`j = 0`, `split(K̂, S_{i,j,k}) ≠ splres_{i,j,k}` (`item:average`, `:48`)."  So the remaining work
is
`BoundaryMatched` on exactly the cells `dwz63Boundary` marks, and `dwz63_boundary_index_zero` is
the fifteen-cell check that `dwz63Boundary` is that `i = 0 ∨ j = 0`.

`:70` "Due to symmetry, we only have to discuss the case where `j = 0`.  By our zeroing-out rules,
we know that `split(Î, S_{i,0,k}) = splres^{(X)}_{i,0,k}`.  As `j = 0` and
`Î + Ĵ + K̂ = (2^{ℓ-1}, …, 2^{ℓ-1})`, we necessarily have that
`split(K̂, S_{i,0,k})(k') = split(Î, S_{i,0,k})(2^{ℓ-1} - k') = splres^{(X)}_{i,0,k}(2^{ℓ-1} -
k')
= splres_{i,0,k}(k')`."  At level two this chain is assembled here from four committed pieces:

* the `.X` rule of `dwz63FineStepOneKeep` (`:55-57`), applied at the retained triple the paper's
  "since `X_I` (if retained) is in a unique triple" (`:55`) names --- that uniqueness is the
  hypothesis `hX`, and `dwz63_tripleOfLegWord_eq` is where it is used;
* `Î_s = 2 - K̂_s` on a `j = 0` component, which is image 137's
  `cwSquare_fineX_eq_complement_of_zeroY`; the paper's "due to symmetry" `i = 0` half is image
  139's `cwSquare_fineY_eq_complement_of_zeroX`, needed because `item:average` (`:48`) ranges over
  both;
* the counting step `segmentMultiplicity_comp_involutive`
  (`MatrixMultiplication/SegmentMultiplicityReflect.lean`), which is the displayed chain's first
  equality;
* `splres^{(X)}` being `splres` reflected (`dwz63SplresReflected`, `:56`), so the last equality is
  the involutivity `cwSquareComplementLetter_involutive` of the reflection.

## The alphabet, and the two disclosures that remain

The paper's `split_k(K̂, S)` (`:35`) is the distribution of the **left** digit `K̂_{2t-1}`, while
every Step-1 rule used here, inherited from `dwz63FineStepOneKeep`, compares full **pair**
distributions.  The same sentence of `:35` says why that is the same condition --- "for those
`t ∈ S`, we always have `K̂_{2t} = k - K̂_{2t-1}`" --- and that equivalence is now proved, not
merely asserted: `dwz63_segmentMultiplicity_eq_iff_leftDegree`
(`Examples/DuanWuZhouLevelTwoLeftPairBridge.lean`) is the iff, and
`dwz63_fineStepOneKeep_of_leftKeep` / `dwz63_fineStepOneLeftKeep_of_keep`
(`Examples/DuanWuZhouLevelTwoStepOneLeftKeep.lean`) transfer it to the three Step-1 rules on the
reachable ambient, so the paper's `𝒯^{(1)}` and this module's are the same tensor.  The
conclusion
is also available in the paper's own alphabet as `dwz63_stepOneCut_isCompatible_left`.  The
forward half is image 123's `dwz63_splitPair_letterPushforward`.

Two disclosures remain:

* The Lean positive words are indexed by `Fin (n + 1)`, so the paper's `n` positions are `n + 1`
  here, and a level-one digit pair sits at `Fin 1`-indexed positions rather than `2t-1, 2t`.
* `dwz63TripleOfLegWord`'s fallback `a₀` on unretained leg words (the paper says "if retained") is
  never reached on a supported address: `hret` supplies the witness.

Primary source `[duan2023faster]`: Ran Duan, Hongxun Wu and Renfei Zhou, *Faster Matrix
Multiplication via Asymmetric Hashing*, arXiv:2210.10173, section 6.1 `sec:global-algo`,
`papers/sources/2210.10173/global_value.tex:32-72`.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor CompatibleSplit

universe u

noncomputable section

variable {n : ℕ}

/-- **`lemma:triple_implies_compatible` at level two.**

`[duan2023faster]`, section 6.1 `sec:global-algo`, claim `lemma:triple_implies_compatible`
(`papers/sources/2210.10173/global_value.tex:63-71`): every address surviving Additional
Zeroing-Out Step 1 --- i.e. every address of `dwz63FineStepOneCut`, the paper's `𝒯^{(1)}` (`:72`)
--- has its fine `Z`-word compatible (`def:global-compatible`, `:44-50`) with the component word of
its own retained large triple.

`hX` and `hY` are the paper's "`X_I` (if retained) is in a unique triple" (`:55`) and its `Y`
mirror (`:58`), in the `Set.InjOn` shape the committed hash certificates already produce.

Proof sketch, following `:68-70` in the paper's order.  `IsTypical` is the `.Z` rule of
`dwz63FineStepOneKeep` (`:54` via `item:split-match` `:47`), transported along
`dwz63_cell_cellWordOfAddress` at leg `Z` (`:68`, first sentence).  For `BoundaryMatched` the
boundary cells are `i = 0` or `j = 0` (`dwz63_boundary_index_zero`, `item:average` `:48`), and on
each of the two halves the displayed chain of `:70` runs: the fine `Y`- (resp. `X`-) letter has
degree zero at every position of the segment, so the fine `X`- (resp. `Y`-) letter is the
letterwise complement of the fine `Z`-letter there (images 137 and 139); the segment distributions
then reflect along that involution (`segmentMultiplicity_comp_involutive`); the `.X` (resp. `.Y`)
rule of Step 1 (`:55-57`, `:58-60`) equates the reflected distribution with `splres^{(X)}` (resp.
`splres^{(Y)}`), which is `splres` reflected (`dwz63SplresReflected`, `:56`, `:59`); and
involutivity of the reflection cancels, leaving `split(K̂, S_{i,j,k}) = splres_{i,j,k}`. -/
theorem dwz63_stepOneCut_isCompatible (K : Type u) [CommRing K]
    {retained : Finset (BlockAddress fun _ : Leg ↦ PositiveWord (Fin 5) n)} (a₀ : retained)
    (s : ℕ)
    (hX : Set.InjOn (fun g : BlockAddress fun _ : Leg ↦ PositiveWord (Fin 5) n ↦ g Leg.X)
      (retained : Set (BlockAddress fun _ : Leg ↦ PositiveWord (Fin 5) n)))
    (hY : Set.InjOn (fun g : BlockAddress fun _ : Leg ↦ PositiveWord (Fin 5) n ↦ g Leg.Y)
      (retained : Set (BlockAddress fun _ : Leg ↦ PositiveWord (Fin 5) n)))
    (addr : BlockAddress fun _ : Leg ↦ PositiveWord (PositiveWord CWBlock 1) n)
    (haddr : addr ∈ (dwz63FineStepOneCut K n retained a₀ s).support) :
    (dwz63SplitPair s).IsCompatible
      (dwz63CellWordOfAddress
        (coarsenBlockAddress (fun c ↦ positiveWordMap (cwSquareDegreeMap c) n) addr))
      (positiveWordEquiv (PositiveWord CWBlock 1) n (addr Leg.Z)) := by
  classical
  obtain ⟨hpre, hkeep⟩ :=
    (PartitionedTensor.mem_select_support (dwz63PreimageFine K n retained)
      (dwz63FineStepOneKeep retained a₀ s) addr).mp haddr
  obtain ⟨hsup, hret⟩ := (mem_dwz63PreimageFine_support K n retained addr).mp hpre
  -- the paper's `(I_t, J_t, K_t)` (`:32`), coordinate by coordinate
  have hidx : ∀ (c : Leg) (i : Fin (n + 1)),
      dwz63Cell (dwz63CellWordOfAddress
          (coarsenBlockAddress (fun c ↦ positiveWordMap (cwSquareDegreeMap c) n) addr) i) c =
        cwSquareBlockDegree (positiveWordEquiv (PositiveWord CWBlock 1) n (addr c) i) :=
    fun c i ↦ congrFun (dwz63_cell_cellWordOfAddress K addr hsup i) c
  -- `:68`, first sentence: `item:split-match` is the `.Z` rule
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
  refine ⟨?_, htyp⟩
  intro t ht l
  -- `:70`, the displayed chain, in one form serving both halves of "due to symmetry"
  have key : ∀ (comp : Fin (n + 1) → Fin 15) (xw zw : Fin (n + 1) → PositiveWord CWBlock 1)
      (t : Fin 15), segmentMultiplicity comp xw t = dwz63SplresReflected s t →
      (∀ i, comp i = t → xw i = cwSquareComplementLetter (zw i)) →
      segmentMultiplicity comp zw t = (dwz63SplitPair s).splitCount t := by
    intro comp xw zw t hrule hcompl
    have hrefl := segmentMultiplicity_comp_involutive comp xw zw t
      cwSquareComplementLetter cwSquareComplementLetter_involutive hcompl
    funext p
    have hp : segmentMultiplicity comp zw t
          (cwSquareComplementLetter (cwSquareComplementLetter p)) =
        (dwz63SplitPair s).splitCount t
          (cwSquareComplementLetter (cwSquareComplementLetter p)) :=
      (congrFun hrefl (cwSquareComplementLetter p)).symm.trans
        (congrFun hrule (cwSquareComplementLetter p))
    rwa [cwSquareComplementLetter_involutive p] at hp
  have hseg : segmentMultiplicity
      (dwz63CellWordOfAddress
        (coarsenBlockAddress (fun c ↦ positiveWordMap (cwSquareDegreeMap c) n) addr))
      (positiveWordEquiv (PositiveWord CWBlock 1) n (addr Leg.Z)) t =
      (dwz63SplitPair s).splitCount t := by
    rcases dwz63_boundary_index_zero t ht with hx | hy
    · -- `i = 0`: the paper's "due to symmetry" half, carried by the `.Y` rule (`:58-60`)
      refine key _ (positiveWordEquiv (PositiveWord CWBlock 1) n (addr Leg.Y)) _ t ?_ ?_
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
    · -- `j = 0`: the case the paper discusses, carried by the `.X` rule (`:55-57`)
      refine key _ (positiveWordEquiv (PositiveWord CWBlock 1) n (addr Leg.X)) _ t ?_ ?_
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
  rw [multiplicity_jointWord_eq_segmentMultiplicity]
  exact congrFun hseg l

end

end AlgebraicComplexity.Examples
