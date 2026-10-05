/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoStepOneCompatibleCut
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoHoleIntegrationAvailability
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoSegmentedFiberStabilizer
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoSeedSelection

set_option autoImplicit false

/-!
# The hole family of the Step-1 cut, and the three facts its competitors satisfy

Layer 4 (`AlgebraicComplexity/Examples/`).  The hole family of
`Examples/DuanWuZhouLevelTwoPreimageLeaf.lean` is built on the **uncut** preimage ambient, and that
is what made it degree-determined.  This module re-spells it on `dwz63FineStepOneCut`, the paper's
`𝒯^{(1)}` (`papers/sources/2210.10173/global_value.tex:72`), as a **new** definition --- the
uncut modules are superseded and are not imported here --- and proves the three facts that the
domination of `claim:hole_frac_low` needs of a hole's witnessing competitor.

## The paper's necessary condition

`claim:hole_frac_low` is `[duan2023faster]`, section 6.1 `sec:global-algo`,
`papers/sources/2210.10173/global_value.tex:249-265` (**not** `hole_lemma.tex`, which has 168
lines and carries `lemma:hole_lemma`/`cor:hole_lemma` instead).  Its proof opens at `:255`:

>  A necessary condition of `Z_K̂` being a hole is that there exists `I' ≠ I` matchable to `K`
> such
> that (1) `Z_K̂` is compatible with `X_{I'}`; and (2) `I'` is hashed to the same slot as `K`, i.e.
> `hashx(I') = hashz(K)`.

The three lemmas below are exactly the three clauses of that sentence, at the level-two instance:

* **`I' ≠ I` matchable to `K`** --- `dwz63_coarseZ_of_cutReferenceHole`: a hole's witnessing
  address carries the frame-transported available `Z`-word, and an available word's coarse
  `Z`-word is the reference word's own (image 125's `dwz63_coarseZ_of_segmentedAvailable`,
  `Examples/DuanWuZhouLevelTwoHoleIntegrationAvailability.lean:92`), which the reference-frame
  equation `hperm` identifies with `a`'s.  So the competitor is matchable to `K` --- it shares
  `a`'s large `Z`-block, which is `def:global-compatible`'s standing hypothesis
  `Z_K̂ ∈ Z_K` (`:45`).
* **(1) `Z_K̂` is compatible with `X_{I'}`** --- `dwz63_cutReferenceHole_isCompatible`: this is
  where the Step-1 cut pays.  The witnessing address lies in `𝒯^{(1)}`, so image 143's
  `dwz63_stepOneCut_isCompatible` (`lemma:triple_implies_compatible`, `:63-71`) says its own
  retained triple is compatible with its `Z`-word --- and its own retained triple is the
  competitor, by `dwz63PlainCoarseGroup_eq_of_x`.  On the uncut ambient this clause is simply
  false, which is the design gap the repair closes.
* **(2) `I'` is hashed to the same slot as `K`** --- `dwz63_inCommonTriple_of_zIndex_eq`: two
  marked-`XY`-isolated triples with the same hash `Z`-word sit in the same bucket, because a legal
  triple's `Z`-hash is determined by its `X`- and `Y`-hashes
  (`Seed.zHash_eq_of_commonBucket`, `Combinatorics/Hashing.lean:185`), and the bucket event is the
  two-equation common-bucket event (`Seed.inCommonTriple_iff_commonBucket`, `:198`).

`dwz63Seg_sourceWordOfLegalTriple` is the encoding bridge that lets the first two facts, which are
stated about block addresses, be read as facts about the component word
`dwz63ComponentWord`/`dwz63Seg` that `dwz63SplitCompatTyped`
(`Examples/DuanWuZhouLevelTwoCompetitorCount.lean:104`) quantifies over.

## Not here

The assembled domination --- `dwz63CutReferenceHoles a ⊆ dwz63SeedSharedHoles …`, in the
`card_le_card` shape image 129's `dwz63_exists_seed_holeFraction_and_copyCount` consumes --- is
**not** proved in this module.  What it still needs is the choice of the `component`/`read` pair
at which `dwz63SplitCompatTyped` is instantiated, together with the joint-type conjunct
(`marked` typicality) and the usefulness conjunct
(`isUseful_of_segmentedAvailableWord`, `Examples/DuanWuZhouLevelTwoSeedInputs.lean:235`), neither
of which is a fact about the cut.

Primary source `[duan2023faster]`: Ran Duan, Hongxun Wu and Renfei Zhou, *Faster Matrix
Multiplication via Asymmetric Hashing*, arXiv:2210.10173, section 6.1 `sec:global-algo`,
`papers/sources/2210.10173/global_value.tex:44-72, 249-265`.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor ProgressionHash

universe u v

noncomputable section

variable {n : ℕ}

/-! ## The hole family on the Step-1 cut -/

/-- **The reference-frame hole family of `𝒯^{(1)}`.**

The available reference words whose frame transport some address *of the Step-1 cut* carries over a
competing retained group.  This is `[duan2023faster]`'s "`Z_K̂` is a hole in
`𝒯^{(2)}|_{X_I,Y_J,Z_K}`" (`global_value.tex:251`), i.e. rule (i) of Additional Zeroing-Out Step
2
(`:84-89`) read in the reference frame; the ambient it quantifies over is the tensor after Step 1
(`:72`), which is the whole point of the repair. -/
def dwz63CutReferenceHoles (K : Type u) [CommRing K]
    (retained : Finset (BlockAddress fun _ : Leg ↦ PositiveWord (Fin 5) n))
    (a₀ : retained) (s : ℕ) (alphaTilde : Fin 15 → PositiveWord CWBlock 1 → ℕ)
    (wRef : PositiveWord ((cwSquarePartitionedTensor K dwz63Q).support) n)
    (perm : retained → Equiv.Perm (Fin (n + 1))) (a : retained) :
    Finset (SegmentedAvailableWord (dwz63Seg K n wRef) alphaTilde) := by
  classical
  exact Finset.univ.filter fun z ↦
    ∃ other ∈ (dwz63FineStepOneCut K n retained a₀ s).support,
      other Leg.Z = positiveWordPositionEquiv (PositiveWord CWBlock 1) n (perm a) z.1 ∧
        dwz63PlainCoarseGroup retained
          (fun c ↦ positiveWordMap (cwSquareDegreeMap c) n) a₀ other ≠ a

@[simp] theorem mem_dwz63CutReferenceHoles (K : Type u) [CommRing K]
    (retained : Finset (BlockAddress fun _ : Leg ↦ PositiveWord (Fin 5) n))
    (a₀ : retained) (s : ℕ) (alphaTilde : Fin 15 → PositiveWord CWBlock 1 → ℕ)
    (wRef : PositiveWord ((cwSquarePartitionedTensor K dwz63Q).support) n)
    (perm : retained → Equiv.Perm (Fin (n + 1))) (a : retained)
    (z : SegmentedAvailableWord (dwz63Seg K n wRef) alphaTilde) :
    z ∈ dwz63CutReferenceHoles K retained a₀ s alphaTilde wRef perm a ↔
      ∃ other ∈ (dwz63FineStepOneCut K n retained a₀ s).support,
        other Leg.Z = positiveWordPositionEquiv (PositiveWord CWBlock 1) n (perm a) z.1 ∧
          dwz63PlainCoarseGroup retained
            (fun c ↦ positiveWordMap (cwSquareDegreeMap c) n) a₀ other ≠ a := by
  classical
  simp [dwz63CutReferenceHoles]

/-! ## The encoding bridge (`global_value.tex:32`) -/

/-- **The segmentation of a legal triple's source word is the component word of its address.**

`dwz63Seg` (`Examples/DuanWuZhouLevelTwoSegmentationData.lean:80`) reads the cell index of each
position of a supported word; `dwz63CellWordOfAddress`
(`Examples/DuanWuZhouLevelTwoStepOneKeep.lean:32`) reads the component `(I_t, J_t, K_t)` of each
position of a block address (`global_value.tex:32`).  On the address a legal triple models, the two
are the same function, so a statement about one transfers to the other.

Proof sketch: `positiveWordEquiv_supportWordAddress` says the transposed address, read at a
position and a leg, is that position's supported address read at that leg; the two `dwz63CellIndex`
arguments then agree by eta. -/
theorem dwz63Seg_sourceWordOfLegalTriple {R : Type v} [Field R] (K : Type u) [CommRing K]
    (H : PartitionHashEncoding (R := R) ((cwSquarePartitionedTensor K dwz63Q).support))
    (x : LegalTriple R (Fin (n + 1)) H.target) :
    dwz63Seg K n (H.sourceWordOfLegalTriple n x) =
      dwz63CellWordOfAddress (H.modeledAddress n x) := by
  funext i
  show dwz63CellIndex _ = dwz63CellIndex _
  congr 1
  funext c
  exact (congrFun (PartitionHashEncoding.positiveWordEquiv_supportWordAddress n
    (H.sourceWordOfLegalTriple n x) c) i).symm

/-! ## `:255`, clause "`I'` matchable to `K`": the competitor shares `a`'s coarse `Z`-word -/

/-- **A hole's witnessing address carries `a`'s own large `Z`-block.**

`global_value.tex:255` requires the competitor `I'` to be *matchable to `K`* --- in
`def:global-compatible` (`:45`) the small block `Z_K̂` is a block **of `Z_K`**, so a competing
triple can only be a competitor if it carries the same large `Z`-block.  Here that is automatic:
the hole's witness carries the frame transport of an *available* word, whose coarse `Z`-word is the
reference word's own by image 125's `dwz63_coarseZ_of_segmentedAvailable`, and the reference-frame
equation `hperm` says the transported reference word's address is `a`.

Proof sketch: transport availability along `perm a` (`dwz63Seg_positionEquiv` moves the
segmentation, `positiveWordEquiv_position_apply` the word, and
`segmentMultiplicity_comp_perm_general` shows the segment counts are unchanged), then apply image
125 at the transported reference word and rewrite by `hperm a`. -/
theorem dwz63_coarseZ_of_cutReferenceHole (K : Type u) [CommRing K]
    (retained : Finset (BlockAddress fun _ : Leg ↦ PositiveWord (Fin 5) n))
    (alphaTilde : Fin 15 → PositiveWord CWBlock 1 → ℕ)
    (hα : ∀ t k, alphaTilde t k ≠ 0 → cwSquareDegreeMap Leg.Z k = dwz63ZIndex t)
    (wRef : PositiveWord ((cwSquarePartitionedTensor K dwz63Q).support) n)
    (perm : retained → Equiv.Perm (Fin (n + 1)))
    (hperm : ∀ b : retained, positiveSupportWordBlockAddress
        ((cwSquarePartitionedTensor K dwz63Q).support) n
        (positiveWordPositionEquiv ((cwSquarePartitionedTensor K dwz63Q).support) n (perm b) wRef)
      = (b : BlockAddress fun _ : Leg ↦ PositiveWord (Fin 5) n))
    (a : retained) (z : SegmentedAvailableWord (dwz63Seg K n wRef) alphaTilde) :
    positiveWordMap (cwSquareDegreeMap Leg.Z) n
        (positiveWordPositionEquiv (PositiveWord CWBlock 1) n (perm a) z.1) =
      (a : BlockAddress fun _ : Leg ↦ PositiveWord (Fin 5) n) Leg.Z := by
  classical
  have havail : ∀ t, segmentMultiplicity
      (dwz63Seg K n (positiveWordPositionEquiv
        ((cwSquarePartitionedTensor K dwz63Q).support) n (perm a) wRef))
      (positiveWordEquiv (PositiveWord CWBlock 1) n
        (positiveWordPositionEquiv (PositiveWord CWBlock 1) n (perm a) z.1)) t =
      alphaTilde t := by
    intro t
    rw [dwz63Seg_positionEquiv, positiveWordEquiv_position_apply,
      segmentMultiplicity_comp_perm_general]
    exact z.2 t
  have h := dwz63_coarseZ_of_segmentedAvailable K n
    (positiveWordPositionEquiv ((cwSquarePartitionedTensor K dwz63Q).support) n (perm a) wRef)
    alphaTilde hα
    ⟨positiveWordPositionEquiv (PositiveWord CWBlock 1) n (perm a) z.1, havail⟩
  rw [h, hperm a]

/-! ## `:255`, clause (1): the competitor is compatible with the hole word -/

/-- **The witnessing competitor is compatible with the hole's `Z`-word.**

`global_value.tex:255`, clause (1).  The witness lies in the Step-1 cut, so image 143's
`dwz63_stepOneCut_isCompatible` --- the paper's `lemma:triple_implies_compatible` (`:63-71`) ---
says the component word of its own coarsening is compatible (`def:global-compatible`, `:44-50`)
with its fine `Z`-word; `dwz63PlainCoarseGroup_eq_of_x`
(`Examples/DuanWuZhouLevelTwoPlainGroupedStage.lean:111`) identifies that coarsening with the
group the hole condition names, and the hole condition identifies its fine `Z`-word with the
frame-transported available word.

On the **uncut** ambient this statement is false, which is precisely the design gap the R1 repair
closes: the uncut hole condition tests only that a competitor *carries* the word.

Proof sketch: unfold the cut membership to recover the coarse image in `retained`, identify the
group with it under `hX`, and rewrite the `Z`-word by the hole condition. -/
theorem dwz63_cutReferenceHole_isCompatible (K : Type u) [CommRing K]
    {retained : Finset (BlockAddress fun _ : Leg ↦ PositiveWord (Fin 5) n)} (a₀ : retained)
    (s : ℕ)
    (hX : Set.InjOn (fun g : BlockAddress fun _ : Leg ↦ PositiveWord (Fin 5) n ↦ g Leg.X)
      (retained : Set (BlockAddress fun _ : Leg ↦ PositiveWord (Fin 5) n)))
    (hY : Set.InjOn (fun g : BlockAddress fun _ : Leg ↦ PositiveWord (Fin 5) n ↦ g Leg.Y)
      (retained : Set (BlockAddress fun _ : Leg ↦ PositiveWord (Fin 5) n)))
    (other : BlockAddress fun _ : Leg ↦ PositiveWord (PositiveWord CWBlock 1) n)
    (hother : other ∈ (dwz63FineStepOneCut K n retained a₀ s).support) :
    (dwz63SplitPair s).IsCompatible
      (dwz63CellWordOfAddress
        (dwz63PlainCoarseGroup retained
          (fun c ↦ positiveWordMap (cwSquareDegreeMap c) n) a₀ other :
          BlockAddress fun _ : Leg ↦ PositiveWord (Fin 5) n))
      (positiveWordEquiv (PositiveWord CWBlock 1) n (other Leg.Z)) := by
  classical
  have hpre := ((PartitionedTensor.mem_select_support (dwz63PreimageFine K n retained)
    (dwz63FineStepOneKeep retained a₀ s) other).mp hother).1
  have hret := ((mem_dwz63PreimageFine_support K n retained other).mp hpre).2
  have hgroup : (dwz63PlainCoarseGroup retained
      (fun c ↦ positiveWordMap (cwSquareDegreeMap c) n) a₀ other :
        BlockAddress fun _ : Leg ↦ PositiveWord (Fin 5) n) =
      coarsenBlockAddress (fun c ↦ positiveWordMap (cwSquareDegreeMap c) n) other :=
    congrArg Subtype.val (dwz63PlainCoarseGroup_eq_of_x (a₀ := a₀)
      (coarse := fun c ↦ positiveWordMap (cwSquareDegreeMap c) n) (s := other) hX
      (a := (⟨_, hret⟩ : retained)) rfl)
  rw [hgroup]
  exact dwz63_stepOneCut_isCompatible K a₀ s hX hY other hother

/-! ## `:255`, clause (2): the competitor lands in the copy's bucket -/

section Bucket

variable {R : Type v} [Field R] [Fintype R] [NeZero (2 : R)] {ι : Type u} [Fintype ι] {target : R}

/-- **A competitor with the same hash `Z`-word sits in the copy's own bucket.**

`global_value.tex:255`, clause (2): "`I'` is hashed to the same slot as `K`, i.e.
`hashx(I') = hashz(K)`".  Both triples are marked-`XY`-isolated, so each sits in a common `X`/`Y`
bucket of its own; for a legal triple the `Z`-hash is then determined
(`Seed.zHash_eq_of_commonBucket`), so equal hash `Z`-words force the two buckets to coincide, and
the paper's three-hash event is the two-equation common-bucket event
(`Seed.inCommonTriple_iff_commonBucket`).

Proof sketch: read `InCommonBucket` off each isolated incidence (`mem_dwz63IsolatedBucket`,
`isolatedSeeds`), push each through `zHash_eq_of_commonBucket`, equate the two buckets using `hz`,
and convert back with `inCommonTriple_iff_commonBucket`. -/
theorem dwz63_inCommonTriple_of_zIndex_eq
    (ambient marked : Finset (LegalTriple R ι target)) (buckets : Finset R)
    (seed : Seed R ι) {c c' : LegalTriple R ι target}
    (hc : c ∈ LegalTriple.markedXYIsolatedTargets ambient marked buckets seed)
    (hc' : c' ∈ LegalTriple.markedXYIsolatedTargets ambient marked buckets seed)
    (hz : c'.zIndex = c.zIndex) :
    Seed.InCommonTriple c'.xIndex c'.yIndex c'.zIndex target
      (dwz63IsolatedBucket ambient marked buckets seed c) seed := by
  classical
  have hb : Seed.InCommonBucket c.xIndex c.yIndex
      (dwz63IsolatedBucket ambient marked buckets seed c) seed :=
    ((Finset.mem_filter.mp (mem_dwz63IsolatedBucket ambient marked buckets seed hc)).2).1
  have hb' : Seed.InCommonBucket c'.xIndex c'.yIndex
      (dwz63IsolatedBucket ambient marked buckets seed c') seed :=
    ((Finset.mem_filter.mp (mem_dwz63IsolatedBucket ambient marked buckets seed hc')).2).1
  have hzc : seed.zHash target c.zIndex =
      dwz63IsolatedBucket ambient marked buckets seed c :=
    Seed.zHash_eq_of_commonBucket seed c.xIndex c.yIndex c.zIndex target _ c.legal hb
  have hzc' : seed.zHash target c'.zIndex =
      dwz63IsolatedBucket ambient marked buckets seed c' :=
    Seed.zHash_eq_of_commonBucket seed c'.xIndex c'.yIndex c'.zIndex target _ c'.legal hb'
  have hbb : dwz63IsolatedBucket ambient marked buckets seed c' =
      dwz63IsolatedBucket ambient marked buckets seed c := by
    rw [← hzc', hz, hzc]
  rw [← hbb]
  exact (Seed.inCommonTriple_iff_commonBucket seed c'.xIndex c'.yIndex c'.zIndex target _
    c'.legal).mpr hb'

end Bucket

end

end AlgebraicComplexity.Examples
