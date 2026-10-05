/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoStepOneCutHoles
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoMarkedWitness

set_option autoImplicit false

/-!
# The four encoding inputs of the Step-1 cut's domination

Layer 4 (`AlgebraicComplexity/Examples/`).  Four facts with no `[duan2023faster]` content of their
own, isolated because the domination of `claim:hole_frac_low`
(`papers/sources/2210.10173/global_value.tex:249-265`, necessary condition at `:255`) consumes
them and nothing else does.  Each is a statement about the level-two *encoding* --- how a legal
hashing triple, its source word, its block address and its component word relate --- rather than
about holes.

* `dwz63Seg_eq_cellWordOfAddress` --- the segmentation of a supported word is the component word
  `(I_t, J_t, K_t)` (`global_value.tex:32`) of the block address that word transposes to.  This is
  what lets `dwz63SplitCompatTyped`'s `component` be read either way.
* `dwz63_zIndex_dwz63Seg` --- the `Z`-index of a position's component is that position's coarse
  `Z`-letter.  `def:global-compatible` (`:44-50`) reads typicalness against `zIndex ∘ component`,
  and the hole side knows the coarse `Z`-word; this identifies the two.
* `dwz63_multiplicity_dwz63Seg_of_mem_markedWords` --- the marked family is one joint type class
  (`global_value.tex:28`, "all retained triples obey `α`"), so every marked word's cell profile is
  that type.  It is the converse of the committed `dwz63_referenceWord_mem_markedWords`
  (`Examples/DuanWuZhouLevelTwoMarkedWitness.lean:100`) and discharges the joint-type conjunct of
  `dwz63SplitCompatTyped` (`Examples/DuanWuZhouLevelTwoCompetitorCount.lean:104`).
* `dwz63_segmentedAvailable_frameTransport` --- availability travels with the reference frame.
  `[duan2023faster]`'s copies are indexed by retained triples and each is read in its own frame;
  this says an available word transported into another frame is available for the transported
  segmentation, which is what makes the usefulness conjunct
  (`isUseful_of_segmentedAvailableWord`, `Examples/DuanWuZhouLevelTwoSeedInputs.lean:235`)
  applicable at the owner's frame.

Primary source `[duan2023faster]`: Ran Duan, Hongxun Wu and Renfei Zhou, *Faster Matrix
Multiplication via Asymmetric Hashing*, arXiv:2210.10173, section 6.1 `sec:global-algo`,
`papers/sources/2210.10173/global_value.tex:28, 32, 44-50, 249-265`.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor ProgressionHash

universe u

noncomputable section

variable {n : ℕ}

/-! ## The segmentation is the component word of the transposed address (`:32`) -/

/-- **`dwz63Seg` is `dwz63CellWordOfAddress` of the transposed address.**

`global_value.tex:32` reads the component `(I_t, J_t, K_t)` off a large triple; `dwz63Seg`
(`Examples/DuanWuZhouLevelTwoSegmentationData.lean:80`) reads the cell index of each position of a
supported word.  A supported word transposes to a block address, and along that transposition the
two readings agree.

Proof sketch: `positiveWordEquiv_positiveSupportWordBlockAddress`
(`Tensor/PartitionedPower.lean:215`) says the transposed address, read at a position and a leg, is
that position's supported address read at that leg; the two `dwz63CellIndex` arguments then agree
by function extensionality. -/
theorem dwz63Seg_eq_cellWordOfAddress (K : Type u) [CommRing K]
    (w : PositiveWord ((cwSquarePartitionedTensor K dwz63Q).support) n) :
    dwz63Seg K n w =
      dwz63CellWordOfAddress
        (positiveSupportWordBlockAddress ((cwSquarePartitionedTensor K dwz63Q).support) n w) := by
  funext i
  show dwz63CellIndex _ = dwz63CellIndex _
  congr 1
  funext c
  exact (congrFun (positiveWordEquiv_positiveSupportWordBlockAddress
    ((cwSquarePartitionedTensor K dwz63Q).support) n w c) i).symm

/-- **The `Z`-index of a position's component is that position's coarse `Z`-letter.**

`def:global-compatible` (`global_value.tex:44-50`) states typicalness against the large `Z`-block,
which the tree reads as `zIndex ∘ component`; the hole side instead knows the coarse `Z`-word of
an
address.  On the fifteen supported cells the two agree, because `dwz63CellIndex` inverts
`dwz63Cell` there.

Proof sketch: the position's coarse square address is supported, so `dwz63Cell_dwz63CellIndex`
(`Examples/DuanWuZhouLevelTwoFineConfigurationWitness.lean:125`) recovers it from its cell index;
evaluate at `Leg.Z` and transport along
`positiveWordEquiv_positiveSupportWordBlockAddress`. -/
theorem dwz63_zIndex_dwz63Seg (K : Type u) [CommRing K]
    (w : PositiveWord ((cwSquarePartitionedTensor K dwz63Q).support) n) (i : Fin (n + 1)) :
    dwz63ZIndex (dwz63Seg K n w i) =
      positiveWordEquiv (Fin 5) n
        (positiveSupportWordBlockAddress ((cwSquarePartitionedTensor K dwz63Q).support) n w
          Leg.Z) i := by
  have hs : ((positiveWordEquiv ((cwSquarePartitionedTensor K dwz63Q).support) n w i).1
      : BlockAddress fun _ : Leg ↦ Fin 5) ∈ cwSquareSupport :=
    (positiveWordEquiv ((cwSquarePartitionedTensor K dwz63Q).support) n w i).2
  have hcell := dwz63Cell_dwz63CellIndex hs
  rw [congrFun (positiveWordEquiv_positiveSupportWordBlockAddress
    ((cwSquarePartitionedTensor K dwz63Q).support) n w Leg.Z) i]
  exact congrFun hcell Leg.Z

/-! ## The marked family is one joint type class (`global_value.tex:28`) -/

/-- **Every marked word has the marked cell profile.**

`global_value.tex:28` fixes the joint component distribution `α`, and `dwz63MarkedWords`
(`Examples/DuanWuZhouLevelTwoSupportBridge.lean:262`) is the corresponding exact type class,
relabelled to the coarsened square support.  This is the converse of the committed
`dwz63_referenceWord_mem_markedWords` (`Examples/DuanWuZhouLevelTwoMarkedWitness.lean:100`), and it
is what discharges the joint-type conjunct of `dwz63SplitCompatTyped`
(`Examples/DuanWuZhouLevelTwoCompetitorCount.lean:104`) for a competitor drawn from the marked
family.

Proof sketch: membership in the positive type class gives the letter multiplicity as the
pushforward of the profile along `dwz63CellEquiv`; pushing that forward again along
`dwz63CellIndex ∘ Subtype.val`, which is a left inverse of `dwz63CellEquiv`, returns the
profile. -/
theorem dwz63_multiplicity_dwz63Seg_of_mem_markedWords (K : Type u) [CommRing K]
    (profile : Fin 15 → ℕ)
    (w : PositiveWord ((cwSquarePartitionedTensor K dwz63Q).support) n)
    (hw : w ∈ dwz63MarkedWords n profile) :
    WordType.multiplicity (dwz63Seg K n w) = profile := by
  classical
  have hmul : WordType.multiplicity
      (positiveWordEquiv ((cwSquarePartitionedTensor K dwz63Q).support) n w) =
      WordType.mappedType (dwz63CellEquiv : Fin 15 → CWSquareSupport) profile :=
    mem_positiveTypeClass.1 hw
  have hpush : WordType.mappedType (fun x : CWSquareSupport ↦ dwz63CellIndex x.val)
      (WordType.multiplicity
        (positiveWordEquiv ((cwSquarePartitionedTensor K dwz63Q).support) n w)) =
      WordType.multiplicity (dwz63Seg K n w) :=
    (WordType.multiplicity_comp_eq_mappedType _ _).symm
  refine hpush.symm.trans ?_
  refine (congrArg (WordType.mappedType (fun x : CWSquareSupport ↦ dwz63CellIndex x.val))
    hmul).trans ?_
  refine (WordType.mappedType_comp (dwz63CellEquiv : Fin 15 → CWSquareSupport)
    (fun x : CWSquareSupport ↦ dwz63CellIndex x.val) profile).trans ?_
  refine (WordType.mappedType_congr ?_ profile).trans (WordType.mappedType_id profile)
  intro c
  show dwz63CellIndex (dwz63CellEquiv c).val = c
  rw [dwz63CellEquiv_coe, dwz63CellIndex_dwz63Cell]

/-! ## Availability travels with the reference frame -/

/-- **A frame transport of an available word is available for the transported segmentation.**

`[duan2023faster]` reads each broken copy in its own frame (`global_value.tex:270-320`; the
reference-frame equation is the `hperm` binder of the level-two stage).  Availability is a family
of segment counts, and moving positions by one permutation in *both* the segmentation and the word
leaves every count unchanged.

Proof sketch: `dwz63Seg_positionEquiv` moves the permutation onto the segmentation,
`positiveWordEquiv_position_apply` moves it onto the word, and
`segmentMultiplicity_comp_perm_general`
(`MatrixMultiplication/SegmentedFiberUniformity.lean:48`) cancels it. -/
theorem dwz63_segmentedAvailable_frameTransport (K : Type u) [CommRing K]
    (alphaTilde : Fin 15 → PositiveWord CWBlock 1 → ℕ)
    (w : PositiveWord ((cwSquarePartitionedTensor K dwz63Q).support) n)
    (σ : Equiv.Perm (Fin (n + 1)))
    (z : SegmentedAvailableWord (dwz63Seg K n w) alphaTilde) :
    ∀ u, segmentMultiplicity
      (dwz63Seg K n
        (positiveWordPositionEquiv ((cwSquarePartitionedTensor K dwz63Q).support) n σ w))
      (positiveWordEquiv (PositiveWord CWBlock 1) n
        (positiveWordPositionEquiv (PositiveWord CWBlock 1) n σ z.1)) u = alphaTilde u := by
  intro u
  rw [dwz63Seg_positionEquiv, positiveWordEquiv_position_apply,
    segmentMultiplicity_comp_perm_general]
  exact z.2 u

end

end AlgebraicComplexity.Examples
