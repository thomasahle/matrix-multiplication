/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.SegmentedRegionalConstantTarget
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoConsecutiveSegments
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoFineCellJoined
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoFineConfigurationWitness

set_option autoImplicit false

/-!
# The regional coarse targets of the section 6.3 leaf

Layer 4 (`AlgebraicComplexity/Examples/`).  The regional division asks, at every peel, for the
head region's coarse target.  `MatrixMultiplication/SegmentedRegionalConstantTarget.lean` reduces
that to one fact --- the region's positions all carry the same coarse letter on each leg --- and
this module proves it for `[duan2023faster]`'s section 6.3 leaf.

## Why the region sees one letter

`dwz63Seg K n wRef i` is the *cell index* of the letter of `wRef` at position `i`
(`Examples/DuanWuZhouLevelTwoSegmentationData.lean`), and `dwz63CellIndex` is injective on the
coarse support (`dwz63Cell_dwz63CellIndex`).  So a position whose segment is `t` carries the
letter `dwz63Cell t` --- the whole letter, on all three legs at once, not merely a leg's worth.
After the sorting permutation, the positions of region `t` are exactly the positions of segment
`t` (`SegmentRegionBlock.segmentationLeft_seg`), so the region's piece of the relabelled coarse
target is the constant word `dwz63Cell t`.

## One spelling for all fifteen cells

`dwz63CellTarget t n` is that constant address.  Table 2 of section 6.3 has **twelve** cells with a
zero coordinate, not eleven --- rows `0,1,2,3,4,5,8,9,11,12,13,14`, the twelfth being row `11`,
`(2,2,0)` --- and at each of them `dwz63CellTarget t n` is `dwz63ZeroCellTarget zero k n`.  Eleven
of the twelve are proved cell by cell below, so the two transcriptions of the table are checked
against each other rather than trusted; the twelfth, row `11`, is `dwz63CellTarget_eleven` in
`Examples/DuanWuZhouLevelTwoRegionalCells.lean`, which also consumes it in an actual row-11
composition check.

At the three orbit rows `6`, `7`, `10` the identification with the fine-counting lane's
`dwz63OrbitTarget` is **not** definitional and is not claimed here: it is the checked bridge
`dwz63CellTarget_orbit` in `Examples/DuanWuZhouLevelTwoRegionalCells.lean`, proved through image
104's `dwz63OrbitTarget_eq_component` and `dwz63Cell_eq_dwz63Component` and consumed there in the
three orbit region entries.  Given those two identities, using one spelling for all fifteen means
the assembly never case-splits on which route weighed a cell; nothing in *this* module establishes
them.

Primary source: `[duan2023faster]` --- Ran Duan, Hongxun Wu and Renfei Zhou, *Faster Matrix
Multiplication via Asymmetric Hashing*, arXiv:2210.10173, section 6.3 (the level-two global-value
example), `papers/sources/2210.10173/global_value.tex:332-348`; the fifteen cells and their
`alpha` values are Table 2, `papers/sources/2210.10173/global_value.tex:354-378` (row `(2,2,0)` at
`:369-370`).
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor

universe u

/-! ## The constant coarse address of a cell -/

/-- **The coarse target of a region sitting inside cell `t`**: the constant word of `t`'s coarse
letter, on every leg.  This is the one spelling used for all fifteen cells. -/
def dwz63CellTarget (t : Fin 15) (n : ℕ) :
    BlockAddress (fun _ : Leg ↦ PositiveWord (Fin 5) n) :=
  fun c ↦ positiveWordConst (dwz63Cell t c) n

/-- The bridge to the zero-coordinate spelling: the two transcriptions agree as soon as their
letters do, which is checked per cell. -/
theorem dwz63CellTarget_eq_zeroCellTarget (t : Fin 15) (zero : Leg) (k : Fin 5) (n : ℕ)
    (h : ∀ c, dwz63Cell t c = dwz63ZeroCellTarget zero k 0 c) :
    dwz63CellTarget t n = dwz63ZeroCellTarget zero k n := by
  funext c
  show positiveWordConst (dwz63Cell t c) n = _
  rw [h c]
  cases zero <;> cases c <;> rfl

/-- Row `0` of Table 2 is `(0,0,4)`, whose zero coordinate is on `X`; its constant coarse
address is therefore `dwz63ZeroCellTarget Leg.X 4 n`. -/
theorem dwz63CellTarget_zero (n : ℕ) : dwz63CellTarget 0 n = dwz63ZeroCellTarget Leg.X 4 n :=
  dwz63CellTarget_eq_zeroCellTarget 0 Leg.X 4 n (fun c ↦ by cases c <;> rfl)

/-- Row `1` of Table 2 is `(0,1,3)`, whose zero coordinate is on `X`; its constant coarse
address is therefore `dwz63ZeroCellTarget Leg.X 3 n`. -/
theorem dwz63CellTarget_one (n : ℕ) : dwz63CellTarget 1 n = dwz63ZeroCellTarget Leg.X 3 n :=
  dwz63CellTarget_eq_zeroCellTarget 1 Leg.X 3 n (fun c ↦ by cases c <;> rfl)

/-- Row `2` of Table 2 is `(0,2,2)`, whose zero coordinate is on `X`; its constant coarse
address is therefore `dwz63ZeroCellTarget Leg.X 2 n`. -/
theorem dwz63CellTarget_two (n : ℕ) : dwz63CellTarget 2 n = dwz63ZeroCellTarget Leg.X 2 n :=
  dwz63CellTarget_eq_zeroCellTarget 2 Leg.X 2 n (fun c ↦ by cases c <;> rfl)

/-- Row `3` of Table 2 is `(0,3,1)`, whose zero coordinate is on `X`; its constant coarse
address is therefore `dwz63ZeroCellTarget Leg.X 1 n`. -/
theorem dwz63CellTarget_three (n : ℕ) : dwz63CellTarget 3 n = dwz63ZeroCellTarget Leg.X 1 n :=
  dwz63CellTarget_eq_zeroCellTarget 3 Leg.X 1 n (fun c ↦ by cases c <;> rfl)

/-- Row `4` of Table 2 is `(0,4,0)`, which is zero on `X` and on `Z`; the spelling below reads it
at the `X` leg, giving `dwz63ZeroCellTarget Leg.X 0 n`. -/
theorem dwz63CellTarget_four (n : ℕ) : dwz63CellTarget 4 n = dwz63ZeroCellTarget Leg.X 0 n :=
  dwz63CellTarget_eq_zeroCellTarget 4 Leg.X 0 n (fun c ↦ by cases c <;> rfl)

/-- Row `5` of Table 2 is `(1,0,3)`, whose zero coordinate is on `Y`; its constant coarse
address is therefore `dwz63ZeroCellTarget Leg.Y 3 n`. -/
theorem dwz63CellTarget_five (n : ℕ) : dwz63CellTarget 5 n = dwz63ZeroCellTarget Leg.Y 3 n :=
  dwz63CellTarget_eq_zeroCellTarget 5 Leg.Y 3 n (fun c ↦ by cases c <;> rfl)

/-- Row `8` of Table 2 is `(1,3,0)`, whose zero coordinate is on `Z`; its constant coarse
address is therefore `dwz63ZeroCellTarget Leg.Z 3 n`. -/
theorem dwz63CellTarget_eight (n : ℕ) : dwz63CellTarget 8 n = dwz63ZeroCellTarget Leg.Z 3 n :=
  dwz63CellTarget_eq_zeroCellTarget 8 Leg.Z 3 n (fun c ↦ by cases c <;> rfl)

/-- Row `9` of Table 2 is `(2,0,2)`, whose zero coordinate is on `Y`; its constant coarse
address is therefore `dwz63ZeroCellTarget Leg.Y 2 n`. -/
theorem dwz63CellTarget_nine (n : ℕ) : dwz63CellTarget 9 n = dwz63ZeroCellTarget Leg.Y 2 n :=
  dwz63CellTarget_eq_zeroCellTarget 9 Leg.Y 2 n (fun c ↦ by cases c <;> rfl)

/-- Row `12` of Table 2 is `(3,0,1)`, whose zero coordinate is on `Y`; its constant coarse
address is therefore `dwz63ZeroCellTarget Leg.Y 1 n`. -/
theorem dwz63CellTarget_twelve (n : ℕ) : dwz63CellTarget 12 n = dwz63ZeroCellTarget Leg.Y 1 n :=
  dwz63CellTarget_eq_zeroCellTarget 12 Leg.Y 1 n (fun c ↦ by cases c <;> rfl)

/-- Row `13` of Table 2 is `(3,1,0)`, whose zero coordinate is on `Z`; its constant coarse
address is therefore `dwz63ZeroCellTarget Leg.Z 1 n`. -/
theorem dwz63CellTarget_thirteen (n : ℕ) :
    dwz63CellTarget 13 n = dwz63ZeroCellTarget Leg.Z 1 n :=
  dwz63CellTarget_eq_zeroCellTarget 13 Leg.Z 1 n (fun c ↦ by cases c <;> rfl)

/-- Row `14` of Table 2 is `(4,0,0)`, which is zero on `Y` and on `Z`; the spelling below reads it
at the `Y` leg, giving `dwz63ZeroCellTarget Leg.Y 0 n`. -/
theorem dwz63CellTarget_fourteen (n : ℕ) :
    dwz63CellTarget 14 n = dwz63ZeroCellTarget Leg.Y 0 n :=
  dwz63CellTarget_eq_zeroCellTarget 14 Leg.Y 0 n (fun c ↦ by cases c <;> rfl)

/-! ## A position of segment `t` carries `t`'s coarse letter -/

section Letterwise

variable (K : Type u) [CommRing K]

/-- **The relabelled coarse address is `t`'s letter at every position of segment `t`.**

The whole content of the regional target: `dwz63Seg` reads the cell index off the letter and
`dwz63Cell_dwz63CellIndex` reads the letter back off the cell index, so a position's segment
determines its coarse letter on all three legs at once.

Proof sketch: let `x` be the supported square address `wRef` carries at the relabelled position
`σ i`.  Its membership in `cwSquareSupport` comes from `cwSquarePartitionedTensor_support`, and
`dwz63Seg` is by definition `dwz63CellIndex x`; the hypothesis `hi` says that index is `t`, so
`dwz63Cell_dwz63CellIndex` --- the left inverse on the supported addresses --- gives `x = dwz63Cell
t` as a whole square address, all three legs at once.  It remains to see that the left-hand side
reads exactly that letter: `positionRelabelBlockAddress` is `positiveWordPositionEquiv` legwise
(`rfl`), so `positiveWordEquiv_position_apply` turns reading at `i` into reading the unrelabelled
address at `σ i`, and `positiveWordEquiv_positiveSupportWordBlockAddress` says the transposed leg
word of a supported word is that word's letter's `c`-component.  Composing the two equalities at
leg `c` finishes it.  No enumeration of the fifteen cells occurs. -/
theorem dwz63_relabelledAddress_eq_dwz63Cell (N : ℕ)
    (wRef : PositiveWord ((cwSquarePartitionedTensor K dwz63Q).support) N)
    (σ : Equiv.Perm (Fin (N + 1))) (t : Fin 15) (i : Fin (N + 1))
    (hi : dwz63Seg K N wRef (σ i) = t) (c : Leg) :
    positiveWordEquiv (Fin 5) N
      (positionRelabelBlockAddress (fun _ : Leg ↦ Fin 5) N σ
        (positiveSupportWordBlockAddress
          ((cwSquarePartitionedTensor K dwz63Q).support) N wRef) c) i
      = dwz63Cell t c := by
  have hsupp : ∀ x : CWSquareAddress,
      x ∈ (cwSquarePartitionedTensor K dwz63Q).support ↔ x ∈ cwSquareSupport := by
    intro x
    rw [cwSquarePartitionedTensor_support]
  have hmem : ((positiveWordEquiv ((cwSquarePartitionedTensor K dwz63Q).support) N wRef
      (σ i)).1 : CWSquareAddress) ∈ cwSquareSupport :=
    (hsupp _).1 (positiveWordEquiv ((cwSquarePartitionedTensor K dwz63Q).support) N wRef (σ i)).2
  have hcell : ((positiveWordEquiv ((cwSquarePartitionedTensor K dwz63Q).support) N wRef
      (σ i)).1 : CWSquareAddress) = dwz63Cell t := by
    rw [← hi]
    unfold dwz63Seg
    rw [dwz63Cell_dwz63CellIndex hmem]
  have hword := positiveWordEquiv_positiveSupportWordBlockAddress
    (A := fun _ : Leg ↦ Fin 5) ((cwSquarePartitionedTensor K dwz63Q).support) N wRef c
  have hrel : positionRelabelBlockAddress (fun _ : Leg ↦ Fin 5) N σ
      (positiveSupportWordBlockAddress
        ((cwSquarePartitionedTensor K dwz63Q).support) N wRef) c =
      positiveWordPositionEquiv (Fin 5) N σ
        (positiveSupportWordBlockAddress
          ((cwSquarePartitionedTensor K dwz63Q).support) N wRef c) := rfl
  rw [hrel, positiveWordEquiv_position_apply, Function.comp_apply]
  exact (congrFun hword (σ i)).trans (congrFun hcell c)

/-! ## The head region's coarse target -/

variable (b t' : SegmentRegionBlock (fun _ : Leg ↦ PositiveWord CWBlock 1) Leg.Z 15)
  (rest : List (SegmentRegionBlock (fun _ : Leg ↦ PositiveWord CWBlock 1) Leg.Z 15))
  (wRef : PositiveWord ((cwSquarePartitionedTensor K dwz63Q).support)
    (SegmentRegionBlock.total b (t' :: rest)))
  (σ : Equiv.Perm (Fin (SegmentRegionBlock.total b (t' :: rest) + 1)))

/-- **Every position of the head region carries the head cell's coarse letter.** -/
theorem dwz63_regionConst_head
    (hσ : dwz63Seg K (SegmentRegionBlock.total b (t' :: rest)) wRef ∘ ⇑σ =
      SegmentRegionBlock.seg b (t' :: rest))
    (c : Leg) (i : Fin (b.size + 1)) :
    positiveWordEquiv (Fin 5) (SegmentRegionBlock.total b (t' :: rest))
      (positionRelabelBlockAddress (fun _ : Leg ↦ Fin 5)
        (SegmentRegionBlock.total b (t' :: rest)) σ
        (positiveSupportWordBlockAddress
          ((cwSquarePartitionedTensor K dwz63Q).support)
          (SegmentRegionBlock.total b (t' :: rest)) wRef) c)
      (regionIndexLeft b.size (SegmentRegionBlock.total t' rest) i)
      = dwz63Cell b.label c := by
  refine dwz63_relabelledAddress_eq_dwz63Cell K _ wRef σ b.label _ ?_ c
  have hconst : SegmentRegionBlock.seg b (t' :: rest)
      (regionIndexLeft b.size (SegmentRegionBlock.total t' rest) i) = b.label :=
    congrFun (SegmentRegionBlock.segmentationLeft_seg b t' rest) i
  exact (congrFun hσ (regionIndexLeft b.size (SegmentRegionBlock.total t' rest) i)).trans hconst

/-- **The concatenation obligation of the head peel, discharged.**  The head piece of the
relabelled coarse target is `dwz63CellTarget` at the head cell --- the address the per-cell
weights are stated at. -/
theorem dwz63_relabelledTarget_eq_append
    (hσ : dwz63Seg K (SegmentRegionBlock.total b (t' :: rest)) wRef ∘ ⇑σ =
      SegmentRegionBlock.seg b (t' :: rest)) (c : Leg) :
    positionRelabelBlockAddress (fun _ : Leg ↦ Fin 5)
        (SegmentRegionBlock.total b (t' :: rest)) σ
        (positiveSupportWordBlockAddress
          ((cwSquarePartitionedTensor K dwz63Q).support)
          (SegmentRegionBlock.total b (t' :: rest)) wRef) c =
      positiveWordAppend (dwz63CellTarget b.label b.size c)
        (SegmentRegionBlock.total t' rest)
        ((positiveWordAppendEquiv (Fin 5) b.size
          (SegmentRegionBlock.total t' rest)).symm
          (positionRelabelBlockAddress (fun _ : Leg ↦ Fin 5)
            (SegmentRegionBlock.total b (t' :: rest)) σ
            (positiveSupportWordBlockAddress
              ((cwSquarePartitionedTensor K dwz63Q).support)
              (SegmentRegionBlock.total b (t' :: rest)) wRef) c)).2 :=
  blockAddress_eq_append_const_of_regionConst b.size (SegmentRegionBlock.total t' rest) _
    (fun c ↦ dwz63Cell b.label c) (dwz63_regionConst_head K b t' rest wRef σ hσ) c

end Letterwise

end AlgebraicComplexity.Examples
