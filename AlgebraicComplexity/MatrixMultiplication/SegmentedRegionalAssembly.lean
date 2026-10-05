/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.SegmentedRegionalConstantTarget
import AlgebraicComplexity.MatrixMultiplication.SegmentedConsecutiveBlocks
import AlgebraicComplexity.MatrixMultiplication.SegmentedLocalizedDivisionSymSix

set_option autoImplicit false

/-!
# Assembling the regional weight bundle from per-cell weights

Layer 3 (`AlgebraicComplexity/MatrixMultiplication/`).  `SegmentedRegionalSymSixWeights` is a
recursion over the region list, so building one by hand means peeling fifteen times and, at each
peel, exhibiting the two regional coarse targets and proving the parent target is their
concatenation.  This module does that peeling once, generically.

## The invariant

Everything hangs on a single statement about the parent coarse target:

`positiveWordEquiv (target c) i = letter (seg i) c` --- *every position carries the coarse letter
of its own segment*.

It is preserved by the peel.  The head region sees only positions of segment `bl.label`
(`SegmentRegionBlock.segmentationLeft_seg`), so its piece is the constant word
`letter bl.label` --- which is the address the per-cell weights are stated at --- and the tail's
piece satisfies the same invariant one segment list shorter
(`positiveWordEquiv_appendEquiv_symm_snd` plus
`SegmentRegionBlock.segmentationRight_seg`).  So the fifteen concatenation obligations collapse to
one hypothesis, checked once at the parent.

Nothing here knows what a cell is: `letter` is an arbitrary map from segments to coarse block
addresses.

Primary source: `[duan2023faster]` --- Ran Duan, Hongxun Wu and Renfei Zhou, *Faster Matrix
Multiplication via Asymmetric Hashing*, arXiv:2210.10173, section 6.3 (the level-two global-value
example), `papers/sources/2210.10173/global_value.tex:332-348`.
-/

namespace AlgebraicComplexity

open Tensor

universe u v w x

/-! ## The tail piece, letterwise -/

namespace Tensor

/-- The right regional piece of a word reads the parent's letters at the right region's
positions.

Proof sketch: `positiveWordAppendEquiv` is an equivalence, so re-appending the word's two pieces
returns the word (`Equiv.apply_symm_apply`); rewriting the right-hand side backwards along that
identity turns it into a read of the *appended* word.  `positiveWordEquiv_append` then evaluates
that read as `Fin.append` after the cast, and the cast of `regionIndexRight n p j` is
`Fin.natAdd (n + 1) j` (`Fin.ext` on the index arithmetic), so `Fin.append_right` selects the
right piece at `j`.  This is the tail half of `positiveWordAppendEquiv_symm_fst_eq_const`'s
argument, kept general because the tail piece is not constant. -/
theorem positiveWordEquiv_appendEquiv_symm_snd {I : Type w} (n p : ℕ)
    (word : PositiveWord I (n + p + 1)) (j : Fin (p + 1)) :
    positiveWordEquiv I p ((positiveWordAppendEquiv I n p).symm word).2 j =
      positiveWordEquiv I (n + p + 1) word (regionIndexRight n p j) := by
  have happend : positiveWordAppend ((positiveWordAppendEquiv I n p).symm word).1 p
      ((positiveWordAppendEquiv I n p).symm word).2 = word := by
    rw [← positiveWordAppendEquiv_apply]
    exact (positiveWordAppendEquiv I n p).apply_symm_apply word
  conv_rhs => rw [← happend]
  rw [positiveWordEquiv_append, Function.comp_apply,
    show Fin.cast (show n + p + 1 + 1 = n + 1 + (p + 1) from by omega)
        (regionIndexRight n p j) = Fin.natAdd (n + 1) j from Fin.ext (by simp [regionIndexRight]),
    Fin.append_right]

end Tensor

/-! ## The bundle, assembled -/

section Assembly

variable {K : Type u} [CommSemiring K]
variable {A : Leg → Type w} {B : Leg → Type x}
variable [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]
variable [∀ c, Fintype (B c)] [∀ c, DecidableEq (B c)]
variable {V : ∀ c, A c → Type (max u v)}
variable [∀ c a, AddCommMonoid (V c a)] [∀ c a, Module K (V c a)]
variable {M : ℕ}

omit [∀ c, Fintype (B c)] [∀ c, DecidableEq (B c)] in
/-- **The regional `sym₆`-weight bundle, from one weight per region.**

The client supplies the fifteen per-region weights, each at the *constant* coarse address of that
region's segment, plus the single invariant that the parent coarse target carries each position's
own segment letter.  The peeling, the regional targets and the fifteen concatenation obligations
are all discharged here.

Proof sketch: structural induction on the region list, carrying the invariant.  With one region
left, the invariant says the target agrees pointwise with `positiveWordConst (letter bl.label c)`
on every leg, so `positiveWordEquiv`'s injectivity turns it into an equality of addresses and the
goal is literally the client's weight for that region.  At a peel, the head region sees only
positions of segment `bl.label` (`SegmentRegionBlock.segmentationLeft_seg` composed with the
invariant), so `blockAddress_eq_append_const_of_regionConst` discharges the concatenation
obligation with the head piece taken to be the constant word and the tail piece taken to be
whatever `positiveWordAppendEquiv` leaves; the head weight is the client's, after
`segmentationLeft_seg` rewrites the head's segmentation to the constant `bl.label`.  For the tail,
`SegmentRegionBlock.segmentationRight_seg` rewrites its segmentation, and the invariant is
re-established one region shorter by reading the tail piece with
`positiveWordEquiv_appendEquiv_symm_snd` and then applying the parent invariant at
`regionIndexRight`.  Nothing here knows what a cell is: `letter` is an arbitrary map from segments
to coarse block addresses. -/
theorem segmentedRegionalSymSixWeights_of_letterwise
    (P : PartitionedTensor (K := K) (A := A) V) (f : ∀ c, A c → B c) (c₀ : Leg) (τ : ℝ)
    (letter : Fin M → ∀ c, B c) :
    ∀ (bl : SegmentRegionBlock A c₀ M) (rest : List (SegmentRegionBlock A c₀ M))
      (target : BlockAddress
        (fun c ↦ PositiveWord (B c) (SegmentRegionBlock.total bl rest))),
      (∀ (c : Leg) (i : Fin (SegmentRegionBlock.total bl rest + 1)),
        positiveWordEquiv (B c) (SegmentRegionBlock.total bl rest) (target c) i =
          letter (SegmentRegionBlock.seg bl rest i) c) →
      (∀ u ∈ bl :: rest, HasTauWeight K
        (symSix K (P.segmentedLocalizedSplittingPower f u.size M (fun _ ↦ u.label)
          (SegmentedSplitRestriction.ofLeg c₀ u.type)
          (fun c ↦ positiveWordConst (letter u.label c) u.size)).realize) τ u.value) →
      SegmentedRegionalSymSixWeights P f c₀ τ bl.toSegmentRegionSpec
        (SegmentRegionBlock.specs rest) (SegmentRegionBlock.seg bl rest) target
  | bl, [], target, hconst, hw => by
      have htarget : target = fun c ↦ positiveWordConst (letter bl.label c) bl.size := by
        funext c
        apply (positiveWordEquiv (B c) bl.size).injective
        funext i
        rw [positiveWordEquiv_const]
        exact hconst c i
      show HasTauWeight K
        (symSix K (P.segmentedLocalizedSplittingPower f bl.size M
          (SegmentRegionBlock.seg bl []) (SegmentedSplitRestriction.ofLeg c₀ bl.type)
          target).realize) τ bl.value
      rw [htarget]
      exact hw bl (List.mem_cons_self ..)
  | bl, t :: rest, target, hconst, hw => by
      have hleft : ∀ (c : Leg) (i : Fin (bl.size + 1)),
          positiveWordEquiv (B c) (SegmentRegionBlock.total bl (t :: rest)) (target c)
            (regionIndexLeft bl.size (SegmentRegionBlock.total t rest) i) =
            letter bl.label c := by
        intro c i
        refine (hconst c
          (regionIndexLeft bl.size (SegmentRegionBlock.total t rest) i)).trans ?_
        exact congrArg (fun z ↦ letter z c)
          (congrFun (SegmentRegionBlock.segmentationLeft_seg bl t rest) i)
      refine ⟨fun c ↦ positiveWordConst (letter bl.label c) bl.size,
        fun c ↦ ((positiveWordAppendEquiv (B c) bl.size
          (SegmentRegionBlock.total t rest)).symm (target c)).2, ?_, ?_, ?_⟩
      · exact blockAddress_eq_append_const_of_regionConst bl.size
          (SegmentRegionBlock.total t rest) target (fun c ↦ letter bl.label c) hleft
      · rw [SegmentRegionBlock.segmentationLeft_seg]
        exact hw bl (List.mem_cons_self ..)
      · rw [SegmentRegionBlock.segmentationRight_seg]
        refine segmentedRegionalSymSixWeights_of_letterwise P f c₀ τ letter t rest _ ?_ ?_
        · intro c j
          refine (Tensor.positiveWordEquiv_appendEquiv_symm_snd bl.size
            (SegmentRegionBlock.total t rest) (target c) j).trans ?_
          refine (hconst c
            (regionIndexRight bl.size (SegmentRegionBlock.total t rest) j)).trans ?_
          exact congrArg (fun z ↦ letter z c)
            (congrFun (SegmentRegionBlock.segmentationRight_seg bl t rest) j)
        · intro u hu
          exact hw u (List.mem_cons_of_mem bl hu)

end Assembly

end AlgebraicComplexity
