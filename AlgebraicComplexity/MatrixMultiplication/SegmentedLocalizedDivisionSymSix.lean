/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.SegmentedLocalizedDivisionIterated
import AlgebraicComplexity.MatrixMultiplication.SymSixDistribution
import AlgebraicComplexity.MatrixMultiplication.SymSixUniformLeaf

set_option autoImplicit false

/-!
# The iterated regional division under `sym₆`

Layer 3 (`AlgebraicComplexity/MatrixMultiplication/`).
`MatrixMultiplication/SegmentedLocalizedDivisionIterated.lean` composes one `tau`-weight per
consecutive region into a `tau`-weight of the whole localized segmented leaf.  `[duan2023faster]`'s
value functional is `V^{(6)}`, so what a client actually has to weigh is `sym₆` of the leaf, not
the leaf.  This module is that same induction with `sym₆` applied throughout.

## Why `sym₆` costs nothing here

Two committed facts do all the work, and both are functorial rather than combinatorial:

* `Tensor.Restricts.symSix_congr` (`MatrixMultiplication/SymSixUniformLeaf.lean`) --- a restriction
  survives six-symmetrisation, so the regional division still applies;
* `Tensor.Isomorphic.symSix_external` (`MatrixMultiplication/SymSixDistribution.lean`) --- in a
  product the six orientations of each factor stay attached to that factor, so a per-factor
  six-symmetrised weight applies factorwise.

Consequently the induction is the unsymmetrised one with two extra steps per peel, and the
hypothesis is the same recursive bundle with `HasTauWeight K (symSix K …)` in place of
`HasTauWeight K …`.  As there, the iterated external product is never named:
`HasTauWeight.external` and `Isomorphic.symSix_external` are both binary and the regions have
different block-space types, so the weight law is iterated alongside the division and the
intermediate products live only inside the proof.

Primary source: `[duan2023faster]` --- Ran Duan, Hongxun Wu and Renfei Zhou, *Faster Matrix
Multiplication via Asymmetric Hashing*, arXiv:2210.10173, section 6.3 (the level-two global-value
example), `papers/sources/2210.10173/global_value.tex:332-348`.
-/

namespace AlgebraicComplexity

open Tensor

universe u v w x

section RegionalSymSix

variable {K : Type u} [CommSemiring K]
variable {A : Leg → Type w} {B : Leg → Type x}
variable [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]
variable [∀ c, Fintype (B c)] [∀ c, DecidableEq (B c)]
variable {V : ∀ c, A c → Type (max u v)}
variable [∀ c a, AddCommMonoid (V c a)] [∀ c a, Module K (V c a)]
variable {M : ℕ}

/-- **The regional `sym₆`-weight hypothesis.**

`SegmentedRegionalWeights` with the six-symmetrised leaf: at each peel it supplies the two
regional coarse targets, the statement that the parent target is their concatenation, and a
`tau`-weight for `sym₆` of the head region's factor. -/
def SegmentedRegionalSymSixWeights (P : PartitionedTensor (K := K) (A := A) V)
    (f : ∀ c, A c → B c) (c₀ : Leg) (τ : ℝ) :
    (s : SegmentRegionSpec A c₀ M) → (rest : List (SegmentRegionSpec A c₀ M)) →
      (Fin (SegmentRegionSpec.total s rest + 1) → Fin M) →
      BlockAddress (fun c ↦ PositiveWord (B c) (SegmentRegionSpec.total s rest)) → Prop
  | s, [], seg, target =>
      HasTauWeight K
        (symSix K (P.segmentedLocalizedSplittingPower f s.size M seg
          (SegmentedSplitRestriction.ofLeg c₀ s.type) target).realize) τ s.value
  | s, t :: rest, seg, target =>
      ∃ (targetHead : BlockAddress (fun c ↦ PositiveWord (B c) s.size))
        (targetTail : BlockAddress
          (fun c ↦ PositiveWord (B c) (SegmentRegionSpec.total t rest))),
        (∀ c, target c = positiveWordAppend (targetHead c)
          (SegmentRegionSpec.total t rest) (targetTail c)) ∧
        HasTauWeight K
          (symSix K (P.segmentedLocalizedSplittingPower f s.size M
            (segmentationLeft s.size (SegmentRegionSpec.total t rest) seg)
            (SegmentedSplitRestriction.ofLeg c₀ s.type) targetHead).realize) τ s.value ∧
        SegmentedRegionalSymSixWeights P f c₀ τ t rest
          (segmentationRight s.size (SegmentRegionSpec.total t rest) seg) targetTail

omit [∀ c, Fintype (B c)] [∀ c, DecidableEq (B c)] in
/-- **The iterated regional division, as a `sym₆`-weight law.**

`[duan2023faster]`'s `claim:degen` iterated over an arbitrary finite list of consecutive regions
and composed with the value law, under `V^{(6)}`.  One `sym₆`-weight per region in, one
`sym₆`-weight for the whole leaf out, with the product of the regional weights --- which is the
shape the section 6.3 endpoint's `hleafWeight` binder consumes.

Proof sketch: induction on the region list.  With no tail the bundle *is* the conclusion.  At a
peel, destructure the bundle into the two regional coarse targets, the concatenation equation, the
head region's `sym₆`-weight and the tail's bundle; the induction hypothesis weighs the tail at
`SegmentRegionSpec.totalValue`, and `HasTauWeight.external` multiplies the two weights (both values
are nonnegative, the tail's by `SegmentRegionSpec.totalValue_nonneg`).  One restriction then
remains: the parent leaf restricts onto the product of the two regional leaves by
`Restricts.segmentedLocalizedSplittingPower_binaryDivision` at the concatenation equation and the
`SegmentedSplitRestriction.ofLeg_sum` splitting of the parent profile; `Restricts.symSix_congr`
carries that restriction through the symmetrisation, and `Isomorphic.symSix_external` identifies
`sym₆` of the product with the product of the two `sym₆` factors.  `HasTauWeight.of_restricts`
pulls the product weight back to the parent. -/
theorem hasTauWeight_symSix_segmentedLocalizedSplittingPower_regional
    (P : PartitionedTensor (K := K) (A := A) V) (f : ∀ c, A c → B c) (c₀ : Leg) {τ : ℝ} :
    ∀ (s : SegmentRegionSpec A c₀ M) (rest : List (SegmentRegionSpec A c₀ M))
      (seg : Fin (SegmentRegionSpec.total s rest + 1) → Fin M)
      (target : BlockAddress (fun c ↦ PositiveWord (B c) (SegmentRegionSpec.total s rest))),
      0 ≤ s.value → (∀ u ∈ rest, 0 ≤ u.value) →
      SegmentedRegionalSymSixWeights P f c₀ τ s rest seg target →
      HasTauWeight K
        (symSix K (P.segmentedLocalizedSplittingPower f (SegmentRegionSpec.total s rest) M seg
          (SegmentedSplitRestriction.ofLeg c₀ (SegmentRegionSpec.parentType s rest))
          target).realize) τ (SegmentRegionSpec.totalValue s rest)
  | _, [], _, _, _, _, h => h
  | s, t :: rest, seg, target, hs, hrest, h => by
      obtain ⟨targetHead, targetTail, htarget, hhead, htail⟩ := h
      have hrestHead : 0 ≤ t.value := hrest t (List.mem_cons_self ..)
      have hrestTail : ∀ u ∈ rest, 0 ≤ u.value :=
        fun u hu ↦ hrest u (List.mem_cons_of_mem t hu)
      have htailWeight := hasTauWeight_symSix_segmentedLocalizedSplittingPower_regional P f c₀
        t rest (segmentationRight s.size (SegmentRegionSpec.total t rest) seg) targetTail
        hrestHead hrestTail htail
      have hprod := hhead.external htailWeight hs
        (SegmentRegionSpec.totalValue_nonneg t rest hrestHead hrestTail)
      refine hprod.of_restricts ?_
      refine Tensor.Restricts.trans
        (Tensor.Restricts.symSix_congr
          (Tensor.Restricts.segmentedLocalizedSplittingPower_binaryDivision P f seg
            (SegmentedSplitRestriction.ofLeg c₀ (SegmentRegionSpec.parentType s (t :: rest)))
            (SegmentedSplitRestriction.ofLeg c₀ s.type)
            (SegmentedSplitRestriction.ofLeg c₀ (SegmentRegionSpec.parentType t rest))
            (SegmentedSplitRestriction.ofLeg_sum c₀ (SegmentRegionSpec.parentType s (t :: rest))
              s.type (SegmentRegionSpec.parentType t rest) (fun _ ↦ rfl))
            target targetHead targetTail htarget)) ?_
      exact (Tensor.Isomorphic.symSix_external _ _).restricts

end RegionalSymSix

end AlgebraicComplexity
