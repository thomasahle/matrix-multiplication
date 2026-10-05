/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.SegmentedSplitRestriction
import AlgebraicComplexity.Combinatorics.ConditionalWordTypeCore
import AlgebraicComplexity.Combinatorics.WordTypeMultiplicityFilter

set_option autoImplicit false

/-!
# Joint-word multiplicities are segment multiplicities

Layer 3 (`AlgebraicComplexity/MatrixMultiplication/`).  One spelling bridge, isolated because it is
generic and carries no `[duan2023faster]` data: the multiplicity of the pair `(t, a)` in the joint
word of a segmentation with a letter word is the number of positions of segment `t` carrying the
letter `a`, i.e. the segment-`t` distribution evaluated at `a`.

The two spellings are the tree's two ways of writing the same count.
`Combinatorics/CompatibleSplitCountDefs.lean` states DWZ's compatibility conditions with
`WordType.multiplicity (WordType.jointWord comp w)` --- `BoundaryMatched` at
`Combinatorics/CompatibleSplitCountDefs.lean:117` and `IsUseful` at `:127` --- while the localized
hole machinery states them with `segmentMultiplicity`
(`MatrixMultiplication/SegmentedSplitRestriction.lean:55`).  The same conversion is performed
inline inside the proof of `isUseful_of_segmentedAvailableWord`
(`Examples/DuanWuZhouLevelTwoSeedInputs.lean:235`); this module states it once, so that a client
proving a `BoundaryMatched` goal out of segment distributions can `rw` instead of re-deriving it.

## The paper step this serves

It is not itself a statement of any paper.  Its consumer is the transcription of the claim
`lemma:triple_implies_compatible` of `[duan2023faster]`, section 6.1 `sec:global-algo`
(`papers/sources/2210.10173/global_value.tex:63-71`), whose conclusion is `def:global-compatible`
(`:44-50`): condition `item:average` (`:48`) is a family of equations
`split(K̂, S_{i,j,k}) = α̃_{i,j,k}` on the boundary components, which the tree's
`BoundaryMatched`
writes with `multiplicity ∘ jointWord` and the Step-1 zeroing rules
(`Examples/DuanWuZhouLevelTwoStepOneKeep.lean`, transcribing `:52-61`) write with
`segmentMultiplicity`.  Nothing about DWZ's alphabet, split tables or components enters here.

Primary source `[duan2023faster]`: Ran Duan, Hongxun Wu and Renfei Zhou, *Faster Matrix
Multiplication via Asymmetric Hashing*, arXiv:2210.10173, section 6.1 `sec:global-algo`,
`papers/sources/2210.10173/global_value.tex:44-71`.
-/

namespace AlgebraicComplexity

universe w

variable {I : Type w} [DecidableEq I] {n m : ℕ}

/-- **A joint-word multiplicity is a segment multiplicity.**

`WordType.multiplicity (WordType.jointWord seg word) (t, a)` counts the positions `i` with
`seg i = t` and `word i = a`; that is `segmentMultiplicity seg word t a` by definition of both
sides.  The proof is the identification of the two position filters, with
`WordType.multiplicity_eq_card_filter` absorbing the difference between `multiplicity`'s internal
`Classical.propDecidable` and the ambient `[DecidableEq I]`.

Proof sketch: rewrite `multiplicity` as an explicit filter cardinality, unfold
`segmentMultiplicity` to its filter cardinality, and check the two predicates agree pointwise via
`Prod.mk.injEq`. -/
theorem multiplicity_jointWord_eq_segmentMultiplicity
    (seg : Fin n → Fin m) (word : Fin n → I) (t : Fin m) (a : I) :
    WordType.multiplicity (WordType.jointWord seg word) (t, a) =
      segmentMultiplicity seg word t a := by
  classical
  have hseg : segmentMultiplicity seg word t a =
      (Finset.univ.filter fun i ↦ seg i = t ∧ word i = a).card := rfl
  rw [WordType.multiplicity_eq_card_filter, hseg]
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, WordType.jointWord, Prod.mk.injEq]

end AlgebraicComplexity
