/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Combinatorics.TypedWordMapFiberComposition
import AlgebraicComplexity.Examples.CoppersmithWinogradNestedTotalWeightCoarsening

set_option autoImplicit false

/-!
# Finite disintegration of the nested CW total-weight fiber

A depth-two complete-split word has two consecutive depth-one children.  The map
`cwDepthTwoTotalWeightPayload` records their two ordered total weights, while
`CWDepthTwoTotalWeightPayload.outer` adds those weights and recovers the ordinary depth-two total.
This module specializes the generic typed-word fiber disintegration to those two maps.

For a fine profile `a` and an outer target word, the resulting identity partitions the fine
total-weight fiber by its intermediate words of ordered two-child payloads.  The intermediate
profile is exactly `mappedType cwDepthTwoTotalWeightPayload a`; pushing it through `outer` gives
the ordinary depth-two total-weight profile.  Both statements are exact finite equalities.

At level four, set the generic word length to
`(parentWordDepth + 1) + (parentWordDepth + 1)`.  A middle word then has type

```text
Fin ((parentWordDepth + 1) + (parentWordDepth + 1)) →
  (Fin 2 → CWCoarseDigit 1),
```

which is the curried form of `CWLevelFourNestedTotalWeightWord parentWordDepth`; no flattening of
the labelled occurrence and child-side indices is required.

This exact disintegration is the finite counterpart of the conditional-entropy chain rule
`eq:coarse-conditional-chain` and is needed by the staged count in the Total-Weight
quotient-feature condition (`better_bound/paper.tex:1598-1609,1749-1761`).  It follows the
consecutive-child convention in Definition `def:split-hatI` of [alman2025more],
`papers/sources/2404.16349/prelim.tex:225-269`.  It deliberately makes no claim that either finite
profile agrees with an evaluator row, has a stated entropy, or occurs in a selected tensor.

## References

- [alman2025more] Josh Alman, Ran Duan, Virginia Vassilevska Williams, Yinzhan Xu, Zixuan Xu,
  and Renfei Zhou, *More Asymmetry Yields Faster Matrix Multiplication*.
- *Total-Weight Hashing and Rectangular Volume in the Coppersmith--Winograd Method*,
  Hypothesis `hyp:quotient-count`.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity
open scoped BigOperators

/-! ## The two-stage quotient map -/

/-- Adding the ordered depth-one totals after extracting them is the ordinary depth-two
total-weight map.

This is the function-level form of `cwDepthTwoTotalWeightPayload_outer`; it is convenient for
specializing functorial statements whose map is written as a composition. -/
@[simp] theorem cwDepthTwoTotalWeightOuter_comp_payload :
    CWDepthTwoTotalWeightPayload.outer ∘ cwDepthTwoTotalWeightPayload =
      cwSplitWordTotalDigit 2 := by
  funext word
  exact cwDepthTwoTotalWeightPayload_outer word

/-! ## Exact fiber disintegration -/

/-- Fine words of one fixed type and outer total word are exactly a nested payload word together
with a fine lift of that payload word.

The outer typed fiber uses the pushed payload profile
`mappedType cwDepthTwoTotalWeightPayload a`; the inner fiber retains the original fine profile
`a`.  Thus no multiplicity information is discarded between the two stages.

Proof sketch: specialize `WordType.typedWordMapFiberCompEquiv` to the payload and outer maps, then
rewrite their composite by `cwDepthTwoTotalWeightOuter_comp_payload`. -/
noncomputable def cwDepthTwoTotalWeightFiberCompEquiv
    {N : ℕ} (a : SplitWord 2 → ℕ)
    (target : Fin N → CWRecursiveChildDigit 2) :
    {word // word ∈
      WordType.typedWordMapFiber (cwSplitWordTotalDigit 2) a target} ≃
      Σ payloadWord : {payloadWord //
          payloadWord ∈ WordType.typedWordMapFiber
            CWDepthTwoTotalWeightPayload.outer
            (WordType.mappedType cwDepthTwoTotalWeightPayload a) target},
        {word // word ∈ WordType.typedWordMapFiber
          cwDepthTwoTotalWeightPayload a payloadWord.1} := by
  rw [← cwDepthTwoTotalWeightOuter_comp_payload]
  exact WordType.typedWordMapFiberCompEquiv
    cwDepthTwoTotalWeightPayload CWDepthTwoTotalWeightPayload.outer a target

/-- The fine outer-total fiber cardinality is the sum of the fine payload-fiber cardinalities over
all intermediate payload words of the pushed type.

This is an equality rather than an estimate: every fine word has exactly one ordered payload word.

Proof sketch: specialize the generic exact cardinality identity and rewrite the composite quotient
map as the ordinary depth-two total. -/
theorem card_cwDepthTwoTotalWeightFiber_eq_sum
    {N : ℕ} (a : SplitWord 2 → ℕ)
    (target : Fin N → CWRecursiveChildDigit 2) :
    (WordType.typedWordMapFiber (cwSplitWordTotalDigit 2) a target).card =
      ∑ payloadWord ∈ WordType.typedWordMapFiber
          CWDepthTwoTotalWeightPayload.outer
          (WordType.mappedType cwDepthTwoTotalWeightPayload a) target,
        (WordType.typedWordMapFiber
          cwDepthTwoTotalWeightPayload a payloadWord).card := by
  rw [← cwDepthTwoTotalWeightOuter_comp_payload]
  exact WordType.card_typedWordMapFiber_comp_eq_sum
    cwDepthTwoTotalWeightPayload CWDepthTwoTotalWeightPayload.outer a target

/-! ## Profile compatibility -/

/-- Pushing a fine profile first to ordered child totals and then to their sum gives the same
profile as pushing directly to the ordinary depth-two total.

Proof sketch: use functoriality of `mappedType` and the function-level quotient identity above. -/
theorem mappedType_cwDepthTwoTotalWeightPayload_outer
    (a : SplitWord 2 → ℕ) :
    WordType.mappedType CWDepthTwoTotalWeightPayload.outer
        (WordType.mappedType cwDepthTwoTotalWeightPayload a) =
      WordType.mappedType (cwSplitWordTotalDigit 2) a := by
  rw [← cwDepthTwoTotalWeightOuter_comp_payload]
  exact WordType.mappedType_comp
    cwDepthTwoTotalWeightPayload CWDepthTwoTotalWeightPayload.outer a

end AlgebraicComplexity.Examples
