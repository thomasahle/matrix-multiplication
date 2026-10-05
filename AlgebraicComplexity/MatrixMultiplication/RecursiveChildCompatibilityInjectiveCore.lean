/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.InterfaceTensorWordSplitCore
import AlgebraicComplexity.MatrixMultiplication.RecursiveChildOccurrences

set_option autoImplicit false

/-!
# Dependency-light injectivity of labelled recursive-child words

The complete-split compatibility argument observes both consecutive children of every parent
chunk.  This module identifies those lightweight half-word observations with the public split-word
equivalence and proves that the full labelled-child sequence loses no parent information.  It is
the finite semantic bridge used by the compatibility count in
`papers/sources/2404.16349/constituent.tex:404-429` of [alman2025more], the proof of Claim 6.18;
compatibility models and counting remain downstream.

## References

- [alman2025more] Josh Alman, Ran Duan, Virginia Vassilevska Williams, Yinzhan Xu, Zixuan Xu,
  and Renfei Zhou, *More Asymmetry Yields Faster Matrix Multiplication*.
-/

namespace AlgebraicComplexity.MoreAsymmetryCompatibility

open Tensor

universe u v

/-- The lightweight left-half observation is definitionally the public complete-split left
projection. -/
@[simp] theorem leftChildHalf_eq_splitWordSuccEquiv {depth : ℕ}
    (parent : SplitWord (depth + 1)) :
    leftChildHalf parent = (splitWordSuccEquiv depth parent).1 :=
  rfl

/-- The lightweight right-half observation is definitionally the public complete-split right
projection. -/
@[simp] theorem rightChildHalf_eq_splitWordSuccEquiv {depth : ℕ}
    (parent : SplitWord (depth + 1)) :
    rightChildHalf parent = (splitWordSuccEquiv depth parent).2 :=
  rfl

/-- If one parent chunk is determined by its complete-split word, then a positive word of parent
chunks is determined by the full sequence of its labelled left and right children. -/
theorem positiveWordLabelledChildren_injective
    {A : Type u} {depth n : ℕ}
    (encode : A → SplitWord (depth + 1)) (hinjective : Function.Injective encode) :
    Function.Injective (positiveWordLabelledChildren (n := n) encode) := by
  intro left right hchildren
  apply (positiveWordEquiv A n).injective
  funext sample
  apply hinjective
  apply (splitWordSuccEquiv depth).injective
  have hleft := congrFun hchildren (Fin.castAdd (n + 1) sample)
  have hright := congrFun hchildren (Fin.natAdd (n + 1) sample)
  rw [positiveWordLabelledChildren_left, positiveWordLabelledChildren_left] at hleft
  rw [positiveWordLabelledChildren_right, positiveWordLabelledChildren_right] at hright
  apply Prod.ext
  · simpa only [leftChildHalf_eq_splitWordSuccEquiv] using hleft
  · simpa only [rightChildHalf_eq_splitWordSuccEquiv] using hright

end AlgebraicComplexity.MoreAsymmetryCompatibility
