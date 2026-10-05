/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinogradSplitWordCore
import Mathlib.Tactic.FinCases

set_option autoImplicit false

/-!
# Equivalence between native CW chunks and complete-split words

This dependency-light module upgrades the native Coppersmith--Winograd complete-split encoding to
an equivalence.  It realizes the finite chunk alphabet used in the complete-split distributions of
`papers/sources/2404.16349/prelim.tex:249-269` of [alman2025more]; recursive parent/child
splitting and tensor reassociation remain downstream.

## References

- [alman2025more] Josh Alman, Ran Duan, Virginia Vassilevska Williams, Yinzhan Xu, Zixuan Xu,
  and Renfei Zhou, *More Asymmetry Yields Faster Matrix Multiplication*.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor

universe u

/-- The native three CW blocks are exactly the three complete-split digits. -/
noncomputable def cwBlockDigitEquiv : CWBlock ≃ SplitDigit :=
  Equiv.ofBijective cwBlockDigit ⟨cwBlockDigit_injective, by
    intro digit
    fin_cases digit
    · exact ⟨.zero, rfl⟩
    · exact ⟨.middle, rfl⟩
    · exact ⟨.last, rfl⟩⟩

/-- The block/digit equivalence acts by the underlying complete-split digit map. -/
@[simp] theorem cwBlockDigitEquiv_apply (block : CWBlock) :
    cwBlockDigitEquiv block = cwBlockDigit block :=
  rfl

/-- Complete-split encoding is an equivalence, not merely an injection: every ternary word is a
unique native CW block word in the same position order. -/
noncomputable def cwChunkSplitWordEquiv (depth : ℕ) :
    PositiveWord CWBlock (2 ^ depth - 1) ≃ SplitWord depth :=
  (positiveWordEquiv CWBlock (2 ^ depth - 1)).trans
    (Equiv.arrowCongr (cwChunkPositionEquiv depth) cwBlockDigitEquiv)

/-- The chunk/word equivalence acts by the underlying complete-split encoding, so upgrading the
encoding to an equivalence changes no value. -/
@[simp] theorem cwChunkSplitWordEquiv_apply (depth : ℕ)
    (chunk : PositiveWord CWBlock (2 ^ depth - 1)) :
    cwChunkSplitWordEquiv depth chunk = cwChunkSplitWord depth chunk :=
  rfl

end AlgebraicComplexity.Examples
