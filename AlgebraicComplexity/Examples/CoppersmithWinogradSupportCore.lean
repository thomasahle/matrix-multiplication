/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinogradCore

/-!
# The six-block support of the Coppersmith--Winograd tensor

This lightweight module contains the finite CW support, its tightness witness, and the elementary
constituent-volume data.  Probability distributions and entropy identities are layered in the
public re-exporting module `CoppersmithWinogradSupport`.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor

/-- The three coordinate blocks in the standard CW partition. -/
inductive CWBlock
  | zero
  | middle
  | last
  deriving DecidableEq, Repr

private def cwBlockEquiv : Option (Option Unit) ≃ CWBlock where
  toFun
    | none => .zero
    | some none => .middle
    | some (some _) => .last
  invFun
    | .zero => none
    | .middle => some none
    | .last => some (some ())
  left_inv x := by
    rcases x with _ | (_ | u)
    · rfl
    · rfl
    · cases u
      rfl
  right_inv x := by cases x <;> rfl

instance : Fintype CWBlock :=
  Fintype.ofEquiv (Option (Option Unit)) cwBlockEquiv

/-- A CW block address has one block label on each tensor leg. -/
abbrev CWBlockAddress := ∀ _ : Leg, CWBlock

abbrev cwBlockAddress (x y z : CWBlock) : CWBlockAddress :=
  ofLegs x y z

abbrev cw200 : CWBlockAddress := cwBlockAddress .last .zero .zero
abbrev cw020 : CWBlockAddress := cwBlockAddress .zero .last .zero
abbrev cw002 : CWBlockAddress := cwBlockAddress .zero .zero .last
abbrev cw011 : CWBlockAddress := cwBlockAddress .zero .middle .middle
abbrev cw101 : CWBlockAddress := cwBlockAddress .middle .zero .middle
abbrev cw110 : CWBlockAddress := cwBlockAddress .middle .middle .zero

/-- The standard six-address support of the full CW tensor. -/
def cwBlockSupport : Finset CWBlockAddress :=
  {cw200, cw020, cw002, cw011, cw101, cw110}

end AlgebraicComplexity.Examples
