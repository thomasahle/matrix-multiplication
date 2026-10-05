/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoFineCellSupport

set_option autoImplicit false

/-!
# Letterwise determination lifts to words, and the fine-alphabet instance

Layer 4 (`AlgebraicComplexity/Examples/`).  `Examples/DuanWuZhouLevelTwoFineCellSupport.lean`
proves that a supported zero-coordinate Coppersmith--Winograd **letter** is pinned by its label on
either live leg.  The one-slice fusion needs that one level up, at the **fine** alphabet
`PositiveWord CWBlock 1`: its `hx` and `hy` hypotheses are injectivity of `address ↦ address c` on
the support of the localized power, whose letters are fine pairs rather than base blocks.

Rather than repeat the argument at each level, the lift is isolated as a statement about an
arbitrary partition support.  It is **relativised** to a predicate `Good` on letters, because the
determination it lifts is not unconditional: a Coppersmith--Winograd letter is pinned by one live
leg only when it is zero on the zero leg.  Taking `Good := fun _ ↦ True` recovers the plain form.

`PROMOTE:` `positiveSupportWord_injective_of_letterwise` mentions no Coppersmith--Winograd datum
and belongs next to `positiveSupportWordBlockAddress` in `Tensor/PartitionedPower.lean`.  It is
kept here only to avoid posting a `Tensor/`-level name mid-sprint.

Primary source: Ran Duan, Hongxun Wu and Renfei Zhou, *Faster Matrix Multiplication via Asymmetric
Hashing*, arXiv:2210.10173, `global_value.tex` section 6.3.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor MoreAsymmetryCompatibility

universe u w

/-- **Letterwise determination lifts to words.**  If two supported letters that both satisfy `Good`
and agree on leg `c` are equal, then two supported words whose letters all satisfy `Good` and whose
leg-`c` label words agree are equal. -/
theorem positiveSupportWord_injective_of_letterwise {A : Leg → Type w}
    [∀ c, DecidableEq (A c)] (support : Finset (BlockAddress A)) (c : Leg) (n : ℕ)
    (Good : support → Prop)
    (hdet : ∀ s t : support, Good s → Good t → s.1 c = t.1 c → s = t)
    (w w' : PositiveWord support n)
    (hw : ∀ position, Good (positiveWordEquiv support n w position))
    (hw' : ∀ position, Good (positiveWordEquiv support n w' position))
    (h : positiveSupportWordBlockAddress support n w c =
      positiveSupportWordBlockAddress support n w' c) :
    w = w' := by
  refine (positiveWordEquiv support n).injective ?_
  funext position
  refine hdet _ _ (hw position) (hw' position) ?_
  have hleft := congrFun
    (positiveWordEquiv_positiveSupportWordBlockAddress_recursive support n w c) position
  have hright := congrFun
    (positiveWordEquiv_positiveSupportWordBlockAddress_recursive support n w' c) position
  rw [← hleft, ← hright, h]

variable (K : Type u) [CommRing K] (q : ℕ)

/-- **A supported fine letter that is zero on the zero leg is pinned by its first-live-leg pair.**
A fine letter is a length-one word of base blocks, so this is the word form of
`cwSupported_eq_of_zero_of_firstLiveLeg_eq` at `m = 1`. -/
theorem dwz63_fineLetter_eq_of_zero_of_firstLiveLeg_eq (zero : Leg)
    (s t : ((cwPartitionedTensor K q).positivePower 1).support)
    (hs : s.1 zero = positiveWordConst CWBlock.zero 1)
    (ht : t.1 zero = positiveWordConst CWBlock.zero 1)
    (h : s.1 (firstLiveLeg zero) = t.1 (firstLiveLeg zero)) :
    s = t := by
  obtain ⟨ws, hws⟩ :=
    (cwPartitionedTensor K q).exists_positiveSupportWord_of_mem_positivePower_support 1 s.2
  obtain ⟨wt, hwt⟩ :=
    (cwPartitionedTensor K q).exists_positiveSupportWord_of_mem_positivePower_support 1 t.2
  refine Subtype.ext ?_
  rw [← hws, ← hwt]
  refine congrArg (positiveSupportWordBlockAddress (cwPartitionedTensor K q).support 1) ?_
  refine positiveSupportWord_injective_of_zero_firstLiveLeg zero 1 ws wt ?_ ?_ ?_
  · rw [show positiveSupportWordBlockAddress cwBlockSupport 1 ws zero = s.1 zero from
      congrFun hws zero]
    exact hs
  · rw [show positiveSupportWordBlockAddress cwBlockSupport 1 wt zero = t.1 zero from
      congrFun hwt zero]
    exact ht
  · rw [show positiveSupportWordBlockAddress cwBlockSupport 1 ws (firstLiveLeg zero) =
      s.1 (firstLiveLeg zero) from congrFun hws (firstLiveLeg zero),
    show positiveSupportWordBlockAddress cwBlockSupport 1 wt (firstLiveLeg zero) =
      t.1 (firstLiveLeg zero) from congrFun hwt (firstLiveLeg zero)]
    exact h

/-- **`hx` / `hy` for the fine power.**  Two supported fine words whose letters are all zero on the
zero leg and whose first-live-leg label words agree are equal. -/
theorem dwz63_finePower_injective_firstLiveLeg (zero : Leg) (n : ℕ)
    (w w' : PositiveWord ((cwPartitionedTensor K q).positivePower 1).support n)
    (hw : ∀ position,
      (positiveWordEquiv ((cwPartitionedTensor K q).positivePower 1).support n w position).1
        zero = positiveWordConst CWBlock.zero 1)
    (hw' : ∀ position,
      (positiveWordEquiv ((cwPartitionedTensor K q).positivePower 1).support n w' position).1
        zero = positiveWordConst CWBlock.zero 1)
    (h : positiveSupportWordBlockAddress
        ((cwPartitionedTensor K q).positivePower 1).support n w (firstLiveLeg zero) =
      positiveSupportWordBlockAddress
        ((cwPartitionedTensor K q).positivePower 1).support n w' (firstLiveLeg zero)) :
    w = w' :=
  positiveSupportWord_injective_of_letterwise
    ((cwPartitionedTensor K q).positivePower 1).support (firstLiveLeg zero) n
    (fun s ↦ s.1 zero = positiveWordConst CWBlock.zero 1)
    (fun s t hgs hgt hst ↦ dwz63_fineLetter_eq_of_zero_of_firstLiveLeg_eq K q zero s t hgs hgt hst)
    w w' hw hw' h

end AlgebraicComplexity.Examples
