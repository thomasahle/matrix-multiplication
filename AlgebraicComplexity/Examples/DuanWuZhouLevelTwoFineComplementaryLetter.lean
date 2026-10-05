/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoFineCellZeroLeg

set_option autoImplicit false

/-!
# Complementary fine letters, and the completion that makes a hole family degenerate

Layer 4 (`AlgebraicComplexity/Examples/`).  Two facts about the Coppersmith--Winograd block
alphabet that `[duan2023faster]`'s Additional Zeroing-Out Step 1 (`global_value.tex:52-62`) and its
`lemma:triple_implies_compatible` (`:63-72`) rest on.

## Degrees determine letters, and a zero leg makes the other two complementary

`cwBlockSupport` (`Examples/CoppersmithWinogradSupportCore.lean:62`) is the six addresses whose
three block degrees sum to two, and `cwBlockDegree` is injective --- the three degrees `0, 1, 2`
name the three letters.  So on a support address whose `Y` letter is `zero`, the `X` letter is
determined by the `Z` letter: it is `cwBlockComplement` of it.  That is the whole content of the
paper's remark that on a `j = 0` component the `X̂`-rule *is* the `Ẑ`-rule, which is what makes
Step 1's three legwise rules imply the joint compatibility statement.

At the square (level-two) alphabet the same holds letterwise, since a fine letter is a pair of
`CWBlock`s and the square degree is the sum of the two block degrees
(`cwSquareBlockDegree_val`).  `cwSquare_fineX_eq_complement_of_zeroY` is that statement.

## The completion, and why it is a guard

`cwBlockAddress_exists_split` says: given a supported pair of level-one addresses and any pair of
`Z`-letters of the same total degree, the pair can be rebuilt with those `Z`-letters and the same
`X`- and `Y`-degrees.  Position by position this is why the *uncut* fine ambient carries **every**
fine `Z`-word of the right degree over a given coarse cell --- and hence why a hole family defined
by "some ambient address over a competitor carries this word" cannot depend on the word at all.
Any proposed hole family should be checked against this lemma before it is built on: a family that
this completion makes constant in `z` is the `∅`-or-`univ` family that the aggregate hole fraction
refutes.

Primary source `[duan2023faster]`: Ran Duan, Hongxun Wu and Renfei Zhou, *Faster Matrix
Multiplication via Asymmetric Hashing*, arXiv:2210.10173, section 6.1 `sec:global-algo`
(`global_value.tex`).
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor

/-! ## Degrees name letters -/

/-- **The three block degrees name the three blocks.** -/
theorem cwBlockDegree_injective : Function.Injective cwBlockDegree := by
  decide

/-- **The complementary block**: the letter whose degree completes the given one to two. -/
def cwBlockComplement : CWBlock → CWBlock
  | .zero => .last
  | .middle => .middle
  | .last => .zero

@[simp] theorem cwBlockDegree_cwBlockComplement (b : CWBlock) :
    cwBlockDegree (cwBlockComplement b) + cwBlockDegree b = 2 := by
  cases b <;> rfl

/-! ## The support, by degree -/

/-- **`cwBlockSupport` is the degree-two antidiagonal**, at an explicit address. -/
theorem mem_cwBlockSupport_ofLegs (x y z : CWBlock) :
    cwBlockAddress x y z ∈ cwBlockSupport ↔
      cwBlockDegree x + cwBlockDegree y + cwBlockDegree z = 2 := by
  cases x <;> cases y <;> cases z <;> decide

/-! ## A zero `Y` leg makes `X` the complement of `Z` -/

/-- **On a supported address with `Y`-letter `zero`, the `X`-letter is the complement of the
`Z`-letter.**  `[duan2023faster]`'s "`X_I` is in a unique triple" on a `j = 0` component: the
`X̂`-rule and the `Ẑ`-rule are the same rule there. -/
theorem cwBlock_eq_complement_of_zeroY (x z : CWBlock)
    (h : cwBlockAddress x CWBlock.zero z ∈ cwBlockSupport) :
    x = cwBlockComplement z := by
  rw [mem_cwBlockSupport_ofLegs] at h
  refine cwBlockDegree_injective ?_
  have hc := cwBlockDegree_cwBlockComplement z
  cases z <;> cases x <;> simp_all [cwBlockDegree, cwBlockComplement]

/-! ## The letterwise complement at the square alphabet -/

/-- The letterwise complement of a fine (level-two) letter. -/
def cwSquareComplementLetter (p : PositiveWord CWBlock 1) : PositiveWord CWBlock 1 :=
  (cwBlockComplement p.1, cwBlockComplement p.2)

/-- **The square-alphabet form of `cwBlock_eq_complement_of_zeroY`.**

A raw fine square address whose `Y` letter has square degree zero has its `X` letter the letterwise
complement of its `Z` letter. -/
theorem cwSquare_fineX_eq_complement_of_zeroY
    (f : BlockAddress (fun _ : Leg ↦ PositiveWord CWBlock 1))
    (hf : f ∈ cwSquareRawSupport) (hY : cwSquareBlockDegree (f Leg.Y) = 0) :
    f Leg.X = cwSquareComplementLetter (f Leg.Z) := by
  classical
  obtain ⟨q, hq, hqf⟩ := Finset.mem_map.mp hf
  obtain ⟨b₁, b₂⟩ := q
  obtain ⟨hb₁, hb₂⟩ := Finset.mem_product.mp hq
  have hfX : f Leg.X = (b₁ Leg.X, b₂ Leg.X) := by rw [← hqf]; rfl
  have hfY : f Leg.Y = (b₁ Leg.Y, b₂ Leg.Y) := by rw [← hqf]; rfl
  have hfZ : f Leg.Z = (b₁ Leg.Z, b₂ Leg.Z) := by rw [← hqf]; rfl
  have hy : cwBlockDegree (b₁ Leg.Y) + cwBlockDegree (b₂ Leg.Y) = 0 := by
    have := hY
    rw [hfY] at this
    simpa [cwSquareBlockDegree, Fin.ext_iff] using this
  have hy₁ : b₁ Leg.Y = CWBlock.zero := by
    refine cwBlockDegree_injective ?_
    have : cwBlockDegree (b₁ Leg.Y) = 0 := by omega
    simpa [cwBlockDegree] using this
  have hy₂ : b₂ Leg.Y = CWBlock.zero := by
    refine cwBlockDegree_injective ?_
    have : cwBlockDegree (b₂ Leg.Y) = 0 := by omega
    simpa [cwBlockDegree] using this
  have hmem₁ : cwBlockAddress (b₁ Leg.X) CWBlock.zero (b₁ Leg.Z) ∈ cwBlockSupport := by
    have : cwBlockAddress (b₁ Leg.X) (b₁ Leg.Y) (b₁ Leg.Z) = b₁ := by
      funext c; cases c <;> rfl
    rw [← hy₁, this]
    exact hb₁
  have hmem₂ : cwBlockAddress (b₂ Leg.X) CWBlock.zero (b₂ Leg.Z) ∈ cwBlockSupport := by
    have : cwBlockAddress (b₂ Leg.X) (b₂ Leg.Y) (b₂ Leg.Z) = b₂ := by
      funext c; cases c <;> rfl
    rw [← hy₂, this]
    exact hb₂
  rw [hfX, hfZ]
  exact Prod.ext (cwBlock_eq_complement_of_zeroY _ _ hmem₁)
    (cwBlock_eq_complement_of_zeroY _ _ hmem₂)

/-! ## The completion -/

/-- **Every pair of `Z`-letters of the right total degree is realised over the same coarse cell.**

Given two supported level-one addresses and any two `Z`-letters whose degrees sum to the same
total, the pair can be rebuilt carrying exactly those `Z`-letters, with the `X`- and `Y`-degree
totals unchanged --- so the coarse square cell is unchanged.

This is **not** a theorem of the paper.  It is a project-specific definition-validation and
regression guard: exhaustive computation over the three-letter alphabet and the six supported
addresses, showing that an uncut coarse square fibre carries every fine `Z` letter of the right
degree.  That is what exposes why the rejected compatibility-free `dwz63ReferenceHoles` object
degenerates, and it protects Additional Zeroing-Out Step 1 (`global_value.tex:52-61`); it is in no
sense a substitute proof of `lemma:triple_implies_compatible`.  It is also the
guard: it shows that "some address over this coarse cell carries this fine `Z`-word" is a condition
on the word's **degrees** alone. -/
theorem cwBlockAddress_exists_split :
    ∀ b₁ ∈ cwBlockSupport, ∀ b₂ ∈ cwBlockSupport, ∀ z₁ z₂ : CWBlock,
      cwBlockDegree z₁ + cwBlockDegree z₂ =
          cwBlockDegree (b₁ Leg.Z) + cwBlockDegree (b₂ Leg.Z) →
        ∃ c₁ ∈ cwBlockSupport, ∃ c₂ ∈ cwBlockSupport,
          c₁ Leg.Z = z₁ ∧ c₂ Leg.Z = z₂ ∧
            cwBlockDegree (c₁ Leg.X) + cwBlockDegree (c₂ Leg.X) =
              cwBlockDegree (b₁ Leg.X) + cwBlockDegree (b₂ Leg.X) ∧
            cwBlockDegree (c₁ Leg.Y) + cwBlockDegree (c₂ Leg.Y) =
              cwBlockDegree (b₁ Leg.Y) + cwBlockDegree (b₂ Leg.Y) := by
  decide

end AlgebraicComplexity.Examples
