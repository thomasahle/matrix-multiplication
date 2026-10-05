/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoFineCellHypotheses

set_option autoImplicit false

/-!
# Every typed fine word occurs in the `(0,2,2)` fibre

Layer 4 (`AlgebraicComplexity/Examples/`).  `Examples/DuanWuZhouLevelTwoFineCellFusion.lean` fuses
one cell of the `[duan2023faster]` section 6.3 fine leaf onto `⟨1, |fibre| * q ^ k, 1⟩`, and
`Examples/DuanWuZhouLevelTwoFineCellWeight.lean` reads that as a `tau`-weight with `|fibre|` left
symbolic.  This module is the lower bound on `|fibre|`: the whole `alphatilde`-typical type class
injects into the fibre, so

`|typeClass (n+1) alphatilde| <= |fibre|`,

which is the half that a *value* lower bound needs.  (Injectivity of `s ↦ s Leg.Z`, which image 87
already has as `dwz63_finePower_injOn_liveLeg`, gives the reverse inequality and is not used here:
it is the wrong direction for a lower bound.)

## `alphatilde`, not `alpha`

The profile is the split profile of `global_value.tex`'s table --- `dwz63AlphaTilde`'s rows --- and
it is a profile on **fine letters**, `PositiveWord CWBlock 1`, i.e. on ordered pairs of level-one
Coppersmith--Winograd blocks.  That is exactly the alphabet `WordType.typeClass` is taken over here,
and exactly what `SegmentedSplitRestriction.ofLeg Leg.Z` restricts, so the two agree with no
translation.  There is no separate coarse `alpha` in this statement.

## The construction: the zero leg forces the third leg

For the `(0,2,2)` frame the zero coordinate is on `X`, and `alphatilde` is carried on `Z`
(`secondLiveLeg .X = .Z`).  Given the `Z` word, every other leg is *forced*:

* the `X` letter is the constant zero pair, because the cell has `X`-degree `0`;
* the `Y` letter is the **degree complement** of the `Z` letter, sub-position by sub-position:
  a supported Coppersmith--Winograd triple has its three degrees summing to `2`, so with the `X`
  digit `0` the `Y` digit is `2` minus the `Z` digit --- `dwz63BlockComplement` below.

So the witness is not a choice: it is a function of the `Z` word, which is why this is an explicit
injection and not an existence statement.  Note that the witness letter is supported for **every**
`Z` pair, with no degree hypothesis --- each sub-position sums to `2` by construction.  The degree
hypothesis `halpha` enters only where the address has to coarsen to the *fixed* target `(0,2,2)`:
that needs every occurring `Z` letter to have coarse degree `2`, and then the `Y` degree is
`4 - 2 = 2` automatically.

Primary source: Ran Duan, Hongxun Wu and Renfei Zhou, *Faster Matrix Multiplication via Asymmetric
Hashing*, arXiv:2210.10173, `global_value.tex` section 6.3 and `lem:non-rot-values`.

Exact source lines: `papers/sources/2210.10173/global_value.tex:332-378` (§6.3),
`papers/sources/2210.10173/second_power.tex:144-158` (`lem:non-rot-values`).
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor MoreAsymmetryCompatibility

universe u

/-! ## The degree complement of a level-one block -/

/-- **The degree complement**: the level-one block whose degree is `2` minus the given one.  On a
supported triple with a zero digit, this is the digit forced on the remaining leg. -/
def dwz63BlockComplement : CWBlock → CWBlock
  | .zero => .last
  | .middle => .middle
  | .last => .zero

@[simp] theorem dwz63_blockDegree_complement (a : CWBlock) :
    cwBlockDegree (dwz63BlockComplement a) = 2 - cwBlockDegree a := by
  cases a <;> rfl

/-- The forced triple of a zero-`X` supported letter is supported, for every `Z` digit. -/
theorem dwz63_blockAddress_zero_complement_mem (a : CWBlock) :
    cwBlockAddress CWBlock.zero (dwz63BlockComplement a) a ∈ cwBlockSupport := by
  cases a <;> decide

/-- **The complement of a degree-two fine letter has degree two.**  Stated over
`CWBlock × CWBlock` so that `decide` applies: on `PositiveWord CWBlock 1` the `Fintype` instance is
the noncomputable `positiveWordFintype`, while the two types are definitionally equal, so a client
holding a `PositiveWord CWBlock 1` can still use this. -/
theorem dwz63_squareBlockDegree_complement_of_eq_two (a b : CWBlock)
    (h : cwSquareBlockDegree ((a, b) : PositiveWord CWBlock 1) = 2) :
    cwSquareBlockDegree
      ((dwz63BlockComplement a, dwz63BlockComplement b) : PositiveWord CWBlock 1) = 2 := by
  revert h
  cases a <;> cases b <;> decide

variable (K : Type u) [CommRing K] (q : ℕ)

/-! ## The forced fine letter -/

/-- **The zero-`X` fine letter forced by a `Z` pair.**  Its `X` pair is the constant zero pair, its
`Y` pair is the sub-position-wise degree complement, and its `Z` pair is the given one. -/
def dwz63ZeroXFineLetterAddress (p : PositiveWord CWBlock 1) :
    BlockAddress (fun _ : Leg ↦ PositiveWord CWBlock 1) :=
  ofLegs (positiveWordConst CWBlock.zero 1)
    ((dwz63BlockComplement p.1, dwz63BlockComplement p.2) : PositiveWord CWBlock 1) p

@[simp] theorem dwz63ZeroXFineLetterAddress_X (p : PositiveWord CWBlock 1) :
    dwz63ZeroXFineLetterAddress p Leg.X = positiveWordConst CWBlock.zero 1 := rfl

@[simp] theorem dwz63ZeroXFineLetterAddress_Z (p : PositiveWord CWBlock 1) :
    dwz63ZeroXFineLetterAddress p Leg.Z = p := rfl

@[simp] theorem dwz63ZeroXFineLetterAddress_Y (p : PositiveWord CWBlock 1) :
    dwz63ZeroXFineLetterAddress p Leg.Y =
      ((dwz63BlockComplement p.1, dwz63BlockComplement p.2) : PositiveWord CWBlock 1) := rfl

/-- **The forced letter is a supported fine letter.**  The witnessing word of supported level-one
triples is the pair of forced triples, and the block-address computation is a reduction at each of
the three legs. -/
theorem dwz63ZeroXFineLetterAddress_mem (p : PositiveWord CWBlock 1) :
    dwz63ZeroXFineLetterAddress p ∈ ((cwPartitionedTensor K q).positivePower 1).support := by
  classical
  rw [(cwPartitionedTensor K q).positivePower_support_eq_image_positiveSupportWordBlockAddress 1]
  refine Finset.mem_image.mpr
    ⟨(⟨cwBlockAddress CWBlock.zero (dwz63BlockComplement p.1) p.1,
        dwz63_blockAddress_zero_complement_mem p.1⟩,
      ⟨cwBlockAddress CWBlock.zero (dwz63BlockComplement p.2) p.2,
        dwz63_blockAddress_zero_complement_mem p.2⟩), Finset.mem_univ _, ?_⟩
  funext c
  cases c <;> rfl

/-- The forced letter, as an element of the fine support. -/
def dwz63ZeroXFineLetter (p : PositiveWord CWBlock 1) :
    ((cwPartitionedTensor K q).positivePower 1).support :=
  ⟨dwz63ZeroXFineLetterAddress p, dwz63ZeroXFineLetterAddress_mem K q p⟩

/-! ## The witness address of a typed `Z` word -/

/-- **The witness address of a `Z` word.**  Letterwise the forced fine letter; this is the map that
injects the type class into the fibre. -/
noncomputable def dwz63ZeroXFineWitness (n : ℕ)
    (zw : Fin (n + 1) → PositiveWord CWBlock 1) :
    BlockAddress (fun _ : Leg ↦ PositiveWord (PositiveWord CWBlock 1) n) :=
  positiveSupportWordBlockAddress ((cwPartitionedTensor K q).positivePower 1).support n
    ((positiveWordEquiv ((cwPartitionedTensor K q).positivePower 1).support n).symm
      (fun i ↦ dwz63ZeroXFineLetter K q (zw i)))

/-- The letterwise reading of the witness, at any leg. -/
theorem dwz63_zeroXFineWitness_equiv (n : ℕ)
    (zw : Fin (n + 1) → PositiveWord CWBlock 1) (c : Leg) :
    positiveWordEquiv (PositiveWord CWBlock 1) n (dwz63ZeroXFineWitness K q n zw c) =
      fun i ↦ dwz63ZeroXFineLetterAddress (zw i) c := by
  rw [dwz63ZeroXFineWitness,
    positiveWordEquiv_positiveSupportWordBlockAddress_recursive
      ((cwPartitionedTensor K q).positivePower 1).support n _ c,
    Equiv.apply_symm_apply]
  rfl

/-- The witness is trivial on the zero leg `X`. -/
theorem dwz63_zeroXFineWitness_X (n : ℕ)
    (zw : Fin (n + 1) → PositiveWord CWBlock 1) :
    dwz63ZeroXFineWitness K q n zw Leg.X =
      positiveWordConst (positiveWordConst CWBlock.zero 1) n := by
  refine (positiveWordEquiv (PositiveWord CWBlock 1) n).injective ?_
  rw [dwz63_zeroXFineWitness_equiv, positiveWordEquiv_const]
  rfl

/-- The witness carries the given word on the `alphatilde` leg `Z`. -/
theorem dwz63_zeroXFineWitness_Z (n : ℕ)
    (zw : Fin (n + 1) → PositiveWord CWBlock 1) :
    positiveWordEquiv (PositiveWord CWBlock 1) n (dwz63ZeroXFineWitness K q n zw Leg.Z) = zw := by
  rw [dwz63_zeroXFineWitness_equiv]
  rfl

/-- The witness is a supported address of the fine positive power. -/
theorem dwz63_zeroXFineWitness_mem (n : ℕ)
    (zw : Fin (n + 1) → PositiveWord CWBlock 1) :
    dwz63ZeroXFineWitness K q n zw ∈
      (((cwPartitionedTensor K q).positivePower 1).positivePower n).support := by
  classical
  rw [((cwPartitionedTensor K q).positivePower
    1).positivePower_support_eq_image_positiveSupportWordBlockAddress n]
  exact Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩

/-- The witness coarsens to the constant `(0,2,2)` address, provided every occurring `Z` letter has
coarse degree two. -/
theorem dwz63_zeroXFineWitness_coarsens (n : ℕ)
    (zw : Fin (n + 1) → PositiveWord CWBlock 1)
    (hdeg : ∀ i, cwSquareBlockDegree (zw i) = 2) (c : Leg) :
    positiveWordMap (cwSquareDegreeMap c) n (dwz63ZeroXFineWitness K q n zw c) =
      ofLegs (V := fun _ : Leg ↦ PositiveWord (Fin 5) n) (positiveWordConst (0 : Fin 5) n)
        (positiveWordConst (2 : Fin 5) n) (positiveWordConst (2 : Fin 5) n) c := by
  refine (positiveWordEquiv (Fin 5) n).injective ?_
  rw [positiveWordEquiv_map, dwz63_zeroXFineWitness_equiv]
  cases c
  · rw [ofLegs_X, positiveWordEquiv_const]
    funext i
    exact (by decide : cwSquareBlockDegree (positiveWordConst CWBlock.zero 1) = (0 : Fin 5))
  · rw [ofLegs_Y, positiveWordEquiv_const]
    funext i
    exact dwz63_squareBlockDegree_complement_of_eq_two (zw i).1 (zw i).2 (hdeg i)
  · rw [ofLegs_Z, positiveWordEquiv_const]
    funext i
    exact hdeg i

/-! ## The injection -/

/-- **Surjectivity of the fibre onto the type class**, as an injection the other way.

Every `alphatilde`-typed fine word on the `Z` leg is the `Z` leg of a supported address of the
one-segment localized power over the coarse cell `(0,2,2)`.  Together with
`WordType.card_typeClass_eq_multinomial` this is the lower bound on `|fibre|` that
`Examples/DuanWuZhouLevelTwoFineCellWeight.lean`'s symbolic cardinality needs. -/
theorem dwz63_card_typeClass_le_zeroXFineCellSupport (n : ℕ)
    (alphaTilde : PositiveWord CWBlock 1 → ℕ)
    (halpha : ∀ p : PositiveWord CWBlock 1, alphaTilde p ≠ 0 →
      cwSquareBlockDegree p = 2) :
    (WordType.typeClass (n + 1) alphaTilde).card ≤
      (((cwPartitionedTensor K q).positivePower 1).segmentedLocalizedSplittingPower
        cwSquareDegreeMap n 1 (fun _ ↦ 0)
        (SegmentedSplitRestriction.ofLeg
          (A := fun _ : Leg ↦ PositiveWord CWBlock 1) Leg.Z (fun _ ↦ alphaTilde))
        (ofLegs (V := fun _ : Leg ↦ PositiveWord (Fin 5) n) (positiveWordConst (0 : Fin 5) n)
          (positiveWordConst (2 : Fin 5) n) (positiveWordConst (2 : Fin 5) n))).support.card := by
  classical
  refine Finset.card_le_card_of_injOn (dwz63ZeroXFineWitness K q n) ?_ ?_
  · intro zw hzw
    have hzwFinset : zw ∈ WordType.typeClass (n + 1) alphaTilde := by simpa using hzw
    have htype : WordType.multiplicity zw = alphaTilde := WordType.mem_typeClass.mp hzwFinset
    have hdeg : ∀ i, cwSquareBlockDegree (zw i) = 2 := by
      intro i
      refine halpha (zw i) ?_
      rw [← htype]
      exact WordType.multiplicity_apply_ne_zero zw i
    have hmem : dwz63ZeroXFineWitness K q n zw ∈
        (((cwPartitionedTensor K q).positivePower 1).segmentedLocalizedSplittingPower
          cwSquareDegreeMap n 1 (fun _ ↦ 0)
          (SegmentedSplitRestriction.ofLeg
            (A := fun _ : Leg ↦ PositiveWord CWBlock 1) Leg.Z (fun _ ↦ alphaTilde))
          (ofLegs (V := fun _ : Leg ↦ PositiveWord (Fin 5) n) (positiveWordConst (0 : Fin 5) n)
            (positiveWordConst (2 : Fin 5) n) (positiveWordConst (2 : Fin 5) n))).support := by
      rw [dwz63_mem_cellPower_support_iff]
      refine ⟨dwz63_zeroXFineWitness_mem K q n zw,
        fun c ↦ dwz63_zeroXFineWitness_coarsens K q n zw hdeg c, ?_⟩
      rw [dwz63_zeroXFineWitness_Z]
      exact htype
    simpa using hmem
  · intro zw _ zw' _ heq
    have h := congrArg (fun s ↦ positiveWordEquiv (PositiveWord CWBlock 1) n (s Leg.Z)) heq
    rw [dwz63_zeroXFineWitness_Z, dwz63_zeroXFineWitness_Z] at h
    exact h

end AlgebraicComplexity.Examples
