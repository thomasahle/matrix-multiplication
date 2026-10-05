/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoFineCellPower
import AlgebraicComplexity.Examples.CoppersmithWinogradZeroOrientationCoherentRestriction

set_option autoImplicit false

/-!
# The coherent certificate of one fine cell address, in every zero orientation

Layer 4 (`AlgebraicComplexity/Examples/`).  Stage (2) of the `[duan2023faster]` section 6.3 value
route fuses one **cell** of the reference leaf into a single matrix-multiplication tensor.  The
fusion datum `CTensor.PermutedSharedOneSliceFiberData`
(`MatrixMultiplication/PermutedSharedOneSliceFiber.lean`) needs, as *data*, one coherent one-slice
certificate **per supported address** of the cell's partitioned tensor, all at one common dimension
`q ^ k` and all using one common map on the shared zero leg.

Two things stand between the committed inputs and that datum, and this module supplies both.

## The fine letter base, in every orientation at once

`Examples/DuanWuZhouLevelTwoFineCellBase.lean` supplies the fine-letter coherent base only in the
zero-`X` and zero-`Y` frames (`dwz63FineZeroXBase`, `dwz63FineZeroYBase`).  Three of the twelve
non-orbit cells of `table:result-2nd` --- `(1,3,0)`, `(3,1,0)` and `(2,2,0)` --- have their zero
coordinate on `Z` and are not reachable from either.  `dwz63FineZeroRotatedBase` is the single
leg-indexed base that covers all three frames, obtained by running the committed
`cwZeroBaseRotatedWordCoherentRestriction` (itself leg-indexed) at word length `1`, which is what a
fine letter is.  It subsumes both committed instances.

## The address, decoded

`CTensor.PermutedSharedOneSliceFiberData.certificate` is indexed by `P.support`, so producing it
means turning a supported **address** back into the supported **word** the coherent recursion
consumes --- and `exists_positiveSupportWord_of_mem_positivePower_support`
(`Tensor/PartitionedPower.lean:545`) is an existential, which cannot be eliminated into data.  The
committed idiom is used: `Classical.choice` first, so the goal is the `Prop`
`Nonempty { C // HEq (C.legMap .Z) zMap }`, and the shared-leg coherence travels *inside* the
subtype, fixed against a `zMap` chosen before the decoding.  That is what makes the three fields of
the fusion datum cohere; reading a `zMap` off a chosen certificate would leave it opaque and
`z_coherent` unprovable.

The dimension is rewritten in the goal, not transported: `OneSliceRestriction.castDimension` is a
`subst` with no `legMap` lemma, so a `HEq` does not travel across it.

Primary source: Ran Duan, Hongxun Wu and Renfei Zhou, *Faster Matrix Multiplication via Asymmetric
Hashing*, arXiv:2210.10173, `global_value.tex` section 6.3 and `lem:non-rot-values`.

Exact source lines: `papers/sources/2210.10173/global_value.tex:332-378` (§6.3),
`papers/sources/2210.10173/second_power.tex:144-158` (`lem:non-rot-values`),
`papers/sources/2210.10173/global_value.tex:354-378` (`table:result-2nd`).
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor MoreAsymmetryCompatibility

universe u

variable (K : Type u) [CommRing K] (q : ℕ)

/-! ## The fine-letter base, indexed by the zero leg -/

/-- **The fine-letter coherent base in the frame that rotates `zero` onto `Z`.**

A supported fine letter --- a length-one word of Coppersmith--Winograd blocks --- whose `zero` leg
carries the constant zero pair, together with its rotated one-slice certificate at the transparent
dimension `dwz63FineDimension q zero` and the retained proof that its shared-leg map is the
committed canonical one.

At `zero = .X` and `zero = .Y` this is `dwz63FineZeroXBase` / `dwz63FineZeroYBase`; at `zero = .Z`
it is the case those two do not cover, and which `(1,3,0)`, `(3,1,0)` and `(2,2,0)` need. -/
noncomputable def dwz63FineZeroRotatedBase (zero : Leg)
    (s : ((cwPartitionedTensor K q).positivePower 1).support)
    (hzero : s.1 zero = positiveWordConst CWBlock.zero 1) :
    { C : OneSliceRestriction
        (Tensor.permute (K := K) (zeroOrientation zero)
          (((cwPartitionedTensor K q).positivePower 1).constituent s.1))
        (dwz63FineDimension q zero s.1) //
      HEq (C.legMap .Z) (cwZeroBaseRotatedWordCanonicalZMap K q zero 1) } := by
  classical
  obtain ⟨a, ha⟩ := s
  refine Classical.choice ?_
  obtain ⟨word, hword⟩ :=
    (cwPartitionedTensor K q).exists_positiveSupportWord_of_mem_positivePower_support 1 ha
  subst hword
  refine ⟨?_⟩
  have hzWord : positiveSupportWordBlockAddress cwBlockSupport 1 word zero =
      positiveWordConst CWBlock.zero 1 := hzero
  have hdim : dwz63FineDimension q zero
        (positiveSupportWordBlockAddress (cwPartitionedTensor K q).support 1 word) =
      positiveWordProduct
        (fun t ↦ cwBaseConstituentDimension q t (secondLiveLeg zero)) 1 word :=
    (positiveWordProduct_cwBaseDimension_secondLiveLeg_eq_pow_cwWordMiddleCount q zero 1 word
      hzWord).symm
  rw [(cwPartitionedTensor K q).positivePower_constituent_positiveSupportWordBlockAddress 1 word,
    hdim]
  exact cwZeroBaseRotatedWordCoherentRestriction K q zero 1 word hzWord

/-! ## The canonical shared map of a whole cell word -/

/-- **The canonical map on the shared zero block of a whole cell word.**

The `(n+1)`-fold one-slice coordinate product of the fine-letter map with itself.  It is fixed
here, *before* any address is decoded, which is what lets the coherence of
`dwz63FineCellRotatedCoherent` be stated at all. -/
noncomputable def dwz63FineCellRotatedCanonicalZMap (zero : Leg) (n : ℕ) :
    PositivePowerBlockSpace K (PositivePowerBlockSpace K (CWPartitionBlockSpace K q) 1) n
        ((zeroOrientation zero).symm .Z)
        (positiveWordConst (positiveWordConst CWBlock.zero 1) n) →ₗ[K] MMSpace K 1 1 1 .Z :=
  OneSliceRestriction.constWordZMap
    (A := fun _ : Leg ↦ PositiveWord CWBlock 1)
    (V := PositivePowerBlockSpace K (CWPartitionBlockSpace K q) 1)
    ((zeroOrientation zero).symm .Z)
    (zLabel := positiveWordConst CWBlock.zero 1)
    (cwZeroBaseRotatedWordCanonicalZMap K q zero 1) n

/-! ## The certificate of one supported cell address -/

/-- **Every supported address of the fine positive power that is trivial on `zero` and has
one-slice exponent `k` carries a coherent certificate at the *uniform* dimension `q ^ k`.**

This is the datum the shared-fibre fusion consumes.  Both hypotheses are read off the address:
`hzero` is `hz` (`Examples/DuanWuZhouLevelTwoFineCellZeroLeg.lean`), and `hones` is `huniform`
(`Examples/DuanWuZhouLevelTwoFineCellUniform.lean`,
`Examples/DuanWuZhouLevelTwoFineCellBridge.lean`).  Neither mentions a word, so a client never has
to decode an address itself. -/
noncomputable def dwz63FineCellRotatedCoherent (zero : Leg) (n k : ℕ)
    (s : BlockAddress (fun _ : Leg ↦ PositiveWord (PositiveWord CWBlock 1) n))
    (hmem : s ∈ (((cwPartitionedTensor K q).positivePower 1).positivePower n).support)
    (hzero : s zero = positiveWordConst (positiveWordConst CWBlock.zero 1) n)
    (hones : dwz63CellOnes zero n s = k) :
    { C : OneSliceRestriction
        (Tensor.permute (K := K) (zeroOrientation zero)
          ((((cwPartitionedTensor K q).positivePower 1).positivePower n).constituent s))
        (q ^ k) //
      HEq (C.legMap .Z) (dwz63FineCellRotatedCanonicalZMap K q zero n) } := by
  classical
  refine Classical.choice ?_
  obtain ⟨word, hword⟩ :=
    ((cwPartitionedTensor K q).positivePower
        1).exists_positiveSupportWord_of_mem_positivePower_support
      n hmem
  subst hword
  refine ⟨?_⟩
  have hzWord : positiveSupportWordBlockAddress
      ((cwPartitionedTensor K q).positivePower 1).support n word
      ((zeroOrientation zero).symm .Z) =
      positiveWordConst (positiveWordConst CWBlock.zero 1) n := by
    rw [zeroOrientation_symm_Z]
    exact hzero
  have hdim : positiveWordProduct
      (fun t : ((cwPartitionedTensor K q).positivePower 1).support ↦
        dwz63FineDimension q zero t.1) n word = q ^ k := by
    rw [positiveWordProduct_dwz63FineDimension_eq_pow_dwz63CellOnes K q zero n word]
    exact congrArg (fun e ↦ q ^ e) hones
  rw [← hdim]
  exact OneSliceRestriction.permutedCoherentPositivePowerConstituent
    ((cwPartitionedTensor K q).positivePower 1)
    (fun t ↦ dwz63FineDimension q zero t.1) (zeroOrientation zero)
    (zLabel := positiveWordConst CWBlock.zero 1)
    (cwZeroBaseRotatedWordCanonicalZMap K q zero 1)
    (fun t ht ↦ dwz63FineZeroRotatedBase K q zero t
      (by rw [zeroOrientation_symm_Z] at ht; exact ht))
    n word hzWord

end AlgebraicComplexity.Examples
