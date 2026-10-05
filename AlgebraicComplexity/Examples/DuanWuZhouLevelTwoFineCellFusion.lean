/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoFineCellRotatedCertificate
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoFineCellSupport
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoFineCellInjective
import AlgebraicComplexity.MatrixMultiplication.PermutedSharedOneSliceFiber

set_option autoImplicit false

/-!
# Fusing one cell of the `[duan2023faster]` section 6.3 fine leaf

Layer 4 (`AlgebraicComplexity/Examples/`).  This is stage (2) of the section 6.3 value route: the
whole `alphatilde`-typical fibre over **one** cell with a zero coordinate restricts, exactly and
with no representative selection, onto a single matrix-multiplication tensor

`⟨1, |fibre| * q ^ k, 1⟩`.

The cardinality `|fibre|` is what carries the multinomial factor of
`global_value.tex`'s `V(T_{i,j,k}, alphatilde)`; a single fine word carries only the bare product
`q ^ k` of its per-pair volumes, which is strictly below the published value (at `(0,2,2)`,
`36 ^ tau` against `38 ^ tau`).  Recovering the cardinality is exactly what the shared-fibre fusion
does.

## The statement is about a *selection*, so one theorem serves every cell

`Tensor.PartitionedTensor.segmentedLocalizedSplittingPower` is by definition
`(P.positivePower n).select (segmentedLocalizedKeep …)`
(`MatrixMultiplication/SegmentedLocalizedHoleRepair.lean`), so the one-segment localized power of a
cell is literally an instance of the `select` below --- no second object is introduced, and the
`(2,2,0)` uniform sub-class of the pigeonhole
(`ZeroCoordinateMerge.exists_uniform_fibre_mergedDimension_le`) is another instance of the same
theorem, at a finer `keep`.

## What the client supplies, and what it does not

Only two hypotheses, both read off an address and neither mentioning a word:

* `hzero` --- the fibre is trivial on the zero leg (`hz`, from
  `Examples/DuanWuZhouLevelTwoFineCellZeroLeg.lean`);
* `hones` --- the one-slice exponent is the constant `k` on the fibre (`huniform`, from
  `Examples/DuanWuZhouLevelTwoFineCellUniform.lean` and
  `Examples/DuanWuZhouLevelTwoFineCellBridge.lean`).

The two injectivity hypotheses `hx`, `hy` of the generic fusion are **not** asked for: on a
zero-coordinate fibre they are consequences of `hzero`, because a supported Coppersmith--Winograd
block that is trivial on one leg is pinned by either of the other two
(`cwSupported_eq_of_zero_of_firstLiveLeg_eq`, `cwSupported_eq_of_zero_of_secondLiveLeg_eq`).  The
block alphabet `fun _ : Leg ↦ PositiveWord (PositiveWord CWBlock 1) n` does not depend on the leg,
so the orientation rewrites `zeroOrientation_symm_X` / `_Y` / `_Z` are ordinary rewrites here
rather than the leg-by-leg reductions the Coppersmith--Winograd interface fusion needs.

The conclusion stays in the permuted frame `Tensor.permute (zeroOrientation zero)`, as the
committed orientation discipline requires: rotating back is an isomorphism and belongs with the
leaf packaging.

Primary source: Ran Duan, Hongxun Wu and Renfei Zhou, *Faster Matrix Multiplication via Asymmetric
Hashing*, arXiv:2210.10173, `global_value.tex` section 6.3 and `lem:non-rot-values`.

Exact source lines: `papers/sources/2210.10173/global_value.tex:332-378` (§6.3),
`papers/sources/2210.10173/second_power.tex:144-158` (`lem:non-rot-values`).
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor MoreAsymmetryCompatibility

universe u

variable (K : Type u) [CommRing K] (q : ℕ)

/-! ## From a constant address on the zero leg to constant letters -/

/-- **A fine word whose zero-leg address word is constant has every letter trivial on that leg.**
The fine-power analogue of the committed
`positiveSupportWord_letter_eq_zero_of_address_eq_const`, which is stated one level down, at the
Coppersmith--Winograd base alphabet. -/
theorem dwz63_finePower_letter_eq_const_of_address (zero : Leg) (n : ℕ)
    (w : PositiveWord ((cwPartitionedTensor K q).positivePower 1).support n)
    (hzero : positiveSupportWordBlockAddress
        ((cwPartitionedTensor K q).positivePower 1).support n w zero =
      positiveWordConst (positiveWordConst CWBlock.zero 1) n)
    (position : Fin (n + 1)) :
    (positiveWordEquiv ((cwPartitionedTensor K q).positivePower 1).support n w position).1 zero =
      positiveWordConst CWBlock.zero 1 := by
  have h : positiveWordEquiv (PositiveWord CWBlock 1) n
      (positiveSupportWordBlockAddress
        ((cwPartitionedTensor K q).positivePower 1).support n w zero) position =
      (positiveWordEquiv ((cwPartitionedTensor K q).positivePower 1).support n w position).1
        zero :=
    congrFun
      (positiveWordEquiv_positiveSupportWordBlockAddress_recursive
        ((cwPartitionedTensor K q).positivePower 1).support n w zero) position
  rw [← h, hzero]
  simp

/-! ## Injectivity on a zero-coordinate fibre, at either live leg -/

/-- **A supported fine letter that is trivial on `zero` is pinned by its label at `live`.**

The hypothesis is the letter-level determination at the Coppersmith--Winograd alphabet; both live
legs satisfy it (`cwSupported_eq_of_zero_of_firstLiveLeg_eq`,
`cwSupported_eq_of_zero_of_secondLiveLeg_eq`), which is why this is stated once at a general
`live` rather than twice. -/
theorem dwz63_fineLetter_eq_of_zero_of_liveLeg_eq (zero live : Leg)
    (hbase : ∀ s ∈ cwBlockSupport, ∀ t ∈ cwBlockSupport,
      s zero = CWBlock.zero → t zero = CWBlock.zero → s live = t live → s = t)
    (s t : ((cwPartitionedTensor K q).positivePower 1).support)
    (hs : s.1 zero = positiveWordConst CWBlock.zero 1)
    (ht : t.1 zero = positiveWordConst CWBlock.zero 1)
    (h : s.1 live = t.1 live) :
    s = t := by
  obtain ⟨ws, hws⟩ :=
    (cwPartitionedTensor K q).exists_positiveSupportWord_of_mem_positivePower_support 1 s.2
  obtain ⟨wt, hwt⟩ :=
    (cwPartitionedTensor K q).exists_positiveSupportWord_of_mem_positivePower_support 1 t.2
  refine Subtype.ext ?_
  rw [← hws, ← hwt]
  refine congrArg (positiveSupportWordBlockAddress (cwPartitionedTensor K q).support 1) ?_
  refine positiveSupportWord_injective_of_letterwise cwBlockSupport live 1
    (fun u ↦ u.1 zero = CWBlock.zero)
    (fun u v hu hv huv ↦ Subtype.ext (hbase u.1 u.2 v.1 v.2 hu hv huv)) ws wt ?_ ?_ ?_
  · refine fun position ↦ positiveSupportWord_letter_eq_zero_of_address_eq_const zero ws ?_
      position
    rw [show positiveSupportWordBlockAddress cwBlockSupport 1 ws zero = s.1 zero from
      congrFun hws zero]
    exact hs
  · refine fun position ↦ positiveSupportWord_letter_eq_zero_of_address_eq_const zero wt ?_
      position
    rw [show positiveSupportWordBlockAddress cwBlockSupport 1 wt zero = t.1 zero from
      congrFun hwt zero]
    exact ht
  · rw [show positiveSupportWordBlockAddress cwBlockSupport 1 ws live = s.1 live from
      congrFun hws live,
    show positiveSupportWordBlockAddress cwBlockSupport 1 wt live = t.1 live from
      congrFun hwt live]
    exact h

/-- **`hx` and `hy` at the address level.**  On any set of supported addresses of the fine positive
power that are trivial on the zero leg, the label at either live leg is injective. -/
theorem dwz63_finePower_injOn_liveLeg (zero live : Leg)
    (hbase : ∀ s ∈ cwBlockSupport, ∀ t ∈ cwBlockSupport,
      s zero = CWBlock.zero → t zero = CWBlock.zero → s live = t live → s = t)
    (n : ℕ)
    (S : Finset (BlockAddress (fun _ : Leg ↦ PositiveWord (PositiveWord CWBlock 1) n)))
    (hmem : ∀ s ∈ S, s ∈ (((cwPartitionedTensor K q).positivePower 1).positivePower
        n).support)
    (hzero : ∀ s ∈ S, s zero = positiveWordConst (positiveWordConst CWBlock.zero 1) n) :
    Set.InjOn (fun s ↦ s live)
      (S : Set (BlockAddress (fun _ : Leg ↦ PositiveWord (PositiveWord CWBlock 1) n))) := by
  intro s hs t ht hlive
  obtain ⟨ws, hws⟩ :=
    ((cwPartitionedTensor K q).positivePower
        1).exists_positiveSupportWord_of_mem_positivePower_support
      n (hmem s (Finset.mem_coe.mp hs))
  obtain ⟨wt, hwt⟩ :=
    ((cwPartitionedTensor K q).positivePower
        1).exists_positiveSupportWord_of_mem_positivePower_support
      n (hmem t (Finset.mem_coe.mp ht))
  rw [← hws, ← hwt]
  refine congrArg
    (positiveSupportWordBlockAddress ((cwPartitionedTensor K q).positivePower 1).support n) ?_
  refine positiveSupportWord_injective_of_letterwise
    ((cwPartitionedTensor K q).positivePower 1).support live n
    (fun u ↦ u.1 zero = positiveWordConst CWBlock.zero 1)
    (fun u v hu hv huv ↦
      dwz63_fineLetter_eq_of_zero_of_liveLeg_eq K q zero live hbase u v hu hv huv)
    ws wt ?_ ?_ ?_
  · refine dwz63_finePower_letter_eq_const_of_address K q zero n ws ?_
    rw [hws]
    exact hzero s (Finset.mem_coe.mp hs)
  · refine dwz63_finePower_letter_eq_const_of_address K q zero n wt ?_
    rw [hwt]
    exact hzero t (Finset.mem_coe.mp ht)
  · rw [hws, hwt]
    exact hlive

/-! ## The shared-fibre datum of one cell -/

/-- **The coherent shared-fibre datum of one zero-coordinate cell.**

Every field is supplied by `dwz63FineCellRotatedCoherent`, whose payload is a subtype carrying the
coherence: the certificate and the proof that it uses `dwz63FineCellRotatedCanonicalZMap` on the
shared leg come out of *one* `Classical.choice`, which is what makes `z_coherent` provable at
all. -/
noncomputable def dwz63FineCellSharedData (zero : Leg) (n k : ℕ)
    (keep : ∀ _c : Leg, PositiveWord (PositiveWord CWBlock 1) n → Prop)
    [∀ c a, Decidable (keep c a)]
    (hzero : ∀ s ∈ ((((cwPartitionedTensor K q).positivePower 1).positivePower n).select
        keep).support,
      s zero = positiveWordConst (positiveWordConst CWBlock.zero 1) n)
    (hones : ∀ s ∈ ((((cwPartitionedTensor K q).positivePower 1).positivePower n).select
        keep).support,
      dwz63CellOnes zero n s = k) :
    CTensor.PermutedSharedOneSliceFiberData
      ((((cwPartitionedTensor K q).positivePower 1).positivePower n).select keep)
      (zeroOrientation zero)
      (positiveWordConst (positiveWordConst CWBlock.zero 1) n)
      (q ^ k) where
  certificate := fun address ↦
    (dwz63FineCellRotatedCoherent K q zero n k address.1
      ((PartitionedTensor.mem_select_support _ _ _).mp address.2).1
      (hzero address.1 address.2) (hones address.1 address.2)).1
  zMap := dwz63FineCellRotatedCanonicalZMap K q zero n
  z_coherent := fun address ↦
    (dwz63FineCellRotatedCoherent K q zero n k address.1
      ((PartitionedTensor.mem_select_support _ _ _).mp address.2).1
      (hzero address.1 address.2) (hones address.1 address.2)).2

/-! ## The fusion -/

/-- **Exact fusion of one zero-coordinate cell of the fine leaf.**

The whole selected fibre --- not one representative --- restricts onto
`⟨1, |fibre| * q ^ k, 1⟩`, with no loss factor and no cardinality estimate.  This is the
`[duan2023faster]` section 6.3 statement `V(T_{i,j,k}, alphatilde)` at the level of exact
restrictions: the cardinality of the `alphatilde`-typical fibre is the multinomial that the value
formula's entropy term is the rate of, and `q ^ k` is its `q`-power factor.

At `keep := segmentedLocalizedKeep …` the selection is the one-segment localized splitting power
of
`Examples/DuanWuZhouLevelTwoFineCellPowerSupport.lean` verbatim; at a further `ones = k` cut it is
the uniform sub-class that the `(2,2,0)` pigeonhole
(`ZeroCoordinateMerge.exists_uniform_fibre_mergedDimension_le`) selects. -/
theorem dwz63_fineCellPower_restricts_matrixMultiplication (zero : Leg) (n k : ℕ)
    (keep : ∀ _c : Leg, PositiveWord (PositiveWord CWBlock 1) n → Prop)
    [∀ c a, Decidable (keep c a)]
    (hzero : ∀ s ∈ ((((cwPartitionedTensor K q).positivePower 1).positivePower n).select
        keep).support,
      s zero = positiveWordConst (positiveWordConst CWBlock.zero 1) n)
    (hones : ∀ s ∈ ((((cwPartitionedTensor K q).positivePower 1).positivePower n).select
        keep).support,
      dwz63CellOnes zero n s = k) :
    Restricts
      (Tensor.permute (zeroOrientation zero)
        ((((cwPartitionedTensor K q).positivePower 1).positivePower n).select keep).realize)
      (matrixMultiplication (K := K) 1
        (((((cwPartitionedTensor K q).positivePower 1).positivePower n).select keep).support.card *
          q ^ k) 1) := by
  classical
  have hmem : ∀ s ∈ ((((cwPartitionedTensor K q).positivePower 1).positivePower n).select
      keep).support,
      s ∈ (((cwPartitionedTensor K q).positivePower 1).positivePower n).support :=
    fun s hs ↦ ((PartitionedTensor.mem_select_support _ _ _).mp hs).1
  refine
    (dwz63FineCellSharedData K q zero n k keep hzero
      hones).restricts_permute_oneSliceMatrixMultiplication
    ?_ ?_ ?_
  · rw [zeroOrientation_symm_X]
    exact dwz63_finePower_injOn_liveLeg K q zero (firstLiveLeg zero)
      (cwSupported_eq_of_zero_of_firstLiveLeg_eq zero) n _ hmem hzero
  · rw [zeroOrientation_symm_Y]
    exact dwz63_finePower_injOn_liveLeg K q zero (secondLiveLeg zero)
      (cwSupported_eq_of_zero_of_secondLiveLeg_eq zero) n _ hmem hzero
  · rw [zeroOrientation_symm_Z]
    exact hzero

end AlgebraicComplexity.Examples
