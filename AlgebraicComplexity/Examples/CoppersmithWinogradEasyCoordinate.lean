/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/
import AlgebraicComplexity.Analysis.BehrendRate
import AlgebraicComplexity.Examples.CoppersmithWinogradEasyHashing
import AlgebraicComplexity.Examples.GeneralizedCoppersmithWinograd
import AlgebraicComplexity.MatrixMultiplication.CoordinateBlockCertificate
import AlgebraicComplexity.MatrixMultiplication.IndependenceBarrier
import AlgebraicComplexity.Tensor.CoordinateBlockWord
import AlgebraicComplexity.MatrixMultiplication.IndependentDiagonal

/-!
# The coordinate easy Coppersmith--Winograd extraction

Layer 4 (`AlgebraicComplexity/Examples/`).  This module is milestones **M5** and **M6** of
`BARRIER_FRAMEWORK.md`, the one large step of the plan for
[AlmanVassilevskaWilliams2018, Theorem 7.3] and the limit that follows it.

## Why a coordinate shadow is needed

The independence number `Tensor.independenceNumber` of the barrier program of
[AlmanVassilevskaWilliams2018] is a function of a *coefficient table*, not of an abstract tensor: it
is not invariant under a legwise change of basis.  Every extraction of this repository is, by
contrast, a `Tensor.Restricts` between abstract tensors, so none of them says anything about `Ī`.
The barrier argument therefore needs a *coordinate shadow* of the classical laser extraction: a
statement about the coefficient table `gcwTable K μ σ` itself.

This file builds that shadow for the three-constituent "easy" construction of
[CoppersmithWinograd1990, §6], whose abstract extraction lives in
`Examples/CoppersmithWinogradEasyHashing.lean`.  **No combinatorics is redone.**  The word family,
the legal hashing targets, the isolated addresses, the good seed, the competitor quarter bound, the
Behrend set and the prime modulus are consumed unchanged from that file
(`easyEqualTypeWords`, `easyEqualTypeTargets`,
`ProgressionHash.LegalTriple.exists_seed_many_legwiseIsolatedTargets`,
`easyEqualType_competitorQuarter_of_fieldCard`, `easyCopies_lower_of_hashingCount`,
`exists_threeAPFree_zmod_half`, `Nat.exists_prime_lt_and_le_two_mul`).  Only the two *tensor-level*
steps are replaced by their coordinate twins from `Tensor/CoordinateBlockWord.lean` (milestone M3)
and `MatrixMultiplication/IndependentDiagonal.lean` (milestone M4).

Since the six-constituent first-power shadow of
`Examples/CoppersmithWinogradFirstPowerCoordinate.lean` repeats the same two steps verbatim, they
are factored out into the paper-independent
`MatrixMultiplication/CoordinateBlockCertificate.lean`: an
`AlgebraicComplexity.BlockMMIndexing` records a block labelling together with legwise coordinate
bijections identifying each block with a matrix-multiplication shape, and
`AlgebraicComplexity.BlockMMIndexing.exists_zeroOut_eq_extend` turns a legwise-injective family of
selected block words into the zeroing out.  The easy construction supplies that data as
`gcwEasyIndexing`; everything in the `Constituent` section below is the generic machinery
specialized to it, and the extraction theorem is the generic assembly fed with the easy hashing
data.

## Main definitions

* `gcwEasyTable K μ σ`: **the easy generalized Coppersmith--Winograd table**, the coordinate table
  of `CW_q^σ` with the coordinate `q + 1` zeroed out on every leg.  What survives is exactly the
  three middle families `∑ x_i y_{σ(i)} z_0 + ∑ x_i y_0 z_i + ∑ x_0 y_i z_i`.
* `easyBlockLetter`, `easyZeroLeg`, `easyBlockWord`, `easyZeroLegWord`: the three easy block
  addresses `cw011`, `cw101`, `cw110` indexed by the leg carrying the `zero` block, and the
  corresponding description of a block word triple by a single word `Fin N → Leg`.
* `easyDimM`, `easyDimN`, `easyDimP`: the matrix-multiplication shapes `⟨1,1,q⟩`, `⟨q,1,1⟩`,
  `⟨1,q,1⟩` of the three easy constituents, read at that leg.
* `gcwEasyIndexEquiv`: the legwise bijection between the coordinates of one easy constituent and
  the coordinates of its matrix-multiplication shape.  These are `cw011Index`, `cw101Index` and
  `cw110Index` of `Examples/CoppersmithWinograd.lean`, with the middle block indexed by `μ`.
* `gcwEasyIndexing`: the previous four items packaged as an
  `AlgebraicComplexity.BlockMMIndexing`, the input of the shared coordinate block certificate.
* `gcwEasyWordIndex`, `gcwEasyConstituentIndex`: the same, positionwise along a word of blocks and
  then compressed by the mixed-radix bijection `mmWordIndexEquiv` of milestone M4; both are the
  corresponding operations of `AlgebraicComplexity.BlockMMIndexing` at `gcwEasyIndexing`.

## Main results

* `gcwTable_gcwEasyIndexEquiv` and `gcwEasyTable_gcwEasyIndexEquiv`: **the letter identity**, for
  the full table `CW_q^σ` and for its easy zeroing out.  On one easy block the table, read along
  the listed coordinates, is the coefficient table of the block's matrix-multiplication shape.
  The `gcwTable` form is what the six-constituent first-power shadow reuses.
* `coordinatePower_gcwEasyConstituentIndex`: **the constituent identity.**  On a whole word of easy
  blocks with `k` blocks of each kind the `3k`-th Kronecker power of `gcwEasyTable`, read along the
  compressed coordinates, is `mmCoefficients K (q^k) (q^k) (q^k)`.
* `exists_easyCoordinate_zeroOut_eq_extend`: **the extraction at a fixed seed**, the coordinate twin
  of `easyPower_restricts_legwiseIsolatedSquareDirectSum`.
* `exists_easyCoordinate_squareExtraction`: **the milestone.**  For every `k ≥ 1` there are
  `M ≤ 24·4^k` and `copies` with `27^k · roth(M/2) ≤ 6·k²·M²·copies` such that
  `coordinatePower (gcwEasyTable K μ σ) (3k)` zeroes out to `copies` disjoint copies of
  `⟨q^k, q^k, q^k⟩`.
* `coordinateGalacticCertificate_gcwEasyTable`: the same, packaged by milestone M2
  (`coordinateGalacticCertificate_of_zeroOut`) as a
  `AlgebraicComplexity.CoordinateGalacticCertificate`.
* `easyCW_independence_base_inequality`: **milestone M6**, the `k → ∞` limit of the previous item:
  `(27/4)·q² ≤ Ī(CW_q^σ)³` for every `q ≥ 1`.  This is the whole content of
  [AlmanVassilevskaWilliams2018, Theorem 7.3]; the passage from it to AVW's displayed
  `(q+2)^{2/f(q)} ≤ Ī(CW_q^σ)` is pure real arithmetic and lives in
  `Examples/GeneralizedCoppersmithWinogradIndependenceLower.lean`.

## The permutation `σ` costs nothing

`CW_q^σ` differs from `CW_q` only inside the constituent `T_{110} = ∑_i x_i y_{σ(i)} z_0`.  The
extraction below zeroes out *blocks*, and the three easy blocks use pairwise disjoint sets of
variables on each leg; within the `cw110` block the permutation is a relabelling of the `Y`
variables (`gcwMiddleTwist`), which is absorbed into the constituent's index bijection
`gcwEasyIndexEquiv Leg.Z Leg.Y`.  Since a block labelling is unchanged by a permutation of the
variables inside a block, no block word, no hashing datum and no count is affected; compare
`Tensor.coordinateBlockZeroOut_coordinateRelabel`, which is the same observation stated for a
global legwise relabelling.  (Note that `σ` is *not* a relabelling of the whole table: it moves the
`(middle, middle, zero)` support triples while fixing the `(zero, middle, middle)` ones.)

## Hypotheses

The coefficient ring carries only `[CommSemiring K]`.  The field-size condition `12·4^k ≤ |R|` of
`easyEqualType_competitorQuarter_of_fieldCard` is a statement about the *hashing* field, here
`ZMod M` for a prime `M` supplied by Bertrand's postulate, and not about `K`; the extraction is a
zeroing out, so no subtraction, division or interpolation is used.

The middle index type `μ` is taken in `Type 0`.  This is forced by
`Tensor/CoordinateBlockWord.lean`, whose variable alphabet `κ` and block alphabet `A` live in the
same universe, and the block alphabet here is `CWBlock : Type`.  The intended instance,
`μ = Fin q` of [AlmanVassilevskaWilliams2018, Definition 3.1], is in `Type 0`; a `ULift` block
alphabet in M3 would remove the restriction.

## Position in the library

Layer 4.  It imports `Examples/CoppersmithWinogradEasyHashing.lean` (the unchanged combinatorics),
`Examples/GeneralizedCoppersmithWinogradBarrier.lean` (for `gcwTable`, `GenCWSupport` and the
coordinate galactic certificate of milestone M2), `Tensor/CoordinateBlockWord.lean` (M3),
`MatrixMultiplication/IndependentDiagonal.lean` (M4) and
`MatrixMultiplication/CoordinateBlockCertificate.lean` (the shared M3/M4 assembly).  Nothing here
is imported by a lower layer.

## References

* [AlmanVassilevskaWilliams2018] J. Alman and V. Vassilevska Williams, *Limits on all known (and
  some unknown) approaches to matrix multiplication*, arXiv:1810.08671; Definition 3.1,
  Lemma 4.4, Theorem 7.3.
* [CoppersmithWinograd1990] D. Coppersmith and S. Winograd, *Matrix multiplication via arithmetic
  progressions*, J. Symbolic Comput. 9 (1990); §6, the three-constituent construction.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor

universe u

section EasyTable

variable {K : Type u} [CommSemiring K] {μ : Type} [Fintype μ] [DecidableEq μ]

/-- **The easy generalized Coppersmith--Winograd table.**  Zeroing the coordinate `q + 1` out on
every leg of `gcwTable K μ σ` deletes the three corner terms of
[AlmanVassilevskaWilliams2018, Definition 3.1] and leaves exactly the three middle families

```text
∑_i x_i y_{σ(i)} z_0 + ∑_i x_i y_0 z_i + ∑_i x_0 y_i z_i,
```

the coefficient table of the easy tensor of [CoppersmithWinograd1990, §6]. -/
noncomputable def gcwEasyTable (K : Type u) [CommSemiring K] (μ : Type) [Fintype μ]
    [DecidableEq μ] (σ : Equiv.Perm μ) : (∀ c, GenCWIndexFamily μ c) → K :=
  coordinateZeroOut (gcwTable K μ σ) fun _ ↦ Finset.univ.erase GenCWIndex.last

/-- Off the easy support the table vanishes: a coordinate triple whose coarse block address is not
one of `cw011`, `cw101`, `cw110` has coefficient `0`. -/
theorem gcwEasyTable_eq_zero_of_notMem_easyBlockSupport (σ : Equiv.Perm μ)
    {s : ∀ c, GenCWIndexFamily μ c}
    (h : (fun c ↦ gcwBlockLabel μ (s c)) ∉ easyBlockSupport) :
    gcwEasyTable K μ σ s = 0 := by
  classical
  by_cases hlast : ∀ c, s c ∈ Finset.univ.erase (GenCWIndex.last : GenCWIndex μ)
  · rw [gcwEasyTable, coordinateZeroOut_of_mem hlast, gcwTable_apply, if_neg]
    intro hsupp
    apply h
    rcases hsupp with ⟨hx, hy, hz⟩ | ⟨hx, hy, hz⟩ | ⟨hx, hy, hz⟩ |
      ⟨i, hx, hy, hz⟩ | ⟨i, hx, hy, hz⟩ | ⟨i, hx, hy, hz⟩
    · exact absurd (Finset.mem_erase.mp (hlast .Z)).1 (by simp [hz])
    · exact absurd (Finset.mem_erase.mp (hlast .Y)).1 (by simp [hy])
    · exact absurd (Finset.mem_erase.mp (hlast .X)).1 (by simp [hx])
    · have : (fun c ↦ gcwBlockLabel μ (s c)) = cw110 := by
        funext c; cases c <;> simp [hx, hy, hz]
      simp [this, easyBlockSupport]
    · have : (fun c ↦ gcwBlockLabel μ (s c)) = cw101 := by
        funext c; cases c <;> simp [hx, hy, hz]
      simp [this, easyBlockSupport]
    · have : (fun c ↦ gcwBlockLabel μ (s c)) = cw011 := by
        funext c; cases c <;> simp [hx, hy, hz]
      simp [this, easyBlockSupport]
  · exact coordinateZeroOut_of_notMem hlast

/-! ### The three easy constituents, indexed by the leg carrying the `zero` block

Every address of `easyBlockSupport` has the `zero` block on exactly one leg and the `middle` block
on the other two, so the three constituents of the easy tensor are indexed by that leg:
`easyBlockLetter .X = cw011`, `easyBlockLetter .Y = cw101` and `easyBlockLetter .Z = cw110`.  Their
matrix-multiplication shapes `⟨1,1,q⟩`, `⟨q,1,1⟩` and `⟨1,q,1⟩` are `easyDimM`/`easyDimN`/`easyDimP`
read at the same leg. -/

/-- The easy block address whose `zero` block sits on leg `z`. -/
def easyBlockLetter : Leg → Leg → CWBlock
  | .X, .X => .zero
  | .X, .Y => .middle
  | .X, .Z => .middle
  | .Y, .X => .middle
  | .Y, .Y => .zero
  | .Y, .Z => .middle
  | .Z, .X => .middle
  | .Z, .Y => .middle
  | .Z, .Z => .zero

/-- The three addresses `easyBlockLetter z` are the easy support. -/
theorem easyBlockLetter_mem_easyBlockSupport (z : Leg) :
    easyBlockLetter z ∈ easyBlockSupport := by
  cases z <;> decide

/-- The leg carrying the `zero` block of an easy block address. -/
def easyZeroLeg (a : CWBlockAddress) : Leg :=
  if a .X = .zero then .X else if a .Y = .zero then .Y else .Z

/-- Reading off the `zero` leg recovers the block address. -/
theorem easyBlockLetter_easyZeroLeg {a : CWBlockAddress} (ha : a ∈ easyBlockSupport) :
    easyBlockLetter (easyZeroLeg a) = a := by
  fin_cases ha <;> decide

/-- First matrix-multiplication dimension of the easy constituent with `zero` block on leg `z`. -/
abbrev easyDimM (q : ℕ) : Leg → ℕ
  | .X => 1
  | .Y => q
  | .Z => 1

/-- Second matrix-multiplication dimension of the easy constituent with `zero` block on leg `z`. -/
abbrev easyDimN (q : ℕ) : Leg → ℕ
  | .X => 1
  | .Y => 1
  | .Z => q

/-- Third matrix-multiplication dimension of the easy constituent with `zero` block on leg `z`. -/
abbrev easyDimP (q : ℕ) : Leg → ℕ
  | .X => q
  | .Y => 1
  | .Z => 1

/-! ### The variables of one block

`gcwZeroFiberFin` and `gcwMiddleFiberEquiv` list the variables carrying a fixed block label: one
variable above `zero` and `q` variables above `middle`. -/

/-- The unique variable carrying the block label `zero`. -/
noncomputable def gcwZeroFiberFin (μ : Type) :
    Fin 1 ≃ {x : GenCWIndex μ // gcwBlockLabel μ x = CWBlock.zero} :=
  Equiv.ofBijective (fun _ ↦ ⟨.zero, rfl⟩)
    ⟨fun a b _ ↦ Subsingleton.elim a b, by
      rintro ⟨x, hx⟩
      cases x with
      | zero => exact ⟨0, rfl⟩
      | middle i => simp at hx
      | last => simp at hx⟩

/-- The `q` variables carrying the block label `middle`. -/
noncomputable def gcwMiddleFiberEquiv (μ : Type) [Fintype μ] :
    Fin (Fintype.card μ) ≃ {x : GenCWIndex μ // gcwBlockLabel μ x = CWBlock.middle} :=
  (Fintype.equivFin μ).symm.trans
    (Equiv.ofBijective (fun i : μ ↦ ⟨.middle i, rfl⟩)
      ⟨fun a b h ↦ by simpa using congrArg Subtype.val h, by
        rintro ⟨x, hx⟩
        cases x with
        | zero => simp at hx
        | middle i => exact ⟨i, rfl⟩
        | last => simp at hx⟩)

/-- The unique variable carrying the block label `last`, i.e. the coordinate `q + 1` of
[AlmanVassilevskaWilliams2018, Definition 3.1].  It is not used by the easy extraction, which
deletes that coordinate; it is listed here beside `gcwZeroFiberFin` and `gcwMiddleFiberEquiv` so
that the three block fibers of `CW_q^σ` are available together, as the six-constituent
first-power extraction of `Examples/CoppersmithWinogradFirstPowerCoordinate.lean` needs. -/
noncomputable def gcwLastFiberFin (μ : Type) :
    Fin 1 ≃ {x : GenCWIndex μ // gcwBlockLabel μ x = CWBlock.last} :=
  Equiv.ofBijective (fun _ ↦ ⟨.last, rfl⟩)
    ⟨fun a b _ ↦ Subsingleton.elim a b, by
      rintro ⟨x, hx⟩
      cases x with
      | zero => simp at hx
      | middle i => simp at hx
      | last => exact ⟨0, rfl⟩⟩

omit [DecidableEq μ] in
/-- The variable listed by `gcwMiddleFiberEquiv` is the middle coordinate it names. -/
@[simp] theorem gcwMiddleFiberEquiv_val (j : Fin (Fintype.card μ)) :
    ((gcwMiddleFiberEquiv μ j : {x : GenCWIndex μ // gcwBlockLabel μ x = CWBlock.middle}) : _)
      = GenCWIndex.middle ((Fintype.equivFin μ).symm j) := rfl

/-- The permutation `σ` acting on the variables above the `middle` block.  It is a relabelling of
one block only, which is why the permutation of
[AlmanVassilevskaWilliams2018, Definition 3.1] costs nothing in the extraction below. -/
noncomputable def gcwMiddleTwist (σ : Equiv.Perm μ) :
    {x : GenCWIndex μ // gcwBlockLabel μ x = CWBlock.middle} ≃
      {x : GenCWIndex μ // gcwBlockLabel μ x = CWBlock.middle} :=
  Equiv.subtypeEquiv (GenCWIndex.congr σ) (by
    rintro (_ | i | _) <;> simp [gcwBlockLabel])

/-- **The coordinates of one easy constituent.**  For the block address `easyBlockLetter z` the
variables of leg `c` of the matrix-multiplication tensor
`⟨easyDimM q z, easyDimN q z, easyDimP q z⟩` are in bijection with the variables of leg `c` of
`CW_q^σ` carrying the block label `easyBlockLetter z c`.  These are the maps `cw011Index`,
`cw101Index`, `cw110Index` of `Examples/CoppersmithWinograd.lean`, with the middle block indexed by
`μ` and with `σ` inserted on the `Y` leg of the `(1,1,0)` constituent. -/
noncomputable def gcwEasyIndexEquiv (σ : Equiv.Perm μ) :
    (z c : Leg) →
      MMIndex (easyDimM (Fintype.card μ) z) (easyDimN (Fintype.card μ) z)
          (easyDimP (Fintype.card μ) z) c ≃
        {x : GenCWIndex μ // gcwBlockLabel μ x = easyBlockLetter z c}
  | .X, .X => (Equiv.prodUnique (Fin 1) (Fin 1)).trans (gcwZeroFiberFin μ)
  | .X, .Y => (Equiv.uniqueProd (Fin (Fintype.card μ)) (Fin 1)).trans (gcwMiddleFiberEquiv μ)
  | .X, .Z => (Equiv.prodUnique (Fin (Fintype.card μ)) (Fin 1)).trans (gcwMiddleFiberEquiv μ)
  | .Y, .X => (Equiv.prodUnique (Fin (Fintype.card μ)) (Fin 1)).trans (gcwMiddleFiberEquiv μ)
  | .Y, .Y => (Equiv.prodUnique (Fin 1) (Fin 1)).trans (gcwZeroFiberFin μ)
  | .Y, .Z => (Equiv.uniqueProd (Fin (Fintype.card μ)) (Fin 1)).trans (gcwMiddleFiberEquiv μ)
  | .Z, .X => (Equiv.uniqueProd (Fin (Fintype.card μ)) (Fin 1)).trans (gcwMiddleFiberEquiv μ)
  | .Z, .Y => ((Equiv.prodUnique (Fin (Fintype.card μ)) (Fin 1)).trans
      (gcwMiddleFiberEquiv μ)).trans (gcwMiddleTwist σ)
  | .Z, .Z => (Equiv.prodUnique (Fin 1) (Fin 1)).trans (gcwZeroFiberFin μ)

omit [DecidableEq μ] in
/-- A variable of an easy constituent carries the block label prescribed by its block address. -/
@[simp] theorem gcwBlockLabel_gcwEasyIndexEquiv (σ : Equiv.Perm μ) (z c : Leg)
    (x : MMIndex (easyDimM (Fintype.card μ) z) (easyDimN (Fintype.card μ) z)
      (easyDimP (Fintype.card μ) z) c) :
    gcwBlockLabel μ (gcwEasyIndexEquiv σ z c x : GenCWIndex μ) = easyBlockLetter z c :=
  (gcwEasyIndexEquiv σ z c x).2

/-- Only the `q + 1` coordinate is deleted by `gcwEasyTable`; on the surviving coordinates the
easy table is the generalized Coppersmith--Winograd table. -/
theorem gcwEasyTable_of_ne_last (σ : Equiv.Perm μ) {s : ∀ c, GenCWIndexFamily μ c}
    (h : ∀ c, s c ≠ GenCWIndex.last) :
    gcwEasyTable K μ σ s = if GenCWSupport σ s then 1 else 0 := by
  classical
  rw [gcwEasyTable,
    coordinateZeroOut_of_mem fun c ↦ Finset.mem_erase.mpr ⟨h c, Finset.mem_univ _⟩,
    gcwTable_apply]

/-! ### The support of `CW_q^σ` on the three easy blocks -/

omit [Fintype μ] [DecidableEq μ] in
/-- On the block `cw011` the support condition of [AlmanVassilevskaWilliams2018, Definition 3.1]
is the equality of the two middle coordinates. -/
theorem genCWSupport_zero_middle_middle (σ : Equiv.Perm μ) (a b : μ) :
    GenCWSupport σ (ofLegs (V := GenCWIndexFamily μ) GenCWIndex.zero (.middle a) (.middle b))
      ↔ a = b := by
  simp [GenCWSupport, eq_comm]

omit [Fintype μ] [DecidableEq μ] in
/-- On the block `cw101` the support condition is the equality of the two middle coordinates. -/
theorem genCWSupport_middle_zero_middle (σ : Equiv.Perm μ) (a b : μ) :
    GenCWSupport σ (ofLegs (V := GenCWIndexFamily μ) (.middle a) GenCWIndex.zero (.middle b))
      ↔ a = b := by
  simp [GenCWSupport, eq_comm]

omit [Fintype μ] [DecidableEq μ] in
/-- On the block `cw110` the support condition is `σ a = b`: this is the only place where the
permutation of [AlmanVassilevskaWilliams2018, Definition 3.1] is visible. -/
theorem genCWSupport_middle_middle_zero (σ : Equiv.Perm μ) (a b : μ) :
    GenCWSupport σ (ofLegs (V := GenCWIndexFamily μ) (.middle a) (.middle b) GenCWIndex.zero)
      ↔ σ a = b := by
  simp [GenCWSupport, eq_comm]

omit [DecidableEq μ] in
/-- The coordinates listed by `gcwEasyIndexEquiv` avoid the deleted coordinate `q + 1`: an easy
block address never carries the block label `last`. -/
theorem gcwEasyIndexEquiv_ne_last (σ : Equiv.Perm μ) (z c : Leg)
    (x : MMIndex (easyDimM (Fintype.card μ) z) (easyDimN (Fintype.card μ) z)
      (easyDimP (Fintype.card μ) z) c) :
    (gcwEasyIndexEquiv σ z c x : GenCWIndex μ) ≠ GenCWIndex.last := by
  intro hc
  have hlabel := gcwBlockLabel_gcwEasyIndexEquiv σ z c x
  rw [hc, gcwBlockLabel_last] at hlabel
  cases z <;> cases c <;> simp [easyBlockLetter] at hlabel

omit [DecidableEq μ] in
/-- **The support condition on an easy block is matrix-multiplication compatibility.**  On each of
the three blocks the support condition of [AlmanVassilevskaWilliams2018, Definition 3.1] is a
single equation between the two middle coordinates, and `MMCompatible` is the same equation once
the two `Fin 1` components are discarded; the `σ` of the `cw110` block is absorbed by
`gcwMiddleTwist` on the `Y` leg. -/
theorem genCWSupport_gcwEasyIndexEquiv (σ : Equiv.Perm μ) (z : Leg)
    (u : ∀ c, MMIndex (easyDimM (Fintype.card μ) z) (easyDimN (Fintype.card μ) z)
      (easyDimP (Fintype.card μ) z) c) :
    GenCWSupport σ (fun c ↦ (gcwEasyIndexEquiv σ z c (u c) : GenCWIndex μ))
      ↔ MMCompatible u := by
  classical
  have hiff : GenCWSupport σ (fun c ↦ (gcwEasyIndexEquiv σ z c (u c) : GenCWIndex μ))
      ↔ MMCompatible u := by
    cases z with
    | X =>
        have hs : (fun c ↦ (gcwEasyIndexEquiv σ Leg.X c (u c) : GenCWIndex μ))
            = ofLegs (V := GenCWIndexFamily μ) GenCWIndex.zero
                (.middle ((Fintype.equivFin μ).symm (u .Y).2))
                (.middle ((Fintype.equivFin μ).symm (u .Z).1)) := by
          funext c; cases c <;> rfl
        rw [hs, genCWSupport_zero_middle_middle]
        exact ⟨fun h ↦ ⟨Subsingleton.elim _ _, (Fintype.equivFin μ).symm.injective h,
            Subsingleton.elim _ _⟩,
          fun h ↦ congrArg _ h.2.1⟩
    | Y =>
        have hs : (fun c ↦ (gcwEasyIndexEquiv σ Leg.Y c (u c) : GenCWIndex μ))
            = ofLegs (V := GenCWIndexFamily μ)
                (.middle ((Fintype.equivFin μ).symm (u .X).1)) GenCWIndex.zero
                (.middle ((Fintype.equivFin μ).symm (u .Z).2)) := by
          funext c; cases c <;> rfl
        rw [hs, genCWSupport_middle_zero_middle]
        exact ⟨fun h ↦ ⟨Subsingleton.elim _ _, Subsingleton.elim _ _,
            ((Fintype.equivFin μ).symm.injective h).symm⟩,
          fun h ↦ congrArg _ h.2.2.symm⟩
    | Z =>
        have hs : (fun c ↦ (gcwEasyIndexEquiv σ Leg.Z c (u c) : GenCWIndex μ))
            = ofLegs (V := GenCWIndexFamily μ)
                (.middle ((Fintype.equivFin μ).symm (u .X).2))
                (.middle (σ ((Fintype.equivFin μ).symm (u .Y).1))) GenCWIndex.zero := by
          funext c; cases c <;> rfl
        rw [hs, genCWSupport_middle_middle_zero]
        constructor
        · intro h
          exact ⟨(Fintype.equivFin μ).symm.injective (σ.injective h), Subsingleton.elim _ _,
            Subsingleton.elim _ _⟩
        · intro h
          exact congrArg (fun i ↦ σ ((Fintype.equivFin μ).symm i)) h.1
  exact hiff

/-- **The letter identity of the easy extraction, on the full table `CW_q^σ`.**  Read along the
coordinates listed by `gcwEasyIndexEquiv`, the coefficient table of `CW_q^σ` restricted to one easy
block is exactly the coefficient table of the corresponding matrix-multiplication tensor:
`⟨1,1,q⟩` for the block `cw011`, `⟨q,1,1⟩` for `cw101` and `⟨1,q,1⟩` for `cw110`.

This is the `gcwTable` form; the easy extraction consumes the `gcwEasyTable` form
`gcwEasyTable_gcwEasyIndexEquiv` below, and the six-constituent first-power extraction of
`Examples/CoppersmithWinogradFirstPowerCoordinate.lean` consumes this one.

Proof sketch: the value of `gcwTable` is the indicator of the support of
[AlmanVassilevskaWilliams2018, Definition 3.1], and on an easy block that support condition is
matrix-multiplication compatibility (`genCWSupport_gcwEasyIndexEquiv`). -/
theorem gcwTable_gcwEasyIndexEquiv (σ : Equiv.Perm μ) (z : Leg)
    (u : ∀ c, MMIndex (easyDimM (Fintype.card μ) z) (easyDimN (Fintype.card μ) z)
      (easyDimP (Fintype.card μ) z) c) :
    gcwTable K μ σ (fun c ↦ (gcwEasyIndexEquiv σ z c (u c) : GenCWIndex μ))
      = mmCoefficients K (easyDimM (Fintype.card μ) z) (easyDimN (Fintype.card μ) z)
          (easyDimP (Fintype.card μ) z) u := by
  classical
  have hiff := genCWSupport_gcwEasyIndexEquiv σ z u
  show gcwTable K μ σ _ = if MMCompatible u then 1 else 0
  rw [gcwTable_apply]
  by_cases hc : MMCompatible u
  · rw [if_pos (hiff.mpr hc), if_pos hc]
  · rw [if_neg fun h ↦ hc (hiff.mp h), if_neg hc]

/-- **The letter identity of the easy extraction.**  Read along the coordinates listed by
`gcwEasyIndexEquiv`, the coefficient table of `CW_q^σ` restricted to one easy block is exactly the
coefficient table of the corresponding matrix-multiplication tensor: `⟨1,1,q⟩` for the block
`cw011`, `⟨q,1,1⟩` for `cw101` and `⟨1,q,1⟩` for `cw110`.

Proof sketch: all listed coordinates avoid `q + 1` (`gcwEasyIndexEquiv_ne_last`), so
`gcwEasyTable` is `gcwTable` there, and `gcwTable_gcwEasyIndexEquiv` applies. -/
theorem gcwEasyTable_gcwEasyIndexEquiv (σ : Equiv.Perm μ) (z : Leg)
    (u : ∀ c, MMIndex (easyDimM (Fintype.card μ) z) (easyDimN (Fintype.card μ) z)
      (easyDimP (Fintype.card μ) z) c) :
    gcwEasyTable K μ σ (fun c ↦ (gcwEasyIndexEquiv σ z c (u c) : GenCWIndex μ))
      = mmCoefficients K (easyDimM (Fintype.card μ) z) (easyDimN (Fintype.card μ) z)
          (easyDimP (Fintype.card μ) z) u := by
  classical
  rw [gcwEasyTable_of_ne_last σ fun c ↦ gcwEasyIndexEquiv_ne_last σ z c (u c),
    ← gcwTable_apply, gcwTable_gcwEasyIndexEquiv]

/-! ### Words of easy blocks

A block word triple all of whose letters are easy block addresses is the same thing as a word
`w : Fin N → Leg` recording, at each position, the leg carrying the `zero` block
(`easyBlockWord`/`easyZeroLegWord`).  The constituent selected by such a block word is a product of
`N` matrix-multiplication tensors of the three easy shapes, that is a heterogeneous word product in
the sense of `MatrixMultiplication/IndependentDiagonal.lean`. -/

omit [Fintype μ] [DecidableEq μ] in
/-- On an easy block address the `zero` block sits on leg `c` exactly at the recorded leg. -/
theorem easyBlockLetter_eq_zero_iff (z c : Leg) :
    easyBlockLetter z c = CWBlock.zero ↔ z = c := by
  cases z <;> cases c <;> decide

/-- The block word triple determined by a word of `zero`-legs. -/
def easyBlockWord {N : ℕ} (w : Fin N → Leg) : BlockAddress fun _ : Leg ↦ Fin N → CWBlock :=
  fun c t ↦ easyBlockLetter (w t) c

/-- The word of `zero`-legs of a block word triple whose letters are easy block addresses. -/
def easyZeroLegWord {N : ℕ} (s : BlockAddress fun _ : Leg ↦ Fin N → CWBlock) : Fin N → Leg :=
  fun t ↦ easyZeroLeg fun c ↦ s c t

/-- A block word triple whose letters are easy block addresses is the block word of its
`zero`-leg word. -/
theorem easyBlockWord_easyZeroLegWord {N : ℕ}
    {s : BlockAddress fun _ : Leg ↦ Fin N → CWBlock}
    (hs : ∀ t, (fun c ↦ s c t) ∈ easyBlockSupport) :
    easyBlockWord (easyZeroLegWord s) = s := by
  funext c t
  exact congrFun (easyBlockLetter_easyZeroLeg (hs t)) c

/-- A letter of a block word is `zero` on leg `c` exactly at the positions recorded by `c`. -/
theorem easyBlockWord_eq_zero_iff {N : ℕ} (w : Fin N → Leg) (c : Leg) (t : Fin N) :
    easyBlockWord w c t = CWBlock.zero ↔ w t = c :=
  easyBlockLetter_eq_zero_iff _ _

end EasyTable

section Dimensions

/-- A product of dimensions that is `q` at one letter and `1` elsewhere is a power of `q`. -/
private theorem prod_dim_eq_pow {N : ℕ} (q : ℕ) (w : Fin N → Leg) (z : Leg) (d : Leg → ℕ)
    (hz : d z = q) (hne : ∀ y, y ≠ z → d y = 1) :
    ∏ t, d (w t) = q ^ (Finset.univ.filter fun t ↦ w t = z).card := by
  classical
  rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ (fun t ↦ w t = z)]
  have h1 : (∏ t ∈ Finset.univ.filter fun t ↦ w t = z, d (w t))
      = q ^ (Finset.univ.filter fun t ↦ w t = z).card := by
    rw [Finset.prod_congr rfl fun t ht ↦ by rw [(Finset.mem_filter.mp ht).2, hz],
      Finset.prod_const]
  have h2 : (∏ t ∈ Finset.univ.filter fun t ↦ ¬ w t = z, d (w t)) = 1 :=
    Finset.prod_eq_one fun t ht ↦ hne _ (Finset.mem_filter.mp ht).2
  rw [h1, h2, mul_one]

/-- The first dimension of a heterogeneous easy word product is `q` to the number of positions
whose `zero` block sits on the `Y` leg. -/
theorem prod_easyDimM {N : ℕ} (q : ℕ) (w : Fin N → Leg) :
    ∏ t, easyDimM q (w t) = q ^ (Finset.univ.filter fun t ↦ w t = Leg.Y).card :=
  prod_dim_eq_pow q w .Y _ rfl (by rintro (_ | _ | _) h <;> simp_all)

/-- The second dimension of a heterogeneous easy word product is `q` to the number of positions
whose `zero` block sits on the `Z` leg. -/
theorem prod_easyDimN {N : ℕ} (q : ℕ) (w : Fin N → Leg) :
    ∏ t, easyDimN q (w t) = q ^ (Finset.univ.filter fun t ↦ w t = Leg.Z).card :=
  prod_dim_eq_pow q w .Z _ rfl (by rintro (_ | _ | _) h <;> simp_all)

/-- The third dimension of a heterogeneous easy word product is `q` to the number of positions
whose `zero` block sits on the `X` leg. -/
theorem prod_easyDimP {N : ℕ} (q : ℕ) (w : Fin N → Leg) :
    ∏ t, easyDimP q (w t) = q ^ (Finset.univ.filter fun t ↦ w t = Leg.X).card :=
  prod_dim_eq_pow q w .X _ rfl (by rintro (_ | _ | _) h <;> simp_all)

end Dimensions

section Constituent

variable {K : Type u} [CommSemiring K] {μ : Type} [Fintype μ] [DecidableEq μ]

/-- **The easy block indexing of `CW_q^σ`.**  The three easy constituents indexed by the leg
carrying their `zero` block, with their block addresses, their matrix-multiplication shapes and
the legwise coordinate bijections of `gcwEasyIndexEquiv`.  This is the paper-side input of the
generic coordinate block certificate of
`MatrixMultiplication/CoordinateBlockCertificate.lean`; everything below in this section is that
generic machinery specialized here. -/
noncomputable def gcwEasyIndexing (μ : Type) [Fintype μ] [DecidableEq μ] (σ : Equiv.Perm μ) :
    BlockMMIndexing (GenCWIndexFamily μ) (fun _ : Leg ↦ CWBlock) Leg where
  label := fun _ ↦ gcwBlockLabel μ
  letter := easyBlockLetter
  dimM := easyDimM (Fintype.card μ)
  dimN := easyDimN (Fintype.card μ)
  dimP := easyDimP (Fintype.card μ)
  index := gcwEasyIndexEquiv σ

/-- The easy table is a block table for the easy indexing: this is the letter identity
`gcwEasyTable_gcwEasyIndexEquiv`. -/
theorem gcwEasyIndexing_isBlockTable (σ : Equiv.Perm μ) :
    (gcwEasyIndexing μ σ).IsBlockTable (gcwEasyTable K μ σ) :=
  fun z u ↦ gcwEasyTable_gcwEasyIndexEquiv σ z u

/-- **The coordinates of leg `c` of the easy constituent selected by a `zero`-leg word.**  Position
by position it is the letter listing `gcwEasyIndexEquiv`; it is
`AlgebraicComplexity.BlockMMIndexing.wordIndex` at the easy indexing. -/
noncomputable def gcwEasyWordIndex (σ : Equiv.Perm μ) {N : ℕ} (w : Fin N → Leg) (c : Leg)
    (v : ∀ t, MMIndex (easyDimM (Fintype.card μ) (w t)) (easyDimN (Fintype.card μ) (w t))
      (easyDimP (Fintype.card μ) (w t)) c) : Fin N → GenCWIndex μ :=
  (gcwEasyIndexing μ σ).wordIndex w c v

/-- The listed coordinates of a constituent form the prescribed block word. -/
theorem coordinateBlockLegWord_gcwEasyWordIndex (σ : Equiv.Perm μ) {N : ℕ} (w : Fin N → Leg)
    (c : Leg) (v : ∀ t, MMIndex (easyDimM (Fintype.card μ) (w t))
      (easyDimN (Fintype.card μ) (w t)) (easyDimP (Fintype.card μ) (w t)) c) :
    coordinateBlockLegWord (κ := GenCWIndexFamily μ) (fun _ ↦ gcwBlockLabel μ) c
        (gcwEasyWordIndex σ w c v) = easyBlockWord w c :=
  (gcwEasyIndexing μ σ).coordinateBlockLegWord_wordIndex w c v

/-- Distinct coordinates of a constituent are listed by distinct indices. -/
theorem gcwEasyWordIndex_injective (σ : Equiv.Perm μ) {N : ℕ} (w : Fin N → Leg) (c : Leg) :
    Function.Injective (gcwEasyWordIndex σ w c) :=
  (gcwEasyIndexing μ σ).wordIndex_injective w c

/-- Every coordinate word with the prescribed block word is listed by the constituent. -/
theorem exists_gcwEasyWordIndex (σ : Equiv.Perm μ) {N : ℕ} (w : Fin N → Leg) (c : Leg)
    {x : Fin N → GenCWIndex μ}
    (hx : ∀ t, gcwBlockLabel μ (x t) = easyBlockLetter (w t) c) :
    ∃ v, gcwEasyWordIndex σ w c v = x :=
  (gcwEasyIndexing μ σ).exists_wordIndex w c hx

/-- **The word identity of the easy extraction.**  The constituent selected by a `zero`-leg word is
the heterogeneous word product of the three easy matrix-multiplication shapes, in the sense of
`AlgebraicComplexity.mmWordCoefficients`. -/
theorem coordinatePower_gcwEasyWordIndex (σ : Equiv.Perm μ) {N : ℕ} (w : Fin N → Leg)
    (v : ∀ c, ∀ t, MMIndex (easyDimM (Fintype.card μ) (w t))
      (easyDimN (Fintype.card μ) (w t)) (easyDimP (Fintype.card μ) (w t)) c) :
    coordinatePower (gcwEasyTable K μ σ) N (fun c ↦ gcwEasyWordIndex σ w c (v c))
      = mmWordCoefficients K (fun t ↦ easyDimM (Fintype.card μ) (w t))
          (fun t ↦ easyDimN (Fintype.card μ) (w t))
          (fun t ↦ easyDimP (Fintype.card μ) (w t)) v :=
  (gcwEasyIndexing μ σ).coordinatePower_wordIndex (gcwEasyIndexing_isBlockTable σ) w v

/-- **The coordinates of one constituent, compressed to a single square shape.**  The mixed-radix
digit bijection `mmWordIndexEquiv` turns a word of indices of the three easy shapes into one index
of `⟨a, b, d⟩`, where `a`, `b` and `d` are the products of the three dimension words. -/
noncomputable def gcwEasyConstituentIndex (σ : Equiv.Perm μ) {N : ℕ} (w : Fin N → Leg)
    {a b d : ℕ}
    (hm : ∏ t, easyDimM (Fintype.card μ) (w t) = a)
    (hn : ∏ t, easyDimN (Fintype.card μ) (w t) = b)
    (hp : ∏ t, easyDimP (Fintype.card μ) (w t) = d)
    (c : Leg) (u : MMIndex a b d c) : Fin N → GenCWIndex μ :=
  (gcwEasyIndexing μ σ).constituentIndex w hm hn hp c u

/-- **The constituent identity.**  Read along the compressed coordinates, the `N`-th Kronecker
power of the easy table is the coefficient table of `⟨a, b, d⟩`. -/
theorem coordinatePower_gcwEasyConstituentIndex (σ : Equiv.Perm μ) {N : ℕ} (w : Fin N → Leg)
    {a b d : ℕ}
    (hm : ∏ t, easyDimM (Fintype.card μ) (w t) = a)
    (hn : ∏ t, easyDimN (Fintype.card μ) (w t) = b)
    (hp : ∏ t, easyDimP (Fintype.card μ) (w t) = d)
    (u : ∀ c, MMIndex a b d c) :
    coordinatePower (gcwEasyTable K μ σ) N
        (fun c ↦ gcwEasyConstituentIndex σ w hm hn hp c (u c))
      = mmCoefficients K a b d u :=
  (gcwEasyIndexing μ σ).coordinatePower_constituentIndex (gcwEasyIndexing_isBlockTable σ)
    w hm hn hp u

/-- The compressed coordinates of a constituent are still listed injectively. -/
theorem gcwEasyConstituentIndex_injective (σ : Equiv.Perm μ) {N : ℕ} (w : Fin N → Leg)
    {a b d : ℕ}
    (hm : ∏ t, easyDimM (Fintype.card μ) (w t) = a)
    (hn : ∏ t, easyDimN (Fintype.card μ) (w t) = b)
    (hp : ∏ t, easyDimP (Fintype.card μ) (w t) = d) (c : Leg) :
    Function.Injective (gcwEasyConstituentIndex σ w hm hn hp c) :=
  (gcwEasyIndexing μ σ).constituentIndex_injective w hm hn hp c

/-- The compressed coordinates of a constituent form the prescribed block word. -/
theorem coordinateBlockLegWord_gcwEasyConstituentIndex (σ : Equiv.Perm μ) {N : ℕ}
    (w : Fin N → Leg) {a b d : ℕ}
    (hm : ∏ t, easyDimM (Fintype.card μ) (w t) = a)
    (hn : ∏ t, easyDimN (Fintype.card μ) (w t) = b)
    (hp : ∏ t, easyDimP (Fintype.card μ) (w t) = d) (c : Leg) (u : MMIndex a b d c) :
    coordinateBlockLegWord (κ := GenCWIndexFamily μ) (fun _ ↦ gcwBlockLabel μ) c
        (gcwEasyConstituentIndex σ w hm hn hp c u) = easyBlockWord w c :=
  (gcwEasyIndexing μ σ).coordinateBlockLegWord_constituentIndex w hm hn hp c u

/-- Every coordinate word with the prescribed block word is listed by the compressed
constituent. -/
theorem exists_gcwEasyConstituentIndex (σ : Equiv.Perm μ) {N : ℕ} (w : Fin N → Leg)
    {a b d : ℕ}
    (hm : ∏ t, easyDimM (Fintype.card μ) (w t) = a)
    (hn : ∏ t, easyDimN (Fintype.card μ) (w t) = b)
    (hp : ∏ t, easyDimP (Fintype.card μ) (w t) = d) (c : Leg)
    {x : Fin N → GenCWIndex μ}
    (hx : ∀ t, gcwBlockLabel μ (x t) = easyBlockLetter (w t) c) :
    ∃ u, gcwEasyConstituentIndex σ w hm hn hp c u = x :=
  (gcwEasyIndexing μ σ).exists_constituentIndex w hm hn hp c hx

end Constituent

section HashingBridge

/-- **The two legwise filters of the easy hashing pipeline.**  A block address survives the hash
filter exactly when it is a block address of the full `3k`-fold power, has the equal type
(`easyEqualTypeKeepBlock`, `k` occurrences of the `zero` block on each leg) and survives the three
hash membership tests (`AlgebraicComplexity.PartitionHashEncoding.hashKeepBlock`).  Both filters are
legwise, which is what makes the coordinate zeroing out below possible. -/
theorem mem_easyFilteredPowerAddresses_iff {R : Type} [Field R] [NeZero (2 : R)] (k : ℕ)
    (B : Finset R) (seed : ProgressionHash.Seed R (Fin (easyEqualTypeDepth k + 1)))
    (u : BlockAddress fun _ : Leg ↦ PositiveWord CWBlock (easyEqualTypeDepth k)) :
    u ∈ (easyPartitionHashEncoding (R := R)).filteredPowerAddresses (easyEqualTypeDepth k)
        (easyEqualTypeWords k) B seed ↔
      u ∈ (easyPartitionHashEncoding (R := R)).modeledAddresses (easyEqualTypeDepth k)
          ((easyPartitionHashEncoding (R := R)).legalTargets (easyEqualTypeDepth k)
            Finset.univ) ∧
        (∀ c, easyEqualTypeKeepBlock k c (u c)) ∧
        ∀ c, (easyPartitionHashEncoding (R := R)).hashKeepBlock (easyEqualTypeDepth k) B seed c
          (u c) := by
  classical
  rw [← (easyPartitionHashEncoding (R := R)).filter_modeledAddresses_hashKeepBlock_eq
      (easyEqualTypeDepth k) (easyEqualTypeWords k) B seed,
    PartitionHashEncoding.hashFilteredModeledAddresses,
    ← (easyPartitionHashEncoding (R := R)).filter_modeledLegalTargets_eq_of_mem_iff
      (easyEqualTypeDepth k) (easyEqualTypeWords k) (easyEqualTypeKeepBlock k)
      (mem_easyEqualTypeWords_iff_keepBlocks k)]
  simp only [Finset.mem_filter]
  tauto

end HashingBridge

section Support

variable {K : Type u} [CommSemiring K] {μ : Type} [Fintype μ] [DecidableEq μ]

/-- **The block words of the support of the easy power are support words.**  If a triple of
coordinate words has a nonzero coefficient in the `(n+1)`-fold Kronecker power of `gcwEasyTable`,
then every position of it carries an easy block address, so the triple of block words is the block
address of a word of easy support addresses. -/
theorem exists_supportWord_of_coordinatePower_ne_zero (σ : Equiv.Perm μ) (n : ℕ)
    {p : ∀ c, Fin (n + 1) → GenCWIndexFamily μ c}
    (hp : coordinatePower (gcwEasyTable K μ σ) (n + 1) p ≠ 0) :
    ∃ word : PositiveWord easyBlockSupport n,
      blockAddressWordEquiv (fun _ : Leg ↦ CWBlock) n (PartitionHashEncoding.supportWordAddress
          (A := fun _ : Leg ↦ CWBlock) (support := easyBlockSupport) n word)
        = coordinateBlockWord (κ := GenCWIndexFamily μ) (fun _ ↦ gcwBlockLabel μ) p :=
  exists_blockSupportWord_of_coordinatePower_ne_zero (gcwEasyTable K μ σ)
    (fun _ ↦ gcwBlockLabel μ) easyBlockSupport
    (fun _ hs ↦ gcwEasyTable_eq_zero_of_notMem_easyBlockSupport σ hs) n hp

end Support

section Extraction

/-- **The coordinate easy Coppersmith--Winograd extraction, at a fixed hash seed.**

For a successful seed of the easy hashing pipeline of `Examples/CoppersmithWinogradEasyHashing.lean`
the `3k`-fold Kronecker power of `gcwEasyTable K μ σ` can be *zeroed out* to a block table of
`copies` disjoint copies of `⟨q^k, q^k, q^k⟩`, where `copies` is the number of legwise-isolated
addresses produced by the seed.  This is the coordinate shadow of
`easyPower_restricts_legwiseIsolatedSquareDirectSum`: no combinatorics is redone, only the two
tensor-level steps are replaced by their coordinate twins
`Tensor.coordinateBlockZeroOut_eq_coordinateZeroOut` and
`Tensor.coordinateBlockZeroOut_eq_extend_directSum`.

Proof sketch.  The selected addresses are the legwise-isolated ones, transported to coordinate
block words along `AlgebraicComplexity.blockAddressWordEquiv`.  Zeroing out, on each leg, the words whose block word is a leg
of a selected address realizes exactly the selected block words: a surviving triple of the power has
an easy block address at every position (`exists_supportWord_of_coordinatePower_ne_zero`), so it
lies in the full power support, and each of its three legwise block words carries the equal type and
the hash membership of some selected address (`mem_easyFilteredPowerAddresses_iff`); therefore it
lies in the hash-filtered family, where the selected address is alone in its `X`-fiber
(`AlgebraicComplexity.PartitionHashEncoding.legwiseIsolatedPowerAddresses_hasUniqueLegFibers`).
Legwise injectivity of the selected addresses then splits the zeroing out into a block table, whose
block at a selected block word is a heterogeneous word product of the three easy shapes with `k`
factors of each; the mixed-radix compression of `AlgebraicComplexity.mmWordIndexEquiv` turns it into
`⟨q^k, q^k, q^k⟩`. -/
theorem exists_easyCoordinate_zeroOut_eq_extend {R : Type} [Field R] [NeZero (2 : R)]
    (K : Type u) [CommSemiring K] (μ : Type) [Fintype μ] [DecidableEq μ] (σ : Equiv.Perm μ)
    (hq : 0 < Fintype.card μ) (k : ℕ)
    (B : Finset R) (hB : ThreeAPFree (B : Set R))
    (seed : ProgressionHash.Seed R (Fin (easyEqualTypeDepth k + 1))) (copies : ℕ)
    (hcopies : copies = ((easyPartitionHashEncoding (R := R)).legwiseIsolatedPowerAddresses
      (easyEqualTypeDepth k) (easyEqualTypeWords k) B seed).card)
    (hpos : 0 < copies) :
    ∃ (A : ∀ i, Finset (Fin (easyEqualTypeDepth k + 1) → GenCWIndexFamily μ i))
      (f : ∀ i, Fin copies × MMIndex (Fintype.card μ ^ k) (Fintype.card μ ^ k)
          (Fintype.card μ ^ k) i → (Fin (easyEqualTypeDepth k + 1) → GenCWIndexFamily μ i))
      (g : ∀ i, (Fin (easyEqualTypeDepth k + 1) → GenCWIndexFamily μ i) →
          Fin copies × MMIndex (Fintype.card μ ^ k) (Fintype.card μ ^ k)
            (Fintype.card μ ^ k) i),
      (∀ i x, g i (f i x) = x) ∧
        coordinateZeroOut
            (coordinatePower (gcwEasyTable K μ σ) (easyEqualTypeDepth k + 1)) A =
          coordinateExtend f g (coordinateDirectSum fun _ : Fin copies ↦
            mmCoefficients K (Fintype.card μ ^ k) (Fintype.card μ ^ k)
              (Fintype.card μ ^ k)) := by
  classical
  set D := gcwEasyIndexing μ σ with hDdef
  set S₀ := (easyPartitionHashEncoding (R := R)).legwiseIsolatedPowerAddresses
    (easyEqualTypeDepth k) (easyEqualTypeWords k) B seed with hS₀def
  -- The properties of the selected addresses supplied by the hashing pipeline.
  have hkeep : ∀ t ∈ S₀,
      t ∈ (easyPartitionHashEncoding (R := R)).modeledAddresses (easyEqualTypeDepth k)
          ((easyPartitionHashEncoding (R := R)).legalTargets (easyEqualTypeDepth k)
            Finset.univ) ∧
        (∀ c, easyEqualTypeKeepBlock k c (t c)) ∧
        ∀ c, (easyPartitionHashEncoding (R := R)).hashKeepBlock (easyEqualTypeDepth k) B seed c
          (t c) := fun t ht ↦
    (mem_easyFilteredPowerAddresses_iff k B seed t).mp
      (PartitionHashEncoding.legwiseIsolatedPowerAddresses_subset_filteredPowerAddresses
        (easyPartitionHashEncoding (R := R)) (easyEqualTypeDepth k) (easyEqualTypeWords k) B seed
        ht)
  have hlegwise : IsLegwiseInjective S₀ :=
    PartitionHashEncoding.legwiseIsolatedPowerAddresses_isLegwiseInjective
      (easyPartitionHashEncoding (R := R)) (easyEqualTypeDepth k) (easyEqualTypeWords k) B hB seed
  have hunique := PartitionHashEncoding.legwiseIsolatedPowerAddresses_hasUniqueLegFibers
    (easyPartitionHashEncoding (R := R)) (easyEqualTypeDepth k) (easyEqualTypeWords k) B hB seed
    Leg.X
  -- Enumerate the selected addresses.
  have enum := (Finset.equivFinOfCardEq hcopies.symm).symm
  set key : Fin copies → BlockAddress fun _ : Leg ↦ Fin (easyEqualTypeDepth k + 1) → CWBlock :=
    fun j ↦ blockAddressWordEquiv (fun _ : Leg ↦ CWBlock) (easyEqualTypeDepth k)
      ((enum j : S₀) : BlockAddress fun _ : Leg ↦ PositiveWord CWBlock (easyEqualTypeDepth k))
    with hkeydef
  have hkeyval : ∀ (j : Fin copies) (c : Leg) (t : Fin (easyEqualTypeDepth k + 1)),
      key j c t = positiveWordEquiv CWBlock (easyEqualTypeDepth k)
        (((enum j : S₀) : BlockAddress fun _ : Leg ↦
          PositiveWord CWBlock (easyEqualTypeDepth k)) c) t := fun _ _ _ ↦ rfl
  have hmemS : ∀ j, key j ∈ S₀.image
      (blockAddressWordEquiv (fun _ : Leg ↦ CWBlock) (easyEqualTypeDepth k)) :=
    fun j ↦ Finset.mem_image_of_mem _ (enum j).2
  have hkeyinj : ∀ i, Function.Injective fun j ↦ key j i := by
    intro i j j' hfun
    have h : key j i = key j' i := hfun
    have h1 : ((enum j : S₀) : BlockAddress fun _ : Leg ↦
          PositiveWord CWBlock (easyEqualTypeDepth k)) i
        = ((enum j' : S₀) : BlockAddress fun _ : Leg ↦
          PositiveWord CWBlock (easyEqualTypeDepth k)) i := by
      refine (positiveWordEquiv CWBlock (easyEqualTypeDepth k)).injective ?_
      funext t
      have := congrFun h t
      rw [hkeyval, hkeyval] at this
      exact this
    exact enum.injective (Subtype.ext
      (hlegwise i (Finset.mem_coe.mpr (enum j).2) (Finset.mem_coe.mpr (enum j').2) h1))
  -- Every selected block word is a word of easy block addresses.
  have hfullmem : ∀ j, ∀ t, (fun c ↦ key j c t) ∈ easyBlockSupport := by
    intro j t
    obtain ⟨word, -, hword⟩ :=
      (easyPartitionHashEncoding (R := R)).exists_sourceWord_of_mem_modeledAddresses_legalTargets
        (easyEqualTypeDepth k) Finset.univ (hkeep _ (enum j).2).1
    have hk : key j = blockAddressWordEquiv (fun _ : Leg ↦ CWBlock) (easyEqualTypeDepth k)
        (PartitionHashEncoding.supportWordAddress (A := fun _ : Leg ↦ CWBlock)
          (support := easyBlockSupport) (easyEqualTypeDepth k) word) := by
      rw [hkeydef, hword]
    rw [hk]
    exact PartitionHashEncoding.mem_support_blockAddressWordEquiv
      (A := fun _ : Leg ↦ CWBlock) (support := easyBlockSupport) (easyEqualTypeDepth k) word t
  set wf : Fin copies → Fin (easyEqualTypeDepth k + 1) → Leg :=
    fun j ↦ easyZeroLegWord (key j) with hwfdef
  have hword : ∀ j, easyBlockWord (wf j) = key j := by
    intro j
    rw [hwfdef]
    exact easyBlockWord_easyZeroLegWord (hfullmem j)
  have hletter : ∀ (j : Fin copies) (c : Leg) (t : Fin (easyEqualTypeDepth k + 1)),
      key j c t = D.letter (wf j t) c := by
    intro j c t
    rw [← hword j]
    rfl
  -- The equal type says that each leg is the `zero` leg at exactly `k` positions.
  have hzerocount : ∀ j c, (Finset.univ.filter fun t ↦ wf j t = c).card = k := by
    intro j c
    have h := (hkeep _ (enum j).2).2.1 c
    rw [easyEqualTypeKeepBlock, WordType.multiplicity_eq_card_fiber, Fintype.card_subtype] at h
    refine Eq.trans (congrArg Finset.card ?_) h
    refine Finset.filter_congr fun t _ ↦ ?_
    rw [← hkeyval j c t, hletter j c t]
    exact (easyBlockLetter_eq_zero_iff _ _).symm
  have hdimM : ∀ j, ∏ t, D.dimM (wf j t) = Fintype.card μ ^ k := by
    intro j
    show ∏ t, easyDimM (Fintype.card μ) (wf j t) = _
    rw [prod_easyDimM, hzerocount j Leg.Y]
  have hdimN : ∀ j, ∏ t, D.dimN (wf j t) = Fintype.card μ ^ k := by
    intro j
    show ∏ t, easyDimN (Fintype.card μ) (wf j t) = _
    rw [prod_easyDimN, hzerocount j Leg.Z]
  have hdimP : ∀ j, ∏ t, D.dimP (wf j t) = Fintype.card μ ^ k := by
    intro j
    show ∏ t, easyDimP (Fintype.card μ) (wf j t) = _
    rw [prod_easyDimP, hzerocount j Leg.X]
  -- The legwise sets of block words used by the zeroing out.
  set BW : ∀ i : Leg, Finset (Fin (easyEqualTypeDepth k + 1) → CWBlock) :=
    fun i ↦ (S₀.image (blockAddressWordEquiv (fun _ : Leg ↦ CWBlock)
      (easyEqualTypeDepth k))).image fun s ↦ s i with hBWdef
  have hsub : ∀ (j : Fin copies) (i : Leg), key j i ∈ BW i :=
    fun j i ↦ Finset.mem_image_of_mem _ (hmemS j)
  have hclosed : ∀ p : ∀ i, Fin (easyEqualTypeDepth k + 1) → GenCWIndexFamily μ i,
      coordinatePower (gcwEasyTable K μ σ) (easyEqualTypeDepth k + 1) p ≠ 0 →
      (∀ i, coordinateBlockWord D.label p i ∈ BW i) →
      ∃ j, coordinateBlockWord D.label p = key j := by
    intro p hp hmem
    obtain ⟨word, hwordeq⟩ :=
      exists_supportWord_of_coordinatePower_ne_zero σ (easyEqualTypeDepth k) hp
    have hlegeq : ∀ (c : Leg) (t : BlockAddress fun _ : Leg ↦
          PositiveWord CWBlock (easyEqualTypeDepth k)),
        blockAddressWordEquiv (fun _ : Leg ↦ CWBlock) (easyEqualTypeDepth k) t c
          = coordinateBlockWord (κ := GenCWIndexFamily μ) (fun _ ↦ gcwBlockLabel μ) p c →
        PartitionHashEncoding.supportWordAddress (A := fun _ : Leg ↦ CWBlock)
          (support := easyBlockSupport) (easyEqualTypeDepth k) word c = t c := by
      intro c t hct
      refine (positiveWordEquiv CWBlock (easyEqualTypeDepth k)).injective ?_
      have hu : blockAddressWordEquiv (fun _ : Leg ↦ CWBlock) (easyEqualTypeDepth k)
          (PartitionHashEncoding.supportWordAddress (A := fun _ : Leg ↦ CWBlock)
            (support := easyBlockSupport) (easyEqualTypeDepth k) word) c
          = coordinateBlockWord (κ := GenCWIndexFamily μ) (fun _ ↦ gcwBlockLabel μ) p c := by
        rw [hwordeq]
      rw [blockAddressWordEquiv_apply] at hu hct
      rw [hu, hct]
    have hkeepu : ∀ c, easyEqualTypeKeepBlock k c
          (PartitionHashEncoding.supportWordAddress (A := fun _ : Leg ↦ CWBlock)
            (support := easyBlockSupport) (easyEqualTypeDepth k) word c) ∧
        (easyPartitionHashEncoding (R := R)).hashKeepBlock (easyEqualTypeDepth k) B seed c
          (PartitionHashEncoding.supportWordAddress (A := fun _ : Leg ↦ CWBlock)
            (support := easyBlockSupport) (easyEqualTypeDepth k) word c) := by
      intro c
      obtain ⟨s, hs, hsc⟩ := Finset.mem_image.mp (hBWdef ▸ hmem c)
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hs
      rw [hlegeq c t hsc]
      exact ⟨(hkeep t ht).2.1 c, (hkeep t ht).2.2 c⟩
    have hufull : PartitionHashEncoding.supportWordAddress (A := fun _ : Leg ↦ CWBlock)
        (support := easyBlockSupport) (easyEqualTypeDepth k) word ∈
          (easyPartitionHashEncoding (R := R)).modeledAddresses (easyEqualTypeDepth k)
            ((easyPartitionHashEncoding (R := R)).legalTargets (easyEqualTypeDepth k)
              Finset.univ) := by
      rw [PartitionHashEncoding.modeledAddresses_legalTargets_eq_image]
      exact Finset.mem_image.mpr ⟨word, Finset.mem_univ _, rfl⟩
    have hufilt := (mem_easyFilteredPowerAddresses_iff k B seed _).mpr
      ⟨hufull, fun c ↦ (hkeepu c).1, fun c ↦ (hkeepu c).2⟩
    obtain ⟨s, hs, hsX⟩ := Finset.mem_image.mp (hBWdef ▸ hmem Leg.X)
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hs
    have hut := hunique.2 t ht _ hufilt (hlegeq Leg.X t hsX)
    refine ⟨enum.symm ⟨t, ht⟩, ?_⟩
    show coordinateBlockWord (κ := GenCWIndexFamily μ) (fun _ ↦ gcwBlockLabel μ) p
      = key (enum.symm ⟨t, ht⟩)
    rw [← hwordeq, hut, hkeydef]
    simp
  exact D.exists_zeroOut_eq_extend (gcwEasyIndexing_isBlockTable σ) key wf hletter hkeyinj
    hdimM hdimN hdimP hpos (pow_pos hq k) (pow_pos hq k) (pow_pos hq k) BW hsub hclosed

/-- **Milestone M5 of `BARRIER_FRAMEWORK.md`: the coordinate easy Coppersmith--Winograd
extraction.**

For every `k ≥ 1` there are a hashing modulus `M ≤ 24·4^k` and a number `copies` of extracted
blocks with

```text
27^k · roth(M/2) ≤ 6·k²·M² · copies
```

such that the `3k`-fold Kronecker power of the easy generalized Coppersmith--Winograd table
`gcwEasyTable K μ σ` *zeroes out* to a block table of `copies` disjoint copies of
`⟨q^k, q^k, q^k⟩`, `q = |μ|`.  This is exactly the finite data of an
`AlgebraicComplexity.CoordinateGalacticCertificate K (gcwEasyTable K μ σ) (3k) (q^k) (q^k) (q^k)
copies` in zeroing-out form: milestone M2 (`coordinateGalacticCertificate_of_zeroOut`, weights
`if v ∈ A i then 0 else 1` and threshold `0`) converts it into a certificate.

The copy count is the one proved by the abstract pipeline: it is
`easyCopies_lower_of_hashingCount` fed with the seed of
`ProgressionHash.LegalTriple.exists_seed_many_legwiseIsolatedTargets`, the Behrend set of
`exists_threeAPFree_zmod_half`, and the prime modulus of `Nat.exists_prime_lt_and_le_two_mul`,
exactly as in `exists_prime_easyPower_asymptoticSum_rate_bound`.  Only the tensor-level steps are
different, and they are `exists_easyCoordinate_zeroOut_eq_extend`.

The hypothesis on the coefficient ring is only `CommSemiring K`: the field-size condition
`12·4^k ≤ |R|` of `easyEqualType_competitorQuarter_of_fieldCard` is a statement about the hashing
field `ZMod M`, not about `K`. -/
theorem exists_easyCoordinate_squareExtraction (K : Type u) [CommSemiring K]
    (μ : Type) [Fintype μ] [DecidableEq μ] (σ : Equiv.Perm μ)
    (hq : 0 < Fintype.card μ) {k : ℕ} (hk : 0 < k) :
    ∃ M copies : ℕ, 2 ≤ M ∧ M ≤ 24 * 4 ^ k ∧
      27 ^ k * rothNumberNat (M / 2) ≤ 6 * k ^ 2 * (M * M) * copies ∧
      ∃ (A : ∀ i, Finset (Fin (3 * k) → GenCWIndexFamily μ i))
        (f : ∀ i, Fin copies × MMIndex (Fintype.card μ ^ k) (Fintype.card μ ^ k)
            (Fintype.card μ ^ k) i → (Fin (3 * k) → GenCWIndexFamily μ i))
        (g : ∀ i, (Fin (3 * k) → GenCWIndexFamily μ i) →
            Fin copies × MMIndex (Fintype.card μ ^ k) (Fintype.card μ ^ k)
              (Fintype.card μ ^ k) i),
        (∀ i x, g i (f i x) = x) ∧
          coordinateZeroOut (coordinatePower (gcwEasyTable K μ σ) (3 * k)) A =
            coordinateExtend f g (coordinateDirectSum fun _ : Fin copies ↦
              mmCoefficients K (Fintype.card μ ^ k) (Fintype.card μ ^ k)
                (Fintype.card μ ^ k)) := by
  classical
  rw [← easyEqualTypeDepth_add_one hk]
  -- The prime hashing modulus of Bertrand's postulate and the Behrend progression-free set.
  have hnz : 12 * 4 ^ k ≠ 0 := by positivity
  obtain ⟨M, hprime, hlower, hupper⟩ := Nat.exists_prime_lt_and_le_two_mul (12 * 4 ^ k) hnz
  haveI : Fact M.Prime := ⟨hprime⟩
  have hpow : 0 < 4 ^ k := pow_pos (by norm_num) k
  have hM3 : 3 ≤ M := by omega
  haveI : NeZero (2 : ZMod M) := neZero_two_zmod_of_three_le hM3
  obtain ⟨B, hBcard, hB⟩ := exists_threeAPFree_zmod_half M
  have hfield : 12 * 4 ^ k ≤ Fintype.card (ZMod M) := by simpa [ZMod.card] using hlower.le
  -- A good hash seed, from the unchanged legwise isolation theorem.
  obtain ⟨seed, hcount, -, -⟩ :=
    ProgressionHash.LegalTriple.exists_seed_many_legwiseIsolatedTargets
      (easyEqualTypeTargets (R := ZMod M) k) B hB
      (easyEqualType_competitorQuarter_of_fieldCard k hfield)
  set copies := ((easyPartitionHashEncoding (R := ZMod M)).legwiseIsolatedPowerAddresses
    (easyEqualTypeDepth k) (easyEqualTypeWords k) B seed).card with hcopiesdef
  have hcount' : 3 * (easyEqualTypeWords k).card * B.card ≤ 4 * (M * M) * copies := by
    rw [hcopiesdef, PartitionHashEncoding.card_legwiseIsolatedPowerAddresses]
    change 3 * ((easyPartitionHashEncoding (R := ZMod M)).legalTargets (easyEqualTypeDepth k)
      (easyEqualTypeWords k)).card * B.card ≤ _ at hcount
    rw [PartitionHashEncoding.card_legalTargets, ZMod.card] at hcount
    exact hcount
  have hrate : 27 ^ k * rothNumberNat (M / 2) ≤ 6 * k ^ 2 * (M * M) * copies := by
    have hcard : 3 * (easyEqualTypeWords k).card * Fintype.card B ≤ 4 * (M * M) * copies := by
      simpa using hcount'
    have h := easyCopies_lower_of_hashingCount (k := k) (M := M) (copies := copies) (B := B)
      hk hcard
    rw [← hBcard]
    simpa using h
  -- The count forces at least one extracted block.
  have hpos : 0 < copies := by
    rcases Nat.eq_zero_or_pos copies with h0 | h
    · rw [h0, Nat.mul_zero] at hrate
      have hroth : 1 ≤ rothNumberNat (M / 2) := rothNumberNat_pos (by omega)
      have h27 : 0 < 27 ^ k := pow_pos (by norm_num) k
      exact absurd hrate (Nat.not_le.mpr (Nat.mul_pos h27 hroth))
    · exact h
  obtain ⟨A, f, g, hgf, heq⟩ :=
    exists_easyCoordinate_zeroOut_eq_extend K μ σ hq k B hB seed copies rfl hpos
  refine ⟨M, copies, by omega, ?_, hrate, A, f, g, hgf, heq⟩
  calc M ≤ 2 * (12 * 4 ^ k) := hupper
    _ = 24 * 4 ^ k := by ring

/-- **The packaged certificate.**  Milestone M2 (`coordinateGalacticCertificate_of_zeroOut`) turns
the zeroing out of `exists_easyCoordinate_squareExtraction` into a coordinate galactic certificate
for the easy generalized Coppersmith--Winograd table, with the indicator weights
`w i v = if v ∈ A i then 0 else 1` and threshold `0`.  Feeding the copy count to milestone M6
(`sq_le_asymptoticIndependenceNumber_pow_of_zeroOut` together with the Behrend rate) is what yields
`(27/4)·q² ≤ Ī(CW_q^σ)³` of [AlmanVassilevskaWilliams2018, Theorem 7.3]. -/
theorem coordinateGalacticCertificate_gcwEasyTable (K : Type u) [CommSemiring K]
    (μ : Type) [Fintype μ] [DecidableEq μ] (σ : Equiv.Perm μ)
    (hq : 0 < Fintype.card μ) {k : ℕ} (hk : 0 < k) :
    ∃ M copies : ℕ, 2 ≤ M ∧ M ≤ 24 * 4 ^ k ∧
      27 ^ k * rothNumberNat (M / 2) ≤ 6 * k ^ 2 * (M * M) * copies ∧
        CoordinateGalacticCertificate K (gcwEasyTable K μ σ) (3 * k)
          (Fintype.card μ ^ k) (Fintype.card μ ^ k) (Fintype.card μ ^ k) copies := by
  obtain ⟨M, copies, hM2, hMub, hrate, A, f, g, hgf, heq⟩ :=
    exists_easyCoordinate_squareExtraction K μ σ hq hk
  exact ⟨M, copies, hM2, hMub, hrate,
    coordinateGalacticCertificate_of_zeroOut K A f g hgf heq⟩

end Extraction

section BaseInequality

/-- **Milestone M6, and the substance of [AlmanVassilevskaWilliams2018, Theorem 7.3]**: for every
parameter `q = |μ| ≥ 1` and every permutation `σ` of `μ`,

```text
(27/4)·q² ≤ Ī(CW_q^σ)³.
```

Note that the statement is about the *full* generalized Coppersmith--Winograd table `gcwTable`, not
about the easy table `gcwEasyTable` the extraction is performed on; the two are compared in the
last line of the proof.

Proof sketch.  Milestone M5 (`coordinateGalacticCertificate_gcwEasyTable`) produces, for every
`k ≥ 1`, a modulus `M ≤ 24·4^k` and a copy count `copies` with
`27^k·roth(M/2) ≤ 6k²·M²·copies` and a balanced coordinate galactic certificate of data
`(3k, q^k, q^k, q^k, copies)` for `gcwEasyTable`.  Milestone M1
(`CoordinateGalacticCertificate.sq_le_asymptoticIndependenceNumber_pow`) converts each certificate
into `copies·(q^k)² ≤ Ī(easy)^{3k}`, i.e. into the value bound
`copies·(q²)^k ≤ (Ī(easy)³)^k` of the Behrend rate argument.  The two bounds are exactly the
hypotheses of `AlgebraicComplexity.Growth.le_of_forall_exists_rothNumberNat_copies` with
`A = 27`, `D = 4`, `E = 24`, `poly k = 6k²` (subexponential), `V = q²` and `ρ = Ī(easy)³`, whose
conclusion `A/D·V ≤ ρ` is the claim for the easy table: Behrend's construction, the hashing losses
and the modulus all disappear in the limit `k → ∞`, and the only surviving trace of the modulus is
the division of the progression base `27` by the modulus growth rate `4`.  Finally `gcwEasyTable`
is by definition a zeroing out of `gcwTable`, and `Ī` is monotone under zeroing outs
(`Tensor.asymptoticIndependenceNumber_coordinateZeroOut_le`), which lifts the inequality from the
easy table to `CW_q^σ`. -/
theorem easyCW_independence_base_inequality (K : Type u) [CommSemiring K] [NoZeroDivisors K]
    [Nontrivial K] (μ : Type) [Fintype μ] [DecidableEq μ] (σ : Equiv.Perm μ)
    (hq : 0 < Fintype.card μ) :
    (27 : ℝ) / 4 * (Fintype.card μ : ℝ) ^ 2 ≤
      asymptoticIndependenceNumber (gcwTable K μ σ) ^ 3 := by
  have hnn : (0 : ℝ) ≤ asymptoticIndependenceNumber (gcwEasyTable K μ σ) :=
    asymptoticIndependenceNumber_nonneg _
  -- The Behrend rate argument, applied to the M5 certificates.
  have hbase : (27 : ℝ) / 4 * (Fintype.card μ : ℝ) ^ 2 ≤
      asymptoticIndependenceNumber (gcwEasyTable K μ σ) ^ 3 := by
    refine Growth.le_of_forall_exists_rothNumberNat_copies
      (A := 27) (D := 4) (E := 24) (V := (Fintype.card μ : ℝ) ^ 2)
      (ρ := asymptoticIndependenceNumber (gcwEasyTable K μ σ) ^ 3)
      (poly := fun k ↦ 6 * (k : ℝ) ^ 2)
      (by norm_num) (by norm_num) (by norm_num) (by positivity) (by positivity)
      ((Growth.Subexponential.natCast_pow 2).const_mul (by norm_num)) ?_
    intro k hk
    obtain ⟨M, copies, hM2, hMub, hrate, hcert⟩ :=
      coordinateGalacticCertificate_gcwEasyTable K μ σ hq hk
    refine ⟨M, copies, hM2, by exact_mod_cast hMub, by exact_mod_cast hrate, ?_⟩
    -- M1 on the balanced certificate of length `3k` and dimension `q^k`.
    have hI := hcert.sq_le_asymptoticIndependenceNumber_pow K (by omega)
    calc (copies : ℝ) * ((Fintype.card μ : ℝ) ^ 2) ^ k
        = (copies : ℝ) * (((Fintype.card μ ^ k : ℕ) : ℝ)) ^ 2 := by push_cast; ring
      _ ≤ asymptoticIndependenceNumber (gcwEasyTable K μ σ) ^ (3 * k) := hI
      _ = (asymptoticIndependenceNumber (gcwEasyTable K μ σ) ^ 3) ^ k := by rw [pow_mul]
  -- `gcwEasyTable` is a zeroing out of `gcwTable`, and `Ī` is monotone under zeroing outs.
  refine hbase.trans (pow_le_pow_left₀ hnn ?_ 3)
  exact asymptoticIndependenceNumber_coordinateZeroOut_le (gcwTable K μ σ) _

end BaseInequality

end AlgebraicComplexity.Examples
