/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/
import AlgebraicComplexity.Analysis.BehrendRate
import AlgebraicComplexity.Examples.CoppersmithWinogradEasyCoordinate
import AlgebraicComplexity.Examples.CoppersmithWinogradFirstPowerHashing
import AlgebraicComplexity.MatrixMultiplication.CoordinateBlockCertificate

/-!
# The coordinate six-constituent first-power Coppersmith--Winograd extraction

Layer 4 (`AlgebraicComplexity/Examples/`).  This module is
[AlmanVassilevskaWilliams2018, Remark 7.3]: the coordinate shadow of the classical
six-constituent first-power analysis of [CoppersmithWinograd1990] applied to the barrier
program, giving the independence-number lower bound

```text
6.419 ≤ Ī(CW_6^σ).
```

## What is reused

Nothing combinatorial is redone.  The rational type, its exact marginal and joint counts, the
legal hashing targets, the fiber bound and the good-seed averaging are consumed unchanged from
`Examples/CoppersmithWinogradFirstPowerHashing.lean` (`cwFirstPowerWords`,
`cwFirstPowerNaturalType`, `cwFirstPowerMarginalType`, `cwFirstPowerKeepBlock`,
`mem_cwFirstPowerWords_iff_keepBlocks`, `cwFirstPowerFiberSize`,
`cwFirstPower_competitorQuarter_of_fieldCard`, `cwFirstPowerSubexponentialLoss`), and the three
*middle* constituents together with their letter identity are consumed unchanged from
`Examples/CoppersmithWinogradEasyCoordinate.lean` (`gcwEasyIndexEquiv`,
`gcwTable_gcwEasyIndexEquiv`), on top of the shared coordinate block label `gcwBlockLabel` of
`Examples/GeneralizedCoppersmithWinograd.lean`.  The two tensor-level steps are the generic ones of
`MatrixMultiplication/CoordinateBlockCertificate.lean`.

The one genuinely new ingredient is the three *corner* constituents `x_{q+1} y_0 z_0`,
`x_0 y_{q+1} z_0`, `x_0 y_0 z_{q+1}` of [AlmanVassilevskaWilliams2018, Definition 3.1], each a
single variable triple and hence a copy of `⟨1,1,1⟩`.  Their presence is why this file works with
the *full* table `gcwTable K μ σ` and not with the easy table `gcwEasyTable K μ σ`.

## Main definitions

* `CWFullConstituent`: the six constituents of `CW_q^σ`, indexed as `Sum.inl z` (the corner whose
  `last` block sits on leg `z`) and `Sum.inr z` (the middle constituent whose `zero` block sits on
  leg `z`).
* `cwFullBlockLetter`, `cwFullDimM`, `cwFullDimN`, `cwFullDimP`: the block address and the
  matrix-multiplication shape of each constituent; `⟨1,1,1⟩` for the corners and `⟨1,1,q⟩`,
  `⟨q,1,1⟩`, `⟨1,q,1⟩` for the middle ones.
* `gcwFullIndexEquiv`, `gcwFullIndexing`: the legwise coordinate bijections of each constituent,
  packaged as an `AlgebraicComplexity.BlockMMIndexing`.
* `cwFullConstituentOf`: the constituent occupying a supported block address, inverse to
  `cwFullBlockLetter`.

## Main results

* `gcwTable_gcwFullIndexEquiv`: **the letter identity for all six blocks.**
* `coordinateGalacticCertificate_gcwTable_firstPower`: **the milestone.**  For every `k ≥ 1` there
  are a prime hashing modulus `M` with `12·d_k < M ≤ 24·d_k` (`d_k = cwFirstPowerFiberSize k`) and
  a copy count with `3·|W_k|·roth(M/2) ≤ 4·M²·copies` such that the `30000k`-th Kronecker power of
  `gcwTable K μ σ` zeroes out to `copies` disjoint copies of `⟨q^{9519k}, q^{9519k}, q^{9519k}⟩`.
* `asymptoticIndependenceNumber_gcwTable_firstPower_lower`: the `k → ∞` limit,
  `H·q^{19038} ≤ Ī(CW_q^σ)^{30000}` with `H = ternaryEntropyBase 10481 19038 481`, and its
  specialization `asymptoticIndependenceNumber_cwTable_six_lower` at the checked `q = 6`.
* `avw_remark_seven_three`: the readable numeric corollary at `q = 6`,
  `6 + 419/1000 ≤ Ī(CW_6^σ)`.

## The numeric value

`ternaryEntropyBase 10481 19038 481` is the *rational* number
`30000^30000 / (10481^10481·19038^19038·481^481)` (the factors of `e` in its definition cancel
because the profile sums to its own total), so the final numeric step is exact integer
arithmetic and loses nothing.  With this repository's rational type the exact limit value of
`(H·6^{19038})^{1/30000}` is `6.41933327…`; AVW display `6.4194…`, which the exact optimizer of
the first-power analysis presumably attains but this rational type does not.  Only the certified
`6 + 419/1000` is claimed.

## Position in the library

Layer 4.  It imports the unchanged first-power combinatorics, the easy coordinate file (for the
three middle constituents and their letter identity), the generic layer-3 block certificate, and
the Behrend rate estimates.  Nothing here is imported by a lower layer.

## References

* [AlmanVassilevskaWilliams2018] J. Alman and V. Vassilevska Williams, *Limits on all known (and
  some unknown) approaches to matrix multiplication*, arXiv:1810.08671; Definition 3.1,
  Lemma 4.4, Theorem 7.3, Remark 7.3.
* [CoppersmithWinograd1990] D. Coppersmith and S. Winograd, *Matrix multiplication via arithmetic
  progressions*, J. Symbolic Comput. 9 (1990); §7, the six-constituent first-power analysis.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor

universe u

/-! ## The six constituents of `CW_q^σ` -/

/-- **The six constituents of the generalized Coppersmith--Winograd tensor.**  `Sum.inl z` is the
corner constituent whose `last` block sits on leg `z` (the block addresses `cw200`, `cw020`,
`cw002`), and `Sum.inr z` is the middle constituent whose `zero` block sits on leg `z` (the easy
block addresses `cw011`, `cw101`, `cw110`). -/
abbrev CWFullConstituent := Leg ⊕ Leg

/-- The block address of the corner constituent whose `last` block sits on leg `z`. -/
def cwCornerBlockLetter : Leg → Leg → CWBlock
  | .X, .X => .last
  | .X, .Y => .zero
  | .X, .Z => .zero
  | .Y, .X => .zero
  | .Y, .Y => .last
  | .Y, .Z => .zero
  | .Z, .X => .zero
  | .Z, .Y => .zero
  | .Z, .Z => .last

/-- The block address of a constituent of `CW_q^σ`. -/
def cwFullBlockLetter : CWFullConstituent → CWBlockAddress
  | .inl z => cwCornerBlockLetter z
  | .inr z => easyBlockLetter z

/-- First matrix-multiplication dimension of a constituent: `1` for a corner, `easyDimM` for a
middle constituent. -/
def cwFullDimM (q : ℕ) : CWFullConstituent → ℕ
  | .inl _ => 1
  | .inr z => easyDimM q z

/-- Second matrix-multiplication dimension of a constituent. -/
def cwFullDimN (q : ℕ) : CWFullConstituent → ℕ
  | .inl _ => 1
  | .inr z => easyDimN q z

/-- Third matrix-multiplication dimension of a constituent. -/
def cwFullDimP (q : ℕ) : CWFullConstituent → ℕ
  | .inl _ => 1
  | .inr z => easyDimP q z

/-- The block addresses of the six constituents are the standard six-address CW support. -/
theorem cwFullBlockLetter_mem_cwBlockSupport (s : CWFullConstituent) :
    cwFullBlockLetter s ∈ cwBlockSupport := by
  cases s with
  | inl z => cases z <;> decide
  | inr z => cases z <;> decide

/-- **The constituent occupying a supported block address.**  A supported address carries the
`last` block on at most one leg; if it does, the address is a corner, and otherwise it is the
middle constituent read off by `easyZeroLeg`. -/
def cwFullConstituentOf (a : CWBlockAddress) : CWFullConstituent :=
  if a .X = CWBlock.last then Sum.inl .X
  else if a .Y = CWBlock.last then Sum.inl .Y
  else if a .Z = CWBlock.last then Sum.inl .Z
  else Sum.inr (easyZeroLeg a)

@[simp] theorem cwFullConstituentOf_cw200 : cwFullConstituentOf cw200 = Sum.inl .X := by decide
@[simp] theorem cwFullConstituentOf_cw020 : cwFullConstituentOf cw020 = Sum.inl .Y := by decide
@[simp] theorem cwFullConstituentOf_cw002 : cwFullConstituentOf cw002 = Sum.inl .Z := by decide
@[simp] theorem cwFullConstituentOf_cw011 : cwFullConstituentOf cw011 = Sum.inr .X := by decide
@[simp] theorem cwFullConstituentOf_cw101 : cwFullConstituentOf cw101 = Sum.inr .Y := by decide
@[simp] theorem cwFullConstituentOf_cw110 : cwFullConstituentOf cw110 = Sum.inr .Z := by decide

/-- Reading off the constituent recovers a supported block address. -/
theorem cwFullBlockLetter_cwFullConstituentOf {a : CWBlockAddress} (ha : a ∈ cwBlockSupport) :
    cwFullBlockLetter (cwFullConstituentOf a) = a := by
  fin_cases ha <;> decide

section Indexing

variable {K : Type u} [CommSemiring K] {μ : Type} [Fintype μ] [DecidableEq μ]

/-- **The coordinates of one corner constituent.**  Each of the three corners is the single
variable triple `x_{q+1} y_0 z_0` (and its two cyclic rotations), so its coordinates are those of
`⟨1,1,1⟩`. -/
noncomputable def gcwCornerIndexEquiv (μ : Type) :
    (z c : Leg) → MMIndex 1 1 1 c ≃
      {x : GenCWIndex μ // gcwBlockLabel μ x = cwCornerBlockLetter z c}
  | .X, .X => (Equiv.prodUnique (Fin 1) (Fin 1)).trans (gcwLastFiberFin μ)
  | .X, .Y => (Equiv.prodUnique (Fin 1) (Fin 1)).trans (gcwZeroFiberFin μ)
  | .X, .Z => (Equiv.prodUnique (Fin 1) (Fin 1)).trans (gcwZeroFiberFin μ)
  | .Y, .X => (Equiv.prodUnique (Fin 1) (Fin 1)).trans (gcwZeroFiberFin μ)
  | .Y, .Y => (Equiv.prodUnique (Fin 1) (Fin 1)).trans (gcwLastFiberFin μ)
  | .Y, .Z => (Equiv.prodUnique (Fin 1) (Fin 1)).trans (gcwZeroFiberFin μ)
  | .Z, .X => (Equiv.prodUnique (Fin 1) (Fin 1)).trans (gcwZeroFiberFin μ)
  | .Z, .Y => (Equiv.prodUnique (Fin 1) (Fin 1)).trans (gcwZeroFiberFin μ)
  | .Z, .Z => (Equiv.prodUnique (Fin 1) (Fin 1)).trans (gcwLastFiberFin μ)

/-- **The coordinates of one constituent of `CW_q^σ`**, corner or middle. -/
noncomputable def gcwFullIndexEquiv (σ : Equiv.Perm μ) :
    (s : CWFullConstituent) → (c : Leg) →
      MMIndex (cwFullDimM (Fintype.card μ) s) (cwFullDimN (Fintype.card μ) s)
          (cwFullDimP (Fintype.card μ) s) c ≃
        {x : GenCWIndex μ // gcwBlockLabel μ x = cwFullBlockLetter s c}
  | .inl z, c => gcwCornerIndexEquiv μ z c
  | .inr z, c => gcwEasyIndexEquiv σ z c

/-- **The letter identity on a corner block.**  Read along the coordinates listed by
`gcwCornerIndexEquiv`, the coefficient table of `CW_q^σ` restricted to a corner block is the
coefficient table of `⟨1,1,1⟩`: the listed triple is the single support triple of
[AlmanVassilevskaWilliams2018, Definition 3.1] with `q + 1` on leg `z` and `0` on the other two,
so the left side is `1`; and every triple of indices of `⟨1,1,1⟩` is compatible because all six
components live in `Fin 1`, so the right side is `1` too. -/
theorem gcwTable_gcwCornerIndexEquiv (σ : Equiv.Perm μ) (z : Leg)
    (u : ∀ c, MMIndex 1 1 1 c) :
    gcwTable K μ σ (fun c ↦ (gcwCornerIndexEquiv μ z c (u c) : GenCWIndex μ))
      = mmCoefficients K 1 1 1 u := by
  have hcomp : MMCompatible u :=
    ⟨Subsingleton.elim _ _, Subsingleton.elim _ _, Subsingleton.elim _ _⟩
  have hsupp : GenCWSupport σ (fun c ↦ (gcwCornerIndexEquiv μ z c (u c) : GenCWIndex μ)) := by
    cases z
    · exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩))
    · exact Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)
    · exact Or.inl ⟨rfl, rfl, rfl⟩
  show gcwTable K μ σ _ = if MMCompatible u then 1 else 0
  rw [gcwTable_apply, if_pos hsupp, if_pos hcomp]

/-- **The letter identity of the six-constituent extraction.**  Read along the coordinates listed
by `gcwFullIndexEquiv`, the coefficient table of `CW_q^σ` restricted to one of its six blocks is
exactly the coefficient table of the corresponding matrix-multiplication tensor.

Proof sketch: on a middle block this is `gcwTable_gcwEasyIndexEquiv`.  On a corner block the
listed triple is the single support triple of [AlmanVassilevskaWilliams2018, Definition 3.1] with
`q + 1` on one leg and `0` on the other two, so the left side is `1`; and every triple of indices
of `⟨1,1,1⟩` is compatible because all six components live in `Fin 1`, so the right side is `1`
too. -/
theorem gcwTable_gcwFullIndexEquiv (σ : Equiv.Perm μ) (s : CWFullConstituent)
    (u : ∀ c, MMIndex (cwFullDimM (Fintype.card μ) s) (cwFullDimN (Fintype.card μ) s)
      (cwFullDimP (Fintype.card μ) s) c) :
    gcwTable K μ σ (fun c ↦ (gcwFullIndexEquiv σ s c (u c) : GenCWIndex μ))
      = mmCoefficients K (cwFullDimM (Fintype.card μ) s) (cwFullDimN (Fintype.card μ) s)
          (cwFullDimP (Fintype.card μ) s) u := by
  cases s with
  | inr z => exact gcwTable_gcwEasyIndexEquiv σ z u
  | inl z => exact gcwTable_gcwCornerIndexEquiv σ z u

/-- **The six-constituent block indexing of `CW_q^σ`.**  This is the paper-side input of the
generic coordinate block certificate of `MatrixMultiplication/CoordinateBlockCertificate.lean`. -/
noncomputable def gcwFullIndexing (μ : Type) [Fintype μ] [DecidableEq μ] (σ : Equiv.Perm μ) :
    BlockMMIndexing (GenCWIndexFamily μ) (fun _ : Leg ↦ CWBlock) CWFullConstituent where
  label := fun _ ↦ gcwBlockLabel μ
  letter := cwFullBlockLetter
  dimM := cwFullDimM (Fintype.card μ)
  dimN := cwFullDimN (Fintype.card μ)
  dimP := cwFullDimP (Fintype.card μ)
  index := gcwFullIndexEquiv σ

/-- The table of `CW_q^σ` is a block table for its six-constituent indexing. -/
theorem gcwFullIndexing_isBlockTable (σ : Equiv.Perm μ) :
    (gcwFullIndexing μ σ).IsBlockTable (gcwTable K μ σ) :=
  fun s u ↦ gcwTable_gcwFullIndexEquiv σ s u

/-- Off the six standard blocks the table of `CW_q^σ` vanishes: every support triple of
[AlmanVassilevskaWilliams2018, Definition 3.1] has one of the six standard block addresses. -/
theorem gcwTable_eq_zero_of_notMem_cwBlockSupport (σ : Equiv.Perm μ)
    {s : ∀ c, GenCWIndexFamily μ c}
    (h : (fun c ↦ gcwBlockLabel μ (s c)) ∉ cwBlockSupport) :
    gcwTable K μ σ s = 0 := by
  classical
  rw [gcwTable_apply, if_neg]
  intro hsupp
  apply h
  rcases hsupp with ⟨hx, hy, hz⟩ | ⟨hx, hy, hz⟩ | ⟨hx, hy, hz⟩ |
    ⟨i, hx, hy, hz⟩ | ⟨i, hx, hy, hz⟩ | ⟨i, hx, hy, hz⟩
  · have heq : (fun c ↦ gcwBlockLabel μ (s c)) = cw002 := by
      funext c; cases c <;> simp [hx, hy, hz]
    rw [heq]; decide
  · have heq : (fun c ↦ gcwBlockLabel μ (s c)) = cw020 := by
      funext c; cases c <;> simp [hx, hy, hz]
    rw [heq]; decide
  · have heq : (fun c ↦ gcwBlockLabel μ (s c)) = cw200 := by
      funext c; cases c <;> simp [hx, hy, hz]
    rw [heq]; decide
  · have heq : (fun c ↦ gcwBlockLabel μ (s c)) = cw110 := by
      funext c; cases c <;> simp [hx, hy, hz]
    rw [heq]; decide
  · have heq : (fun c ↦ gcwBlockLabel μ (s c)) = cw101 := by
      funext c; cases c <;> simp [hx, hy, hz]
    rw [heq]; decide
  · have heq : (fun c ↦ gcwBlockLabel μ (s c)) = cw011 := by
      funext c; cases c <;> simp [hx, hy, hz]
    rw [heq]; decide

/-- **The block words of the support of the power are support words.**  If a triple of coordinate
words has a nonzero coefficient in the `(n+1)`-fold Kronecker power of `gcwTable`, then every
position of it carries one of the six standard block addresses, so the triple of block words is
the block address of a word of supported addresses. -/
theorem exists_cwSupportWord_of_coordinatePower_ne_zero (σ : Equiv.Perm μ) (n : ℕ)
    {p : ∀ c, Fin (n + 1) → GenCWIndexFamily μ c}
    (hp : coordinatePower (gcwTable K μ σ) (n + 1) p ≠ 0) :
    ∃ word : PositiveWord cwBlockSupport n,
      blockAddressWordEquiv (fun _ : Leg ↦ CWBlock) n (PartitionHashEncoding.supportWordAddress
          (A := fun _ : Leg ↦ CWBlock) (support := cwBlockSupport) n word)
        = coordinateBlockWord (κ := GenCWIndexFamily μ) (fun _ ↦ gcwBlockLabel μ) p :=
  exists_blockSupportWord_of_coordinatePower_ne_zero (gcwTable K μ σ)
    (fun _ ↦ gcwBlockLabel μ) cwBlockSupport
    (fun _ hs ↦ gcwTable_eq_zero_of_notMem_cwBlockSupport σ hs) n hp

end Indexing

/-! ## Dimension products along a typed word -/

section Dimensions

/-- The product of a constituent parameter along a word of the first-power rational type depends
only on that type. -/
private theorem prod_cwFullDim_word (k : ℕ) (f : CWFullConstituent → ℕ)
    {word : PositiveWord cwBlockSupport (cwFirstPowerDepth k)}
    (hword : word ∈ cwFirstPowerWords k) :
    (∏ t, f (cwFullConstituentOf
        ((positiveWordEquiv cwBlockSupport (cwFirstPowerDepth k) word t : cwBlockSupport) :
          CWBlockAddress)))
      = ∏ s ∈ cwBlockSupport, f (cwFullConstituentOf s) ^ cwFirstPowerAddressCount k s := by
  classical
  rw [WordType.prod_word_eq_prod_pow (fun s : cwBlockSupport ↦ f (cwFullConstituentOf s.1))
    (positiveWordEquiv cwBlockSupport (cwFirstPowerDepth k) word)]
  rw [show WordType.multiplicity
      (positiveWordEquiv cwBlockSupport (cwFirstPowerDepth k) word)
      = cwFirstPowerNaturalType k from mem_positiveTypeClass.mp hword]
  exact Finset.prod_subtype cwBlockSupport (fun _ ↦ Iff.rfl)
    (fun s ↦ f (cwFullConstituentOf s) ^ cwFirstPowerAddressCount k s)

/-- The first dimension product of a first-power word is `q^{9519k}`: only the constituent `cw101`
has first dimension `q`, and the rational type gives it multiplicity `9519k`. -/
theorem prod_cwFullDimM_word (q k : ℕ)
    {word : PositiveWord cwBlockSupport (cwFirstPowerDepth k)}
    (hword : word ∈ cwFirstPowerWords k) :
    (∏ t, cwFullDimM q (cwFullConstituentOf
        ((positiveWordEquiv cwBlockSupport (cwFirstPowerDepth k) word t : cwBlockSupport) :
          CWBlockAddress))) = q ^ (9519 * k) := by
  rw [prod_cwFullDim_word k (cwFullDimM q) hword, prod_cwBlockSupport]
  simp [cwFullDimM, cwFirstPowerAddressCount, cw200, cw020, cw002, cw011, cw101, cw110,
    cwBlockAddress]

/-- The second dimension product of a first-power word is `q^{9519k}` (the constituent `cw110`). -/
theorem prod_cwFullDimN_word (q k : ℕ)
    {word : PositiveWord cwBlockSupport (cwFirstPowerDepth k)}
    (hword : word ∈ cwFirstPowerWords k) :
    (∏ t, cwFullDimN q (cwFullConstituentOf
        ((positiveWordEquiv cwBlockSupport (cwFirstPowerDepth k) word t : cwBlockSupport) :
          CWBlockAddress))) = q ^ (9519 * k) := by
  rw [prod_cwFullDim_word k (cwFullDimN q) hword, prod_cwBlockSupport]
  simp [cwFullDimN, cwFirstPowerAddressCount, cw200, cw020, cw002, cw011, cw101, cw110,
    cwBlockAddress]

/-- The third dimension product of a first-power word is `q^{9519k}` (the constituent `cw011`). -/
theorem prod_cwFullDimP_word (q k : ℕ)
    {word : PositiveWord cwBlockSupport (cwFirstPowerDepth k)}
    (hword : word ∈ cwFirstPowerWords k) :
    (∏ t, cwFullDimP q (cwFullConstituentOf
        ((positiveWordEquiv cwBlockSupport (cwFirstPowerDepth k) word t : cwBlockSupport) :
          CWBlockAddress))) = q ^ (9519 * k) := by
  rw [prod_cwFullDim_word k (cwFullDimP q) hword, prod_cwBlockSupport]
  simp [cwFullDimP, cwFirstPowerAddressCount, cw200, cw020, cw002, cw011, cw101, cw110,
    cwBlockAddress]

end Dimensions

/-! ## The hashing bridge -/

section HashingBridge

/-- **The two legwise filters of the first-power hashing pipeline.**  A block address survives the
hash filter exactly when it is a block address of the full `30000k`-fold power, has the rational
marginal type (`cwFirstPowerKeepBlock`) and survives the three hash membership tests.  Both filters
are legwise, which is what makes the coordinate zeroing out below possible.  This is the exact
analogue of `mem_easyFilteredPowerAddresses_iff`. -/
theorem mem_cwFirstPowerFilteredPowerAddresses_iff {R : Type} [Field R] [NeZero (2 : R)] (k : ℕ)
    (B : Finset R) (seed : ProgressionHash.Seed R (Fin (cwFirstPowerDepth k + 1)))
    (u : BlockAddress fun _ : Leg ↦ PositiveWord CWBlock (cwFirstPowerDepth k)) :
    u ∈ (cwPartitionHashEncoding (R := R)).filteredPowerAddresses (cwFirstPowerDepth k)
        (cwFirstPowerWords k) B seed ↔
      u ∈ (cwPartitionHashEncoding (R := R)).modeledAddresses (cwFirstPowerDepth k)
          ((cwPartitionHashEncoding (R := R)).legalTargets (cwFirstPowerDepth k)
            Finset.univ) ∧
        (∀ c, cwFirstPowerKeepBlock k c (u c)) ∧
        ∀ c, (cwPartitionHashEncoding (R := R)).hashKeepBlock (cwFirstPowerDepth k) B seed c
          (u c) := by
  classical
  rw [← (cwPartitionHashEncoding (R := R)).filter_modeledAddresses_hashKeepBlock_eq
      (cwFirstPowerDepth k) (cwFirstPowerWords k) B seed,
    PartitionHashEncoding.hashFilteredModeledAddresses,
    ← (cwPartitionHashEncoding (R := R)).filter_modeledLegalTargets_eq_of_mem_iff
      (cwFirstPowerDepth k) (cwFirstPowerWords k) (cwFirstPowerKeepBlock k)
      (mem_cwFirstPowerWords_iff_keepBlocks k)]
  simp only [Finset.mem_filter]
  tauto

end HashingBridge

/-! ## The extraction -/

section Extraction

/-- **The coordinate six-constituent extraction, at a fixed hash seed.**

For a successful seed of the first-power hashing pipeline of
`Examples/CoppersmithWinogradFirstPowerHashing.lean`, the `30000k`-fold Kronecker power of
`gcwTable K μ σ` can be *zeroed out* to a block table of `copies` disjoint copies of
`⟨q^{9519k}, q^{9519k}, q^{9519k}⟩`, where `copies` is the number of legwise-isolated addresses
produced by the seed.  This is the coordinate shadow of
`cwPower_restricts_legwiseIsolatedSquareDirectSum`.

Proof sketch.  The selected addresses are the legwise-isolated ones, transported to coordinate
block words along `AlgebraicComplexity.blockAddressWordEquiv`.  Each of them is the block word of
a word of six-constituent letters whose three dimension products are `q^{9519k}` (the rational
type, `prod_cwFullDimM_word` and companions).  A surviving triple of the power has a supported
block address at every position (`exists_cwSupportWord_of_coordinatePower_ne_zero`), and each of
its three legwise block words carries the marginal type and the hash membership of some selected
address (`mem_cwFirstPowerFilteredPowerAddresses_iff`); therefore it lies in the hash-filtered
family, where the selected address is alone in its `X`-fiber.  The generic assembly
`AlgebraicComplexity.BlockMMIndexing.exists_zeroOut_eq_extend` then does the rest. -/
theorem exists_cwFirstPowerCoordinate_zeroOut_eq_extend {R : Type} [Field R] [NeZero (2 : R)]
    (K : Type u) [CommSemiring K] (μ : Type) [Fintype μ] [DecidableEq μ] (σ : Equiv.Perm μ)
    (hq : 0 < Fintype.card μ) (k : ℕ)
    (B : Finset R) (hB : ThreeAPFree (B : Set R))
    (seed : ProgressionHash.Seed R (Fin (cwFirstPowerDepth k + 1))) (copies : ℕ)
    (hcopies : copies = ((cwPartitionHashEncoding (R := R)).legwiseIsolatedPowerAddresses
      (cwFirstPowerDepth k) (cwFirstPowerWords k) B seed).card)
    (hpos : 0 < copies) :
    CoordinateGalacticCertificate K (gcwTable K μ σ) (cwFirstPowerDepth k + 1)
      (Fintype.card μ ^ (9519 * k)) (Fintype.card μ ^ (9519 * k))
      (Fintype.card μ ^ (9519 * k)) copies := by
  classical
  set D := gcwFullIndexing μ σ with hDdef
  set S₀ := (cwPartitionHashEncoding (R := R)).legwiseIsolatedPowerAddresses
    (cwFirstPowerDepth k) (cwFirstPowerWords k) B seed with hS₀def
  -- The properties of the selected addresses supplied by the hashing pipeline.
  have hkeep : ∀ t ∈ S₀,
      t ∈ (cwPartitionHashEncoding (R := R)).modeledAddresses (cwFirstPowerDepth k)
          ((cwPartitionHashEncoding (R := R)).legalTargets (cwFirstPowerDepth k)
            Finset.univ) ∧
        (∀ c, cwFirstPowerKeepBlock k c (t c)) ∧
        ∀ c, (cwPartitionHashEncoding (R := R)).hashKeepBlock (cwFirstPowerDepth k) B seed c
          (t c) := fun t ht ↦
    (mem_cwFirstPowerFilteredPowerAddresses_iff k B seed t).mp
      (PartitionHashEncoding.legwiseIsolatedPowerAddresses_subset_filteredPowerAddresses
        (cwPartitionHashEncoding (R := R)) (cwFirstPowerDepth k) (cwFirstPowerWords k) B seed ht)
  have hlegwise : IsLegwiseInjective S₀ :=
    PartitionHashEncoding.legwiseIsolatedPowerAddresses_isLegwiseInjective
      (cwPartitionHashEncoding (R := R)) (cwFirstPowerDepth k) (cwFirstPowerWords k) B hB seed
  have hunique := PartitionHashEncoding.legwiseIsolatedPowerAddresses_hasUniqueLegFibers
    (cwPartitionHashEncoding (R := R)) (cwFirstPowerDepth k) (cwFirstPowerWords k) B hB seed
    Leg.X
  -- Enumerate the selected addresses.
  have enum := (Finset.equivFinOfCardEq hcopies.symm).symm
  set key : Fin copies → BlockAddress fun _ : Leg ↦ Fin (cwFirstPowerDepth k + 1) → CWBlock :=
    fun j ↦ blockAddressWordEquiv (fun _ : Leg ↦ CWBlock) (cwFirstPowerDepth k)
      ((enum j : S₀) : BlockAddress fun _ : Leg ↦ PositiveWord CWBlock (cwFirstPowerDepth k))
    with hkeydef
  have hkeyval : ∀ (j : Fin copies) (c : Leg) (t : Fin (cwFirstPowerDepth k + 1)),
      key j c t = positiveWordEquiv CWBlock (cwFirstPowerDepth k)
        (((enum j : S₀) : BlockAddress fun _ : Leg ↦
          PositiveWord CWBlock (cwFirstPowerDepth k)) c) t := fun _ _ _ ↦ rfl
  have hmemS : ∀ j, key j ∈ S₀.image
      (blockAddressWordEquiv (fun _ : Leg ↦ CWBlock) (cwFirstPowerDepth k)) :=
    fun j ↦ Finset.mem_image_of_mem _ (enum j).2
  have hkeyinj : ∀ i, Function.Injective fun j ↦ key j i := by
    intro i j j' hfun
    have h : key j i = key j' i := hfun
    have h1 : ((enum j : S₀) : BlockAddress fun _ : Leg ↦
          PositiveWord CWBlock (cwFirstPowerDepth k)) i
        = ((enum j' : S₀) : BlockAddress fun _ : Leg ↦
          PositiveWord CWBlock (cwFirstPowerDepth k)) i := by
      refine (positiveWordEquiv CWBlock (cwFirstPowerDepth k)).injective ?_
      funext t
      have := congrFun h t
      rw [hkeyval, hkeyval] at this
      exact this
    exact enum.injective (Subtype.ext
      (hlegwise i (Finset.mem_coe.mpr (enum j).2) (Finset.mem_coe.mpr (enum j').2) h1))
  -- Every selected address is the block address of a word of the rational type.
  have hsource : ∀ j : Fin copies, ∃ word : PositiveWord cwBlockSupport (cwFirstPowerDepth k),
      word ∈ cwFirstPowerWords k ∧
        key j = blockAddressWordEquiv (fun _ : Leg ↦ CWBlock) (cwFirstPowerDepth k)
          (PartitionHashEncoding.supportWordAddress (A := fun _ : Leg ↦ CWBlock)
            (support := cwBlockSupport) (cwFirstPowerDepth k) word) := by
    intro j
    obtain ⟨word, -, hword⟩ :=
      (cwPartitionHashEncoding (R := R)).exists_sourceWord_of_mem_modeledAddresses_legalTargets
        (cwFirstPowerDepth k) Finset.univ (hkeep _ (enum j).2).1
    refine ⟨word, ?_, by rw [hkeydef, hword]⟩
    refine (mem_cwFirstPowerWords_iff_keepBlocks k word).mpr fun c ↦ ?_
    have hc := (hkeep _ (enum j).2).2.1 c
    rwa [← hword] at hc
  choose wordOf hwordMem hwordEq using hsource
  -- The constituent word of a selected address, and its dimension products.
  set wf : Fin copies → Fin (cwFirstPowerDepth k + 1) → CWFullConstituent :=
    fun j t ↦ cwFullConstituentOf fun c ↦ key j c t with hwfdef
  have hcell : ∀ (j : Fin copies) (t : Fin (cwFirstPowerDepth k + 1)),
      (fun c ↦ key j c t) =
        ((positiveWordEquiv cwBlockSupport (cwFirstPowerDepth k) (wordOf j) t :
            cwBlockSupport) : CWBlockAddress) := by
    intro j t
    funext c
    have h := PartitionHashEncoding.positiveWordEquiv_supportWordAddress
      (A := fun _ : Leg ↦ CWBlock) (support := cwBlockSupport) (cwFirstPowerDepth k)
      (wordOf j) c
    have := congrFun h t
    rw [hwordEq j]
    rw [blockAddressWordEquiv_apply]
    exact this
  have hfullmem : ∀ (j : Fin copies) (t : Fin (cwFirstPowerDepth k + 1)),
      (fun c ↦ key j c t) ∈ cwBlockSupport := by
    intro j t
    rw [hcell j t]
    exact (positiveWordEquiv cwBlockSupport (cwFirstPowerDepth k) (wordOf j) t).2
  have hletter : ∀ (j : Fin copies) (c : Leg) (t : Fin (cwFirstPowerDepth k + 1)),
      key j c t = D.letter (wf j t) c := by
    intro j c t
    exact (congrFun (cwFullBlockLetter_cwFullConstituentOf (hfullmem j t)) c).symm
  have hdimM : ∀ j, ∏ t, D.dimM (wf j t) = Fintype.card μ ^ (9519 * k) := by
    intro j
    rw [show (fun t ↦ D.dimM (wf j t)) = fun t ↦ cwFullDimM (Fintype.card μ)
        (cwFullConstituentOf ((positiveWordEquiv cwBlockSupport (cwFirstPowerDepth k)
          (wordOf j) t : cwBlockSupport) : CWBlockAddress)) from
      funext fun t ↦ by rw [hwfdef]; simp only [hcell j t]; rfl]
    exact prod_cwFullDimM_word (Fintype.card μ) k (hwordMem j)
  have hdimN : ∀ j, ∏ t, D.dimN (wf j t) = Fintype.card μ ^ (9519 * k) := by
    intro j
    rw [show (fun t ↦ D.dimN (wf j t)) = fun t ↦ cwFullDimN (Fintype.card μ)
        (cwFullConstituentOf ((positiveWordEquiv cwBlockSupport (cwFirstPowerDepth k)
          (wordOf j) t : cwBlockSupport) : CWBlockAddress)) from
      funext fun t ↦ by rw [hwfdef]; simp only [hcell j t]; rfl]
    exact prod_cwFullDimN_word (Fintype.card μ) k (hwordMem j)
  have hdimP : ∀ j, ∏ t, D.dimP (wf j t) = Fintype.card μ ^ (9519 * k) := by
    intro j
    rw [show (fun t ↦ D.dimP (wf j t)) = fun t ↦ cwFullDimP (Fintype.card μ)
        (cwFullConstituentOf ((positiveWordEquiv cwBlockSupport (cwFirstPowerDepth k)
          (wordOf j) t : cwBlockSupport) : CWBlockAddress)) from
      funext fun t ↦ by rw [hwfdef]; simp only [hcell j t]; rfl]
    exact prod_cwFullDimP_word (Fintype.card μ) k (hwordMem j)
  -- The legwise sets of block words used by the zeroing out.
  set BW : ∀ i : Leg, Finset (Fin (cwFirstPowerDepth k + 1) → CWBlock) :=
    fun i ↦ (S₀.image (blockAddressWordEquiv (fun _ : Leg ↦ CWBlock)
      (cwFirstPowerDepth k))).image fun s ↦ s i with hBWdef
  have hsub : ∀ (j : Fin copies) (i : Leg), key j i ∈ BW i := by
    intro j i
    exact Finset.mem_image_of_mem _ (hmemS j)
  have hclosed : ∀ p : ∀ i, Fin (cwFirstPowerDepth k + 1) → GenCWIndexFamily μ i,
      coordinatePower (gcwTable K μ σ) (cwFirstPowerDepth k + 1) p ≠ 0 →
      (∀ i, coordinateBlockWord D.label p i ∈ BW i) →
      ∃ j, coordinateBlockWord D.label p = key j := by
    intro p hp hmem
    obtain ⟨word, hwordeq⟩ :=
      exists_cwSupportWord_of_coordinatePower_ne_zero σ (cwFirstPowerDepth k) hp
    have hlegeq : ∀ (c : Leg) (t : BlockAddress fun _ : Leg ↦
          PositiveWord CWBlock (cwFirstPowerDepth k)),
        blockAddressWordEquiv (fun _ : Leg ↦ CWBlock) (cwFirstPowerDepth k) t c
          = coordinateBlockWord (κ := GenCWIndexFamily μ) (fun _ ↦ gcwBlockLabel μ) p c →
        PartitionHashEncoding.supportWordAddress (A := fun _ : Leg ↦ CWBlock)
          (support := cwBlockSupport) (cwFirstPowerDepth k) word c = t c := by
      intro c t hct
      refine (positiveWordEquiv CWBlock (cwFirstPowerDepth k)).injective ?_
      have hu : blockAddressWordEquiv (fun _ : Leg ↦ CWBlock) (cwFirstPowerDepth k)
          (PartitionHashEncoding.supportWordAddress (A := fun _ : Leg ↦ CWBlock)
            (support := cwBlockSupport) (cwFirstPowerDepth k) word) c
          = coordinateBlockWord (κ := GenCWIndexFamily μ) (fun _ ↦ gcwBlockLabel μ) p c := by
        rw [hwordeq]
      rw [blockAddressWordEquiv_apply] at hu hct
      rw [hu, hct]
    have hkeepu : ∀ c, cwFirstPowerKeepBlock k c
          (PartitionHashEncoding.supportWordAddress (A := fun _ : Leg ↦ CWBlock)
            (support := cwBlockSupport) (cwFirstPowerDepth k) word c) ∧
        (cwPartitionHashEncoding (R := R)).hashKeepBlock (cwFirstPowerDepth k) B seed c
          (PartitionHashEncoding.supportWordAddress (A := fun _ : Leg ↦ CWBlock)
            (support := cwBlockSupport) (cwFirstPowerDepth k) word c) := by
      intro c
      obtain ⟨s, hs, hsc⟩ := Finset.mem_image.mp (hBWdef ▸ hmem c)
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hs
      rw [hlegeq c t hsc]
      exact ⟨(hkeep t ht).2.1 c, (hkeep t ht).2.2 c⟩
    have hufull : PartitionHashEncoding.supportWordAddress (A := fun _ : Leg ↦ CWBlock)
        (support := cwBlockSupport) (cwFirstPowerDepth k) word ∈
          (cwPartitionHashEncoding (R := R)).modeledAddresses (cwFirstPowerDepth k)
            ((cwPartitionHashEncoding (R := R)).legalTargets (cwFirstPowerDepth k)
              Finset.univ) := by
      rw [PartitionHashEncoding.modeledAddresses_legalTargets_eq_image]
      exact Finset.mem_image.mpr ⟨word, Finset.mem_univ _, rfl⟩
    have hufilt := (mem_cwFirstPowerFilteredPowerAddresses_iff k B seed _).mpr
      ⟨hufull, fun c ↦ (hkeepu c).1, fun c ↦ (hkeepu c).2⟩
    obtain ⟨s, hs, hsX⟩ := Finset.mem_image.mp (hBWdef ▸ hmem Leg.X)
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hs
    have hut := hunique.2 t ht _ hufilt (hlegeq Leg.X t hsX)
    refine ⟨enum.symm ⟨t, ht⟩, ?_⟩
    show coordinateBlockWord (κ := GenCWIndexFamily μ) (fun _ ↦ gcwBlockLabel μ) p
      = key (enum.symm ⟨t, ht⟩)
    rw [← hwordeq, hut, hkeydef]
    simp
  exact (gcwFullIndexing μ σ).coordinateGalacticCertificate
    (gcwFullIndexing_isBlockTable σ) key wf hletter hkeyinj hdimM hdimN hdimP hpos
    (pow_pos hq _) (pow_pos hq _) (pow_pos hq _) BW hsub hclosed

/-- **The milestone: the coordinate six-constituent first-power certificate.**

For every `k ≥ 1` there are a prime hashing modulus `M` with
`12·d_k < M ≤ 24·d_k` (`d_k = cwFirstPowerFiberSize k`, the size of a legwise type fiber) and a
number `copies` of extracted blocks with

```text
3·|W_k|·roth(M/2) ≤ 4·M²·copies
```

(`W_k = cwFirstPowerWords k`, the words of the rational type) such that the `30000k`-fold
Kronecker power of `gcwTable K μ σ` *zeroes out* to `copies` disjoint copies of
`⟨q^{9519k}, q^{9519k}, q^{9519k}⟩`, `q = |μ|`.  This is the finite data of a balanced
`AlgebraicComplexity.CoordinateGalacticCertificate`.

The count is the one proved by the abstract pipeline; only the tensor-level steps differ, and
they are `exists_cwFirstPowerCoordinate_zeroOut_eq_extend`.  Compare
`exists_prime_cwPower_asymptoticSum_bound`, which feeds the same finite data to Schönhage's
inequality instead.

The hypothesis on the coefficient ring is only `CommSemiring K`: the field-size condition
`12·d_k ≤ |R|` of `cwFirstPower_competitorQuarter_of_fieldCard` is a statement about the hashing
field `ZMod M`, not about `K`. -/
theorem coordinateGalacticCertificate_gcwTable_firstPower (K : Type u) [CommSemiring K]
    (μ : Type) [Fintype μ] [DecidableEq μ] (σ : Equiv.Perm μ)
    (hq : 0 < Fintype.card μ) {k : ℕ} (hk : 0 < k) :
    ∃ M copies : ℕ, M.Prime ∧ 12 * cwFirstPowerFiberSize k < M ∧
      M ≤ 24 * cwFirstPowerFiberSize k ∧
      3 * (cwFirstPowerWords k).card * rothNumberNat (M / 2) ≤ 4 * (M * M) * copies ∧
        CoordinateGalacticCertificate K (gcwTable K μ σ) (30000 * k)
          (Fintype.card μ ^ (9519 * k)) (Fintype.card μ ^ (9519 * k))
          (Fintype.card μ ^ (9519 * k)) copies := by
  classical
  -- The prime hashing modulus of Bertrand's postulate and the Behrend progression-free set.
  have hn : 12 * cwFirstPowerFiberSize k ≠ 0 := by
    have := cwFirstPowerFiberSize_pos hk
    positivity
  obtain ⟨M, hprime, hlower, hupper⟩ :=
    Nat.exists_prime_lt_and_le_two_mul (12 * cwFirstPowerFiberSize k) hn
  haveI : Fact M.Prime := ⟨hprime⟩
  have hM3 : 3 ≤ M := by
    have := cwFirstPowerFiberSize_pos hk
    omega
  haveI : NeZero (2 : ZMod M) := neZero_two_zmod_of_three_le hM3
  obtain ⟨B, hBcard, hB⟩ := exists_threeAPFree_zmod_half M
  -- A good hash seed, from the unchanged legwise isolation theorem.
  obtain ⟨seed, hcount, -, -⟩ :=
    ProgressionHash.LegalTriple.exists_seed_many_legwiseIsolatedTargets
      (cwFirstPowerTargets (R := ZMod M) k) B hB
      (cwFirstPower_competitorQuarter_of_fieldCard k hk (by simpa [ZMod.card] using hlower.le))
  set copies := ((cwPartitionHashEncoding (R := ZMod M)).legwiseIsolatedPowerAddresses
    (cwFirstPowerDepth k) (cwFirstPowerWords k) B seed).card with hcopiesdef
  have hcount' : 3 * (cwFirstPowerWords k).card * rothNumberNat (M / 2) ≤
      4 * (M * M) * copies := by
    rw [hcopiesdef, PartitionHashEncoding.card_legwiseIsolatedPowerAddresses]
    change 3 * ((cwPartitionHashEncoding (R := ZMod M)).legalTargets (cwFirstPowerDepth k)
      (cwFirstPowerWords k)).card * B.card ≤ _ at hcount
    rw [PartitionHashEncoding.card_legalTargets, ZMod.card] at hcount
    rw [← hBcard]
    exact hcount
  -- The count forces at least one extracted block.
  have hpos : 0 < copies := by
    rcases Nat.eq_zero_or_pos copies with h0 | h
    · rw [h0, Nat.mul_zero] at hcount'
      have hroth : 1 ≤ rothNumberNat (M / 2) := rothNumberNat_pos (by omega)
      have hwords : 0 < (cwFirstPowerWords k).card :=
        Finset.card_pos.mpr (cwFirstPowerWords_nonempty hk)
      exact absurd hcount' (Nat.not_le.mpr (by positivity))
    · exact h
  have hcert := exists_cwFirstPowerCoordinate_zeroOut_eq_extend K μ σ hq k B hB seed copies rfl hpos
  rw [cwFirstPowerDepth_add_one hk] at hcert
  exact ⟨M, copies, hprime, hlower, by omega, hcount', hcert⟩

end Extraction

/-! ## The limit -/

section BaseInequality

/-- **The rate inequality of the coordinate six-constituent extraction.**  For every `k ≥ 1`

```text
(H · q^{19038})^k ≤ loss(k) · (Ī(CW_q^σ)^{30000})^k,
```

where `H = ternaryEntropyBase 10481 19038 481` and `loss` is the explicit subexponential
`cwFirstPowerSubexponentialLoss` of the abstract analysis.

Proof sketch: this is the proof of `cwFirstPower_rate_inequality` with the Schönhage bound
`copies·(q^ω)^{9519k} ≤ (q+2)^{30000k}` replaced by the barrier bound
`copies·(q^{9519k})² ≤ Ī(CW_q^σ)^{30000k}` of milestone M1
(`CoordinateGalacticCertificate.sq_le_asymptoticIndependenceNumber_pow`).  As there, the size
`d_k` of a type fiber cancels between the count `3·P·d_k·roth(M/2) ≤ 4M²·copies` and the modulus
bound `M ≤ 24·d_k` through Behrend's `roth(M/2) ≥ (M/3)·exp(-4√log(M/2))`, and the entropy
estimate `H^k ≤ ternaryMultinomialLoss·P` replaces the marginal type class count `P`. -/
theorem cwFirstPowerCoordinate_rate_inequality (K : Type u) [CommSemiring K] [NoZeroDivisors K]
    [Nontrivial K] (μ : Type) [Fintype μ] [DecidableEq μ] (σ : Equiv.Perm μ)
    (hq : 0 < Fintype.card μ) {k : ℕ} (hk : 0 < k) :
    (WordType.ternaryEntropyBase 10481 19038 481 * ((Fintype.card μ : ℝ) ^ 19038)) ^ k ≤
      cwFirstPowerSubexponentialLoss k *
        (asymptoticIndependenceNumber (gcwTable K μ σ) ^ 30000) ^ k := by
  classical
  obtain ⟨M, copies, -, hlower, hupper, hcount, hcert⟩ :=
    coordinateGalacticCertificate_gcwTable_firstPower K μ σ hq hk
  set q := Fintype.card μ with hqdef
  set I := asymptoticIndependenceNumber (gcwTable K μ σ) with hIdef
  have hInn : (0 : ℝ) ≤ I := asymptoticIndependenceNumber_nonneg _
  set P := (WordType.typeClass (cwFirstPowerDepth k + 1) (cwFirstPowerMarginalType k)).card with hP
  set d := cwFirstPowerFiberSize k with hd
  set S := (cwFirstPowerWords k).card with hS
  have hdPos : 0 < d := cwFirstPowerFiberSize_pos hk
  have hM : 3 ≤ M := by omega
  have hSPNat : P * d = S := by
    simpa [P, d, S] using cwFirstPowerMarginalCard_mul_fiberSize hk
  have hSP : (P : ℝ) * (d : ℝ) = (S : ℝ) := by exact_mod_cast hSPNat
  have hdUpper : d ≤ 6 ^ (30000 * k) :=
    (cwFirstPowerFiberSize_le_words k).trans (card_cwFirstPowerWords_le hk)
  have hhalfPos : (0 : ℝ) < ((M / 2 : ℕ) : ℝ) := by
    have hpos : 0 < M / 2 := by omega
    exact_mod_cast hpos
  have hhalfUpper : ((M / 2 : ℕ) : ℝ) ≤ 12 * (6 : ℝ) ^ (30000 * k) := by
    have hnat : M / 2 ≤ 12 * 6 ^ (30000 * k) := by omega
    calc
      ((M / 2 : ℕ) : ℝ) ≤ ((12 * 6 ^ (30000 * k) : ℕ) : ℝ) := by exact_mod_cast hnat
      _ = 12 * (6 : ℝ) ^ (30000 * k) := by push_cast; ring
  have hsqrt := Growth.sqrt_log_le_mul_sqrt_succ (x := ((M / 2 : ℕ) : ℝ)) (c := 12)
    (G := 6) (s := 425) (m := 30000) (k := k) hhalfPos (by norm_num) (by norm_num)
    (by norm_num) hhalfUpper (by norm_num) (by norm_num)
  have ht : 4 * √(Real.log ((M / 2 : ℕ) : ℝ)) ≤ 1700 * √(((k + 1 : ℕ) : ℝ)) := by linarith
  have hMUpper : (M : ℝ) ≤ 24 * (d : ℝ) := by exact_mod_cast hupper
  have hcountReal : 3 * (S : ℝ) * (rothNumberNat (M / 2) : ℝ) ≤
      4 * ((M : ℝ) * (M : ℝ)) * (copies : ℝ) := by exact_mod_cast hcount
  -- Milestone M1 on the balanced certificate of length `30000k` and dimension `q^{9519k}`.
  have hbar : (copies : ℝ) * (((q : ℝ) ^ 19038) ^ k) ≤ (I ^ 30000) ^ k := by
    have hI := hcert.sq_le_asymptoticIndependenceNumber_pow K (by omega)
    calc (copies : ℝ) * (((q : ℝ) ^ 19038) ^ k)
        = (copies : ℝ) * (((q ^ (9519 * k) : ℕ) : ℝ)) ^ 2 := by
          push_cast
          rw [← pow_mul, ← pow_mul, show 9519 * k * 2 = 19038 * k from by ring]
      _ ≤ I ^ (30000 * k) := hI
      _ = (I ^ 30000) ^ k := by rw [pow_mul]
  have hcnt : 3 * ((P : ℝ) * (d : ℝ)) * (((q : ℝ) ^ 19038) ^ k) *
      (rothNumberNat (M / 2) : ℝ) ≤ 4 * ((I ^ 30000) ^ k) * ((M : ℝ) * (M : ℝ)) := by
    calc
      3 * ((P : ℝ) * (d : ℝ)) * (((q : ℝ) ^ 19038) ^ k) * (rothNumberNat (M / 2) : ℝ)
          = 3 * (S : ℝ) * (rothNumberNat (M / 2) : ℝ) * (((q : ℝ) ^ 19038) ^ k) := by
            rw [← hSP]; ring
      _ ≤ 4 * ((M : ℝ) * (M : ℝ)) * (copies : ℝ) * (((q : ℝ) ^ 19038) ^ k) :=
        mul_le_mul_of_nonneg_right hcountReal (by positivity)
      _ = 4 * ((M : ℝ) * (M : ℝ)) * ((copies : ℝ) * (((q : ℝ) ^ 19038) ^ k)) := by ring
      _ ≤ 4 * ((M : ℝ) * (M : ℝ)) * ((I ^ 30000) ^ k) :=
        mul_le_mul_of_nonneg_left hbar (by positivity)
      _ = 4 * ((I ^ 30000) ^ k) * ((M : ℝ) * (M : ℝ)) := by ring
  have hrate := Growth.le_mul_exp_of_mul_rothNumberNat_le (M := M)
    (a := 3 * ((P : ℝ) * (d : ℝ)) * (((q : ℝ) ^ 19038) ^ k))
    (b := 4 * ((I ^ 30000) ^ k))
    (U := 24 * (d : ℝ)) (t := 1700 * √(((k + 1 : ℕ) : ℝ)))
    (by omega) (by positivity) (by positivity) hMUpper ht hcnt
  have hremoveExp : (P : ℝ) * (((q : ℝ) ^ 19038) ^ k) ≤
      96 * Real.exp (1700 * √(((k + 1 : ℕ) : ℝ))) * ((I ^ 30000) ^ k) := by
    have hdReal : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hdPos
    refine le_of_mul_le_mul_right ?_ (show (0 : ℝ) < 3 * (d : ℝ) by positivity)
    calc
      (P : ℝ) * (((q : ℝ) ^ 19038) ^ k) * (3 * (d : ℝ))
          = 3 * ((P : ℝ) * (d : ℝ)) * (((q : ℝ) ^ 19038) ^ k) := by ring
      _ ≤ 3 * (4 * ((I ^ 30000) ^ k)) * (24 * (d : ℝ)) *
            Real.exp (1700 * √(((k + 1 : ℕ) : ℝ))) := hrate
      _ = 96 * Real.exp (1700 * √(((k + 1 : ℕ) : ℝ))) * ((I ^ 30000) ^ k) * (3 * (d : ℝ)) := by
            ring
  have hentropy := WordType.ternaryEntropyBase_pow_le_cubic_mul_multinomial
    10481 19038 481 k (by norm_num) (by norm_num) (by norm_num) hk
  rw [← card_cwFirstPowerMarginalTypeClass hk] at hentropy
  change WordType.ternaryEntropyBase 10481 19038 481 ^ k ≤
    WordType.ternaryMultinomialLoss 10481 19038 481 k * (P : ℝ) at hentropy
  rw [mul_pow]
  calc
    WordType.ternaryEntropyBase 10481 19038 481 ^ k * (((q : ℝ) ^ 19038) ^ k)
        ≤ (WordType.ternaryMultinomialLoss 10481 19038 481 k * (P : ℝ)) *
          (((q : ℝ) ^ 19038) ^ k) := by gcongr
    _ = WordType.ternaryMultinomialLoss 10481 19038 481 k *
          ((P : ℝ) * (((q : ℝ) ^ 19038) ^ k)) := by ring
    _ ≤ WordType.ternaryMultinomialLoss 10481 19038 481 k *
          (96 * Real.exp (1700 * √(((k + 1 : ℕ) : ℝ))) * ((I ^ 30000) ^ k)) :=
      mul_le_mul_of_nonneg_left hremoveExp (by
        unfold WordType.ternaryMultinomialLoss
        positivity)
    _ = _ := by unfold cwFirstPowerSubexponentialLoss; ring

/-- **[AlmanVassilevskaWilliams2018, Remark 7.3] in exact form.**  For every parameter `q = |μ|`
and every permutation `σ` of `μ`,

```text
H · q^{19038} ≤ Ī(CW_q^σ)^{30000},    H = ternaryEntropyBase 10481 19038 481.
```

Proof sketch: the `k → ∞` limit of `cwFirstPowerCoordinate_rate_inequality` through
`AlgebraicComplexity.Growth.le_of_pow_succ_le_subexponential_mul_pow_succ`, whose subexponential
input is `cwFirstPowerSubexponentialLoss_subexponential`. -/
theorem asymptoticIndependenceNumber_gcwTable_firstPower_lower (K : Type u) [CommSemiring K]
    [NoZeroDivisors K] [Nontrivial K] (μ : Type) [Fintype μ] [DecidableEq μ] (σ : Equiv.Perm μ)
    (hq : 0 < Fintype.card μ) :
    WordType.ternaryEntropyBase 10481 19038 481 * ((Fintype.card μ : ℝ) ^ 19038) ≤
      asymptoticIndependenceNumber (gcwTable K μ σ) ^ 30000 := by
  refine Growth.le_of_pow_succ_le_subexponential_mul_pow_succ
    (by positivity) cwFirstPowerSubexponentialLoss_subexponential ?_
  intro n
  exact cwFirstPowerCoordinate_rate_inequality K μ σ hq (k := n + 1) (by omega)

/-- **[AlmanVassilevskaWilliams2018, Remark 7.3] at the checked parameter `q = 6`**, in exact
form: `H · 6^{19038} ≤ Ī(CW_6^σ)^{30000}` with `H = ternaryEntropyBase 10481 19038 481`.  This is
`asymptoticIndependenceNumber_gcwTable_firstPower_lower` at `μ = Fin 6`; the readable numeric
consequence is `avw_remark_seven_three`. -/
theorem asymptoticIndependenceNumber_cwTable_six_lower (K : Type u) [CommSemiring K]
    [NoZeroDivisors K] [Nontrivial K] (σ : Equiv.Perm (Fin 6)) :
    WordType.ternaryEntropyBase 10481 19038 481 * (6 : ℝ) ^ 19038 ≤
      asymptoticIndependenceNumber (gcwTable K (Fin 6) σ) ^ 30000 := by
  have h := asymptoticIndependenceNumber_gcwTable_firstPower_lower K (Fin 6) σ (by simp)
  simpa only [Fintype.card_fin, Nat.cast_ofNat] using h

end BaseInequality

/-! ## The numeric value at `q = 6` -/

section Numeric

/-- **The ternary entropy base of a profile is a rational number.**  The factors of `e` in the
definition of `WordType.ternaryEntropyBase` cancel exactly, because the profile `(a,b,c)` sums to
the total `N` appearing in the numerator:

```text
ternaryEntropyBase a b c · (a^a · b^b · c^c) = N^N.
```

No positivity hypothesis is needed: `(0 : ℝ)^0 = 1`, so the denominator is never zero.  This is
what makes the numeric step below exact integer arithmetic. -/
theorem ternaryEntropyBase_mul_prod (a b c N : ℕ) (hN : a + b + c = N) :
    WordType.ternaryEntropyBase a b c * ((a : ℝ) ^ a * (b : ℝ) ^ b * (c : ℝ) ^ c)
      = (N : ℝ) ^ N := by
  subst hN
  have hE : (Real.exp 1) ≠ 0 := Real.exp_ne_zero 1
  have hne : ∀ n : ℕ, ((n : ℝ) ^ n) ≠ 0 := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | h
    · simp
    · exact pow_ne_zero _ (Nat.cast_ne_zero.mpr h.ne')
  have hY : (((a : ℝ) / Real.exp 1) ^ a * ((b : ℝ) / Real.exp 1) ^ b *
      ((c : ℝ) / Real.exp 1) ^ c) ≠ 0 := by
    simp only [div_pow]
    exact mul_ne_zero (mul_ne_zero (div_ne_zero (hne a) (pow_ne_zero _ hE))
      (div_ne_zero (hne b) (pow_ne_zero _ hE))) (div_ne_zero (hne c) (pow_ne_zero _ hE))
  have hstep : WordType.ternaryEntropyBase a b c *
      (((a : ℝ) / Real.exp 1) ^ a * ((b : ℝ) / Real.exp 1) ^ b * ((c : ℝ) / Real.exp 1) ^ c)
      = (((a + b + c : ℕ) : ℝ) / Real.exp 1) ^ (a + b + c) := by
    unfold WordType.ternaryEntropyBase
    exact div_mul_cancel₀ _ hY
  have hexpand : (((a : ℝ) / Real.exp 1) ^ a * ((b : ℝ) / Real.exp 1) ^ b *
      ((c : ℝ) / Real.exp 1) ^ c)
      = ((a : ℝ) ^ a * (b : ℝ) ^ b * (c : ℝ) ^ c) / (Real.exp 1) ^ (a + b + c) := by
    simp only [div_pow]
    rw [div_mul_div_comm, div_mul_div_comm, ← pow_add, ← pow_add]
  rw [hexpand, div_pow] at hstep
  have h2 := congrArg (fun x : ℝ ↦ x * (Real.exp 1) ^ (a + b + c)) hstep
  rwa [mul_assoc, div_mul_cancel₀ _ (pow_ne_zero _ hE),
    div_mul_cancel₀ _ (pow_ne_zero _ hE)] at h2

set_option exponentiation.threshold 100000 in
/-- **The exact integer inequality behind [AlmanVassilevskaWilliams2018, Remark 7.3].**

```text
6419^30000 · 10481^10481 · 19038^19038 · 481^481  ≤  1000^30000 · 30000^30000 · 6^19038.
```

Both sides have 239128 and 239129 decimal digits; the comparison is a single kernel `Nat.ble`
evaluation (no `decide` unfolding, no `native_decide`).  The left side is about `0.2107` times the
right side, i.e. the constant `6.419` has genuine slack: the exact limit value
`(H·6^{19038})^{1/30000}` is `6.41933327…`, and the same statement with `641933/100000` in place
of `6419/1000` is still true while `64194/10000` is false. -/
theorem cwFirstPower_six_numeric_bound :
    (6419 : ℕ) ^ 30000 * (10481 ^ 10481 * 19038 ^ 19038 * 481 ^ 481) ≤
      1000 ^ 30000 * (30000 ^ 30000 * 6 ^ 19038) :=
  Nat.le_of_ble_eq_true (Eq.refl true)

/-- The real form of `cwFirstPower_six_numeric_bound`. -/
theorem cwFirstPower_six_numeric_bound_real :
    (6419 : ℝ) ^ 30000 * ((10481 : ℝ) ^ 10481 * (19038 : ℝ) ^ 19038 * (481 : ℝ) ^ 481) ≤
      (1000 : ℝ) ^ 30000 * ((30000 : ℝ) ^ 30000 * (6 : ℝ) ^ 19038) := by
  exact_mod_cast cwFirstPower_six_numeric_bound

/-- **The numeric base inequality at `q = 6`**: `(6.419)^30000 ≤ H · 6^{19038}` with
`H = ternaryEntropyBase 10481 19038 481`.

Proof sketch: `ternaryEntropyBase_mul_prod` turns `H` into the rational
`30000^30000 / (10481^10481·19038^19038·481^481)`, after which the claim is
`cwFirstPower_six_numeric_bound`, an exact comparison of two integers. -/
theorem cwFirstPower_six_base_numeric :
    ((6 : ℝ) + 419 / 1000) ^ 30000 ≤
      WordType.ternaryEntropyBase 10481 19038 481 * (6 : ℝ) ^ 19038 := by
  have hD : (0 : ℝ) < (10481 : ℝ) ^ 10481 * (19038 : ℝ) ^ 19038 * (481 : ℝ) ^ 481 := by
    positivity
  have hent : WordType.ternaryEntropyBase 10481 19038 481 *
      ((10481 : ℝ) ^ 10481 * (19038 : ℝ) ^ 19038 * (481 : ℝ) ^ 481) = (30000 : ℝ) ^ 30000 := by
    have h := ternaryEntropyBase_mul_prod 10481 19038 481 30000 (by norm_num)
    simpa only [Nat.cast_ofNat] using h
  have hsix : ((6 : ℝ) + 419 / 1000) = 6419 / 1000 := by norm_num
  rw [hsix]
  refine le_of_mul_le_mul_right ?_ hD
  calc ((6419 : ℝ) / 1000) ^ 30000 *
        ((10481 : ℝ) ^ 10481 * (19038 : ℝ) ^ 19038 * (481 : ℝ) ^ 481)
      ≤ (30000 : ℝ) ^ 30000 * (6 : ℝ) ^ 19038 := by
        rw [div_pow, div_mul_eq_mul_div,
          div_le_iff₀ (by positivity : (0 : ℝ) < (1000 : ℝ) ^ 30000)]
        exact cwFirstPower_six_numeric_bound_real.trans (le_of_eq (mul_comm _ _))
    _ = (WordType.ternaryEntropyBase 10481 19038 481 *
          ((10481 : ℝ) ^ 10481 * (19038 : ℝ) ^ 19038 * (481 : ℝ) ^ 481)) * (6 : ℝ) ^ 19038 := by
        rw [hent]
    _ = (WordType.ternaryEntropyBase 10481 19038 481 * (6 : ℝ) ^ 19038) *
          ((10481 : ℝ) ^ 10481 * (19038 : ℝ) ^ 19038 * (481 : ℝ) ^ 481) := mul_right_comm _ _ _

/-- **[AlmanVassilevskaWilliams2018, Remark 7.3].**  For every permutation `σ` of the six middle
coordinates,

```text
6.419 ≤ Ī(CW_6^σ).
```

This improves the `6 + 6/25 = 6.24` of `avw_gcwTable_independence_sandwich_fin_six`, which comes
from the three-constituent easy analysis, to the six-constituent first-power analysis; the upper
half of that sandwich, `Ī(CW_6^σ) < 8`, is unchanged.

AVW display `6.4194…`.  With the rational type `(10481, 19038, 481)/30000` fixed by
`Examples/CoppersmithWinogradFirstPowerHashing.lean` the exact limit value is `6.41933327…`, so
`6.4194` is not available here; presumably it comes from the exact optimizer of the first-power
analysis rather than from a rational approximation to it.  Only `6 + 419/1000` is claimed. -/
theorem avw_remark_seven_three (K : Type u) [CommSemiring K] [NoZeroDivisors K] [Nontrivial K]
    (σ : Equiv.Perm (Fin 6)) :
    (6 : ℝ) + 419 / 1000 ≤ asymptoticIndependenceNumber (gcwTable K (Fin 6) σ) := by
  exact le_of_pow_le_pow_left₀ (n := 30000) (by norm_num)
    (asymptoticIndependenceNumber_nonneg _)
    (cwFirstPower_six_base_numeric.trans (asymptoticIndependenceNumber_cwTable_six_lower K σ))

end Numeric

end AlgebraicComplexity.Examples
