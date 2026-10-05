/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoCopyCount
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoCounting

/-!
# Per-orientation typicality of a six-orientation block word

Layer 4 (`AlgebraicComplexity/Examples/`).  The count lane's marked family
`markedWords : Finset (PositiveWord ((dwz63SymSixPartition K).support) n)` is the interface
between three lanes: the count lane needs its cardinality and the marginal types of its words, and
the values lane needs every marked word's *per-orientation* letter type in order to read the leaf
weight off `dwz63Alpha`.  This module fixes that shared predicate.

## The six oriented sub-words

A block label of `dwz63SymSixPartition K` is a six-tuple of coarse Coppersmith--Winograd square
degrees per leg, one entry per leg permutation, in the association
`((id, cycle), cycle⁻¹), ((s, cycle·s), cycle⁻¹·s)` of `PartitionedTensor.symSixPartition`.  The
`o`-th entry lives in `PermutedBlockIndex e_o`, so reading it *in the source partition's own
address space* means reading the label at leg `e_o c` --- this is
`permuteBlockAddress_symm_apply_apply`, and it is exactly the un-permutation that makes the `X`
and `Z` marginals of the resulting letter the published profiles `dwz63AlphaX`, `dwz63AlphaZ`
rather than permuted copies of them.  `dwz63SourceLetter` performs it; `dwz63OrientedWord` reads
the whole word one orientation at a time, through `positiveWordEquiv`.

## The predicate

`Dwz63OrientationTypical K n t q` says all six oriented sub-words of `q` have the *same* letter
type, `WordType.proportionalCounts dwz63AlphaAddress t`, where `dwz63AlphaAddress` is the fifteen
entry table `dwz63Alpha` pushed onto the coarse square's own address space along
`dwz63CellAddress`.  `dwz63OrientationTypical_length` records the arithmetic this forces:
`n + 1 = 10 ^ 8 * t`, which is the `10 ^ 8 ∣ n + 1` divisibility of
`Examples/DuanWuZhouLevelTwoCofinalIndex.lean`, derived rather than assumed.

Because `WordType.mappedType dwz63XIndex dwz63Alpha = dwz63AlphaX` and
`WordType.mappedType dwz63ZIndex dwz63Alpha = dwz63AlphaZ` are committed in
`Examples/DuanWuZhouLevelTwoCounting.lean`, a family satisfying this predicate has exactly the
marginal types the hashing count and the leaf value both read.

Primary source: Ran Duan, Hongxun Wu and Renfei Zhou, *Faster Matrix Multiplication via Asymmetric
Hashing*, arXiv:2210.10173, section 6.3.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor
open scoped BigOperators

universe u v

/-! ## The fifteen cells as coarse square addresses -/

/-- **The `i`-th cell of `table:result-2nd` as a coarse Coppersmith--Winograd square address**, the
degree triple `(dwz63XIndex i, dwz63YIndex i, dwz63ZIndex i)`. -/
def dwz63CellAddress (i : Fin 15) : CWSquareAddress := fun leg ↦
  match leg with
  | .X => dwz63XIndex i
  | .Y => dwz63YIndex i
  | .Z => dwz63ZIndex i

/-- **`dwz63Alpha` on the coarse square's own address space.**  The fifteen-entry table pushed
forward along `dwz63CellAddress`; every address off the antidiagonal gets multiplicity zero. -/
noncomputable def dwz63AlphaAddress : CWSquareAddress → ℕ :=
  WordType.mappedType dwz63CellAddress dwz63Alpha

/-- **The pushforward keeps the total mass `10 ^ 8`.**  So a word typical for
`dwz63AlphaAddress` at scale `t` has length `10 ^ 8 * t`. -/
theorem profileMass_dwz63AlphaAddress :
    WordType.profileMass dwz63AlphaAddress = 100000000 := by
  unfold dwz63AlphaAddress
  rw [WordType.profileMass_mappedType, profileMass_dwz63Alpha]

/-! ## The six oriented letters of one block label -/

/-- **The `o`-th oriented coarse letter of a six-orientation block label, in the source
partition's own address space.**

The six leg permutations of `PartitionedTensor.symSixPartition` are, in order,
`1, cycle, cycle⁻¹, s, cycle·s, cycle⁻¹·s` with `s = swapXY`, and the `o`-th component of a
permuted address is read at the permuted leg --- `permuteBlockAddress_symm_apply_apply`. -/
def dwz63SourceLetter : Fin 6 → BlockAddress DwzSymSixBlock → CWSquareAddress :=
  ![fun s c ↦ (s c).1.1.1,
    fun s c ↦ (s (cycle c)).1.1.2,
    fun s c ↦ (s (cycle.symm c)).1.2,
    fun s c ↦ (s (swapXY c)).2.1.1,
    fun s c ↦ (s ((cycle.trans swapXY) c)).2.1.2,
    fun s c ↦ (s ((cycle.symm.trans swapXY) c)).2.2]

/-- **The `o`-th oriented coarse sub-word of a six-orientation block word**, as a function on the
`n + 1` positions.  This is the object the values lane reads its leaf weight from and the count
lane takes marginal types of. -/
noncomputable def dwz63OrientedWord (K : Type u) [CommRing K] (n : ℕ) (o : Fin 6)
    (q : PositiveWord ((dwz63SymSixPartition K).support) n) : Fin (n + 1) → CWSquareAddress :=
  fun j ↦ dwz63SourceLetter o (positiveWordEquiv _ n q j).val

/-! ## Typicality -/

/-- **The marked family's defining predicate.**

Every one of the six oriented sub-words of `q` has letter type
`WordType.proportionalCounts dwz63AlphaAddress t`: the `dwz63Alpha` table repeated `t` times.
This is the *joint* typicality `[DuanWuZhou2022]` section 6.3 marks with, read one orientation at
a time, and it is simultaneously

* the count lane's input --- its `X`- and `Z`-marginal types are then
  `WordType.proportionalCounts dwz63AlphaX t` and `WordType.proportionalCounts dwz63AlphaZ t`, by
  `mappedType_dwz63XIndex_proportionalCounts` and `mappedType_dwz63ZIndex_proportionalCounts`;
* the values lane's input --- the constituent at a typical word is the one-period base raised to
  the scale. -/
def Dwz63OrientationTypical (K : Type u) [CommRing K] (n t : ℕ)
    (q : PositiveWord ((dwz63SymSixPartition K).support) n) : Prop :=
  ∀ o : Fin 6,
    WordType.multiplicity (dwz63OrientedWord K n o q) =
      WordType.proportionalCounts dwz63AlphaAddress t

/-- **The word length is forced.**  A typical word at scale `t` has `n + 1 = 10 ^ 8 * t`
positions, so `10 ^ 8 ∣ n + 1`: the divisibility `dwz63CofinalIndex` builds in is a *consequence*
of typicality, not an extra assumption. -/
theorem dwz63OrientationTypical_length {K : Type u} [CommRing K] {n t : ℕ}
    {q : PositiveWord ((dwz63SymSixPartition K).support) n}
    (h : Dwz63OrientationTypical K n t q) : n + 1 = 100000000 * t := by
  have hsum := WordType.sum_multiplicity (dwz63OrientedWord K n 0 q)
  rw [h 0] at hsum
  have hprofile : ∑ a : CWSquareAddress, WordType.proportionalCounts dwz63AlphaAddress t a =
      100000000 * t := by
    unfold WordType.proportionalCounts
    rw [← Finset.sum_mul]
    rw [show (∑ a : CWSquareAddress, dwz63AlphaAddress a) =
      WordType.profileMass dwz63AlphaAddress from rfl, profileMass_dwz63AlphaAddress]
  omega

/-- **The typical family**, as a `Finset`: this is the canonical choice of `markedWords`. -/
noncomputable def dwz63TypicalWords (K : Type u) [CommRing K] (n t : ℕ) :
    Finset (PositiveWord ((dwz63SymSixPartition K).support) n) := by
  classical
  exact Finset.univ.filter (Dwz63OrientationTypical K n t)

theorem mem_dwz63TypicalWords {K : Type u} [CommRing K] {n t : ℕ}
    {q : PositiveWord ((dwz63SymSixPartition K).support) n} :
    q ∈ dwz63TypicalWords K n t ↔ Dwz63OrientationTypical K n t q := by
  classical
  simp [dwz63TypicalWords]

/-- **The interface obligation, discharged for the canonical choice.**  Any `markedWords` a client
supplies has to sit inside the typical family; the canonical one does, by definition. -/
theorem dwz63TypicalWords_orientationTypical (K : Type u) [CommRing K] (n t : ℕ) :
    ∀ q ∈ dwz63TypicalWords K n t, Dwz63OrientationTypical K n t q :=
  fun _ hq ↦ mem_dwz63TypicalWords.mp hq

/-- Every subfamily of the typical family is typical.  This is the form the values lane consumes:
the count lane is free to shrink `markedWords` without renegotiating the interface. -/
theorem orientationTypical_of_subset {K : Type u} [CommRing K] {n t : ℕ}
    {markedWords : Finset (PositiveWord ((dwz63SymSixPartition K).support) n)}
    (hsub : markedWords ⊆ dwz63TypicalWords K n t) :
    ∀ q ∈ markedWords, Dwz63OrientationTypical K n t q :=
  fun _ hq ↦ mem_dwz63TypicalWords.mp (hsub hq)

/-! ## Anti-vacuity: the six projections land in the coarse support -/

set_option maxRecDepth 8000 in
set_option maxHeartbeats 1000000 in
set_option linter.constructorNameAsVariable false in
/-- **Every oriented letter of a block label of the six-orientation partition is a genuine coarse
Coppersmith--Winograd square address.**

This is the check that `dwz63SourceLetter` un-permutes in the right direction: the `o`-th
component of a `symSixPartition` label lives in `PermutedBlockIndex e_o`, so it is a source
address only after transport by `(permuteBlockAddress e_o).symm`, which reads it at leg `e_o c`.
Had the transport gone the other way the projection would leave `cwSquareSupport` --- the fifteen
degree triples summing to four are not permutation-invariant as a *labelled* family --- so this
statement pins the convention rather than merely documenting it. -/
theorem dwz63SourceLetter_mem_cwSquareSupport (K : Type u) [CommRing K]
    (w : BlockAddress DwzSymSixBlock) (hw : w ∈ (dwz63SymSixPartition K).support) (o : Fin 6) :
    dwz63SourceLetter o w ∈ cwSquareSupport := by
  classical
  have hperm : ∀ (e : Orientation)
      (t : BlockAddress (PermutedBlockIndex e fun _ : Leg ↦ Fin 5)) (c : Leg),
      (permuteBlockAddress e).symm t c = t (e c) := by
    intro e t c
    have h := permuteBlockAddress_symm_apply_apply (A := fun _ : Leg ↦ Fin 5) e t (e c)
    rwa [Equiv.symm_apply_apply] at h
  rw [dwz63SymSixPartition, PartitionedTensor.symSixPartition,
    PartitionedTensor.symThreePartition, PartitionedTensor.swapSymThreePartition] at hw
  simp only [PartitionedTensor.mem_external_support, PartitionedTensor.mem_permute_support,
    cwSquarePartitionedTensor_support] at hw
  obtain ⟨⟨⟨h0, h1⟩, h2⟩, ⟨h3, h4⟩, h5⟩ := hw
  have e1 : ((permuteBlockAddress cycle).symm fun c ↦ (w c).1.1.2)
      = fun c ↦ (w (cycle c)).1.1.2 := funext fun c ↦ hperm cycle _ c
  have e2 : ((permuteBlockAddress cycle.symm).symm fun c ↦ (w c).1.2)
      = fun c ↦ (w (cycle.symm c)).1.2 := funext fun c ↦ hperm cycle.symm _ c
  have e3 : ((permuteBlockAddress swapXY).symm fun c ↦ (w c).2.1.1)
      = fun c ↦ (w (swapXY c)).2.1.1 := funext fun c ↦ hperm swapXY _ c
  have e4 : ((permuteBlockAddress (cycle.trans swapXY)).symm fun c ↦ (w c).2.1.2)
      = fun c ↦ (w ((cycle.trans swapXY) c)).2.1.2 :=
    funext fun c ↦ hperm (cycle.trans swapXY) _ c
  have e5 : ((permuteBlockAddress (cycle.symm.trans swapXY)).symm fun c ↦ (w c).2.2)
      = fun c ↦ (w ((cycle.symm.trans swapXY) c)).2.2 :=
    funext fun c ↦ hperm (cycle.symm.trans swapXY) _ c
  rw [e1] at h1
  rw [e2] at h2
  rw [e3] at h3
  rw [e4] at h4
  rw [e5] at h5
  fin_cases o
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4
  · exact h5

end AlgebraicComplexity.Examples
