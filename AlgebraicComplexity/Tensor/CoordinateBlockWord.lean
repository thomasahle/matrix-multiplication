/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Tensor.IndependenceNumber
import AlgebraicComplexity.Tensor.PartitionedDirectSum

/-!
# Coordinate block words: the coordinate twin of partitioned extraction

Layer 1 (`AlgebraicComplexity/Tensor/`).  This module is milestone **M3** of
`BARRIER_FRAMEWORK.md`.

The laser-method extraction chain of this repository is stated for *abstract* tensors: a
`PartitionedTensor` is zeroed down to a selected set of block addresses
(`Tensor.Restricts.partitionedUniqueLegFibers`, from `HasUniqueLegFibers`) and the survivors are
then folded into an indexed direct sum
(`Tensor.Restricts.partitionedLegwiseInjective_to_indexedDirectSum`, from `IsLegwiseInjective`).
The independence number `Tensor.independenceNumber` of the Alman--Vassilevska Williams barrier
program is, by contrast, a function of a *coefficient table*: it is not an isomorphism invariant,
so nothing about it can be read off an abstract restriction.  A barrier statement about an
extraction therefore needs a coordinate-level shadow of that chain, which is what this file is.

## The correspondence

Fix a coefficient table `T : (∀ i, κ i) → K` and a **block labelling** `blk i : κ i → A i` of the
variables of each leg.  A triple of length-`n` words `p : ∀ i, Fin n → κ i` --- a variable triple
of the Kronecker power `Tensor.coordinatePower T n` --- has a **block word**
`coordinateBlockWord blk p : ∀ i, Fin n → A i`, obtained by applying `blk` positionwise.  A block
word is a `Tensor.BlockAddress` for the alphabets `fun i ↦ Fin n → A i`, so the two combinatorial
predicates of the abstract chain apply to a finite set `S` of block words *verbatim*, and all the
hashing combinatorics that produces such an `S` transfers unchanged:

| abstract chain | coordinate twin |
| --- | --- |
| `PartitionedTensor.select` / `Restricts.partitionedSelect` | `Tensor.coordinateZeroOut` |
| `HasUniqueLegFibers ambient S pivot` | `coordinateBlockZeroOut_eq_coordinateZeroOut_of_hasUniqueLegFibers` |
| `IsLegwiseInjective S` | `coordinateBlockZeroOut_eq_extend_directSum_of_isLegwiseInjective` |
| `realizePartition` of the constituents | `Tensor.coordinateDirectSum` of `coordinateBlockWordConstituent` |
| the constituent at a block address | `coordinateBlockWordTable`, a plain product over `Fin n` |

No `TensorProduct` reassociation occurs anywhere: `Tensor.coordinatePower` is already indexed by
words, so the constituent selected by a block word is the *plain product over positions* of the
block sub-tables `coordinateBlock`, and `coordinateBlockWordTable_const` reduces the constant
block word to `Tensor.coordinatePower (coordinateBlock T blk a) n`.

## Main definitions

* `coordinateBlockWord blk p`, `coordinateBlockLegWord blk i w`: the block word of a triple of
  words, and of one leg's word.
* `coordinateBlock T blk a`: the block sub-table of `T` at a block address; it is a zeroing out
  (`coordinateBlock_eq_coordinateZeroOut`).
* `coordinateBlockWordTable T blk s`: the constituent selected by the block word `s`, the
  positionwise product (`Tensor.coordinateWordProduct`) of the block sub-tables.
* `coordinateBlockWordConstituent T blk emb s`: that constituent read in its own variables, along
  legwise maps `emb` into the words.
* `coordinateBlockZeroOut T blk n S`: the entries of `Tensor.coordinatePower T n` whose block word
  lies in `S`, everything else set to `0`.
* `coordinateBlockFiber blk i B`: the words of leg `i` whose block word lies in `B`; the legwise
  variable sets of the zeroing out.

## Main results

* `coordinateBlockZeroOut_eq_coordinateZeroOut`: **the block zeroing out is a zeroing out.**  Given
  legwise sets `B i` of block words that contain the legwise projections of `S` and whose common
  preimage meets the support of the power only inside `S`, the block zeroing out is literally
  `Tensor.coordinateZeroOut` of the power at the legwise variable sets `coordinateBlockFiber blk i (B i)`.
  The second hypothesis is the coordinate form of `IsProjectionClosed` with all legs active, taken
  relative to the support of `coordinatePower T n`; a *triple* set `S` is not a product of three
  leg sets, so some such rectangularity hypothesis is unavoidable.
* `coordinateBlockZeroOut_eq_coordinateZeroOut_of_hasUniqueLegFibers`: the same identification from
  `HasUniqueLegFibers ambient S pivot` --- zeroing out *one* leg suffices --- mirroring
  `Restricts.partitionedUniqueLegFibers`.
* `coordinateBlockZeroOut_eq_extend_directSum`: **the block zeroing out is a block table.**  Under
  legwise injectivity of the selected block words, and given legwise embeddings of the constituent
  variables that respect blocks and cover the fibers used by `S`, the block zeroing out equals
  `Tensor.coordinateExtend emb ret (Tensor.coordinateDirectSum ...)`.  This is the coordinate twin
  of `Restricts.partitionedLegwiseInjective_to_indexedDirectSum`, and it is exactly the right-hand
  side of `AlgebraicComplexity.CoordinateGalacticCertificate`.
* `independenceNumber_coordinateBlockZeroOut_le` and `independenceNumber_coordinateBlockZeroOut`:
  the two consequences for `Tensor.independenceNumber`, from
  `independenceNumber_coordinateZeroOut_le`, `independenceNumber_coordinateExtend` and
  `independenceNumber_coordinateDirectSum`.

## Position in the library

Layer 1.  It imports only `Tensor/IndependenceNumber.lean` (the coordinate calculus:
`coordinateZeroOut`, `coordinateExtend`, `coordinateDirectSum`, `coordinateRelabel`,
`coordinatePower`) and `Tensor/PartitionedDirectSum.lean` (the two combinatorial predicates
`HasUniqueLegFibers` and `IsLegwiseInjective`, and `Tensor.BlockAddress`).  Nothing here mentions a
named construction or a numerical bound.
-/

namespace AlgebraicComplexity.Tensor

universe u v

section BlockWords

variable {K : Type u} [CommSemiring K] {κ : Leg → Type v} {A : Leg → Type v}

/-- The **block word** of one leg's word: apply the block labelling of that leg positionwise. -/
def coordinateBlockLegWord (blk : ∀ i, κ i → A i) (i : Leg) {n : ℕ} (w : Fin n → κ i) :
    Fin n → A i :=
  fun t ↦ blk i (w t)

/-- The letters of a block word are the block labels of the letters. -/
@[simp] theorem coordinateBlockLegWord_apply (blk : ∀ i, κ i → A i) (i : Leg) {n : ℕ}
    (w : Fin n → κ i) (t : Fin n) : coordinateBlockLegWord blk i w t = blk i (w t) := rfl

/-- The **block word of a variable triple** of `coordinatePower T n`: the legwise block words,
packaged as a `BlockAddress` for the block alphabets `fun i ↦ Fin n → A i`.  This is the index at
which the abstract predicates `HasUniqueLegFibers` and `IsLegwiseInjective` are reused. -/
def coordinateBlockWord (blk : ∀ i, κ i → A i) {n : ℕ} (p : ∀ i, Fin n → κ i) :
    BlockAddress fun i ↦ Fin n → A i :=
  fun i ↦ coordinateBlockLegWord blk i (p i)

/-- The block word of a triple is the legwise block word. -/
@[simp] theorem coordinateBlockWord_apply (blk : ∀ i, κ i → A i) {n : ℕ}
    (p : ∀ i, Fin n → κ i) (i : Leg) :
    coordinateBlockWord blk p i = coordinateBlockLegWord blk i (p i) := rfl

variable [∀ i, DecidableEq (A i)]

/-- The **block sub-table** of `T` at a block address: the entries of `T` all of whose variables
carry the prescribed block label, and `0` elsewhere. -/
def coordinateBlock (T : (∀ i, κ i) → K) (blk : ∀ i, κ i → A i) (a : BlockAddress A) :
    (∀ i, κ i) → K :=
  fun q ↦ if ∀ i, blk i (q i) = a i then T q else 0

/-- Inside its block, the block sub-table is the original table. -/
theorem coordinateBlock_of_mem {T : (∀ i, κ i) → K} {blk : ∀ i, κ i → A i} {a : BlockAddress A}
    {q : ∀ i, κ i} (h : ∀ i, blk i (q i) = a i) : coordinateBlock T blk a q = T q :=
  if_pos h

/-- Outside its block, the block sub-table vanishes. -/
theorem coordinateBlock_of_notMem {T : (∀ i, κ i) → K} {blk : ∀ i, κ i → A i} {a : BlockAddress A}
    {q : ∀ i, κ i} (h : ¬ ∀ i, blk i (q i) = a i) : coordinateBlock T blk a q = 0 :=
  if_neg h

/-- **A block sub-table is a zeroing out**: it keeps precisely the variables of the prescribed
block on each leg.  This is the letterwise case of `coordinateBlockZeroOut_eq_coordinateZeroOut`. -/
theorem coordinateBlock_eq_coordinateZeroOut [∀ i, Fintype (κ i)] [∀ i, DecidableEq (κ i)]
    (T : (∀ i, κ i) → K) (blk : ∀ i, κ i → A i) (a : BlockAddress A) :
    coordinateBlock T blk a =
      coordinateZeroOut T fun i ↦ Finset.univ.filter fun x ↦ blk i x = a i := by
  funext q
  by_cases h : ∀ i, blk i (q i) = a i
  · rw [coordinateBlock_of_mem h, coordinateZeroOut_of_mem]
    intro i
    simpa using h i
  · rw [coordinateBlock_of_notMem h, coordinateZeroOut_of_notMem]
    intro hmem
    exact h fun i ↦ by simpa using hmem i

/-- The **constituent selected by a block word**: the plain product over the `n` positions of the
block sub-tables prescribed by the letters of the word.  It is the coordinate twin of a
constituent of a `PartitionedTensor`, and no `TensorProduct` reassociation is involved --- the
variables of `coordinatePower T n` are already words.  It is the positionwise product
`Tensor.coordinateWordProduct` of the block sub-tables; the index family happens to be constant in
the position, so no transport of index types is involved. -/
def coordinateBlockWordTable (T : (∀ i, κ i) → K) (blk : ∀ i, κ i → A i) {n : ℕ}
    (s : BlockAddress fun i ↦ Fin n → A i) : (∀ i, Fin n → κ i) → K :=
  coordinateWordProduct fun t ↦ coordinateBlock T blk fun i ↦ s i t

/-- The constituent selected by a block word, as a product over the positions of the word. -/
@[simp] theorem coordinateBlockWordTable_apply (T : (∀ i, κ i) → K) (blk : ∀ i, κ i → A i) {n : ℕ}
    (s : BlockAddress fun i ↦ Fin n → A i) (p : ∀ i, Fin n → κ i) :
    coordinateBlockWordTable T blk s p =
      ∏ t : Fin n, coordinateBlock T blk (fun i ↦ s i t) fun i ↦ p i t :=
  coordinateWordProduct_apply _ p

/-- On its own block word the constituent is the Kronecker power. -/
theorem coordinateBlockWordTable_of_eq {T : (∀ i, κ i) → K} {blk : ∀ i, κ i → A i} {n : ℕ}
    {s : BlockAddress fun i ↦ Fin n → A i} {p : ∀ i, Fin n → κ i}
    (h : coordinateBlockWord blk p = s) :
    coordinateBlockWordTable T blk s p = coordinatePower T n p := by
  rw [coordinateBlockWordTable_apply, coordinatePower_apply]
  refine Finset.prod_congr rfl fun t _ ↦ coordinateBlock_of_mem fun i ↦ ?_
  exact congrFun (congrFun h i) t

/-- A constituent vanishes off its own block word: a single mismatched letter kills the product. -/
theorem coordinateBlockWordTable_of_ne {T : (∀ i, κ i) → K} {blk : ∀ i, κ i → A i} {n : ℕ}
    {s : BlockAddress fun i ↦ Fin n → A i} {p : ∀ i, Fin n → κ i}
    (h : coordinateBlockWord blk p ≠ s) : coordinateBlockWordTable T blk s p = 0 := by
  rw [coordinateBlockWordTable_apply]
  obtain ⟨i, hi⟩ := Function.ne_iff.mp h
  obtain ⟨t, ht⟩ := Function.ne_iff.mp hi
  refine Finset.prod_eq_zero (Finset.mem_univ t) (coordinateBlock_of_notMem ?_)
  intro hall
  exact ht (hall i)

/-- The constituent selected by a block word, in closed form. -/
theorem coordinateBlockWordTable_eq_ite (T : (∀ i, κ i) → K) (blk : ∀ i, κ i → A i) {n : ℕ}
    (s : BlockAddress fun i ↦ Fin n → A i) (p : ∀ i, Fin n → κ i) :
    coordinateBlockWordTable T blk s p =
      if coordinateBlockWord blk p = s then coordinatePower T n p else 0 := by
  by_cases h : coordinateBlockWord blk p = s
  · rw [if_pos h, coordinateBlockWordTable_of_eq h]
  · rw [if_neg h, coordinateBlockWordTable_of_ne h]

/-- **The same block at every position gives a Kronecker power**: the constituent selected by a
constant block word is the `n`-th power of that block sub-table.  This is the constant-family case
`Tensor.coordinateWordProduct_const` of the positionwise product. -/
theorem coordinateBlockWordTable_const (T : (∀ i, κ i) → K) (blk : ∀ i, κ i → A i) (n : ℕ)
    (a : BlockAddress A) :
    coordinateBlockWordTable T blk (n := n) (fun i _ ↦ a i) =
      coordinatePower (coordinateBlock T blk a) n :=
  coordinateWordProduct_const _ n

/-- The constituent selected by a block word, **read in its own variables** along legwise maps
`emb` into the words of the power.  In an extraction `emb` is the legwise injection that lists the
variables of one surviving constituent; `coordinateBlockWordConstituent_eq_coordinatePower` says
that when `emb` respects blocks this is just the power restricted to those variables. -/
def coordinateBlockWordConstituent (T : (∀ i, κ i) → K) (blk : ∀ i, κ i → A i) {n : ℕ}
    {ν : Leg → Type v} (emb : ∀ i, ν i → (Fin n → κ i))
    (s : BlockAddress fun i ↦ Fin n → A i) : (∀ i, ν i) → K :=
  fun q ↦ coordinateBlockWordTable T blk s fun i ↦ emb i (q i)

/-- The constituent in its own variables is the constituent table at the listed words. -/
@[simp] theorem coordinateBlockWordConstituent_apply (T : (∀ i, κ i) → K) (blk : ∀ i, κ i → A i)
    {n : ℕ} {ν : Leg → Type v} (emb : ∀ i, ν i → (Fin n → κ i))
    (s : BlockAddress fun i ↦ Fin n → A i) (q : ∀ i, ν i) :
    coordinateBlockWordConstituent T blk emb s q =
      coordinateBlockWordTable T blk s fun i ↦ emb i (q i) := rfl

/-- **Block-respecting variables see only the power**: if every listed variable of leg `i` has
block word `s i`, the constituent is the Kronecker power restricted to those variables. -/
theorem coordinateBlockWordConstituent_eq_coordinatePower (T : (∀ i, κ i) → K)
    (blk : ∀ i, κ i → A i) {n : ℕ} {ν : Leg → Type v} {emb : ∀ i, ν i → (Fin n → κ i)}
    {s : BlockAddress fun i ↦ Fin n → A i}
    (hblock : ∀ i x, coordinateBlockLegWord blk i (emb i x) = s i) :
    coordinateBlockWordConstituent T blk emb s =
      fun q ↦ coordinatePower T n fun i ↦ emb i (q i) := by
  funext q
  exact coordinateBlockWordTable_of_eq (funext fun i ↦ hblock i (q i))

end BlockWords

/-! ## The block zeroing out

`coordinateBlockZeroOut T blk n S` keeps exactly the entries of `coordinatePower T n` whose block
word lies in `S`.  The two identification theorems below say what it is: a zeroing out of the
power, and a block table of constituents. -/

section BlockZeroOut

variable {K : Type u} [CommSemiring K] {κ : Leg → Type v} {A : Leg → Type v}
variable [∀ i, DecidableEq (A i)]

/-- The **block zeroing out** of a Kronecker power: keep exactly the entries of
`coordinatePower T n` whose legwise block words form a triple in `S`, and set every other entry to
`0`.  `coordinateBlockZeroOut_eq_coordinateZeroOut` identifies it with a genuine
`Tensor.coordinateZeroOut`, which is what makes `Tensor.independenceNumber` monotone along it. -/
def coordinateBlockZeroOut (T : (∀ i, κ i) → K) (blk : ∀ i, κ i → A i) (n : ℕ)
    (S : Finset (BlockAddress fun i ↦ Fin n → A i)) : (∀ i, Fin n → κ i) → K :=
  fun p ↦ if coordinateBlockWord blk p ∈ S then coordinatePower T n p else 0

/-- A selected block word contributes its power entry. -/
theorem coordinateBlockZeroOut_of_mem {T : (∀ i, κ i) → K} {blk : ∀ i, κ i → A i} {n : ℕ}
    {S : Finset (BlockAddress fun i ↦ Fin n → A i)} {p : ∀ i, Fin n → κ i}
    (h : coordinateBlockWord blk p ∈ S) :
    coordinateBlockZeroOut T blk n S p = coordinatePower T n p :=
  if_pos h

/-- An unselected block word contributes nothing. -/
theorem coordinateBlockZeroOut_of_notMem {T : (∀ i, κ i) → K} {blk : ∀ i, κ i → A i} {n : ℕ}
    {S : Finset (BlockAddress fun i ↦ Fin n → A i)} {p : ∀ i, Fin n → κ i}
    (h : coordinateBlockWord blk p ∉ S) : coordinateBlockZeroOut T blk n S p = 0 :=
  if_neg h

/-- Every surviving term of a block zeroing out is a term of the power with a selected block
word. -/
theorem coordinateBlockZeroOut_ne_zero {T : (∀ i, κ i) → K} {blk : ∀ i, κ i → A i} {n : ℕ}
    {S : Finset (BlockAddress fun i ↦ Fin n → A i)} {p : ∀ i, Fin n → κ i}
    (h : coordinateBlockZeroOut T blk n S p ≠ 0) :
    coordinatePower T n p ≠ 0 ∧ coordinateBlockWord blk p ∈ S := by
  by_cases hmem : coordinateBlockWord blk p ∈ S
  · exact ⟨by rwa [coordinateBlockZeroOut_of_mem hmem] at h, hmem⟩
  · exact absurd (coordinateBlockZeroOut_of_notMem hmem) h

variable [∀ i, Fintype (κ i)] [∀ i, DecidableEq (κ i)]

/-- The words of leg `i` whose block word lies in `B`: the legwise variable set of a block zeroing
out.  It is the word-level analogue of the letterwise fiber used in
`coordinateBlock_eq_coordinateZeroOut`. -/
def coordinateBlockFiber (blk : ∀ i, κ i → A i) (i : Leg) {n : ℕ} (B : Finset (Fin n → A i)) :
    Finset (Fin n → κ i) :=
  Finset.univ.filter fun w ↦ coordinateBlockLegWord blk i w ∈ B

omit [∀ i, DecidableEq (κ i)] in
/-- Membership in the fiber of a set of block words. -/
@[simp] theorem mem_coordinateBlockFiber {blk : ∀ i, κ i → A i} {i : Leg} {n : ℕ}
    {B : Finset (Fin n → A i)} {w : Fin n → κ i} :
    w ∈ coordinateBlockFiber blk i B ↔ coordinateBlockLegWord blk i w ∈ B := by
  simp [coordinateBlockFiber]

/-- **A block zeroing out is a zeroing out** (the coordinate twin of
`Tensor.Restricts.partitionedSelect`).

The legwise variable sets are the fibers of legwise sets `B i` of block words.  Since a set `S` of
block-word *triples* is not a product of three leg sets, an identification of this kind needs `S`
to be cut out from the support of the power by legwise data; the two hypotheses are exactly that,
and no more:

* `hsub`: `B i` contains the `i`-th projection of `S`, so no selected term is lost;
* `hclosed`: a *support* triple of the power all of whose legwise block words are selected by `B`
  already has its block word in `S`, so no cross term is gained.

`hclosed` is the coordinate form of `IsProjectionClosed` with all legs active, taken relative to
the support of `coordinatePower T n`; both hypotheses are used only on that support. -/
theorem coordinateBlockZeroOut_eq_coordinateZeroOut (T : (∀ i, κ i) → K) (blk : ∀ i, κ i → A i)
    {n : ℕ} (S : Finset (BlockAddress fun i ↦ Fin n → A i)) (B : ∀ i, Finset (Fin n → A i))
    (hsub : ∀ s ∈ S, ∀ i, s i ∈ B i)
    (hclosed : ∀ p : ∀ i, Fin n → κ i, coordinatePower T n p ≠ 0 →
      (∀ i, coordinateBlockWord blk p i ∈ B i) → coordinateBlockWord blk p ∈ S) :
    coordinateBlockZeroOut T blk n S =
      coordinateZeroOut (coordinatePower T n) fun i ↦ coordinateBlockFiber blk i (B i) := by
  funext p
  by_cases hmem : coordinateBlockWord blk p ∈ S
  · rw [coordinateBlockZeroOut_of_mem hmem, coordinateZeroOut_of_mem]
    intro i
    exact mem_coordinateBlockFiber.mpr (hsub _ hmem i)
  · rw [coordinateBlockZeroOut_of_notMem hmem]
    by_cases hfiber : ∀ i, p i ∈ coordinateBlockFiber blk i (B i)
    · rw [coordinateZeroOut_of_mem hfiber]
      by_contra hne
      exact hmem (hclosed p (fun h ↦ hne h.symm) fun i ↦ mem_coordinateBlockFiber.mp (hfiber i))
    · rw [coordinateZeroOut_of_notMem hfiber]

variable [∀ i, Fintype (A i)]

/-- The legwise block-word sets of a **single-leg** zeroing out: everything on the legs other than
`pivot`, and just the `pivot`-projections of `S` on the pivot leg. -/
def coordinateBlockPivotWords {n : ℕ} (S : Finset (BlockAddress fun i ↦ Fin n → A i))
    (pivot : Leg) (i : Leg) : Finset (Fin n → A i) :=
  if i = pivot then S.image fun s ↦ s i else Finset.univ

/-- **Unique fibers on one leg suffice**: the coordinate twin of
`Tensor.Restricts.partitionedUniqueLegFibers`.

If the block words of the support of `coordinatePower T n` all lie in `ambient`, and each selected
block word is the only ambient block word in its `pivot`-fiber (`HasUniqueLegFibers`, reused
verbatim from `Tensor/PartitionedExtraction.lean`), then zeroing out the `pivot` leg alone --- and
leaving the other two legs untouched --- already realizes the block zeroing out. -/
theorem coordinateBlockZeroOut_eq_coordinateZeroOut_of_hasUniqueLegFibers
    (T : (∀ i, κ i) → K) (blk : ∀ i, κ i → A i) {n : ℕ}
    {ambient S : Finset (BlockAddress fun i ↦ Fin n → A i)} {pivot : Leg}
    (hunique : HasUniqueLegFibers ambient S pivot)
    (hsupport : ∀ p : ∀ i, Fin n → κ i, coordinatePower T n p ≠ 0 →
      coordinateBlockWord blk p ∈ ambient) :
    coordinateBlockZeroOut T blk n S =
      coordinateZeroOut (coordinatePower T n) fun i ↦
        coordinateBlockFiber blk i (coordinateBlockPivotWords S pivot i) := by
  refine coordinateBlockZeroOut_eq_coordinateZeroOut T blk S _ (fun s hs i ↦ ?_) (fun p hp h ↦ ?_)
  · by_cases hi : i = pivot
    · rw [coordinateBlockPivotWords, if_pos hi]
      exact Finset.mem_image_of_mem _ hs
    · rw [coordinateBlockPivotWords, if_neg hi]
      exact Finset.mem_univ _
  · have hpivot := h pivot
    rw [coordinateBlockPivotWords, if_pos rfl] at hpivot
    obtain ⟨s, hs, hsp⟩ := Finset.mem_image.mp hpivot
    have := hunique.2 s hs _ (hsupport p hp) hsp.symm
    rwa [this]

omit [∀ i, Fintype (A i)] in
/-- **`I` is monotone along a block zeroing out.**  Under the hypotheses that make the block
zeroing out a genuine zeroing out, `Tensor.independenceNumber_coordinateZeroOut_le` applies.  (The
hypotheses cannot be dropped: `Tensor.independenceNumber` is *not* monotone under passing to an
arbitrary sub-support.) -/
theorem independenceNumber_coordinateBlockZeroOut_le (T : (∀ i, κ i) → K) (blk : ∀ i, κ i → A i)
    {n : ℕ} (S : Finset (BlockAddress fun i ↦ Fin n → A i)) (B : ∀ i, Finset (Fin n → A i))
    (hsub : ∀ s ∈ S, ∀ i, s i ∈ B i)
    (hclosed : ∀ p : ∀ i, Fin n → κ i, coordinatePower T n p ≠ 0 →
      (∀ i, coordinateBlockWord blk p i ∈ B i) → coordinateBlockWord blk p ∈ S) :
    independenceNumber (coordinateBlockZeroOut T blk n S) ≤
      independenceNumber (coordinatePower T n) := by
  rw [coordinateBlockZeroOut_eq_coordinateZeroOut T blk S B hsub hclosed]
  exact independenceNumber_coordinateZeroOut_le _ _

/-- `I` is monotone along a block zeroing out cut out by unique fibers on one leg. -/
theorem independenceNumber_coordinateBlockZeroOut_le_of_hasUniqueLegFibers
    (T : (∀ i, κ i) → K) (blk : ∀ i, κ i → A i) {n : ℕ}
    {ambient S : Finset (BlockAddress fun i ↦ Fin n → A i)} {pivot : Leg}
    (hunique : HasUniqueLegFibers ambient S pivot)
    (hsupport : ∀ p : ∀ i, Fin n → κ i, coordinatePower T n p ≠ 0 →
      coordinateBlockWord blk p ∈ ambient) :
    independenceNumber (coordinateBlockZeroOut T blk n S) ≤
      independenceNumber (coordinatePower T n) := by
  rw [coordinateBlockZeroOut_eq_coordinateZeroOut_of_hasUniqueLegFibers T blk hunique hsupport]
  exact independenceNumber_coordinateZeroOut_le _ _

end BlockZeroOut

/-! ## The block zeroing out as a block table

The second half of the extraction chain.  Abstractly, a legwise-injective support turns the
selected constituents into an indexed direct sum
(`Tensor.Restricts.partitionedLegwiseInjective_to_indexedDirectSum`).  In coordinates the
constituents keep the variables of the ambient power, so the direct sum appears through a legwise
*embedding* of the constituent variables into the words --- which is precisely the shape
`Tensor.coordinateExtend` of a `Tensor.coordinateDirectSum` demanded by
`AlgebraicComplexity.CoordinateGalacticCertificate`. -/

section BlockTable

variable {K : Type u} [CommSemiring K] {κ : Leg → Type v} {A : Leg → Type v}
variable {ν : Leg → Type v} {ι : Type v}
variable [∀ i, DecidableEq (A i)] [∀ i, DecidableEq (κ i)] [DecidableEq ι]

/-- **A block zeroing out is a block table of its constituents**: the coordinate twin of
`Tensor.Restricts.partitionedLegwiseInjective_to_indexedDirectSum`.

The selected block words are listed by `key : ι → _` (`hmem`, `hsurj`), and `hkey` is legwise
injectivity of that listing --- for `ι = ↥S` and `key = Subtype.val` it is exactly
`IsLegwiseInjective S`, see
`coordinateBlockZeroOut_eq_extend_directSum_of_isLegwiseInjective`.  The variables of the block
indexed by `j` are listed by `emb · (j, ·)`, subject to the two conditions that make the listing a
legwise bijection onto the fibers it must cover:

* `hblock`: a listed variable of block `j` on leg `i` has block word `key j i`;
* `hcover`: every word of leg `i` whose block word is used by some block is listed, which is
  phrased through the retraction `ret` because that is what `Tensor.coordinateExtend` tests.

No relation between `emb` and `ret` is assumed beyond `hcover`; in particular `hgf` (`ret` is a
retraction of `emb`, needed downstream by `Tensor.independenceNumber_coordinateExtend`) is not
used here. -/
theorem coordinateBlockZeroOut_eq_extend_directSum (T : (∀ i, κ i) → K) (blk : ∀ i, κ i → A i)
    {n : ℕ} {S : Finset (BlockAddress fun i ↦ Fin n → A i)}
    {key : ι → BlockAddress fun i ↦ Fin n → A i}
    {emb : ∀ i, ι × ν i → (Fin n → κ i)} {ret : ∀ i, (Fin n → κ i) → ι × ν i}
    (hmem : ∀ j, key j ∈ S) (hsurj : ∀ s ∈ S, ∃ j, key j = s)
    (hkey : ∀ i, Function.Injective fun j ↦ key j i)
    (hblock : ∀ i j x, coordinateBlockLegWord blk i (emb i (j, x)) = key j i)
    (hcover : ∀ (i : Leg) (w : Fin n → κ i),
      (∃ j, key j i = coordinateBlockLegWord blk i w) → emb i (ret i w) = w) :
    coordinateBlockZeroOut T blk n S =
      coordinateExtend emb ret (coordinateDirectSum fun j ↦
        coordinateBlockWordConstituent T blk (fun i x ↦ emb i (j, x)) (key j)) := by
  funext p
  by_cases hcond : ∀ i, emb i (ret i (p i)) = p i
  · -- The listed variables cover `p`, so the extension reads the block table at `ret ∘ p`.
    rw [coordinateExtend, if_pos hcond]
    -- Under `hcond` the block index of each leg determines the constituent, whose value at `p`
    -- is the constituent table of that block word.
    have hstep : ∀ j : ι, (∀ i, (ret i (p i)).1 = j) →
        coordinateDirectSum
            (fun j ↦ coordinateBlockWordConstituent T blk (fun i x ↦ emb i (j, x)) (key j))
            (fun i ↦ ret i (p i)) =
          coordinateBlockWordTable T blk (key j) p := by
      intro j hj
      have htriple : (fun i ↦ ret i (p i)) = blockTriple j fun i ↦ (ret i (p i)).2 := by
        funext i
        exact Prod.ext (hj i) rfl
      rw [htriple, coordinateDirectSum_blockTriple, coordinateBlockWordConstituent_apply]
      congr 1
      funext i
      have : (j, (ret i (p i)).2) = ret i (p i) := Prod.ext (hj i).symm rfl
      rw [this, hcond i]
    by_cases hmemS : coordinateBlockWord blk p ∈ S
    · obtain ⟨j, hjs⟩ := hsurj _ hmemS
      have hj : ∀ i, (ret i (p i)).1 = j := by
        intro i
        have hb := hblock i (ret i (p i)).1 (ret i (p i)).2
        rw [Prod.mk.eta, hcond i] at hb
        apply hkey i
        show key (ret i (p i)).1 i = key j i
        rw [← hb, hjs]
        rfl
      rw [hstep j hj, coordinateBlockZeroOut_of_mem hmemS,
        coordinateBlockWordTable_of_eq hjs.symm]
    · rw [coordinateBlockZeroOut_of_notMem hmemS]
      by_cases hall : ∀ i, (ret i (p i)).1 = (ret Leg.X (p Leg.X)).1
      · rw [hstep _ hall, coordinateBlockWordTable_of_ne]
        intro heq
        exact hmemS (heq ▸ hmem (ret Leg.X (p Leg.X)).1)
      · rw [coordinateDirectSum, if_neg hall]
  · -- No listed variable triple maps onto `p`, so `p` is not selected either.
    rw [coordinateExtend, if_neg hcond, coordinateBlockZeroOut_of_notMem]
    intro hmemS
    obtain ⟨j, hjs⟩ := hsurj _ hmemS
    exact hcond fun i ↦ hcover i (p i) ⟨j, by rw [hjs]; rfl⟩

/-- The block-table identification with the selected block words as the index type, driven by
`IsLegwiseInjective` reused verbatim from `Tensor/PartitionedDirectSum.lean`. -/
theorem coordinateBlockZeroOut_eq_extend_directSum_of_isLegwiseInjective
    (T : (∀ i, κ i) → K) (blk : ∀ i, κ i → A i) {n : ℕ}
    {S : Finset (BlockAddress fun i ↦ Fin n → A i)}
    {emb : ∀ i, S × ν i → (Fin n → κ i)} {ret : ∀ i, (Fin n → κ i) → S × ν i}
    (hinj : IsLegwiseInjective S)
    (hblock : ∀ (i : Leg) (s : S) (x : ν i),
      coordinateBlockLegWord blk i (emb i (s, x)) = s.1 i)
    (hcover : ∀ (i : Leg) (w : Fin n → κ i),
      (∃ s : S, s.1 i = coordinateBlockLegWord blk i w) → emb i (ret i w) = w) :
    coordinateBlockZeroOut T blk n S =
      coordinateExtend emb ret (coordinateDirectSum fun s : S ↦
        coordinateBlockWordConstituent T blk (fun i x ↦ emb i (s, x)) s.1) :=
  coordinateBlockZeroOut_eq_extend_directSum T blk (key := Subtype.val)
    (fun s ↦ s.2) (fun s hs ↦ ⟨⟨s, hs⟩, rfl⟩)
    (fun i s t h ↦ Subtype.ext (hinj i (Finset.mem_coe.mpr s.2) (Finset.mem_coe.mpr t.2) h))
    hblock hcover

variable [∀ i, Fintype (κ i)] [∀ i, Fintype (ν i)] [∀ i, DecidableEq (ν i)] [Fintype ι]

/-- **The independence number of a block zeroing out is the sum over its blocks.**  With `ret` an
actual retraction of the legwise embeddings, `Tensor.independenceNumber_coordinateExtend` discards
the words used by no constituent and `Tensor.independenceNumber_coordinateDirectSum` evaluates the
block table.  This is the coordinate counterpart of the asymptotic-sum step of an extraction. -/
theorem independenceNumber_coordinateBlockZeroOut (T : (∀ i, κ i) → K) (blk : ∀ i, κ i → A i)
    {n : ℕ} {S : Finset (BlockAddress fun i ↦ Fin n → A i)}
    {key : ι → BlockAddress fun i ↦ Fin n → A i}
    {emb : ∀ i, ι × ν i → (Fin n → κ i)} {ret : ∀ i, (Fin n → κ i) → ι × ν i}
    (hmem : ∀ j, key j ∈ S) (hsurj : ∀ s ∈ S, ∃ j, key j = s)
    (hkey : ∀ i, Function.Injective fun j ↦ key j i)
    (hblock : ∀ i j x, coordinateBlockLegWord blk i (emb i (j, x)) = key j i)
    (hcover : ∀ (i : Leg) (w : Fin n → κ i),
      (∃ j, key j i = coordinateBlockLegWord blk i w) → emb i (ret i w) = w)
    (hgf : ∀ i x, ret i (emb i x) = x) :
    independenceNumber (coordinateBlockZeroOut T blk n S) =
      ∑ j : ι, independenceNumber
        (coordinateBlockWordConstituent T blk (fun i x ↦ emb i (j, x)) (key j)) := by
  classical
  rw [coordinateBlockZeroOut_eq_extend_directSum T blk hmem hsurj hkey hblock hcover,
    independenceNumber_coordinateExtend hgf, independenceNumber_coordinateDirectSum]

end BlockTable

/-! ## Relabelling the variables

`Tensor.coordinateRelabel` renames the variables of every leg.  Block words are unaffected once the
block labelling is transported along the renaming, so a block zeroing out commutes with it. -/

section Relabel

variable {K : Type u} [CommSemiring K] {κ κ' : Leg → Type v} {A : Leg → Type v}
variable [∀ i, DecidableEq (A i)]

/-- **Block zeroing out commutes with relabelling the variables.**  Renaming the variables of every
leg along `e` and transporting the block labelling along `e.symm` renames the words of the power
letterwise, and leaves the selected set of block words untouched. -/
theorem coordinateBlockZeroOut_coordinateRelabel (T : (∀ i, κ i) → K) (blk : ∀ i, κ i → A i)
    (n : ℕ) (S : Finset (BlockAddress fun i ↦ Fin n → A i)) (e : ∀ i, κ i ≃ κ' i) :
    coordinateBlockZeroOut (coordinateRelabel e T) (fun i x ↦ blk i ((e i).symm x)) n S =
      coordinateRelabel (fun i ↦ Equiv.arrowCongr (Equiv.refl (Fin n)) (e i))
        (coordinateBlockZeroOut T blk n S) := by
  funext p
  have hword : coordinateBlockWord (fun i x ↦ blk i ((e i).symm x)) p =
      coordinateBlockWord blk fun i t ↦ (e i).symm (p i t) := rfl
  have hpower : coordinatePower (coordinateRelabel e T) n p =
      coordinatePower T n fun i t ↦ (e i).symm (p i t) := by
    rw [coordinatePower_coordinateRelabel, coordinateRelabel_apply]
    rfl
  by_cases hmem : coordinateBlockWord (fun i x ↦ blk i ((e i).symm x)) p ∈ S
  · rw [coordinateBlockZeroOut_of_mem hmem, hpower, coordinateRelabel_apply,
      coordinateBlockZeroOut_of_mem]
    · rfl
    · rw [hword] at hmem
      exact hmem
  · rw [coordinateBlockZeroOut_of_notMem hmem, coordinateRelabel_apply,
      coordinateBlockZeroOut_of_notMem]
    rw [hword] at hmem
    exact hmem

end Relabel

end AlgebraicComplexity.Tensor
