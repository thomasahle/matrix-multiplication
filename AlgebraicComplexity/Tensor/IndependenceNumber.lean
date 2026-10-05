/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Tensor.AsymptoticRank
import AlgebraicComplexity.Tensor.Coordinates
import AlgebraicComplexity.Tensor.IndexedDirectSum
import AlgebraicComplexity.Tensor.SliceRank
import AlgebraicComplexity.Tensor.Subrank

/-!
# The independence number of a coordinate tensor

This file is the finite foundation of the Alman--Vassilevska Williams barrier framework
(J. Alman and V. Vassilevska Williams, *Limits on All Known (and Some Unknown) Approaches to
Matrix Multiplication*, arXiv:1810.08671; Section 3.1.1, Section 3.1.2 and Section 3.5).  It
defines the **independence number** `I(T)` of a tensor given in coordinates and proves the part
of its calculus that is unconditionally true at finite level.

## The definition being transcribed

AVW work with a tensor `T = ∑ T_{ijk} x_i y_j z_k` over three finite variable sets, and use two
support-combinatorial notions (Section 3.1.2 and Section 3.1.1):

* a *zeroing out* of `T` selects subsets `X' ⊆ X`, `Y' ⊆ Y`, `Z' ⊆ Z` and sets every variable
  outside them to zero; the result is the tensor over `X', Y', Z'` agreeing with `T` there;
* a tensor is *independent of size `r`* if it equals `⟨r⟩` up to a permutation of the indices of
  each leg, i.e. its support is a perfect matching of `r` triples, pairwise distinct in all three
  coordinates, and nothing else survives.

Their independence number `I(T)` (Section 3.5) is the largest `r` such that some zeroing out of
`T` is an independent tensor of size `r`.

Unfolding "some zeroing out is independent" gives the definition adopted here, `IndependentSet`:
a finite set `S` of index triples such that

1. every element of `S` is in the support of `T`;
2. two elements of `S` that agree in *some* coordinate are equal (the three coordinate
   projections are injective on `S`); and
3. `S` is *closed*: every support triple all of whose three coordinates are used by `S` already
   belongs to `S`.

Condition 3 is the one that is easy to drop by accident, and dropping it changes the invariant
completely (see the non-monotonicity discussion below).  It is exactly the second clause in the
definition of a tri-colored sum-free set (AVW Definition 3.3 and Lemma 6.1): for the group tensor
`T_G` it says that `a₁b₂ = c₃` with `(aₗ, bₗ, cₗ) ∈ S` forces the three triples to coincide.
`independenceNumber T` is then the largest cardinality of such an `S`; `IndependentSet.zeroOut_support`
and `independentSet_of_zeroOut_support` prove that this is equivalent to AVW's zeroing-out
formulation, taking `X'`, `Y'`, `Z'` to be the variables used by `S`.

## Main definitions

* `IndependentSet T S`: `S` is an independent set of terms of the coordinate tensor `T`.
* `independenceNumber T`: the largest cardinality of an independent set of terms, `I(T)`.
* `coordinateZeroOut T A`: the zeroing out of `T` to the coordinate subsets `A`.
* `coordinateProduct T T'`: the Kronecker product of two coordinate tensors.
* `coordinateRelabel e T`: the coefficient table obtained by renaming the variables of every leg
  along a bijection.
* `coordinateWordProduct T`: the positionwise product of a *heterogeneous* family of coefficient
  tables, position `t` carrying its own index family and table.
* `coordinatePower T n`: the `n`-fold Kronecker power `T^{⊗n}`, indexed by *words*
  `Fin n → κ i` on leg `i`.  This is the index convention matching `Tensor.power`; it is the
  constant-family case of `coordinateWordProduct`.
* `powerIndependentSet S n`: the `n`-fold power of a set of terms, the triples of words all of
  whose letters lie in `S`.
* `diagonalCoefficients K ι`: the coordinate tensor of `⟨|ι|⟩`.
* `coordinateTensor T`: the abstract `Tensor3` with coefficient function `T`, the bridge into the
  basis-free layer.  It is the inverse of `Tensor.standardCoordinateEquiv`, and
  `coordinateTensor_diagonalCoefficients` identifies it on `diagonalCoefficients K ι` with the
  basis-free `Tensor.diagonalTensor K ι`, so the two models of `⟨|ι|⟩` in this repository are one.

## Main results

* `IndependentSet.mix_eq` (AVW Lemma 6.1 in the abstract): if one element of `S` is chosen for
  each leg and the resulting mixed triple is in the support of `T`, then the three chosen
  elements coincide.  Everything else in the file is a consequence of this reformulation of
  closure.
* `independenceNumber_le_card`: `I(T) ≤ min(|X|, |Y|, |Z|)` (AVW Section 3.5).
* `IndependentSet.of_subSupport`: a fixed independent set restricts to any sub-support.  This is
  the true statement in the neighbourhood of the *false* one that `I` is monotone under passing to
  sub-supports; see below.
* `independenceNumber_coordinateZeroOut_le`: **`I` is monotone under zeroing outs.**
* `independenceNumber_coordinateProduct_ge`: **`I` is supermultiplicative**,
  `I(S ⊗ T) ≥ I(S) · I(T)`, over a coefficient ring without zero divisors.  This is the direction
  Fekete's lemma needs in order for the asymptotic independence number
  `Ī(T) = limₙ I(T^{⊗n})^{1/n}` of the next tranche to exist and to equal `supₙ I(T^{⊗n})^{1/n}`.
* `independenceNumber_diagonalCoefficients`: `I(⟨r⟩) = r`.
* `IndependentSet.restricts_diagonalTensor` and `independenceNumber_le_subrank`: the bridge to
  the proved barrier chain.  An independent set of size `m` gives *legwise linear maps* carrying
  `coordinateTensor T` to the diagonal tensor of size `m` --- that is, a subrank witness --- so
  `I(T) ≤ Q(T)`.  `independenceNumber_le_sliceRank` and `independenceNumber_le_rank` are then the
  composites with `subrank_le_sliceRank` (Tao's diagonal lemma, in its subrank packaging) and
  `sliceRank_le_rank`, giving `I(T) ≤ Q(T) ≤ sliceRank(T) ≤ rank(T)`.
* `independenceNumber_coordinateRelabel`: **`I` is invariant under relabelling the variables of the
  legs.**  This is what makes the index bookkeeping of Kronecker powers free; it is *not*
  invariance under legwise isomorphism, which is false (see below).
* `independenceNumber_coordinatePower_add_ge`: **the additive form of supermultiplicativity**,
  `I(T^{⊗m}) · I(T^{⊗n}) ≤ I(T^{⊗(m+n)})`.  Together with
  `one_le_independenceNumber_coordinatePower` and `independenceNumber_coordinatePower_le_pow`
  (`I(T^{⊗n}) ≤ |κ i|^n`) these are exactly the hypotheses of Fekete's lemma used by
  `Tensor/AsymptoticIndependenceNumber.lean`.
* `Isomorphic.coordinateTensor_coordinatePower`: **the word-indexed Kronecker power is the
  canonical tensor power**, `coordinateTensor (T^{⊗n}) ≅ (coordinateTensor T)^{⊗n}`, whence
  `independenceNumber_coordinatePower_le_subrank` and
  `independenceNumber_coordinatePower_le_rank` over a field.
* `independentSet_powerIndependentSet` and `card_powerIndependentSet`: the `n`-fold power of an
  independent set of size `f` is an independent set of size `f^n` for `T^{⊗n}`.
* `coordinatePower_coordinateZeroOut`: zeroing outs commute with Kronecker powers, hence
  `independenceNumber_coordinatePower_coordinateZeroOut_le`.
* `independenceNumber_coordinatePower_coordinatePower`: Kronecker powers iterate,
  `I((T^{⊗k})^{⊗n}) = I(T^{⊗(n·k)})`, through the flattening bijection `flattenIndexEquiv`.
* `coordinateDirectSum`: the **block table** of a finite family of coefficient tables, the
  coordinate counterpart of `Tensor.indexedDirectSum`; `coordinateDirectSum_const` identifies `F`
  disjoint copies of one table with its Kronecker product with `⟨F⟩`, and
  `independenceNumber_coordinateDirectSum` computes `I(⊕ⱼ Aⱼ) = ∑ⱼ I(Aⱼ)` exactly.
* `coordinateExtend`: the **zero-extension** of a table along a legwise injection of variable sets,
  with `independenceNumber_coordinateExtend` (`I` does not see unused variables) and
  `coordinatePower_coordinateExtend`.  This is the shape of the target of a monomial degeneration,
  which leaves the variables of its source in place.
* `coordinateRelabel_coordinatePower_coordinateProduct` and
  `coordinatePower_diagonalCoefficients`: Kronecker powers distribute over Kronecker products, and
  `⟨r⟩^{⊗k} = ⟨r^k⟩`; together they turn `(F ⊙ A)^{⊗k}` into `F^k ⊙ A^{⊗k}`.
* `Restricts.coordinateTensor_pullback` and `coordinateTensor_coordinateDirectSum_eq_sum`: the two
  bridges from these constructions to the abstract layer.

## Why the invariant lives on the coefficient function

`independenceNumber` is deliberately a function of a *coordinate presentation* `T : (∀ i, κ i) → K`
and not of the abstract `Tensor3` it defines: it is genuinely basis-dependent.  Over `ℚ`, the
tensor `⟨2⟩` has independence number `2`, while the legwise-isomorphic coefficient table
`T'_{ijk} = 1 + s_i s_j s_k` (with `s₁ = 1`, `s₂ = -1`), obtained by the change of basis
`[[1, 1], [1, -1]]` on every leg, is supported on the four triples with an even number of index-`2`
entries and has independence number `1`, since no two of those four triples differ in all three
coordinates.  Every tensor in the AVW framework comes with a fixed table of terms, so this is the
right level of generality; the comparison with the basis-free `sliceRank` below is consequently a
one-way inequality.  This is formalized at the end of the module, in the namespace
`HadamardWitness`: `independenceNumber_not_isomorphism_invariant` exhibits the two legwise
isomorphic tables together with their different independence numbers.

## What is deliberately *not* proved here, and why

* **`I` is not monotone under passing to sub-supports.**  Deleting terms from the support can
  *increase* the independence number: the all-ones tensor on `ι³` has `I = 1`
  (`independenceNumber_const_one`) while its diagonal sub-support has `I = |ι|`
  (`independenceNumber_diagonalCoefficients`).  The same example shows that slice rank is not
  monotone under passing to sub-supports either (the all-ones tensor is a single slice term).
  This is why the barrier framework is organized around `I` and `Ī` and only *compares* them
  with slice rank on honest restrictions; the finite slice-rank bound proved here applies to
  restrictions, i.e. to `coordinateTensor T` itself, never to an arbitrary sub-support of it.
* **`I` is not claimed monotone under monomial degeneration.**  AVW obtain
  `Ī(A) ≤ Ī(B)` for a monomial degeneration `A` of `B` (Corollary 4.2) only through the
  asymptotic Lemma 4.3 of Alman--Vassilevska Williams ITCS 2018, whose conversion of a monomial
  degeneration into zeroing outs of tensor powers loses a subexponential factor.  No finite
  statement of that form is available, and none is assumed here.
* The asymptotic independence number `Ī` itself is defined one module up, in
  `Tensor/AsymptoticIndependenceNumber.lean`; the Galactic-method exponent `ω_g` and the
  inequality `Ī(T) ≥ R̃(T)^{6/ω_g(T) − 2}` (AVW Theorem 4.1) are later tranches; see
  `BARRIER_FRAMEWORK.md`.

## Position in the library

This is a layer-1 tensor-algebra module.  It imports `Tensor.SliceRank` (for the diagonal
tensor and the proved slice-rank barrier), `Tensor.Subrank` (for the subrank, and through it the
canonical tensor powers of `Tensor.Power`) and `Tensor.Coordinates` (for the standard coefficient
equivalence), and it mentions no named matrix-multiplication construction and no numerical bound.
The definitions are support-combinatorial: `IndependentSet`, `independenceNumber`,
`coordinateZeroOut`, `coordinateProduct`, `coordinateRelabel` and `coordinatePower` need only a
commutative semiring; supermultiplicativity adds `NoZeroDivisors` (and, for the powers of a set of
terms, `Nontrivial`, since an empty product of coefficients must be nonzero); and only the passage
to `sliceRank`, `subrank` and `rank` uses a field.
-/

namespace AlgebraicComplexity.Tensor

universe u v w

section Support

variable {K : Type u} [CommSemiring K] {κ : Leg → Type v}

/-- `IndependentSet T S` says that the finite set `S` of index triples is an *independent set of
terms* of the coordinate tensor `T`, in the sense of Alman--Vassilevska Williams: zeroing out all
variables not used by `S` turns `T` into the independent tensor `⟨|S|⟩` supported on `S`.

The three fields are exactly the three requirements: the terms are terms of `T`; they are
pairwise distinct in every one of the three coordinates; and no *other* term of `T` uses only
variables occurring in `S`. -/
structure IndependentSet (T : (∀ i, κ i) → K) (S : Finset (∀ i, κ i)) : Prop where
  /-- Every chosen triple is a term of `T`. -/
  ne_zero : ∀ p ∈ S, T p ≠ 0
  /-- Two chosen triples sharing a variable on some leg are equal: the three coordinate
  projections are injective on `S`. -/
  distinct : ∀ p ∈ S, ∀ q ∈ S, ∀ i, p i = q i → p = q
  /-- Closure: a term of `T` all of whose variables are used by `S` is itself in `S`.  This is
  the clause that makes the zeroing out to the variables of `S` *exactly* `S`. -/
  closed : ∀ p, T p ≠ 0 → (∀ i, ∃ q ∈ S, q i = p i) → p ∈ S

namespace IndependentSet

variable {T : (∀ i, κ i) → K} {S : Finset (∀ i, κ i)}

/-- The empty set of terms is independent. -/
theorem empty : IndependentSet T (∅ : Finset (∀ i, κ i)) where
  ne_zero p hp := absurd hp (Finset.notMem_empty p)
  distinct p hp := absurd hp (Finset.notMem_empty p)
  closed p _ hbox := by
    obtain ⟨q, hq, -⟩ := hbox .X
    exact absurd hq (Finset.notMem_empty q)

/-- A single term of `T` is an independent set: the closure condition forces any competitor to
agree with it in all three coordinates. -/
theorem singleton [DecidableEq (∀ i, κ i)] {p : ∀ i, κ i} (hp : T p ≠ 0) :
    IndependentSet T ({p} : Finset (∀ i, κ i)) where
  ne_zero q hq := by
    rw [Finset.mem_singleton] at hq
    exact hq ▸ hp
  distinct q hq r hr _ _ := by
    rw [Finset.mem_singleton] at hq hr
    rw [hq, hr]
  closed r _ hbox := by
    rw [Finset.mem_singleton]
    funext i
    obtain ⟨q, hq, hqi⟩ := hbox i
    rw [Finset.mem_singleton] at hq
    rw [← hqi, hq]

/-- **Mixing lemma.**  Choose one element `sel i ∈ S` for every leg `i` and build the mixed triple
whose `i`-th coordinate is read off `sel i`.  If that triple is a term of `T`, then all three
chosen elements coincide.

This is the abstract form of the defining property of a tri-colored sum-free set (AVW
Definition 3.3): for the group tensor `T_G`, `x_{a₁} y_{b₂} z_{c₃}` is a term whenever
`a₁b₂ = c₃`, so the lemma says `a₁b₂ = c₃` forces the three triples of `S` to be equal.

Proof sketch: the mixed triple uses only variables occurring in `S`, so closure puts it in `S`;
it then shares its `i`-th coordinate with `sel i`, so injectivity of the `i`-th projection on `S`
identifies it with `sel i` for every `i`. -/
theorem mix_eq (h : IndependentSet T S) (sel : Leg → ∀ i, κ i) (hsel : ∀ i, sel i ∈ S)
    (hmix : T (fun i ↦ sel i i) ≠ 0) : ∀ i j, sel i = sel j := by
  have hmem : (fun i ↦ sel i i) ∈ S :=
    h.closed _ hmix fun i ↦ ⟨sel i, hsel i, rfl⟩
  have key : ∀ i, (fun j ↦ sel j j) = sel i := fun i ↦
    h.distinct _ hmem _ (hsel i) i rfl
  intro i j
  rw [← key i, key j]

/-- **Independent sets restrict to sub-supports.**  If the support of `T'` is contained in the
support of `T` (that is, `T'` is a sub-tensor of `T` in the sense of AVW Section 3.1.2) and `S` is
an independent set of terms of `T`, then the elements of `S` surviving in `T'` are an independent
set of terms of `T'`.

Note carefully what this does *not* say: it does not say `I(T') ≤ I(T)`, which is false — compare
`independenceNumber_const_one` with `independenceNumber_diagonalCoefficients`.  The statement is
about one fixed independent set, and in that form it is exactly the step used by the partitioning
arguments of AVW Section 5, where a fixed zeroing out is reapplied after replacing one tensor
factor by one part of a partition.

Proof sketch: the first two conditions are inherited.  For closure, a term of `T'` boxed by `S'`
is a term of `T` boxed by `S`, hence lies in `S` by closure for `T`; being a term of `T'` it then
lies in `S'`. -/
theorem of_subSupport {T T' : (∀ i, κ i) → K} {S S' : Finset (∀ i, κ i)}
    (h : IndependentSet T S) (hsub : ∀ p, T' p ≠ 0 → T p ≠ 0)
    (hS' : ∀ p, p ∈ S' ↔ p ∈ S ∧ T' p ≠ 0) : IndependentSet T' S' where
  ne_zero p hp := ((hS' p).mp hp).2
  distinct p hp q hq i hpq :=
    h.distinct p ((hS' p).mp hp).1 q ((hS' q).mp hq).1 i hpq
  closed p hp hbox := by
    refine (hS' p).mpr ⟨h.closed p (hsub p hp) ?_, hp⟩
    intro i
    obtain ⟨q, hq, hqi⟩ := hbox i
    exact ⟨q, ((hS' q).mp hq).1, hqi⟩

/-- The `i`-th coordinate projection is injective on an independent set. -/
theorem injOn (h : IndependentSet T S) (i : Leg) :
    Set.InjOn (fun p : ∀ j, κ j ↦ p i) (S : Set (∀ j, κ j)) :=
  fun p hp q hq hpq ↦ h.distinct p hp q hq i hpq

/-- An independent set has at most as many elements as there are variables on any single leg:
`|S| ≤ |κ i|`.  This is AVW's `I(T) ≤ min{|X|, |Y|, |Z|}` at the level of a single certificate. -/
theorem card_le_card [∀ i, Fintype (κ i)] [∀ i, DecidableEq (κ i)]
    (h : IndependentSet T S) (i : Leg) : S.card ≤ Fintype.card (κ i) := by
  have hcard : S.card ≤ (Finset.univ : Finset (κ i)).card :=
    Finset.card_le_card_of_injOn (fun p ↦ p i) (fun p _ ↦ Finset.mem_univ _) (h.injOn i)
  simpa using hcard

end IndependentSet

end Support

section Number

variable {K : Type u} [CommSemiring K] {κ : Leg → Type v}

/-- The set of cardinalities of independent sets of terms of `T`. -/
def independenceCards (T : (∀ i, κ i) → K) : Set ℕ :=
  {n | ∃ S : Finset (∀ i, κ i), IndependentSet T S ∧ S.card = n}

/-- `0` is always the cardinality of an independent set, namely the empty one. -/
theorem zero_mem_independenceCards (T : (∀ i, κ i) → K) : 0 ∈ independenceCards T :=
  ⟨∅, IndependentSet.empty, rfl⟩

/-- **The independence number `I(T)`** of a coordinate tensor: the largest number of terms of `T`
that form an independent set, equivalently the largest size of an independent tensor obtainable
from `T` by a zeroing out (Alman--Vassilevska Williams, arXiv:1810.08671, Section 3.5).

The supremum is over a set of natural numbers that is always nonempty and, for a tensor in
finitely many variables, bounded (`bddAbove_independenceCards`). -/
noncomputable def independenceNumber (T : (∀ i, κ i) → K) : ℕ :=
  sSup (independenceCards T)

variable [∀ i, Fintype (κ i)] [∀ i, DecidableEq (κ i)]

/-- Cardinalities of independent sets are bounded by the number of `X`-variables. -/
theorem bddAbove_independenceCards (T : (∀ i, κ i) → K) : BddAbove (independenceCards T) := by
  refine ⟨Fintype.card (κ .X), ?_⟩
  rintro n ⟨S, hS, rfl⟩
  exact hS.card_le_card .X

/-- Every independent set of terms is at most as large as the independence number. -/
theorem IndependentSet.card_le_independenceNumber {T : (∀ i, κ i) → K}
    {S : Finset (∀ i, κ i)} (h : IndependentSet T S) : S.card ≤ independenceNumber T :=
  le_csSup (bddAbove_independenceCards T) ⟨S, h, rfl⟩

/-- The independence number is attained by an explicit independent set of terms. -/
theorem exists_independentSet_card_eq (T : (∀ i, κ i) → K) :
    ∃ S : Finset (∀ i, κ i), IndependentSet T S ∧ S.card = independenceNumber T := by
  have hmem : independenceNumber T ∈ independenceCards T :=
    Nat.sSup_mem ⟨0, zero_mem_independenceCards T⟩ (bddAbove_independenceCards T)
  exact hmem

omit [∀ i, Fintype (κ i)] [∀ i, DecidableEq (κ i)] in
/-- The independence number is bounded by any bound valid for all independent sets. -/
theorem independenceNumber_le {T : (∀ i, κ i) → K} {n : ℕ}
    (h : ∀ S : Finset (∀ i, κ i), IndependentSet T S → S.card ≤ n) :
    independenceNumber T ≤ n := by
  refine csSup_le ⟨0, zero_mem_independenceCards T⟩ ?_
  rintro m ⟨S, hS, rfl⟩
  exact h S hS

/-- `I(T) ≤ |κ i|` for every leg `i`; together over the three legs this is AVW's bound
`I(T) ≤ min{|X|, |Y|, |Z|}`, since a zeroing out cannot increase the number of variables of any
one leg. -/
theorem independenceNumber_le_card (T : (∀ i, κ i) → K) (i : Leg) :
    independenceNumber T ≤ Fintype.card (κ i) :=
  independenceNumber_le fun _ hS ↦ hS.card_le_card i

/-- A nonzero coordinate tensor has independence number at least one. -/
theorem one_le_independenceNumber {T : (∀ i, κ i) → K} {p : ∀ i, κ i} (hp : T p ≠ 0) :
    1 ≤ independenceNumber T := by
  classical
  have h := (IndependentSet.singleton (T := T) hp).card_le_independenceNumber
  simpa using h

end Number

section ZeroingOut

variable {K : Type u} [CommSemiring K] {κ : Leg → Type v} [∀ i, DecidableEq (κ i)]

/-- The **zeroing out** of a coordinate tensor to the coordinate subsets `A`: every variable
outside `A i` on leg `i` is set to zero, so only terms whose three variables all survive are
kept.  This is AVW's combinatorial restriction (Section 3.1.2). -/
def coordinateZeroOut (T : (∀ i, κ i) → K) (A : ∀ i, Finset (κ i)) : (∀ i, κ i) → K :=
  fun p ↦ if ∀ i, p i ∈ A i then T p else 0

/-- A term of the source whose variables all survive is a term of the zeroing out. -/
theorem coordinateZeroOut_of_mem {T : (∀ i, κ i) → K} {A : ∀ i, Finset (κ i)}
    {p : ∀ i, κ i} (hmem : ∀ i, p i ∈ A i) : coordinateZeroOut T A p = T p := by
  simp only [coordinateZeroOut, if_pos hmem]

/-- A zeroed-out variable kills every term that uses it. -/
theorem coordinateZeroOut_of_notMem {T : (∀ i, κ i) → K} {A : ∀ i, Finset (κ i)}
    {p : ∀ i, κ i} (hmem : ¬ ∀ i, p i ∈ A i) : coordinateZeroOut T A p = 0 := by
  simp only [coordinateZeroOut, if_neg hmem]

/-- A surviving term of a zeroing out is a term of the source. -/
theorem coordinateZeroOut_ne_zero {T : (∀ i, κ i) → K} {A : ∀ i, Finset (κ i)}
    {p : ∀ i, κ i} (h : coordinateZeroOut T A p ≠ 0) : T p ≠ 0 ∧ ∀ i, p i ∈ A i := by
  by_cases hmem : ∀ i, p i ∈ A i
  · rw [coordinateZeroOut_of_mem hmem] at h
    exact ⟨h, hmem⟩
  · rw [coordinateZeroOut_of_notMem hmem] at h
    exact absurd rfl h

/-- **Zeroing outs cannot create independence.**  An independent set of terms of a zeroing out of
`T` is an independent set of terms of `T` itself.

Proof sketch: the two support conditions are inherited because a surviving term is a term of the
source.  For closure, a term `p` of `T` using only variables of `S` survives the zeroing out,
because each of its three variables already occurs in some element of `S`, and elements of `S`
survive; so closure for the zeroed tensor applies. -/
theorem IndependentSet.of_coordinateZeroOut {T : (∀ i, κ i) → K} {A : ∀ i, Finset (κ i)}
    {S : Finset (∀ i, κ i)} (h : IndependentSet (coordinateZeroOut T A) S) :
    IndependentSet T S where
  ne_zero p hp := (coordinateZeroOut_ne_zero (h.ne_zero p hp)).1
  distinct := h.distinct
  closed p hp hbox := by
    refine h.closed p ?_ hbox
    have hmem : ∀ i, p i ∈ A i := by
      intro i
      obtain ⟨q, hq, hqi⟩ := hbox i
      have := (coordinateZeroOut_ne_zero (h.ne_zero q hq)).2 i
      rwa [hqi] at this
    rwa [coordinateZeroOut_of_mem hmem]

/-- **Monotonicity of the independence number under zeroing outs**:
`I(T|_{X',Y',Z'}) ≤ I(T)`. -/
theorem independenceNumber_coordinateZeroOut_le [∀ i, Fintype (κ i)]
    (T : (∀ i, κ i) → K) (A : ∀ i, Finset (κ i)) :
    independenceNumber (coordinateZeroOut T A) ≤ independenceNumber T :=
  independenceNumber_le fun _ hS ↦ hS.of_coordinateZeroOut.card_le_independenceNumber

/-- The variables of leg `i` used by a finite set of terms. -/
def legImage (S : Finset (∀ i, κ i)) (i : Leg) : Finset (κ i) :=
  S.image fun p ↦ p i

/-- Membership in `legImage` says that a variable is used by some chosen term. -/
theorem mem_legImage {S : Finset (∀ i, κ i)} {i : Leg} {a : κ i} :
    a ∈ legImage S i ↔ ∃ p ∈ S, p i = a := by
  simp [legImage]

/-- **Faithfulness of the transcription**, one direction: if `S` is an independent set of terms of
`T`, then zeroing out `T` to the variables used by `S` leaves exactly the terms of `S`.  That is
the zeroing-out formulation of AVW's definition: the result is the independent tensor `⟨|S|⟩`. -/
theorem IndependentSet.zeroOut_support {T : (∀ i, κ i) → K}
    {S : Finset (∀ i, κ i)} (h : IndependentSet T S) (p : ∀ i, κ i) :
    coordinateZeroOut T (legImage S) p ≠ 0 ↔ p ∈ S := by
  constructor
  · intro hne
    obtain ⟨hp, hmem⟩ := coordinateZeroOut_ne_zero hne
    exact h.closed p hp fun i ↦ mem_legImage.mp (hmem i)
  · intro hp
    have hmem : ∀ i, p i ∈ legImage S i := fun i ↦ mem_legImage.mpr ⟨p, hp, rfl⟩
    rw [coordinateZeroOut_of_mem hmem]
    exact h.ne_zero p hp

/-- **Faithfulness of the transcription**, converse direction: a set of terms that is pairwise
distinct in all three coordinates and whose induced zeroing out has support exactly `S` is an
independent set in the sense of `IndependentSet`. -/
theorem independentSet_of_zeroOut_support {T : (∀ i, κ i) → K}
    {S : Finset (∀ i, κ i)}
    (hdistinct : ∀ p ∈ S, ∀ q ∈ S, ∀ i, p i = q i → p = q)
    (hsupport : ∀ p, coordinateZeroOut T (legImage S) p ≠ 0 ↔ p ∈ S) :
    IndependentSet T S where
  ne_zero p hp := (coordinateZeroOut_ne_zero ((hsupport p).mpr hp)).1
  distinct := hdistinct
  closed p hp hbox := by
    refine (hsupport p).mp ?_
    have hmem : ∀ i, p i ∈ legImage S i := fun i ↦ mem_legImage.mpr (hbox i)
    rwa [coordinateZeroOut_of_mem hmem]

end ZeroingOut

/-! ## The support and the minimal variable sets

The projection `legImage` of the support of a table onto one leg is AVW's *minimal variable set*
of that leg (arXiv:1810.08671, Definition 5.2): the smallest subset of the variables outside of
which every coefficient vanishes.  The measure `μ(T) = ∏ i, |minimalLegSet T i|` built from them,
and its calculus, live in `Tensor/IndependenceMeasure.lean`. -/

section MinimalLegSet

variable {K : Type u} [CommSemiring K] {κ : Leg → Type v}
variable [∀ i, Fintype (κ i)] [∀ i, DecidableEq (κ i)]

open scoped Classical in
/-- The **support** of a coefficient table, as a finite set of index triples: the triples whose
coefficient is nonzero. -/
noncomputable def coordinateSupport (T : (∀ i, κ i) → K) : Finset (∀ i, κ i) :=
  Finset.univ.filter fun p ↦ T p ≠ 0

omit [∀ i, DecidableEq (κ i)] in
/-- Membership in the support is nonvanishing of the coefficient. -/
@[simp] theorem mem_coordinateSupport {T : (∀ i, κ i) → K} {p : ∀ i, κ i} :
    p ∈ coordinateSupport T ↔ T p ≠ 0 := by
  classical
  simp [coordinateSupport]

/-- The **minimal variable set of `T` on leg `i`** (Alman--Vassilevska Williams,
arXiv:1810.08671, Definition 5.2): the smallest subset of the variables of leg `i` outside of
which every coefficient of `T` vanishes, equivalently the projection of the support of `T` onto
leg `i`.  For the three legs these are AVW's `X'`, `Y'`, `Z'`. -/
noncomputable def minimalLegSet (T : (∀ i, κ i) → K) (i : Leg) : Finset (κ i) :=
  legImage (coordinateSupport T) i

/-- A variable is minimal for `T` on leg `i` exactly when some term of `T` uses it. -/
theorem mem_minimalLegSet {T : (∀ i, κ i) → K} {i : Leg} {a : κ i} :
    a ∈ minimalLegSet T i ↔ ∃ p, T p ≠ 0 ∧ p i = a := by
  simp [minimalLegSet, mem_legImage]

/-- Every variable used by a term of `T` is minimal for `T`. -/
theorem mem_minimalLegSet_of_ne_zero {T : (∀ i, κ i) → K} {p : ∀ i, κ i} (hp : T p ≠ 0)
    (i : Leg) : p i ∈ minimalLegSet T i :=
  mem_minimalLegSet.mpr ⟨p, hp, rfl⟩

end MinimalLegSet


section Product

variable {K : Type u} [CommSemiring K] {κ κ' : Leg → Type v}

/-- The **Kronecker product** of two coordinate tensors: the variables of the product are pairs of
variables, and the coefficient of a pair of terms is the product of the two coefficients. -/
def coordinateProduct (T : (∀ i, κ i) → K) (T' : (∀ i, κ' i) → K) :
    (∀ i, κ i × κ' i) → K :=
  fun p ↦ T (fun i ↦ (p i).1) * T' (fun i ↦ (p i).2)

/-- Pair two index triples into an index triple of the Kronecker product. -/
def pairTriple (q : (∀ i, κ i) × (∀ i, κ' i)) : ∀ i, κ i × κ' i :=
  fun i ↦ (q.1 i, q.2 i)

/-- Pairing index triples is injective. -/
theorem pairTriple_injective :
    Function.Injective (pairTriple (κ := κ) (κ' := κ')) := by
  rintro ⟨p, p'⟩ ⟨q, q'⟩ h
  have h1 : p = q := funext fun i ↦ congrArg Prod.fst (congrFun h i)
  have h2 : p' = q' := funext fun i ↦ congrArg Prod.snd (congrFun h i)
  rw [h1, h2]

/-- **Independent sets multiply.**  The set of pairwise products of two independent sets is an
independent set of the Kronecker product.

Proof sketch: the coefficient of a pair of terms is the product of two nonzero coefficients,
hence nonzero in a ring without zero divisors.  Two paired triples agreeing on leg `i` agree
componentwise on leg `i`, so both components are forced equal.  For closure, a term of the
product all of whose variables come from the paired set has both components in the support (a
product of coefficients is nonzero only if both are) and both components boxed, so closure of the
two factors applies componentwise. -/
theorem IndependentSet.coordinateProduct [NoZeroDivisors K]
    [DecidableEq (∀ i, κ i × κ' i)]
    {T : (∀ i, κ i) → K} {T' : (∀ i, κ' i) → K}
    {S : Finset (∀ i, κ i)} {S' : Finset (∀ i, κ' i)}
    (h : IndependentSet T S) (h' : IndependentSet T' S') :
    IndependentSet (coordinateProduct T T') ((S ×ˢ S').image pairTriple) where
  ne_zero p hp := by
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨hq1, hq2⟩ := Finset.mem_product.mp hq
    exact mul_ne_zero (h.ne_zero _ hq1) (h'.ne_zero _ hq2)
  distinct p hp r hr i hpr := by
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hr
    obtain ⟨hq1, hq2⟩ := Finset.mem_product.mp hq
    obtain ⟨hs1, hs2⟩ := Finset.mem_product.mp hs
    have h1 : q.1 i = s.1 i := congrArg Prod.fst hpr
    have h2 : q.2 i = s.2 i := congrArg Prod.snd hpr
    have e1 : q.1 = s.1 := h.distinct _ hq1 _ hs1 i h1
    have e2 : q.2 = s.2 := h'.distinct _ hq2 _ hs2 i h2
    rw [show q = s from Prod.ext e1 e2]
  closed p hp hbox := by
    have hmul : T (fun i ↦ (p i).1) * T' (fun i ↦ (p i).2) ≠ 0 := hp
    have hp1 : T (fun i ↦ (p i).1) ≠ 0 := fun h0 ↦ hmul (by rw [h0, zero_mul])
    have hp2 : T' (fun i ↦ (p i).2) ≠ 0 := fun h0 ↦ hmul (by rw [h0, mul_zero])
    have hbox1 : ∀ i, ∃ q ∈ S, q i = (p i).1 := by
      intro i
      obtain ⟨r, hr, hri⟩ := hbox i
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hr
      exact ⟨q.1, (Finset.mem_product.mp hq).1, congrArg Prod.fst hri⟩
    have hbox2 : ∀ i, ∃ q ∈ S', q i = (p i).2 := by
      intro i
      obtain ⟨r, hr, hri⟩ := hbox i
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hr
      exact ⟨q.2, (Finset.mem_product.mp hq).2, congrArg Prod.snd hri⟩
    have hm1 := h.closed _ hp1 hbox1
    have hm2 := h'.closed _ hp2 hbox2
    refine Finset.mem_image.mpr ⟨(fun i ↦ (p i).1, fun i ↦ (p i).2), ?_, rfl⟩
    exact Finset.mem_product.mpr ⟨hm1, hm2⟩

/-- **Supermultiplicativity of the independence number**: `I(S ⊗ T) ≥ I(S) · I(T)`.

This is the inequality that makes `n ↦ log I(T^{⊗n})` superadditive, so that Fekete's lemma will
give the existence of the asymptotic independence number
`Ī(T) = limₙ I(T^{⊗n})^{1/n} = supₙ I(T^{⊗n})^{1/n}` in the next tranche.  The reverse
inequality is false: AVW's Example 5.1 exhibits tensors with `Ī(A ⊗ B) ≫ Ī(A) · Ī(B)`. -/
theorem independenceNumber_coordinateProduct_ge [NoZeroDivisors K]
    [∀ i, Fintype (κ i)] [∀ i, DecidableEq (κ i)]
    [∀ i, Fintype (κ' i)] [∀ i, DecidableEq (κ' i)]
    (T : (∀ i, κ i) → K) (T' : (∀ i, κ' i) → K) :
    independenceNumber T * independenceNumber T' ≤
      independenceNumber (coordinateProduct T T') := by
  classical
  obtain ⟨S, hS, hcard⟩ := exists_independentSet_card_eq T
  obtain ⟨S', hS', hcard'⟩ := exists_independentSet_card_eq T'
  have hprod := (hS.coordinateProduct hS').card_le_independenceNumber
  have himg : ((S ×ˢ S').image pairTriple).card = S.card * S'.card := by
    rw [Finset.card_image_of_injective _ pairTriple_injective, Finset.card_product]
  rw [himg, hcard, hcard'] at hprod
  exact hprod

end Product

section Diagonal

variable (K : Type u) [CommSemiring K] (ι : Type v) [Fintype ι] [DecidableEq ι]

/-- The coefficient function of the independent tensor `⟨|ι|⟩`: the coefficient is `1` on the
constant triples `(s, s, s)` and `0` elsewhere. -/
def diagonalCoefficients : (∀ _ : Leg, ι) → K :=
  fun p ↦ if ∀ i, p i = p .X then 1 else 0

omit [Fintype ι] in
/-- The coefficient of `⟨|ι|⟩` at a constant triple is `1`. -/
@[simp] theorem diagonalCoefficients_const (s : ι) :
    diagonalCoefficients K ι (fun _ ↦ s) = 1 := by
  simp [diagonalCoefficients]

omit [Fintype ι] in
/-- A term of `⟨|ι|⟩` is a constant triple. -/
theorem const_of_diagonalCoefficients_ne_zero {p : ∀ _ : Leg, ι}
    (h : diagonalCoefficients K ι p ≠ 0) : ∀ i, p i = p .X := by
  by_contra hcon
  rw [diagonalCoefficients, if_neg hcon] at h
  exact h rfl

/-- The diagonal set of terms of `⟨|ι|⟩`. -/
def diagonalTerms : Finset (∀ _ : Leg, ι) :=
  (Finset.univ : Finset ι).image fun s _ ↦ s

/-- The diagonal terms are exactly the constant triples. -/
theorem mem_diagonalTerms {p : ∀ _ : Leg, ι} :
    p ∈ diagonalTerms ι ↔ ∀ i, p i = p .X := by
  classical
  constructor
  · intro hp
    obtain ⟨s, -, rfl⟩ := Finset.mem_image.mp hp
    intro i
    rfl
  · intro hp
    refine Finset.mem_image.mpr ⟨p .X, Finset.mem_univ _, ?_⟩
    funext i
    exact (hp i).symm

/-- The diagonal has exactly `|ι|` terms. -/
theorem card_diagonalTerms : (diagonalTerms ι).card = Fintype.card ι := by
  classical
  rw [diagonalTerms, Finset.card_image_of_injective _ ?inj, Finset.card_univ]
  case inj =>
    intro s t hst
    exact congrFun hst .X

/-- The diagonal terms form an independent set of `⟨|ι|⟩`. -/
theorem independentSet_diagonalTerms [Nontrivial K] :
    IndependentSet (diagonalCoefficients K ι) (diagonalTerms ι) where
  ne_zero p hp := by
    rw [mem_diagonalTerms] at hp
    rw [diagonalCoefficients, if_pos hp]
    exact one_ne_zero
  distinct p hp q hq i hpq := by
    rw [mem_diagonalTerms] at hp hq
    funext j
    rw [hp j, hq j, ← hp i, ← hq i, hpq]
  closed p hp _ := by
    rw [mem_diagonalTerms]
    exact const_of_diagonalCoefficients_ne_zero K ι hp

/-- **The independence number of the independent tensor**: `I(⟨r⟩) = r`.

The diagonal itself is an independent set of the right size, and no independent set can exceed
the number of variables on a leg. -/
theorem independenceNumber_diagonalCoefficients [Nontrivial K] :
    independenceNumber (diagonalCoefficients K ι) = Fintype.card ι := by
  classical
  refine le_antisymm (independenceNumber_le_card _ .X) ?_
  have h := (independentSet_diagonalTerms K ι).card_le_independenceNumber
  rwa [card_diagonalTerms] at h

omit [Fintype ι] [DecidableEq ι] in
/-- **The independence number of the all-ones tensor is at most one.**  More generally a tensor
whose support is a full combinatorial box has no two independent terms: mixing the `X`
coordinate of one with the `Y` and `Z` coordinates of the other produces a term of `T`, and
closure then identifies the two.

Together with `independenceNumber_diagonalCoefficients` this is the promised counterexample to
sub-support monotonicity: the diagonal is a sub-support of the all-ones tensor, yet has a strictly
larger independence number as soon as `|ι| ≥ 2`. -/
theorem independenceNumber_const_one_le [Nontrivial K] :
    independenceNumber (fun _ : ∀ _ : Leg, ι ↦ (1 : K)) ≤ 1 := by
  classical
  refine independenceNumber_le fun S hS ↦ ?_
  by_contra hcard
  rw [not_le] at hcard
  obtain ⟨p, hp, q, hq, hpq⟩ := Finset.one_lt_card.mp hcard
  have hsel : ∀ i, (if i = Leg.X then p else q) ∈ S := by
    intro i
    by_cases h : i = Leg.X <;> simp [h, hp, hq]
  have := hS.mix_eq (fun i ↦ if i = Leg.X then p else q) hsel one_ne_zero
  have hXY := this .X .Y
  simp only [if_neg (by decide : ¬ (Leg.Y = Leg.X))] at hXY
  exact hpq hXY

/-- The all-ones tensor on a nonempty index type has independence number exactly one. -/
theorem independenceNumber_const_one [Nontrivial K] [Nonempty ι] :
    independenceNumber (fun _ : ∀ _ : Leg, ι ↦ (1 : K)) = 1 := by
  refine le_antisymm (independenceNumber_const_one_le K ι) ?_
  exact one_le_independenceNumber (p := fun _ ↦ Classical.arbitrary ι) one_ne_zero

end Diagonal

section AbstractTensor

variable {K : Type u} [CommSemiring K] {κ : Leg → Type v}
variable [∀ i, Fintype (κ i)] [∀ i, DecidableEq (κ i)]

/-- The abstract three-legged tensor with coefficient function `T` in the standard coordinate
spaces: `∑ p, T p · e_{p X} ⊗ e_{p Y} ⊗ e_{p Z}`.

It is the inverse of the house coefficient equivalence `standardCoordinateEquiv` of
`Tensor/Coordinates.lean`, named for readability; `coordinateTensor_eq_sum` recovers the explicit
sum. -/
noncomputable def coordinateTensor (T : (∀ i, κ i) → K) : Tensor3 K (CoordinateSpace K κ) :=
  (standardCoordinateEquiv (K := K) (κ := κ)).symm T

omit [∀ i, DecidableEq (κ i)] in
/-- The coefficient function of `coordinateTensor T` is `T`: the definition really is the tensor
with the prescribed coordinates.  This is the bridge to the house coordinate API of
`Tensor.Coordinates`. -/
@[simp] theorem standardCoordinateEquiv_coordinateTensor (T : (∀ i, κ i) → K) :
    standardCoordinateEquiv (K := K) (κ := κ) (coordinateTensor T) = T :=
  (standardCoordinateEquiv (K := K) (κ := κ)).apply_symm_apply T

/-- `coordinateTensor T` written out as the sum of scaled standard-basis pure tensors, the form in
which support arguments read off individual terms. -/
theorem coordinateTensor_eq_sum (T : (∀ i, κ i) → K) :
    coordinateTensor T =
      ∑ p : (∀ i, κ i), T p • pure (K := K) (fun i ↦ Pi.single (p i) (1 : K)) := by
  classical
  refine standardCoordinate_ext (K := K) (κ := κ) fun q ↦ ?_
  rw [standardCoordinateEquiv_coordinateTensor,
    standardCoordinateEquiv_sum_single (K := K) (κ := κ) T (fun p ↦ p) q]
  simp [Finset.filter_eq']

omit [∀ i, DecidableEq (κ i)] in
/-- The all-ones coordinate tensor is a single pure tensor, hence has slice rank at most one.  With
`coordinateTensor_diagonalCoefficients` this is the tensor-level form of the non-monotonicity
example discussed in the module header. -/
theorem coordinateTensor_const_one :
    coordinateTensor (fun _ : ∀ i, κ i ↦ (1 : K)) =
      pure (K := K) (fun i ↦ (fun _ : κ i ↦ (1 : K))) := by
  refine standardCoordinate_ext (K := K) (κ := κ) fun q ↦ ?_
  rw [standardCoordinateEquiv_coordinateTensor, standardCoordinateEquiv_pure]
  simp

end AbstractTensor

/-! ### The two models of the independent tensor

`diagonalCoefficients K ι` and `Tensor.diagonalTensor K ι` of `Tensor/SliceRank.lean` are the
coefficient function and the abstract tensor of the same object `⟨|ι|⟩`.  `coordinateTensor` turns
the first into the second, so `independenceNumber_diagonalCoefficients` and
`sliceRank_diagonalTensor` are statements about one tensor rather than two. -/

section DiagonalModel

variable {K : Type u} [CommSemiring K] {ι : Type v} [Fintype ι] [DecidableEq ι]

/-- **The two presentations of `⟨|ι|⟩` agree**: the abstract tensor with coefficient function
`diagonalCoefficients K ι` is the diagonal tensor `diagonalTensor K ι`. -/
theorem coordinateTensor_diagonalCoefficients :
    coordinateTensor (diagonalCoefficients K ι) = diagonalTensor K ι := by
  refine standardCoordinate_ext (K := K) (κ := fun _ : Leg ↦ ι) fun q ↦ ?_
  rw [standardCoordinateEquiv_coordinateTensor, standardCoordinateEquiv_diagonalTensor]
  rfl

end DiagonalModel


section SliceRankBridge

variable {K : Type u} [CommSemiring K] {κ : Leg → Type v}
variable [∀ i, Fintype (κ i)] [∀ i, DecidableEq (κ i)]

/-- **From an independent set to a diagonal restriction.**  If `S` is an independent set of terms
of `T` whose coefficients are units, then legwise linear maps carry the abstract tensor
`coordinateTensor T` onto the diagonal tensor indexed by `S`.

Proof sketch: on legs `X` and `Y` send the basis vector of a variable used by `S` to the basis
vector of the unique element of `S` using it, and kill the unused variables; on leg `Z` do the
same but scale by the inverse coefficient.  Expanding `coordinateTensor T` in coordinates, the
image coefficient at a triple `q` of elements of `S` is `T p₀ · (T q_Z)⁻¹`, where `p₀` reads the
`i`-th coordinate off `q i`.  If the three entries of `q` agree this is `1`; otherwise `p₀` uses
only variables of `S`, so if it were a term of `T` closure would place it in `S` and injectivity
of the three projections would force the three entries of `q` to agree.  Hence the image is
exactly the diagonal. -/
theorem IndependentSet.restricts_diagonalTensor {T : (∀ i, κ i) → K}
    {S : Finset (∀ i, κ i)} (h : IndependentSet T S) (hu : ∀ p ∈ S, IsUnit (T p)) :
    Restricts (coordinateTensor T) (diagonalTensor K {p // p ∈ S}) := by
  classical
  -- A right inverse for the coefficient of each chosen term.
  have hinv : ∀ s : {p // p ∈ S}, ∃ b : K, T s.1 * b = 1 := fun s ↦
    (hu s.1 s.2).exists_right_inv
  choose inv hinv using hinv
  set w : Leg → {p // p ∈ S} → K := fun i s ↦ if i = Leg.Z then inv s else 1 with hw
  refine ⟨fun i ↦ LinearMap.pi fun s : {p // p ∈ S} ↦
    w i s • LinearMap.proj ((s : ∀ j, κ j) i), ?_⟩
  set f : ∀ i, CoordinateSpace K κ i →ₗ[K] ({p // p ∈ S} → K) :=
    fun i ↦ LinearMap.pi fun s : {p // p ∈ S} ↦
      w i s • LinearMap.proj ((s : ∀ j, κ j) i) with hf
  have hfapply : ∀ (i : Leg) (x : κ i → K) (s : {p // p ∈ S}),
      f i x s = w i s * x ((s : ∀ j, κ j) i) := by
    intro i x s
    simp [hf]
  -- Compare both sides in standard coordinates on the target.
  refine standardCoordinate_ext (K := K) (κ := fun _ : Leg ↦ {p // p ∈ S}) ?_
  intro q
  -- Left-hand side: expand the image of the coordinate expansion.
  have hlhs : standardCoordinateEquiv (K := K) (κ := fun _ : Leg ↦ {p // p ∈ S})
      (map f (coordinateTensor T)) q =
        ∑ p : (∀ i, κ i), T p * ∏ i, (if (q i : ∀ j, κ j) i = p i then w i (q i) else 0) := by
    rw [coordinateTensor_eq_sum, map_sum, map_sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun p _ ↦ ?_
    rw [LinearMap.map_smul, map_smul, map_pure]
    show T p * standardCoordinateEquiv (K := K) (κ := fun _ : Leg ↦ {p // p ∈ S})
      (pure (K := K) fun i ↦ f i (Pi.single (p i) (1 : K))) q = _
    rw [standardCoordinateEquiv_pure]
    refine congrArg (fun z ↦ T p * z) (Finset.prod_congr rfl fun i _ ↦ ?_)
    rw [hfapply]
    simp [Pi.single_apply]
  -- The mixed triple read off `q`.
  set p₀ : ∀ i, κ i := fun i ↦ (q i : ∀ j, κ j) i with hp₀
  have hprod : ∀ p : ∀ i, κ i,
      (∏ i, (if (q i : ∀ j, κ j) i = p i then w i (q i) else 0)) =
        if p = p₀ then ∏ i, w i (q i) else 0 := by
    intro p
    rw [prod_leg, prod_leg]
    by_cases hx : (q .X : ∀ j, κ j) .X = p .X <;>
      by_cases hy : (q .Y : ∀ j, κ j) .Y = p .Y <;>
        by_cases hz : (q .Z : ∀ j, κ j) .Z = p .Z <;>
      simp only [hx, hy, hz, if_true, if_false, mul_zero, zero_mul]
    · rw [if_pos]
      funext i
      cases i <;> simp [hp₀, hx, hy, hz]
    all_goals
      rw [if_neg]
      intro hpp
      subst hpp
      simp_all
  rw [hlhs, Finset.sum_congr rfl fun p _ ↦ congrArg (fun z ↦ T p * z) (hprod p)]
  rw [Finset.sum_eq_single p₀]
  · -- The remaining single term, compared with the diagonal coefficient.
    rw [if_pos rfl]
    have hwprod : (∏ i, w i (q i)) = inv (q .Z) := by
      rw [prod_leg]
      simp [hw]
    rw [hwprod, standardCoordinateEquiv_diagonalTensor]
    by_cases hconst : ∀ i, q i = q .X
    · -- All three entries of `q` are the same chosen term.
      have hq : ∀ i, q i = q .Z := by
        intro i
        rw [hconst i, (hconst .Z).symm]
      have hp₀eq : p₀ = ((q .Z : ∀ j, κ j)) := by
        funext i
        rw [hp₀]
        simp only
        rw [hq i]
      rw [if_pos hconst, hp₀eq]
      exact hinv (q .Z)
    · -- Distinct entries: the mixed triple cannot be a term of `T`.
      rw [if_neg hconst]
      have hzero : T p₀ = 0 := by
        by_contra hne
        have hsel : ∀ i, ((q i : ∀ j, κ j)) ∈ S := fun i ↦ (q i).2
        have := h.mix_eq (fun i ↦ (q i : ∀ j, κ j)) hsel hne
        exact hconst fun i ↦ Subtype.ext (this i .X)
      rw [hzero, zero_mul]
  · intro p _ hp
    rw [if_neg hp, mul_zero]
  · intro hmem
    exact absurd (Finset.mem_univ p₀) hmem

/-- **From an independent set to a subrank bound.**  An independent set of terms of `T` whose
coefficients are units is a diagonal restriction of `coordinateTensor T`, hence a witness for its
subrank.  This is the sharpest of the three barrier bounds: `card_le_sliceRank` and
`independenceNumber_le_rank` both factor through it. -/
theorem IndependentSet.card_le_subrank {K : Type u} [Field K] {κ : Leg → Type v}
    [∀ i, Fintype (κ i)] [∀ i, DecidableEq (κ i)]
    {T : (∀ i, κ i) → K} {S : Finset (∀ i, κ i)} (h : IndependentSet T S) :
    S.card ≤ subrank (coordinateTensor T) := by
  classical
  have hu : ∀ p ∈ S, IsUnit (T p) := fun p hp ↦ isUnit_iff_ne_zero.mpr (h.ne_zero p hp)
  exact le_subrank_of_restricts
    ((h.restricts_diagonalTensor hu).trans
      (Isomorphic.diagonalTensor_congr (K := K)
        (Fintype.equivFinOfCardEq (α := {p // p ∈ S}) (by simp))).restricts)

/-- **The finite slice-rank barrier for the independence number.**  Over a field, an independent
set of terms of `T` is no larger than the slice rank of the abstract tensor with coefficients `T`.

This is the finite bridge from the Alman--Vassilevska Williams framework to Tao's diagonal lemma:
an independent set of size `m` is extracted by *legwise linear maps* (a zeroing out followed by a
diagonal rescaling), so it bounds the subrank, and `subrank_le_sliceRank` --- which is
`card_le_sliceRank_of_restricts_diagonalTensor` in the subrank packaging --- caps that by the slice
rank.  Note that the bound holds for restrictions of `T` only; it does not descend to arbitrary
sub-supports of `T`, under which slice rank is not monotone. -/
theorem IndependentSet.card_le_sliceRank {K : Type u} [Field K] {κ : Leg → Type v}
    [∀ i, Fintype (κ i)] [∀ i, DecidableEq (κ i)]
    {T : (∀ i, κ i) → K} {S : Finset (∀ i, κ i)} (h : IndependentSet T S) :
    S.card ≤ sliceRank (coordinateTensor T) :=
  h.card_le_subrank.trans (subrank_le_sliceRank _)

/-- **`I(T) ≤ Q(T)`** over a field: the independence number of a coordinate tensor is at most the
subrank of the tensor it defines.  Together with `subrank_le_sliceRank` and `sliceRank_le_rank`
this makes the barrier chain `I(T) ≤ Q(T) ≤ sliceRank(T) ≤ rank(T)` explicit; it is the form in
which the Alman--Vassilevska Williams framework uses the bound. -/
theorem independenceNumber_le_subrank {K : Type u} [Field K] {κ : Leg → Type v}
    [∀ i, Fintype (κ i)] [∀ i, DecidableEq (κ i)] (T : (∀ i, κ i) → K) :
    independenceNumber T ≤ subrank (coordinateTensor T) :=
  independenceNumber_le fun _ hS ↦ hS.card_le_subrank

/-- **`I(T) ≤ sliceRank(T)`** over a field: the independence number of a coordinate tensor is at
most the slice rank of the tensor it defines. -/
theorem independenceNumber_le_sliceRank {K : Type u} [Field K] {κ : Leg → Type v}
    [∀ i, Fintype (κ i)] [∀ i, DecidableEq (κ i)] (T : (∀ i, κ i) → K) :
    independenceNumber T ≤ sliceRank (coordinateTensor T) :=
  (independenceNumber_le_subrank T).trans (subrank_le_sliceRank _)

/-- **`I(T) ≤ rank(T)`** over a field, by composing the slice-rank barrier with
`sliceRank_le_rank`.  Applied to tensor powers this is the elementary upper bound
`Ī(T) ≤ R̃(T)` of AVW Section 2 on the asymptotic independence number. -/
theorem independenceNumber_le_rank {K : Type u} [Field K] {κ : Leg → Type v}
    [∀ i, Fintype (κ i)] [∀ i, DecidableEq (κ i)] (T : (∀ i, κ i) → K) :
    independenceNumber T ≤ rank (coordinateTensor T) :=
  (independenceNumber_le_sliceRank T).trans (sliceRank_le_rank _)

end SliceRankBridge

/-! ## Relabelling the variables of a leg

The independence number is *basis-dependent* (see the module header), but it is invariant under a
bijective renaming of the variables on each leg: relabelling permutes the terms of the coefficient
table without changing which triples share a coordinate.  This is what makes the index-type
bookkeeping of tensor powers --- `(∀ i, κ i × κ' i)` versus `∀ i, Fin n → κ i` --- free of
mathematical content, and it is used below to identify the iterated Kronecker product with the
binary one.

The distinction to keep in mind: this is a relabelling of *indices*, not a change of *basis*.  A
legwise linear isomorphism of the ambient coordinate spaces does not preserve `I`.

`independenceNumber_smul_of_isUnit` is the other invariance of the same kind: a unit scalar factor
moves no coefficient into or out of the support, so it does not move `I` either. -/

section Relabel

variable {K : Type u} [CommSemiring K] {κ : Leg → Type v} {κ' : Leg → Type w}

/-- Relabel the variables of every leg along a bijection: `coordinateRelabel e T` is the
coefficient table over the new index types whose value at `p` is the value of `T` at the
preimage of `p`. -/
def coordinateRelabel (e : ∀ i, κ i ≃ κ' i) (T : (∀ i, κ i) → K) : (∀ i, κ' i) → K :=
  fun p ↦ T fun i ↦ (e i).symm (p i)

omit [CommSemiring K] in
/-- Evaluating a relabelled table pulls the index back through the bijections. -/
@[simp] theorem coordinateRelabel_apply (e : ∀ i, κ i ≃ κ' i) (T : (∀ i, κ i) → K)
    (p : ∀ i, κ' i) : coordinateRelabel e T p = T fun i ↦ (e i).symm (p i) := rfl

omit [CommSemiring K] in
/-- Relabelling back along the inverse bijections recovers the original table. -/
theorem coordinateRelabel_symm (e : ∀ i, κ i ≃ κ' i) (T : (∀ i, κ i) → K) :
    coordinateRelabel (fun i ↦ (e i).symm) (coordinateRelabel e T) = T := by
  funext p
  simp [coordinateRelabel]

/-- The bijection of index triples induced by one bijection of index types per leg. -/
def relabelTriple (e : ∀ i, κ i ≃ κ' i) : (∀ i, κ i) ≃ (∀ i, κ' i) := Equiv.piCongrRight e

/-- **Independent sets transport along a relabelling.**  The image of an independent set of terms
of `T` under a legwise bijection of index types is an independent set of terms of the relabelled
table.

Proof sketch: all three conditions are read off coordinatewise, because `relabelTriple e` acts on
each leg separately by a bijection.  Nonvanishing is immediate; two images agreeing on leg `i`
have preimages agreeing on leg `i` by injectivity of `e i`; and a term of the relabelled table
boxed by the image of `S` has a preimage that is a term of `T` boxed by `S`, so closure for `S`
applies. -/
theorem IndependentSet.coordinateRelabel [DecidableEq (∀ i, κ' i)]
    {T : (∀ i, κ i) → K} {S : Finset (∀ i, κ i)} (h : IndependentSet T S)
    (e : ∀ i, κ i ≃ κ' i) :
    IndependentSet (Tensor.coordinateRelabel e T) (S.image (relabelTriple e)) where
  ne_zero p hp := by
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
    simpa [Tensor.coordinateRelabel, relabelTriple] using h.ne_zero q hq
  distinct p hp r hr i hpr := by
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hr
    have : q i = s i := (e i).injective hpr
    rw [h.distinct q hq s hs i this]
  closed p hp hbox := by
    have hp' : T (fun i ↦ (e i).symm (p i)) ≠ 0 := hp
    have hbox' : ∀ i, ∃ q ∈ S, q i = (e i).symm (p i) := by
      intro i
      obtain ⟨r, hr, hri⟩ := hbox i
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hr
      exact ⟨q, hq, by rw [← hri]; simp [relabelTriple]⟩
    refine Finset.mem_image.mpr ⟨fun i ↦ (e i).symm (p i), h.closed _ hp' hbox', ?_⟩
    funext i
    simp [relabelTriple]

/-- **The independence number is invariant under relabelling the variables of the legs.**  This is
*not* invariance under legwise isomorphism, which is false; only bijective renamings of the
variables are allowed. -/
theorem independenceNumber_coordinateRelabel
    [∀ i, Fintype (κ i)] [∀ i, DecidableEq (κ i)]
    [∀ i, Fintype (κ' i)] [∀ i, DecidableEq (κ' i)]
    (e : ∀ i, κ i ≃ κ' i) (T : (∀ i, κ i) → K) :
    independenceNumber (coordinateRelabel e T) = independenceNumber T := by
  classical
  refine le_antisymm (independenceNumber_le fun S hS ↦ ?_) (independenceNumber_le fun S hS ↦ ?_)
  · have h2 := hS.coordinateRelabel (fun i ↦ (e i).symm)
    rw [coordinateRelabel_symm] at h2
    have := h2.card_le_independenceNumber
    rwa [Finset.card_image_of_injective _ (relabelTriple (fun i ↦ (e i).symm)).injective] at this
  · have h2 := hS.coordinateRelabel e
    have := h2.card_le_independenceNumber
    rwa [Finset.card_image_of_injective _ (relabelTriple e).injective] at this

/-- **The independence number does not see a unit scalar factor.**  Scaling a coefficient table by
a unit changes neither its support nor, therefore, its independent sets, so the independence number
is unchanged.

Proof sketch: the three clauses of `IndependentSet` mention the coefficients only through
`T p ≠ 0`, and multiplication by a unit preserves and reflects nonvanishing, so the two tables have
the same independent sets and hence the same set `independenceCards` of admissible cardinalities. -/
theorem independenceNumber_smul_of_isUnit
    [∀ i, Fintype (κ i)] [∀ i, DecidableEq (κ i)] {c : K} (hc : IsUnit c)
    (T : (∀ i, κ i) → K) : independenceNumber (c • T) = independenceNumber T := by
  obtain ⟨u, rfl⟩ := hc
  have hne : ∀ p, ((u : K) • T) p ≠ 0 ↔ T p ≠ 0 := by
    intro p
    constructor
    · intro h hz
      exact h (by simp [Pi.smul_apply, hz])
    · intro h hz
      refine h ?_
      have : (↑u⁻¹ : K) * ((↑u : K) * T p) = T p := by
        rw [← mul_assoc, Units.inv_mul, one_mul]
      rw [← this, show (↑u : K) * T p = ((u : K) • T) p from rfl, hz, mul_zero]
  have hind : ∀ S : Finset (∀ i, κ i), IndependentSet ((u : K) • T) S ↔ IndependentSet T S := by
    intro S
    constructor
    · exact fun h ↦ ⟨fun p hp ↦ (hne p).mp (h.ne_zero p hp), h.distinct,
        fun p hp hq ↦ h.closed p ((hne p).mpr hp) hq⟩
    · exact fun h ↦ ⟨fun p hp ↦ (hne p).mpr (h.ne_zero p hp), h.distinct,
        fun p hp hq ↦ h.closed p ((hne p).mp hp) hq⟩
  have hcards : independenceCards ((u : K) • T) = independenceCards T := by
    ext n
    exact ⟨fun ⟨S, hS, hn⟩ ↦ ⟨S, (hind S).mp hS, hn⟩, fun ⟨S, hS, hn⟩ ↦ ⟨S, (hind S).mpr hS, hn⟩⟩
  unfold independenceNumber
  rw [hcards]

end Relabel

/-! ## Kronecker powers in coordinates

`coordinatePower T n` is the `n`-fold Kronecker power of a coefficient table, indexed by *words*:
a variable of leg `i` of `T^{⊗n}` is a word `Fin n → κ i`, and the coefficient of a triple of words
is the product of the `n` coefficients read letter by letter.  This is the index convention that
matches `Tensor.power`, whose leg spaces are `n`th tensor powers, and it is the one in which the
type-counting arguments of the barrier framework are stated.

Two index bijections do all the bookkeeping: `appendIndexEquiv` concatenates an `m`-letter word
with an `n`-letter word, and `snocIndexEquiv` appends one letter.  Through
`independenceNumber_coordinateRelabel` they turn the binary supermultiplicativity
`independenceNumber_coordinateProduct_ge` into the additive law
`independenceNumber_coordinatePower_add_ge`, which is the hypothesis of Fekete's lemma for the
asymptotic independence number of `Tensor/AsymptoticIndependenceNumber.lean`.

`coordinateWordProduct` is the *heterogeneous* form of the same product, in which each position
carries its own index family and its own table; `coordinatePower` is its constant-family case
(`coordinateWordProduct_const`).  Clients that multiply tables of varying shapes position by
position --- block words in `Tensor/CoordinateBlockWord.lean`, matrix-multiplication word products
in `MatrixMultiplication/IndependentDiagonal.lean` --- instantiate it rather than rebuilding the
product. -/

section Power

variable {K : Type u} [CommSemiring K] {κ : Leg → Type v}

/-- The positionwise product of a heterogeneous family of coefficient tables: position `t` carries
its own index family `κ t` and table `T t`.  `coordinatePower` is the constant-family case. -/
def coordinateWordProduct {n : ℕ} {κ : Fin n → Leg → Type v} (T : ∀ t, (∀ i, κ t i) → K) :
    (∀ i, ∀ t, κ t i) → K := fun v ↦ ∏ t, T t (fun i ↦ v i t)

/-- The coefficient of a triple of words is the product of the coefficients of its letters, each
read in its own position's table. -/
@[simp] theorem coordinateWordProduct_apply {n : ℕ} {κ : Fin n → Leg → Type v}
    (T : ∀ t, (∀ i, κ t i) → K) (v : ∀ i, ∀ t, κ t i) :
    coordinateWordProduct T v = ∏ t, T t (fun i ↦ v i t) := rfl

/-- The **`n`-fold Kronecker power** of a coefficient table, in the word indexing: the variables of
leg `i` are the words `Fin n → κ i`, and the coefficient of a triple of words is the product of the
coefficients of its `n` letters.  For `n = 0` every coefficient is the empty product `1`.

This is `coordinateWordProduct` at a constant family (`coordinatePower_eq_coordinateWordProduct`);
it is kept as a definition of its own because it is the head symbol of the power calculus below. -/
def coordinatePower (T : (∀ i, κ i) → K) (n : ℕ) : (∀ i, Fin n → κ i) → K :=
  fun p ↦ ∏ k : Fin n, T fun i ↦ p i k

/-- The coefficient of a triple of words is the product of the coefficients of its letters. -/
@[simp] theorem coordinatePower_apply (T : (∀ i, κ i) → K) (n : ℕ) (p : ∀ i, Fin n → κ i) :
    coordinatePower T n p = ∏ k : Fin n, T fun i ↦ p i k := rfl

/-- **The constant-family word product is the Kronecker power**, on the nose: for a constant index
family the word type `∀ i, ∀ _ : Fin n, κ i` *is* `∀ i, Fin n → κ i`, and both tables are the same
product over positions. -/
theorem coordinateWordProduct_const (A : (∀ i, κ i) → K) (n : ℕ) :
    coordinateWordProduct (fun _ : Fin n ↦ A) = coordinatePower A n := rfl

/-- The Kronecker power, read as a word product over a constant family. -/
theorem coordinatePower_eq_coordinateWordProduct (A : (∀ i, κ i) → K) (n : ℕ) :
    coordinatePower A n = coordinateWordProduct (fun _ : Fin n ↦ A) := rfl

/-- **Relabelling commutes with Kronecker powers**: renaming the variables of every leg and then
taking the `k`-th power is the same as taking the power and renaming its words letterwise. -/
theorem coordinatePower_coordinateRelabel {κ' : Leg → Type w} (e : ∀ i, κ i ≃ κ' i)
    (T : (∀ i, κ i) → K) (k : ℕ) :
    coordinatePower (coordinateRelabel e T) k
      = coordinateRelabel (fun i ↦ Equiv.piCongrRight fun _ : Fin k ↦ e i)
          (coordinatePower T k) := rfl

/-- Concatenation of an `m`-letter word with an `n`-letter word, as a bijection of index types. -/
def appendIndexEquiv (α : Type v) (m n : ℕ) : (Fin m → α) × (Fin n → α) ≃ (Fin (m + n) → α) :=
  (Equiv.sumArrowEquivProdArrow (Fin m) (Fin n) α).symm.trans
    (Equiv.arrowCongr finSumFinEquiv (Equiv.refl α))

/-- Appending one letter to an `n`-letter word, as a bijection of index types. -/
def snocIndexEquiv (α : Type v) (n : ℕ) : (Fin n → α) × α ≃ (Fin (n + 1) → α) where
  toFun q := Fin.snoc q.1 q.2
  invFun p := (fun k ↦ p k.castSucc, p (Fin.last n))
  left_inv q := by
    rcases q with ⟨f, x⟩
    simp
  right_inv p := Fin.snoc_init_self p

/-- **The Kronecker power splits as a Kronecker product**: relabelling the variables of
`T^{⊗m} ⊗ T^{⊗n}` by word concatenation gives `T^{⊗(m+n)}`.

Proof sketch: the coefficient of a concatenated triple of words is the product over the `m + n`
letters, which `Fin.prod_univ_add` splits into the product over the first `m` letters times the
product over the last `n`. -/
theorem coordinateRelabel_coordinateProduct_coordinatePower (T : (∀ i, κ i) → K) (m n : ℕ) :
    coordinateRelabel (fun i ↦ appendIndexEquiv (κ i) m n)
        (coordinateProduct (coordinatePower T m) (coordinatePower T n)) =
      coordinatePower T (m + n) := by
  funext p
  show (∏ k : Fin m, T fun i ↦ _) * (∏ k : Fin n, T fun i ↦ _) = _
  rw [coordinatePower_apply, Fin.prod_univ_add]
  rfl

/-- The one-letter form of the previous lemma: relabelling `T^{⊗n} ⊗ T` by appending a letter
gives `T^{⊗(n+1)}`.  This is the shape the induction identifying `coordinateTensor (T^{⊗n})` with
`Tensor.power (coordinateTensor T) n` consumes. -/
theorem coordinateRelabel_coordinateProduct_succ (T : (∀ i, κ i) → K) (n : ℕ) :
    coordinateRelabel (fun i ↦ snocIndexEquiv (κ i) n)
        (coordinateProduct (coordinatePower T n) T) = coordinatePower T (n + 1) := by
  funext p
  show (∏ k : Fin n, T fun i ↦ _) * T _ = _
  rw [coordinatePower_apply, Fin.prod_univ_castSucc]
  rfl

/-- Flattening an `n`-letter word of `k`-letter words into a single `n·k`-letter word, as a
bijection of index types.  This is the identification behind `Ī(T^{⊗k}) = Ī(T)^k`. -/
def flattenIndexEquiv (α : Type v) (n k : ℕ) : (Fin n → Fin k → α) ≃ (Fin (n * k) → α) :=
  (Equiv.curry (Fin n) (Fin k) α).symm.trans (Equiv.arrowCongr finProdFinEquiv (Equiv.refl α))

/-- **Kronecker powers iterate.**  Relabelling the variables of `(T^{⊗k})^{⊗n}` by flattening
words of words gives `T^{⊗(n·k)}`.

Proof sketch: the coefficient of a flattened triple is the double product over the `n` outer and
`k` inner positions, which `Fintype.prod_prod_type` turns into a product over pairs and
`Fintype.prod_equiv finProdFinEquiv` into a product over the `n·k` positions. -/
theorem coordinateRelabel_coordinatePower_coordinatePower (T : (∀ i, κ i) → K) (n k : ℕ) :
    coordinateRelabel (fun i ↦ flattenIndexEquiv (κ i) n k)
        (coordinatePower (coordinatePower T k) n) = coordinatePower T (n * k) := by
  funext p
  show (∏ j : Fin n, ∏ l : Fin k, T fun i ↦ p i (finProdFinEquiv (j, l))) = _
  rw [coordinatePower_apply]
  calc (∏ j : Fin n, ∏ l : Fin k, T fun i ↦ p i (finProdFinEquiv (j, l)))
      = ∏ x : Fin n × Fin k, T fun i ↦ p i (finProdFinEquiv x) :=
        (Fintype.prod_prod_type (fun x : Fin n × Fin k ↦ T fun i ↦ p i (finProdFinEquiv x))).symm
    _ = ∏ m : Fin (n * k), T fun i ↦ p i m :=
        Fintype.prod_equiv finProdFinEquiv _ _ fun _ ↦ rfl

/-- The first Kronecker power is the table itself, up to the relabelling that reads a one-letter
word as a letter. -/
theorem coordinateRelabel_coordinatePower_one (T : (∀ i, κ i) → K) :
    coordinateRelabel (fun i ↦ Equiv.funUnique (Fin 1) (κ i)) (coordinatePower T 1) = T := by
  funext p
  simp [coordinateRelabel, coordinatePower]

/-! ### The sequence `n ↦ I(T^{⊗n})` -/

section Numbers

variable [∀ i, Fintype (κ i)] [∀ i, DecidableEq (κ i)]

/-- `I(T^{⊗1}) = I(T)`. -/
theorem independenceNumber_coordinatePower_one (T : (∀ i, κ i) → K) :
    independenceNumber (coordinatePower T 1) = independenceNumber T := by
  have h := independenceNumber_coordinateRelabel
    (fun i ↦ Equiv.funUnique (Fin 1) (κ i)) (coordinatePower T 1)
  rw [coordinateRelabel_coordinatePower_one] at h
  exact h.symm

/-- `I((T^{⊗k})^{⊗n}) = I(T^{⊗(n·k)})`: iterated Kronecker powers have the same independence
number as the flattened one. -/
theorem independenceNumber_coordinatePower_coordinatePower (T : (∀ i, κ i) → K) (n k : ℕ) :
    independenceNumber (coordinatePower (coordinatePower T k) n) =
      independenceNumber (coordinatePower T (n * k)) := by
  rw [← coordinateRelabel_coordinatePower_coordinatePower T n k,
    independenceNumber_coordinateRelabel]

/-- `I(T^{⊗0}) = 1`: the zeroth Kronecker power is the scalar `1` on one variable per leg. -/
theorem independenceNumber_coordinatePower_zero [Nontrivial K] (T : (∀ i, κ i) → K) :
    independenceNumber (coordinatePower T 0) = 1 := by
  refine le_antisymm ?_ ?_
  · have h := independenceNumber_le_card (coordinatePower T 0) .X
    simpa using h
  · exact one_le_independenceNumber (T := coordinatePower T 0)
      (p := fun _ ↦ default) (by simp)

/-- Every Kronecker power of a nonzero table has an independent term: the constant word built from
a single term of `T` has coefficient `T p ^ n ≠ 0`. -/
theorem one_le_independenceNumber_coordinatePower [NoZeroDivisors K]
    {T : (∀ i, κ i) → K} {p : ∀ i, κ i} (hp : T p ≠ 0) (n : ℕ) :
    1 ≤ independenceNumber (coordinatePower T n) := by
  refine one_le_independenceNumber (T := coordinatePower T n) (p := fun i _ ↦ p i) ?_
  have : coordinatePower T n (fun i _ ↦ p i) = T p ^ n := by simp
  rw [this]
  exact pow_ne_zero n hp

/-- `I(T^{⊗n}) ≤ |κ i|^n` for every leg `i`: a Kronecker power has `|κ i|^n` variables on leg `i`.
This is the geometric upper bound that Fekete's lemma needs in the supermultiplicative direction. -/
theorem independenceNumber_coordinatePower_le_pow (T : (∀ i, κ i) → K) (n : ℕ) (i : Leg) :
    independenceNumber (coordinatePower T n) ≤ Fintype.card (κ i) ^ n := by
  have h := independenceNumber_le_card (coordinatePower T n) i
  simpa using h

/-- **Supermultiplicativity along the power sequence**: `I(T^{⊗m}) · I(T^{⊗n}) ≤ I(T^{⊗(m+n)})`.

Proof sketch: `independenceNumber_coordinateProduct_ge` is the statement for the Kronecker product
of two tables; word concatenation
(`coordinateRelabel_coordinateProduct_coordinatePower`) identifies that product with
`T^{⊗(m+n)}`, and `independenceNumber_coordinateRelabel` transports the independence number
across the identification. -/
theorem independenceNumber_coordinatePower_add_ge [NoZeroDivisors K]
    (T : (∀ i, κ i) → K) (m n : ℕ) :
    independenceNumber (coordinatePower T m) * independenceNumber (coordinatePower T n) ≤
      independenceNumber (coordinatePower T (m + n)) := by
  rw [← coordinateRelabel_coordinateProduct_coordinatePower T m n,
    independenceNumber_coordinateRelabel]
  exact independenceNumber_coordinateProduct_ge _ _

/-- The iterated form: `I(T^{⊗m})^k ≤ I(T^{⊗(m·k)})`, by induction on `k` from the additive law. -/
theorem independenceNumber_coordinatePower_pow_le [NoZeroDivisors K] [Nontrivial K]
    (T : (∀ i, κ i) → K) (m k : ℕ) :
    independenceNumber (coordinatePower T m) ^ k ≤
      independenceNumber (coordinatePower T (m * k)) := by
  induction k with
  | zero => simp [independenceNumber_coordinatePower_zero]
  | succ k ih =>
      calc independenceNumber (coordinatePower T m) ^ (k + 1)
          = independenceNumber (coordinatePower T m) ^ k *
              independenceNumber (coordinatePower T m) := by ring
        _ ≤ independenceNumber (coordinatePower T (m * k)) *
              independenceNumber (coordinatePower T m) := Nat.mul_le_mul_right _ ih
        _ ≤ independenceNumber (coordinatePower T (m * k + m)) :=
              independenceNumber_coordinatePower_add_ge T _ _
        _ = independenceNumber (coordinatePower T (m * (k + 1))) := by rw [Nat.mul_succ]

end Numbers

/-! ### Zeroing outs commute with Kronecker powers -/

section ZeroOut

variable [∀ i, DecidableEq (κ i)]

/-- **Zeroing out a table and then powering is powering and then zeroing out**, to the words all of
whose letters survive.  This is the identity that makes the asymptotic independence number monotone
under zeroing outs.

Proof sketch: if every letter of every leg survives, both sides are the product of the surviving
coefficients; otherwise some letter is killed, the corresponding factor on the left is zero and the
membership test on the right fails. -/
theorem coordinatePower_coordinateZeroOut (T : (∀ i, κ i) → K) (A : ∀ i, Finset (κ i)) (n : ℕ) :
    coordinatePower (coordinateZeroOut T A) n =
      coordinateZeroOut (coordinatePower T n) (fun i ↦ Fintype.piFinset fun _ : Fin n ↦ A i) := by
  funext p
  by_cases hmem : ∀ i, p i ∈ (Fintype.piFinset fun _ : Fin n ↦ A i)
  · rw [coordinateZeroOut_of_mem hmem, coordinatePower_apply, coordinatePower_apply]
    refine Finset.prod_congr rfl fun k _ ↦ ?_
    exact coordinateZeroOut_of_mem fun i ↦ (Fintype.mem_piFinset.mp (hmem i)) k
  · rw [coordinateZeroOut_of_notMem hmem, coordinatePower_apply]
    rw [not_forall] at hmem
    obtain ⟨i, hi⟩ := hmem
    rw [Fintype.mem_piFinset, not_forall] at hi
    obtain ⟨k, hk⟩ := hi
    refine Finset.prod_eq_zero (Finset.mem_univ k) (coordinateZeroOut_of_notMem ?_)
    intro hall
    exact hk (hall i)

/-- **Monotonicity of the power sequence under zeroing outs**:
`I((T|_{X',Y',Z'})^{⊗n}) ≤ I(T^{⊗n})` for every `n`. -/
theorem independenceNumber_coordinatePower_coordinateZeroOut_le [∀ i, Fintype (κ i)]
    (T : (∀ i, κ i) → K) (A : ∀ i, Finset (κ i)) (n : ℕ) :
    independenceNumber (coordinatePower (coordinateZeroOut T A) n) ≤
      independenceNumber (coordinatePower T n) := by
  rw [coordinatePower_coordinateZeroOut]
  exact independenceNumber_coordinateZeroOut_le _ _

end ZeroOut

/-! ### The `n`-fold power of an independent set

The binary `IndependentSet.coordinateProduct` could be iterated, but the explicit description of
the `n`-fold power --- the words all of whose letters lie in `S` --- is what the pigeonhole
argument of `Tensor/MonomialIndependence.lean` needs, so it is proved directly. -/

section PowerSet

variable [∀ i, DecidableEq (κ i)]

/-- The `n`-fold power of a set of terms: the triples of words all of whose letters are triples
of `S`. -/
def powerIndependentSet [∀ i, Fintype (κ i)] (S : Finset (∀ i, κ i)) (n : ℕ) :
    Finset (∀ i, Fin n → κ i) :=
  (Fintype.piFinset fun _ : Fin n ↦ S).image fun g i k ↦ g k i

/-- Membership in the `n`-fold power of `S`: every letter is a term of `S`. -/
theorem mem_powerIndependentSet [∀ i, Fintype (κ i)] {S : Finset (∀ i, κ i)} {n : ℕ}
    {p : ∀ i, Fin n → κ i} :
    p ∈ powerIndependentSet S n ↔ ∀ k : Fin n, (fun i ↦ p i k) ∈ S := by
  constructor
  · intro hp
    obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp hp
    exact fun k ↦ Fintype.mem_piFinset.mp hg k
  · intro hp
    exact Finset.mem_image.mpr ⟨fun k i ↦ p i k, Fintype.mem_piFinset.mpr hp, rfl⟩

/-- The `n`-fold power of a set of `f` terms has `f ^ n` elements. -/
theorem card_powerIndependentSet [∀ i, Fintype (κ i)] (S : Finset (∀ i, κ i)) (n : ℕ) :
    (powerIndependentSet S n).card = S.card ^ n := by
  rw [powerIndependentSet, Finset.card_image_of_injective, Fintype.card_piFinset]
  · simp
  · intro g h hgh
    funext k i
    exact congrFun (congrFun hgh i) k

/-- **The `n`-fold power of an independent set is independent** for the `n`-fold Kronecker power.

Proof sketch: nonvanishing is a product of nonzero coefficients in a ring without zero divisors.
Two power words agreeing on leg `i` agree letter by letter on leg `i`, so injectivity of the `i`-th
projection on `S` identifies the letters, hence the words.  For closure, a term of `T^{⊗n}` boxed
by the power set has each letter a term of `T` (no factor of a nonzero product vanishes) boxed by
`S`, so closure for `S` puts every letter in `S`. -/
theorem independentSet_powerIndependentSet [∀ i, Fintype (κ i)] [NoZeroDivisors K] [Nontrivial K]
    {T : (∀ i, κ i) → K} {S : Finset (∀ i, κ i)} (h : IndependentSet T S) (n : ℕ) :
    IndependentSet (coordinatePower T n) (powerIndependentSet S n) where
  ne_zero p hp := by
    rw [coordinatePower_apply]
    exact Finset.prod_ne_zero_iff.mpr fun k _ ↦ h.ne_zero _ (mem_powerIndependentSet.mp hp k)
  distinct p hp q hq i hpq := by
    have hp' := mem_powerIndependentSet.mp hp
    have hq' := mem_powerIndependentSet.mp hq
    have hk : ∀ k : Fin n, (fun j ↦ p j k) = (fun j ↦ q j k) := fun k ↦
      h.distinct _ (hp' k) _ (hq' k) i (congrFun hpq k)
    funext j k
    exact congrFun (hk k) j
  closed p hp hbox := by
    refine mem_powerIndependentSet.mpr fun k ↦ ?_
    have hpk : T (fun i ↦ p i k) ≠ 0 := by
      rw [coordinatePower_apply] at hp
      exact Finset.prod_ne_zero_iff.mp hp k (Finset.mem_univ k)
    refine h.closed _ hpk fun i ↦ ?_
    obtain ⟨r, hr, hri⟩ := hbox i
    exact ⟨fun j ↦ r j k, mem_powerIndependentSet.mp hr k, congrFun hri k⟩

end PowerSet

end Power

/-! ## Kronecker powers and the abstract tensor

`coordinateTensor` turns the word-indexed Kronecker power into the canonical tensor power
`Tensor.power` of `Tensor/Power.lean`.  With that identification the finite barrier bounds
`I(T) ≤ Q(T) ≤ rank(T)` apply to every power at once, which is what
`Tensor/AsymptoticIndependenceNumber.lean` compares with `asymptoticSubrank` and
`asymptoticRank`. -/

section AbstractPower

variable {K : Type u} [CommSemiring K] {κ : Leg → Type v} {κ' : Leg → Type v}
variable {κ'' : Leg → Type w}
variable [∀ i, Fintype (κ i)] [∀ i, DecidableEq (κ i)]

omit [∀ i, DecidableEq (κ i)] in
/-- Relabelling the variables of the legs is a legwise isomorphism of the abstract tensors: it is
the permutation of the standard basis vectors induced by the index bijections. -/
theorem Isomorphic.coordinateTensor_coordinateRelabel
    [∀ i, Fintype (κ'' i)] [∀ i, DecidableEq (κ'' i)]
    (e : ∀ i, κ i ≃ κ'' i) (T : (∀ i, κ i) → K) :
    Isomorphic (coordinateTensor T) (coordinateTensor (coordinateRelabel e T)) := by
  refine ⟨relabelLegEquiv K e, ?_⟩
  refine standardCoordinate_ext (K := K) (κ := κ'') fun p ↦ ?_
  rw [standardCoordinateEquiv_congr_relabel, standardCoordinateEquiv_coordinateTensor,
    standardCoordinateEquiv_coordinateTensor]
  rfl

/-- **The Kronecker product of coefficient tables is the external product of the tensors they
define.**  The source is the external product `coordinateTensor T ⊠ coordinateTensor T'`, whose legs
are binary tensor products of coordinate spaces, and the target is the coordinate tensor of the
Kronecker product table, whose legs are coordinate spaces on pairs of variables.

Proof sketch: the leg identification is `coordinateTensorEquiv : (κ i → K) ⊗ (κ' i → K) ≃
(κ i × κ' i → K)` of `Tensor/Coordinates.lean`, which sends `e_a ⊗ e_b` to `e_{(a,b)}`.  Expanding
both tables into sums of scaled standard-basis pure tensors turns the external product into the
double sum over pairs of triples; its coefficient at a triple of pairs is supported on the single
pair obtained by splitting that triple, and equals the product of the two coefficients, which is
the definition of `coordinateProduct`. -/
theorem Isomorphic.coordinateTensor_coordinateProduct
    [∀ i, Fintype (κ' i)] [∀ i, DecidableEq (κ' i)]
    (T : (∀ i, κ i) → K) (T' : (∀ i, κ' i) → K) :
    Isomorphic (Tensor.external (coordinateTensor T) (coordinateTensor T'))
      (coordinateTensor (coordinateProduct T T')) := by
  classical
  have hexpand : Tensor.external (coordinateTensor T) (coordinateTensor T') =
      ∑ x : (∀ i, κ i) × (∀ i, κ' i), (T x.1 * T' x.2) • pure (K := K) (fun i ↦
        (Pi.single (x.1 i) (1 : K) : κ i → K) ⊗ₜ[K] (Pi.single (x.2 i) (1 : K) : κ' i → K)) := by
    rw [coordinateTensor_eq_sum, coordinateTensor_eq_sum, external_sum_sum, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun p _ ↦ Finset.sum_congr rfl fun p' _ ↦ ?_
    rw [external_smul_left, external_smul_right, external_pure, smul_smul]
  refine (Isomorphic.map _
    (fun i ↦ coordinateTensorEquiv (K := K) (α := κ i) (β := κ' i))).trans
      (Isomorphic.of_eq ?_)
  have key : Tensor.map
        (fun i ↦ (coordinateTensorEquiv (K := K) (α := κ i) (β := κ' i)).toLinearMap)
        (Tensor.external (coordinateTensor T) (coordinateTensor T')) =
      ∑ x : (∀ i, κ i) × (∀ i, κ' i), (T x.1 * T' x.2) •
        pure (K := K) (fun i ↦ (Pi.single (pairTriple x i) (1 : K) : (κ i × κ' i) → K)) := by
    rw [hexpand, map_sum]
    refine Finset.sum_congr rfl fun x _ ↦ ?_
    have hfun : ∀ i : Leg, (coordinateTensorEquiv (K := K) (α := κ i) (β := κ' i))
        ((Pi.single (x.1 i) (1 : K)) ⊗ₜ[K] (Pi.single (x.2 i) (1 : K))) =
          (Pi.single (pairTriple x i) (1 : K) : (κ i × κ' i) → K) :=
      fun i ↦ coordinateTensorEquiv_single_tmul_single (x.1 i) (x.2 i)
    rw [LinearMap.map_smul, Tensor.map_pure]
    simp only [LinearEquiv.coe_coe, hfun]
  rw [key]
  refine standardCoordinate_ext (K := K) (κ := fun i ↦ κ i × κ' i) fun q ↦ ?_
  rw [standardCoordinateEquiv_sum_single (K := K) (κ := fun i ↦ κ i × κ' i)
      (fun x : (∀ i, κ i) × (∀ i, κ' i) ↦ T x.1 * T' x.2) pairTriple q,
    standardCoordinateEquiv_coordinateTensor]
  have hfilter : (Finset.univ.filter fun x : (∀ i, κ i) × (∀ i, κ' i) ↦ pairTriple x = q) =
      {((fun i ↦ (q i).1), (fun i ↦ (q i).2))} := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · intro h
      refine Prod.ext (funext fun i ↦ ?_) (funext fun i ↦ ?_)
      · exact congrArg Prod.fst (congrFun h i)
      · exact congrArg Prod.snd (congrFun h i)
    · rintro rfl
      funext i
      rfl
  rw [hfilter, Finset.sum_singleton]
  rfl

omit [∀ i, DecidableEq (κ i)] in
/-- The zeroth Kronecker power is the zeroth tensor power: both are the pure tensor of a generator
of a one-dimensional space on every leg. -/
theorem Isomorphic.coordinateTensor_coordinatePower_zero (T : (∀ i, κ i) → K) :
    Isomorphic (coordinateTensor (coordinatePower T 0))
      (Tensor.power (coordinateTensor T) 0) := by
  have h0 : coordinatePower T 0 = fun _ : (∀ i, Fin 0 → κ i) ↦ (1 : K) := by
    funext p
    simp
  rw [h0, coordinateTensor_const_one]
  refine (Isomorphic.map _ (fun i ↦
    (LinearEquiv.funUnique (Fin 0 → κ i) K K).trans
      (PiTensorProduct.isEmptyEquiv (Fin 0)
        (s := fun _ : Fin 0 ↦ CoordinateSpace K κ i)).symm)).trans (Isomorphic.of_eq ?_)
  rw [Tensor.map_pure, power_zero]
  congr 1
  funext i
  have hunit : (PiTensorProduct.isEmptyEquiv (Fin 0)
      (s := fun _ : Fin 0 ↦ CoordinateSpace K κ i))
        (powerUnit (K := K) (V := CoordinateSpace K κ) i) = 1 := by
    simp [powerUnit]
  show (PiTensorProduct.isEmptyEquiv (Fin 0)
      (s := fun _ : Fin 0 ↦ CoordinateSpace K κ i)).symm (1 : K) = _
  rw [← hunit, LinearEquiv.symm_apply_apply]

/-- **The word-indexed Kronecker power is the canonical tensor power**:
`coordinateTensor (T^{⊗n}) ≅ (coordinateTensor T)^{⊗n}`.

Proof sketch: induction on `n`.  The base case is
`Isomorphic.coordinateTensor_coordinatePower_zero`.  For the step, appending a letter
(`coordinateRelabel_coordinateProduct_succ`) identifies `T^{⊗(n+1)}` with the Kronecker product
`T^{⊗n} ⊗ T`; the product bridge turns its coordinate tensor into the external product of the two
coordinate tensors; the induction hypothesis and `Isomorphic.powerOneTransport` replace the two
factors by `(coordinateTensor T)^{⊗n}` and its first power; and `Isomorphic.external_powerMul`
concatenates them into `(coordinateTensor T)^{⊗(n+1)}`. -/
theorem Isomorphic.coordinateTensor_coordinatePower (T : (∀ i, κ i) → K) (n : ℕ) :
    Isomorphic (coordinateTensor (coordinatePower T n))
      (Tensor.power (coordinateTensor T) n) := by
  induction n with
  | zero => exact Isomorphic.coordinateTensor_coordinatePower_zero T
  | succ n ih =>
      have h1 : Isomorphic (coordinateTensor (coordinatePower T (n + 1)))
          (coordinateTensor (coordinateProduct (coordinatePower T n) T)) := by
        rw [← coordinateRelabel_coordinateProduct_succ T n]
        exact (Isomorphic.coordinateTensor_coordinateRelabel _ _).symm
      have h2 : Isomorphic (coordinateTensor (coordinateProduct (coordinatePower T n) T))
          (Tensor.external (coordinateTensor (coordinatePower T n)) (coordinateTensor T)) :=
        (Isomorphic.coordinateTensor_coordinateProduct _ _).symm
      have h3 : Isomorphic
          (Tensor.external (coordinateTensor (coordinatePower T n)) (coordinateTensor T))
          (Tensor.external (Tensor.power (coordinateTensor T) n)
            (Tensor.powerOne (coordinateTensor T))) :=
        ih.external (Isomorphic.powerOneTransport _)
      exact ((h1.trans h2).trans h3).trans
        (Isomorphic.external_powerMul n 1 (Tensor.power (coordinateTensor T) n)
          (Tensor.powerOne (coordinateTensor T)))

end AbstractPower

section PowerBounds

variable {K : Type u} [Field K] {κ : Leg → Type v}
variable [∀ i, Fintype (κ i)] [∀ i, DecidableEq (κ i)]

/-- **The subrank barrier for every Kronecker power**:
`I(T^{⊗n}) ≤ Q((coordinateTensor T)^{⊗n})`.  This is `independenceNumber_le_subrank` transported
along `Isomorphic.coordinateTensor_coordinatePower`. -/
theorem independenceNumber_coordinatePower_le_subrank (T : (∀ i, κ i) → K) (n : ℕ) :
    independenceNumber (coordinatePower T n) ≤ subrank (Tensor.power (coordinateTensor T) n) := by
  have h := independenceNumber_le_subrank (coordinatePower T n)
  rwa [subrank_isomorphic (Isomorphic.coordinateTensor_coordinatePower T n)] at h

/-- **The rank barrier for every Kronecker power**:
`I(T^{⊗n}) ≤ rank((coordinateTensor T)^{⊗n})`.  Applied along the power sequence this is the
elementary bound `Ī(T) ≤ R̃(T)` of AVW Section 4. -/
theorem independenceNumber_coordinatePower_le_rank (T : (∀ i, κ i) → K) (n : ℕ) :
    independenceNumber (coordinatePower T n) ≤ rank (Tensor.power (coordinateTensor T) n) := by
  have h := independenceNumber_le_rank (coordinatePower T n)
  rwa [rank_isomorphic (Isomorphic.coordinateTensor_coordinatePower T n)] at h

end PowerBounds


/-! ## Kronecker powers of a Kronecker product

`coordinatePower` and `coordinateProduct` commute, after the letterwise relabelling that splits a
word of pairs into a pair of words.  With `coordinatePower_diagonalCoefficients` below this is what
turns `(F ⊙ A)^{⊗k}` into `F^k ⊙ A^{⊗k}` for the block tables of the next section. -/

section PowerProduct

variable {K : Type u} [CommSemiring K] {κ κ' : Leg → Type v}

/-- Splitting a word of pairs into a pair of words, as a bijection of index types. -/
def splitIndexEquiv (α β : Type v) (k : ℕ) : (Fin k → α × β) ≃ (Fin k → α) × (Fin k → β) :=
  Equiv.arrowProdEquivProdArrow (Fin k) (fun _ ↦ α) (fun _ ↦ β)

/-- **Kronecker powers distribute over Kronecker products**: relabelling the variables of
`A^{⊗k} ⊗ B^{⊗k}` by pairing letters position by position gives `(A ⊗ B)^{⊗k}`.

Proof sketch: the coefficient of a triple of words of pairs is the product over the `k` positions
of a product of two coefficients, which `Finset.prod_mul_distrib` splits into the two `k`-fold
products read off the two components. -/
theorem coordinateRelabel_coordinatePower_coordinateProduct (A : (∀ i, κ i) → K)
    (B : (∀ i, κ' i) → K) (k : ℕ) :
    coordinateRelabel (fun i ↦ (splitIndexEquiv (κ i) (κ' i) k).symm)
        (coordinateProduct (coordinatePower A k) (coordinatePower B k)) =
      coordinatePower (coordinateProduct A B) k := by
  funext p
  show (∏ t : Fin k, A fun i ↦ (p i t).1) * (∏ t : Fin k, B fun i ↦ (p i t).2) = _
  rw [coordinatePower_apply, ← Finset.prod_mul_distrib]
  rfl

/-- The independence number of a Kronecker power of a Kronecker product is the independence number
of the Kronecker product of the two powers. -/
theorem independenceNumber_coordinatePower_coordinateProduct
    [∀ i, Fintype (κ i)] [∀ i, DecidableEq (κ i)]
    [∀ i, Fintype (κ' i)] [∀ i, DecidableEq (κ' i)]
    (A : (∀ i, κ i) → K) (B : (∀ i, κ' i) → K) (k : ℕ) :
    independenceNumber (coordinatePower (coordinateProduct A B) k) =
      independenceNumber (coordinateProduct (coordinatePower A k) (coordinatePower B k)) := by
  rw [← coordinateRelabel_coordinatePower_coordinateProduct A B k,
    independenceNumber_coordinateRelabel]

end PowerProduct

section DiagonalPower

variable {K : Type u} [CommSemiring K] {ι : Type v} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] in
/-- **Kronecker powers of the independent tensor**: `⟨r⟩^{⊗k}` is the independent tensor on words,
`⟨r^k⟩`.  Both sides are the indicator of the constant triples, read letter by letter on the left
and as words on the right. -/
theorem coordinatePower_diagonalCoefficients (k : ℕ) :
    coordinatePower (diagonalCoefficients K ι) k = diagonalCoefficients K (Fin k → ι) := by
  funext p
  rw [coordinatePower_apply]
  by_cases h : ∀ i, p i = p .X
  · rw [diagonalCoefficients, if_pos h]
    refine Finset.prod_eq_one fun t _ ↦ ?_
    rw [diagonalCoefficients, if_pos]
    exact fun i ↦ congrFun (h i) t
  · rw [diagonalCoefficients, if_neg h]
    obtain ⟨i, hi⟩ := not_forall.mp h
    obtain ⟨t, ht⟩ := Function.ne_iff.mp hi
    refine Finset.prod_eq_zero (Finset.mem_univ t) ?_
    rw [diagonalCoefficients, if_neg]
    intro hall
    exact ht (hall i)

end DiagonalPower

/-! ## Block tables

A *block table* is the coordinate counterpart of `Tensor.indexedDirectSum`: the variables of leg
`i` are pairs `(j, x)` of a block index and a variable of the `j`-th constituent, and a triple has
a nonzero coefficient only when its three block indices agree.  This is the coefficient-level form
of a disjoint sum of tensors --- Alman--Vassilevska Williams's `F ⊙ T` (arXiv:1810.08671,
Lemma 4.4) is `coordinateDirectSum (fun _ : Fin F ↦ T)` --- and the invariant `I` sees it exactly:
`independenceNumber_coordinateDirectSum` computes `I(⊕ⱼ Aⱼ) = ∑ⱼ I(Aⱼ)`.

The constant family is the Kronecker product with the independent tensor
(`coordinateDirectSum_const`), which is how the power law of the next module reaches block
tables. -/

section BlockSum

variable {K : Type u} [CommSemiring K] {κ : Leg → Type v} {ι : Type v} [DecidableEq ι]

/-- The index triple of a block table sitting in block `j` above the triple `q`. -/
def blockTriple (j : ι) (q : ∀ i, κ i) : ∀ i, ι × κ i := fun i ↦ (j, q i)

omit [DecidableEq ι] in
/-- Different triples of one block are different triples of the block table. -/
theorem blockTriple_injective (j : ι) : Function.Injective (blockTriple (κ := κ) j) := by
  intro q r h
  funext i
  exact congrArg Prod.snd (congrFun h i)

/-- The **block table** of a finite family of coefficient tables: the coordinate counterpart of
`Tensor.indexedDirectSum`.  A triple whose three block indices agree gets the coefficient of the
corresponding triple of that block, and a triple mixing two blocks gets `0`. -/
def coordinateDirectSum (A : ι → (∀ i, κ i) → K) : (∀ i, ι × κ i) → K :=
  fun p ↦ if ∀ i, (p i).1 = (p .X).1 then A (p .X).1 (fun i ↦ (p i).2) else 0

/-- Inside one block the block table is the constituent table. -/
@[simp] theorem coordinateDirectSum_blockTriple (A : ι → (∀ i, κ i) → K) (j : ι)
    (q : ∀ i, κ i) : coordinateDirectSum A (blockTriple j q) = A j q := by
  rw [coordinateDirectSum, if_pos]
  · rfl
  · intro i; rfl

/-- Every term of a block table lies in a single block. -/
theorem coordinateDirectSum_ne_zero {A : ι → (∀ i, κ i) → K} {p : ∀ i, ι × κ i}
    (h : coordinateDirectSum A p ≠ 0) :
    ∃ j q, p = blockTriple j q ∧ A j q ≠ 0 := by
  by_cases hb : ∀ i, (p i).1 = (p .X).1
  · refine ⟨(p .X).1, fun i ↦ (p i).2, ?_, ?_⟩
    · funext i
      exact Prod.ext (hb i) rfl
    · rwa [coordinateDirectSum, if_pos hb] at h
  · rw [coordinateDirectSum, if_neg hb] at h
    exact absurd rfl h

/-- **`F` disjoint copies of one table are its Kronecker product with the independent tensor
`⟨F⟩`**: both tables are supported on the triples whose three block indices agree, with the
coefficient read off the constituent.  This is the identity that gives block tables the whole
product calculus, in particular supermultiplicativity and the power law. -/
theorem coordinateDirectSum_const [Fintype ι] (A : (∀ i, κ i) → K) :
    coordinateDirectSum (fun _ : ι ↦ A) = coordinateProduct (diagonalCoefficients K ι) A := by
  funext p
  by_cases h : ∀ i, (p i).1 = (p .X).1
  · show (if _ then _ else _) = (if _ then _ else _) * _
    rw [if_pos h, if_pos h, one_mul]
  · show (if _ then _ else _) = (if _ then _ else _) * _
    rw [if_neg h, if_neg h, zero_mul]

end BlockSum

section BlockIndependence

variable {K : Type u} [CommSemiring K] {κ : Leg → Type v} {ι : Type v} [DecidableEq ι]
variable [Fintype ι] [∀ i, Fintype (κ i)] [∀ i, DecidableEq (κ i)]
variable [DecidableEq (∀ i, ι × κ i)] [DecidableEq (∀ i, κ i)]

omit [DecidableEq ι] [∀ i, Fintype (κ i)] [∀ i, DecidableEq (κ i)] [DecidableEq (∀ i, κ i)] in
/-- Membership in the union of the blockwise images of a family of sets of terms. -/
theorem mem_blockUnion {S : ι → Finset (∀ i, κ i)} {p : ∀ i, ι × κ i} :
    p ∈ (Finset.univ.biUnion fun j ↦ (S j).image (blockTriple j)) ↔
      ∃ j, ∃ q ∈ S j, p = blockTriple j q := by
  simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_image]
  constructor
  · rintro ⟨j, q, hq, rfl⟩
    exact ⟨j, q, hq, rfl⟩
  · rintro ⟨j, q, hq, rfl⟩
    exact ⟨j, q, hq, rfl⟩

omit [∀ i, Fintype (κ i)] [∀ i, DecidableEq (κ i)] [DecidableEq (∀ i, κ i)] in
/-- **Independent sets of the blocks assemble into an independent set of the block table.**

Proof sketch: the three clauses are blockwise.  Two chosen triples that share a variable share its
block index, so they lie in the same block and the constituent's injectivity applies; and a term of
the block table lies in one block (`coordinateDirectSum_ne_zero`), where a boxing triple must also
live, so the constituent's closure applies. -/
theorem IndependentSet.coordinateDirectSum {A : ι → (∀ i, κ i) → K} {S : ι → Finset (∀ i, κ i)}
    (h : ∀ j, IndependentSet (A j) (S j)) :
    IndependentSet (Tensor.coordinateDirectSum A)
      (Finset.univ.biUnion fun j ↦ (S j).image (blockTriple j)) where
  ne_zero p hp := by
    obtain ⟨j, q, hq, rfl⟩ := mem_blockUnion.mp hp
    rw [coordinateDirectSum_blockTriple]
    exact (h j).ne_zero q hq
  distinct p hp r hr i hpr := by
    obtain ⟨j, q, hq, rfl⟩ := mem_blockUnion.mp hp
    obtain ⟨j', q', hq', rfl⟩ := mem_blockUnion.mp hr
    have hj : j = j' := congrArg Prod.fst hpr
    subst hj
    have : q i = q' i := congrArg Prod.snd hpr
    rw [(h j).distinct q hq q' hq' i this]
  closed p hp hbox := by
    obtain ⟨j, q, rfl, hq⟩ := Tensor.coordinateDirectSum_ne_zero hp
    refine mem_blockUnion.mpr ⟨j, q, (h j).closed q hq fun i ↦ ?_, rfl⟩
    obtain ⟨r, hr, hri⟩ := hbox i
    obtain ⟨j', q', hq', rfl⟩ := mem_blockUnion.mp hr
    have hj : j' = j := congrArg Prod.fst hri
    subst hj
    exact ⟨q', hq', congrArg Prod.snd hri⟩

omit [∀ i, Fintype (κ i)] [∀ i, DecidableEq (κ i)] [DecidableEq (∀ i, κ i)] in
omit [DecidableEq ι] in
/-- The assembled set of terms has the sum of the constituent cardinalities: different blocks are
disjoint, and each blockwise image is injective. -/
theorem card_blockUnion (S : ι → Finset (∀ i, κ i)) :
    (Finset.univ.biUnion fun j ↦ (S j).image (blockTriple (κ := κ) j)).card =
      ∑ j, (S j).card := by
  rw [Finset.card_biUnion]
  · exact Finset.sum_congr rfl fun j _ ↦
      Finset.card_image_of_injective _ (blockTriple_injective j)
  · intro j _ j' _ hjj'
    refine Finset.disjoint_left.mpr fun p hp hp' ↦ ?_
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨q', -, hq'⟩ := Finset.mem_image.mp hp'
    exact hjj' (congrArg Prod.fst (congrFun hq' .X)).symm

omit [DecidableEq (∀ i, κ i)] in
/-- **The independence number of a block table is at least the sum of the blockwise independence
numbers.**  This is the direction AVW's Lemma 4.4 uses: a lower bound for each of `F` disjoint
copies of `⟨a,b,c⟩` adds up. -/
theorem independenceNumber_coordinateDirectSum_ge (A : ι → (∀ i, κ i) → K) :
    ∑ j, independenceNumber (A j) ≤ independenceNumber (Tensor.coordinateDirectSum A) := by
  classical
  choose S hS hcard using fun j ↦ exists_independentSet_card_eq (A j)
  have hle := (IndependentSet.coordinateDirectSum hS).card_le_independenceNumber
  rw [card_blockUnion] at hle
  calc ∑ j, independenceNumber (A j) = ∑ j, (S j).card :=
        Finset.sum_congr rfl fun j _ ↦ (hcard j).symm
    _ ≤ _ := hle

/-- The block-`j` part of a set of terms of a block table. -/
def blockPart (S : Finset (∀ i, ι × κ i)) (j : ι) : Finset (∀ i, κ i) :=
  (S.filter fun p ↦ (p .X).1 = j).image fun p i ↦ (p i).2

omit [Fintype ι] [∀ i, Fintype (κ i)] [∀ i, DecidableEq (κ i)] [DecidableEq (∀ i, ι × κ i)] in
/-- **Independent sets of a block table restrict to independent sets of every block.**

Proof sketch: every term of the block table lies in a single block, so the chosen triples split by
block index; the three clauses of `IndependentSet` for the block-`j` part are the clauses for the
block table read on the triples of block `j`. -/
theorem blockPart_independentSet {A : ι → (∀ i, κ i) → K} {S : Finset (∀ i, ι × κ i)}
    (h : IndependentSet (Tensor.coordinateDirectSum A) S) (j : ι) :
    IndependentSet (A j) (blockPart S j) := by
  have hblock : ∀ p ∈ S, p = blockTriple (p .X).1 (fun i ↦ (p i).2) := by
    intro p hp
    obtain ⟨j', q, hpq, -⟩ := Tensor.coordinateDirectSum_ne_zero (h.ne_zero p hp)
    subst hpq
    rfl
  have hmem : ∀ {q : ∀ i, κ i}, q ∈ blockPart S j ↔ blockTriple j q ∈ S := by
    intro q
    constructor
    · intro hq
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hq
      obtain ⟨hpS, hpj⟩ := Finset.mem_filter.mp hp
      have hp' := hblock p hpS
      rw [hpj] at hp'
      rwa [← hp']
    · intro hq
      exact Finset.mem_image.mpr ⟨blockTriple j q, Finset.mem_filter.mpr ⟨hq, rfl⟩, rfl⟩
  refine ⟨fun q hq ↦ ?_, fun q hq r hr i hqr ↦ ?_, fun q hq hbox ↦ ?_⟩
  · have hne := h.ne_zero _ (hmem.mp hq)
    rwa [coordinateDirectSum_blockTriple] at hne
  · have heq := h.distinct _ (hmem.mp hq) _ (hmem.mp hr) i (by
      show (j, q i) = (j, r i)
      rw [hqr])
    exact blockTriple_injective j heq
  · refine hmem.mpr (h.closed _ ?_ fun i ↦ ?_)
    · rwa [coordinateDirectSum_blockTriple]
    · obtain ⟨r, hr, hri⟩ := hbox i
      refine ⟨blockTriple j r, hmem.mp hr, ?_⟩
      show (j, r i) = (j, q i)
      rw [hri]

/-- **The independence number of a block table is exactly the sum of the blockwise independence
numbers**, `I(⊕ⱼ Aⱼ) = ∑ⱼ I(Aⱼ)`.

Proof sketch: `independenceNumber_coordinateDirectSum_ge` is one direction.  For the other, an
independent set of the block table has all its triples inside single blocks, so its cardinality is
the sum of the cardinalities of its blockwise parts (`Finset.card_eq_sum_card_fiberwise`), each of
which is an independent set of its block (`blockPart_independentSet`). -/
theorem independenceNumber_coordinateDirectSum (A : ι → (∀ i, κ i) → K) :
    independenceNumber (Tensor.coordinateDirectSum A) = ∑ j, independenceNumber (A j) := by
  classical
  refine le_antisymm (independenceNumber_le fun S hS ↦ ?_)
    (independenceNumber_coordinateDirectSum_ge A)
  have hcard : S.card = ∑ j, (S.filter fun p ↦ (p .X).1 = j).card :=
    Finset.card_eq_sum_card_fiberwise fun p _ ↦ Finset.mem_univ _
  have hinj : ∀ j, (S.filter fun p ↦ (p .X).1 = j).card = (blockPart S j).card := by
    intro j
    refine (Finset.card_image_of_injOn ?_).symm
    intro p hp r hr hpr
    obtain ⟨hpS, hpj⟩ := Finset.mem_filter.mp hp
    obtain ⟨hrS, hrj⟩ := Finset.mem_filter.mp hr
    obtain ⟨j₁, q₁, e₁, -⟩ := Tensor.coordinateDirectSum_ne_zero (hS.ne_zero p hpS)
    obtain ⟨j₂, q₂, e₂, -⟩ := Tensor.coordinateDirectSum_ne_zero (hS.ne_zero r hrS)
    subst e₁
    subst e₂
    have e1 : j₁ = j := hpj
    have e2 : j₂ = j := hrj
    have hq : q₁ = q₂ := hpr
    rw [e1, e2, hq]
  rw [hcard]
  refine Finset.sum_le_sum fun j _ ↦ ?_
  rw [hinj j]
  exact (blockPart_independentSet hS j).card_le_independenceNumber

/-- **`F` disjoint copies multiply the independence number**, `I(F ⊙ A) = F · I(A)`: the special
case of `independenceNumber_coordinateDirectSum` for a constant family. -/
theorem independenceNumber_coordinateDirectSum_const (A : (∀ i, κ i) → K) :
    independenceNumber (Tensor.coordinateDirectSum (fun _ : ι ↦ A)) =
      Fintype.card ι * independenceNumber A := by
  rw [independenceNumber_coordinateDirectSum, Finset.sum_const, smul_eq_mul, Finset.card_univ]

omit [DecidableEq (∀ i, ι × κ i)] [DecidableEq (∀ i, κ i)] in
/-- **Kronecker powers of `F` disjoint copies.**  The `k`th Kronecker power of `F ⊙ A` is
`F^k ⊙ A^{⊗k}`, so its independence number is `F^k · I(A^{⊗k})`.

Proof sketch: `coordinateDirectSum_const` presents `F ⊙ A` as `⟨F⟩ ⊗ A`;
`coordinateRelabel_coordinatePower_coordinateProduct` distributes the power over the product;
`coordinatePower_diagonalCoefficients` turns `⟨F⟩^{⊗k}` into `⟨F^k⟩`; and
`independenceNumber_coordinateDirectSum` counts the resulting `F^k` blocks. -/
theorem independenceNumber_coordinatePower_coordinateDirectSum_const (A : (∀ i, κ i) → K)
    (k : ℕ) :
    independenceNumber (coordinatePower (Tensor.coordinateDirectSum (fun _ : ι ↦ A)) k) =
      Fintype.card ι ^ k * independenceNumber (coordinatePower A k) := by
  classical
  rw [coordinateDirectSum_const, independenceNumber_coordinatePower_coordinateProduct,
    coordinatePower_diagonalCoefficients, ← coordinateDirectSum_const,
    independenceNumber_coordinateDirectSum]
  rw [Finset.sum_const, smul_eq_mul, Finset.card_univ, Fintype.card_fun, Fintype.card_fin]

end BlockIndependence

/-! ## Unused variables

A monomial degeneration leaves the variables of its source in place, so the table it produces is
the table of its *image* extended by zero to the ambient variables.  `coordinateExtend` is that
zero-extension along a legwise injection --- presented, to stay choice-free, by a map together
with a retraction --- and `independenceNumber_coordinateExtend` says that `I` does not see the
unused variables. -/

section Extend

variable {K : Type u} [CommSemiring K] {α : Leg → Type v} {β : Leg → Type w}
variable [∀ i, DecidableEq (β i)]

/-- The **zero-extension** of a coefficient table along a legwise injection of variable sets: the
value at a triple all of whose variables come from the smaller sets is the value of the original
table there, and every other triple gets `0`.  The injections are presented as maps `f` with
retractions `g`, so that no choice is needed to invert them. -/
def coordinateExtend (f : ∀ i, α i → β i) (g : ∀ i, β i → α i) (A : (∀ i, α i) → K) :
    (∀ i, β i) → K :=
  fun p ↦ if ∀ i, f i (g i (p i)) = p i then A (fun i ↦ g i (p i)) else 0

variable {f : ∀ i, α i → β i} {g : ∀ i, β i → α i} {A : (∀ i, α i) → K}

/-- The extension agrees with the original table on the embedded variables. -/
theorem coordinateExtend_embed (hgf : ∀ i x, g i (f i x) = x) (q : ∀ i, α i) :
    coordinateExtend f g A (fun i ↦ f i (q i)) = A q := by
  have h : ∀ i, f i (g i (f i (q i))) = f i (q i) := fun i ↦ by rw [hgf]
  rw [coordinateExtend, if_pos h]
  simp only [hgf]

/-- Every term of the extension is the image of a term of the original table. -/
theorem coordinateExtend_ne_zero {p : ∀ i, β i} (h : coordinateExtend f g A p ≠ 0) :
    (∀ i, f i (g i (p i)) = p i) ∧ A (fun i ↦ g i (p i)) ≠ 0 := by
  by_cases hc : ∀ i, f i (g i (p i)) = p i
  · rw [coordinateExtend, if_pos hc] at h
    exact ⟨hc, h⟩
  · rw [coordinateExtend, if_neg hc] at h
    exact absurd rfl h

omit [∀ i, DecidableEq (β i)] in
/-- A map with a retraction is injective. -/
theorem injective_of_retraction (hgf : ∀ i x, g i (f i x) = x) (i : Leg) :
    Function.Injective (f i) := by
  intro x y hxy
  rw [← hgf i x, hxy, hgf]

variable [∀ i, DecidableEq (α i)]

omit [∀ i, DecidableEq (α i)] in
/-- **Independent sets are carried to the zero-extension.** -/
theorem IndependentSet.coordinateExtend (hgf : ∀ i x, g i (f i x) = x)
    {S : Finset (∀ i, α i)} (h : IndependentSet A S) :
    IndependentSet (Tensor.coordinateExtend f g A) (S.image fun q i ↦ f i (q i)) where
  ne_zero p hp := by
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
    rw [coordinateExtend_embed hgf]
    exact h.ne_zero q hq
  distinct p hp r hr i hpr := by
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨q', hq', rfl⟩ := Finset.mem_image.mp hr
    have hi : q i = q' i := injective_of_retraction hgf i hpr
    rw [h.distinct q hq q' hq' i hi]
  closed p hp hbox := by
    obtain ⟨hrange, hne⟩ := coordinateExtend_ne_zero hp
    have hq : (fun i ↦ g i (p i)) ∈ S := by
      refine h.closed _ hne fun i ↦ ?_
      obtain ⟨r, hr, hri⟩ := hbox i
      obtain ⟨q', hq', rfl⟩ := Finset.mem_image.mp hr
      have hri' : f i (q' i) = p i := hri
      refine ⟨q', hq', injective_of_retraction hgf i ?_⟩
      rw [hri', hrange i]
    refine Finset.mem_image.mpr ⟨_, hq, ?_⟩
    funext i
    exact hrange i

/-- **Independent sets of the zero-extension come from the original table.** -/
theorem IndependentSet.of_coordinateExtend (hgf : ∀ i x, g i (f i x) = x)
    {S : Finset (∀ i, β i)} (h : IndependentSet (Tensor.coordinateExtend f g A) S) :
    IndependentSet A (S.image fun p i ↦ g i (p i)) := by
  have hfix : ∀ p ∈ S, ∀ i, f i (g i (p i)) = p i := fun p hp ↦
    (coordinateExtend_ne_zero (h.ne_zero p hp)).1
  refine ⟨fun q hq ↦ ?_, fun q hq r hr i hqr ↦ ?_, fun q hq hbox ↦ ?_⟩
  · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hq
    exact (coordinateExtend_ne_zero (h.ne_zero p hp)).2
  · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hq
    obtain ⟨p', hp', rfl⟩ := Finset.mem_image.mp hr
    have hqr' : g i (p i) = g i (p' i) := hqr
    have hpi : p i = p' i := by
      rw [← hfix p hp i, ← hfix p' hp' i, hqr']
    rw [h.distinct p hp p' hp' i hpi]
  · refine Finset.mem_image.mpr ⟨fun i ↦ f i (q i), h.closed _ ?_ fun i ↦ ?_, ?_⟩
    · rw [coordinateExtend_embed hgf]
      exact hq
    · obtain ⟨r, hr, hri⟩ := hbox i
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hr
      have hri' : g i (p i) = q i := hri
      exact ⟨p, hp, by rw [← hri', hfix p hp i]⟩
    · funext i
      exact hgf i (q i)

variable [∀ i, Fintype (α i)] [∀ i, Fintype (β i)]

/-- **The independence number does not see unused variables**: zero-extending a table along a
legwise injection leaves `I` unchanged. -/
theorem independenceNumber_coordinateExtend (hgf : ∀ i x, g i (f i x) = x) :
    independenceNumber (coordinateExtend f g A) = independenceNumber A := by
  classical
  refine le_antisymm (independenceNumber_le fun S hS ↦ ?_) (independenceNumber_le fun S hS ↦ ?_)
  · have hcard : (S.image fun p i ↦ g i (p i)).card = S.card := by
      refine Finset.card_image_of_injOn fun p hp r hr hpr ↦ ?_
      have hfp := (coordinateExtend_ne_zero (hS.ne_zero p hp)).1
      have hfr := (coordinateExtend_ne_zero (hS.ne_zero r hr)).1
      funext i
      rw [← hfp i, ← hfr i]
      exact congrArg (f i) (congrFun hpr i)
    have hle := (hS.of_coordinateExtend hgf).card_le_independenceNumber
    rwa [hcard] at hle
  · have hcard : (S.image fun q i ↦ f i (q i)).card = S.card := by
      refine Finset.card_image_of_injOn fun q _ r _ hqr ↦ ?_
      funext i
      exact injective_of_retraction hgf i (congrFun hqr i)
    have hle := (hS.coordinateExtend hgf).card_le_independenceNumber
    rwa [hcard] at hle

omit [∀ i, DecidableEq (α i)] [∀ i, Fintype (α i)] [∀ i, Fintype (β i)] in
/-- Pulling a zero-extension back along the injection recovers the original table.  With
`Restricts.coordinateTensor_pullback` this exhibits the original table as an exact restriction of
its zero-extension. -/
theorem coordinateExtend_pullback (hgf : ∀ i x, g i (f i x) = x) :
    (fun q ↦ coordinateExtend f g A fun i ↦ f i (q i)) = A :=
  funext fun q ↦ coordinateExtend_embed hgf q

omit [∀ i, DecidableEq (α i)] [∀ i, Fintype (α i)] [∀ i, Fintype (β i)] in
/-- **Zero-extension commutes with Kronecker powers**: the `k`th power of an extension is the
extension of the `k`th power along the letterwise injection of words. -/
theorem coordinatePower_coordinateExtend (f : ∀ i, α i → β i) (g : ∀ i, β i → α i)
    (A : (∀ i, α i) → K) (k : ℕ) :
    coordinatePower (coordinateExtend f g A) k =
      coordinateExtend (fun i q t ↦ f i (q t)) (fun i p t ↦ g i (p t))
        (coordinatePower A k) := by
  funext p
  by_cases hall : ∀ i, ∀ t : Fin k, f i (g i (p i t)) = p i t
  · rw [coordinateExtend, if_pos fun i ↦ funext (hall i), coordinatePower_apply,
      coordinatePower_apply]
    refine Finset.prod_congr rfl fun t _ ↦ ?_
    rw [coordinateExtend, if_pos fun i ↦ hall i t]
  · rw [coordinateExtend, if_neg, coordinatePower_apply]
    · obtain ⟨i, hi⟩ := not_forall.mp hall
      obtain ⟨t, ht⟩ := not_forall.mp hi
      refine Finset.prod_eq_zero (Finset.mem_univ t) ?_
      rw [coordinateExtend, if_neg]
      intro hc
      exact ht (hc i)
    · intro hc
      exact hall fun i ↦ congrFun (hc i)

end Extend


/-! ## Coordinate tables and the abstract layer, continued

Two bridges used by the barrier program.  `Restricts.coordinateTensor_pullback` says that renaming
the variables of the legs along *arbitrary* maps — not only bijections — is an exact restriction of
the abstract tensors; with `coordinateExtend_pullback` it converts a zero-extension back into its
original table.  `coordinateTensor_coordinateDirectSum_eq_sum` writes the abstract tensor of a
block table as the sum of its blocks embedded on every leg, which is the shape of
`Tensor.indexedDirectSum` and is what a client with the direct-sum API in scope turns into a
comparison with `Tensor.indexedDirectSum` itself.
-/


section Pullback

variable {K : Type u} [CommSemiring K] {α : Leg → Type v} {β : Leg → Type w}
variable [∀ i, Fintype (α i)] [∀ i, DecidableEq (α i)]
variable [∀ i, Fintype (β i)] [∀ i, DecidableEq (β i)]

omit [∀ i, DecidableEq (α i)] [∀ i, DecidableEq (β i)] in
/-- **Renaming variables along arbitrary legwise maps is an exact restriction.** -/
theorem Restricts.coordinateTensor_pullback (f : ∀ i, α i → β i) (E : (∀ i, β i) → K) :
    Restricts (coordinateTensor E) (coordinateTensor fun q ↦ E fun i ↦ f i (q i)) := by
  refine ⟨fun i ↦ LinearMap.funLeft K K (f i), ?_⟩
  refine standardCoordinate_ext (K := K) (κ := α) fun q ↦ ?_
  rw [standardCoordinateEquiv_map_funLeft, standardCoordinateEquiv_coordinateTensor,
    standardCoordinateEquiv_coordinateTensor]

end Pullback

section BlockInclude

variable {K : Type u} [CommSemiring K] {κ : Leg → Type v} {ι : Type v} [DecidableEq ι]

/-- The inclusion of the `j`-th block on one leg. -/
def coordinateBlockInclude (j : ι) (c : Leg) : (κ c → K) →ₗ[K] ((ι × κ c) → K) where
  toFun v := fun q ↦ if q.1 = j then v q.2 else 0
  map_add' u v := by
    funext q
    by_cases h : q.1 = j <;> simp [h]
  map_smul' a v := by
    funext q
    by_cases h : q.1 = j <;> simp [h]

@[simp] theorem blockInclude_apply (j : ι) (c : Leg) (v : κ c → K) (q : ι × κ c) :
    coordinateBlockInclude (K := K) j c v q = if q.1 = j then v q.2 else 0 := rfl

variable [∀ i, DecidableEq (κ i)]

/-- The block inclusion sends the standard basis vector of `x` to that of `(j, x)`. -/
theorem blockInclude_single (j : ι) (c : Leg) (x : κ c) :
    coordinateBlockInclude (K := K) j c (Pi.single x 1) = Pi.single (j, x) 1 := by
  funext q
  rw [blockInclude_apply, Pi.single_apply, Pi.single_apply]
  by_cases h : q = (j, x)
  · rw [if_pos h, if_pos (show q.1 = j by rw [h]), if_pos (show q.2 = x by rw [h])]
  · rw [if_neg h]
    by_cases h1 : q.1 = j
    · rw [if_pos h1, if_neg]
      intro h2
      exact h (Prod.ext h1 h2)
    · rw [if_neg h1]

variable [Fintype ι] [∀ i, Fintype (κ i)]

/-- **The abstract tensor of a block table is the sum of its embedded blocks.** -/
theorem coordinateTensor_coordinateDirectSum_eq_sum (A : ι → (∀ i, κ i) → K) :
    coordinateTensor (coordinateDirectSum A) =
      ∑ j, Tensor.map (coordinateBlockInclude (K := K) (κ := κ) j) (coordinateTensor (A j)) := by
  classical
  have hblock : ∀ j : ι, Tensor.map (coordinateBlockInclude (K := K) (κ := κ) j) (coordinateTensor (A j)) =
      ∑ q : (∀ i, κ i), A j q •
        pure (K := K) (fun c ↦ (Pi.single (blockTriple j q c) (1 : K) : (ι × κ c) → K)) := by
    intro j
    rw [coordinateTensor_eq_sum, map_sum]
    refine Finset.sum_congr rfl fun q _ ↦ ?_
    rw [LinearMap.map_smul, Tensor.map_pure]
    have hfun : (fun c ↦ coordinateBlockInclude (K := K) (κ := κ) j c (Pi.single (q c) (1 : K))) =
        (fun c ↦ (Pi.single (blockTriple j q c) (1 : K) : (ι × κ c) → K)) := by
      funext c
      exact blockInclude_single j c (q c)
    rw [hfun]
  refine standardCoordinate_ext (K := K) (κ := fun c ↦ ι × κ c) fun p ↦ ?_
  rw [standardCoordinateEquiv_coordinateTensor, map_sum, Finset.sum_apply]
  have hterm : ∀ j : ι,
      standardCoordinateEquiv (K := K) (κ := fun c ↦ ι × κ c)
          (Tensor.map (coordinateBlockInclude (K := K) (κ := κ) j) (coordinateTensor (A j))) p =
        ∑ q ∈ Finset.univ.filter fun q : (∀ i, κ i) ↦ blockTriple j q = p, A j q := by
    intro j
    rw [hblock j]
    exact standardCoordinateEquiv_sum_single (K := K) (κ := fun c ↦ ι × κ c) (A j)
      (fun q ↦ blockTriple j q) p
  rw [Finset.sum_congr rfl fun j _ ↦ hterm j]
  by_cases hp : ∀ i, (p i).1 = (p .X).1
  · obtain ⟨j₀, q₀, rfl⟩ : ∃ j₀ q₀, p = blockTriple j₀ q₀ :=
      ⟨(p .X).1, fun i ↦ (p i).2, funext fun i ↦ Prod.ext (hp i) rfl⟩
    have hsum : ∀ j : ι,
        (∑ q ∈ Finset.univ.filter fun q : (∀ i, κ i) ↦
            blockTriple j q = blockTriple j₀ q₀, A j q) =
          if j = j₀ then A j₀ q₀ else 0 := by
      intro j
      by_cases hj : j = j₀
      · subst hj
        have hfil : (Finset.univ.filter fun q : (∀ i, κ i) ↦
            blockTriple j q = blockTriple j q₀) = {q₀} := by
          ext q
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
          exact ⟨fun h ↦ blockTriple_injective j h, fun h ↦ by rw [h]⟩
        rw [hfil, Finset.sum_singleton, if_pos rfl]
      · have hfil : (Finset.univ.filter fun q : (∀ i, κ i) ↦
            blockTriple j q = blockTriple j₀ q₀) = ∅ := by
          ext q
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty,
            iff_false]
          intro h
          exact hj (congrArg Prod.fst (congrFun h .X))
        rw [hfil, Finset.sum_empty, if_neg hj]
    rw [Finset.sum_congr rfl fun j _ ↦ hsum j,
      Finset.sum_ite_eq' Finset.univ j₀ (fun _ ↦ A j₀ q₀), if_pos (Finset.mem_univ j₀),
      coordinateDirectSum_blockTriple]
  · have hzero : ∀ j : ι,
        (∑ q ∈ Finset.univ.filter fun q : (∀ i, κ i) ↦ blockTriple j q = p, A j q) = 0 := by
      intro j
      refine Finset.sum_eq_zero fun q hq ↦ ?_
      exfalso
      obtain ⟨-, h⟩ := Finset.mem_filter.mp hq
      refine hp fun i ↦ ?_
      rw [← h]
      rfl
    rw [Finset.sum_congr rfl fun j _ ↦ hzero j, Finset.sum_const_zero,
      coordinateDirectSum, if_neg hp]

end BlockInclude


/-! ## The basis-dependence witness

`independenceNumber` is a function of a *coefficient table*, not of the abstract tensor it defines.
This section makes that concrete over `ℚ`, exactly as in `BARRIER_FRAMEWORK.md` §1: the table of
`⟨2⟩` and the table obtained from it by the change of basis `[[1, 1], [1, -1]]` on every leg define
legwise isomorphic tensors, yet have independence numbers `2` and `1`.

Consequently no lemma of the form `Isomorphic T S → independenceNumber ... = ...` can exist, the
comparisons `I(T) ≤ Q(T) ≤ sliceRank(T) ≤ rank(T)` proved above are necessarily one-way, and the
asymptotic independence number of `Tensor/AsymptoticIndependenceNumber.lean` cannot be built with
the `Tensor3` invariant wrapper of `Tensor/AsymptoticInvariant.lean`. -/

namespace HadamardWitness

/-- The sign of a `Fin 2` index: `+1` at `0` and `-1` at `1`.  These are the entries of the second
column of the change of basis `[[1, 1], [1, -1]]`. -/
def signCoefficient (i : Fin 2) : ℚ := if i = 0 then 1 else -1

@[simp] theorem signCoefficient_zero : signCoefficient 0 = 1 := rfl

/-- Signs are units. -/
theorem signCoefficient_ne_zero (i : Fin 2) : signCoefficient i ≠ 0 := by
  fin_cases i <;> norm_num [signCoefficient]

/-- Signs square to one. -/
theorem signCoefficient_mul_self (i : Fin 2) : signCoefficient i * signCoefficient i = 1 := by
  fin_cases i <;> norm_num [signCoefficient]

/-- The two signs are opposite. -/
theorem signCoefficient_of_ne {i j : Fin 2} (h : i ≠ j) :
    signCoefficient j = -signCoefficient i := by
  fin_cases i <;> fin_cases j <;> simp_all [signCoefficient]

/-- The coefficient table `T'_{abc} = 1 + s_a s_b s_c` obtained from the table of `⟨2⟩` by the
change of basis `[[1, 1], [1, -1]]` on every leg.  Its support is the four triples with an even
number of index-`1` entries. -/
def hadamardCoefficients : (∀ _ : Leg, Fin 2) → ℚ :=
  fun p ↦ 1 + signCoefficient (p .X) * signCoefficient (p .Y) * signCoefficient (p .Z)

/-- The change of basis `[[1, 1], [1, -1]]` as a linear map of coordinate vectors. -/
def hadamardLegMap : (Fin 2 → ℚ) →ₗ[ℚ] (Fin 2 → ℚ) where
  toFun x := fun i ↦ if i = 0 then x 0 + x 1 else x 0 - x 1
  map_add' x y := by
    funext i
    by_cases h : i = 0 <;> simp [h] <;> ring
  map_smul' c x := by
    funext i
    by_cases h : i = 0 <;> simp [h] <;> ring

@[simp] theorem hadamardLegMap_apply (x : Fin 2 → ℚ) (i : Fin 2) :
    hadamardLegMap x i = if i = 0 then x 0 + x 1 else x 0 - x 1 := rfl

/-- The inverse change of basis, `(1/2)·[[1, 1], [1, -1]]`. -/
def hadamardLegInv : (Fin 2 → ℚ) →ₗ[ℚ] (Fin 2 → ℚ) where
  toFun y := fun i ↦ if i = 0 then (y 0 + y 1) / 2 else (y 0 - y 1) / 2
  map_add' x y := by
    funext i
    by_cases h : i = 0 <;> simp [h] <;> ring
  map_smul' c x := by
    funext i
    by_cases h : i = 0 <;> simp [h] <;> ring

@[simp] theorem hadamardLegInv_apply (y : Fin 2 → ℚ) (i : Fin 2) :
    hadamardLegInv y i = if i = 0 then (y 0 + y 1) / 2 else (y 0 - y 1) / 2 := rfl

/-- The change of basis is invertible: this is where `2 ≠ 0` is used, so the witness is stated over
`ℚ` rather than over an arbitrary field. -/
def hadamardLegEquiv : (Fin 2 → ℚ) ≃ₗ[ℚ] (Fin 2 → ℚ) :=
  LinearEquiv.ofLinear hadamardLegMap hadamardLegInv
    (by
      ext y i
      fin_cases i <;> simp <;> ring)
    (by
      ext x i
      fin_cases i <;> simp)

@[simp] theorem hadamardLegEquiv_apply (x : Fin 2 → ℚ) :
    hadamardLegEquiv x = hadamardLegMap x := rfl

/-- The images of the two standard basis vectors: `e₀ ↦ (1, 1)` and `e₁ ↦ (1, -1)`. -/
theorem hadamardLegMap_single (i j : Fin 2) :
    hadamardLegMap (Pi.single i 1) j = if i = 0 then 1 else signCoefficient j := by
  fin_cases i <;> fin_cases j <;> simp [signCoefficient]

/-- **The two tables define legwise isomorphic tensors.**

Proof sketch: apply `hadamardLegEquiv` on every leg to `⟨2⟩ = ∑_i e_i ⊗ e_i ⊗ e_i` and read off
coordinates.  The `i = 0` summand contributes the constant `1` and the `i = 1` summand contributes
`s_a s_b s_c`, so the coefficient at `(a, b, c)` is `1 + s_a s_b s_c`. -/
theorem isomorphic_coordinateTensor_hadamardCoefficients :
    Isomorphic (coordinateTensor (diagonalCoefficients ℚ (Fin 2)))
      (coordinateTensor hadamardCoefficients) := by
  refine (Isomorphic.map _ (fun _ : Leg ↦ hadamardLegEquiv)).trans (Isomorphic.of_eq ?_)
  refine standardCoordinate_ext (K := ℚ) (κ := fun _ : Leg ↦ Fin 2) fun q ↦ ?_
  have hlhs : standardCoordinateEquiv (K := ℚ) (κ := fun _ : Leg ↦ Fin 2)
      (Tensor.map (fun _ : Leg ↦ (hadamardLegEquiv : (Fin 2 → ℚ) →ₗ[ℚ] (Fin 2 → ℚ)))
        (coordinateTensor (diagonalCoefficients ℚ (Fin 2)))) q =
      ∑ i : Fin 2, ∏ c : Leg, hadamardLegMap (Pi.single i 1) (q c) := by
    rw [coordinateTensor_diagonalCoefficients, diagonalTensor, map_sum, map_sum,
      Finset.sum_apply]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [Tensor.map_pure, standardCoordinateEquiv_pure]
    rfl
  rw [hlhs, standardCoordinateEquiv_coordinateTensor, Fin.sum_univ_two]
  simp only [hadamardLegMap_single]
  rw [prod_leg, prod_leg]
  simp [hadamardCoefficients]

/-- **The transformed table has independence number one.**

Proof sketch: two distinct terms of an independent set differ in all three coordinates, so their
sign products are opposite; but `(1 + t)(1 - t) = 1 - t² = 0` because each sign squares to one, so
one of the two coefficients vanishes, contradicting membership in the support.  A single term
exists, namely the all-`0` triple with coefficient `2`. -/
theorem independenceNumber_hadamardCoefficients :
    independenceNumber hadamardCoefficients = 1 := by
  refine le_antisymm (independenceNumber_le fun S hS ↦ ?_) ?_
  · by_contra hcard
    rw [not_le] at hcard
    obtain ⟨p, hp, q, hq, hpq⟩ := Finset.one_lt_card.mp hcard
    have hdiff : ∀ c, p c ≠ q c := fun c h ↦ hpq (hS.distinct p hp q hq c h)
    have ha := signCoefficient_mul_self (p .X)
    have hb := signCoefficient_mul_self (p .Y)
    have hc := signCoefficient_mul_self (p .Z)
    have hmul : hadamardCoefficients p * hadamardCoefficients q = 0 := by
      simp only [hadamardCoefficients]
      rw [signCoefficient_of_ne (hdiff .X), signCoefficient_of_ne (hdiff .Y),
        signCoefficient_of_ne (hdiff .Z)]
      have ht : (signCoefficient (p .X) * signCoefficient (p .Y) * signCoefficient (p .Z)) *
          (signCoefficient (p .X) * signCoefficient (p .Y) * signCoefficient (p .Z)) = 1 := by
        calc (signCoefficient (p .X) * signCoefficient (p .Y) * signCoefficient (p .Z)) *
              (signCoefficient (p .X) * signCoefficient (p .Y) * signCoefficient (p .Z))
            = (signCoefficient (p .X) * signCoefficient (p .X)) *
                ((signCoefficient (p .Y) * signCoefficient (p .Y)) *
                  (signCoefficient (p .Z) * signCoefficient (p .Z))) := by ring
          _ = 1 := by rw [ha, hb, hc]; ring
      have hexp : (1 + signCoefficient (p .X) * signCoefficient (p .Y) * signCoefficient (p .Z)) *
          (1 + -signCoefficient (p .X) * -signCoefficient (p .Y) * -signCoefficient (p .Z)) =
          1 - (signCoefficient (p .X) * signCoefficient (p .Y) * signCoefficient (p .Z)) *
            (signCoefficient (p .X) * signCoefficient (p .Y) * signCoefficient (p .Z)) := by ring
      rw [hexp, ht]
      ring
    rcases mul_eq_zero.mp hmul with h | h
    · exact hS.ne_zero p hp h
    · exact hS.ne_zero q hq h
  · refine one_le_independenceNumber (T := hadamardCoefficients) (p := fun _ ↦ 0) ?_
    norm_num [hadamardCoefficients, signCoefficient]

/-- The table of `⟨2⟩` over `ℚ` has independence number two. -/
theorem independenceNumber_diagonalCoefficients_fin_two :
    independenceNumber (diagonalCoefficients ℚ (Fin 2)) = 2 := by
  rw [independenceNumber_diagonalCoefficients]
  simp

/-- **The independence number is not an invariant of the abstract tensor.**  Two legwise isomorphic
coefficient tables over `ℚ` have different independence numbers, `2` and `1`.  This is the reason
`independenceNumber` and the asymptotic independence number are defined on coefficient tables and
never on `Tensor3`. -/
theorem independenceNumber_not_isomorphism_invariant :
    Isomorphic (coordinateTensor (diagonalCoefficients ℚ (Fin 2)))
        (coordinateTensor hadamardCoefficients) ∧
      independenceNumber (diagonalCoefficients ℚ (Fin 2)) ≠
        independenceNumber hadamardCoefficients := by
  refine ⟨isomorphic_coordinateTensor_hadamardCoefficients, ?_⟩
  rw [independenceNumber_diagonalCoefficients_fin_two, independenceNumber_hadamardCoefficients]
  norm_num

end HadamardWitness

/-! ## Block tables and indexed direct sums

The abstract tensor of a block table `coordinateDirectSum A` restricts onto the indexed direct sum
of the abstract tensors of its blocks.  This is the bridge the Galactic-method certificates of
`MatrixMultiplication/GalacticMethod.lean` use to turn a coefficient-level block decomposition into
a direct-sum restriction. -/

section CoordinateDirectSum

variable {K : Type u} [CommSemiring K] {κ : Leg → Type v} {ι : Type v}
variable [DecidableEq ι] [Fintype ι] [∀ i, Fintype (κ i)] [∀ i, DecidableEq (κ i)]

/-- Fold the coordinate space of a block table into the indexed direct sum of the coordinate
spaces of its blocks: read off each block and include it in the corresponding summand. -/
noncomputable def blockFold (c : Leg) :
    CoordinateSpace K (fun i ↦ ι × κ i) c →ₗ[K]
      IndexedDirectSumSpace K (fun _ : ι ↦ CoordinateSpace K κ) c :=
  ∑ j : ι, (indexedInclude (K := K) (V := fun _ : ι ↦ CoordinateSpace K κ) j c) ∘ₗ
    LinearMap.funLeft K K (fun x : κ c ↦ (j, x))

omit [∀ i, Fintype (κ i)] [∀ i, DecidableEq (κ i)] in
/-- Folding after the inclusion of block `j` is the inclusion of the `j`-th summand. -/
theorem blockFold_comp_blockInclude (j : ι) (c : Leg) :
    blockFold (K := K) (κ := κ) (ι := ι) c ∘ₗ coordinateBlockInclude (K := K) j c =
      indexedInclude (K := K) (V := fun _ : ι ↦ CoordinateSpace K κ) j c := by
  classical
  refine LinearMap.ext fun v ↦ ?_
  show (∑ j' : ι, (indexedInclude (K := K) (V := fun _ : ι ↦ CoordinateSpace K κ) j' c) ∘ₗ
      LinearMap.funLeft K K (fun x : κ c ↦ (j', x))) (coordinateBlockInclude (K := K) j c v) = _
  rw [LinearMap.sum_apply]
  have hterm : ∀ j' : ι,
      ((indexedInclude (K := K) (V := fun _ : ι ↦ CoordinateSpace K κ) j' c) ∘ₗ
          LinearMap.funLeft K K (fun x : κ c ↦ (j', x))) (coordinateBlockInclude (K := K) j c v) =
        if j' = j then
          indexedInclude (K := K) (V := fun _ : ι ↦ CoordinateSpace K κ) j c v else 0 := by
    intro j'
    have hres : LinearMap.funLeft K K (fun x : κ c ↦ (j', x)) (coordinateBlockInclude (K := K) j c v) =
        if j' = j then v else 0 := by
      funext x
      by_cases hj : j' = j
      · subst hj
        simp [LinearMap.funLeft_apply, blockInclude_apply]
      · simp [LinearMap.funLeft_apply, blockInclude_apply, hj]
    show (indexedInclude (K := K) (V := fun _ : ι ↦ CoordinateSpace K κ) j' c)
        (LinearMap.funLeft K K (fun x : κ c ↦ (j', x)) (coordinateBlockInclude (K := K) j c v)) = _
    rw [hres]
    by_cases hj : j' = j
    · subst hj
      simp
    · simp [hj]
  rw [Finset.sum_congr rfl fun j' _ ↦ hterm j', Finset.sum_ite_eq' Finset.univ j
    (fun _ ↦ indexedInclude (K := K) (V := fun _ : ι ↦ CoordinateSpace K κ) j c v),
    if_pos (Finset.mem_univ j)]

/-- **The abstract tensor of a block table restricts onto the indexed direct sum of its blocks.**

The legwise map `blockFold` reads off each block and includes it in the corresponding summand; for
a finite index type it is bijective, but only the restriction direction is proved here, because
that is the direction the Galactic-method certificates need. -/
theorem Restricts.coordinateTensor_coordinateDirectSum (A : ι → (∀ i, κ i) → K) :
    Restricts (coordinateTensor (coordinateDirectSum A))
      (Tensor.indexedDirectSum (K := K) (V := fun _ : ι ↦ CoordinateSpace K κ)
        (fun j ↦ coordinateTensor (A j))) := by
  classical
  refine ⟨blockFold (K := K) (κ := κ) (ι := ι), ?_⟩
  rw [coordinateTensor_coordinateDirectSum_eq_sum, map_sum]
  unfold Tensor.indexedDirectSum
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  have hcomp : Tensor.map (fun c ↦ blockFold (K := K) (κ := κ) (ι := ι) c ∘ₗ
        coordinateBlockInclude (K := K) j c) (coordinateTensor (A j)) =
      Tensor.map (blockFold (K := K) (κ := κ) (ι := ι))
        (Tensor.map (coordinateBlockInclude (K := K) j) (coordinateTensor (A j))) := by
    rw [Tensor.map_comp]
    rfl
  have hfun : (fun c ↦ blockFold (K := K) (κ := κ) (ι := ι) c ∘ₗ coordinateBlockInclude (K := K) j c) =
      indexedInclude (K := K) (V := fun _ : ι ↦ CoordinateSpace K κ) j := by
    funext c
    exact blockFold_comp_blockInclude j c
  rw [← hcomp, hfun]

end CoordinateDirectSum

/-! ## Conciseness in coordinates, in the coordinate calculus

`Tensor/Concise.lean` defines `IsCoordinateConcise` --- the slices of the coefficient table in the
direction of a leg span that leg --- together with the pointwise-product infrastructure
(`mulPair`, `span_image2_mulPair`) it rests on.  Everything below relates that predicate to the
coordinate calculus of this file: Kronecker products, relabellings, Kronecker powers, and the
flattening lower bounds `card_le_of_rankLE` and `card_le_asymptoticRank`.

`card_le_asymptoticRank` is the form the Alman--Vassilevska Williams barrier consumes:
`|κ i| ≤ R̃(T)` for a table concise on leg `i`. -/

section CoordinateConcise

open Submodule

variable {K : Type u} [Field K] {κ : Leg → Type v} {κ' : Leg → Type v}
variable {κ'' : Leg → Type w}

/-- Slices of a Kronecker product are pointwise products of slices. -/
theorem coordinateSlice_coordinateProduct (A : (∀ j, κ j) → K) (B : (∀ j, κ' j) → K)
    (i : Leg) (p : ∀ j, κ j × κ' j) :
    coordinateSlice (coordinateProduct A B) i p =
      mulPair K (κ i) (κ' i) (coordinateSlice A i fun j ↦ (p j).1)
        (coordinateSlice B i fun j ↦ (p j).2) := by
  funext q
  rw [mulPair_apply, coordinateSlice, coordinateProduct, coordinateSlice, coordinateSlice]
  congr 1
  · congr 1
    funext j
    by_cases hj : j = i
    · subst hj
      simp
    · simp [Function.update_of_ne hj]
  · congr 1
    funext j
    by_cases hj : j = i
    · subst hj
      simp
    · simp [Function.update_of_ne hj]

/-- **Conciseness in coordinates is multiplicative under Kronecker products.** -/
theorem IsCoordinateConcise.coordinateProduct [∀ j, Fintype (κ j)] [∀ j, DecidableEq (κ j)]
    [∀ j, Fintype (κ' j)] [∀ j, DecidableEq (κ' j)]
    {A : (∀ j, κ j) → K} {B : (∀ j, κ' j) → K} {i : Leg}
    (hA : IsCoordinateConcise A i) (hB : IsCoordinateConcise B i) :
    IsCoordinateConcise (Tensor.coordinateProduct A B) i := by
  have hrange : Set.range (coordinateSlice (Tensor.coordinateProduct A B) i) =
      Set.image2 (fun u v ↦ mulPair K (κ i) (κ' i) u v)
        (Set.range (coordinateSlice A i)) (Set.range (coordinateSlice B i)) := by
    ext v
    constructor
    · rintro ⟨p, rfl⟩
      exact ⟨_, ⟨fun j ↦ (p j).1, rfl⟩, _, ⟨fun j ↦ (p j).2, rfl⟩,
        (coordinateSlice_coordinateProduct A B i p).symm⟩
    · rintro ⟨u, ⟨p, rfl⟩, w, ⟨q, rfl⟩, rfl⟩
      exact ⟨fun j ↦ (p j, q j), coordinateSlice_coordinateProduct A B i _⟩
  rw [IsCoordinateConcise, hrange]
  exact span_image2_mulPair K (κ i) (κ' i) hA hB

/-- Slices of a relabelled table are the relabelled slices. -/
theorem coordinateSlice_coordinateRelabel (e : ∀ j, κ j ≃ κ'' j) (A : (∀ j, κ j) → K)
    (i : Leg) (p : ∀ j, κ'' j) :
    coordinateSlice (coordinateRelabel e A) i p =
      LinearMap.funLeft K K (e i).symm (coordinateSlice A i fun j ↦ (e j).symm (p j)) := by
  funext y
  rw [coordinateSlice, coordinateRelabel_apply, LinearMap.funLeft_apply, coordinateSlice]
  congr 1
  funext j
  by_cases hj : j = i
  · subst hj
    simp
  · simp [Function.update_of_ne hj]

/-- **Conciseness in coordinates is invariant under relabelling the variables.** -/
theorem IsCoordinateConcise.coordinateRelabel {A : (∀ j, κ j) → K} {i : Leg}
    (hA : IsCoordinateConcise A i) (e : ∀ j, κ j ≃ κ'' j) :
    IsCoordinateConcise (Tensor.coordinateRelabel e A) i := by
  have hrange : Set.range (coordinateSlice (Tensor.coordinateRelabel e A) i) =
      (LinearMap.funLeft K K (e i).symm) '' (Set.range (coordinateSlice A i)) := by
    ext v
    constructor
    · rintro ⟨p, rfl⟩
      exact ⟨_, ⟨fun j ↦ (e j).symm (p j), rfl⟩, (coordinateSlice_coordinateRelabel e A i p).symm⟩
    · rintro ⟨u, ⟨p, rfl⟩, rfl⟩
      exact ⟨fun j ↦ e j (p j), by
        rw [coordinateSlice_coordinateRelabel]
        simp⟩
  have hsurj : Function.Surjective (LinearMap.funLeft K K (e i).symm) :=
    (LinearEquiv.funCongrLeft K K (e i).symm).surjective
  rw [IsCoordinateConcise, hrange, ← Submodule.map_span, hA, ← LinearMap.range_eq_map]
  exact LinearMap.range_eq_top.mpr hsurj

end CoordinateConcise

section ConcisePower

open Submodule

variable {K : Type u} [Field K] {κ : Leg → Type v}

/-- The zeroth Kronecker power is concise on every leg: it is the scalar `1` on the single
variable per leg. -/
theorem isCoordinateConcise_coordinatePower_zero (T : (∀ j, κ j) → K) (i : Leg) :
    IsCoordinateConcise (coordinatePower T 0) i := by
  refine le_antisymm le_top fun v _ ↦ ?_
  have hone : (fun _ : Fin 0 → κ i ↦ (1 : K)) ∈
      Set.range (coordinateSlice (coordinatePower T 0) i) := by
    refine ⟨fun _ t ↦ t.elim0, ?_⟩
    funext x
    simp [coordinateSlice]
  have hv : v = v (fun t ↦ t.elim0) • (fun _ : Fin 0 → κ i ↦ (1 : K)) := by
    funext y
    have hy : y = fun t ↦ t.elim0 := by
      funext t
      exact t.elim0
    rw [hy, Pi.smul_apply, smul_eq_mul, mul_one]
  rw [hv]
  exact Submodule.smul_mem _ _ (Submodule.subset_span hone)

variable [∀ j, Fintype (κ j)] [∀ j, DecidableEq (κ j)]

/-- **Conciseness in coordinates passes to Kronecker powers.** -/
theorem IsCoordinateConcise.coordinatePower {T : (∀ j, κ j) → K} {i : Leg}
    (h : IsCoordinateConcise T i) (n : ℕ) :
    IsCoordinateConcise (Tensor.coordinatePower T n) i := by
  induction n with
  | zero => exact isCoordinateConcise_coordinatePower_zero T i
  | succ n ih =>
      rw [← coordinateRelabel_coordinateProduct_succ T n]
      exact (ih.coordinateProduct h).coordinateRelabel _

omit [∀ j, DecidableEq (κ j)] in
/-- **The flattening lower bound in coordinates.**  If `T` is concise on leg `i` in coordinates,
every rank decomposition of the tensor it defines has at least `|κ i|` terms.

Proof sketch: expanding a decomposition into `r` pure tensors, the coefficient of `T` at a triple
is the sum over the `r` terms of the product of their three coordinates; slicing in the direction
of leg `i` therefore writes every slice as a linear combination of the `r` leg-`i` vectors of the
terms.  Conciseness says the slices span, so those `r` vectors span, and `|κ i| ≤ r`. -/
theorem card_le_of_rankLE {T : (∀ j, κ j) → K} {i : Leg} {r : ℕ}
    (hconc : IsCoordinateConcise T i) (hr : RankLE r (coordinateTensor T)) :
    Fintype.card (κ i) ≤ r := by
  classical
  obtain ⟨terms, hlen, hsum⟩ := hr
  set N := terms.length with hN
  have hcoef : ∀ p : ∀ j, κ j, T p = ∑ t : Fin N, ∏ j, (terms.get t j) (p j) := by
    intro p
    have h : standardCoordinateEquiv (K := K) (κ := κ) (coordinateTensor T) p =
        standardCoordinateEquiv (K := K) (κ := κ) ((terms.map (pure (K := K))).sum) p := by
      rw [← hsum]
    rw [standardCoordinateEquiv_coordinateTensor] at h
    rw [h, list_map_sum_eq_fin_sum (pure (K := K)) terms, map_sum, Finset.sum_apply]
    exact Finset.sum_congr rfl fun t _ ↦ standardCoordinateEquiv_pure _ p
  have hslice : ∀ p : ∀ j, κ j, coordinateSlice T i p ∈
      Submodule.span K (Set.range fun t : Fin N ↦ (terms.get t) i) := by
    intro p
    have hrepr : coordinateSlice T i p =
        ∑ t : Fin N, (∏ j ∈ Finset.univ.erase i, (terms.get t j) (p j)) • ((terms.get t) i) := by
      funext x
      rw [coordinateSlice, hcoef, Finset.sum_apply]
      refine Finset.sum_congr rfl fun t _ ↦ ?_
      rw [Pi.smul_apply, smul_eq_mul,
        ← Finset.mul_prod_erase Finset.univ (fun j ↦ (terms.get t j) (Function.update p i x j))
          (Finset.mem_univ i), Function.update_self, mul_comm]
      congr 1
      refine Finset.prod_congr rfl fun j hj ↦ ?_
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
    rw [hrepr]
    exact Submodule.sum_mem _ fun t _ ↦
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨t, rfl⟩)
  have hspan : Submodule.span K (Set.range fun t : Fin N ↦ (terms.get t) i) = ⊤ := by
    refine le_antisymm le_top ?_
    rw [← hconc]
    exact Submodule.span_le.mpr (by rintro _ ⟨p, rfl⟩; exact hslice p)
  have hfin := finrank_le_of_span_eq_top hspan
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at hfin
  exact hfin.trans hlen

/-- **Conciseness in coordinates bounds the leg dimensions by the asymptotic rank**,
`|κ i| ≤ R̃(T)`.  This is the single use of conciseness in AVW Theorem 4.1.

Proof sketch: conciseness passes to every Kronecker power
(`IsCoordinateConcise.coordinatePower`), whose leg `i` has `|κ i|^n` variables, so
`card_le_of_rankLE` gives `|κ i|^n ≤ R(T^{⊗n})` for every `n`; a geometric lower bound along the
powers is a lower bound for the asymptotic rank (`le_asymptoticRank_of_pow_le`). -/
theorem card_le_asymptoticRank {T : (∀ j, κ j) → K} {i : Leg}
    (hconc : IsCoordinateConcise T i) :
    ((Fintype.card (κ i) : ℕ) : ℝ) ≤ asymptoticRank (coordinateTensor T) := by
  refine le_asymptoticRank_of_pow_le fun n ↦ ?_
  have hpow : Fintype.card (Fin n → κ i) ≤ rank (coordinateTensor (Tensor.coordinatePower T n)) :=
    card_le_of_rankLE (hconc.coordinatePower n) (rank_spec _)
  rw [Fintype.card_fun, Fintype.card_fin] at hpow
  have hiso : rank (coordinateTensor (Tensor.coordinatePower T n)) =
      rankPowerSequence (coordinateTensor T) n :=
    rank_isomorphic (Isomorphic.coordinateTensor_coordinatePower T n)
  rw [hiso] at hpow
  exact_mod_cast hpow
/-- Every canonical power of a concise coordinate tensor has positive rank. -/
theorem one_le_rank_power_coordinateTensor {T : (∀ j, κ j) → K} {i : Leg} [Nonempty (κ i)]
    (h : IsCoordinateConcise T i) (m : ℕ) :
    1 ≤ rank (Tensor.power (coordinateTensor T) m) := by
  obtain ⟨p, hp⟩ := exists_ne_zero_of_isCoordinateConcise h
  exact le_trans (one_le_independenceNumber_coordinatePower hp m)
    (independenceNumber_coordinatePower_le_rank T m)

end ConcisePower

/-! ## Letters of a triple of words -/

section Letters

variable {K : Type u} [CommSemiring K] {κ : Leg → Type v}

/-- The `k`-th **letter** of a triple of length-`n` words: the index triple of the base table
obtained by reading coordinate `k` on each leg.  A term of `T^{⊗n}` is a term of `T` in each of
its `n` letters. -/
def powerLetter {n : ℕ} (s : ∀ i, Fin n → κ i) (k : Fin n) : ∀ i, κ i := fun i ↦ s i k

/-- The `i`-th coordinate of the `k`-th letter is the `k`-th letter of the `i`-th word. -/
@[simp] theorem powerLetter_apply {n : ℕ} (s : ∀ i, Fin n → κ i) (k : Fin n) (i : Leg) :
    powerLetter s k i = s i k := rfl

/-- The coefficient of a triple of words is the product of the coefficients of its letters. -/
theorem coordinatePower_eq_prod_powerLetter (T : (∀ i, κ i) → K) {n : ℕ}
    (s : ∀ i, Fin n → κ i) : coordinatePower T n s = ∏ k : Fin n, T (powerLetter s k) := rfl

/-- Every letter of a term of `T^{⊗n}` is a term of `T`: a product vanishes as soon as one of its
factors does. -/
theorem ne_zero_of_coordinatePower_ne_zero {T : (∀ i, κ i) → K} {n : ℕ}
    {s : ∀ i, Fin n → κ i} (hs : coordinatePower T n s ≠ 0) (k : Fin n) :
    T (powerLetter s k) ≠ 0 := fun h ↦
  hs (by rw [coordinatePower_eq_prod_powerLetter]; exact Finset.prod_eq_zero (Finset.mem_univ k) h)

end Letters


end AlgebraicComplexity.Tensor
