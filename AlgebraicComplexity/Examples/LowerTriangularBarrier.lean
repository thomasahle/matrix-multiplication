/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.CornerBarrier

/-!
# Lower triangular tensors and the corner barrier (AVW Section 7.3)

This file is the first half of milestone **N** of `BARRIER_FRAMEWORK.md`.  It formalizes

> J. Alman and V. Vassilevska Williams, *Limits on All Known (and Some Unknown) Approaches to
> Matrix Multiplication*, arXiv:1810.08671v1, Section 7.3, **Theorem 7.5**,

together with AVW **Definition 7.1** (lower triangular tensors, Section 7.4) and the trivial half
of **Theorem 7.6**.

## The tensor

AVW define, for each positive integer `q`, the *lower triangular version* of the cyclic group
tensor `T_q = T_{C_q}`:

```text
T_q^lower = ∑_{i=0}^{q-1} ∑_{j=0}^{q-1-i} x_i y_j z_{i+j}.
```

Its support is therefore `{(i, j, k) | i + j = k}` inside `{0,…,q-1}³` — the *unreduced* sums,
which is exactly what distinguishes it from `T_q`, whose support uses `i + j mod q`.  The
coefficient table is `lowerTriangularTable K q`, the indicator of `i + j = k` read in `ℕ`.

## Main result: AVW Theorem 7.5

AVW state Theorem 7.5 as "for each integer `q ≥ 2` there is a constant `c_q > 2` such that
`ω_g(T_q^lower) ≥ c_q`", and prove it in two lines: `T_q^lower` is of the form described by
Corollary 5.1, so `Ī(T_q^lower) < q`, and Corollary 4.3 concludes.  Both inputs are already in
the tree, and both are *explicit*, so the constant here is explicit as well:

```text
ω_g^{coord}(T_q^lower) ≥ 6 / (3 − cornerExponent q) > 2,
cornerExponent q = 1 / (q² (q+1)² log q).
```

The paper states no numerical constant at all (`c_q` is left unnamed), so this is a strictly
sharper statement than the printed one; `cornerExponent` is the repository's constant from
`MatrixMultiplication/IndependenceMassDistribution.lean`, which is exactly AVW's printed
`1/(q²(q+1)² log q)`, the sharp Pinsker exponent of `Combinatorics/BinomialTail.lean` leaving no
gap.

## Why the corner hypotheses hold

`T_q^lower` has `q` variables on each leg, and its two extreme terms are

```text
x_{q-1} y_0 z_{q-1}      and      x_0 y_{q-1} z_{q-1}.
```

The first is the *only* term using `x_{q-1}` (as `i = q-1` forces `j = 0`, hence `k = q-1`), the
second is the only term using `y_{q-1}`, both use `z_{q-1}`, and `x_0 ≠ x_{q-1}` as soon as
`q ≥ 2`.  That is literally the configuration of AVW Corollary 5.1
(`asymptoticIndependenceNumber_le_cornerBound_of_corner_terms`), after the harmless
relabelling of AVW's `z₁` as `z_{q-1}` — the corollary never asks the shared `z`-variable to be
any particular one.

## Deviations from the paper

* **Which exponent.**  Per the milestone-F correction recorded in
  `MatrixMultiplication/IndependenceBarrier.lean`, the independence number is basis-dependent, so
  AVW Theorem 4.1 and Corollary 4.3 bound the **coordinate** galactic exponent
  `coordinateGalacticExponent`, the infimum over monomial degenerations read *in the variables of
  the given table*.  Theorem 7.5 is therefore stated for `coordinateGalacticExponent`; the
  abstract `galacticExponent` satisfies `galacticExponent ≤ coordinateGalacticExponent`, which is
  the wrong direction to transport a lower bound, so **no claim is made about it**.
* **The nonemptiness side condition.**  `coordinateGalacticExponent` is an `sInf`, so Corollary
  4.3 carries the hypothesis that the certificate value set is nonempty.  It is discharged here
  for every `q ≥ 2` by the explicit certificate `(n,a,b,c,F) = (1,1,1,q,1)`
  (`coordinateGalacticCertificate_lowerTriangularTable`), exactly as
  `Examples/GroupTensorBarrier.lean` does for `T_G`, so Theorem 7.5 below has no side condition.
* **Constants.**  See above: explicit rather than unnamed, and a factor `2` weaker in the exponent
  gap than AVW's printed constant.

## What is *not* done here

**AVW Theorem 7.6** (a lower triangular tensor has `Ī(T) = q` if and only if it has `q` diagonal
terms no two of which share a `z`-variable) is the second half of milestone **N** and is not
attempted.  What is recorded is AVW **Definition 7.1** itself (`IsLowerTriangular`), the check
that `T_q^lower` satisfies it (`isLowerTriangular_lowerTriangularTable`), the trivial half
`Ī(T) ≤ q` of Theorem 7.6 (`asymptoticIndependenceNumber_le_card_of_isLowerTriangular`, which
needs no triangularity at all), and the observation that `T_q^lower` fails the Theorem 7.6
criterion in the strongest possible way: *all* of its diagonal terms share the single variable
`z_{q-1}` (`lowerTriangularTable_diagonal_z`).  That is the structural reason Theorem 7.5 is true
and is consistent with AVW Remark 7.4.

## Layer placement

This is a layer-4 client (`AlgebraicComplexity/Examples/`).  It introduces one new coefficient
table and one new predicate on tables, and consumes the barrier chain unchanged:
`asymptoticIndependenceNumber_le_cornerBound_of_corner_terms` (AVW Corollary 5.1),
`Tensor.card_le_asymptoticRank` (conciseness), and
`six_div_add_two_le_coordinateGalacticExponent_of_concise` (AVW Corollary 4.3).
-/

namespace AlgebraicComplexity.Examples

open Tensor

universe u

/-! ## The coefficient table of `T_q^lower`

The independence-number API of `Tensor/IndependenceNumber.lean` is a calculus of *coefficient
tables* `T : (∀ i, κ i) → K`, not of abstract tensors, because `I` is basis-dependent.  All three
legs of `T_q^lower` carry the same variable set `{x_0,…,x_{q-1}}`, so the index family is the
constant family `fun _ ↦ Fin q`, in the style of `Tensor.GroupIndex`. -/

section Table

/-- The index family of the lower triangular tensor `T_q^lower`: the same `q` variables
`{0,…,q-1}` on each of the three legs. -/
abbrev LowerTriangularIndex (q : ℕ) : Leg → Type := fun _ ↦ Fin q

variable {K : Type u} [CommSemiring K]

/-- **The coefficient table of the lower triangular tensor `T_q^lower`** (Alman--Vassilevska
Williams, arXiv:1810.08671v1, Section 7.3):

```text
T_q^lower = ∑_{i=0}^{q-1} ∑_{j=0}^{q-1-i} x_i y_j z_{i+j},
```

i.e. the indicator of `i + j = k`, the sum being taken in `ℕ` and *not* modulo `q`.  The inner
range `j ≤ q-1-i` of AVW's double sum is automatic: `k = i + j` has to be a variable index, so
`i + j < q`.  Compare `Tensor.groupCoefficients` for the cyclic group `C_q`, whose support uses
`i + j mod q` instead; `T_q^lower ⊆ T_q` in AVW's sub-tensor sense. -/
def lowerTriangularTable (K : Type u) [CommSemiring K] (q : ℕ) :
    (∀ i, LowerTriangularIndex q i) → K :=
  fun p ↦ if (p .X : ℕ) + (p .Y : ℕ) = (p .Z : ℕ) then 1 else 0

/-- Evaluating the table of `T_q^lower`: the indicator of `i + j = k`. -/
theorem lowerTriangularTable_apply (q : ℕ) (p : ∀ i, LowerTriangularIndex q i) :
    lowerTriangularTable K q p = if (p .X : ℕ) + (p .Y : ℕ) = (p .Z : ℕ) then 1 else 0 := rfl

/-- The coefficient at a triple with `i + j = k` is `1`. -/
theorem lowerTriangularTable_of_add_eq {q : ℕ} {p : ∀ i, LowerTriangularIndex q i}
    (h : (p .X : ℕ) + (p .Y : ℕ) = (p .Z : ℕ)) : lowerTriangularTable K q p = 1 := if_pos h

/-- **The support of the table of `T_q^lower` is the locus `i + j = k`.**  This is the form every
support-combinatorial argument below consumes. -/
theorem lowerTriangularTable_ne_zero_iff [Nontrivial K] (q : ℕ)
    (p : ∀ i, LowerTriangularIndex q i) :
    lowerTriangularTable K q p ≠ 0 ↔ (p .X : ℕ) + (p .Y : ℕ) = (p .Z : ℕ) := by
  rw [lowerTriangularTable]
  by_cases h : (p .X : ℕ) + (p .Y : ℕ) = (p .Z : ℕ) <;> simp [h]

/-- **The last variable `x_{q-1}` of a leg of `T_q^lower`.**  It is the `x`-index of AVW's first
corner term `x_{q-1} y_0 z_{q-1}` and the shared `z`-index of both corner terms. -/
def lowerTriangularLast (q : ℕ) [NeZero q] : Fin q :=
  ⟨q - 1, Nat.sub_lt (Nat.pos_of_ne_zero (NeZero.ne q)) one_pos⟩

@[simp] theorem lowerTriangularLast_val (q : ℕ) [NeZero q] :
    (lowerTriangularLast q : ℕ) = q - 1 := rfl

end Table

/-! ## AVW Definition 7.1 and the trivial half of Theorem 7.6

Definition 7.1 is a property of an arbitrary table over `q` variables per leg, not of `T_q^lower`
alone; Theorem 7.6 characterizes the lower triangular tables with `Ī(T) = q`.  Only the definition,
the fact that `T_q^lower` satisfies it, and the direction `Ī(T) ≤ q` (which is the generic bound
`Tensor.asymptoticIndependenceNumber_le_card` and needs no triangularity) are recorded here. -/

section Definition71

variable {K : Type u} [CommSemiring K]

/-- **AVW Definition 7.1**: a table `T` over `X = {x_0,…,x_{q-1}}`, `Y = {y_0,…,y_{q-1}}`,
`Z = {z_0,…,z_{q-1}}` is *lower triangular* when

* for every `i, j` there is at most one `k` with `x_i y_j z_k` a term of `T` (`unique_z`), and
* no term `x_i y_j z_k` has `i + j ≥ q` (`triangular`).

The first clause is phrased as "two terms agreeing on the `X` and `Y` legs are equal", which is
the same statement and is the form the arguments consume. -/
structure IsLowerTriangular {q : ℕ} (T : (∀ i, LowerTriangularIndex q i) → K) : Prop where
  /-- At most one `z`-variable occurs with any given pair `(x_i, y_j)`. -/
  unique_z : ∀ p p', T p ≠ 0 → T p' ≠ 0 → p .X = p' .X → p .Y = p' .Y → p = p'
  /-- No term has `i + j ≥ q`. -/
  triangular : ∀ p, T p ≠ 0 → (p .X : ℕ) + (p .Y : ℕ) < q

/-- **`T_q^lower` is lower triangular** in the sense of AVW Definition 7.1: its terms are exactly
the triples with `k = i + j`, so `k` is determined by `(i, j)`, and `k < q` forces `i + j < q`. -/
theorem isLowerTriangular_lowerTriangularTable [Nontrivial K] (q : ℕ) :
    IsLowerTriangular (lowerTriangularTable K q) where
  unique_z := by
    intro p p' hp hp' hX hY
    rw [lowerTriangularTable_ne_zero_iff] at hp hp'
    funext i
    cases i with
    | X => exact hX
    | Y => exact hY
    | Z => exact Fin.ext (by rw [← hp, ← hp', hX, hY])
  triangular := by
    intro p hp
    rw [lowerTriangularTable_ne_zero_iff] at hp
    rw [hp]
    exact (p .Z).isLt

/-- **The trivial half of AVW Theorem 7.6**: a lower triangular tensor over `q` variables per leg
has `Ī(T) ≤ q`.

This direction needs no triangularity whatsoever — it is
`Tensor.asymptoticIndependenceNumber_le_card`, valid for every table, since a zeroing out cannot
create variables.  The content of Theorem 7.6 is the characterization of *when* the bound is
attained, which is milestone **N**'s second half and is not proved here. -/
theorem asymptoticIndependenceNumber_le_card_of_isLowerTriangular {q : ℕ}
    {T : (∀ i, LowerTriangularIndex q i) → K} (_h : IsLowerTriangular T) :
    asymptoticIndependenceNumber T ≤ (q : ℝ) := by
  have h := asymptoticIndependenceNumber_le_card T Leg.X
  simpa using h

/-- **`T_q^lower` fails the criterion of AVW Theorem 7.6 as badly as possible**: *every* diagonal
term `x_i y_j z_k` with `i + j = q - 1` uses the single variable `z_{q-1}`.

Theorem 7.6 says a lower triangular tensor has `Ī(T) = q` exactly when it has `q` diagonal terms
no two of which share a `z`-variable.  Here all `q` diagonal terms share `z_{q-1}`, which is the
structural reason `Ī(T_q^lower) < q` (Theorem 7.5 below) and matches AVW Remark 7.4. -/
theorem lowerTriangularTable_diagonal_z [Nontrivial K] (q : ℕ) [NeZero q]
    {p : ∀ i, LowerTriangularIndex q i} (hp : lowerTriangularTable K q p ≠ 0)
    (hdiag : (p .X : ℕ) + (p .Y : ℕ) = q - 1) : p .Z = lowerTriangularLast q := by
  rw [lowerTriangularTable_ne_zero_iff] at hp
  exact Fin.ext (by rw [← hp, hdiag, lowerTriangularLast_val])

end Definition71

/-! ## AVW Corollary 5.1 applied to `T_q^lower`

The two corner terms are `x_{q-1} y_0 z_{q-1}` and `x_0 y_{q-1} z_{q-1}`.  Uniqueness of each is
immediate from the support description `i + j = k < q`: `i = q-1` leaves only `j = 0`, and
`j = q-1` leaves only `i = 0`. -/

section Corner

variable {K : Type u} [CommSemiring K] [NoZeroDivisors K] [Nontrivial K]

omit [NoZeroDivisors K] in
/-- The unique term of `T_q^lower` using `x_{q-1}` is `x_{q-1} y_0 z_{q-1}`. -/
theorem lowerTriangularTable_eq_of_X_last {q : ℕ} [NeZero q]
    {p : ∀ i, LowerTriangularIndex q i} (hp : lowerTriangularTable K q p ≠ 0)
    (hx : p .X = lowerTriangularLast q) :
    p = ofLegs (lowerTriangularLast q) (0 : Fin q) (lowerTriangularLast q) := by
  have hq : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  rw [lowerTriangularTable_ne_zero_iff] at hp
  have hxv : (p .X : ℕ) = q - 1 := by rw [hx, lowerTriangularLast_val]
  have hzlt : (p .Z : ℕ) < q := (p .Z).isLt
  have hy : (p .Y : ℕ) = 0 := by omega
  have hz : (p .Z : ℕ) = q - 1 := by omega
  funext i
  cases i with
  | X => exact hx
  | Y => exact Fin.ext (by rw [hy]; simp)
  | Z => exact Fin.ext (by rw [hz]; rfl)

omit [NoZeroDivisors K] in
/-- The unique term of `T_q^lower` using `y_{q-1}` is `x_0 y_{q-1} z_{q-1}`. -/
theorem lowerTriangularTable_eq_of_Y_last {q : ℕ} [NeZero q]
    {p : ∀ i, LowerTriangularIndex q i} (hp : lowerTriangularTable K q p ≠ 0)
    (hy : p .Y = lowerTriangularLast q) :
    p = ofLegs (0 : Fin q) (lowerTriangularLast q) (lowerTriangularLast q) := by
  have hq : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  rw [lowerTriangularTable_ne_zero_iff] at hp
  have hyv : (p .Y : ℕ) = q - 1 := by rw [hy, lowerTriangularLast_val]
  have hzlt : (p .Z : ℕ) < q := (p .Z).isLt
  have hx : (p .X : ℕ) = 0 := by omega
  have hz : (p .Z : ℕ) = q - 1 := by omega
  funext i
  cases i with
  | X => exact Fin.ext (by rw [hx]; simp)
  | Y => exact hy
  | Z => exact Fin.ext (by rw [hz]; rfl)

/-- **AVW Theorem 7.5, step 1**: `Ī(T_q^lower) ≤ c_q = q^{1 - cornerExponent q} < q` for every
`q ≥ 2`.

This is AVW Corollary 5.1
(`asymptoticIndependenceNumber_le_cornerBound_of_corner_terms`) applied with
`xOne = x_0`, `xLast = x_{q-1}`, `yOne = y_0`, `yLast = y_{q-1}`, `zOne = z_{q-1}`: the table has
`q` variables per leg, `x_{q-1} y_0 z_{q-1}` and `x_0 y_{q-1} z_{q-1}` are terms
(`lowerTriangularTable_of_add_eq`), each is the only term using its extreme variable
(`lowerTriangularTable_eq_of_X_last`, `lowerTriangularTable_eq_of_Y_last`), and `x_0 ≠ x_{q-1}`
because `q ≥ 2`.  AVW's printed corollary places the shared `z`-variable at index `1`; nothing in
its proof or its Lean statement depends on which `z`-variable it is. -/
theorem asymptoticIndependenceNumber_lowerTriangularTable_le_cornerBound {q : ℕ} (hq : 2 ≤ q) :
    asymptoticIndependenceNumber (lowerTriangularTable K q) ≤ cornerBound q := by
  haveI : NeZero q := ⟨by omega⟩
  have hne : (0 : Fin q) ≠ lowerTriangularLast q := by
    intro h
    have : (0 : ℕ) = q - 1 := congrArg Fin.val h
    omega
  refine asymptoticIndependenceNumber_le_cornerBound_of_corner_terms (lowerTriangularTable K q)
    hq (fun _ ↦ Fintype.card_fin q)
    (xOne := (0 : Fin q)) (xLast := lowerTriangularLast q)
    (yOne := (0 : Fin q)) (yLast := lowerTriangularLast q)
    (zOne := lowerTriangularLast q) hne ?_ ?_ ?_ ?_
  · rw [lowerTriangularTable_of_add_eq (K := K)]
    · exact one_ne_zero
    · show (lowerTriangularLast q : ℕ) + ((0 : Fin q) : ℕ) = (lowerTriangularLast q : ℕ)
      simp
  · rw [lowerTriangularTable_of_add_eq (K := K)]
    · exact one_ne_zero
    · show ((0 : Fin q) : ℕ) + (lowerTriangularLast q : ℕ) = (lowerTriangularLast q : ℕ)
      simp
  · exact fun p hp hx ↦ lowerTriangularTable_eq_of_X_last hp hx
  · exact fun p hp hy ↦ lowerTriangularTable_eq_of_Y_last hp hy

/-- **AVW Theorem 7.5, step 1'**: the strict inequality `Ī(T_q^lower) < q` that AVW's proof of
Theorem 7.5 quotes from Corollary 5.1. -/
theorem asymptoticIndependenceNumber_lowerTriangularTable_lt {q : ℕ} (hq : 2 ≤ q) :
    asymptoticIndependenceNumber (lowerTriangularTable K q) < (q : ℝ) :=
  lt_of_le_of_lt (asymptoticIndependenceNumber_lowerTriangularTable_le_cornerBound hq)
    (cornerBound_lt hq)

end Corner

/-! ## Conciseness of `T_q^lower` in coordinates

Conciseness enters AVW Theorem 4.1 exactly once, to give `|X| ≤ R̃(T)`.  For `T_q^lower` every
standard basis vector is literally a slice: on the `X` leg, fixing `(y_0, z_g)` leaves the
indicator of `x = g`, and symmetrically on the other two legs. -/

section Concise

variable {K : Type u} [Field K]

/-- The triple of indices realizing the standard basis vector at `g` as a slice of `T_q^lower` in
the direction of leg `i`: fill the two remaining legs so that the support equation `i + j = k`
reads `x = g`. -/
private def ltSliceWitness {q : ℕ} (i : Leg) (g : Fin q) : ∀ j, LowerTriangularIndex q j :=
  match i with
  | .X => fun j ↦ match j with | .X => g | .Y => ⟨0, g.pos⟩ | .Z => g
  | .Y => fun j ↦ match j with | .X => ⟨0, g.pos⟩ | .Y => g | .Z => g
  | .Z => fun j ↦ match j with | .X => g | .Y => ⟨0, g.pos⟩ | .Z => g

/-- **`T_q^lower` is concise in coordinates on every leg.**

Proof sketch: the slice through `ltSliceWitness i g` is the indicator of `x = g`, i.e. the standard
basis vector at `g`; as `g` ranges over the leg these span the whole leg space.  For `q = 0` the
leg space is trivial and there is nothing to prove. -/
theorem isCoordinateConcise_lowerTriangularTable (q : ℕ) (i : Leg) :
    IsCoordinateConcise (lowerTriangularTable K q) i := by
  classical
  refine le_antisymm le_top ?_
  rw [← (Pi.basisFun K (Fin q)).span_eq]
  refine Submodule.span_mono ?_
  rintro _ ⟨g, rfl⟩
  rw [Pi.basisFun_apply]
  refine ⟨ltSliceWitness i g, ?_⟩
  funext x
  rw [Pi.single_apply, coordinateSlice, lowerTriangularTable]
  refine if_congr ?_ rfl rfl
  cases i with
  | X =>
      have h1 : Function.update (ltSliceWitness (q := q) .X g) .X x .X = x := by simp
      have h2 : Function.update (ltSliceWitness (q := q) .X g) .X x .Y = ⟨0, g.pos⟩ := by
        rw [Function.update_of_ne (by decide)]; rfl
      have h3 : Function.update (ltSliceWitness (q := q) .X g) .X x .Z = g := by
        rw [Function.update_of_ne (by decide)]; rfl
      rw [h1, h2, h3]
      exact ⟨fun h ↦ Fin.ext (by simpa using h), fun h ↦ by simp [h]⟩
  | Y =>
      have h1 : Function.update (ltSliceWitness (q := q) .Y g) .Y x .X = ⟨0, g.pos⟩ := by
        rw [Function.update_of_ne (by decide)]; rfl
      have h2 : Function.update (ltSliceWitness (q := q) .Y g) .Y x .Y = x := by simp
      have h3 : Function.update (ltSliceWitness (q := q) .Y g) .Y x .Z = g := by
        rw [Function.update_of_ne (by decide)]; rfl
      rw [h1, h2, h3]
      exact ⟨fun h ↦ Fin.ext (by simpa using h), fun h ↦ by simp [h]⟩
  | Z =>
      have h1 : Function.update (ltSliceWitness (q := q) .Z g) .Z x .X = g := by
        rw [Function.update_of_ne (by decide)]; rfl
      have h2 : Function.update (ltSliceWitness (q := q) .Z g) .Z x .Y = ⟨0, g.pos⟩ := by
        rw [Function.update_of_ne (by decide)]; rfl
      have h3 : Function.update (ltSliceWitness (q := q) .Z g) .Z x .Z = x := by simp
      rw [h1, h2, h3]
      exact ⟨fun h ↦ (Fin.ext (by simpa using h.symm)), fun h ↦ by simp [h]⟩

/-- **`q ≤ R̃(T_q^lower)`**: the leg dimensions of a coordinate-concise table are bounded by its
asymptotic rank (`Tensor.card_le_asymptoticRank`).  This is the single use of conciseness in AVW
Theorem 4.1. -/
theorem card_le_asymptoticRank_lowerTriangularTable (q : ℕ) :
    (q : ℝ) ≤ Tensor.asymptoticRank (coordinateTensor (lowerTriangularTable K q)) := by
  have h := Tensor.card_le_asymptoticRank
    (isCoordinateConcise_lowerTriangularTable (K := K) q Leg.X)
  simpa using h

end Concise

/-! ## A galactic certificate for `T_q^lower`

`coordinateGalacticExponent` is an infimum over the certificate value set, so AVW Corollary 4.3
carries the side condition that this set is nonempty.  It is discharged here by an explicit
certificate with data `(n, a, b, c, F) = (1, 1, 1, q, 1)`: zero out the `X` leg to `x_0`, and the
surviving terms are

```text
x_0 y_j z_j,   j = 0, …, q-1,
```

one copy of `⟨1,1,q⟩` after the identification `y_j ↦ z_j`.  That is exactly the shape packaged by
`AlgebraicComplexity.coordinateGalacticCertificate_of_pivot_bijection`, so the only thing to check
here is the support condition: with `i = 0` the defining relation `i + j = k` reads `j = k`. -/

section Certificate

variable {K : Type u} [CommSemiring K]

/-- **A coordinate galactic certificate for `T_q^lower`** with data `(n,a,b,c,F) = (1,1,1,q,1)`.

Proof sketch: this is the pivot-bijection certificate
`AlgebraicComplexity.coordinateGalacticCertificate_of_pivot_bijection` with pivot `x_0`, all `q`
`y`-variables and all `q` `z`-variables retained, and the identity as the matching bijection: with
`i = 0` the support condition `i + j = k` reads `j = k`, and the surviving terms
`x_0 y_j z_j` are one copy of `⟨1,1,q⟩`. -/
theorem coordinateGalacticCertificate_lowerTriangularTable (q : ℕ) [NeZero q] :
    CoordinateGalacticCertificate K (lowerTriangularTable K q) 1 1 1 q 1 := by
  classical
  have h : CoordinateGalacticCertificate K (lowerTriangularTable K q) 1 1 1
      (Finset.univ : Finset (Fin q)).card 1 := by
    refine coordinateGalacticCertificate_of_pivot_bijection K
      (T := lowerTriangularTable K q)
      (fun i ↦ match i with
        | .X => ({0} : Finset (Fin q))
        | .Y => (Finset.univ : Finset (Fin q))
        | .Z => (Finset.univ : Finset (Fin q)))
      0 rfl ⟨0, Finset.mem_univ _⟩ (Equiv.refl _) ?_
    intro y _ z _
    rw [lowerTriangularTable_apply]
    show (if ((0 : Fin q) : ℕ) + (y : ℕ) = (z : ℕ) then (1 : K) else 0) = _
    simp [Fin.val_eq_val, eq_comm]
  rwa [Finset.card_fin] at h

end Certificate

section CertificateField

variable {K : Type u} [Field K]

/-- For `q ≥ 2` the certificate value set of `T_q^lower` is nonempty, so its coordinate galactic
exponent is a genuine infimum and AVW Theorem 7.5 carries no side condition. -/
theorem coordinateGalacticValues_lowerTriangularTable_nonempty {q : ℕ} (hq : 2 ≤ q) :
    (coordinateGalacticValues K (lowerTriangularTable K q)).Nonempty := by
  haveI : NeZero q := ⟨by omega⟩
  exact ⟨_, ⟨1, 1, 1, q, 1, coordinateGalacticCertificate_lowerTriangularTable q,
    by simpa using hq, le_rfl, rfl⟩⟩

end CertificateField

/-! ## AVW Theorem 7.5 -/

section Barrier

variable {K : Type u} [Field K]

/-- **AVW Theorem 7.5, step 2**: the Corollary-4.3 shape `Ī(T) ≤ R̃(T)^s` with the explicit
exponent `s = 1 - cornerExponent q < 1`.  This is the generic first step of the corner chain,
`AlgebraicComplexity.asymptoticIndependenceNumber_le_rpow_asymptoticRank_of_le_cornerBound`, fed by
`asymptoticIndependenceNumber_lowerTriangularTable_le_cornerBound` and the conciseness bound
`q ≤ R̃(T_q^lower)` (`card_le_asymptoticRank_lowerTriangularTable`). -/
theorem asymptoticIndependenceNumber_lowerTriangularTable_le_rpow_asymptoticRank
    {q : ℕ} (hq : 2 ≤ q) :
    asymptoticIndependenceNumber (lowerTriangularTable K q) ≤
      Tensor.asymptoticRank (coordinateTensor (lowerTriangularTable K q)) ^
        (1 - cornerExponent q) :=
  asymptoticIndependenceNumber_le_rpow_asymptoticRank_of_le_cornerBound hq
    (card_le_asymptoticRank_lowerTriangularTable (K := K) q)
    (asymptoticIndependenceNumber_lowerTriangularTable_le_cornerBound hq)

/-- **AVW Theorem 7.5**, with an explicit constant: for every integer `q ≥ 2`, the Galactic method
applied to the lower triangular tensor `T_q^lower` in its own variables cannot prove any exponent
bound below

```text
c_q = 6 / (3 − cornerExponent q),     cornerExponent q = 1/(q² (q+1)² log q).
```

AVW leave `c_q` unnamed; this is the explicit form the repository's Corollary 5.1 yields, with
their own printed exponent gap `1/(q²(q+1)² log q)`; see the module header.

Proof sketch: AVW Corollary 5.1 gives `Ī(T_q^lower) ≤ cornerBound q`
(`asymptoticIndependenceNumber_lowerTriangularTable_le_cornerBound`), and the packaged corner
chain `AlgebraicComplexity.six_div_sub_cornerExponent_le_coordinateGalacticExponent_of_concise`
(`MatrixMultiplication/CornerBarrier.lean`) turns it into the exponent bound.  The nonemptiness
side condition is supplied by `coordinateGalacticValues_lowerTriangularTable_nonempty`. -/
theorem six_div_le_coordinateGalacticExponent_lowerTriangularTable {q : ℕ} (hq : 2 ≤ q) :
    6 / (3 - cornerExponent q) ≤
      coordinateGalacticExponent K (lowerTriangularTable K q) := by
  haveI : NeZero q := ⟨by omega⟩
  haveI : ∀ i, Nonempty (LowerTriangularIndex q i) := fun _ ↦ ⟨(0 : Fin q)⟩
  exact six_div_sub_cornerExponent_le_coordinateGalacticExponent_of_concise K hq
    (fun i ↦ isCoordinateConcise_lowerTriangularTable q i)
    (card_le_asymptoticRank_lowerTriangularTable (K := K) q)
    (asymptoticIndependenceNumber_lowerTriangularTable_le_cornerBound hq)
    (coordinateGalacticValues_lowerTriangularTable_nonempty hq)

/-- **AVW Theorem 7.5**, in the printed form: for each integer `q ≥ 2` there is a constant
`c_q > 2` with `ω_g^{coord}(T_q^lower) ≥ c_q`.  The constant is the explicit
`6/(3 − cornerExponent q)` of
`six_div_le_coordinateGalacticExponent_lowerTriangularTable`.

Per the module header the conclusion is about the **coordinate** galactic exponent, which is the
quantity AVW Theorem 4.1 actually bounds; no claim is made about the basis-free
`galacticExponent`. -/
theorem avw_theorem_seven_five (K : Type u) [Field K] {q : ℕ} (hq : 2 ≤ q) :
    ∃ c : ℝ, 2 < c ∧ c ≤ coordinateGalacticExponent K (lowerTriangularTable K q) := by
  exact ⟨6 / (3 - cornerExponent q), two_lt_six_div_sub_cornerExponent hq,
    six_div_le_coordinateGalacticExponent_lowerTriangularTable hq⟩

/-- **AVW Theorem 7.5**, final form: the Galactic method applied to `T_q^lower` in its own
variables cannot prove `ω = 2`. -/
theorem two_lt_coordinateGalacticExponent_lowerTriangularTable {q : ℕ} (hq : 2 ≤ q) :
    2 < coordinateGalacticExponent K (lowerTriangularTable K q) := by
  obtain ⟨c, hc, hle⟩ := avw_theorem_seven_five K hq
  linarith

end Barrier

/-! ## A tiny client

`DESIGN.md` asks every semantic step to have a deliberately small regression client.  The smallest
lower triangular tensor with the corner configuration is `q = 2`:

```text
T_2^lower = x_0 y_0 z_0 + x_0 y_1 z_1 + x_1 y_0 z_1,
```

whose corner terms are `x_1 y_0 z_1` and `x_0 y_1 z_1`.  Its two extreme variables `x_1` and `y_1`
each occur in exactly one term, and those two terms share `z_1`, so it is an instance of AVW
Corollary 5.1 with the same constant `c_2 = 2^{1 - 1/(72 log 2)}` as
`asymptoticIndependenceNumber_twoCornerTable_le`. -/

section Tiny

/-- **Regression test for AVW Theorem 7.5** at `q = 2`: `Ī(T_2^lower) < 2`, even though
`T_2^lower` has two variables on each leg. -/
theorem asymptoticIndependenceNumber_lowerTriangularTable_two_lt :
    asymptoticIndependenceNumber (lowerTriangularTable ℚ 2) < 2 := by
  have h := asymptoticIndependenceNumber_lowerTriangularTable_lt (K := ℚ) (q := 2) le_rfl
  norm_num at h
  exact h

/-- The support of `T_2^lower` is `{x_0y_0z_0, x_0y_1z_1, x_1y_0z_1}`: three terms, not four, and
in particular the "missing" term is `x_1 y_1 z_?`, which is what makes `x_1` and `y_1` corner
variables. -/
theorem lowerTriangularTable_two_support (p : ∀ i, LowerTriangularIndex 2 i) :
    lowerTriangularTable ℚ 2 p ≠ 0 ↔ (p .X : ℕ) + (p .Y : ℕ) = (p .Z : ℕ) :=
  lowerTriangularTable_ne_zero_iff 2 p

end Tiny

end AlgebraicComplexity.Examples
