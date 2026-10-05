/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Tensor.GroupCoefficients
import AlgebraicComplexity.MatrixMultiplication.IndependenceBarrier

/-!
# Group tensors and the tri-coloured sum-free barrier (AVW Section 6)

This file is milestone **L** of `BARRIER_FRAMEWORK.md`.  It connects the structural tensor `T_G`
of a finite group algebra (`Tensor/GroupTensor.lean`) with the independence-number barrier
(`MatrixMultiplication/IndependenceBarrier.lean`), following

> J. Alman and V. Vassilevska Williams, *Limits on All Known (and Some Unknown) Approaches to
> Matrix Multiplication*, arXiv:1810.08671v1, **Definition 3.3**, **Theorem 3.2**, **Lemma 6.1**,
> **Corollary 6.1** and **Theorem 6.1**.

## The convention for `T_G`

`Tensor/GroupTensor.lean` takes the *symmetric* presentation of the structural tensor of `K[G]` as
primary,

```text
T_G = ∑_{g,h ∈ G} x_g ⊗ y_h ⊗ z_{(g·h)⁻¹},   support  {(a, b, c) | a · b · c = 1},
```

because that support condition is cyclically invariant even for a nonabelian group.  This file
follows the same convention throughout: `groupCoefficients K G` is the coefficient table of
`groupTensor K G` (`coordinateTensor_groupCoefficients`), and tri-coloured sum-free sets are
therefore defined by the symmetric equation `a · b · c = 1` rather than AVW's `a · b = c`.  The
bridge to the multiplicative presentation is already available upstream and is cheap:
`Tensor.groupTensor_isomorphic_groupTensorMul` relabels the `Z` leg by inversion, and
`triColoredSumFree_iff_mulForm` below records the corresponding bijection
`(a, b, c) ↦ (a, b, c⁻¹)` on triples, so a reader who prefers AVW's printed form may translate
every statement here mechanically.  Nothing in the mathematics depends on the choice.

## Main definitions

* `Tensor.groupCoefficients K G`: the coefficient table of `T_G`, the indicator of
  `a · b · c = 1`; it and the two identifications below live in `Tensor/GroupCoefficients.lean`.
* `TriColoredSumFree G S` (**AVW Definition 3.3**): a finite set `S` of triples of `G` with
  `a · b · c = 1` on `S` and such that a *mixed* product `aᵢ · bⱼ · cₖ` equals `1` only when the
  three triples coincide.
* `triColoredSumFreeNumber G`: the largest size of a tri-coloured sum-free set in `G`.
* `SawinBound G` (**AVW Theorem 3.2**): the named proof obligation transcribing Sawin's theorem.

## Main results

* `coordinatePower_groupCoefficients`: `T_G^{⊗n} = T_{Gⁿ}` **on the nose**.  The variables of the
  `n`-th Kronecker power of `T_G` are words `Fin n → G`, which are exactly the elements of the
  product group `Gⁿ`, and the two coefficient tables are literally the same function.  This is the
  "group-power identification" that makes the passage from `G` to `Gⁿ` free of relabelling.
* `triColoredSumFree_of_independentSet` and `independentSet_of_triColoredSumFree`
  (**AVW Lemma 6.1**, both directions): the independent sets of terms of the table `T_G` are
  precisely the tri-coloured sum-free sets of `G`.  The forward direction is exactly
  `Tensor.IndependentSet.mix_eq`, the abstract form of the closure clause.
* `independenceNumber_groupCoefficients`: `I(T_G) = triColoredSumFreeNumber G`, and
  `independenceNumber_coordinatePower_groupCoefficients`:
  `I(T_G^{⊗n}) = triColoredSumFreeNumber Gⁿ`.  AVW state these as inequalities `≤`; the equality
  holds and is proved.
* `triColoredSumFreeNumber_pow_le`: the product structure, `f(G)^n ≤ f(Gⁿ)`.
* `isCoordinateConcise_groupCoefficients` and `card_le_asymptoticRank_groupCoefficients`:
  `T_G` is concise in coordinates on all three legs (Latin-square slices), hence `|G| ≤ R̃(T_G)`.
* `coordinateGalacticCertificate_groupCoefficients`: for `|G| ≥ 2` the table `T_G` admits the
  coordinate galactic certificate `(n,a,b,c,F) = (1, 1, 1, |G|, 1)` — zero out the `X` leg to the
  identity and the surviving terms `x₁ y_g z_{g⁻¹}` are one copy of `⟨1,1,|G|⟩`.  This makes the
  certificate value set nonempty, so `ω_g^{coord}(T_G)` is a genuine infimum and the barrier
  theorem below needs no extra hypothesis.
* `asymptoticIndependenceNumber_groupCoefficients_le_of_sawinBound` (**AVW Corollary 6.1**) and
  `two_lt_coordinateGalacticExponent_groupCoefficients_of_sawinBound` (**AVW Theorem 6.1**):
  conditionally on `SawinBound G`, `Ī(T_G) ≤ δ·|G|` for some `δ < 1`, and consequently
  `ω_g^{coord}(T_G) > 2`.

## The status of Sawin's theorem

`SawinBound G` is a **named proof obligation** in the sense of `DESIGN.md`: a `Prop` definition,
never an `axiom`, never a typeclass instance, and never reported as proved.  **No Lean proof of it
exists in this repository and none is claimed.**  It transcribes AVW Theorem 3.2 (Sawin, building
on Croot–Lev–Pach, Ellenberg–Gijswijt and Kleinberg–Sawin–Speyer): for a finite group `G` there is
a `δ < 1` such that every tri-coloured sum-free set in `Gⁿ` has size at most `(δ|G|)^n`.  It
appears as an explicit hypothesis of every theorem below that uses it.

Two honesty notes about the transcription.

* The obligation is **false for the trivial group** (`not_sawinBound_of_card_le_one`): the single
  triple `(1,1,1)` is tri-coloured sum-free in `Gⁿ` and has size `1 = |G|^n`, which no `δ < 1`
  can dominate.  This is not a defect of the transcription but of the unqualified reading of the
  source statement; `two_le_card_of_sawinBound` records that the obligation already carries
  `|G| ≥ 2` with it, which is the range in which AVW use it.
* The existential is stated with the single constraint `δ < 1`, without a companion `0 < δ`.  That
  is the weaker — hence the more usable — hypothesis, and positivity is recovered for free:
  applying the bound to the singleton `{(1,1,1)}` gives `1 ≤ δ|G|`.

## What is proved unconditionally

Everything except the two `SawinBound`-hypothesised statements: the whole of the Lemma 6.1
correspondence, the group-power identification, the tri-coloured API, conciseness of `T_G` in
coordinates, the bound `|G| ≤ R̃(T_G)`, and the galactic certificate that makes the exponent
well-defined.  In particular the support-combinatorial part is field-free — it needs only a
commutative semiring, and `Nontrivial` only where a coefficient must be seen to be nonzero.

## Which exponent the conclusion is about

Per the milestone-F correction recorded in `MatrixMultiplication/IndependenceBarrier.lean`, the
independence number is basis-dependent, so AVW's Theorem 4.1 bounds the **coordinate** galactic
exponent `coordinateGalacticExponent`, the infimum over monomial degenerations read *in the
variables of `T_G`*.  Theorem 6.1 is therefore stated for `coordinateGalacticExponent`.  The
abstract `galacticExponent` satisfies `galacticExponent ≤ coordinateGalacticExponent`, which is the
wrong direction to transport a lower bound, so **no claim is made about the abstract exponent**.

## Layer placement

This is a layer-4 client (`AlgebraicComplexity/Examples/`).  It imports the group tensor from the
tensor layer and the barrier from the matrix-multiplication layer, and introduces no new
independence, measure, or barrier notion: the tri-coloured sum-free set is the only new definition
with mathematical content, and it is a statement about groups, not about tensors.

## Non-goals

AVW Lemmas 6.2 and 6.3 and Theorem 6.2 (`CW_q` is not a sub-tensor of a small `T_G`) are
independent of Sawin's theorem and live in `Examples/CoppersmithWinogradGroupExclusion.lean`.
The monomial degeneration of `T_G` onto a generalized Coppersmith--Winograd tensor (AVW
Theorem 7.2) is milestone **M** and is not attempted here.
-/

namespace AlgebraicComplexity.Examples

open Tensor

universe u v

/-! ## Tri-coloured sum-free sets (AVW Definition 3.3)

A tri-coloured sum-free set is a finite family of triples `(aᵢ, bᵢ, cᵢ)` of group elements with
`aᵢ · bᵢ · cᵢ = 1`, such that a *mixed* product `aᵢ · bⱼ · cₖ` equals `1` only for `i = j = k`.
Presenting the family as a `Finset` of triples rather than as an indexed list loses nothing: the
mixing condition forces the three coordinate projections to be injective on the family
(`TriColoredSumFree.eq_of_fst_eq` and its two companions), so a repeated index would already
violate it.

The convention is the symmetric one, `a · b · c = 1`; see the module header. -/

section TriColored

variable {G : Type v} [Group G]

/-- **A tri-coloured sum-free set** in a group `G` (Alman--Vassilevska Williams,
arXiv:1810.08671, Definition 3.3, in the symmetric convention): a finite set `S` of triples whose
own products are `1`, and for which a product mixing the first coordinate of one member, the
second of another and the third of a third is `1` only when all three members coincide. -/
structure TriColoredSumFree (G : Type v) [Group G] (S : Finset (G × G × G)) : Prop where
  /-- Every member triple multiplies to the identity. -/
  mul_eq_one : ∀ t ∈ S, t.1 * t.2.1 * t.2.2 = 1
  /-- A mixed product equal to the identity forces the three members to coincide. -/
  eq_of_mul_eq_one : ∀ t₁ ∈ S, ∀ t₂ ∈ S, ∀ t₃ ∈ S,
    t₁.1 * t₂.2.1 * t₃.2.2 = 1 → t₁ = t₂ ∧ t₁ = t₃

namespace TriColoredSumFree

variable {S : Finset (G × G × G)}

/-- Two members of a tri-coloured sum-free set with the same first coordinate are equal: mix the
first coordinate of one with the last two coordinates of the other. -/
theorem eq_of_fst_eq (h : TriColoredSumFree G S) {t u : G × G × G} (ht : t ∈ S) (hu : u ∈ S)
    (hfst : t.1 = u.1) : t = u :=
  (h.eq_of_mul_eq_one t ht u hu u hu (by rw [hfst]; exact h.mul_eq_one u hu)).1

/-- Two members with the same second coordinate are equal. -/
theorem eq_of_snd_eq (h : TriColoredSumFree G S) {t u : G × G × G} (ht : t ∈ S) (hu : u ∈ S)
    (hsnd : t.2.1 = u.2.1) : t = u :=
  ((h.eq_of_mul_eq_one u hu t ht u hu (by rw [hsnd]; exact h.mul_eq_one u hu)).1).symm

/-- Two members with the same third coordinate are equal. -/
theorem eq_of_thd_eq (h : TriColoredSumFree G S) {t u : G × G × G} (ht : t ∈ S) (hu : u ∈ S)
    (hthd : t.2.2 = u.2.2) : t = u :=
  ((h.eq_of_mul_eq_one u hu u hu t ht (by rw [hthd]; exact h.mul_eq_one u hu)).2).symm

/-- The first-coordinate projection is injective on a tri-coloured sum-free set. -/
theorem injOn_fst (h : TriColoredSumFree G S) :
    Set.InjOn Prod.fst (S : Set (G × G × G)) :=
  fun _ ht _ hu hfst ↦ h.eq_of_fst_eq ht hu hfst

/-- **A tri-coloured sum-free set has at most `|G|` elements**, since its first coordinates are
pairwise distinct. -/
theorem card_le_card [Fintype G] (h : TriColoredSumFree G S) : S.card ≤ Fintype.card G := by
  have hcard : S.card ≤ (Finset.univ : Finset G).card :=
    Finset.card_le_card_of_injOn Prod.fst (fun _ _ ↦ Finset.mem_univ _) h.injOn_fst
  simpa using hcard

end TriColoredSumFree

/-- The singleton `{(1,1,1)}` is tri-coloured sum-free in every group: its only mixed product is
its own product. -/
theorem triColoredSumFree_singleton_one :
    TriColoredSumFree G ({(1, 1, 1)} : Finset (G × G × G)) where
  mul_eq_one t ht := by
    rw [Finset.mem_singleton] at ht
    subst ht
    simp
  eq_of_mul_eq_one t₁ h₁ t₂ h₂ t₃ h₃ _ := by
    rw [Finset.mem_singleton] at h₁ h₂ h₃
    exact ⟨by rw [h₁, h₂], by rw [h₁, h₃]⟩

/-- The set of cardinalities of tri-coloured sum-free sets of `G`. -/
def triColoredSumFreeCards (G : Type v) [Group G] : Set ℕ :=
  {n | ∃ S : Finset (G × G × G), TriColoredSumFree G S ∧ S.card = n}

/-- `0` is the cardinality of a tri-coloured sum-free set, namely the empty one. -/
theorem zero_mem_triColoredSumFreeCards : 0 ∈ triColoredSumFreeCards G :=
  ⟨∅, ⟨fun t ht ↦ absurd ht (Finset.notMem_empty t),
    fun t ht ↦ absurd ht (Finset.notMem_empty t)⟩, rfl⟩

variable [Fintype G]

/-- Cardinalities of tri-coloured sum-free sets are bounded by `|G|`. -/
theorem bddAbove_triColoredSumFreeCards : BddAbove (triColoredSumFreeCards G) := by
  refine ⟨Fintype.card G, ?_⟩
  rintro n ⟨S, hS, rfl⟩
  exact hS.card_le_card

/-- **The tri-coloured sum-free number of `G`**: the largest size of a tri-coloured sum-free set
in `G`.  This is the quantity Sawin's theorem bounds, and by `independenceNumber_groupCoefficients`
it is exactly the independence number of the table of `T_G`. -/
noncomputable def triColoredSumFreeNumber (G : Type v) [Group G] [Fintype G] : ℕ :=
  sSup (triColoredSumFreeCards G)

/-- Every tri-coloured sum-free set is at most as large as the tri-coloured sum-free number. -/
theorem TriColoredSumFree.card_le_triColoredSumFreeNumber {S : Finset (G × G × G)}
    (h : TriColoredSumFree G S) : S.card ≤ triColoredSumFreeNumber G :=
  le_csSup bddAbove_triColoredSumFreeCards ⟨S, h, rfl⟩

/-- The tri-coloured sum-free number is attained by an explicit tri-coloured sum-free set. -/
theorem exists_triColoredSumFree_card_eq :
    ∃ S : Finset (G × G × G), TriColoredSumFree G S ∧ S.card = triColoredSumFreeNumber G :=
  Nat.sSup_mem ⟨0, zero_mem_triColoredSumFreeCards⟩ bddAbove_triColoredSumFreeCards

/-- A bound valid for every tri-coloured sum-free set bounds the tri-coloured sum-free number. -/
theorem triColoredSumFreeNumber_le {n : ℕ}
    (h : ∀ S : Finset (G × G × G), TriColoredSumFree G S → S.card ≤ n) :
    triColoredSumFreeNumber G ≤ n := by
  refine csSup_le ⟨0, zero_mem_triColoredSumFreeCards⟩ ?_
  rintro m ⟨S, hS, rfl⟩
  exact h S hS

/-- `f(G) ≤ |G|`. -/
theorem triColoredSumFreeNumber_le_card : triColoredSumFreeNumber G ≤ Fintype.card G :=
  triColoredSumFreeNumber_le fun _ hS ↦ hS.card_le_card

/-- `1 ≤ f(G)`, witnessed by `{(1,1,1)}`. -/
theorem one_le_triColoredSumFreeNumber : 1 ≤ triColoredSumFreeNumber G := by
  classical
  have h := (triColoredSumFree_singleton_one (G := G)).card_le_triColoredSumFreeNumber
  simpa using h

end TriColored

/-! ## AVW Lemma 6.1

> An independent set of terms of the table of `T_G` is exactly a tri-coloured sum-free set of `G`.

AVW state one direction, and only as an inequality on the numbers.  Both directions hold and are
proved: the three clauses of `Tensor.IndependentSet` and the two clauses of `TriColoredSumFree`
are the same conditions read through the support characterisation
`groupCoefficients_ne_zero_iff`.  Concretely, `Tensor.IndependentSet.mix_eq` — the abstract
consequence of the closure clause isolated in `Tensor/IndependenceNumber.lean` precisely for this
purpose — *is* the mixing clause of Definition 3.3. -/

section LemmaSixOne

variable {K : Type u} [CommSemiring K] [Nontrivial K]
variable {G : Type v} [Group G] [Fintype G] [DecidableEq G]

/-- The bijection between triples indexed by the three legs and ordinary ordered triples. -/
def legTripleEquiv (G : Type v) : (∀ _ : Leg, G) ≃ G × G × G where
  toFun t := (t .X, t .Y, t .Z)
  invFun s := fun i ↦ match i with
    | .X => s.1
    | .Y => s.2.1
    | .Z => s.2.2
  left_inv t := by funext i; cases i <;> rfl
  right_inv s := rfl

omit [Group G] [Fintype G] [DecidableEq G] in
@[simp] theorem legTripleEquiv_apply (t : ∀ _ : Leg, G) :
    legTripleEquiv G t = (t .X, t .Y, t .Z) := rfl

omit [Group G] [Fintype G] [DecidableEq G] in
@[simp] theorem legTripleEquiv_symm_apply_X (s : G × G × G) :
    (legTripleEquiv G).symm s .X = s.1 := rfl

omit [Group G] [Fintype G] [DecidableEq G] in
@[simp] theorem legTripleEquiv_symm_apply_Y (s : G × G × G) :
    (legTripleEquiv G).symm s .Y = s.2.1 := rfl

omit [Group G] [Fintype G] [DecidableEq G] in
@[simp] theorem legTripleEquiv_symm_apply_Z (s : G × G × G) :
    (legTripleEquiv G).symm s .Z = s.2.2 := rfl

omit [Fintype G] in
/-- **AVW Lemma 6.1, forward direction.**  An independent set of terms of the table of `T_G` is a
tri-coloured sum-free set of `G`.

Proof sketch: membership in the support is the equation `a · b · c = 1`
(`groupCoefficients_ne_zero_iff`), which is the first clause.  For the second, three members of
the independent set assemble into a leg-indexed selection whose mixed triple is in the support
exactly when the mixed product is `1`; `Tensor.IndependentSet.mix_eq`, the abstract form of the
closure clause, then identifies the three members. -/
theorem triColoredSumFree_of_independentSet {S : Finset (∀ i, GroupIndex G i)}
    (h : IndependentSet (groupCoefficients K G) S) :
    TriColoredSumFree G (S.image (legTripleEquiv G)) where
  mul_eq_one t ht := by
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp ht
    exact (groupCoefficients_ne_zero_iff (K := K) p).mp (h.ne_zero p hp)
  eq_of_mul_eq_one t₁ h₁ t₂ h₂ t₃ h₃ hmix := by
    obtain ⟨p₁, hp₁, rfl⟩ := Finset.mem_image.mp h₁
    obtain ⟨p₂, hp₂, rfl⟩ := Finset.mem_image.mp h₂
    obtain ⟨p₃, hp₃, rfl⟩ := Finset.mem_image.mp h₃
    set sel : Leg → (∀ i, GroupIndex G i) := fun i ↦ match i with
      | .X => p₁
      | .Y => p₂
      | .Z => p₃ with hsel
    have hmem : ∀ i, sel i ∈ S := by
      intro i; cases i <;> assumption
    have hne : groupCoefficients K G (fun i ↦ sel i i) ≠ 0 := by
      refine (groupCoefficients_ne_zero_iff (K := K) _).mpr ?_
      simpa [hsel] using hmix
    have hall := h.mix_eq sel hmem hne
    exact ⟨by rw [show p₁ = p₂ from hall .X .Y], by rw [show p₁ = p₃ from hall .X .Z]⟩

omit [Fintype G] in
/-- **AVW Lemma 6.1, converse direction.**  A tri-coloured sum-free set of `G` is an independent
set of terms of the table of `T_G`.

Proof sketch: the first clause of `Tensor.IndependentSet` is again the support characterisation.
Injectivity of the three leg projections is the mixing clause applied with two of the three
members repeated (`TriColoredSumFree.eq_of_fst_eq` and its companions), and closure is the mixing
clause applied to the three members that supply the three coordinates of a competing support
triple. -/
theorem independentSet_of_triColoredSumFree {S : Finset (G × G × G)}
    (h : TriColoredSumFree G S) :
    IndependentSet (groupCoefficients K G) (S.image (legTripleEquiv G).symm) where
  ne_zero p hp := by
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hp
    refine (groupCoefficients_ne_zero_iff (K := K) _).mpr ?_
    simpa using h.mul_eq_one t ht
  distinct p hp q hq i hpq := by
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hq
    have htu : t = u := by
      cases i with
      | X => exact h.eq_of_fst_eq ht hu (by simpa using hpq)
      | Y => exact h.eq_of_snd_eq ht hu (by simpa using hpq)
      | Z => exact h.eq_of_thd_eq ht hu (by simpa using hpq)
    rw [htu]
  closed p hp hbox := by
    obtain ⟨qX, hqX, hqXeq⟩ := hbox .X
    obtain ⟨qY, hqY, hqYeq⟩ := hbox .Y
    obtain ⟨qZ, hqZ, hqZeq⟩ := hbox .Z
    obtain ⟨tX, htX, rfl⟩ := Finset.mem_image.mp hqX
    obtain ⟨tY, htY, rfl⟩ := Finset.mem_image.mp hqY
    obtain ⟨tZ, htZ, rfl⟩ := Finset.mem_image.mp hqZ
    have hcompat : p .X * p .Y * p .Z = 1 :=
      (groupCoefficients_ne_zero_iff (K := K) p).mp hp
    have hmix : tX.1 * tY.2.1 * tZ.2.2 = 1 := by
      rw [show tX.1 = p .X from by simpa using hqXeq,
        show tY.2.1 = p .Y from by simpa using hqYeq,
        show tZ.2.2 = p .Z from by simpa using hqZeq]
      exact hcompat
    obtain ⟨hXY, hXZ⟩ := h.eq_of_mul_eq_one tX htX tY htY tZ htZ hmix
    refine Finset.mem_image.mpr ⟨tX, htX, ?_⟩
    funext i
    cases i with
    | X => simpa using hqXeq
    | Y => rw [hXY]; simpa using hqYeq
    | Z => rw [hXZ]; simpa using hqZeq

/-- **AVW Lemma 6.1, as an identity of numbers**: the independence number of the table of `T_G` is
the tri-coloured sum-free number of `G`.  AVW state only `≤`. -/
theorem independenceNumber_groupCoefficients :
    independenceNumber (groupCoefficients K G) = triColoredSumFreeNumber G := by
  classical
  refine le_antisymm (independenceNumber_le fun S hS ↦ ?_) (triColoredSumFreeNumber_le ?_)
  · have hcard := (triColoredSumFree_of_independentSet (K := K)
      hS).card_le_triColoredSumFreeNumber
    rwa [Finset.card_image_of_injective _ (legTripleEquiv G).injective] at hcard
  · intro S hS
    have hcard := (independentSet_of_triColoredSumFree (K := K) hS).card_le_independenceNumber
    rwa [Finset.card_image_of_injective _ (legTripleEquiv G).symm.injective] at hcard

/-- **AVW Lemma 6.1 for the Kronecker powers**: `I(T_G^{⊗n})` is the tri-coloured sum-free number
of the product group `Gⁿ`.  This is where the group-power identification
`coordinatePower_groupCoefficients` earns its keep — there is nothing to relabel. -/
theorem independenceNumber_coordinatePower_groupCoefficients (n : ℕ) :
    independenceNumber (coordinatePower (groupCoefficients K G) n) =
      triColoredSumFreeNumber (Fin n → G) := by
  rw [coordinatePower_groupCoefficients, independenceNumber_groupCoefficients (K := K)]

/-- **The product structure of tri-coloured sum-free sets**: `f(G)^n ≤ f(Gⁿ)`.

Proof sketch: this is supermultiplicativity of the independence number along Kronecker powers
(`Tensor.independenceNumber_coordinatePower_pow_le`), read through Lemma 6.1 in both directions.
The statement is field-free; the proof runs the tensor calculus over `ℚ`, whose only role is to
supply a nontrivial coefficient ring without zero divisors. -/
theorem triColoredSumFreeNumber_pow_le (n : ℕ) :
    triColoredSumFreeNumber G ^ n ≤ triColoredSumFreeNumber (Fin n → G) := by
  have h := independenceNumber_coordinatePower_pow_le (groupCoefficients ℚ G) 1 n
  rw [independenceNumber_coordinatePower_one, one_mul,
    independenceNumber_groupCoefficients (K := ℚ),
    independenceNumber_coordinatePower_groupCoefficients (K := ℚ)] at h
  exact h

end LemmaSixOne

/-! ## The multiplicative presentation

For a reader quoting AVW's printed form `a · b = c` rather than the symmetric `a · b · c = 1`,
the translation is the bijection `(a, b, c) ↦ (a, b, c⁻¹)` of triples.  It is recorded here so
that the choice of convention is on the record rather than folklore; nothing below uses it. -/

section MulForm

variable {G : Type v} [Group G] [DecidableEq G]

/-- Inverting the third coordinate of a triple. -/
def invThdEquiv (G : Type v) [Group G] : G × G × G ≃ G × G × G where
  toFun t := (t.1, t.2.1, t.2.2⁻¹)
  invFun t := (t.1, t.2.1, t.2.2⁻¹)
  left_inv t := by simp
  right_inv t := by simp

omit [DecidableEq G] in
/-- In a group, `a · b · c = 1` is the same equation as `a · b = c⁻¹`.  This is the whole content
of the translation between the two conventions. -/
private theorem mul_three_eq_one_iff (a b c : G) : a * b * c = 1 ↔ a * b = c⁻¹ :=
  mul_eq_one_iff_eq_inv

/-- **The two conventions for tri-coloured sum-free sets agree** up to inverting the third
coordinate: `S` is tri-coloured sum-free for the symmetric equation `a · b · c = 1` if and only if
its image under `(a, b, c) ↦ (a, b, c⁻¹)` satisfies AVW's printed multiplicative equation
`a · b = c`, in the same mixed form. -/
theorem triColoredSumFree_iff_mulForm (S : Finset (G × G × G)) :
    TriColoredSumFree G S ↔
      ((∀ t ∈ S.image (invThdEquiv G), t.1 * t.2.1 = t.2.2) ∧
        ∀ t₁ ∈ S.image (invThdEquiv G), ∀ t₂ ∈ S.image (invThdEquiv G),
          ∀ t₃ ∈ S.image (invThdEquiv G),
            t₁.1 * t₂.2.1 = t₃.2.2 → t₁ = t₂ ∧ t₁ = t₃) := by
  classical
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · rintro t ht
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp ht
      show u.1 * u.2.1 = u.2.2⁻¹
      exact (mul_three_eq_one_iff u.1 u.2.1 u.2.2).mp (h.mul_eq_one u hu)
    · rintro t₁ h₁ t₂ h₂ t₃ h₃ hmix
      obtain ⟨u₁, hu₁, rfl⟩ := Finset.mem_image.mp h₁
      obtain ⟨u₂, hu₂, rfl⟩ := Finset.mem_image.mp h₂
      obtain ⟨u₃, hu₃, rfl⟩ := Finset.mem_image.mp h₃
      have hmix' : u₁.1 * u₂.2.1 = u₃.2.2⁻¹ := hmix
      obtain ⟨e12, e13⟩ := h.eq_of_mul_eq_one u₁ hu₁ u₂ hu₂ u₃ hu₃
        ((mul_three_eq_one_iff u₁.1 u₂.2.1 u₃.2.2).mpr hmix')
      exact ⟨by rw [e12], by rw [e13]⟩
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · intro t ht
      have hmul : t.1 * t.2.1 = t.2.2⁻¹ :=
        h1 (invThdEquiv G t) (Finset.mem_image_of_mem _ ht)
      exact (mul_three_eq_one_iff t.1 t.2.1 t.2.2).mpr hmul
    · intro t₁ h₁ t₂ h₂ t₃ h₃ hmix
      have harg : ((invThdEquiv G) t₁).1 * ((invThdEquiv G) t₂).2.1 = ((invThdEquiv G) t₃).2.2 :=
        (mul_three_eq_one_iff t₁.1 t₂.2.1 t₃.2.2).mp hmix
      have hm := h2 (invThdEquiv G t₁) (Finset.mem_image_of_mem _ h₁)
        (invThdEquiv G t₂) (Finset.mem_image_of_mem _ h₂)
        (invThdEquiv G t₃) (Finset.mem_image_of_mem _ h₃) harg
      exact ⟨(invThdEquiv G).injective hm.1, (invThdEquiv G).injective hm.2⟩

end MulForm

/-! ## Sawin's theorem as a named proof obligation (AVW Theorem 3.2)

See the module header for the policy.  There is no Lean proof of `SawinBound` in this repository
and none is claimed; it is an explicit hypothesis of every theorem that uses it. -/

section Sawin

variable {G : Type v} [Group G] [Fintype G]

/-- **Sawin's theorem, as a named proof obligation** (Alman--Vassilevska Williams,
arXiv:1810.08671, Theorem 3.2, attributed to Sawin building on Croot--Lev--Pach,
Ellenberg--Gijswijt and Kleinberg--Sawin--Speyer):

> for a finite group `G` there is a `δ < 1` such that every tri-coloured sum-free set in the
> product group `Gⁿ` has size at most `(δ·|G|)^n`.

**This is not proved here, and nothing in this file claims that it is.**  It is a `Prop`, never an
`axiom` and never an instance, and it appears as an explicit hypothesis of
`asymptoticIndependenceNumber_groupCoefficients_le_of_sawinBound` and
`two_lt_coordinateGalacticExponent_groupCoefficients_of_sawinBound`.

Two remarks on the transcription are in the module header: the statement is false for the trivial
group (`not_sawinBound_of_card_le_one`), and no positivity constraint on `δ` is imposed because
`1 ≤ δ·|G|` follows from the bound itself (`one_le_of_sawinBound`). -/
def SawinBound (G : Type v) [Group G] [Fintype G] : Prop :=
  ∃ δ : ℝ, δ < 1 ∧ ∀ (n : ℕ) (S : Finset ((Fin n → G) × (Fin n → G) × (Fin n → G))),
    TriColoredSumFree (Fin n → G) S → (S.card : ℝ) ≤ (δ * Fintype.card G) ^ n

/-- The constant of a Sawin bound satisfies `1 ≤ δ·|G|`: apply the bound at `n = 1` to the
tri-coloured sum-free singleton `{(1,1,1)}`. -/
theorem one_le_of_sawinBound {δ : ℝ}
    (h : ∀ (n : ℕ) (S : Finset ((Fin n → G) × (Fin n → G) × (Fin n → G))),
      TriColoredSumFree (Fin n → G) S → (S.card : ℝ) ≤ (δ * Fintype.card G) ^ n) :
    1 ≤ δ * Fintype.card G := by
  classical
  have hs := h 1 ({(1, 1, 1)} : Finset ((Fin 1 → G) × (Fin 1 → G) × (Fin 1 → G)))
    triColoredSumFree_singleton_one
  rw [Finset.card_singleton, pow_one] at hs
  exact_mod_cast hs

/-- A Sawin bound forces `|G| ≥ 2`.  This is the honest content of the observation that AVW's
Theorem 3.2 is stated for groups of size at least two. -/
theorem two_le_card_of_sawinBound (h : SawinBound G) : 2 ≤ Fintype.card G := by
  obtain ⟨δ, hδ, hb⟩ := h
  have h1 : 1 ≤ δ * Fintype.card G := one_le_of_sawinBound hb
  by_contra hcon
  have hcard : Fintype.card G = 1 := by
    have := Fintype.card_pos (α := G)
    omega
  rw [hcard] at h1
  simp only [Nat.cast_one, mul_one] at h1
  exact absurd hδ (not_lt.mpr h1)

/-- **The obligation is false for the trivial group.**  The single triple `(1,1,1)` is
tri-coloured sum-free in `Gⁿ` and has size `1 = |G|^n`, which no `δ < 1` can dominate.  This is
recorded so that no reader mistakes `SawinBound` for a statement about all finite groups. -/
theorem not_sawinBound_of_card_le_one (h : Fintype.card G ≤ 1) : ¬ SawinBound G := by
  intro hs
  have := two_le_card_of_sawinBound hs
  omega

end Sawin

/-! ## Conciseness of `T_G` in coordinates

The Latin-square property of a group makes every slice of `T_G` a standard basis vector: fixing
two of the three indices of a compatible triple determines the third.  Ranging over the fixed
indices therefore realizes *every* basis vector of the remaining leg, which is conciseness in the
coordinate sense of `MatrixMultiplication/IndependenceBarrier.lean`.  This is the only place where
conciseness enters the barrier chain, and it supplies `|G| ≤ R̃(T_G)`. -/

section Concise

variable {K : Type u} [Field K] {G : Type v} [Group G] [Fintype G] [DecidableEq G]

/-- The triple of indices realizing the standard basis vector at `g` as a slice of `T_G` in the
direction of leg `i`: fill the two remaining legs so that the compatibility equation reads
`x = g`. -/
private def sliceWitness (i : Leg) (g : G) : ∀ j, GroupIndex G j :=
  match i with
  | .X => fun j ↦ match j with | .X => 1 | .Y => g⁻¹ | .Z => 1
  | .Y => fun j ↦ match j with | .X => g⁻¹ | .Y => 1 | .Z => 1
  | .Z => fun j ↦ match j with | .X => 1 | .Y => g⁻¹ | .Z => 1

/-- **The group tensor is concise in coordinates on every leg.**

Proof sketch: the slice of `T_G` in the direction of leg `i` through `sliceWitness i g` is the
indicator of `x = g`, i.e. the standard basis vector at `g`; as `g` ranges over `G` these span the
whole leg space. -/
theorem isCoordinateConcise_groupCoefficients (i : Leg) :
    IsCoordinateConcise (groupCoefficients K G) i := by
  classical
  refine le_antisymm le_top ?_
  rw [← (Pi.basisFun K G).span_eq]
  refine Submodule.span_mono ?_
  rintro _ ⟨g, rfl⟩
  rw [Pi.basisFun_apply]
  refine ⟨sliceWitness i g, ?_⟩
  funext x
  rw [Pi.single_apply]
  show (if GroupCompatible (Function.update (sliceWitness i g) i x) then (1 : K) else 0) =
    if x = g then 1 else 0
  refine if_congr ?_ rfl rfl
  cases i with
  | X =>
      show (x * g⁻¹ * 1 = 1) ↔ x = g
      simp [mul_inv_eq_one]
  | Y =>
      show (g⁻¹ * x * 1 = 1) ↔ x = g
      simp [eq_comm, inv_mul_eq_one]
  | Z =>
      show (1 * g⁻¹ * x = 1) ↔ x = g
      simp [inv_mul_eq_one, eq_comm]

/-- **`|G| ≤ R̃(T_G)`**: the leg dimensions of a coordinate-concise table are bounded by its
asymptotic rank.  This is the single use of conciseness in AVW Theorem 4.1. -/
theorem card_le_asymptoticRank_groupCoefficients :
    ((Fintype.card G : ℕ) : ℝ) ≤
      Tensor.asymptoticRank (coordinateTensor (groupCoefficients K G)) := by
  have h := Tensor.card_le_asymptoticRank
    (isCoordinateConcise_groupCoefficients (K := K) (G := G) Leg.X)
  simpa using h

end Concise

/-! ## A galactic certificate for `T_G`

For `|G| ≥ 2` the table of `T_G` admits a coordinate galactic certificate with data
`(n, a, b, c, F) = (1, 1, 1, |G|, 1)`.  It is the zeroing out of the `X` leg to the identity
element: the surviving terms are `x₁ y_g z_{g⁻¹}` for `g ∈ G`, which is one copy of `⟨1,1,|G|⟩`
after the matching bijection `g ↦ g⁻¹`.  That is exactly the shape packaged by
`AlgebraicComplexity.coordinateGalacticCertificate_of_pivot_bijection`, so the only thing to check
here is the support condition: `x·y·z = 1` at `x = 1` reads `z = y⁻¹`.

The point of proving this is that the certificate value set of `T_G` is then nonempty, so
`ω_g^{coord}(T_G)` is a genuine infimum and Theorem 6.1 below carries no side hypothesis. -/

section Certificate

variable {K : Type u} [CommSemiring K] {G : Type v} [Group G] [Fintype G] [DecidableEq G]

/-- **A coordinate galactic certificate for `T_G`** with data `(n,a,b,c,F) = (1,1,1,|G|,1)`.

Proof sketch: this is the pivot-bijection certificate
`AlgebraicComplexity.coordinateGalacticCertificate_of_pivot_bijection` with pivot the identity
element, all of `G` retained on the `Y` and `Z` legs, and inversion `g ↦ g⁻¹` as the matching
bijection: the compatibility relation `x·y·z = 1` at `x = 1` reads `z = y⁻¹`, so the surviving
terms `x_1 y_g z_{g⁻¹}` are one copy of `⟨1,1,|G|⟩`. -/
theorem coordinateGalacticCertificate_groupCoefficients :
    CoordinateGalacticCertificate K (groupCoefficients K G) 1 1 1 (Fintype.card G) 1 := by
  classical
  have h : CoordinateGalacticCertificate K (groupCoefficients K G) 1 1 1
      (Finset.univ : Finset G).card 1 := by
    refine coordinateGalacticCertificate_of_pivot_bijection K
      (T := groupCoefficients K G)
      (fun i ↦ match i with
        | .X => ({1} : Finset G)
        | .Y => (Finset.univ : Finset G)
        | .Z => (Finset.univ : Finset G))
      1 rfl ⟨1, Finset.mem_univ _⟩
      { toFun := fun y ↦ ⟨(y : G)⁻¹, Finset.mem_univ _⟩
        invFun := fun z ↦ ⟨(z : G)⁻¹, Finset.mem_univ _⟩
        left_inv := fun y ↦ by simp
        right_inv := fun z ↦ by simp } ?_
    intro y _ z _
    rw [groupCoefficients_apply]
    show (if (1 : G) * y * z = 1 then (1 : K) else 0) = _
    simp [mul_eq_one_iff_inv_eq, eq_comm]
  rwa [Finset.card_univ] at h

end Certificate

section CertificateField

variable {K : Type u} [Field K] {G : Type v} [Group G] [Fintype G] [DecidableEq G]

/-- For `|G| ≥ 2` the certificate value set of `T_G` is nonempty, so its coordinate galactic
exponent is a genuine infimum. -/
theorem coordinateGalacticValues_groupCoefficients_nonempty (h2 : 2 ≤ Fintype.card G) :
    (coordinateGalacticValues K (groupCoefficients K G)).Nonempty :=
  ⟨_, ⟨1, 1, 1, Fintype.card G, 1, coordinateGalacticCertificate_groupCoefficients,
    by simpa using h2, le_rfl, rfl⟩⟩

end CertificateField

/-! ## AVW Corollary 6.1 and Theorem 6.1, conditional on Sawin's theorem -/

section Barrier

variable {K : Type u} [Field K] {G : Type v} [Group G] [Fintype G] [DecidableEq G]

/-- **AVW Corollary 6.1**, conditional on the named proof obligation `SawinBound G`: the
asymptotic independence number of the table of `T_G` is at most `δ·|G|` for the very `δ < 1` of
the Sawin bound.

Proof sketch: `Ī` is the supremum of the roots `I(T^{⊗n})^{1/n}`
(`Tensor.asymptoticIndependenceNumber_le_of_pow`), the group-power identification turns
`I(T_G^{⊗n})` into the tri-coloured sum-free number of `Gⁿ` (Lemma 6.1), and that is what the
Sawin bound bounds by `(δ|G|)^n`. -/
theorem asymptoticIndependenceNumber_groupCoefficients_le_of_sawinBound (h : SawinBound G) :
    ∃ δ : ℝ, δ < 1 ∧ 1 ≤ δ * Fintype.card G ∧
      asymptoticIndependenceNumber (groupCoefficients K G) ≤ δ * Fintype.card G := by
  classical
  obtain ⟨δ, hδ, hb⟩ := h
  have h1 : 1 ≤ δ * Fintype.card G := one_le_of_sawinBound hb
  refine ⟨δ, hδ, h1, ?_⟩
  refine asymptoticIndependenceNumber_le_of_pow (by linarith) fun n ↦ ?_
  obtain ⟨S, hS, hcard⟩ :=
    exists_triColoredSumFree_card_eq (G := Fin n → G)
  have hbn := hb n S hS
  rw [hcard] at hbn
  rw [independenceNumberPowerSequence,
    independenceNumber_coordinatePower_groupCoefficients (K := K)]
  exact hbn

/-- **AVW Theorem 6.1**, the honest deliverable of milestone L:

> conditionally on Sawin's theorem for `G`, the Galactic method applied to the group tensor `T_G`
> cannot prove any exponent bound below `6/(s+2) > 2`, where `s = log(δ|G|)/log|G| < 1`.

The exponent is the **coordinate** galactic exponent of the table of `T_G`; see the module header
for why no claim is made about the abstract `galacticExponent`.  Every hypothesis is explicit:
`SawinBound G` is a named proof obligation and is not proved anywhere in this repository.

Proof sketch: Corollary 6.1 gives `Ī(T_G) ≤ δ|G|` with `1 ≤ δ|G| < |G|`, so `|G| ≥ 2`.  Conciseness
of `T_G` in coordinates gives `|G| ≤ R̃(T_G)`, hence `1 < R̃(T_G)`; with
`s = log(δ|G|)/log|G| ∈ [0, 1)` we get `R̃(T_G)^s ≥ |G|^s = δ|G| ≥ Ī(T_G)`.  The zeroing out of the
`X` leg to the identity supplies a galactic certificate, so the exponent is a genuine infimum, and
AVW Corollary 4.3 (`two_lt_coordinateGalacticExponent_of_concise`) concludes. -/
theorem two_lt_coordinateGalacticExponent_groupCoefficients_of_sawinBound (h : SawinBound G) :
    2 < coordinateGalacticExponent K (groupCoefficients K G) := by
  classical
  obtain ⟨δ, hδ, h1, hbar⟩ :=
    asymptoticIndependenceNumber_groupCoefficients_le_of_sawinBound (K := K) h
  have h2card : 2 ≤ Fintype.card G := two_le_card_of_sawinBound h
  set N : ℝ := ((Fintype.card G : ℕ) : ℝ) with hN
  have hN2 : (2 : ℝ) ≤ N := by rw [hN]; exact_mod_cast h2card
  have hN0 : (0 : ℝ) < N := by linarith
  set c : ℝ := δ * N with hc
  have hc1 : 1 ≤ c := h1
  have hc0 : (0 : ℝ) < c := by linarith
  have hcN : c < N := by
    calc c = δ * N := rfl
      _ < 1 * N := by exact mul_lt_mul_of_pos_right hδ hN0
      _ = N := one_mul N
  -- The exponent `s`.
  have hlogN : 0 < Real.log N := Real.log_pos (by linarith)
  set s : ℝ := Real.log c / Real.log N with hs
  have hs0 : 0 ≤ s := div_nonneg (Real.log_nonneg hc1) hlogN.le
  have hs1 : s < 1 := by
    rw [hs, div_lt_one hlogN]
    exact Real.log_lt_log hc0 hcN
  -- `N ^ s = c`.
  have hpow : N ^ s = c := by
    rw [Real.rpow_def_of_pos hN0, hs, ← mul_div_assoc, mul_comm,
      mul_div_assoc, div_self (ne_of_gt hlogN), mul_one, Real.exp_log hc0]
  -- The asymptotic rank dominates `N`.
  set R : ℝ := Tensor.asymptoticRank (coordinateTensor (groupCoefficients K G)) with hR
  have hNR : N ≤ R := card_le_asymptoticRank_groupCoefficients (K := K) (G := G)
  have hR1 : 1 < R := by linarith
  have hIs : asymptoticIndependenceNumber (groupCoefficients K G) ≤ R ^ s := by
    refine hbar.trans ?_
    rw [← hpow]
    exact Real.rpow_le_rpow hN0.le hNR hs0
  exact two_lt_coordinateGalacticExponent_of_concise K
    (fun i ↦ isCoordinateConcise_groupCoefficients i) hR1 (by linarith) hs1 hIs
    (coordinateGalacticValues_groupCoefficients_nonempty h2card)

end Barrier

/-! ## Tiny clients: the trivial group and the two-element group

`DESIGN.md` asks every major semantic operation to have a deliberately tiny client that catches
direction and convention errors before they hide inside a large proof.  The two-element group is
the smallest interesting test: its tri-coloured sum-free number is `1`, not `2`, and getting the
convention backwards would produce `2`.

The answer `1` is also a consistency check against a completely independent computation already in
the tree: `Tensor.HadamardWitness.independenceNumber_hadamardCoefficients` evaluates the
independence number of the table `1 + s_i s_j s_k` over `ℚ`, which has exactly the support of
`T_{C₂}`, and finds `1`. -/

section TinyClients

/-- The trivial group has tri-coloured sum-free number `1`: at most `|G| = 1` by the projection
bound, at least `1` by the singleton `{(1,1,1)}`. -/
theorem triColoredSumFreeNumber_punit : triColoredSumFreeNumber PUnit.{v + 1} = 1 := by
  refine le_antisymm ?_ one_le_triColoredSumFreeNumber
  have h := triColoredSumFreeNumber_le_card (G := PUnit.{v + 1})
  simpa using h

/-- **The two-element group has tri-coloured sum-free number `1`.**

Proof sketch: two distinct members of a tri-coloured sum-free set have pairwise distinct
coordinates on all three legs, so in `C₂` the second is obtained from the first by flipping all
three coordinates; that changes the product by the cube of the nonidentity element, which is the
nonidentity element, so the two products cannot both be `1`.  The finite case check is a `decide`
over `(ZMod 2)^6`. -/
theorem triColoredSumFreeNumber_multiplicative_zmod_two :
    triColoredSumFreeNumber (Multiplicative (ZMod 2)) = 1 := by
  classical
  refine le_antisymm (triColoredSumFreeNumber_le fun S hS ↦ ?_) one_le_triColoredSumFreeNumber
  rw [Finset.card_le_one]
  intro t ht u hu
  by_contra hne
  have hfst : t.1 ≠ u.1 := fun hc ↦ hne (hS.eq_of_fst_eq ht hu hc)
  have hsnd : t.2.1 ≠ u.2.1 := fun hc ↦ hne (hS.eq_of_snd_eq ht hu hc)
  have hthd : t.2.2 ≠ u.2.2 := fun hc ↦ hne (hS.eq_of_thd_eq ht hu hc)
  have key : ∀ a₁ b₁ c₁ a₂ b₂ c₂ : Multiplicative (ZMod 2),
      a₁ * b₁ * c₁ = 1 → a₂ * b₂ * c₂ = 1 → a₁ ≠ a₂ → b₁ ≠ b₂ → c₁ ≠ c₂ → False := by decide
  exact key t.1 t.2.1 t.2.2 u.1 u.2.1 u.2.2 (hS.mul_eq_one t ht) (hS.mul_eq_one u hu)
    hfst hsnd hthd

/-- The convention regression test at the tensor level: over `ℚ`, the independence number of the
table of `T_{C₂}` is `1`.  This is `independenceNumber_groupCoefficients` instantiated at the
two-element group; a wrong direction or a wrong support convention would give `2`. -/
theorem independenceNumber_groupCoefficients_zmod_two :
    independenceNumber (groupCoefficients ℚ (Multiplicative (ZMod 2))) = 1 := by
  rw [independenceNumber_groupCoefficients (K := ℚ),
    triColoredSumFreeNumber_multiplicative_zmod_two]

end TinyClients

end AlgebraicComplexity.Examples
