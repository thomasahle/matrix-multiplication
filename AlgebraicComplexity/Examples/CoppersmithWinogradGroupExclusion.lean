/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinograd
import AlgebraicComplexity.Tensor.Coordinates
import AlgebraicComplexity.Tensor.GroupTensor
import AlgebraicComplexity.Tensor.IndependenceNumber

/-!
# The Coppersmith--Winograd tensor is not a sub-tensor of a small abelian group tensor

This file formalizes Lemma 6.3 of Alman--Vassilevska Williams, *Limits on all known (and some
unknown) approaches to matrix multiplication* (arXiv:1810.08671), together with the elementary
square-root count (their Lemma 6.2) that it rests on:

> For every positive integer `q`, the Coppersmith--Winograd tensor `CW_q` is not a sub-tensor of
> the group tensor `T_G` of an abelian group `G` with `|G| < 2q`.

## The sub-tensor relation, and why the definition here is faithful

AVW define (Section 3.1.2) a tensor `t` to be a *sub-tensor* of `t'`, written `t ⊆ t'`, when `t` is
obtained from `t'` by deleting triples from its support: for every index triple `(i, j, k)`, either
`t_{ijk} = t'_{ijk}` or `t_{ijk} = 0`.  Verbatim, that relation only compares tensors living on the
*same* three index sets.  In the statement of Lemma 6.3 the two tensors have different formats
(`CW_q` has `q + 2` variables per leg, `T_G` has `|G|`), and the proof spells out the intended
reading: "there are injections `a, b, c : {0, 1, …, q+1} → G` such that if `x_i y_j z_k ∈ CW_q`,
then `x̄_{a(i)} ȳ_{b(j)} z̄_{c(k)} ∈ T_G`".  In other words, one first *zeroes out* `T_G` down to
the images of three injections -- one per leg -- and then compares in AVW's verbatim sense after
identifying the surviving variables with those of `CW_q` along those injections.

`IsSubTensorVia` below is exactly that composite: injections `f c` on the three legs, plus the
verbatim entrywise condition "every coefficient of the small tensor is either zero or equal to the
coefficient of the large tensor at the relabelled address".  Three points about fidelity:

* the entrywise disjunction is kept in AVW's *inclusive* form.  Requiring instead that the small
  tensor be *equal* to the induced zeroing-out of the large one is a strictly stronger hypothesis;
  it is recorded separately as `IsInducedSubTensorVia` and shown to imply `IsSubTensorVia`.  Since
  the theorem proved here is a non-existence statement, using the inclusive relation makes it
  strictly stronger, and it is the relation the AVW proof actually consumes;
* injectivity on each leg is part of the definition, matching AVW's "injections".  It is what makes
  the relation a genuine sub-object relation rather than an arbitrary combinatorial restriction, and
  the proof of Lemma 6.3 uses it twice (once on the `X` leg, once on the `Z` leg);
* this is **not** the repository's `Restricts` relation of `Tensor/Restriction.lean`.  `Restricts`
  allows arbitrary linear maps on the legs, whereas a sub-tensor witness is the special
  "combinatorial" case in which each leg map is a coordinate injection.  Both halves of the
  comparison are proved below.  The induced form *is* an exact linear pullback:
  `IsInducedSubTensorVia.restricts` turns it into `Restricts t' t` --- note the exchange of source
  and target --- and does not even need injectivity.  The inclusive form is not:
  `isSubTensorVia_not_restricts` exhibits `⟨2⟩ ⊆ all-ones` over `ℚ` with no restriction the other
  way, because deleting triples can raise the slice rank.  The exclusion theorem proved here is
  therefore about the inclusive relation only, and says nothing about `Restricts`.

Coefficients are read through the canonical coordinate equivalence `standardCoordinateEquiv` of
`Tensor/Coordinates.lean`, so the definition applies to any tensor presented on finite standard
coordinate legs.

## Main results

* `IsSubTensorVia`, `IsSubTensor`, `IsInducedSubTensorVia`, `IsInducedSubTensor`: the relation
  above, in its "with a named witness" and existential forms, with reflexivity, transitivity, and
  the implication from the induced (zeroing-out) form;
* `IsInducedSubTensorVia.restricts` and `isSubTensorVia_not_restricts`: the comparison with
  `Tensor.Restricts` --- true for the induced relation, false for the inclusive one;
* `standardCoordinateEquiv_coppersmithWinograd`: the coefficient function of `CW_q` in standard
  coordinates, and the six families of address-wise consequences
  `standardCoordinateEquiv_coppersmithWinograd_011` … `_002` giving the coefficient `1` on the CW
  support;
* `two_mul_card_squareRootFinset_le`: AVW Lemma 6.2 -- in a finite abelian group, a non-identity
  element has at most `|G| / 2` square roots;
* `two_mul_le_card_of_coppersmithWinogradRelations`: the coefficient-free combinatorial core of AVW
  Lemma 6.3.  Three maps `A, B, C : CWIndex q → G` into an abelian group satisfying the six support
  equations of `CW_q` (in the `a * b * c = 1` convention), injective enough to separate the `q`
  middle `X`-labels and the two extreme `Z`-labels, force `2q ≤ |G|`;
* `not_isSubTensor_coppersmithWinograd_groupTensor` and
  `not_isSubTensor_coppersmithWinograd_groupTensorMul`: AVW Lemma 6.3 for both coordinate
  conventions of the group tensor supplied by `Tensor/GroupTensor.lean`;
* `not_isSubTensor_coppersmithWinograd_groupTensor_of_card_eq`: the abelian half of AVW Theorem 6.2
  -- for `q ≥ 3`, `CW_q` is not a sub-tensor of `T_G` for any abelian `G` of order `q + 2`.

## Hypotheses

The mathematical content is purely combinatorial, and the core statement
`two_mul_le_card_of_coppersmithWinogradRelations` mentions no coefficient ring at all.  The
tensor-level statements are over a commutative semiring `K` that is `Nontrivial`: nontriviality is
not a convenience but a necessity, since over the zero ring `1 = 0` and *every* tensor is a
sub-tensor of every other one.  No field, no characteristic assumption, and no finite-dimensionality
beyond the finiteness of the coordinate legs is used.

The group is assumed abelian (`CommGroup`); this is exactly AVW's hypothesis, and it is used twice:
in Lemma 6.2 (the translation `a ↦ a * √g` is a bijection between the square roots of `1` and those
of `g` only when `G` is abelian) and when solving the CW support equations for `a_i²`.  The
nonabelian orders `q + 2` for `q = 4, 6, 8` of AVW Theorem 6.2 are a separate finite check and are
**not** attempted here.

## Proof sketch of the main theorem

Write `u = A(0)`, `v = B(0)`, `w = C(0)` for the images of the CW zero coordinate and `a_i, b_i, c_i`
for the images of the `i`-th middle coordinate.  The CW support contains `(0, i, i)`, `(i, 0, i)`,
`(i, i, 0)` for each middle index `i`, and the corner `(0, 0, q+1)`.  In the group tensor's
`a * b * c = 1` convention these become `u b_i c_i = 1`, `a_i v c_i = 1`, `a_i b_i w = 1`, and
`u v s = 1` with `s = C(q+1)`.  Eliminating `b_i` and `c_i` from the first three gives
`a_i² = u w⁻¹ v⁻¹`, independent of `i`.  Translating by `u⁻¹` -- which is a bijection of `G`, so the
`q` shifted elements `a_i u⁻¹` are still distinct -- gives `(a_i u⁻¹)² = g` for the single element
`g = u w⁻¹ v⁻¹ u⁻²`.  If `g` were the identity then `w⁻¹ v⁻¹ = u`, hence `w = (u v)⁻¹ = s` by the
corner equation, contradicting injectivity of `C` on the two extreme `Z` coordinates.  So `g ≠ 1`
has at least `q` square roots, and Lemma 6.2 gives `2q ≤ |G|`.

This is AVW's argument with their "without loss of generality `a(0) = b(0) = c(0) = 1`"
normalization replaced by the explicit translation by `u⁻¹`; the normalization is exactly the
statement that the translated maps still solve the same equations, so nothing is lost.

## Layer placement

This is a layer-4 regression client (`AlgebraicComplexity/Examples/`).  It consumes the layer-1
group tensor of `Tensor/GroupTensor.lean`, the layer-1 independence number of
`Tensor/IndependenceNumber.lean` (only for the counterexample `isSubTensorVia_not_restricts`), and
the layer-4 Coppersmith--Winograd tensor of `Examples/CoppersmithWinograd.lean`; it introduces no
new reusable-core declaration.  The index family `CWCoordIndex`, the address characterization
`cwIndex_eq_ofLegs_iff` and the standard-basis restatements `cwMiddle_eq_pure`/`cwCorners_eq_pure`
live with the tensor itself in `Examples/CoppersmithWinograd.lean`, since
`Examples/GeneralizedCoppersmithWinograd.lean` needs them too.  The `IsSubTensor` family is a
candidate for later promotion into `Tensor/Restriction.lean` next to `Restricts`; it is kept here
until a second client needs it, per the promotion policy in `DESIGN.md`.

`Examples/CoppersmithWinogradSupport.lean` is deliberately **not** imported: it records the
*block* support of `CW_q` (the six coarse addresses used by the laser method), whereas the argument
below needs the *coordinate* support -- individual middle indices `i ∈ Fin q` must be told apart,
which is precisely what the block partition forgets.

## Non-goals

* the nonabelian cases of AVW Theorem 6.2 (`|G| = q + 2`, `q = 4, 6, 8`), which need a finite search
  over four groups;
* AVW Remark 6.2's converse construction exhibiting `CW_{2^k+1}` inside `T_{C_{2^k} × C_4}`, which
  would show the bound `2q` is attained;
* the monomial-degeneration statements of AVW Section 7, which are about a strictly weaker relation
  than the one excluded here.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor

universe u v w w'

/-! ## The sub-tensor relation for coordinate tensors -/

section SubTensor

variable {K : Type u} [CommSemiring K]
variable {ι : Leg → Type v} [∀ c, Finite (ι c)]
variable {κ : Leg → Type w} [∀ c, Finite (κ c)]
variable {μ : Leg → Type w'} [∀ c, Finite (μ c)]

/-- `IsSubTensorVia f t t'` says that the family of leg maps `f` witnesses `t ⊆ t'` in the sense of
Alman--Vassilevska Williams (arXiv:1810.08671, Section 3.1.2), extended across differing formats:
each `f c` is an injection of the `c`-th index set of `t` into that of `t'`, and every coefficient
of `t` is either zero or equal to the coefficient of `t'` at the relabelled address.

Equivalently: zero out all variables of `t'` outside the images of `f`, identify the survivors with
the variables of `t` along `f`, and then `t` is obtained from the result by deleting triples. -/
def IsSubTensorVia (f : ∀ c, ι c → κ c)
    (t : Tensor3 K (CoordinateSpace K ι)) (t' : Tensor3 K (CoordinateSpace K κ)) : Prop :=
  (∀ c, Function.Injective (f c)) ∧
    ∀ a : ∀ c, ι c,
      standardCoordinateEquiv (K := K) (κ := ι) t a = 0 ∨
        standardCoordinateEquiv (K := K) (κ := ι) t a =
          standardCoordinateEquiv (K := K) (κ := κ) t' fun c ↦ f c (a c)

/-- `IsSubTensor t t'` says that `t` is a sub-tensor of `t'` for *some* choice of leg injections;
this is the relation `t ⊆ t'` of Alman--Vassilevska Williams as used in their Lemma 6.3. -/
def IsSubTensor (t : Tensor3 K (CoordinateSpace K ι))
    (t' : Tensor3 K (CoordinateSpace K κ)) : Prop :=
  ∃ f : ∀ c, ι c → κ c, IsSubTensorVia f t t'

/-- The stricter, "zeroing-out" variant: the leg injections `f` identify `t` with *exactly* the
sub-tensor of `t'` induced on the images of `f`, with no further deletion of triples allowed. -/
def IsInducedSubTensorVia (f : ∀ c, ι c → κ c)
    (t : Tensor3 K (CoordinateSpace K ι)) (t' : Tensor3 K (CoordinateSpace K κ)) : Prop :=
  (∀ c, Function.Injective (f c)) ∧
    ∀ a : ∀ c, ι c,
      standardCoordinateEquiv (K := K) (κ := ι) t a =
        standardCoordinateEquiv (K := K) (κ := κ) t' fun c ↦ f c (a c)

/-- `t` is the zeroing-out of `t'` induced by some triple of leg injections. -/
def IsInducedSubTensor (t : Tensor3 K (CoordinateSpace K ι))
    (t' : Tensor3 K (CoordinateSpace K κ)) : Prop :=
  ∃ f : ∀ c, ι c → κ c, IsInducedSubTensorVia f t t'

/-- An induced (zeroing-out) sub-tensor is in particular a sub-tensor, with the same witness. -/
theorem IsInducedSubTensorVia.isSubTensorVia {f : ∀ c, ι c → κ c}
    {t : Tensor3 K (CoordinateSpace K ι)} {t' : Tensor3 K (CoordinateSpace K κ)}
    (h : IsInducedSubTensorVia f t t') : IsSubTensorVia f t t' :=
  ⟨h.1, fun a ↦ Or.inr (h.2 a)⟩

/-- Existential form of `IsInducedSubTensorVia.isSubTensorVia`. -/
theorem IsInducedSubTensor.isSubTensor {t : Tensor3 K (CoordinateSpace K ι)}
    {t' : Tensor3 K (CoordinateSpace K κ)} (h : IsInducedSubTensor t t') : IsSubTensor t t' := by
  obtain ⟨f, hf⟩ := h
  exact ⟨f, hf.isSubTensorVia⟩

/-- Every tensor is a sub-tensor of itself, via the identity injections. -/
theorem isSubTensor_rfl (t : Tensor3 K (CoordinateSpace K ι)) : IsSubTensor t t :=
  ⟨fun _ x ↦ x, fun _ ↦ Function.injective_id, fun _ ↦ Or.inr rfl⟩

/-- The sub-tensor relation is transitive: compose the leg injections.

Proof sketch: for a fixed address, either the coefficient of the smallest tensor is zero (done), or
it agrees with the middle tensor's coefficient at the relabelled address, and that coefficient is
in turn either zero -- forcing the first one to be zero as well -- or equal to the coefficient of
the largest tensor at the twice-relabelled address. -/
theorem IsSubTensor.trans {t : Tensor3 K (CoordinateSpace K ι)}
    {t' : Tensor3 K (CoordinateSpace K κ)} {t'' : Tensor3 K (CoordinateSpace K μ)}
    (h : IsSubTensor t t') (h' : IsSubTensor t' t'') : IsSubTensor t t'' := by
  obtain ⟨f, hfinj, hf⟩ := h
  obtain ⟨g, hginj, hg⟩ := h'
  refine ⟨fun c ↦ g c ∘ f c, fun c ↦ (hginj c).comp (hfinj c), fun a ↦ ?_⟩
  rcases hf a with h1 | h1
  · exact Or.inl h1
  · rcases hg (fun c ↦ f c (a c)) with h2 | h2
    · exact Or.inl (h1.trans h2)
    · exact Or.inr (h1.trans h2)

/-- Transport of a coefficient equal to `1` along a sub-tensor witness: if the small tensor has
coefficient `1` at an address, the large tensor has coefficient `1` at the relabelled address.

This is the only consequence of the sub-tensor relation that the exclusion theorem uses, and it is
where nontriviality of the coefficient semiring enters: over the zero ring the disjunction in
`IsSubTensorVia` carries no information. -/
theorem IsSubTensorVia.coeff_eq_one [Nontrivial K] {f : ∀ c, ι c → κ c}
    {t : Tensor3 K (CoordinateSpace K ι)} {t' : Tensor3 K (CoordinateSpace K κ)}
    (h : IsSubTensorVia f t t') {a : ∀ c, ι c}
    (ha : standardCoordinateEquiv (K := K) (κ := ι) t a = 1) :
    standardCoordinateEquiv (K := K) (κ := κ) t' (fun c ↦ f c (a c)) = 1 := by
  rcases h.2 a with h1 | h1
  · exact absurd (ha.symm.trans h1) one_ne_zero
  · exact h1.symm.trans ha

/-! ### Comparison with `Restricts`

The induced (zeroing-out) relation *is* an exact linear pullback, so it implies `Restricts` with
the source and target exchanged; injectivity of the leg maps is not even needed.  The inclusive
relation is not, and `isSubTensorVia_not_restricts` exhibits a counterexample. -/

/-- **An induced sub-tensor is a restriction.**  If `f` identifies `t` with the zeroing-out of `t'`
on the images of `f`, then the legwise coordinate restrictions `LinearMap.funLeft K K (f c)` carry
`t'` to `t`.  Note the exchange of source and target: `t'` is the tensor being restricted.

Proof sketch: `standardCoordinateEquiv_map_funLeft` computes the coefficient function of the image
of `t'` under those maps as `a ↦ t'_{f(a)}`, which is exactly the defining equation of
`IsInducedSubTensorVia`.  Injectivity of `f` plays no role. -/
theorem IsInducedSubTensorVia.restricts {f : ∀ c, ι c → κ c}
    {t : Tensor3 K (CoordinateSpace K ι)} {t' : Tensor3 K (CoordinateSpace K κ)}
    (h : IsInducedSubTensorVia f t t') : Restricts t' t := by
  refine ⟨fun c ↦ LinearMap.funLeft K K (f c), ?_⟩
  refine standardCoordinate_ext (K := K) (κ := ι) fun p ↦ ?_
  rw [standardCoordinateEquiv_map_funLeft]
  exact (h.2 p).symm

/-- Existential form of `IsInducedSubTensorVia.restricts`. -/
theorem IsInducedSubTensor.restricts {t : Tensor3 K (CoordinateSpace K ι)}
    {t' : Tensor3 K (CoordinateSpace K κ)} (h : IsInducedSubTensor t t') : Restricts t' t := by
  obtain ⟨f, hf⟩ := h
  exact hf.restricts

end SubTensor

/-- **The inclusive sub-tensor relation does not imply `Restricts`.**  Over `ℚ` on two-element
legs, the diagonal `⟨2⟩` is a verbatim sub-tensor of the all-ones tensor via the identity
injections --- deleting the four off-diagonal triples --- yet the all-ones tensor is a single pure
tensor of slice rank at most one, while `⟨2⟩` has slice rank two, so no legwise linear maps can
carry the second onto the first.

This is the same all-ones/diagonal pair that `Tensor/IndependenceNumber.lean` cites for the
non-monotonicity of the independence number, and it is what makes the deletion of triples allowed
by `IsSubTensorVia` genuinely non-linear. -/
theorem isSubTensorVia_not_restricts :
    IsSubTensorVia (ι := fun _ : Leg ↦ Fin 2) (κ := fun _ : Leg ↦ Fin 2) (fun _ x ↦ x)
        (coordinateTensor (diagonalCoefficients ℚ (Fin 2)))
        (coordinateTensor (fun _ : ∀ _ : Leg, Fin 2 ↦ (1 : ℚ))) ∧
      ¬ Restricts (coordinateTensor (fun _ : ∀ _ : Leg, Fin 2 ↦ (1 : ℚ)))
        (coordinateTensor (diagonalCoefficients ℚ (Fin 2))) := by
  classical
  constructor
  · refine ⟨fun _ ↦ Function.injective_id, fun a ↦ ?_⟩
    rw [standardCoordinateEquiv_coordinateTensor, standardCoordinateEquiv_coordinateTensor]
    by_cases h : ∀ i, a i = a .X
    · exact Or.inr (by simp [diagonalCoefficients, h])
    · exact Or.inl (by simp [diagonalCoefficients, h])
  · intro hres
    have h1 : sliceRank (coordinateTensor (diagonalCoefficients ℚ (Fin 2))) ≤
        sliceRank (coordinateTensor (fun _ : ∀ _ : Leg, Fin 2 ↦ (1 : ℚ))) :=
      sliceRank_restricts_le hres
    rw [coordinateTensor_diagonalCoefficients, sliceRank_diagonalTensor,
      coordinateTensor_const_one] at h1
    have h2 := sliceRank_pure_le_one (K := ℚ)
      (V := CoordinateSpace ℚ (fun _ : Leg ↦ Fin 2))
      (fun _ ↦ (fun _ : Fin 2 ↦ (1 : ℚ)))
    simp only [Fintype.card_fin] at h1
    omega


/-! ## Coordinate support of the Coppersmith--Winograd tensor -/

section CWCoefficients

variable (K : Type u) [CommSemiring K] (q : ℕ)

/-- The coefficient function of a pure tensor built from three standard CW basis vectors is the
indicator of the single address `ofLegs x y z`. -/
theorem standardCoordinateEquiv_pure_cwBasis (x y z : CWIndex q) (a : ∀ c, CWCoordIndex q c) :
    standardCoordinateEquiv (K := K) (κ := CWCoordIndex q)
        (pure (K := K) (ofLegs (V := CWSpace K q)
          (cwBasis K q x) (cwBasis K q y) (cwBasis K q z))) a =
      if a = ofLegs x y z then 1 else 0 := by
  classical
  have h : (ofLegs (V := CWSpace K q) (cwBasis K q x) (cwBasis K q y) (cwBasis K q z)) =
      fun i ↦ (Pi.single (ofLegs (V := CWCoordIndex q) x y z i) (1 : K) : CWIndex q → K) := by
    funext i; cases i <;> rfl
  rw [h, standardCoordinateEquiv_pure_single]
  exact if_congr eq_comm rfl rfl

/-- Coordinate coefficient formula for the full Coppersmith--Winograd tensor: `CW_q` is the sum of
the indicators of its `3q + 3` support addresses.

Proof sketch: `coppersmithWinograd` is by definition the sum of the `q` middle blocks and the
corner block, each of which is a sum of three pure standard-basis tensors; apply linearity of the
coefficient equivalence and `standardCoordinateEquiv_pure_cwBasis` to each summand. -/
theorem standardCoordinateEquiv_coppersmithWinograd (a : ∀ c, CWCoordIndex q c) :
    standardCoordinateEquiv (K := K) (κ := CWCoordIndex q) (coppersmithWinograd K q) a =
      (∑ i : Fin q,
          ((if a = ofLegs .zero (.middle i) (.middle i) then (1 : K) else 0) +
            (if a = ofLegs (.middle i) .zero (.middle i) then (1 : K) else 0) +
            (if a = ofLegs (.middle i) (.middle i) .zero then (1 : K) else 0))) +
        ((if a = ofLegs .last .zero .zero then (1 : K) else 0) +
          (if a = ofLegs .zero .last .zero then (1 : K) else 0) +
          (if a = ofLegs .zero .zero .last then (1 : K) else 0)) := by
  classical
  unfold coppersmithWinograd
  simp only [map_add, Pi.add_apply, map_sum, Finset.sum_apply]
  congr 1
  · refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [cwMiddle_eq_pure]
    simp only [map_add, Pi.add_apply, standardCoordinateEquiv_pure_cwBasis]
  · rw [cwCorners_eq_pure]
    simp only [map_add, Pi.add_apply, standardCoordinateEquiv_pure_cwBasis]

/-- The `(0, i, i)` support address of `CW_q` carries coefficient `1`. -/
theorem standardCoordinateEquiv_coppersmithWinograd_011 (i : Fin q) :
    standardCoordinateEquiv (K := K) (κ := CWCoordIndex q) (coppersmithWinograd K q)
        (ofLegs .zero (.middle i) (.middle i)) = 1 := by
  classical
  rw [standardCoordinateEquiv_coppersmithWinograd]
  simp [cwIndex_eq_ofLegs_iff, eq_comm]

/-- The `(i, 0, i)` support address of `CW_q` carries coefficient `1`. -/
theorem standardCoordinateEquiv_coppersmithWinograd_101 (i : Fin q) :
    standardCoordinateEquiv (K := K) (κ := CWCoordIndex q) (coppersmithWinograd K q)
        (ofLegs (.middle i) .zero (.middle i)) = 1 := by
  classical
  rw [standardCoordinateEquiv_coppersmithWinograd]
  simp [cwIndex_eq_ofLegs_iff, eq_comm]

/-- The `(i, i, 0)` support address of `CW_q` carries coefficient `1`. -/
theorem standardCoordinateEquiv_coppersmithWinograd_110 (i : Fin q) :
    standardCoordinateEquiv (K := K) (κ := CWCoordIndex q) (coppersmithWinograd K q)
        (ofLegs (.middle i) (.middle i) .zero) = 1 := by
  classical
  rw [standardCoordinateEquiv_coppersmithWinograd]
  simp [cwIndex_eq_ofLegs_iff, eq_comm]

/-- The `(q+1, 0, 0)` corner address of `CW_q` carries coefficient `1`. -/
theorem standardCoordinateEquiv_coppersmithWinograd_200 :
    standardCoordinateEquiv (K := K) (κ := CWCoordIndex q) (coppersmithWinograd K q)
        (ofLegs .last .zero .zero) = 1 := by
  classical
  rw [standardCoordinateEquiv_coppersmithWinograd]
  simp [cwIndex_eq_ofLegs_iff]

/-- The `(0, q+1, 0)` corner address of `CW_q` carries coefficient `1`. -/
theorem standardCoordinateEquiv_coppersmithWinograd_020 :
    standardCoordinateEquiv (K := K) (κ := CWCoordIndex q) (coppersmithWinograd K q)
        (ofLegs .zero .last .zero) = 1 := by
  classical
  rw [standardCoordinateEquiv_coppersmithWinograd]
  simp [cwIndex_eq_ofLegs_iff]

/-- The `(0, 0, q+1)` corner address of `CW_q` carries coefficient `1`. -/
theorem standardCoordinateEquiv_coppersmithWinograd_002 :
    standardCoordinateEquiv (K := K) (κ := CWCoordIndex q) (coppersmithWinograd K q)
        (ofLegs .zero .zero .last) = 1 := by
  classical
  rw [standardCoordinateEquiv_coppersmithWinograd]
  simp [cwIndex_eq_ofLegs_iff]

end CWCoefficients

/-! ## Square roots in a finite abelian group (AVW Lemma 6.2) -/

section SquareRoots

/-- The finite set of square roots of `g` in a finite monoid. -/
def squareRootFinset (G : Type v) [Monoid G] [Fintype G] [DecidableEq G] (g : G) : Finset G :=
  Finset.univ.filter fun a ↦ a * a = g

/-- Membership in `squareRootFinset G g` is the equation `a * a = g`. -/
@[simp] theorem mem_squareRootFinset {G : Type v} [Monoid G] [Fintype G] [DecidableEq G]
    {g a : G} : a ∈ squareRootFinset G g ↔ a * a = g := by
  simp [squareRootFinset]

/-- **AVW Lemma 6.2.** In a finite abelian group, every element other than the identity has at most
`|G| / 2` square roots, stated multiplication-free as `2 · #{a | a² = g} ≤ |G|`.

Proof sketch: if `g` has no square root the claim is trivial.  Otherwise fix one square root `r`.
Because `G` is abelian, `a ↦ a * r` is a bijection from the square roots of `1` onto the square
roots of `g`, with inverse `s ↦ s * r⁻¹`; so the two sets have the same size.  They are disjoint,
since a common element would give `g = a * a = 1`.  Their union sits inside `G`, which yields
`2 · #{a | a² = g} = #{a | a² = 1} + #{a | a² = g} ≤ |G|`. -/
theorem two_mul_card_squareRootFinset_le {G : Type v} [CommGroup G] [Fintype G] [DecidableEq G]
    {g : G} (hg : g ≠ 1) :
    2 * (squareRootFinset G g).card ≤ Fintype.card G := by
  classical
  rcases Finset.eq_empty_or_nonempty (squareRootFinset G g) with hemp | ⟨r, hr⟩
  · simp [hemp]
  · have hr' : r * r = g := mem_squareRootFinset.mp hr
    have hcard : (squareRootFinset G 1).card = (squareRootFinset G g).card := by
      refine Finset.card_nbij' (fun a ↦ a * r) (fun s ↦ s * r⁻¹) ?_ ?_ ?_ ?_
      · intro a ha
        simp only [Finset.mem_coe, mem_squareRootFinset] at ha ⊢
        rw [mul_mul_mul_comm, ha, hr', one_mul]
      · intro s hs
        simp only [Finset.mem_coe, mem_squareRootFinset] at hs ⊢
        rw [mul_mul_mul_comm, hs, ← mul_inv, hr', mul_inv_cancel]
      · intro a _
        simp
      · intro s _
        simp
    have hdisj : Disjoint (squareRootFinset G 1) (squareRootFinset G g) := by
      rw [Finset.disjoint_left]
      intro a ha1 ha2
      rw [mem_squareRootFinset] at ha1 ha2
      exact hg (ha2.symm.trans ha1)
    calc 2 * (squareRootFinset G g).card
        = (squareRootFinset G 1).card + (squareRootFinset G g).card := by rw [hcard]; ring
      _ = (squareRootFinset G 1 ∪ squareRootFinset G g).card :=
          (Finset.card_union_of_disjoint hdisj).symm
      _ ≤ Fintype.card G := Finset.card_le_univ _

end SquareRoots

/-! ## The combinatorial core of AVW Lemma 6.3 -/

/-- **Coefficient-free core of AVW Lemma 6.3.**  Suppose three maps `A, B, C : CWIndex q → G` into a
finite abelian group solve the support equations of `CW_q` in the symmetric group-tensor convention
`a * b * c = 1`: the three middle families `(0, i, i)`, `(i, 0, i)`, `(i, i, 0)` and the corner
`(0, 0, q+1)`.  If `A` separates the `q` middle `X`-labels and `C` separates the two extreme
`Z`-labels, then `2q ≤ |G|`.

Note the deliberately weak injectivity hypotheses: full injectivity of `A`, `B` and `C` is never
needed, only the two separations actually used by the argument.

Proof sketch: write `u = A 0`, `v = B 0`, `w = C 0` and `a_i = A i`, `b_i = B i`, `c_i = C i`.  The
equations `u b_i c_i = 1` and `a_i v c_i = 1` both express `c_i` as an inverse, so `u b_i = a_i v`;
substituting into `a_i b_i w = 1`, which says `a_i b_i = w⁻¹`, eliminates `b_i` and gives
`a_i² v = u w⁻¹`, hence `a_i² = u w⁻¹ v⁻¹` for every `i`.  Translating by `u⁻¹` keeps the `q`
elements distinct and makes all of them square roots of the single element
`g = u w⁻¹ v⁻¹ · u⁻¹ u⁻¹`.  If `g = 1` then `w⁻¹ v⁻¹ = u`, so `u v = w⁻¹`, so `w = (u v)⁻¹`; but the
corner equation `u v (C (q+1)) = 1` says `C (q+1) = (u v)⁻¹` too, contradicting `C 0 ≠ C (q+1)`.
Therefore `g ≠ 1` has at least `q` square roots, and AVW Lemma 6.2 gives `2q ≤ |G|`. -/
theorem two_mul_le_card_of_coppersmithWinogradRelations
    {G : Type v} [CommGroup G] [Fintype G] [DecidableEq G] {q : ℕ}
    {A B C : CWIndex q → G}
    (hA : Function.Injective fun i : Fin q ↦ A (.middle i))
    (hC : C .zero ≠ C .last)
    (h011 : ∀ i : Fin q, A .zero * B (.middle i) * C (.middle i) = 1)
    (h101 : ∀ i : Fin q, A (.middle i) * B .zero * C (.middle i) = 1)
    (h110 : ∀ i : Fin q, A (.middle i) * B (.middle i) * C .zero = 1)
    (h002 : A .zero * B .zero * C .last = 1) :
    2 * q ≤ Fintype.card G := by
  classical
  set u : G := A .zero with hu
  set v : G := B .zero with hv
  set w : G := C .zero with hw
  -- Every middle `X`-label squares to the same element of `G`.
  have hsq : ∀ i : Fin q, A (.middle i) * A (.middle i) = u * w⁻¹ * v⁻¹ := by
    intro i
    have hc1 : C (.middle i) = (u * B (.middle i))⁻¹ := eq_inv_of_mul_eq_one_right (h011 i)
    have hc2 : C (.middle i) = (A (.middle i) * v)⁻¹ := eq_inv_of_mul_eq_one_right (h101 i)
    have hub : u * B (.middle i) = A (.middle i) * v := inv_injective (hc1.symm.trans hc2)
    have hab : A (.middle i) * B (.middle i) = w⁻¹ := eq_inv_of_mul_eq_one_left (h110 i)
    have hstep : A (.middle i) * A (.middle i) * v = u * w⁻¹ := by
      calc A (.middle i) * A (.middle i) * v
          = A (.middle i) * (A (.middle i) * v) := mul_assoc _ _ _
        _ = A (.middle i) * (u * B (.middle i)) := by rw [hub]
        _ = u * (A (.middle i) * B (.middle i)) := mul_left_comm _ _ _
        _ = u * w⁻¹ := by rw [hab]
    calc A (.middle i) * A (.middle i)
        = A (.middle i) * A (.middle i) * v * v⁻¹ := by
          rw [mul_assoc, mul_inv_cancel, mul_one]
      _ = u * w⁻¹ * v⁻¹ := by rw [hstep]
  -- The common square of the translated labels.
  set g : G := u * w⁻¹ * v⁻¹ * (u⁻¹ * u⁻¹) with hgdef
  have hgne : g ≠ 1 := by
    intro hone
    have h1 : u * w⁻¹ * v⁻¹ = (u⁻¹ * u⁻¹)⁻¹ := eq_inv_of_mul_eq_one_left hone
    have h2 : u * (w⁻¹ * v⁻¹) = u * u := by
      rw [← mul_assoc, h1]
      simp
    have h3 : w⁻¹ * v⁻¹ = u := mul_left_cancel h2
    have h4 : u * v = w⁻¹ := by
      calc u * v = w⁻¹ * v⁻¹ * v := by rw [h3]
        _ = w⁻¹ := by rw [mul_assoc, inv_mul_cancel, mul_one]
    have h5 : C .last = (u * v)⁻¹ := eq_inv_of_mul_eq_one_right h002
    exact hC (by rw [h5, h4, inv_inv])
  have hroot : ∀ i : Fin q, (A (.middle i) * u⁻¹) * (A (.middle i) * u⁻¹) = g := by
    intro i
    calc (A (.middle i) * u⁻¹) * (A (.middle i) * u⁻¹)
        = A (.middle i) * A (.middle i) * (u⁻¹ * u⁻¹) := mul_mul_mul_comm _ _ _ _
      _ = u * w⁻¹ * v⁻¹ * (u⁻¹ * u⁻¹) := by rw [hsq i]
      _ = g := hgdef.symm
  have hinj : Function.Injective fun i : Fin q ↦ A (.middle i) * u⁻¹ := by
    intro i j hij
    have hij' : A (.middle i) * u⁻¹ = A (.middle j) * u⁻¹ := hij
    exact hA (mul_right_cancel hij')
  have hqcard : q ≤ (squareRootFinset G g).card := by
    have hle := Finset.card_le_card_of_injOn (s := (Finset.univ : Finset (Fin q)))
      (t := squareRootFinset G g) (fun i ↦ A (.middle i) * u⁻¹)
      (fun i _ ↦ mem_squareRootFinset.mpr (hroot i)) (fun i _ j _ h ↦ hinj h)
    simpa using hle
  calc 2 * q ≤ 2 * (squareRootFinset G g).card := Nat.mul_le_mul_left 2 hqcard
    _ ≤ Fintype.card G := two_mul_card_squareRootFinset_le hgne

/-! ## AVW Lemma 6.3 -/

section Exclusion

variable {K : Type u} [CommSemiring K] [Nontrivial K]
variable {G : Type v} [CommGroup G] [Fintype G] [DecidableEq G] {q : ℕ}

/-- **AVW Lemma 6.3** in the symmetric group-tensor convention `T_G = ∑ x_a y_b z_{(ab)⁻¹}` of
`Tensor/GroupTensor.lean`: for an abelian group `G` with `|G| < 2q`, the Coppersmith--Winograd
tensor `CW_q` is not a sub-tensor of `T_G`.

Proof sketch: a sub-tensor witness supplies leg injections `A = f X`, `B = f Y`, `C = f Z` from
`CWIndex q` to `G`.  Every coefficient of `CW_q` equal to `1` must be matched by a coefficient `1`
of `T_G` at the relabelled address, and the support formula for `T_G` turns each such match into the
group equation `A x · B y · C z = 1`.  Feeding the six CW support families into
`two_mul_le_card_of_coppersmithWinogradRelations` gives `2q ≤ |G|`, contradicting the hypothesis. -/
theorem not_isSubTensor_coppersmithWinograd_groupTensor (hcard : Fintype.card G < 2 * q) :
    ¬ IsSubTensor (coppersmithWinograd K q) (groupTensor K G) := by
  classical
  rintro ⟨f, hinj, hf⟩
  have hsub : IsSubTensorVia f (coppersmithWinograd K q) (groupTensor K G) := ⟨hinj, hf⟩
  -- Each supported CW address becomes a group equation.
  have key : ∀ x y z : CWIndex q,
      standardCoordinateEquiv (K := K) (κ := CWCoordIndex q) (coppersmithWinograd K q)
          (ofLegs x y z) = 1 →
        f .X x * f .Y y * f .Z z = 1 := by
    intro x y z hxyz
    have h := hsub.coeff_eq_one hxyz
    rw [standardCoordinateEquiv_groupTensor] at h
    split_ifs at h with hc
    · exact hc
    · exact absurd h.symm one_ne_zero
  have hAinj : Function.Injective fun i : Fin q ↦ f .X (.middle i) := by
    intro i j hij
    have := hinj .X hij
    simpa using this
  have hCne : f .Z .zero ≠ f .Z .last := by
    intro h
    exact absurd (hinj .Z h) (by simp)
  have hle := two_mul_le_card_of_coppersmithWinogradRelations (G := G) (q := q)
    (A := f .X) (B := f .Y) (C := f .Z) hAinj hCne
    (fun i ↦ key _ _ _ (standardCoordinateEquiv_coppersmithWinograd_011 K q i))
    (fun i ↦ key _ _ _ (standardCoordinateEquiv_coppersmithWinograd_101 K q i))
    (fun i ↦ key _ _ _ (standardCoordinateEquiv_coppersmithWinograd_110 K q i))
    (key _ _ _ (standardCoordinateEquiv_coppersmithWinograd_002 K q))
  omega

/-- **AVW Lemma 6.3** in the multiplicative convention `T_G = ∑ x_a y_b z_{ab}` printed as AVW
Definition 3.2: for an abelian group `G` with `|G| < 2q`, `CW_q` is not a sub-tensor of `T_G`.

Proof sketch: identical to the symmetric-convention statement, except that the support formula now
reads `A x · B y = C z`; composing the `Z`-leg injection with inversion of `G` -- still an
injection -- turns those equations into the `A x · B y · C' z = 1` form consumed by
`two_mul_le_card_of_coppersmithWinogradRelations`. -/
theorem not_isSubTensor_coppersmithWinograd_groupTensorMul (hcard : Fintype.card G < 2 * q) :
    ¬ IsSubTensor (coppersmithWinograd K q) (groupTensorMul K G) := by
  classical
  rintro ⟨f, hinj, hf⟩
  have hsub : IsSubTensorVia f (coppersmithWinograd K q) (groupTensorMul K G) := ⟨hinj, hf⟩
  have key : ∀ x y z : CWIndex q,
      standardCoordinateEquiv (K := K) (κ := CWCoordIndex q) (coppersmithWinograd K q)
          (ofLegs x y z) = 1 →
        f .X x * f .Y y * (f .Z z)⁻¹ = 1 := by
    intro x y z hxyz
    have h := hsub.coeff_eq_one hxyz
    rw [standardCoordinateEquiv_groupTensorMul] at h
    split_ifs at h with hc
    · show f .X x * f .Y y * (f .Z z)⁻¹ = 1
      rw [show f .X x * f .Y y = f .Z z from hc, mul_inv_cancel]
    · exact absurd h.symm one_ne_zero
  have hAinj : Function.Injective fun i : Fin q ↦ f .X (.middle i) := by
    intro i j hij
    have := hinj .X hij
    simpa using this
  have hCne : (f .Z .zero)⁻¹ ≠ (f .Z .last)⁻¹ := by
    intro h
    exact absurd (hinj .Z (inv_injective h)) (by simp)
  have hle := two_mul_le_card_of_coppersmithWinogradRelations (G := G) (q := q)
    (A := f .X) (B := f .Y) (C := fun x ↦ (f .Z x)⁻¹) hAinj hCne
    (fun i ↦ key _ _ _ (standardCoordinateEquiv_coppersmithWinograd_011 K q i))
    (fun i ↦ key _ _ _ (standardCoordinateEquiv_coppersmithWinograd_101 K q i))
    (fun i ↦ key _ _ _ (standardCoordinateEquiv_coppersmithWinograd_110 K q i))
    (key _ _ _ (standardCoordinateEquiv_coppersmithWinograd_002 K q))
  omega

/-- The same exclusion for the stricter zeroing-out relation: `CW_q` is not the sub-tensor of `T_G`
induced by any triple of leg injections, when `G` is abelian with `|G| < 2q`. -/
theorem not_isInducedSubTensor_coppersmithWinograd_groupTensor (hcard : Fintype.card G < 2 * q) :
    ¬ IsInducedSubTensor (coppersmithWinograd K q) (groupTensor K G) := fun h ↦
  not_isSubTensor_coppersmithWinograd_groupTensor hcard h.isSubTensor

/-- **The abelian half of AVW Theorem 6.2**, in the generality Lemma 6.3 supports: for every
`q ≥ 3`, the Coppersmith--Winograd tensor `CW_q` is not a sub-tensor of the group tensor of an
abelian group of order exactly `q + 2`.

Proof sketch: `q + 2 < 2q` for `q ≥ 3`, so this is a special case of
`not_isSubTensor_coppersmithWinograd_groupTensor`.  AVW state Theorem 6.2 for `q = 3, …, 9` and
handle the nonabelian orders `q + 2` with `q = 4, 6, 8` separately; those four groups are outside
the scope of this file. -/
theorem not_isSubTensor_coppersmithWinograd_groupTensor_of_card_eq
    (hq : 3 ≤ q) (hcard : Fintype.card G = q + 2) :
    ¬ IsSubTensor (coppersmithWinograd K q) (groupTensor K G) :=
  not_isSubTensor_coppersmithWinograd_groupTensor (by omega)

end Exclusion

end AlgebraicComplexity.Examples
