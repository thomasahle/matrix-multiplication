/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Combinatorics.HashingExtraction

/-!
# Marked X-only isolation by affine hashing

Layer 2 (`AlgebraicComplexity/Combinatorics/`).  This module supplies the marked/ambient form of
the one-leg extraction used by the recursive constituent theorem of

> J. Alman, R. Duan, V. Vassilevska Williams, Y. Xu, Z. Xu and R. Zhou,
> *More Asymmetry Yields Faster Matrix Multiplication*, SODA 2025,
> subsection "More Asymmetric Hashing".

There are two finite target families.  The ambient family contains every triple having the three
prescribed marginal types (`N_triple` in the paper), while the marked subfamily has the prescribed
joint type (`N_alpha`).  The affine seed is averaged over marked targets, so the retained count is
measured against `marked.card`.  A marked target is nevertheless isolated against every competing
Y-word in its **ambient** X-fiber.  This is what permits the X-variable zero-out without deleting
the hash-loss ratio `N_alpha / N_triple`.

Only X is isolated.  No uniqueness conclusion is made on Y or Z: the paper deliberately leaves
those collisions for its compatibility and usefulness zero-outs.  Thus this theorem is strictly
different from both `MarkedTwoLegHashingExtraction` (the Duan--Wu--Zhou X/Y extractor) and
`MarkedLegwiseHashingExtraction` (the three-leg extractor used by ordinary laser clients).

The principal theorem is `exists_seed_many_markedXIsolatedTargets`.  It has the anti-laundering
shape needed by clients:

* the count is against the marked family;
* the competitor bound is computed in the ambient family;
* the result survives the ambient common-bucket filter; and
* X is injective on the selected family, while
  `eq_of_mem_markedXIsolatedTargets_of_mem_filteredTargets` proves the stronger fact that a
  selected X-word occurs in no other ambient filtered target.

At `marked = ambient`, the construction is definitionally the unmarked `xIsolatedTargets` and the
main theorem specializes back to `exists_seed_many_xIsolatedTargets`.  This regression prevents
the two family roles from drifting.
-/

namespace AlgebraicComplexity

universe u v

namespace ProgressionHash.LegalTriple

variable {R : Type u} [Field R]
variable {ι : Type v} [Fintype ι]
variable {target : R}

/-- X-competitor lists are monotone in the target family from which they are drawn.

In particular, using the marked family instead of the ambient family can only remove collision
proxies and is therefore not sound for the later ambient X-variable zero-out. -/
theorem xCompetitorYIndices_subset_of_subset
    {small large : Finset (LegalTriple R ι target)} (hsubset : small ⊆ large)
    (triple : LegalTriple R ι target) :
    xCompetitorYIndices small triple ⊆ xCompetitorYIndices large triple := by
  classical
  intro J' hJ'
  rw [xCompetitorYIndices, Finset.mem_image] at hJ' ⊢
  obtain ⟨other, hother, rfl⟩ := hJ'
  refine ⟨other, ?_, rfl⟩
  obtain ⟨herase, hx⟩ := Finset.mem_filter.mp hother
  obtain ⟨hne, hmem⟩ := Finset.mem_erase.mp herase
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_erase.mpr ⟨hne, hsubset hmem⟩, hx⟩

/-- Marked targets isolated on X against competitor lists from a possibly larger ambient family.

The target incidence is drawn from `marked`, but the alternative Y-words are computed from
`ambient`. -/
noncomputable def markedXIsolatedTargets
    (ambient marked : Finset (LegalTriple R ι target)) (B : Finset R)
    (seed : Seed R ι) : Finset (LegalTriple R ι target) :=
  Seed.isolatedTargets marked B LegalTriple.xIndex LegalTriple.yIndex
    (xCompetitorYIndices ambient) seed

/-- Marked X-isolation never introduces a target outside the marked family. -/
theorem markedXIsolatedTargets_subset_marked
    (ambient marked : Finset (LegalTriple R ι target)) (B : Finset R)
    (seed : Seed R ι) :
    markedXIsolatedTargets ambient marked B seed ⊆ marked := by
  classical
  intro triple htriple
  unfold markedXIsolatedTargets Seed.isolatedTargets at htriple
  obtain ⟨pair, hpair, hfirst⟩ := Finset.mem_image.mp htriple
  subst triple
  unfold Seed.isolatedIncidences at hpair
  exact (Finset.mem_product.mp (Finset.mem_filter.mp hpair).1).1

/-- The retained count cannot exceed the marked count `N_alpha`. -/
theorem card_markedXIsolatedTargets_le_card_marked
    (ambient marked : Finset (LegalTriple R ι target)) (B : Finset R)
    (seed : Seed R ι) :
    (markedXIsolatedTargets ambient marked B seed).card ≤ marked.card :=
  Finset.card_le_card (markedXIsolatedTargets_subset_marked ambient marked B seed)

/-- A marked target isolated against ambient competitors belongs to the ordinary ambient
X-isolated family.

Proof sketch: replace the marked membership of the target/bucket incidence by ambient membership.
The common-bucket condition and the competitor-avoidance condition are unchanged because the
competitor list was already computed in the ambient family. -/
theorem markedXIsolatedTargets_subset_xIsolatedTargets
    (ambient marked : Finset (LegalTriple R ι target))
    (hmarked : marked ⊆ ambient) (B : Finset R) (seed : Seed R ι) :
    markedXIsolatedTargets ambient marked B seed ⊆
      xIsolatedTargets ambient B seed := by
  classical
  intro triple htriple
  unfold markedXIsolatedTargets Seed.isolatedTargets at htriple
  unfold xIsolatedTargets Seed.isolatedTargets
  obtain ⟨pair, hpair, rfl⟩ := Finset.mem_image.mp htriple
  apply Finset.mem_image.mpr
  refine ⟨pair, ?_, rfl⟩
  unfold Seed.isolatedIncidences at hpair ⊢
  obtain ⟨hpairProduct, hevent⟩ := Finset.mem_filter.mp hpair
  obtain ⟨hpairMarked, hb⟩ := Finset.mem_product.mp hpairProduct
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_product.mpr ⟨hmarked hpairMarked, hb⟩, hevent⟩

/-- Every marked X-isolated target survives the three-leg hash filter of the ambient family. -/
theorem markedXIsolatedTargets_subset_filteredTargets [NeZero (2 : R)]
    (ambient marked : Finset (LegalTriple R ι target))
    (hmarked : marked ⊆ ambient) (B : Finset R) (seed : Seed R ι) :
    markedXIsolatedTargets ambient marked B seed ⊆
      filteredTargets ambient B seed :=
  (markedXIsolatedTargets_subset_xIsolatedTargets
      ambient marked hmarked B seed).trans
    (xIsolatedTargets_subset_filteredTargets ambient B seed)

/-- A selected target is the unique survivor in its entire ambient X-fiber.

This statement, rather than mere pairwise injectivity within the selected family, licenses the
X-variable zero-out: retaining a selected X-block cannot accidentally retain an unmarked ambient
constituent. -/
theorem eq_of_mem_markedXIsolatedTargets_of_mem_filteredTargets [NeZero (2 : R)]
    (ambient marked : Finset (LegalTriple R ι target))
    (hmarked : marked ⊆ ambient) (B : Finset R) (hB : ThreeAPFree (B : Set R))
    (seed : Seed R ι)
    {triple other : LegalTriple R ι target}
    (htriple : triple ∈ markedXIsolatedTargets ambient marked B seed)
    (hother : other ∈ filteredTargets ambient B seed)
    (hx : other.xIndex = triple.xIndex) :
    other = triple :=
  eq_of_mem_xIsolatedTargets_of_mem_filteredTargets ambient B hB seed
    (markedXIsolatedTargets_subset_xIsolatedTargets
      ambient marked hmarked B seed htriple)
    hother hx

/-- Selected marked targets have pairwise distinct X words.  No assertion is made about Y or Z. -/
theorem xIndex_injectiveOn_markedXIsolatedTargets
    (ambient marked : Finset (LegalTriple R ι target))
    (hmarked : marked ⊆ ambient) (B : Finset R) (seed : Seed R ι) :
    Set.InjOn (fun triple : LegalTriple R ι target ↦ triple.xIndex)
      (markedXIsolatedTargets ambient marked B seed : Set _) := by
  apply Seed.xIndex_injectiveOn_isolatedTargets marked B LegalTriple.xIndex
    LegalTriple.yIndex (xCompetitorYIndices ambient) seed
  intro triple htriple other hother hne hx
  exact yIndex_mem_xCompetitorYIndices ambient (hmarked hother) hne hx

/-- **Complete marked finite X-only extraction.**

There is one affine seed for which many marked targets survive.  The count is taken against
`marked.card`; every competitor and the hash filter use `ambient`; and the only isolation output
is X-injectivity.  This is the exact finite hashing interface of the recursive constituent proof.
-/
theorem exists_seed_many_markedXIsolatedTargets [Fintype R] [NeZero (2 : R)]
    (ambient marked : Finset (LegalTriple R ι target))
    (hmarked : marked ⊆ ambient) (B : Finset R)
    (hquarter : ∀ triple ∈ marked,
      4 * (xCompetitorYIndices ambient triple).card ≤ Fintype.card R) :
    ∃ seed : Seed R ι,
      3 * marked.card * B.card ≤
          4 * (Fintype.card R * Fintype.card R) *
            (markedXIsolatedTargets ambient marked B seed).card ∧
        markedXIsolatedTargets ambient marked B seed ⊆
          filteredTargets ambient B seed ∧
        Set.InjOn (fun triple : LegalTriple R ι target ↦ triple.xIndex)
          (markedXIsolatedTargets ambient marked B seed : Set _) := by
  classical
  have hdistinct : ∀ triple ∈ marked,
      ∀ J' ∈ xCompetitorYIndices ambient triple, J' ≠ triple.yIndex := by
    intro triple _htriple J' hJ'
    exact yIndex_ne_of_mem_xCompetitorYIndices ambient triple hJ'
  obtain ⟨seed, hcount⟩ := Seed.exists_seed_many_isolatedTargets marked B
    LegalTriple.xIndex LegalTriple.yIndex (xCompetitorYIndices ambient)
    hdistinct hquarter
  refine ⟨seed, ?_,
    markedXIsolatedTargets_subset_filteredTargets ambient marked hmarked B seed,
    xIndex_injectiveOn_markedXIsolatedTargets ambient marked hmarked B seed⟩
  simpa [markedXIsolatedTargets] using hcount

/-- The paper's convenient modulus hypothesis in marked/ambient form.

An eight-times bound on every marked target's **ambient** X-fiber implies the four-times bound on
its ambient competitor proxy list.  The constant is deliberately left in this conservative form,
matching the constituent theorem's choice `M_0 >= 8 N_triple / N_X`. -/
theorem markedX_competitor_quarter_of_eight_mul_ambient_xFiber_le [Fintype R]
    (ambient marked : Finset (LegalTriple R ι target))
    (hdegree : ∀ triple ∈ marked,
      8 * (xFiber ambient triple).card ≤ Fintype.card R) :
    ∀ triple ∈ marked,
      4 * (xCompetitorYIndices ambient triple).card ≤ Fintype.card R := by
  intro triple htriple
  calc
    4 * (xCompetitorYIndices ambient triple).card ≤
        4 * (xFiber ambient triple).card :=
      Nat.mul_le_mul_left 4
        (card_xCompetitorYIndices_le_card_xFiber ambient triple)
    _ ≤ 8 * (xFiber ambient triple).card := by omega
    _ ≤ Fintype.card R := hdegree triple htriple

/-- Marked X-only extraction under the paper's abstract ambient X-fiber modulus bound. -/
theorem exists_seed_many_markedXIsolatedTargets_of_modulus
    [Fintype R] [NeZero (2 : R)]
    (ambient marked : Finset (LegalTriple R ι target))
    (hmarked : marked ⊆ ambient) (B : Finset R)
    (hdegree : ∀ triple ∈ marked,
      8 * (xFiber ambient triple).card ≤ Fintype.card R) :
    ∃ seed : Seed R ι,
      3 * marked.card * B.card ≤
          4 * (Fintype.card R * Fintype.card R) *
            (markedXIsolatedTargets ambient marked B seed).card ∧
        markedXIsolatedTargets ambient marked B seed ⊆
          filteredTargets ambient B seed ∧
        Set.InjOn (fun triple : LegalTriple R ι target ↦ triple.xIndex)
          (markedXIsolatedTargets ambient marked B seed : Set _) :=
  exists_seed_many_markedXIsolatedTargets ambient marked hmarked B
    (markedX_competitor_quarter_of_eight_mul_ambient_xFiber_le
      ambient marked hdegree)

/-! ### Regression against the unmarked X-only theorem -/

/-- At `marked = ambient`, marked X-only isolation is definitionally ordinary X-only isolation. -/
theorem markedXIsolatedTargets_self
    (targets : Finset (LegalTriple R ι target)) (B : Finset R) (seed : Seed R ι) :
    markedXIsolatedTargets targets targets B seed = xIsolatedTargets targets B seed := rfl

/-- Specializing the marked theorem to equal families reproduces the unmarked extraction theorem. -/
theorem exists_seed_many_xIsolatedTargets_of_marked [Fintype R] [NeZero (2 : R)]
    (targets : Finset (LegalTriple R ι target)) (B : Finset R)
    (hquarter : ∀ triple ∈ targets,
      4 * (xCompetitorYIndices targets triple).card ≤ Fintype.card R) :
    ∃ seed : Seed R ι,
      3 * targets.card * B.card ≤
          4 * (Fintype.card R * Fintype.card R) *
            (xIsolatedTargets targets B seed).card ∧
        xIsolatedTargets targets B seed ⊆ filteredTargets targets B seed ∧
        Set.InjOn (fun triple : LegalTriple R ι target ↦ triple.xIndex)
          (xIsolatedTargets targets B seed : Set _) := by
  simpa only [markedXIsolatedTargets_self] using
    exists_seed_many_markedXIsolatedTargets targets targets
      (Finset.Subset.refl targets) B hquarter

end ProgressionHash.LegalTriple

end AlgebraicComplexity
