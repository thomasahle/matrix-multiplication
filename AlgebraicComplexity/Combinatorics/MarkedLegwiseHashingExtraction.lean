/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Combinatorics.LegwiseHashingExtraction

/-!
# Legwise hashing with a marked target family

Classical tensor-square laser arguments distinguish two finite families.  The ambient family
contains every constituent word surviving the legwise marginal zeroing, while the marked family
contains the one joint type whose value will be counted.  A marked target must be isolated against
all ambient competitors; counting only competitors from the marked family would not justify the
subsequent variable zeroing.

This module supplies that reusable variant of affine hashing.  The good-seed averaging is applied
to the marked targets, but each target's alternative-index list is computed in the ambient family.
The resulting marked targets are contained in the ordinary ambient hash filter and are unique
against every ambient survivor on every tensor leg.
-/

namespace AlgebraicComplexity

universe u v

namespace ProgressionHash.LegalTriple

variable {R : Type u} [Field R]
variable {ι : Type v} [Fintype ι]
variable {target : R}

/-- Marked targets isolated using competitor lists from a possibly larger ambient family. -/
noncomputable def markedLegwiseIsolatedTargets
    (ambient marked : Finset (LegalTriple R ι target)) (B : Finset R)
    (seed : ProgressionHash.Seed R ι) : Finset (LegalTriple R ι target) :=
  ProgressionHash.Seed.isolatedTargets marked B LegalTriple.xIndex LegalTriple.yIndex
    (legwiseCompetitorYIndices ambient) seed

/-- Marked isolation never introduces a target outside the marked family. -/
theorem markedLegwiseIsolatedTargets_subset_marked
    (ambient marked : Finset (LegalTriple R ι target)) (B : Finset R)
    (seed : ProgressionHash.Seed R ι) :
    markedLegwiseIsolatedTargets ambient marked B seed ⊆ marked := by
  classical
  intro triple htriple
  unfold markedLegwiseIsolatedTargets ProgressionHash.Seed.isolatedTargets at htriple
  obtain ⟨pair, hpair, hfirst⟩ := Finset.mem_image.mp htriple
  subst triple
  unfold ProgressionHash.Seed.isolatedIncidences at hpair
  exact (Finset.mem_product.mp (Finset.mem_filter.mp hpair).1).1

/-- A marked target isolated against the ambient family is one of the ordinary ambient isolated
targets.

Proof sketch: an isolated target is the first projection of a target/bucket incidence.  Replace
the marked membership of that incidence by ambient membership; its hash and collision-avoidance
conditions are unchanged. -/
theorem markedLegwiseIsolatedTargets_subset_legwiseIsolatedTargets
    (ambient marked : Finset (LegalTriple R ι target))
    (hmarked : marked ⊆ ambient) (B : Finset R)
    (seed : ProgressionHash.Seed R ι) :
    markedLegwiseIsolatedTargets ambient marked B seed ⊆
      legwiseIsolatedTargets ambient B seed := by
  classical
  intro triple htriple
  unfold markedLegwiseIsolatedTargets ProgressionHash.Seed.isolatedTargets at htriple
  unfold legwiseIsolatedTargets ProgressionHash.Seed.isolatedTargets
  obtain ⟨pair, hpair, rfl⟩ := Finset.mem_image.mp htriple
  apply Finset.mem_image.mpr
  refine ⟨pair, ?_, rfl⟩
  unfold ProgressionHash.Seed.isolatedIncidences at hpair ⊢
  obtain ⟨hpairProduct, hevent⟩ := Finset.mem_filter.mp hpair
  obtain ⟨hpairMarked, hb⟩ := Finset.mem_product.mp hpairProduct
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_product.mpr ⟨hmarked hpairMarked, hb⟩, hevent⟩

/-- Marked ambient-isolated targets survive the ordinary three-leg hash filter on the ambient
family. -/
theorem markedLegwiseIsolatedTargets_subset_filteredTargets [NeZero (2 : R)]
    (ambient marked : Finset (LegalTriple R ι target))
    (hmarked : marked ⊆ ambient) (B : Finset R)
    (seed : ProgressionHash.Seed R ι) :
    markedLegwiseIsolatedTargets ambient marked B seed ⊆
      filteredTargets ambient B seed :=
  (markedLegwiseIsolatedTargets_subset_legwiseIsolatedTargets
      ambient marked hmarked B seed).trans
    (legwiseIsolatedTargets_subset_filteredTargets ambient B seed)

/-- A marked isolated target is the unique ambient hash survivor using any one of its leg words.

This is the semantic property needed to zero the filtered partition down to the marked direct
sum: retaining a selected block cannot accidentally retain an unmarked constituent. -/
theorem eq_of_mem_markedLegwiseIsolatedTargets_of_mem_filteredTargets
    [NeZero (2 : R)]
    (ambient marked : Finset (LegalTriple R ι target))
    (hmarked : marked ⊆ ambient) (B : Finset R) (hB : ThreeAPFree (B : Set R))
    (seed : ProgressionHash.Seed R ι)
    {triple other : LegalTriple R ι target}
    (htriple : triple ∈ markedLegwiseIsolatedTargets ambient marked B seed)
    (hother : other ∈ filteredTargets ambient B seed)
    (leg : Tensor.Leg) (hleg : other.legIndex leg = triple.legIndex leg) :
    other = triple := by
  exact eq_of_mem_legwiseIsolatedTargets_of_mem_filteredTargets ambient B hB seed
    (markedLegwiseIsolatedTargets_subset_legwiseIsolatedTargets
      ambient marked hmarked B seed htriple) hother leg hleg

/-- Marked ambient-isolated targets have pairwise distinct block words on every leg. -/
theorem legIndex_injectiveOn_markedLegwiseIsolatedTargets [NeZero (2 : R)]
    (ambient marked : Finset (LegalTriple R ι target))
    (hmarked : marked ⊆ ambient) (B : Finset R) (hB : ThreeAPFree (B : Set R))
    (seed : ProgressionHash.Seed R ι) (leg : Tensor.Leg) :
    Set.InjOn (fun triple : LegalTriple R ι target => triple.legIndex leg)
      (markedLegwiseIsolatedTargets ambient marked B seed : Set _) :=
  (legIndex_injectiveOn_legwiseIsolatedTargets ambient B hB seed leg).mono
    (markedLegwiseIsolatedTargets_subset_legwiseIsolatedTargets
      ambient marked hmarked B seed)

/-- Complete marked finite legwise extraction.

The lower count uses the marked-family cardinality.  The degree hypothesis and every uniqueness
conclusion use ambient competitor lists, so the theorem remains sound when many unmarked joint
types share the same three marginal types. -/
theorem exists_seed_many_markedLegwiseIsolatedTargets
    [Fintype R] [NeZero (2 : R)]
    (ambient marked : Finset (LegalTriple R ι target))
    (hmarked : marked ⊆ ambient) (B : Finset R) (hB : ThreeAPFree (B : Set R))
    (hquarter : ∀ triple ∈ marked,
      4 * (legwiseCompetitorYIndices ambient triple).card ≤ Fintype.card R) :
    ∃ seed : ProgressionHash.Seed R ι,
      3 * marked.card * B.card ≤
          4 * (Fintype.card R * Fintype.card R) *
            (markedLegwiseIsolatedTargets ambient marked B seed).card ∧
        markedLegwiseIsolatedTargets ambient marked B seed ⊆
          filteredTargets ambient B seed ∧
        ∀ leg, Set.InjOn
          (fun triple : LegalTriple R ι target => triple.legIndex leg)
          (markedLegwiseIsolatedTargets ambient marked B seed : Set _) := by
  classical
  have hdistinct : ∀ triple ∈ marked,
      ∀ J' ∈ legwiseCompetitorYIndices ambient triple, J' ≠ triple.yIndex := by
    intro triple _htriple J' hJ'
    exact yIndex_ne_of_mem_legwiseCompetitorYIndices ambient triple hJ'
  obtain ⟨seed, hcount⟩ := ProgressionHash.Seed.exists_seed_many_isolatedTargets
    marked B LegalTriple.xIndex LegalTriple.yIndex
      (legwiseCompetitorYIndices ambient) hdistinct hquarter
  refine ⟨seed, ?_,
    markedLegwiseIsolatedTargets_subset_filteredTargets ambient marked hmarked B seed,
    ?_⟩
  · simpa [markedLegwiseIsolatedTargets] using hcount
  · intro leg
    exact legIndex_injectiveOn_markedLegwiseIsolatedTargets
      ambient marked hmarked B hB seed leg

end ProgressionHash.LegalTriple

end AlgebraicComplexity
