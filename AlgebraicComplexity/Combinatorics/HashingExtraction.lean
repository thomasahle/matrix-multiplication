/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Combinatorics.HashingIsolation

/-!
# Progression-free filtering and asymmetric extraction

This module packages the combinatorial hashing layer in the form used by laser-method clients.
A `LegalTriple` records the three block-index words and their coordinatewise sum constraint.
Progression-free filtering forces every surviving legal triple into one common bucket.  We then
construct, from a finite target family, the complete list of competing `Y`-indices sharing each
target's `X`-index and apply the finite good-seed theorem from `HashingIsolation`.

The resulting family is large in the precise division-free sense used by the papers, consists of
triples that survive the three-leg progression-free zero-out, and has pairwise distinct
`X`-indices.  This is the full combinatorial content of the more-asymmetric hashing cleanup; later
compatibility zero-outs are responsible for uniqueness on the finer `Y`- and `Z`-interfaces.
-/

namespace AlgebraicComplexity

universe u v

namespace ProgressionHash

/-- A block triple whose three index words have a fixed coordinatewise sum. -/
@[ext]
structure LegalTriple (R : Type u) [Add R] (ι : Type v) (target : R) where
  xIndex : ι → R
  yIndex : ι → R
  zIndex : ι → R
  legal : ∀ i, xIndex i + yIndex i + zIndex i = target

namespace LegalTriple

variable {R : Type u} [Field R]
variable {ι : Type v} [Fintype ι]
variable {target : R}

omit [Fintype ι] in
/-- For a fixed target sum, the `X`- and `Y`-words determine the `Z`-word. -/
theorem eq_of_xIndex_eq_yIndex_eq {left right : LegalTriple R ι target}
    (hx : left.xIndex = right.xIndex) (hy : left.yIndex = right.yIndex) :
    left = right := by
  apply LegalTriple.ext hx hy
  funext i
  have hleft := left.legal i
  have hright := right.legal i
  rw [congrFun hx i, congrFun hy i] at hleft
  linear_combination hleft - hright

/-- A legal triple survives the three independent hash-membership zero-outs. -/
def SurvivesHashFilter (B : Set R) (seed : Seed R ι)
    (triple : LegalTriple R ι target) : Prop :=
  seed.xHash triple.xIndex ∈ B ∧
    seed.yHash triple.yIndex ∈ B ∧
    seed.zHash target triple.zIndex ∈ B

/-- Progression-free filtering is exactly common-bucket filtering for legal triples. -/
theorem survivesHashFilter_iff_exists_commonBucket [NeZero (2 : R)]
    {B : Set R} (hB : ThreeAPFree B) (seed : Seed R ι)
    (triple : LegalTriple R ι target) :
    SurvivesHashFilter B seed triple ↔
      ∃ b ∈ B, Seed.InCommonBucket triple.xIndex triple.yIndex b seed := by
  constructor
  · rintro ⟨hX, hY, hZ⟩
    obtain ⟨hXY, _hYZ⟩ := surviving_hashes_equal hB seed.offset seed.shift target
      seed.weights triple.xIndex triple.yIndex triple.zIndex triple.legal hX hY hZ
    refine ⟨seed.xHash triple.xIndex, hX, rfl, ?_⟩
    exact hXY.symm
  · rintro ⟨b, hb, hX, hY⟩
    have hZ : seed.zHash target triple.zIndex = b :=
      Seed.zHash_eq_of_commonBucket seed triple.xIndex triple.yIndex triple.zIndex
        target b triple.legal ⟨hX, hY⟩
    constructor
    · simpa [hX] using hb
    constructor
    · simpa [hY] using hb
    · simpa [hZ] using hb

/-- Finite set of target triples surviving the progression-free three-leg zero-out. -/
noncomputable def filteredTargets (targets : Finset (LegalTriple R ι target))
    (B : Finset R) (seed : Seed R ι) : Finset (LegalTriple R ι target) := by
  classical
  exact targets.filter fun triple => SurvivesHashFilter (B : Set R) seed triple

/-- Hash filtering only removes targets. -/
theorem filteredTargets_subset
    (targets : Finset (LegalTriple R ι target)) (B : Finset R) (seed : Seed R ι) :
    filteredTargets targets B seed ⊆ targets := by
  classical
  intro triple htriple
  exact (Finset.mem_filter.mp htriple).1

@[simp] theorem mem_filteredTargets [NeZero (2 : R)]
    (targets : Finset (LegalTriple R ι target)) (B : Finset R)
    (hB : ThreeAPFree (B : Set R)) (seed : Seed R ι) (triple : LegalTriple R ι target) :
    triple ∈ filteredTargets targets B seed ↔
      triple ∈ targets ∧
        ∃ b ∈ B, Seed.InCommonBucket triple.xIndex triple.yIndex b seed := by
  classical
  rw [filteredTargets, Finset.mem_filter,
    survivesHashFilter_iff_exists_commonBucket hB]
  constructor <;> rintro ⟨ht, b, hb, hcommon⟩ <;>
    exact ⟨ht, b, hb, hcommon⟩

/-- Distinct competing `Y`-indices belonging to other targets with the same `X`-index. -/
noncomputable def xCompetitorYIndices
    (targets : Finset (LegalTriple R ι target)) (triple : LegalTriple R ι target) :
    Finset (ι → R) := by
  classical
  exact ((targets.erase triple).filter fun other =>
    other.xIndex = triple.xIndex).image LegalTriple.yIndex

/-- All targets using the same `X`-index as `triple`, including `triple` itself when present. -/
noncomputable def xFiber
    (targets : Finset (LegalTriple R ι target)) (triple : LegalTriple R ι target) :
    Finset (LegalTriple R ι target) := by
  classical
  exact targets.filter fun other => other.xIndex = triple.xIndex

/-- Distinct competing `Y`-indices are no more numerous than targets in the corresponding
`X`-fiber. -/
theorem card_xCompetitorYIndices_le_card_xFiber
    (targets : Finset (LegalTriple R ι target)) (triple : LegalTriple R ι target) :
    (xCompetitorYIndices targets triple).card ≤ (xFiber targets triple).card := by
  classical
  unfold xCompetitorYIndices xFiber
  refine (Finset.card_image_le).trans (Finset.card_le_card ?_)
  intro other hother
  obtain ⟨herase, hx⟩ := Finset.mem_filter.mp hother
  exact Finset.mem_filter.mpr ⟨(Finset.mem_erase.mp herase).2, hx⟩

/-- The paper's convenient modulus condition, stated with eight times the full `X`-fiber degree,
implies the four-times-competitor condition used by the exact `3/4` isolation theorem. -/
theorem competitor_quarter_of_eight_mul_xFiber_le
    [Fintype R]
    (targets : Finset (LegalTriple R ι target))
    (hdegree : ∀ triple ∈ targets,
      8 * (xFiber targets triple).card ≤ Fintype.card R) :
    ∀ triple ∈ targets,
      4 * (xCompetitorYIndices targets triple).card ≤ Fintype.card R := by
  intro triple htriple
  calc
    4 * (xCompetitorYIndices targets triple).card ≤
        4 * (xFiber targets triple).card :=
      Nat.mul_le_mul_left 4 (card_xCompetitorYIndices_le_card_xFiber targets triple)
    _ ≤ 8 * (xFiber targets triple).card := by omega
    _ ≤ Fintype.card R := hdegree triple htriple

/-- Every listed competitor `Y`-index differs from the intended one. -/
theorem yIndex_ne_of_mem_xCompetitorYIndices
    (targets : Finset (LegalTriple R ι target)) (triple : LegalTriple R ι target)
    {J' : ι → R} (hJ' : J' ∈ xCompetitorYIndices targets triple) :
    J' ≠ triple.yIndex := by
  classical
  rw [xCompetitorYIndices, Finset.mem_image] at hJ'
  obtain ⟨other, hother, rfl⟩ := hJ'
  have herase := (Finset.mem_filter.mp hother).1
  have hx := (Finset.mem_filter.mp hother).2
  intro hy
  have heq : other = triple := eq_of_xIndex_eq_yIndex_eq hx hy
  exact (Finset.mem_erase.mp herase).1 heq

/-- The competitor list is complete for other targets sharing the same `X`-index. -/
theorem yIndex_mem_xCompetitorYIndices
    (targets : Finset (LegalTriple R ι target)) {triple other : LegalTriple R ι target}
    (hother : other ∈ targets) (hne : other ≠ triple)
    (hx : other.xIndex = triple.xIndex) :
    other.yIndex ∈ xCompetitorYIndices targets triple := by
  classical
  rw [xCompetitorYIndices, Finset.mem_image]
  exact ⟨other, Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨hne, hother⟩, hx⟩, rfl⟩

/-- Targets isolated using the complete `X`-competitor lists. -/
noncomputable def xIsolatedTargets
    (targets : Finset (LegalTriple R ι target)) (B : Finset R) (seed : Seed R ι) :
    Finset (LegalTriple R ι target) :=
  Seed.isolatedTargets targets B LegalTriple.xIndex LegalTriple.yIndex
    (xCompetitorYIndices targets) seed

/-- Every target isolated into a bucket survives the three-leg hash filter.  This direction only
uses legality; progression-freeness is needed for the converse statement about arbitrary filtered
targets. -/
theorem xIsolatedTargets_subset_filteredTargets [NeZero (2 : R)]
    (targets : Finset (LegalTriple R ι target)) (B : Finset R)
    (seed : Seed R ι) :
    xIsolatedTargets targets B seed ⊆ filteredTargets targets B seed := by
  classical
  intro triple htriple
  have himage : triple ∈ Seed.isolatedTargets targets B LegalTriple.xIndex
      LegalTriple.yIndex (xCompetitorYIndices targets) seed := by
    simpa [xIsolatedTargets] using htriple
  obtain ⟨⟨other, b⟩, hincidence, hfst⟩ := Finset.mem_image.mp himage
  simp only at hfst
  subst other
  have hfilter := Finset.mem_filter.mp hincidence
  have htarget : triple ∈ targets := (Finset.mem_product.mp hfilter.1).1
  have hb : b ∈ B := (Finset.mem_product.mp hfilter.1).2
  have hcommon := hfilter.2.1
  have hZ : seed.zHash target triple.zIndex = b :=
    Seed.zHash_eq_of_commonBucket seed triple.xIndex triple.yIndex triple.zIndex
      target b triple.legal hcommon
  apply Finset.mem_filter.mpr
  refine ⟨htarget, ?_⟩
  exact ⟨by simpa [hcommon.1] using hb,
    by simpa [hcommon.2] using hb,
    by simpa [hZ] using hb⟩

/-- An isolated target is the unique surviving target in its entire `X`-fiber, not merely unique
among the isolated targets.  This stronger formulation is what licenses the subsequent `X`-leg
variable zero-out: retaining an isolated `X`-block cannot accidentally retain another filtered
constituent. -/
theorem eq_of_mem_xIsolatedTargets_of_mem_filteredTargets [NeZero (2 : R)]
    (targets : Finset (LegalTriple R ι target)) (B : Finset R)
    (hB : ThreeAPFree (B : Set R)) (seed : Seed R ι)
    {triple other : LegalTriple R ι target}
    (htriple : triple ∈ xIsolatedTargets targets B seed)
    (hother : other ∈ filteredTargets targets B seed)
    (hx : other.xIndex = triple.xIndex) :
    other = triple := by
  classical
  by_contra hne
  have himage : triple ∈ Seed.isolatedTargets targets B LegalTriple.xIndex
      LegalTriple.yIndex (xCompetitorYIndices targets) seed := by
    simpa [xIsolatedTargets] using htriple
  obtain ⟨⟨triple', b⟩, hincidence, hfst⟩ := Finset.mem_image.mp himage
  simp only at hfst
  subst triple'
  have hfilter := Finset.mem_filter.mp hincidence
  have hevent := hfilter.2
  change seed ∈ Seed.isolatedSeeds triple.xIndex triple.yIndex
      (xCompetitorYIndices targets triple) b at hevent
  have hotherData := (mem_filteredTargets targets B hB seed other).mp hother
  obtain ⟨hotherTargets, c, _hcB, hcommonOther⟩ := hotherData
  have hyAlternative : other.yIndex ∈ xCompetitorYIndices targets triple :=
    yIndex_mem_xCompetitorYIndices targets hotherTargets hne hx
  have hnotY : seed.yHash other.yIndex ≠ b := hevent.2 _ hyAlternative
  apply hnotY
  calc
    seed.yHash other.yIndex = c := hcommonOther.2
    _ = seed.xHash other.xIndex := hcommonOther.1.symm
    _ = seed.xHash triple.xIndex := congrArg seed.xHash hx
    _ = b := hevent.1.1

/-- Complete finite more-asymmetric hashing extraction.  Under the standard degree condition,
there is a seed producing many targets that survive the progression-free filter and have pairwise
distinct `X`-indices. -/
theorem exists_seed_many_xIsolatedTargets [Fintype R] [NeZero (2 : R)]
    (targets : Finset (LegalTriple R ι target)) (B : Finset R)
    (hquarter : ∀ triple ∈ targets,
      4 * (xCompetitorYIndices targets triple).card ≤ Fintype.card R) :
    ∃ seed : Seed R ι,
      3 * targets.card * B.card ≤
          4 * (Fintype.card R * Fintype.card R) *
            (xIsolatedTargets targets B seed).card ∧
        xIsolatedTargets targets B seed ⊆ filteredTargets targets B seed ∧
        Set.InjOn (fun triple : LegalTriple R ι target => triple.xIndex)
          (xIsolatedTargets targets B seed : Set (LegalTriple R ι target)) := by
  classical
  have hdistinct : ∀ triple ∈ targets,
      ∀ J' ∈ xCompetitorYIndices targets triple, J' ≠ triple.yIndex := by
    intro triple _htriple J' hJ'
    exact yIndex_ne_of_mem_xCompetitorYIndices targets triple hJ'
  obtain ⟨seed, hcount⟩ := Seed.exists_seed_many_isolatedTargets targets B
    LegalTriple.xIndex LegalTriple.yIndex (xCompetitorYIndices targets)
    hdistinct hquarter
  refine ⟨seed, ?_, xIsolatedTargets_subset_filteredTargets targets B seed, ?_⟩
  · simpa [xIsolatedTargets] using hcount
  · apply Seed.xIndex_injectiveOn_isolatedTargets targets B LegalTriple.xIndex
      LegalTriple.yIndex (xCompetitorYIndices targets) seed
    intro triple htriple other hother hne hx
    exact yIndex_mem_xCompetitorYIndices targets hother hne hx

end LegalTriple

end ProgressionHash

end AlgebraicComplexity
