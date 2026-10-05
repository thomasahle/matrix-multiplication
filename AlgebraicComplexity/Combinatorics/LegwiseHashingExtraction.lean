/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Combinatorics.HashingExtraction
import AlgebraicComplexity.Tensor.Leg

/-!
# Legwise isolation by affine hashing

The asymmetric hashing theorem isolates one tensor leg.  A direct-sum extraction needs the
selected constituents to have distinct block labels on all three legs.  This file obtains that
stronger conclusion without paying for three independent hash passes.

Inside the common-bucket fiber of a target `(I,J,K)`, an alternative `X`-word `I'` has the same
hash as the translated `Y`-word `J + I' - I`.  We therefore encode every competitor sharing any
leg by one alternative `Y`-word and reuse the exact collision count and averaging theorem from
`HashingIsolation`.  The resulting selected family is isolated against the entire hash-filtered
support on every leg.
-/

namespace AlgebraicComplexity

universe u v

namespace ProgressionHash.LegalTriple

variable {R : Type u} [Field R]
variable {ι : Type v} [Fintype ι]
variable {target : R}

/-- Read the word carried by a specified tensor leg. -/
def legIndex (triple : LegalTriple R ι target) : ∀ _ : Tensor.Leg, ι → R
  | .X => triple.xIndex
  | .Y => triple.yIndex
  | .Z => triple.zIndex

omit [Fintype ι] in
@[simp] theorem legIndex_X (triple : LegalTriple R ι target) :
    triple.legIndex .X = triple.xIndex := rfl

omit [Fintype ι] in
@[simp] theorem legIndex_Y (triple : LegalTriple R ι target) :
    triple.legIndex .Y = triple.yIndex := rfl

omit [Fintype ι] in
@[simp] theorem legIndex_Z (triple : LegalTriple R ι target) :
    triple.legIndex .Z = triple.zIndex := rfl

/-- Two target triples conflict when they use the same block word on at least one tensor leg. -/
def SharesLeg (left right : LegalTriple R ι target) : Prop :=
  ∃ c, left.legIndex c = right.legIndex c

/-- Encode a competing triple by a `Y`-word collision.  A competitor with the same `X`-word
already supplies its own `Y`-word; otherwise its `X`-word is transported into the fixed target's
common-bucket fiber. -/
noncomputable def collisionProxy
    (triple other : LegalTriple R ι target) : ι → R := by
  classical
  exact if other.xIndex = triple.xIndex then other.yIndex
    else Seed.transportXAlternative triple.xIndex triple.yIndex other.xIndex

/-- A distinct legal triple always yields a proxy different from the intended `Y`-word. -/
theorem collisionProxy_ne
    (triple other : LegalTriple R ι target) (hne : other ≠ triple) :
    collisionProxy triple other ≠ triple.yIndex := by
  classical
  unfold collisionProxy
  split_ifs with hx
  · intro hy
    exact hne (eq_of_xIndex_eq_yIndex_eq hx hy)
  · exact Seed.transportXAlternative_ne triple.xIndex triple.yIndex other.xIndex hx

/-- Other targets sharing at least one block word with `triple`. -/
noncomputable def legCompetitors
    (targets : Finset (LegalTriple R ι target)) (triple : LegalTriple R ι target) :
    Finset (LegalTriple R ι target) := by
  classical
  exact (targets.erase triple).filter (SharesLeg triple)

/-- Targets using the same block word as `triple` on one specified tensor leg. -/
noncomputable def legFiber
    (targets : Finset (LegalTriple R ι target)) (triple : LegalTriple R ι target)
    (c : Tensor.Leg) : Finset (LegalTriple R ι target) := by
  classical
  exact targets.filter fun other ↦ other.legIndex c = triple.legIndex c

@[simp] theorem mem_legFiber
    (targets : Finset (LegalTriple R ι target)) (triple other : LegalTriple R ι target)
    (c : Tensor.Leg) :
    other ∈ legFiber targets triple c ↔
      other ∈ targets ∧ other.legIndex c = triple.legIndex c := by
  classical
  simp [legFiber]

/-- Collision proxies for every other target sharing a leg with `triple`. -/
noncomputable def legwiseCompetitorYIndices
    (targets : Finset (LegalTriple R ι target)) (triple : LegalTriple R ι target) :
    Finset (ι → R) := by
  classical
  exact (legCompetitors targets triple).image (collisionProxy triple)

/-- The collision-proxy count is at most the sum of the three leg-fiber sizes. -/
theorem card_legwiseCompetitorYIndices_le_sum_legFibers
    (targets : Finset (LegalTriple R ι target)) (triple : LegalTriple R ι target) :
    (legwiseCompetitorYIndices targets triple).card ≤
      ∑ c, (legFiber targets triple c).card := by
  classical
  calc
    (legwiseCompetitorYIndices targets triple).card ≤
        (legCompetitors targets triple).card := by
      exact Finset.card_image_le
    _ ≤ ((Finset.univ : Finset Tensor.Leg).biUnion
        (legFiber targets triple)).card := by
      apply Finset.card_le_card
      intro other hother
      obtain ⟨herase, c, hleg⟩ := Finset.mem_filter.mp hother
      apply Finset.mem_biUnion.mpr
      refine ⟨c, Finset.mem_univ c, ?_⟩
      exact mem_legFiber targets triple other c |>.mpr
        ⟨(Finset.mem_erase.mp herase).2, hleg.symm⟩
    _ ≤ ∑ c ∈ (Finset.univ : Finset Tensor.Leg),
        (legFiber targets triple c).card := Finset.card_biUnion_le
    _ = ∑ c, (legFiber targets triple c).card := by simp

/-- A uniform bound on each of the three leg fibers gives a factor-three competitor bound. -/
theorem card_legwiseCompetitorYIndices_le_three_mul
    (targets : Finset (LegalTriple R ι target)) (triple : LegalTriple R ι target)
    (d : ℕ) (hfiber : ∀ c, (legFiber targets triple c).card ≤ d) :
    (legwiseCompetitorYIndices targets triple).card ≤ 3 * d := by
  apply (card_legwiseCompetitorYIndices_le_sum_legFibers targets triple).trans
  rw [show (Finset.univ : Finset Tensor.Leg) = {.X, .Y, .Z} by decide]
  simp only [Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton,
    reduceCtorEq, or_false, not_false_eq_true, Finset.sum_singleton]
  have hX := hfiber Tensor.Leg.X
  have hY := hfiber Tensor.Leg.Y
  have hZ := hfiber Tensor.Leg.Z
  omega

/-- The proxy family contains every genuine leg competitor. -/
theorem collisionProxy_mem_legwiseCompetitorYIndices
    (targets : Finset (LegalTriple R ι target))
    {triple other : LegalTriple R ι target}
    (hother : other ∈ targets) (hne : other ≠ triple)
    (hshare : SharesLeg triple other) :
    collisionProxy triple other ∈ legwiseCompetitorYIndices targets triple := by
  classical
  rw [legwiseCompetitorYIndices, Finset.mem_image]
  refine ⟨other, ?_, rfl⟩
  exact Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨hne, hother⟩, hshare⟩

/-- Every collision proxy differs from the target's own `Y`-word, as required by the exact
one-over-the-field-size collision count. -/
theorem yIndex_ne_of_mem_legwiseCompetitorYIndices
    (targets : Finset (LegalTriple R ι target)) (triple : LegalTriple R ι target)
    {J' : ι → R} (hJ' : J' ∈ legwiseCompetitorYIndices targets triple) :
    J' ≠ triple.yIndex := by
  classical
  rw [legwiseCompetitorYIndices, Finset.mem_image] at hJ'
  obtain ⟨other, hother, rfl⟩ := hJ'
  have herase := (Finset.mem_filter.mp hother).1
  exact collisionProxy_ne triple other (Finset.mem_erase.mp herase).1

/-- Targets isolated against every competitor sharing any tensor leg. -/
noncomputable def legwiseIsolatedTargets
    (targets : Finset (LegalTriple R ι target)) (B : Finset R) (seed : Seed R ι) :
    Finset (LegalTriple R ι target) :=
  Seed.isolatedTargets targets B LegalTriple.xIndex LegalTriple.yIndex
    (legwiseCompetitorYIndices targets) seed

/-- Legwise-isolated targets are among the targets surviving the three-leg hash filter. -/
theorem legwiseIsolatedTargets_subset_filteredTargets [NeZero (2 : R)]
    (targets : Finset (LegalTriple R ι target)) (B : Finset R)
    (seed : Seed R ι) :
    legwiseIsolatedTargets targets B seed ⊆ filteredTargets targets B seed := by
  classical
  intro triple htriple
  have himage : triple ∈ Seed.isolatedTargets targets B LegalTriple.xIndex
      LegalTriple.yIndex (legwiseCompetitorYIndices targets) seed := by
    simpa [legwiseIsolatedTargets] using htriple
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
  exact ⟨htarget, by
    exact ⟨by simpa [hcommon.1] using hb,
      by simpa [hcommon.2] using hb,
      by simpa [hZ] using hb⟩⟩

/-- Two legal triples in common buckets that share a leg necessarily use the same bucket. -/
theorem commonBucket_eq_of_legIndex_eq [NeZero (2 : R)]
    (seed : Seed R ι) (triple other : LegalTriple R ι target) (b c : R)
    (htriple : Seed.InCommonBucket triple.xIndex triple.yIndex b seed)
    (hother : Seed.InCommonBucket other.xIndex other.yIndex c seed)
    (leg : Tensor.Leg) (hleg : other.legIndex leg = triple.legIndex leg) :
    c = b := by
  cases leg with
  | X =>
      exact hother.1.symm.trans ((congrArg seed.xHash hleg).trans htriple.1)
  | Y =>
      exact hother.2.symm.trans ((congrArg seed.yHash hleg).trans htriple.2)
  | Z =>
      have hotherZ : seed.zHash target other.zIndex = c :=
        Seed.zHash_eq_of_commonBucket seed other.xIndex other.yIndex other.zIndex
          target c other.legal hother
      have htripleZ : seed.zHash target triple.zIndex = b :=
        Seed.zHash_eq_of_commonBucket seed triple.xIndex triple.yIndex triple.zIndex
          target b triple.legal htriple
      exact hotherZ.symm.trans ((congrArg (seed.zHash target) hleg).trans htripleZ)

/-- An isolated target is the unique filtered target in each of its three leg fibers. -/
theorem eq_of_mem_legwiseIsolatedTargets_of_mem_filteredTargets [NeZero (2 : R)]
    (targets : Finset (LegalTriple R ι target)) (B : Finset R)
    (hB : ThreeAPFree (B : Set R)) (seed : Seed R ι)
    {triple other : LegalTriple R ι target}
    (htriple : triple ∈ legwiseIsolatedTargets targets B seed)
    (hother : other ∈ filteredTargets targets B seed)
    (leg : Tensor.Leg) (hleg : other.legIndex leg = triple.legIndex leg) :
    other = triple := by
  classical
  by_contra hne
  have himage : triple ∈ Seed.isolatedTargets targets B LegalTriple.xIndex
      LegalTriple.yIndex (legwiseCompetitorYIndices targets) seed := by
    simpa [legwiseIsolatedTargets] using htriple
  obtain ⟨⟨triple', b⟩, hincidence, hfst⟩ := Finset.mem_image.mp himage
  simp only at hfst
  subst triple'
  have hfilter := Finset.mem_filter.mp hincidence
  have htripleTarget : triple ∈ targets := (Finset.mem_product.mp hfilter.1).1
  have htripleEvent := hfilter.2
  change seed ∈ Seed.isolatedSeeds triple.xIndex triple.yIndex
      (legwiseCompetitorYIndices targets triple) b at htripleEvent
  have hotherData := (mem_filteredTargets targets B hB seed other).mp hother
  obtain ⟨hotherTarget, c, _hcB, hotherCommon⟩ := hotherData
  have hshare : SharesLeg triple other := ⟨leg, hleg.symm⟩
  have hproxyMem : collisionProxy triple other ∈
      legwiseCompetitorYIndices targets triple :=
    collisionProxy_mem_legwiseCompetitorYIndices targets hotherTarget hne hshare
  have hnot := htripleEvent.2 _ hproxyMem
  apply hnot
  have hcb : c = b :=
    commonBucket_eq_of_legIndex_eq seed triple other b c
      htripleEvent.1 hotherCommon leg hleg
  unfold collisionProxy
  split_ifs with hx
  · exact hotherCommon.2.trans hcb
  · rw [Seed.yHash_transportXAlternative_eq_xHash seed triple.xIndex
      triple.yIndex other.xIndex b htripleEvent.1]
    exact hotherCommon.1.trans hcb

/-- The selected target family is injective on a specified tensor leg. -/
theorem legIndex_injectiveOn_legwiseIsolatedTargets [NeZero (2 : R)]
    (targets : Finset (LegalTriple R ι target)) (B : Finset R)
    (hB : ThreeAPFree (B : Set R)) (seed : Seed R ι) (leg : Tensor.Leg) :
    Set.InjOn (fun triple : LegalTriple R ι target => triple.legIndex leg)
      (legwiseIsolatedTargets targets B seed : Set (LegalTriple R ι target)) := by
  intro triple htriple other hother hleg
  exact (eq_of_mem_legwiseIsolatedTargets_of_mem_filteredTargets
    targets B hB seed htriple
      (legwiseIsolatedTargets_subset_filteredTargets targets B seed hother)
      leg hleg.symm).symm

/-- Complete finite legwise hashing extraction.  Under the usual degree condition, one affine
seed selects many filtered targets and their block words are pairwise distinct on every leg. -/
theorem exists_seed_many_legwiseIsolatedTargets [Fintype R] [NeZero (2 : R)]
    (targets : Finset (LegalTriple R ι target)) (B : Finset R)
    (hB : ThreeAPFree (B : Set R))
    (hquarter : ∀ triple ∈ targets,
      4 * (legwiseCompetitorYIndices targets triple).card ≤ Fintype.card R) :
    ∃ seed : Seed R ι,
      3 * targets.card * B.card ≤
          4 * (Fintype.card R * Fintype.card R) *
            (legwiseIsolatedTargets targets B seed).card ∧
        legwiseIsolatedTargets targets B seed ⊆ filteredTargets targets B seed ∧
        ∀ leg, Set.InjOn
          (fun triple : LegalTriple R ι target => triple.legIndex leg)
          (legwiseIsolatedTargets targets B seed : Set (LegalTriple R ι target)) := by
  classical
  have hdistinct : ∀ triple ∈ targets,
      ∀ J' ∈ legwiseCompetitorYIndices targets triple, J' ≠ triple.yIndex := by
    intro triple _htriple J' hJ'
    exact yIndex_ne_of_mem_legwiseCompetitorYIndices targets triple hJ'
  obtain ⟨seed, hcount⟩ := Seed.exists_seed_many_isolatedTargets targets B
    LegalTriple.xIndex LegalTriple.yIndex (legwiseCompetitorYIndices targets)
    hdistinct hquarter
  refine ⟨seed, ?_, legwiseIsolatedTargets_subset_filteredTargets targets B seed, ?_⟩
  · simpa [legwiseIsolatedTargets] using hcount
  · intro leg
    exact legIndex_injectiveOn_legwiseIsolatedTargets targets B hB seed leg

end ProgressionHash.LegalTriple

end AlgebraicComplexity
