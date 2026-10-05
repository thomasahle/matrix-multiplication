/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Combinatorics.TwoLegHashingExtraction

/-!
# Marked two-leg (asymmetric) isolation by affine hashing

Layer 2 (`AlgebraicComplexity/Combinatorics/`).  This module supplies the missing quadrant of the
affine-hashing extraction family, the one used by the *asymmetric hashing* of

> R. Duan, H. Wu and R. Zhou, *Faster Matrix Multiplication via Asymmetric Hashing*,
> arXiv:2210.10173v5, **§2.9 (`hashing.tex`)** (`[DuanWuZhou2022]`).

The existing family has three of the four combinations:

| | all three legs isolated | only X and Y isolated |
| --- | --- | --- |
| one family | `legwiseIsolatedTargets` | `xyIsolatedTargets` |
| marked ⊆ ambient | `markedLegwiseIsolatedTargets` | **this module** |

The right-hand column is `[DuanWuZhou2022]`'s asymmetric setting: only X- and Y-blocks are made
unique, while **a Z-block is deliberately allowed to serve many retained triples** (`hashing.tex`
l.3, l.32).  The bottom row is the *refined* laser method's marked/ambient split, which is what
carries the hash loss.

## The two families, and why their roles must not be swapped

`[DuanWuZhou2022]` fix a distribution `α` over the components of the partitioned tensor, with
marginals `α_X, α_Y, α_Z`, and then distinguish (`hashing.tex` l.5--l.13):

| paper | count | this module | meaning |
| --- | --- | --- | --- |
| triples consistent with `α_X, α_Y, α_Z` | `N_triple` | `ambient` | every triple surviving the *marginal* zeroing |
| triples consistent with the joint `α` — the **good** triples | `N_α` | `marked` | the triples whose value is actually counted |

Always `marked ⊆ ambient`, i.e. `N_α ≤ N_triple`, and the *hash loss* of `[DuanWuZhou2022]`
§"Hash Loss" is exactly the ratio `R = N_α / N_triple`.  The asymmetric cleanup keeps
`N_X · N_α / N_triple · 2^{-o(n)}` good triples, so the two counts enter the conclusion in
genuinely different places:

* the **surviving count is measured against `marked`** — the theorem's lower bound reads
  `3 * marked.card * B.card ≤ 4 * |R|² * (selected).card`, and
  `card_markedXYIsolatedTargets_le_card_marked` records the matching upper bound
  `(selected).card ≤ marked.card`.  Substituting the ambient count here would claim `N_triple`
  survivors and silently delete the hash loss;
* the **competitor lists are computed in `ambient`** — `hquarter` bounds
  `xyCompetitorYIndices ambient`, and every uniqueness conclusion is stated against
  `filteredTargets ambient`, i.e. against *every* marginally consistent survivor.  Restricting the
  competitor family to `marked` would be unsound: a retained X-block could still be shared with an
  unmarked filtered triple, so the subsequent variable zeroing would not be legitimate.
  `xyCompetitorYIndices_subset_of_subset` makes the direction of that strengthening explicit.

Three structural facts make the reversal `marked := N_triple, ambient := N_α` impossible rather
than merely discouraged.

1. Every principal theorem carries `hmarked : marked ⊆ ambient`.  Since `N_α ≤ N_triple` with
   equality only in the loss-free case, the swapped instantiation cannot discharge it.
2. The conclusion mentions **both** families in incomparable positions (count against `marked`,
   filter and competitors against `ambient`), so no consistent renaming produces the swapped
   statement.
3. `card_markedXYIsolatedTargets_le_card_marked` caps the output by `N_α`, so a client that
   believed the ambient count survived would be contradicted by the module itself.

## The modulus is deliberately abstract

`[DuanWuZhou2022]` pick the prime modulus `M ≥ 4 · N_triple / N_X` (`hashing.tex` l.15), and the
Hole Lemma client of §6 raises this to `M₀ = 8 · max(N_triple / N_X, N_α · p_comp / N_Z)`.  The
**second branch of that maximum is not a hashing quantity at all**: `p_comp` is the
combination-loss rate of the compatibility cleanup, which this layer knows nothing about.  This
module therefore never computes a modulus.  It takes either

* the raw union-bound hypothesis `hquarter` on the ambient competitor proxy family, or
* the convenience form `quarter_of_eight_mul_legFiber_le`: a bound `d` on the ambient X- and
  Y-leg fibers of each marked triple, together with an abstract `8 * d ≤ |R|`.

The second is the exact analogue of `competitor_quarter_of_eight_mul_xFiber_le`, and `8` is
`[DuanWuZhou2022]`'s own constant: two legs contribute `2d` proxies and the exact `3/4` survival
theorem needs `4 · (2d) ≤ |R|`.  A client that additionally needs
`M ≥ 8 · N_α · p_comp / N_Z` simply strengthens its own `d`; nothing here has to change.

## Relation to the unmarked theorem

Following the audit finding that the unmarked families are definitionally the marked ones at
`marked = ambient`, `markedXYIsolatedTargets_self` is `rfl` and
`exists_seed_many_xyIsolatedTargets_of_marked` re-derives the statement of the existing
`exists_seed_many_xyIsolatedTargets` from the marked theorem.  That specialization is kept as a
standing regression: if the marked statement ever drifts (a competitor family computed in the
wrong place, or a count taken against the wrong family), the specialization stops matching the
unmarked theorem it is supposed to reproduce.

A tiny inhabited instance closes the file.  It exhibits a genuinely lossy configuration
(`N_α = 1 < 2 = N_triple`) with a real X-collision competitor and concludes that the selected
family is nonempty, guarding against the vacuity failure mode in which the isolation event is
never satisfiable.
-/

namespace AlgebraicComplexity

universe u v

namespace ProgressionHash.LegalTriple

variable {R : Type u} [Field R]
variable {ι : Type v} [Fintype ι]
variable {target : R}

/-- The two-leg competitor proxy family is monotone in the family it is drawn from.

This is the formal content of the marked/ambient asymmetry: computing competitors in the smaller
marked family would give a *weaker* hypothesis and a *weaker* uniqueness conclusion, so the
ambient family is the sound choice. -/
theorem xyCompetitorYIndices_subset_of_subset
    {small large : Finset (LegalTriple R ι target)} (hsubset : small ⊆ large)
    (triple : LegalTriple R ι target) :
    xyCompetitorYIndices small triple ⊆ xyCompetitorYIndices large triple := by
  classical
  intro J' hJ'
  rw [xyCompetitorYIndices, Finset.mem_image] at hJ' ⊢
  obtain ⟨other, hother, rfl⟩ := hJ'
  refine ⟨other, ?_, rfl⟩
  obtain ⟨herase, hshare⟩ := Finset.mem_filter.mp hother
  obtain ⟨hne, hmem⟩ := Finset.mem_erase.mp herase
  exact Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨hne, hsubset hmem⟩, hshare⟩

/-- Marked targets isolated on the X and Y legs against competitor lists drawn from a possibly
larger ambient family, with no constraint whatsoever on the Z leg.

In `[DuanWuZhou2022]`'s notation `marked` is the family of `N_α` good triples and `ambient` the
family of `N_triple` marginally consistent triples. -/
noncomputable def markedXYIsolatedTargets
    (ambient marked : Finset (LegalTriple R ι target)) (B : Finset R)
    (seed : Seed R ι) : Finset (LegalTriple R ι target) :=
  Seed.isolatedTargets marked B LegalTriple.xIndex LegalTriple.yIndex
    (xyCompetitorYIndices ambient) seed

/-- Marked isolation never introduces a target outside the marked family. -/
theorem markedXYIsolatedTargets_subset_marked
    (ambient marked : Finset (LegalTriple R ι target)) (B : Finset R)
    (seed : Seed R ι) :
    markedXYIsolatedTargets ambient marked B seed ⊆ marked := by
  classical
  intro triple htriple
  unfold markedXYIsolatedTargets Seed.isolatedTargets at htriple
  obtain ⟨pair, hpair, hfirst⟩ := Finset.mem_image.mp htriple
  subst triple
  unfold Seed.isolatedIncidences at hpair
  exact (Finset.mem_product.mp (Finset.mem_filter.mp hpair).1).1

/-- **The hash loss is visible in the conclusion.**  The selected family is bounded above by the
marked count `N_α`, never by the ambient count `N_triple`. -/
theorem card_markedXYIsolatedTargets_le_card_marked
    (ambient marked : Finset (LegalTriple R ι target)) (B : Finset R)
    (seed : Seed R ι) :
    (markedXYIsolatedTargets ambient marked B seed).card ≤ marked.card :=
  Finset.card_le_card (markedXYIsolatedTargets_subset_marked ambient marked B seed)

/-- A marked target isolated against the ambient family is one of the ambient family's own
two-leg-isolated targets.

Proof sketch: an isolated target is the first projection of a target/bucket incidence; replacing
its marked membership by ambient membership leaves the hash and collision-avoidance conditions
untouched, because those conditions already refer to the ambient competitor list. -/
theorem markedXYIsolatedTargets_subset_xyIsolatedTargets
    (ambient marked : Finset (LegalTriple R ι target))
    (hmarked : marked ⊆ ambient) (B : Finset R) (seed : Seed R ι) :
    markedXYIsolatedTargets ambient marked B seed ⊆ xyIsolatedTargets ambient B seed := by
  classical
  intro triple htriple
  unfold markedXYIsolatedTargets Seed.isolatedTargets at htriple
  unfold xyIsolatedTargets Seed.isolatedTargets
  obtain ⟨pair, hpair, rfl⟩ := Finset.mem_image.mp htriple
  apply Finset.mem_image.mpr
  refine ⟨pair, ?_, rfl⟩
  unfold Seed.isolatedIncidences at hpair ⊢
  obtain ⟨hpairProduct, hevent⟩ := Finset.mem_filter.mp hpair
  obtain ⟨hpairMarked, hb⟩ := Finset.mem_product.mp hpairProduct
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_product.mpr ⟨hmarked hpairMarked, hb⟩, hevent⟩

/-- Marked ambient-isolated targets survive the ordinary three-leg progression-free hash filter of
the **ambient** family. -/
theorem markedXYIsolatedTargets_subset_filteredTargets [NeZero (2 : R)]
    (ambient marked : Finset (LegalTriple R ι target))
    (hmarked : marked ⊆ ambient) (B : Finset R) (seed : Seed R ι) :
    markedXYIsolatedTargets ambient marked B seed ⊆ filteredTargets ambient B seed :=
  (markedXYIsolatedTargets_subset_xyIsolatedTargets ambient marked hmarked B seed).trans
    (xyIsolatedTargets_subset_filteredTargets ambient B seed)

/-- A marked isolated target is the unique **ambient** hash survivor using its X word or its Y
word.  Sharing a Z word is not excluded, and that is the point of asymmetric hashing.

This is the semantic property that licenses the subsequent X- and Y-leg variable zeroing: keeping
a selected X- or Y-block cannot accidentally keep an unmarked ambient constituent. -/
theorem eq_of_mem_markedXYIsolatedTargets_of_mem_filteredTargets [NeZero (2 : R)]
    (ambient marked : Finset (LegalTriple R ι target))
    (hmarked : marked ⊆ ambient) (B : Finset R) (hB : ThreeAPFree (B : Set R))
    (seed : Seed R ι)
    {triple other : LegalTriple R ι target}
    (htriple : triple ∈ markedXYIsolatedTargets ambient marked B seed)
    (hother : other ∈ filteredTargets ambient B seed)
    (hshare : SharesXY triple other) :
    other = triple :=
  eq_of_mem_xyIsolatedTargets_of_mem_filteredTargets ambient B hB seed
    (markedXYIsolatedTargets_subset_xyIsolatedTargets ambient marked hmarked B seed htriple)
    hother hshare

/-- The selected marked family has pairwise distinct X words. -/
theorem xIndex_injectiveOn_markedXYIsolatedTargets [NeZero (2 : R)]
    (ambient marked : Finset (LegalTriple R ι target))
    (hmarked : marked ⊆ ambient) (B : Finset R) (hB : ThreeAPFree (B : Set R))
    (seed : Seed R ι) :
    Set.InjOn (fun triple : LegalTriple R ι target ↦ triple.xIndex)
      (markedXYIsolatedTargets ambient marked B seed : Set (LegalTriple R ι target)) :=
  (xIndex_injectiveOn_xyIsolatedTargets ambient B hB seed).mono
    (by
      exact_mod_cast
        Finset.coe_subset.mpr
          (markedXYIsolatedTargets_subset_xyIsolatedTargets ambient marked hmarked B seed))

/-- The selected marked family has pairwise distinct Y words. -/
theorem yIndex_injectiveOn_markedXYIsolatedTargets [NeZero (2 : R)]
    (ambient marked : Finset (LegalTriple R ι target))
    (hmarked : marked ⊆ ambient) (B : Finset R) (hB : ThreeAPFree (B : Set R))
    (seed : Seed R ι) :
    Set.InjOn (fun triple : LegalTriple R ι target ↦ triple.yIndex)
      (markedXYIsolatedTargets ambient marked B seed : Set (LegalTriple R ι target)) :=
  (yIndex_injectiveOn_xyIsolatedTargets ambient B hB seed).mono
    (by
      exact_mod_cast
        Finset.coe_subset.mpr
          (markedXYIsolatedTargets_subset_xyIsolatedTargets ambient marked hmarked B seed))

/-- **Complete marked two-leg (asymmetric) hashing extraction.**

One affine seed selects a large family of *marked* targets which

* survive the ambient progression-free hash filter,
* have pairwise distinct X words and pairwise distinct Y words, each uniquely so against the
  entire ambient filtered family, and
* carry **no Z constraint at all**, so several selected triples may share one Z block.

The count is taken against `marked.card = N_α`, while the degree hypothesis and every uniqueness
conclusion refer to the ambient family of size `N_triple`.  That asymmetry is the hash loss of
`[DuanWuZhou2022]` §"Hash Loss"; see the module documentation for why the two roles cannot be
exchanged.

Proof sketch: the isolation core `Seed.exists_seed_many_isolatedTargets` is already generic over
the competitor family, so it is applied with targets `marked` and alternatives
`xyCompetitorYIndices ambient`; the uniqueness half is inherited from the unmarked two-leg theorem
through `markedXYIsolatedTargets_subset_xyIsolatedTargets`. -/
theorem exists_seed_many_markedXYIsolatedTargets [Fintype R] [NeZero (2 : R)]
    (ambient marked : Finset (LegalTriple R ι target))
    (hmarked : marked ⊆ ambient) (B : Finset R) (hB : ThreeAPFree (B : Set R))
    (hquarter : ∀ triple ∈ marked,
      4 * (xyCompetitorYIndices ambient triple).card ≤ Fintype.card R) :
    ∃ seed : Seed R ι,
      3 * marked.card * B.card ≤
          4 * (Fintype.card R * Fintype.card R) *
            (markedXYIsolatedTargets ambient marked B seed).card ∧
        markedXYIsolatedTargets ambient marked B seed ⊆ filteredTargets ambient B seed ∧
        Set.InjOn (fun triple : LegalTriple R ι target ↦ triple.xIndex)
          (markedXYIsolatedTargets ambient marked B seed : Set (LegalTriple R ι target)) ∧
        Set.InjOn (fun triple : LegalTriple R ι target ↦ triple.yIndex)
          (markedXYIsolatedTargets ambient marked B seed : Set (LegalTriple R ι target)) := by
  classical
  have hdistinct : ∀ triple ∈ marked,
      ∀ J' ∈ xyCompetitorYIndices ambient triple, J' ≠ triple.yIndex := by
    intro triple _htriple J' hJ'
    exact yIndex_ne_of_mem_xyCompetitorYIndices ambient triple hJ'
  obtain ⟨seed, hcount⟩ := Seed.exists_seed_many_isolatedTargets marked B
    LegalTriple.xIndex LegalTriple.yIndex (xyCompetitorYIndices ambient)
    hdistinct hquarter
  refine ⟨seed, ?_,
    markedXYIsolatedTargets_subset_filteredTargets ambient marked hmarked B seed,
    xIndex_injectiveOn_markedXYIsolatedTargets ambient marked hmarked B hB seed,
    yIndex_injectiveOn_markedXYIsolatedTargets ambient marked hmarked B hB seed⟩
  simpa [markedXYIsolatedTargets] using hcount

/-- `[DuanWuZhou2022]`'s modulus condition in abstract form.  A common bound `d` on the ambient
X- and Y-leg fibers of every marked triple, together with `8 * d ≤ |R|`, implies the
four-times-competitor hypothesis of the exact `3/4` isolation theorem.

The constant `8` is the paper's own: two legs contribute at most `2 * d` collision proxies, and
the isolation theorem needs `4 * (2 * d) ≤ |R|`.  In the paper `d = N_triple / N_X`, so this reads
`M ≥ 8 * N_triple / N_X`, the first branch of `M₀`.  The second branch,
`8 * N_α * p_comp / N_Z`, is a combination-loss quantity that this layer must not attempt to
compute; a client needing it simply supplies a larger `d`. -/
theorem quarter_of_eight_mul_legFiber_le [Fintype R]
    (ambient marked : Finset (LegalTriple R ι target)) (d : ℕ)
    (hX : ∀ triple ∈ marked, (legFiber ambient triple .X).card ≤ d)
    (hY : ∀ triple ∈ marked, (legFiber ambient triple .Y).card ≤ d)
    (hmodulus : 8 * d ≤ Fintype.card R) :
    ∀ triple ∈ marked,
      4 * (xyCompetitorYIndices ambient triple).card ≤ Fintype.card R := by
  intro triple htriple
  have hcard : (xyCompetitorYIndices ambient triple).card ≤ 2 * d :=
    card_xyCompetitorYIndices_le_two_mul ambient triple d
      (hX triple htriple) (hY triple htriple)
  omega

/-- Marked two-leg extraction under the abstract modulus hypothesis.  This is the form a laser
client instantiates: it never mentions the competitor proxy construction, only the ambient
per-block triple degree `d` and a lower bound on the field size. -/
theorem exists_seed_many_markedXYIsolatedTargets_of_modulus
    [Fintype R] [NeZero (2 : R)]
    (ambient marked : Finset (LegalTriple R ι target))
    (hmarked : marked ⊆ ambient) (B : Finset R) (hB : ThreeAPFree (B : Set R))
    (d : ℕ)
    (hX : ∀ triple ∈ marked, (legFiber ambient triple .X).card ≤ d)
    (hY : ∀ triple ∈ marked, (legFiber ambient triple .Y).card ≤ d)
    (hmodulus : 8 * d ≤ Fintype.card R) :
    ∃ seed : Seed R ι,
      3 * marked.card * B.card ≤
          4 * (Fintype.card R * Fintype.card R) *
            (markedXYIsolatedTargets ambient marked B seed).card ∧
        markedXYIsolatedTargets ambient marked B seed ⊆ filteredTargets ambient B seed ∧
        Set.InjOn (fun triple : LegalTriple R ι target ↦ triple.xIndex)
          (markedXYIsolatedTargets ambient marked B seed : Set (LegalTriple R ι target)) ∧
        Set.InjOn (fun triple : LegalTriple R ι target ↦ triple.yIndex)
          (markedXYIsolatedTargets ambient marked B seed : Set (LegalTriple R ι target)) :=
  exists_seed_many_markedXYIsolatedTargets ambient marked hmarked B hB
    (quarter_of_eight_mul_legFiber_le ambient marked d hX hY hmodulus)

/-! ### Regression against the unmarked two-leg theorem -/

/-- At `marked = ambient` the marked construction **is** the unmarked one, definitionally.  This
records the audit finding that the unmarked hashing families are the marked families with a
trivial marking, so the two must never drift apart. -/
theorem markedXYIsolatedTargets_self
    (targets : Finset (LegalTriple R ι target)) (B : Finset R) (seed : Seed R ι) :
    markedXYIsolatedTargets targets targets B seed = xyIsolatedTargets targets B seed := rfl

/-- **Regression check.**  Specializing the marked theorem at `marked = ambient` reproduces the
statement of the existing `exists_seed_many_xyIsolatedTargets` verbatim.

Proof sketch: `markedXYIsolatedTargets_self` rewrites the selected family, and the hypothesis
`marked ⊆ ambient` is discharged by reflexivity. -/
theorem exists_seed_many_xyIsolatedTargets_of_marked [Fintype R] [NeZero (2 : R)]
    (targets : Finset (LegalTriple R ι target)) (B : Finset R)
    (hB : ThreeAPFree (B : Set R))
    (hquarter : ∀ triple ∈ targets,
      4 * (xyCompetitorYIndices targets triple).card ≤ Fintype.card R) :
    ∃ seed : Seed R ι,
      3 * targets.card * B.card ≤
          4 * (Fintype.card R * Fintype.card R) *
            (xyIsolatedTargets targets B seed).card ∧
        xyIsolatedTargets targets B seed ⊆ filteredTargets targets B seed ∧
        Set.InjOn (fun triple : LegalTriple R ι target ↦ triple.xIndex)
          (xyIsolatedTargets targets B seed : Set (LegalTriple R ι target)) ∧
        Set.InjOn (fun triple : LegalTriple R ι target ↦ triple.yIndex)
          (xyIsolatedTargets targets B seed : Set (LegalTriple R ι target)) := by
  simpa only [markedXYIsolatedTargets_self] using
    exists_seed_many_markedXYIsolatedTargets targets targets (Finset.Subset.refl targets)
      B hB hquarter

/-! ### A tiny inhabited instance

The failure mode this guards against is vacuity: an isolation event that no seed satisfies, or a
marked family whose selected part is provably empty, would make every theorem above true and
useless.  The instance below is genuinely lossy — one good triple inside two marginally consistent
ones, `N_α = 1 < 2 = N_triple` — and the two ambient triples really do collide on their X word,
so a competitor has to be avoided.  Over any finite field of characteristic `≠ 2` with at least
four elements the conclusion is that some seed selects a nonempty marked family. -/

section TinyInstance

variable (R)

/-- The good (marked) triple of the tiny instance: `(0, 0, target)` at the single position. -/
def tinyGoodTriple (target : R) : LegalTriple R (Fin 1) target where
  xIndex := fun _ ↦ 0
  yIndex := fun _ ↦ 0
  zIndex := fun _ ↦ target
  legal := by intro i; ring

/-- The unmarked ambient companion `(0, 1, target - 1)`.  It shares the X word of the good triple,
so it is a genuine hashing competitor. -/
def tinyOtherTriple (target : R) : LegalTriple R (Fin 1) target where
  xIndex := fun _ ↦ 0
  yIndex := fun _ ↦ 1
  zIndex := fun _ ↦ target - 1
  legal := by intro i; ring

variable {R}

/-- The two tiny triples are distinct: their Y words differ. -/
theorem tinyOtherTriple_ne (target : R) :
    tinyOtherTriple R target ≠ tinyGoodTriple R target := by
  intro h
  have hy := congrFun (congrArg LegalTriple.yIndex h) 0
  exact one_ne_zero (α := R) hy

/-- The ambient family of the tiny instance: both triples, `N_triple = 2`. -/
noncomputable def tinyAmbient (target : R) : Finset (LegalTriple R (Fin 1) target) := by
  classical
  exact {tinyGoodTriple R target, tinyOtherTriple R target}

/-- The marked family of the tiny instance: the good triple only, `N_α = 1`. -/
noncomputable def tinyMarked (target : R) : Finset (LegalTriple R (Fin 1) target) := by
  classical
  exact {tinyGoodTriple R target}

theorem tinyMarked_subset_tinyAmbient (target : R) :
    tinyMarked target ⊆ tinyAmbient target := by
  classical
  intro triple htriple
  rw [tinyMarked, Finset.mem_singleton] at htriple
  subst htriple
  exact Finset.mem_insert_self _ _

/-- **The instance is genuinely lossy.**  `N_α = 1` is strictly smaller than `N_triple = 2`, so
the hash-loss ratio `R = N_α / N_triple` is not `1`. -/
theorem card_tinyMarked_lt_card_tinyAmbient (target : R) :
    (tinyMarked target).card < (tinyAmbient target).card := by
  classical
  have hcard : (tinyAmbient target).card = 2 := by
    rw [tinyAmbient, Finset.card_insert_of_notMem, Finset.card_singleton]
    simpa [Finset.mem_singleton] using (tinyOtherTriple_ne target).symm
  rw [hcard, tinyMarked, Finset.card_singleton]
  norm_num

/-- The competitor proxy family of the good triple has at most one element: the only candidate is
the other ambient triple. -/
theorem card_tinyCompetitors_le (target : R) :
    (xyCompetitorYIndices (tinyAmbient target) (tinyGoodTriple R target)).card ≤ 1 := by
  classical
  have hsub : xyCompetitors (tinyAmbient target) (tinyGoodTriple R target) ⊆
      {tinyOtherTriple R target} := by
    intro other hother
    obtain ⟨hne, hmem⟩ := Finset.mem_erase.mp (Finset.mem_filter.mp hother).1
    rw [tinyAmbient, Finset.mem_insert] at hmem
    rcases hmem with rfl | hmem
    · exact absurd rfl hne
    · exact hmem
  calc
    (xyCompetitorYIndices (tinyAmbient target) (tinyGoodTriple R target)).card ≤
        (xyCompetitors (tinyAmbient target) (tinyGoodTriple R target)).card :=
      Finset.card_image_le
    _ ≤ ({tinyOtherTriple R target} : Finset (LegalTriple R (Fin 1) target)).card :=
      Finset.card_le_card hsub
    _ = 1 := Finset.card_singleton _

/-- **The tiny instance is inhabited.**  Over a finite field with `2 ≠ 0` and at least four
elements, some affine seed selects a nonempty family of marked two-leg-isolated targets — with the
Z leg unconstrained, exactly as asymmetric hashing requires. -/
theorem tiny_markedXYIsolatedTargets_nonempty
    [Fintype R] [NeZero (2 : R)] (target : R) (hcard : 4 ≤ Fintype.card R) :
    ∃ seed : Seed R (Fin 1),
      (markedXYIsolatedTargets (tinyAmbient target) (tinyMarked target) {0} seed).Nonempty := by
  classical
  have hB : ThreeAPFree (({0} : Finset R) : Set R) :=
    Set.Subsingleton.threeAPFree (by simp)
  have hquarter : ∀ triple ∈ tinyMarked target,
      4 * (xyCompetitorYIndices (tinyAmbient target) triple).card ≤ Fintype.card R := by
    intro triple htriple
    rw [tinyMarked, Finset.mem_singleton] at htriple
    subst htriple
    have := card_tinyCompetitors_le (R := R) target
    omega
  obtain ⟨seed, hcount, -, -, -⟩ :=
    exists_seed_many_markedXYIsolatedTargets (tinyAmbient target) (tinyMarked target)
      (tinyMarked_subset_tinyAmbient target) {0} hB hquarter
  refine ⟨seed, Finset.card_pos.mp (Nat.pos_of_ne_zero ?_)⟩
  intro hzero
  rw [hzero, Nat.mul_zero, tinyMarked, Finset.card_singleton, Finset.card_singleton] at hcount
  omega

end TinyInstance

end ProgressionHash.LegalTriple

end AlgebraicComplexity
