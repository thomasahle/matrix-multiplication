/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Combinatorics.SharedLegSeedHoleMass

set_option autoImplicit false

/-!
# Ordering-free asymmetric hashing and useful nonhole mass

This module formalizes the finite union bound in [duan2023faster], §2.9,
`papers/sources/2210.10173/hashing.tex:7-13,32-65,88-96`, with the two modulus costs
of §6.3, `component_value.tex:255-262`. The extension drops the printed ordering of the
numbers of X/Y and Z blocks; actual X/Y competitor degrees and the shared-Z charge remain.

We reuse the seed-summed estimates behind
`exists_seed_isolation_and_sharedLegHoleMass`: X/Y isolation leaves at least three quarters
of the unfiltered reward, and shared-leg competitors charge at most one eighth. Subtracting
these quantities **before selecting a seed** gives the five-eighths expected nonhole bound.
The count below is a conservative nonhole count: it excludes a fine block whenever any initially
hashed compatible good competitor hits its bucket, whether or not that competitor later survives.

No independence conditioned on greedy retention is assumed. Useful reference subsets are kept
explicit; their density is not replaced by a constant. There is no tensor-restriction, hole-repair,
asymptotic or exponent conclusion, and this module does not change the numerical harness guard.
-/

namespace AlgebraicComplexity.ProgressionHash.LegalTriple

open scoped BigOperators

universe u v w

variable {R : Type u} [Field R] [Fintype R] [NeZero (2 : R)]
variable {ι : Type v} [Fintype ι] {target : R}
variable {A : Type w} [Fintype A]

/-- Number of fine blocks not charged as holes, summed over the isolated owner/bucket incidences
of a single seed. The fine alphabet is read in each owner's reference coordinates. -/
noncomputable def seedSharedLegNonholeMass
    (ambient marked : Finset (LegalTriple R ι target)) (buckets : Finset R)
    (compat : LegalTriple R ι target → A → LegalTriple R ι target → Prop)
    (alternatives : LegalTriple R ι target → Finset (ι → R))
    (seed : Seed R ι) : ℕ := by
  classical
  exact ∑ pair ∈ Seed.isolatedIncidences marked buckets
      LegalTriple.xIndex LegalTriple.yIndex alternatives seed,
    (Fintype.card A - (seedSharedHoles ambient compat seed pair.1 pair.2).card)

omit [Fintype R] [NeZero (2 : R)] in
/-- Nonholes plus holes recover all fine blocks of the isolated incidences, for the same seed.
Proof sketch: each hole set is a subset of the finite fine alphabet, so natural subtraction is
exact; sum that partition over the isolated incidences. -/
theorem seedSharedLegNonholeMass_add_holeMass
    (ambient marked : Finset (LegalTriple R ι target)) (buckets : Finset R)
    (compat : LegalTriple R ι target → A → LegalTriple R ι target → Prop)
    (alternatives : LegalTriple R ι target → Finset (ι → R)) (seed : Seed R ι) :
    seedSharedLegNonholeMass ambient marked buckets compat alternatives seed +
        seedSharedLegHoleMass ambient marked buckets compat alternatives seed =
      Fintype.card A * (Seed.isolatedIncidences marked buckets
        LegalTriple.xIndex LegalTriple.yIndex alternatives seed).card := by
  classical
  unfold seedSharedLegNonholeMass seedSharedLegHoleMass
  rw [← Finset.sum_add_distrib]
  simp only [Nat.sub_add_cancel (Finset.card_le_univ _)]
  simp [mul_comm]

/-- At most a quarter of the initial reward lost to isolation and an eighth lost to compatible
shared-leg competitors leave at least five eighths in seed-summed nonhole mass.

Proof sketch: reuse the exact isolation and shared-leg collision sums, clear the positive field
cardinality, and subtract the hole bound from the isolation reward using the pointwise partition.
No comparison of the numbers of vertices on different legs enters either estimate. -/
theorem five_mul_le_eight_mul_sum_seedSharedLegNonholeMass
    (ambient marked : Finset (LegalTriple R ι target)) (buckets : Finset R)
    (compat : LegalTriple R ι target → A → LegalTriple R ι target → Prop)
    (alternatives : LegalTriple R ι target → Finset (ι → R))
    (sharedLeg : LegalTriple R ι target → A → LegalTriple R ι target → Tensor.Leg)
    (c : ℕ)
    (hdistinct : ∀ owner ∈ marked,
      ∀ alternative ∈ alternatives owner, alternative ≠ owner.yIndex)
    (hquarter : ∀ owner ∈ marked, 4 * (alternatives owner).card ≤ Fintype.card R)
    (hshared : ∀ owner ∈ marked, ∀ fine : A,
      ∀ competitor ∈ fineCompetitors ambient compat owner fine,
        competitor.legIndex (sharedLeg owner fine competitor) =
          owner.legIndex (sharedLeg owner fine competitor))
    (hcompetitors : ∀ owner ∈ marked, ∀ fine : A,
      (fineCompetitors ambient compat owner fine).card ≤ c)
    (hmodulus : 8 * c ≤ Fintype.card R) :
    5 * marked.card * buckets.card * Fintype.card A * Fintype.card (Seed R ι) ≤
      8 * (Fintype.card R * Fintype.card R) *
        ∑ seed : Seed R ι,
          seedSharedLegNonholeMass ambient marked buckets compat alternatives seed := by
  classical
  let q := Fintype.card R
  let reward := ∑ seed : Seed R ι, (Seed.isolatedIncidences marked buckets
    LegalTriple.xIndex LegalTriple.yIndex alternatives seed).card
  let holes := ∑ seed : Seed R ι,
    seedSharedLegHoleMass ambient marked buckets compat alternatives seed
  let nonholes := ∑ seed : Seed R ι,
    seedSharedLegNonholeMass ambient marked buckets compat alternatives seed
  let base := marked.card * buckets.card * Fintype.card A * Fintype.card (Seed R ι)
  have hq : 0 < q := Fintype.card_pos
  have hpartition : nonholes + holes = Fintype.card A * reward := by
    simp only [nonholes, holes, reward, ← Finset.sum_add_distrib, Finset.mul_sum]
    exact Finset.sum_congr rfl fun seed _ ↦
      seedSharedLegNonholeMass_add_holeMass ambient marked buckets compat alternatives seed
  have hisolation :=
    Seed.three_mul_targets_mul_buckets_mul_seeds_le_four_mul_square_mul_sum_isolatedIncidences
      marked buckets LegalTriple.xIndex LegalTriple.yIndex alternatives hdistinct hquarter
  have hreward : 6 * base ≤ 8 * (q * q) * (Fintype.card A * reward) := by
    have h := Nat.mul_le_mul_left (2 * Fintype.card A) hisolation
    convert h using 1 <;> dsimp [base, reward, q] <;> ring
  have hholes := sum_seedSharedLegHoleMass_mul_cube_le
    ambient marked buckets compat alternatives sharedLeg c hshared hcompetitors
  have hchargeScaled : (8 * (q * q) * holes) * q ≤ base * q := by
    calc
      (8 * (q * q) * holes) * q = 8 * (holes * (q * q * q)) := by ring
      _ ≤ 8 * (marked.card * buckets.card * Fintype.card A * c *
          Fintype.card (Seed R ι)) := Nat.mul_le_mul_left 8 hholes
      _ = base * (8 * c) := by dsimp [base]; ring
      _ ≤ base * q := Nat.mul_le_mul_left base hmodulus
  have hcharge : 8 * (q * q) * holes ≤ base :=
    Nat.le_of_mul_le_mul_right hchargeScaled hq
  have hpartitionScaled :
      8 * (q * q) * nonholes + 8 * (q * q) * holes =
        8 * (q * q) * (Fintype.card A * reward) := by
    rw [← Nat.mul_add, hpartition]
  have hresult : 5 * base ≤ 8 * (q * q) * nonholes := by omega
  simpa only [base, q, nonholes, mul_assoc] using hresult

section OwnerReferences

variable (U : LegalTriple R ι target → Type w) [∀ owner, Fintype (U owner)]

/-- Total surviving useful fraction of one seed, with each owner normalized by its own full
reference size. Only useful fine blocks are counted; a compatible initially hashed good
competitor removes a block even if the competitor would itself be removed later. -/
noncomputable def seedMarkedXYNonholeFraction
    (ambient marked : Finset (LegalTriple R ι target)) (buckets : Finset R)
    (useful : (owner : LegalTriple R ι target) → Finset (U owner))
    (compat : (owner : LegalTriple R ι target) → U owner → LegalTriple R ι target → Prop)
    (seed : Seed R ι) : ℚ := by
  classical
  exact ∑ owner ∈ marked,
    (seedSharedLegNonholeMass marked {owner} buckets
      (fun _ (fine : {fine : U owner // fine ∈ useful owner}) competitor ↦
        compat owner fine.1 competitor)
      (xyCompetitorYIndices ambient) seed : ℚ) / Fintype.card (U owner)

/-- The expected sum of surviving useful reference fractions is at least
`(5/8) |B| |G| theta / M²`, with no ordering assumption on the used X/Y/Z block counts.

The X/Y degree bounds refer to the entire ambient family. The compatible-Z degree refers to
other good triples, and is needed only on the useful subset of each owner's actual reference.
All reference sets are nonempty on good owners, but their cardinalities may differ.

Proof sketch: apply the seed-summed nonhole estimate to each singleton owner and its useful
subtype. Divide by that owner's reference size, use its useful-density bound, and interchange
the finite owner and seed sums. No seed is chosen before these quantities are combined. -/
theorem five_eighths_le_expected_seedMarkedXYNonholeFraction
    (ambient marked : Finset (LegalTriple R ι target)) (buckets : Finset R)
    (useful : (owner : LegalTriple R ι target) → Finset (U owner))
    (compat : (owner : LegalTriple R ι target) → U owner → LegalTriple R ι target → Prop)
    (d c : ℕ) (theta : ℚ)
    (hX : ∀ owner ∈ marked, (legFiber ambient owner .X).card ≤ d)
    (hY : ∀ owner ∈ marked, (legFiber ambient owner .Y).card ≤ d)
    (hmodulus : 8 * max d c ≤ Fintype.card R)
    (hreference : ∀ owner ∈ marked, 0 < Fintype.card (U owner))
    (hdensity : ∀ owner ∈ marked,
      theta * Fintype.card (U owner) ≤ (useful owner).card)
    (hshared : ∀ owner ∈ marked, ∀ fine ∈ useful owner,
      ∀ competitor ∈ marked, competitor ≠ owner → compat owner fine competitor →
        competitor.zIndex = owner.zIndex)
    (hcompetitors : ∀ owner ∈ marked, ∀ fine ∈ useful owner,
      (fineCompetitors marked (fun _ fine competitor ↦ compat owner fine competitor)
        owner fine).card ≤ c) :
    (5 / 8 : ℚ) * buckets.card * marked.card * theta / (Fintype.card R : ℚ) ^ 2 ≤
      (∑ seed : Seed R ι,
        seedMarkedXYNonholeFraction U ambient marked buckets useful compat seed) /
          Fintype.card (Seed R ι) := by
  classical
  let count (owner : LegalTriple R ι target) (seed : Seed R ι) : ℕ :=
    seedSharedLegNonholeMass marked {owner} buckets
      (fun _ (fine : {fine : U owner // fine ∈ useful owner}) competitor ↦
        compat owner fine.1 competitor)
      (xyCompetitorYIndices ambient) seed
  let q : ℚ := Fintype.card R
  let seeds : ℚ := Fintype.card (Seed R ι)
  have hq : 0 < q := by dsimp [q]; exact_mod_cast Fintype.card_pos (α := R)
  have hs : 0 < seeds := by
    dsimp [seeds]
    exact_mod_cast Fintype.card_pos (α := Seed R ι)
  have hmodulusX : 8 * d ≤ Fintype.card R :=
    (Nat.mul_le_mul_left 8 (le_max_left d c)).trans hmodulus
  have hmodulusZ : 8 * c ≤ Fintype.card R :=
    (Nat.mul_le_mul_left 8 (le_max_right d c)).trans hmodulus
  have hquarter := quarter_of_eight_mul_legFiber_le
    ambient marked d hX hY hmodulusX
  have hpoint (owner : LegalTriple R ι target) (howner : owner ∈ marked) :
      (5 / 8 : ℚ) * buckets.card * theta / q ^ 2 ≤
        (∑ seed : Seed R ι, (count owner seed : ℚ) / Fintype.card (U owner)) / seeds := by
    let compatOwner := fun (_ : LegalTriple R ι target)
      (fine : {fine : U owner // fine ∈ useful owner}) competitor ↦
        compat owner fine.1 competitor
    have hraw := five_mul_le_eight_mul_sum_seedSharedLegNonholeMass
      marked {owner} buckets compatOwner (xyCompetitorYIndices ambient)
      (fun _ _ _ ↦ Tensor.Leg.Z) c
      (by
        intro other hother alternative halternative
        have heq : other = owner := Finset.mem_singleton.mp hother
        subst other
        exact yIndex_ne_of_mem_xyCompetitorYIndices ambient owner halternative)
      (by simpa only [Finset.mem_singleton, forall_eq] using hquarter owner howner)
      (by
        intro other hother fine competitor hcompetitor
        have heq : other = owner := Finset.mem_singleton.mp hother
        subst other
        obtain ⟨⟨hne, hmem⟩, hcompat⟩ := mem_fineCompetitors.mp hcompetitor
        exact hshared owner howner fine.1 fine.2 competitor hmem hne hcompat)
      (by
        intro other hother fine
        have heq : other = owner := Finset.mem_singleton.mp hother
        subst other
        exact hcompetitors owner howner fine.1 fine.2)
      hmodulusZ
    simp only [Finset.card_singleton, Fintype.card_coe, mul_one] at hraw
    have hrawQ : (5 : ℚ) * buckets.card * (useful owner).card * seeds ≤
        8 * q ^ 2 * ∑ seed : Seed R ι, (count owner seed : ℚ) := by
      dsimp only [q, seeds, count, compatOwner] at *
      simp only [pow_two]
      exact_mod_cast hraw
    have hr : (0 : ℚ) < Fintype.card (U owner) := by
      exact_mod_cast hreference owner howner
    have hstep : (5 : ℚ) * buckets.card * theta * seeds * Fintype.card (U owner) ≤
        8 * q ^ 2 * ∑ seed : Seed R ι, (count owner seed : ℚ) := by
      calc
        (5 : ℚ) * buckets.card * theta * seeds * Fintype.card (U owner) =
            (5 * buckets.card * seeds) * (theta * Fintype.card (U owner)) := by ring
        _ ≤ (5 * buckets.card * seeds) * (useful owner).card :=
          mul_le_mul_of_nonneg_left (hdensity owner howner) (by positivity)
        _ = 5 * buckets.card * (useful owner).card * seeds := by ring
        _ ≤ _ := hrawQ
    have hscaled := div_le_div_of_nonneg_right hstep
      (show (0 : ℚ) ≤ 8 * q ^ 2 * seeds * Fintype.card (U owner) by positivity)
    have hleft : (5 / 8 : ℚ) * buckets.card * theta / q ^ 2 =
        5 * buckets.card * theta * seeds * Fintype.card (U owner) /
          (8 * q ^ 2 * seeds * Fintype.card (U owner)) := by
      field_simp [hq.ne', hs.ne', hr.ne']
    have hright :
        (∑ seed : Seed R ι, (count owner seed : ℚ) / Fintype.card (U owner)) / seeds =
          (8 * q ^ 2 * ∑ seed : Seed R ι, (count owner seed : ℚ)) /
            (8 * q ^ 2 * seeds * Fintype.card (U owner)) := by
      rw [← Finset.sum_div]
      field_simp [hq.ne', hs.ne', hr.ne']
    rw [hleft, hright]
    exact hscaled
  calc
    (5 / 8 : ℚ) * buckets.card * marked.card * theta / (Fintype.card R : ℚ) ^ 2 =
        ∑ _owner ∈ marked, (5 / 8 : ℚ) * buckets.card * theta / q ^ 2 := by
      simp only [Finset.sum_const, nsmul_eq_mul, q]
      ring
    _ ≤ ∑ owner ∈ marked,
        (∑ seed : Seed R ι, (count owner seed : ℚ) / Fintype.card (U owner)) / seeds :=
      Finset.sum_le_sum hpoint
    _ = (∑ seed : Seed R ι,
        seedMarkedXYNonholeFraction U ambient marked buckets useful compat seed) /
          Fintype.card (Seed R ι) := by
      rw [← Finset.sum_div]
      congr 1
      exact Finset.sum_comm

/-- One seed realizes the expected useful nonhole fraction while retaining only good triples,
with X/Y uniqueness against the entire ambient filtered family. No Z uniqueness is asserted:
shared-Z conflicts are charged to fine-block holes of this same seed instead.

Proof sketch: average the preceding total-mass inequality, then reuse the marked X/Y extraction
semantics at the selected seed. -/
theorem exists_seed_markedXYNonholeFraction
    (ambient marked : Finset (LegalTriple R ι target)) (hmarked : marked ⊆ ambient)
    (buckets : Finset R) (hB : ThreeAPFree (buckets : Set R))
    (useful : (owner : LegalTriple R ι target) → Finset (U owner))
    (compat : (owner : LegalTriple R ι target) → U owner → LegalTriple R ι target → Prop)
    (d c : ℕ) (theta : ℚ)
    (hX : ∀ owner ∈ marked, (legFiber ambient owner .X).card ≤ d)
    (hY : ∀ owner ∈ marked, (legFiber ambient owner .Y).card ≤ d)
    (hmodulus : 8 * max d c ≤ Fintype.card R)
    (hreference : ∀ owner ∈ marked, 0 < Fintype.card (U owner))
    (hdensity : ∀ owner ∈ marked,
      theta * Fintype.card (U owner) ≤ (useful owner).card)
    (hshared : ∀ owner ∈ marked, ∀ fine ∈ useful owner,
      ∀ competitor ∈ marked, competitor ≠ owner → compat owner fine competitor →
        competitor.zIndex = owner.zIndex)
    (hcompetitors : ∀ owner ∈ marked, ∀ fine ∈ useful owner,
      (fineCompetitors marked (fun _ fine competitor ↦ compat owner fine competitor)
        owner fine).card ≤ c) :
    ∃ seed : Seed R ι,
      (5 / 8 : ℚ) * buckets.card * marked.card * theta / (Fintype.card R : ℚ) ^ 2 ≤
        seedMarkedXYNonholeFraction U ambient marked buckets useful compat seed ∧
      markedXYIsolatedTargets ambient marked buckets seed ⊆
        filteredTargets ambient buckets seed ∧
      Set.InjOn (fun triple : LegalTriple R ι target ↦ triple.xIndex)
        (markedXYIsolatedTargets ambient marked buckets seed : Set _) ∧
      Set.InjOn (fun triple : LegalTriple R ι target ↦ triple.yIndex)
        (markedXYIsolatedTargets ambient marked buckets seed : Set _) := by
  classical
  have h := five_eighths_le_expected_seedMarkedXYNonholeFraction
    U ambient marked buckets useful compat d c theta hX hY hmodulus
      hreference hdensity hshared hcompetitors
  have hs : (0 : ℚ) < Fintype.card (Seed R ι) := by
    exact_mod_cast Fintype.card_pos (α := Seed R ι)
  have hsum := (le_div_iff₀ hs).mp h
  rw [mul_comm] at hsum
  have hsum' := hsum
  rw [← nsmul_eq_mul, ← Finset.card_univ, ← Finset.sum_const] at hsum'
  obtain ⟨seed, _, hseed⟩ := Finset.exists_le_of_sum_le Finset.univ_nonempty hsum'
  exact ⟨seed, hseed,
    markedXYIsolatedTargets_subset_filteredTargets ambient marked hmarked buckets seed,
    xIndex_injectiveOn_markedXYIsolatedTargets ambient marked hmarked buckets hB seed,
    yIndex_injectiveOn_markedXYIsolatedTargets ambient marked hmarked buckets hB seed⟩

end OwnerReferences

end AlgebraicComplexity.ProgressionHash.LegalTriple
