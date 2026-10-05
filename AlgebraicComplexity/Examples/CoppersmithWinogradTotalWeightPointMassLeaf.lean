/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinogradTotalWeightEmbeddedInnerExtraction
import AlgebraicComplexity.Examples.CoppersmithWinogradTotalWeightInnerGrowthDepthFour

set_option autoImplicit false

/-!
# Marginal rigidity of a point-mass chunk profile, and the one-letter chunk leaf

This module closes the first of the two options listed in `tmp/S3-S4-S6-handoff.md` §S4.7.1 for
discharging the conditional maximum-entropy input of a *sparse* chunk profile, and uses it to build
a hypothesis-free inner growth datum at **any** prescribed profile mass.

## The rigidity criterion

`WordType.isMaximumEntropyInMappedFiber_of_pointMass` is general: if the visible coordinate family
is *jointly injective* — the letter is determined by the tuple of its coordinates — then a law
concentrated on a single letter maximizes entropy in its mapped fiber, because the fiber contains
no other law at all.  Note that joint injectivity does **not** make every law rigid: matching each
coordinate marginal separately does not pin a joint law down (that is exactly why the Gibbs
criterion `isMaximumEntropyInMappedFiber_of_logLinear` is needed for spread profiles).  It is only
the point mass whose fiber collapses.

A chunk letter is jointly determined by its three leg words (`cwChunkCoordinate` is literally the
address projection), so the criterion applies to `cwChunkPartitionedTensor K q depth` at every
depth: `cwChunkPointProfile_isMaximumEntropy`.

## The one-letter leaf

`cwChunkPointLeaf` is the rational typed leaf on a one-element alphabet that spends all of its mass
`m` on a single chunk letter `s`, with the canonical chunk dimensions.  Together with
`cwChunkPointEmbedding` it is the smallest inhabitant of the sparse/embedded interface used by the
acceptance assemblies, and `cwChunkPointGrowthDatum` is the resulting
`CWTotalWeightInnerGrowthDataAtDepth`, whose positive-power exponent is `m * k − 1` for the
prescribed `m` — with `ambient_upper` and the maximum-entropy input both *proved*.

That is what makes it a feasibility witness for an index convention: at depth `d` a chunk-aligned
outer datum has `n r = m · r − 1` with `2 ^ d · m = 8 · stride`, and this leaf realizes that `m`
whenever `m > 0`, for any depth.  What it does *not* do is carry an inner rate: a point mass has
zero conditional entropy, so the accompanying `hWrate` fails.  It separates the two failure modes —
index alignment and rate — which at depth four were entangled (there, mass `19` over a
`6 ^ 16`-letter alphabet is impossible outright, see
`no_levelFour_leaf_growthData_matches_outerExponent`).

The rectangular volume of the leaf is exact: `cwChunkPointLeaf_volume` gives
`(q ^ 2 ^ depth) ^ m` for the all-`cw011` letter, i.e. every one of the `2 ^ depth · m` `CW_q`
letters of a stride block carries a volume-`q` block.
-/

namespace AlgebraicComplexity

open Tensor
open scoped BigOperators

universe u v w

namespace WordType

variable {I : Type u} [Fintype I]
variable {C : Type v} [Fintype C]
variable {A : C → Type w} [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]

omit [Fintype C] in
/-- **Marginal rigidity of a point mass.**

If the letter of a finite alphabet is determined by the tuple of its visible coordinates, then a
profile concentrated on one letter has a *singleton* mapped fiber: any law with the same visible
pushforwards is the same law.  Hence it maximizes entropy there, with no positivity, no Gibbs
potential and no structural input.

This is the criterion named in `tmp/S3-S4-S6-handoff.md` §S4.7.1 as the first way to discharge the
maximum-entropy hypothesis of a sparse profile, for which
`isMaximumEntropyInMappedFiber_of_logLinear` (which needs strict positivity on the whole alphabet)
is unavailable. -/
theorem isMaximumEntropyInMappedFiber_of_pointMass
    (coordinate : ∀ c, I → A c)
    (hinj : ∀ i j : I, (∀ c, coordinate c i = coordinate c j) → i = j)
    (a : I → ℕ) (hmass : 0 < profileMass a) (i₀ : I)
    (hzero : ∀ i, i ≠ i₀ → a i = 0) :
    IsMaximumEntropyInMappedFiber coordinate (normalizedProfileProbability a hmass) := by
  classical
  intro q hq
  set p := normalizedProfileProbability a hmass with hp
  have hpzero : ∀ i, i ≠ i₀ → p.weight i = 0 := by
    intro i hi
    rw [hp, normalizedProfileProbability_weight, hzero i hi]
    simp
  -- every letter carrying `q`-mass agrees with `i₀` in all coordinates, hence *is* `i₀`
  have hqzero : ∀ i, i ≠ i₀ → q.weight i = 0 := by
    intro i hi
    by_contra hne
    have hpos : 0 < q.weight i := lt_of_le_of_ne (q.nonneg i) (Ne.symm hne)
    have hcoord : ∀ c, coordinate c i = coordinate c i₀ := by
      intro c
      by_contra hcne
      have hzeroPush : (p.pushforward (coordinate c)).weight (coordinate c i) = 0 := by
        rw [ProbabilityVector.pushforward_weight]
        refine Finset.sum_eq_zero ?_
        intro j _
        by_cases hj : coordinate c j = coordinate c i
        · by_cases hj0 : j = i₀
          · subst hj0
            exact absurd hj.symm hcne
          · simp [hj, hpzero j hj0]
        · simp [hj]
      have hposPush : 0 < (q.pushforward (coordinate c)).weight (coordinate c i) := by
        rw [ProbabilityVector.pushforward_weight]
        refine Finset.sum_pos' (fun j _ ↦ ?_) ⟨i, Finset.mem_univ i, by simp [hpos]⟩
        by_cases hj : coordinate c j = coordinate c i
        · simpa [hj] using q.nonneg j
        · simp [hj]
      rw [hq c, hzeroPush] at hposPush
      exact lt_irrefl 0 hposPush
    exact hi (hinj i i₀ hcoord)
  have hone : ∀ r : ProbabilityVector I, (∀ i, i ≠ i₀ → r.weight i = 0) → r.weight i₀ = 1 := by
    intro r hr
    have hsum : ∑ i, r.weight i = r.weight i₀ :=
      Finset.sum_eq_single i₀ (fun b _ hb ↦ hr b hb) (fun h ↦ absurd (Finset.mem_univ i₀) h)
    rw [← hsum, r.total]
  have hweq : ∀ i, q.weight i = p.weight i := by
    intro i
    by_cases hi : i = i₀
    · subst hi
      rw [hone q hqzero, hone p hpzero]
    · rw [hqzero i hi, hpzero i hi]
  refine le_of_eq ?_
  unfold ProbabilityVector.entropy
  exact Finset.sum_congr rfl fun i _ ↦ by rw [hweq i]

end WordType

namespace Examples

open AlgebraicComplexity.WordType

/-! ## Joint injectivity of the chunk coordinates -/

/-- A supported chunk letter is determined by its three leg words: `cwChunkCoordinate` is the
address projection, so the coordinate family is jointly injective. -/
theorem cwChunkCoordinate_jointly_injective
    (K : Type u) [CommRing K] (q depth : ℕ)
    (s t : (cwChunkPartitionedTensor K q depth).support)
    (h : ∀ c, cwChunkCoordinate K q depth c s = cwChunkCoordinate K q depth c t) :
    s = t := by
  apply Subtype.ext
  funext c
  exact h c

/-- Any chunk profile concentrated on a single letter maximizes entropy in its three-leg mapped
fiber, at every depth. -/
theorem cwChunkPointProfile_isMaximumEntropy
    (K : Type u) [CommRing K] (q depth : ℕ)
    (a : (cwChunkPartitionedTensor K q depth).support → ℕ)
    (hmass : 0 < WordType.profileMass a)
    (s : (cwChunkPartitionedTensor K q depth).support)
    (hzero : ∀ t, t ≠ s → a t = 0) :
    WordType.IsMaximumEntropyInMappedFiber (cwChunkCoordinate K q depth)
      (WordType.normalizedProfileProbability a hmass) :=
  WordType.isMaximumEntropyInMappedFiber_of_pointMass (cwChunkCoordinate K q depth)
    (cwChunkCoordinate_jointly_injective K q depth) a hmass s hzero

/-! ## The one-letter chunk leaf -/

/-- The rational typed leaf on a one-element alphabet spending mass `m` on the chunk letter `s`,
with the canonical chunk dimensions. -/
noncomputable def cwChunkPointLeaf
    (K : Type u) [CommRing K] (q depth : ℕ) (hq : 0 < q)
    (s : (cwChunkPartitionedTensor K q depth).support) (m : ℕ) (hm : 0 < m) :
    RationalTypedLeaf (Fin 1) (fun _c : Leg ↦ PositiveWord CWBlock (2 ^ depth - 1)) where
  profile :=
    { alphabet := Finset.univ
      complete := fun i ↦ Finset.mem_univ i
      count := fun _ ↦ m
      count_pos := fun _ ↦ hm }
  coordinate := fun c _ ↦ cwChunkCoordinate K q depth c s
  dimension := fun _ c ↦ cwChunkConstituentDimension K q depth s c
  dimension_pos := fun _ c ↦ cwChunkConstituentDimension_pos K q depth hq s c

@[simp] theorem cwChunkPointLeaf_count
    (K : Type u) [CommRing K] (q depth : ℕ) (hq : 0 < q)
    (s : (cwChunkPartitionedTensor K q depth).support) (m : ℕ) (hm : 0 < m) (i : Fin 1) :
    (cwChunkPointLeaf K q depth hq s m hm).profile.count i = m :=
  rfl

/-- The leaf carries exactly the canonical chunk dimensions of its single letter, which is the
`hdimension` hypothesis of the embedded inner constructor. -/
theorem cwChunkPointLeaf_dimension
    (K : Type u) [CommRing K] (q depth : ℕ) (hq : 0 < q)
    (s : (cwChunkPartitionedTensor K q depth).support) (m : ℕ) (hm : 0 < m)
    (i : Fin 1) (c : Leg) :
    (cwChunkPointLeaf K q depth hq s m hm).dimension i c =
      cwChunkConstituentDimension K q depth s c :=
  rfl

/-- The one-letter alphabet, embedded at the chosen chunk letter. -/
def cwChunkPointEmbedding
    (K : Type u) [CommRing K] (q depth : ℕ)
    (s : (cwChunkPartitionedTensor K q depth).support) :
    Fin 1 ↪ (cwChunkPartitionedTensor K q depth).support where
  toFun := fun _ ↦ s
  inj' := fun a b _ ↦ Subsingleton.elim a b

/-- The zero-extension of the one-letter leaf is the point-mass profile at `s`. -/
theorem cwEmbeddedChunkProfile_point
    (K : Type u) [CommRing K] (q depth : ℕ) (hq : 0 < q)
    (s : (cwChunkPartitionedTensor K q depth).support) (m : ℕ) (hm : 0 < m)
    (t : (cwChunkPartitionedTensor K q depth).support) :
    cwEmbeddedChunkProfile (cwChunkPointLeaf K q depth hq s m hm)
        (cwChunkPointEmbedding K q depth s) t = if t = s then m else 0 := by
  classical
  unfold cwEmbeddedChunkProfile WordType.mappedType
  by_cases h : t = s
  · subst h
    have hf : WordType.letterFiber (cwChunkPointEmbedding K q depth t) t =
        (Finset.univ : Finset (Fin 1)) := by
      refine Finset.eq_univ_iff_forall.mpr ?_
      intro i
      rw [WordType.mem_letterFiber]
      rfl
    rw [hf, if_pos rfl]
    simp
  · have hf : WordType.letterFiber (cwChunkPointEmbedding K q depth s) t = ∅ := by
      refine Finset.eq_empty_iff_forall_notMem.mpr ?_
      intro i hi
      rw [WordType.mem_letterFiber] at hi
      have happ : (cwChunkPointEmbedding K q depth s) i = s := rfl
      rw [happ] at hi
      exact h hi.symm
    rw [hf, if_neg h]
    simp

/-- Off its single letter the point profile vanishes. -/
theorem cwEmbeddedChunkProfile_point_zero
    (K : Type u) [CommRing K] (q depth : ℕ) (hq : 0 < q)
    (s : (cwChunkPartitionedTensor K q depth).support) (m : ℕ) (hm : 0 < m)
    (t : (cwChunkPartitionedTensor K q depth).support) (ht : t ≠ s) :
    cwEmbeddedChunkProfile (cwChunkPointLeaf K q depth hq s m hm)
      (cwChunkPointEmbedding K q depth s) t = 0 := by
  rw [cwEmbeddedChunkProfile_point, if_neg ht]

/-- The point profile has mass exactly `m`. -/
theorem profileMass_cwEmbeddedChunkProfile_point
    (K : Type u) [CommRing K] (q depth : ℕ) (hq : 0 < q)
    (s : (cwChunkPartitionedTensor K q depth).support) (m : ℕ) (hm : 0 < m) :
    WordType.profileMass (cwEmbeddedChunkProfile (cwChunkPointLeaf K q depth hq s m hm)
      (cwChunkPointEmbedding K q depth s)) = m := by
  rw [profileMass_cwEmbeddedChunkProfile]
  show WordType.profileMass (fun _ : Fin 1 ↦ m) = m
  simp [WordType.profileMass]

theorem profileMass_cwEmbeddedChunkProfile_point_pos
    (K : Type u) [CommRing K] (q depth : ℕ) (hq : 0 < q)
    (s : (cwChunkPartitionedTensor K q depth).support) (m : ℕ) (hm : 0 < m) :
    0 < WordType.profileMass (cwEmbeddedChunkProfile (cwChunkPointLeaf K q depth hq s m hm)
      (cwChunkPointEmbedding K q depth s)) := by
  rw [profileMass_cwEmbeddedChunkProfile_point]
  exact hm

/-- The maximum-entropy input, discharged for the one-letter leaf by rigidity. -/
theorem cwChunkPointLeaf_maximumEntropy
    (K : Type u) [CommRing K] (q depth : ℕ) (hq : 0 < q)
    (s : (cwChunkPartitionedTensor K q depth).support) (m : ℕ) (hm : 0 < m) :
    WordType.IsMaximumEntropyInMappedFiber (cwChunkCoordinate K q depth)
      (WordType.normalizedProfileProbability
        (cwEmbeddedChunkProfile (cwChunkPointLeaf K q depth hq s m hm)
          (cwChunkPointEmbedding K q depth s))
        (profileMass_cwEmbeddedChunkProfile_point_pos K q depth hq s m hm)) :=
  cwChunkPointProfile_isMaximumEntropy K q depth _ _ s
    (fun t ht ↦ cwEmbeddedChunkProfile_point_zero K q depth hq s m hm t ht)

/-- **A hypothesis-free inner growth datum at any prescribed mass**, at every depth.

Both quantitative fields are proved: `ambient_upper` by S4's zero-safe maximum-entropy bound, and
the maximum-entropy input itself by rigidity of the point mass. -/
noncomputable def cwChunkPointGrowthDatum
    (K : Type u) [CommRing K] (q depth : ℕ) (hq : 0 < q)
    (s : (cwChunkPartitionedTensor K q depth).support) (m : ℕ) (hm : 0 < m) :
    CWTotalWeightInnerGrowthDataAtDepth K q depth
      (cwEmbeddedChunkProfile (cwChunkPointLeaf K q depth hq s m hm)
        (cwChunkPointEmbedding K q depth s))
      (cwChunkAmbientEntropyBase (cwEmbeddedChunkProfile (cwChunkPointLeaf K q depth hq s m hm)
        (cwChunkPointEmbedding K q depth s)))
      (cwChunkAmbientTypeLoss (cwEmbeddedChunkProfile (cwChunkPointLeaf K q depth hq s m hm)
        (cwChunkPointEmbedding K q depth s))) :=
  cwChunkInnerGrowthDataOfMaximumEntropyZeroSafe K q depth _
    (profileMass_cwEmbeddedChunkProfile_point_pos K q depth hq s m hm)
    (cwChunkPointLeaf_maximumEntropy K q depth hq s m hm)

/-- The witness realizes the index convention `m · k − 1` exactly. -/
@[simp] theorem cwChunkPointGrowthDatum_exponent
    (K : Type u) [CommRing K] (q depth : ℕ) (hq : 0 < q)
    (s : (cwChunkPartitionedTensor K q depth).support) (m : ℕ) (hm : 0 < m) (k : ℕ) :
    (cwChunkPointGrowthDatum K q depth hq s m hm).exponent k = m * k - 1 := by
  rw [cwChunkPointGrowthDatum, cwChunkInnerGrowthDataOfMaximumEntropyZeroSafe_exponent,
    profileMass_cwEmbeddedChunkProfile_point]

/-! ## The exact rectangular volume of the one-letter leaf -/

/-- The three dimension products of the one-letter leaf multiply to the letter's own rectangular
volume raised to the mass. -/
theorem cwChunkPointLeaf_dimensionProduct
    (K : Type u) [CommRing K] (q depth : ℕ) (hq : 0 < q)
    (s : (cwChunkPartitionedTensor K q depth).support) (m : ℕ) (hm : 0 < m) :
    (cwChunkPointLeaf K q depth hq s m hm).dimensionProduct .X *
        (cwChunkPointLeaf K q depth hq s m hm).dimensionProduct .Y *
        (cwChunkPointLeaf K q depth hq s m hm).dimensionProduct .Z =
      (cwChunkConstituentDimension K q depth s .X *
        cwChunkConstituentDimension K q depth s .Y *
        cwChunkConstituentDimension K q depth s .Z) ^ m := by
  have hprod : ∀ c : Leg, (cwChunkPointLeaf K q depth hq s m hm).dimensionProduct c =
      cwChunkConstituentDimension K q depth s c ^ m := by
    intro c
    show (∏ _i ∈ (Finset.univ : Finset (Fin 1)),
      cwChunkConstituentDimension K q depth s c ^ m) = _
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, pow_one]
  rw [hprod, hprod, hprod, mul_pow, mul_pow]

/-- For the maximal-volume (all-`cw011`) chunk letter the volume is exactly `(q ^ 2 ^ depth) ^ m`:
every one of the `2 ^ depth · m` `CW_q` letters of the block carries a volume-`q` block. -/
theorem cwChunkPointLeaf_oneTypeWitness_volume
    (K : Type u) [CommRing K] (q depth : ℕ) (hq : 0 < q) (m : ℕ) (hm : 0 < m) :
    (cwChunkPointLeaf K q depth hq (cwChunkOneTypeWitness K q depth) m hm).dimensionProduct .X *
        (cwChunkPointLeaf K q depth hq (cwChunkOneTypeWitness K q depth) m
          hm).dimensionProduct .Y *
        (cwChunkPointLeaf K q depth hq (cwChunkOneTypeWitness K q depth) m
          hm).dimensionProduct .Z =
      (q ^ 2 ^ depth) ^ m := by
  rw [cwChunkPointLeaf_dimensionProduct, cwChunk_oneTypeWitness_volume]

end Examples

end AlgebraicComplexity
