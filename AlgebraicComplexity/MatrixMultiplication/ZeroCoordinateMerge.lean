/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.WholeConstituentLaserVolumeAssembly

/-!
# Merged zero-coordinate leaf dimensions

A laser-method node whose shape has a zero coordinate carries one common block word on that
coordinate, so its whole selected class is a shared-leg C-tensor rather than a family from which
one representative must be chosen.  Taking the class whole replaces a single fine address's
dimension `q ^ ones s` by the *merged* dimension `∑ s, q ^ ones s`.

This module supplies the two arithmetic halves of that step that need no new tensor algebra.

* `mergedDimension` and its comparisons: the merged dimension dominates every fine address, is at
  least the class cardinality (the support-multiplicity content) and is exactly
  `card * q ^ k` on a class of uniform `ones` — the shape the *committed* uniform one-slice
  fusion produces.
* `exists_uniform_fibre_mergedDimension_le`: the division-free pigeonhole that says how much a
  uniform sub-class can lose, namely a factor of the number of available `ones` values.  This is
  the estimate that decides whether the committed uniform fusion suffices.
* `stageOfRestricts` and three `WholeConstituentLaserVolumeStage` absorptions, one per leg: the
  named points at which a merged class dimension enters a leaf.
  `WholeConstituentLaserVolumeStage.external` already multiplies all three dimensions exactly, over
  `Tensor.Isomorphic.matrixMultiplication_external`, so no new tensor algebra is needed to carry a
  merged factor `⟨N,1,1⟩`, `⟨1,N,1⟩` or `⟨1,1,N⟩` through an assembly.

No Coppersmith--Winograd constants, no certificate data and no asymptotic estimate occurs here;
the leg-permuted *support* laws and the non-uniform fusion are deliberately not assumed.

**Dependency note.**  This module imports only tracked, building modules.  The shared-leg support
theorems and the one-slice fusion that would supply the `Restricts … ⟨1,N,1⟩` input to
`stageOfRestricts` currently live in untracked working-tree files, one of which does not elaborate;
until they land, `stageOfRestricts` is stated against a bare restriction so that a client can
supply that input from any source.
-/

namespace AlgebraicComplexity

open Tensor

universe u v w z

namespace ZeroCoordinateMerge

/-! ## The merged dimension of one zero-coordinate class -/

section Arithmetic

variable {ι : Type*}

/-- **The merged dimension of a zero-coordinate class.**  Each member `s` of the class contributes
a fine matrix dimension `q ^ ones s`; taking the class whole contributes their sum. -/
def mergedDimension (q : ℕ) (ones : ι → ℕ) (cls : Finset ι) : ℕ :=
  ∑ s ∈ cls, q ^ ones s

@[simp] theorem mergedDimension_empty (q : ℕ) (ones : ι → ℕ) :
    mergedDimension q ones (∅ : Finset ι) = 0 :=
  Finset.sum_empty

@[simp] theorem mergedDimension_singleton [DecidableEq ι] (q : ℕ) (ones : ι → ℕ) (s : ι) :
    mergedDimension q ones {s} = q ^ ones s :=
  Finset.sum_singleton _ _

/-- **The merge never loses.**  Every fine address of the class has dimension at most the merged
dimension; this is the inequality the volume side needs. -/
theorem pow_ones_le_mergedDimension (q : ℕ) (ones : ι → ℕ) {cls : Finset ι} {s : ι}
    (hs : s ∈ cls) : q ^ ones s ≤ mergedDimension q ones cls :=
  Finset.single_le_sum (f := fun t ↦ q ^ ones t) (fun _ _ ↦ Nat.zero_le _) hs

/-- A nonempty class with positive base has positive merged dimension. -/
theorem mergedDimension_pos (q : ℕ) (hq : 0 < q) (ones : ι → ℕ) {cls : Finset ι}
    (hne : cls.Nonempty) : 0 < mergedDimension q ones cls := by
  obtain ⟨s, hs⟩ := hne
  exact lt_of_lt_of_le (pow_pos hq (ones s)) (pow_ones_le_mergedDimension q ones hs)

/-- **The support-multiplicity content.**  At base at least one the merged dimension dominates the
class cardinality, so the merge retains the entire type class rather than one representative. -/
theorem card_le_mergedDimension {q : ℕ} (hq : 1 ≤ q) (ones : ι → ℕ) (cls : Finset ι) :
    cls.card ≤ mergedDimension q ones cls := by
  classical
  calc cls.card = ∑ _s ∈ cls, 1 := by simp
    _ ≤ ∑ s ∈ cls, q ^ ones s :=
        Finset.sum_le_sum fun s _ ↦ Nat.one_le_pow _ _ hq
    _ = mergedDimension q ones cls := rfl

/-- A uniform bound on `ones` bounds the merged dimension by the class cardinality times the
common power. -/
theorem mergedDimension_le_card_mul_pow {q : ℕ} (hq : 1 ≤ q) (ones : ι → ℕ) (cls : Finset ι)
    {k : ℕ} (hbound : ∀ s ∈ cls, ones s ≤ k) :
    mergedDimension q ones cls ≤ cls.card * q ^ k := by
  classical
  calc mergedDimension q ones cls ≤ ∑ _s ∈ cls, q ^ k :=
        Finset.sum_le_sum fun s hs ↦ Nat.pow_le_pow_right hq (hbound s hs)
    _ = cls.card * q ^ k := by simp [Finset.sum_const, smul_eq_mul]

/-- **A class of uniform `ones` merges to exactly `card * q ^ k`** — the shape the committed
uniform one-slice fusion `CTensorOneSliceFusion` produces.  On such a class the merge costs
nothing beyond the fusion. -/
theorem mergedDimension_of_uniform (q : ℕ) (ones : ι → ℕ) (cls : Finset ι) {k : ℕ}
    (huniform : ∀ s ∈ cls, ones s = k) :
    mergedDimension q ones cls = cls.card * q ^ k := by
  classical
  calc mergedDimension q ones cls = ∑ _s ∈ cls, q ^ k :=
        Finset.sum_congr rfl fun s hs ↦ by rw [huniform s hs]
    _ = cls.card * q ^ k := by simp [Finset.sum_const, smul_eq_mul]

/-- **The uniform-sub-class pigeonhole, division free.**  If `ones` takes at most `bound + 1`
values on the class, then some single value `k` carries at least a `1 / (bound + 1)` share of the
merged dimension.

This is the exact price of dodging a non-uniform fusion by restricting to a uniform sub-class:
the loss factor is the number of available `ones` values, once per merged class. -/
theorem exists_uniform_fibre_mergedDimension_le [DecidableEq ι]
    (q : ℕ) (ones : ι → ℕ) (cls : Finset ι) (bound : ℕ)
    (hmaps : ∀ s ∈ cls, ones s ∈ Finset.range (bound + 1)) :
    ∃ k ∈ Finset.range (bound + 1),
      mergedDimension q ones cls ≤
        (bound + 1) * mergedDimension q ones (cls.filter fun s ↦ ones s = k) := by
  classical
  set total := mergedDimension q ones cls with htotal
  set fibre : ℕ → ℕ := fun k ↦ mergedDimension q ones (cls.filter fun s ↦ ones s = k) with hfibre
  have hsplit : ∑ k ∈ Finset.range (bound + 1), fibre k = total := by
    simpa only [hfibre, htotal, mergedDimension] using
      Finset.sum_fiberwise_of_maps_to hmaps (fun s ↦ q ^ ones s)
  by_contra hcontra
  simp only [not_exists, not_and, not_le] at hcontra
  have hstrict : ∀ k ∈ Finset.range (bound + 1), (bound + 1) * fibre k < total :=
    fun k hk ↦ hcontra k hk
  have hne : (Finset.range (bound + 1)).Nonempty := ⟨0, Finset.mem_range.mpr (Nat.succ_pos _)⟩
  have hsum : ∑ k ∈ Finset.range (bound + 1), (bound + 1) * fibre k <
      ∑ _k ∈ Finset.range (bound + 1), total :=
    Finset.sum_lt_sum_of_nonempty hne hstrict
  rw [← Finset.mul_sum, hsplit, Finset.sum_const, Finset.card_range, smul_eq_mul] at hsum
  exact absurd hsum (lt_irrefl _)

end Arithmetic

/-! ## Absorbing a merged one-slice factor into a whole-constituent stage

`WholeConstituentLaserVolumeStage.external` already multiplies all three rectangular dimensions
exactly, over the committed isomorphism `⟨a,b,c⟩ ⊠ ⟨a',b',c'⟩ ≅ ⟨aa',bb',cc'⟩`.  The three
declarations below are its specializations at a merged one-slice factor, one per leg: they are
the named points at which a zero-coordinate class's merged dimension enters a leaf. -/

section Absorption

variable (K : Type u) [CommSemiring K]
variable {V : Leg → Type v} [∀ c, AddCommMonoid (V c)] [∀ c, Module K (V c)]
variable {W : Leg → Type w} [∀ c, AddCommMonoid (W c)] [∀ c, Module K (W c)]

/-- **A one-copy stage from a bare restriction.**  Any restriction onto a single rectangular
matrix-multiplication tensor is a whole-constituent stage with one copy. -/
noncomputable def stageOfRestricts
    {source : Tensor3 K V} {xSize ySize zSize : ℕ}
    (hrestricts : Restricts source (matrixMultiplication (K := K) xSize ySize zSize)) :
    WholeConstituentLaserVolumeStage.{u, v, z} K source 1 xSize ySize zSize where
  I := PUnit.{z + 1}
  card_I := Fintype.card_punit
  source_restricts := by
    refine hrestricts.trans ?_
    simpa only [matrixMultiplicationDirectSum] using
      (Tensor.Isomorphic.indexedDirectSum_unique (K := K) (ι := PUnit.{z + 1})
        (matrixMultiplication (K := K) xSize ySize zSize)).symm.restricts

/-- Absorb a merged `⟨N,1,1⟩` factor into a stage's first rectangular dimension. -/
noncomputable def mergeX
    {source : Tensor3 K V} {factor : Tensor3 K W}
    {copies xSize ySize zSize merged : ℕ}
    (stage : WholeConstituentLaserVolumeStage K source copies xSize ySize zSize)
    (mergeFactor : WholeConstituentLaserVolumeStage K factor 1 merged 1 1) :
    WholeConstituentLaserVolumeStage K (Tensor.external source factor)
      copies (xSize * merged) ySize zSize := by
  simpa only [Nat.mul_one] using
    WholeConstituentLaserVolumeStage.external K stage mergeFactor

/-- Absorb a merged `⟨1,N,1⟩` factor into a stage's second rectangular dimension.  This is the
orientation the committed one-slice fusion produces. -/
noncomputable def mergeY
    {source : Tensor3 K V} {factor : Tensor3 K W}
    {copies xSize ySize zSize merged : ℕ}
    (stage : WholeConstituentLaserVolumeStage K source copies xSize ySize zSize)
    (mergeFactor : WholeConstituentLaserVolumeStage K factor 1 1 merged 1) :
    WholeConstituentLaserVolumeStage K (Tensor.external source factor)
      copies xSize (ySize * merged) zSize := by
  simpa only [Nat.mul_one] using
    WholeConstituentLaserVolumeStage.external K stage mergeFactor

/-- Absorb a merged `⟨1,1,N⟩` factor into a stage's third rectangular dimension. -/
noncomputable def mergeZ
    {source : Tensor3 K V} {factor : Tensor3 K W}
    {copies xSize ySize zSize merged : ℕ}
    (stage : WholeConstituentLaserVolumeStage K source copies xSize ySize zSize)
    (mergeFactor : WholeConstituentLaserVolumeStage K factor 1 1 1 merged) :
    WholeConstituentLaserVolumeStage K (Tensor.external source factor)
      copies xSize ySize (zSize * merged) := by
  simpa only [Nat.mul_one] using
    WholeConstituentLaserVolumeStage.external K stage mergeFactor

end Absorption

end ZeroCoordinateMerge

end AlgebraicComplexity
