/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import Mathlib.Combinatorics.Additive.AP.Three.Behrend
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.ZMod.Basic

/-!
# Progression-free sets in finite cyclic groups

Mathlib proves Behrend's lower bound for progression-free subsets of an initial interval of the
natural numbers.  Hashing arguments usually need such a set in `ZMod M`.  This file supplies the
paper-independent bridge: casting a set contained in `[0,N)` into `ZMod M` preserves
three-progression-freeness whenever `2N ≤ M`.

It also records the elementary positivity `rothNumberNat_pos` of Mathlib's Roth number, which
hashing counts need in order to keep a Behrend bound from degenerating.
-/

open scoped Pointwise

namespace AlgebraicComplexity

/-- A nonempty initial segment contains a progression-free singleton, so its Roth number is
positive. -/
theorem rothNumberNat_pos {m : ℕ} (hm : 0 < m) : 0 < rothNumberNat m := by
  have h : ({0} : Finset ℕ).card ≤ rothNumberNat m := by
    refine ThreeAPFree.le_addRothNumber (Set.Subsingleton.threeAPFree (by simp)) ?_
    simpa using hm
  have h1 : 1 ≤ rothNumberNat m := by simpa using h
  omega

/-- In a cyclic ring of modulus at least three, the element `2` is nonzero. -/
theorem neZero_two_zmod_of_three_le {M : ℕ} (hM : 3 ≤ M) : NeZero (2 : ZMod M) := by
  apply NeZero.of_not_dvd (ZMod M)
  intro hdiv
  have hle : M ≤ 2 := Nat.le_of_dvd (by norm_num) hdiv
  omega

/-- Natural-number casting into `ZMod M` is injective on any set lying below `N ≤ M`. -/
theorem natCast_zmod_injOn_of_subset_Iio {s : Set ℕ} {N M : ℕ}
    (hs : s ⊆ Set.Iio N) (hNM : N ≤ M) :
    s.InjOn (fun n : ℕ => (n : ZMod M)) := by
  intro a ha b hb hab
  exact CharP.natCast_injOn_Iio (R := ZMod M) M
    ((hs ha).trans_le hNM) ((hs hb).trans_le hNM) hab

/-- The sumset of a subset of `[0,N)` lies below `M` when `2N ≤ M`. -/
theorem add_subset_Iio_of_subset_Iio {s : Set ℕ} {N M : ℕ}
    (hs : s ⊆ Set.Iio N) (hNM : N + N ≤ M) :
    s + s ⊆ Set.Iio M := by
  rintro _ ⟨a, ha, b, hb, rfl⟩
  exact (Nat.add_lt_add (hs ha) (hs hb)).trans_le hNM

/-- A progression-free natural-number set remains progression-free after casting into `ZMod M`,
provided its pairwise sums do not wrap around the modulus. -/
theorem ThreeAPFree.natCast_zmod {s : Set ℕ} {N M : ℕ}
    (hfree : ThreeAPFree s) (hs : s ⊆ Set.Iio N) (hNM : N + N ≤ M) :
    ThreeAPFree ((fun n : ℕ => (n : ZMod M)) '' s) := by
  have hinj : (s + s).InjOn (fun n : ℕ => (n : ZMod M)) :=
    natCast_zmod_injOn_of_subset_Iio (add_subset_Iio_of_subset_Iio hs hNM) le_rfl
  simpa using hfree.image' (Nat.castAddMonoidHom (ZMod M)) hinj

/-- Finite cyclic version of Mathlib's extremal Roth-set witness.  The resulting set has exactly
`rothNumberNat N` elements and is progression-free in `ZMod M`. -/
theorem exists_threeAPFree_zmod_of_two_mul_le (N M : ℕ) (hNM : N + N ≤ M) :
    ∃ B : Finset (ZMod M), B.card = rothNumberNat N ∧ ThreeAPFree (B : Set (ZMod M)) := by
  classical
  obtain ⟨t, ht, hcard, hfree⟩ := rothNumberNat_spec N
  let castFun : ℕ → ZMod M := fun n => n
  let B : Finset (ZMod M) := t.image castFun
  have htIio : (t : Set ℕ) ⊆ Set.Iio N := by
    intro n hn
    exact Finset.mem_range.mp (ht hn)
  have hNleM : N ≤ M := (Nat.le_add_right N N).trans hNM
  have hinj : (t : Set ℕ).InjOn castFun := by
    exact natCast_zmod_injOn_of_subset_Iio htIio hNleM
  refine ⟨B, ?_, ?_⟩
  · change (t.image castFun).card = rothNumberNat N
    rw [Finset.card_image_of_injOn hinj, hcard]
  · have hzmod := AlgebraicComplexity.ThreeAPFree.natCast_zmod hfree htIio hNM
    simpa [B, castFun] using hzmod

/-- A canonical wraparound-safe choice uses the lower half of the cyclic group. -/
theorem exists_threeAPFree_zmod_half (M : ℕ) :
    ∃ B : Finset (ZMod M), B.card = rothNumberNat (M / 2) ∧
      ThreeAPFree (B : Set (ZMod M)) := by
  apply exists_threeAPFree_zmod_of_two_mul_le (M / 2) M
  omega

/-- The same half-interval construction together with Mathlib's explicit Behrend lower bound. -/
theorem exists_threeAPFree_zmod_half_behrend (M : ℕ) :
    ∃ B : Finset (ZMod M), ThreeAPFree (B : Set (ZMod M)) ∧
      ((M / 2 : ℕ) : ℝ) * Real.exp (-4 * √(Real.log (M / 2 : ℕ))) ≤ B.card := by
  obtain ⟨B, hcard, hfree⟩ := exists_threeAPFree_zmod_half M
  refine ⟨B, hfree, ?_⟩
  rw [hcard]
  exact Behrend.roth_lower_bound

end AlgebraicComplexity
