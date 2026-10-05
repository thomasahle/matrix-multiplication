/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Combinatorics.ComplementaryPairFiber
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Finset.Sym

/-!
# Pooled complementary-orbit categories

`pooledOrbitCategory` remembers every relevant unordered orbit of an involution and sends all
irrelevant states to one pooled `none` category.  Equal relevant-orbit sums and equal total mass
then imply equality of the complete pushed profiles.  This is useful when a compatibility
condition exposes boundary orbits individually but deliberately pools the interior.

The proof needs only the literal two-point fiber theorem from `ComplementaryPairFiber`; it does
not depend on the stronger arbitrary-representative enumeration in
`UnlabelledComplementaryOrbit`.
-/

open scoped BigOperators

namespace AlgebraicComplexity.WordType

universe u

variable {Split : Type u} [Fintype Split] [DecidableEq Split]

omit [Fintype Split] [DecidableEq Split] in
/-- Categorize a relevant state by its unordered dual orbit and pool every irrelevant state into
one `none` category. -/
def pooledOrbitCategory (dual : Split → Split) (relevant : Split → Prop)
    [DecidablePred relevant] (u : Split) : Option (Sym2 Split) :=
  if relevant u then some s(u, dual u) else none

omit [Fintype Split] [DecidableEq Split] in
/-- Applying an involution does not change its pooled orbit category when relevance is invariant.

Proof sketch: relevant states give the same unordered pair with its two entries swapped; irrelevant
states give `none` on both sides. -/
theorem pooledOrbitCategory_dual
    (dual : Split → Split) (hdual : Function.Involutive dual)
    (relevant : Split → Prop) [DecidablePred relevant]
    (hrelevant : ∀ u, relevant (dual u) ↔ relevant u) (u : Split) :
    pooledOrbitCategory dual relevant (dual u) = pooledOrbitCategory dual relevant u := by
  by_cases h : relevant u
  · have hd : relevant (dual u) := (hrelevant u).2 h
    simp [pooledOrbitCategory, h, hd, hdual u, Sym2.eq_swap]
  · have hd : ¬relevant (dual u) := fun hd ↦ h ((hrelevant u).1 hd)
    simp [pooledOrbitCategory, h, hd]

/-- Equal masses on every relevant unordered orbit, together with equal total mass, give equal
pushforwards to the relevant-orbit/interior-pool category.

At a non-fixed orbit the hypothesis is already the required two-point fiber equality.  At a fixed
point it reads `p u + p u = q u + q u`, so cancellation recovers the one-point fiber equality.
Every unrepresented `some` category has zero mass.  Finally, after all `some` coordinates agree,
mass preservation determines the pooled `none` coordinate. -/
theorem mappedType_pooledOrbitCategory_eq
    (dual : Split → Split) (hdual : Function.Involutive dual)
    (relevant : Split → Prop) [DecidablePred relevant]
    (hrelevant : ∀ u, relevant (dual u) ↔ relevant u)
    (p q : Split → ℕ) (hmass : profileMass p = profileMass q)
    (horbit : ∀ u, relevant u → p u + p (dual u) = q u + q (dual u)) :
    mappedType (pooledOrbitCategory dual relevant) p =
      mappedType (pooledOrbitCategory dual relevant) q := by
  classical
  let category := pooledOrbitCategory dual relevant
  have hcategoryDual (u : Split) : category (dual u) = category u := by
    exact pooledOrbitCategory_dual dual hdual relevant hrelevant u
  have hsome (orbit : Sym2 Split) :
      mappedType category p (some orbit) = mappedType category q (some orbit) := by
    by_cases hpreimage : ∃ u, category u = some orbit
    · obtain ⟨u, hu⟩ := hpreimage
      have hrel : relevant u := by
        by_contra hnot
        simp [category, pooledOrbitCategory, hnot] at hu
      have hfiber : ∀ v, category v = category u → v = u ∨ v = dual u := by
        intro v hv
        have hvrel : relevant v := by
          by_contra hnot
          simp [category, pooledOrbitCategory, hnot, hrel] at hv
        have hpairs : s(v, dual v) = s(u, dual u) := by
          apply Option.some.inj
          simpa [category, pooledOrbitCategory, hvrel, hrel] using hv
        have hmem : v ∈ s(u, dual u) := by
          rw [← hpairs]
          exact Sym2.mem_iff'.2 (Or.inl rfl)
        exact Sym2.mem_iff'.1 hmem
      have hp := mappedType_apply_of_complementary_pair
        category dual hdual hcategoryDual p u hfiber
      have hq := mappedType_apply_of_complementary_pair
        category dual hdual hcategoryDual q u hfiber
      rw [hu] at hp hq
      rw [hp, hq]
      by_cases hfixed : dual u = u
      · have hsingle : p u = q u := by
          apply Nat.mul_left_cancel (Nat.succ_pos 1)
          simpa [Nat.two_mul, hfixed] using horbit u hrel
        simp [hfixed, hsingle]
      · simpa [hfixed] using horbit u hrel
    · have hzero (r : Split → ℕ) : mappedType category r (some orbit) = 0 := by
        rw [mappedType_eq_sum_ite]
        apply Finset.sum_eq_zero
        intro u _
        have hne : category u ≠ some orbit := fun h ↦ hpreimage ⟨u, h⟩
        simp [hne]
      rw [hzero p, hzero q]
  have hsumSome :
      (∑ orbit : Sym2 Split, mappedType category p (some orbit)) =
        ∑ orbit : Sym2 Split, mappedType category q (some orbit) := by
    apply Finset.sum_congr rfl
    intro orbit _
    exact hsome orbit
  have hnone : mappedType category p none = mappedType category q none := by
    apply Nat.add_left_cancel (n := ∑ orbit : Sym2 Split,
      mappedType category p (some orbit))
    calc
      (∑ orbit : Sym2 Split, mappedType category p (some orbit)) +
          mappedType category p none = profileMass (mappedType category p) := by
        simp [profileMass, Fintype.sum_option, add_comm]
      _ = profileMass p := profileMass_mappedType category p
      _ = profileMass q := hmass
      _ = profileMass (mappedType category q) :=
        (profileMass_mappedType category q).symm
      _ = (∑ orbit : Sym2 Split, mappedType category q (some orbit)) +
          mappedType category q none := by
        simp [profileMass, Fintype.sum_option, add_comm]
      _ = (∑ orbit : Sym2 Split, mappedType category p (some orbit)) +
          mappedType category q none := by rw [hsumSome]
  change mappedType category p = mappedType category q
  funext value
  cases value with
  | none => exact hnone
  | some orbit => exact hsome orbit

end AlgebraicComplexity.WordType
