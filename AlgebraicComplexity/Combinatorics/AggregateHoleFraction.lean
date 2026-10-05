/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring

set_option autoImplicit false

/-!
# Aggregate hole fractions and the Markov retention pass

Layer 2 (`AlgebraicComplexity/Combinatorics/`).  A *hole family* is a map
`holes : ι → Finset A` from a finite index type of copies to subsets of a finite alphabet:
`holes t`
is the set of alphabet letters that copy `t` fails to realize.  Hole-repair arguments need a
per-copy bound `8 * (holes t).card ≤ Fintype.card A`, but probabilistic constructions only ever
produce the *average* bound

`16 * ∑ t, (holes t).card ≤ Fintype.card ι * Fintype.card A`,

which is what `AggregateHoleFraction` names.  Markov's inequality converts one into the other at
the cost of discarding at most half the copies:

* `goodCopies holes` — the copies whose hole fraction is at most `1/8`;
* `card_le_two_mul_card_goodCopies` — `#ι ≤ 2 * #good`, the factor `2` being the only loss.

This is exactly `[duan2023faster]`'s "second retention pass" (`global_value.tex:250-284`,
`claim:hole_frac_low`), with the modulus doubled from `8 · max(…)` to `16 · max(…)` so that
the
statement is about the total hole mass at one seed rather than about every retained triple at
once.  Nothing here mentions a hashing seed, a partition, a tensor, or the paper's alphabets: the
whole retention pass is finite counting, so it is stated once here and instantiated by every
client that has a hole family.

The budget consequences of `goodCopies` — `AsymmetricGlobal.holeBudget_of_goodSubset` and the
batching `goodBatch` — live one layer up in
`MatrixMultiplication/AggregateHoleBudget.lean`, because they rest on
`AsymmetricGlobal.holeBudget_of_etaSum` and `uniformBatch`, which are layer-3 declarations.

Primary source: Ran Duan, Hongxun Wu and Renfei Zhou, *Faster Matrix Multiplication via Asymmetric
Hashing*, arXiv:2210.10173, §6.2 (`global_value.tex`) (`[duan2023faster]`).
-/

namespace AlgebraicComplexity

open scoped BigOperators

universe u v

section Markov

variable {A : Type u} [Fintype A] {ι : Type v} [Fintype ι]

/-- **The average hole fraction is at most `1/16`.**

The aggregate form of `[duan2023faster]`'s `claim:hole_frac_low`, in exact integer form: the total
hole mass of the family is at most a sixteenth of the trivial bound `#ι · |A|`.  A random-seed
argument produces this and not the per-copy bound, because the paper's `fracnonhole ≥ 7/8` enters
only through a sum and an expectation. -/
def AggregateHoleFraction (holes : ι → Finset A) : Prop :=
  16 * ∑ t, (holes t).card ≤ Fintype.card ι * Fintype.card A

/-- **The copies that survive the second retention pass**: those whose hole fraction is at most
`1/8`, which is the per-copy hypothesis every hole-repair budget asks for. -/
def goodCopies (holes : ι → Finset A) : Finset ι :=
  Finset.univ.filter fun t ↦ 8 * (holes t).card ≤ Fintype.card A

@[simp] theorem mem_goodCopies {holes : ι → Finset A} {t : ι} :
    t ∈ goodCopies holes ↔ 8 * (holes t).card ≤ Fintype.card A := by
  simp [goodCopies]

/-- **Markov: at least half the copies survive.**

If the *average* hole fraction over the whole family is at most `1/16`, then at least half of the
copies have hole fraction at most `1/8`.  This is the entire content of `[duan2023faster]`'s
second retention pass; the factor `2` is the only loss.

Proof: a copy outside `goodCopies` has `|A| ≤ 8 |holes t|`, so summing over the bad copies gives
`#bad · |A| ≤ 8 ∑_{bad} |holes|`, and the aggregate bound turns `16 ∑` into `#ι · |A|`;
cancelling
the positive factor `|A|` leaves `2 · #bad ≤ #ι`. -/
theorem card_le_two_mul_card_goodCopies (holes : ι → Finset A)
    (hpos : 0 < Fintype.card A)
    (haggregate : 16 * ∑ t, (holes t).card ≤ Fintype.card ι * Fintype.card A) :
    Fintype.card ι ≤ 2 * (goodCopies holes).card := by
  classical
  set bad : Finset ι := Finset.univ \ goodCopies holes with hbaddef
  have hmembad : ∀ t ∈ bad, Fintype.card A ≤ 8 * (holes t).card := by
    intro t ht
    rw [hbaddef, Finset.mem_sdiff] at ht
    have hnot : ¬ (8 * (holes t).card ≤ Fintype.card A) := fun h ↦
      ht.2 (mem_goodCopies.mpr h)
    omega
  have hgle : (goodCopies holes).card ≤ Fintype.card ι :=
    Finset.card_le_univ _
  have hsplit : bad.card = Fintype.card ι - (goodCopies holes).card := by
    rw [hbaddef, Finset.card_sdiff, Finset.inter_univ, Finset.card_univ]
  have hstep : bad.card * Fintype.card A ≤ 8 * ∑ t ∈ bad, (holes t).card := by
    calc bad.card * Fintype.card A = ∑ _t ∈ bad, Fintype.card A :=
          (Finset.sum_const_nat fun _ _ ↦ rfl).symm
      _ ≤ ∑ t ∈ bad, 8 * (holes t).card := Finset.sum_le_sum hmembad
      _ = 8 * ∑ t ∈ bad, (holes t).card := by rw [Finset.mul_sum]
  have hsub : ∑ t ∈ bad, (holes t).card ≤ ∑ t, (holes t).card :=
    Finset.sum_le_sum_of_subset (Finset.subset_univ bad)
  have hkey : 2 * bad.card * Fintype.card A ≤ Fintype.card ι * Fintype.card A := by
    calc 2 * bad.card * Fintype.card A = 2 * (bad.card * Fintype.card A) := by ring
      _ ≤ 2 * (8 * ∑ t ∈ bad, (holes t).card) := by omega
      _ = 16 * ∑ t ∈ bad, (holes t).card := by ring
      _ ≤ 16 * ∑ t, (holes t).card := by omega
      _ ≤ Fintype.card ι * Fintype.card A := haggregate
  have h2b : 2 * bad.card ≤ Fintype.card ι := Nat.le_of_mul_le_mul_right hkey hpos
  omega

end Markov

section Coe

variable {A : Type u} [Fintype A] {τ : Type v}

/-- **Markov for a family indexed by a `Finset` of retained objects.**

The same statement as `card_le_two_mul_card_goodCopies`, with `Fintype.card ↥retained` already
rewritten to `retained.card`; this is the shape in which a retained family is carried by a stage
binder, and it absorbs the `Fintype.card_coe` step that clients would otherwise repeat. -/
theorem card_le_two_mul_card_goodCopies_of_aggregateHoleFraction (retained : Finset τ)
    (holes : retained → Finset A) (hpos : 0 < Fintype.card A)
    (haggregate : AggregateHoleFraction holes) :
    retained.card ≤ 2 * (goodCopies holes).card := by
  have h := card_le_two_mul_card_goodCopies holes hpos haggregate
  rwa [Fintype.card_coe] at h

end Coe

end AlgebraicComplexity
