/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod

/-!
# Charged averaging and sparse budgets over finite families

Finite selection principles for arguments that must choose a cell of a family **against** the
damage it carries, rather than maximizing a reward first and paying for the damage afterwards.
Nothing here mentions hashing, tensors, entropy, or matrix multiplication: the whole file is
natural-number counting, division-free and rounding-free, so a client clears its denominators
once and then argues with exact integers.

## Selecting one cell

`exists_mem_floor_add_charge_le_reward` is the charged averaging principle: from the single
global inequality

`cells.card * floor + ∑ charge ≤ ∑ reward`

some cell satisfies `floor + charge i ≤ reward i` locally.  Choosing the cell of largest reward
and paying its charge afterwards is *not* a substitute — all the damage may sit on that cell —
which is why the reward and the charge must enter the same average.
`exists_seed_type_floor_add_charge_le_reward` is the product-index form used when a shared seed
and an empirical type must be chosen together, and
`exists_mem_floor_add_weightedCharge_le_reward` allows finitely many separately weighted damage
coordinates.  `finiteWeightedCharge` packages such a weighted damage over a whole finite
coordinate type, which is the form
`exists_seed_type_floor_add_weightedCharge_le_reward` takes at the product index.

## Selecting a sub-family

One good cell is not enough when the same estimate must hold at every node of a finite family.
The second group of results turns an *aggregate* budget into *per-item* guarantees on almost all
items: `card_filter_lt_le_sum_sub` bounds the number of cells that break their own budget by the
total excess, `mul_card_filter_le_sum_sub` is its margin-`m` sharpening, and
`mul_card_filter_le_of_sum_le` is the division-free Markov step
`allowance * |{i : allowance ≤ charge i}| ≤ budget`.  The two selection statements
`exists_subset_forall_cost_le_reward` and `exists_subset_forall_charge_lt` package these as an
explicit sub-family of prescribed size on which the per-item bound holds.

The bridge `sum_sub_le_sum_charge` is what makes the sub-family statements usable from an
aggregate damage bound: when each cell's floor is already covered by its own reward, the total
excess is at most the total charge.

## Source

`better_bound/paper.tex`: `lem:charged-seed-type-averaging` (the one-cell principle, stated there
for `ℤ≥0` rewards and damages) and its use with `lem:aggregate-isolated-reward` and
`lem:aggregate-shared-leg-collision`, where the aggregate reward and the aggregate collision
damage are summed over the complete affine-seed space before any seed is fixed.  The sub-family
results are the uniformity layer needed by the aggregate sparse-hole budget, which must hold at
every node of a finite recursion tree at once.

The `example`s at the end are the deliberately tiny client: a two-cell family in which the
largest-reward cell fails its local inequality while the averaging principle still selects a good
cell, and a five-cell family in which an aggregate budget leaves at least three good cells.
-/

namespace AlgebraicComplexity.ChargedAveraging

open scoped BigOperators

universe u v w

variable {ι : Type u}

/-! ## Selecting one cell -/

/-- Exact averaging over a nonempty finite family: if the total cost does not exceed the total
reward then some cell pays for itself.  Costs and rewards are unrelated functions; no partition,
monotonicity, or positivity is assumed. -/
theorem exists_mem_cost_le_reward {cells : Finset ι} (hcells : cells.Nonempty)
    {cost reward : ι → ℕ}
    (hglobal : ∑ i ∈ cells, cost i ≤ ∑ i ∈ cells, reward i) :
    ∃ i ∈ cells, cost i ≤ reward i :=
  Finset.exists_le_of_sum_le hcells hglobal

/-- **Charged averaging.**  A uniform floor and a per-cell charge are carried through one global
inequality, and some cell meets the floor *after* paying its own charge.

The nonemptiness premise cannot be dropped: over the empty family the global inequality holds
vacuously and there is no cell to return. -/
theorem exists_mem_floor_add_charge_le_reward {cells : Finset ι} (hcells : cells.Nonempty)
    (floor : ℕ) (charge reward : ι → ℕ)
    (hglobal : cells.card * floor + ∑ i ∈ cells, charge i ≤ ∑ i ∈ cells, reward i) :
    ∃ i ∈ cells, floor + charge i ≤ reward i := by
  refine exists_mem_cost_le_reward (cost := fun i ↦ floor + charge i) hcells ?_
  calc ∑ i ∈ cells, (floor + charge i)
      = ∑ _i ∈ cells, floor + ∑ i ∈ cells, charge i := Finset.sum_add_distrib
    _ = cells.card * floor + ∑ i ∈ cells, charge i := by
        rw [Finset.sum_const_nat (m := floor) (f := fun _ ↦ floor) fun _ _ ↦ rfl]
    _ ≤ ∑ i ∈ cells, reward i := hglobal

/-- Charged averaging with finitely many separately weighted damage coordinates.  The weights are
arbitrary natural numbers, so a client may clear denominators into them. -/
theorem exists_mem_floor_add_weightedCharge_le_reward {κ : Type v}
    {cells : Finset ι} (hcells : cells.Nonempty) (coords : Finset κ)
    (floor : ℕ) (weight : κ → ℕ) (damage : ι → κ → ℕ) (reward : ι → ℕ)
    (hglobal : cells.card * floor + ∑ i ∈ cells, ∑ k ∈ coords, weight k * damage i k ≤
      ∑ i ∈ cells, reward i) :
    ∃ i ∈ cells, floor + ∑ k ∈ coords, weight k * damage i k ≤ reward i :=
  exists_mem_floor_add_charge_le_reward hcells floor
    (fun i ↦ ∑ k ∈ coords, weight k * damage i k) reward hglobal

/-- A leg- or feature-weighted charge, summed over a whole finite coordinate type.  Keeping this
definition separate lets certificate clients clear all denominators into `weight` before invoking
the natural-number averaging theorems. -/
def finiteWeightedCharge {κ : Type v} [Fintype κ] (weight damage : κ → ℕ) : ℕ :=
  ∑ k, weight k * damage k

/-- Product-index charged averaging: a seed and a type tag are selected **together** against the
damage.  Neither factor is chosen first, which is the point of the lemma — a seed maximizing the
reward may carry all of the damage in its largest type class. -/
theorem exists_seed_type_floor_add_charge_le_reward {Seed : Type u} {TypeTag : Type v}
    {seeds : Finset Seed} {tags : Finset TypeTag}
    (hseeds : seeds.Nonempty) (htags : tags.Nonempty)
    (floor : ℕ) (charge reward : Seed → TypeTag → ℕ)
    (hglobal : seeds.card * tags.card * floor +
        ∑ seed ∈ seeds, ∑ tag ∈ tags, charge seed tag ≤
      ∑ seed ∈ seeds, ∑ tag ∈ tags, reward seed tag) :
    ∃ seed ∈ seeds, ∃ tag ∈ tags, floor + charge seed tag ≤ reward seed tag := by
  obtain ⟨cell, hcell, hlocal⟩ :=
    exists_mem_floor_add_charge_le_reward (cells := seeds ×ˢ tags) (hseeds.product htags) floor
      (fun cell ↦ charge cell.1 cell.2) (fun cell ↦ reward cell.1 cell.2) (by
        simpa only [Finset.card_product, Finset.sum_product] using hglobal)
  exact ⟨cell.1, (Finset.mem_product.mp hcell).1, cell.2, (Finset.mem_product.mp hcell).2, hlocal⟩

/-- Seed/type selection with finitely many separately weighted damage coordinates: the
product-index form of `exists_mem_floor_add_weightedCharge_le_reward`, stated with
`finiteWeightedCharge` so that a client carrying one weight vector per leg does not have to name
its coordinate `Finset`. -/
theorem exists_seed_type_floor_add_weightedCharge_le_reward {Seed : Type u} {TypeTag : Type v}
    {κ : Type w} [Fintype κ] {seeds : Finset Seed} {tags : Finset TypeTag}
    (hseeds : seeds.Nonempty) (htags : tags.Nonempty)
    (floor : ℕ) (weight : κ → ℕ) (damage : Seed → TypeTag → κ → ℕ)
    (reward : Seed → TypeTag → ℕ)
    (hglobal : seeds.card * tags.card * floor +
        ∑ seed ∈ seeds, ∑ tag ∈ tags, finiteWeightedCharge weight (damage seed tag) ≤
      ∑ seed ∈ seeds, ∑ tag ∈ tags, reward seed tag) :
    ∃ seed ∈ seeds, ∃ tag ∈ tags,
      floor + finiteWeightedCharge weight (damage seed tag) ≤ reward seed tag :=
  exists_seed_type_floor_add_charge_le_reward hseeds htags floor
    (fun seed tag ↦ finiteWeightedCharge weight (damage seed tag)) reward hglobal

/-! ## Selecting a sub-family -/

/-- Margin form of the sparse-budget count: cells whose cost exceeds their reward by at least
`margin` each consume `margin` of the total excess, so there are at most `total excess / margin`
of them.  Stated as a product to stay division-free. -/
theorem mul_card_filter_le_sum_sub (cells : Finset ι) (cost reward : ι → ℕ) (margin : ℕ) :
    margin * (cells.filter fun i ↦ reward i + margin ≤ cost i).card ≤
      ∑ i ∈ cells, (cost i - reward i) := by
  calc margin * (cells.filter fun i ↦ reward i + margin ≤ cost i).card
      = ∑ _i ∈ cells.filter fun i ↦ reward i + margin ≤ cost i, margin := by
        rw [Finset.sum_const_nat (m := margin) (f := fun _ ↦ margin) fun _ _ ↦ rfl]
        exact Nat.mul_comm _ _
    _ ≤ ∑ i ∈ cells.filter fun i ↦ reward i + margin ≤ cost i, (cost i - reward i) := by
        refine Finset.sum_le_sum fun i hi ↦ ?_
        have := (Finset.mem_filter.mp hi).2
        omega
    _ ≤ ∑ i ∈ cells, (cost i - reward i) :=
        Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)

/-- The number of cells that break their own budget is at most the total excess.  This is the
`margin = 1` case of `mul_card_filter_le_sum_sub`, and it is the form the sub-family selection
uses: integrality alone turns an aggregate bound into a bound on the number of bad cells. -/
theorem card_filter_lt_le_sum_sub (cells : Finset ι) (cost reward : ι → ℕ) :
    (cells.filter fun i ↦ reward i < cost i).card ≤ ∑ i ∈ cells, (cost i - reward i) := by
  calc (cells.filter fun i ↦ reward i < cost i).card
      = ∑ _i ∈ cells.filter fun i ↦ reward i < cost i, 1 := Finset.card_eq_sum_ones _
    _ ≤ ∑ i ∈ cells.filter fun i ↦ reward i < cost i, (cost i - reward i) := by
        refine Finset.sum_le_sum fun i hi ↦ ?_
        have := (Finset.mem_filter.mp hi).2
        omega
    _ ≤ ∑ i ∈ cells, (cost i - reward i) :=
        Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)

/-- Division-free Markov step: an aggregate charge budget bounds how many cells can be charged at
least `allowance` each. -/
theorem mul_card_filter_le_of_sum_le (cells : Finset ι) (charge : ι → ℕ)
    (allowance budget : ℕ) (hsum : ∑ i ∈ cells, charge i ≤ budget) :
    allowance * (cells.filter fun i ↦ allowance ≤ charge i).card ≤ budget := by
  calc allowance * (cells.filter fun i ↦ allowance ≤ charge i).card
      = ∑ _i ∈ cells.filter fun i ↦ allowance ≤ charge i, allowance := by
        rw [Finset.sum_const_nat (m := allowance) (f := fun _ ↦ allowance) fun _ _ ↦ rfl]
        exact Nat.mul_comm _ _
    _ ≤ ∑ i ∈ cells.filter fun i ↦ allowance ≤ charge i, charge i :=
        Finset.sum_le_sum fun i hi ↦ (Finset.mem_filter.mp hi).2
    _ ≤ ∑ i ∈ cells, charge i := Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
    _ ≤ budget := hsum

/-- When every cell's floor is already covered by its own reward, the total excess of
`floor + charge` over `reward` is at most the total charge.  This is the bridge from an aggregate
*damage* bound, which is what a counting argument produces, to the excess hypothesis of the
sub-family statements. -/
theorem sum_sub_le_sum_charge (cells : Finset ι) (floor charge reward : ι → ℕ)
    (hfloor : ∀ i ∈ cells, floor i ≤ reward i) :
    ∑ i ∈ cells, (floor i + charge i - reward i) ≤ ∑ i ∈ cells, charge i :=
  Finset.sum_le_sum fun i hi ↦ by have := hfloor i hi; omega

/-- **Sub-family selection.**  An aggregate excess budget leaves an explicit sub-family of
prescribed size on which the per-cell inequality `cost i ≤ reward i` holds everywhere.

The returned family is `cells.filter fun i ↦ cost i ≤ reward i`, so it is canonical: it is the
whole good part, not an arbitrary subset of it. -/
theorem exists_subset_forall_cost_le_reward (cells : Finset ι) (cost reward : ι → ℕ)
    (budget count : ℕ)
    (hexcess : ∑ i ∈ cells, (cost i - reward i) ≤ budget)
    (hcount : count + budget ≤ cells.card) :
    ∃ good ⊆ cells, count ≤ good.card ∧ ∀ i ∈ good, cost i ≤ reward i := by
  refine ⟨cells.filter fun i ↦ cost i ≤ reward i, Finset.filter_subset _ _, ?_,
    fun i hi ↦ (Finset.mem_filter.mp hi).2⟩
  have hsplit : (cells.filter fun i ↦ cost i ≤ reward i).card +
      (cells.filter fun i ↦ ¬ cost i ≤ reward i).card = cells.card :=
    Finset.card_filter_add_card_filter_not _
  have hneg : (cells.filter fun i ↦ ¬ cost i ≤ reward i) =
      cells.filter fun i ↦ reward i < cost i :=
    Finset.filter_congr fun i _ ↦ by simp only [Nat.not_le]
  have hbad : (cells.filter fun i ↦ ¬ cost i ≤ reward i).card ≤ budget := by
    rw [hneg]
    exact le_trans (card_filter_lt_le_sum_sub cells cost reward) hexcess
  omega

/-- **Sub-family selection from an aggregate charge budget.**  At least `count` cells stay
strictly below the per-cell `allowance`, provided the budget is small enough against the family
size — again as an exact product inequality, with no division. -/
theorem exists_subset_forall_charge_lt (cells : Finset ι) (charge : ι → ℕ)
    (allowance budget count : ℕ) (hallowance : 0 < allowance)
    (hsum : ∑ i ∈ cells, charge i ≤ budget)
    (hcount : allowance * count + budget ≤ allowance * cells.card) :
    ∃ good ⊆ cells, count ≤ good.card ∧ ∀ i ∈ good, charge i < allowance := by
  refine ⟨cells.filter fun i ↦ charge i < allowance, Finset.filter_subset _ _, ?_,
    fun i hi ↦ (Finset.mem_filter.mp hi).2⟩
  have hsplit : (cells.filter fun i ↦ charge i < allowance).card +
      (cells.filter fun i ↦ ¬ charge i < allowance).card = cells.card :=
    Finset.card_filter_add_card_filter_not _
  have hneg : (cells.filter fun i ↦ ¬ charge i < allowance) =
      cells.filter fun i ↦ allowance ≤ charge i :=
    Finset.filter_congr fun i _ ↦ by simp only [Nat.not_lt]
  have hbad : allowance * (cells.filter fun i ↦ ¬ charge i < allowance).card ≤ budget := by
    rw [hneg]
    exact mul_card_filter_le_of_sum_le cells charge allowance budget hsum
  have hkey : allowance * count +
        allowance * (cells.filter fun i ↦ ¬ charge i < allowance).card ≤
      allowance * (cells.filter fun i ↦ charge i < allowance).card +
        allowance * (cells.filter fun i ↦ ¬ charge i < allowance).card := by
    calc allowance * count +
          allowance * (cells.filter fun i ↦ ¬ charge i < allowance).card
        ≤ allowance * count + budget := Nat.add_le_add_left hbad _
      _ ≤ allowance * cells.card := hcount
      _ = allowance * (cells.filter fun i ↦ charge i < allowance).card +
            allowance * (cells.filter fun i ↦ ¬ charge i < allowance).card := by
          rw [← Nat.mul_add, hsplit]
  exact Nat.le_of_mul_le_mul_left (Nat.le_of_add_le_add_right hkey) hallowance

/-! ## Tiny clients

The first example is the failure mode the charged principle exists to avoid: cell `0` carries the
largest reward, yet `floor + charge 0 = 13 > 10 = reward 0`.  Averaging reward and charge together
still produces a cell meeting the local inequality, and it is cell `1`. -/

private def tinyReward : Fin 2 → ℕ
  | 0 => 10
  | 1 => 8

private def tinyCharge : Fin 2 → ℕ
  | 0 => 10
  | 1 => 0

example : ¬ 3 + tinyCharge 0 ≤ tinyReward 0 := by decide

example : ∃ i ∈ (Finset.univ : Finset (Fin 2)), 3 + tinyCharge i ≤ tinyReward i := by
  refine exists_mem_floor_add_charge_le_reward Finset.univ_nonempty 3 tinyCharge tinyReward ?_
  decide

/-- Aggregate budget over a five-cell family: total charge at most `4` with allowance `2` leaves
at least `3` cells whose charge is below the allowance. -/
example (charge : Fin 5 → ℕ) (hsum : ∑ i, charge i ≤ 4) :
    ∃ good ⊆ (Finset.univ : Finset (Fin 5)), 3 ≤ good.card ∧ ∀ i ∈ good, charge i < 2 :=
  exists_subset_forall_charge_lt Finset.univ charge 2 4 3 (by omega) hsum (by simp)

end AlgebraicComplexity.ChargedAveraging
