/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Combinatorics.ChargedAveraging

/-!
# Division-free charged averaging over finite families (compatibility layer)

This module used to carry its own proofs of the charged averaging principles, duplicating
`AlgebraicComplexity.Combinatorics.ChargedAveraging`.  The mathematics now lives once, in that
file — including `finiteWeightedCharge` and the seed/type weighted form, which only this module
used to provide.  What remains here is a re-export: each declaration keeps its `AlgebraicComplexity`
name and its original argument order, so existing clients and audit companions are unaffected.

The principal result, `exists_mem_floor_add_charge_le_reward`, says that if

`|S| * floor + sum charge <= sum reward`,

then some member `s` satisfies `floor + charge s <= reward s`.  The statement is over natural
numbers and contains no division or rounding.  `exists_seed_type_floor_add_charge_le_reward` is
the product-index specialization used for a shared affine seed and a recursive type cell.  See the
module docstring of `ChargedAveraging` for why the charge must enter the same average as the
reward, and for the paper reference.

New clients should use `AlgebraicComplexity.ChargedAveraging` directly.
-/

namespace AlgebraicComplexity

open scoped BigOperators

universe u v w

/-- A finite charged averaging lemma in exact division-free form.

The nonemptiness premise is necessary: for the empty family the displayed global inequality is
true, but there is no cell to select.

Re-export of `ChargedAveraging.exists_mem_floor_add_charge_le_reward`. -/
theorem exists_mem_floor_add_charge_le_reward
    {ι : Type u} [DecidableEq ι]
    (cells : Finset ι) (hcells : cells.Nonempty)
    (reward charge : ι → ℕ) (floor : ℕ)
    (hglobal : cells.card * floor + ∑ i ∈ cells, charge i ≤
      ∑ i ∈ cells, reward i) :
    ∃ i ∈ cells, floor + charge i ≤ reward i :=
  ChargedAveraging.exists_mem_floor_add_charge_le_reward hcells floor charge reward hglobal

/-- A leg- or feature-weighted charge.  Keeping this definition separate lets certificate clients
clear all denominators before invoking the natural-number averaging theorem.

Re-export of `ChargedAveraging.finiteWeightedCharge`. -/
abbrev finiteWeightedCharge
    {κ : Type v} [Fintype κ]
    (weight damage : κ → ℕ) : ℕ :=
  ChargedAveraging.finiteWeightedCharge weight damage

/-- Charged averaging with a finite family of separately weighted damage coordinates.

Re-export of `ChargedAveraging.exists_mem_floor_add_weightedCharge_le_reward` at the full
coordinate type. -/
theorem exists_mem_floor_add_weightedCharge_le_reward
    {ι : Type u} {κ : Type v} [DecidableEq ι] [Fintype κ]
    (cells : Finset ι) (hcells : cells.Nonempty)
    (reward : ι → ℕ) (weight : κ → ℕ) (damage : ι → κ → ℕ) (floor : ℕ)
    (hglobal : cells.card * floor +
        ∑ i ∈ cells, finiteWeightedCharge weight (damage i) ≤
      ∑ i ∈ cells, reward i) :
    ∃ i ∈ cells,
      floor + finiteWeightedCharge weight (damage i) ≤ reward i :=
  ChargedAveraging.exists_mem_floor_add_weightedCharge_le_reward hcells Finset.univ floor weight
    damage reward hglobal

/-- Product-index form for selecting a shared seed and a type cell in one step.

The theorem deliberately makes no claim that `reward` or `charge` comes from a partition.  That
keeps the acceptance criterion visible: a client must prove the displayed global inequality for
the actual seed/type cells it uses.

Re-export of `ChargedAveraging.exists_seed_type_floor_add_charge_le_reward`. -/
theorem exists_seed_type_floor_add_charge_le_reward
    {Seed : Type u} {TypeTag : Type v}
    [DecidableEq Seed] [DecidableEq TypeTag]
    (seeds : Finset Seed) (types : Finset TypeTag)
    (hseeds : seeds.Nonempty) (htypes : types.Nonempty)
    (reward charge : Seed → TypeTag → ℕ) (floor : ℕ)
    (hglobal : seeds.card * types.card * floor +
        ∑ seed ∈ seeds, ∑ type ∈ types, charge seed type ≤
      ∑ seed ∈ seeds, ∑ type ∈ types, reward seed type) :
    ∃ seed ∈ seeds, ∃ type ∈ types,
      floor + charge seed type ≤ reward seed type :=
  ChargedAveraging.exists_seed_type_floor_add_charge_le_reward hseeds htypes floor charge reward
    hglobal

/-- Seed/type selection with finitely many separately weighted damage coordinates.

Re-export of `ChargedAveraging.exists_seed_type_floor_add_weightedCharge_le_reward`. -/
theorem exists_seed_type_floor_add_weightedCharge_le_reward
    {Seed : Type u} {TypeTag : Type v} {κ : Type w}
    [DecidableEq Seed] [DecidableEq TypeTag] [Fintype κ]
    (seeds : Finset Seed) (types : Finset TypeTag)
    (hseeds : seeds.Nonempty) (htypes : types.Nonempty)
    (reward : Seed → TypeTag → ℕ)
    (weight : κ → ℕ) (damage : Seed → TypeTag → κ → ℕ) (floor : ℕ)
    (hglobal : seeds.card * types.card * floor +
        ∑ seed ∈ seeds, ∑ type ∈ types,
          finiteWeightedCharge weight (damage seed type) ≤
      ∑ seed ∈ seeds, ∑ type ∈ types, reward seed type) :
    ∃ seed ∈ seeds, ∃ type ∈ types,
      floor + finiteWeightedCharge weight (damage seed type) ≤
        reward seed type :=
  ChargedAveraging.exists_seed_type_floor_add_weightedCharge_le_reward hseeds htypes floor weight
    damage reward hglobal

end AlgebraicComplexity
