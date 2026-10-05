/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Image

set_option autoImplicit false

/-!
# Counting deduplicated coarse competitor pairs against a sum of fibres

Layer 2 (`AlgebraicComplexity/Combinatorics/`).  A compatibility cleanup charges each discarded
address to a *competitor*: another ambient address, compatible with it on a pivot leg, lying in a
different coarse group.  Charging every fine incidence is wasteful, so the charge is first
**deduplicated to the pair of coarse groups it induces**, giving a `Finset (Γ × Γ)`.  The
question
this module answers is how large that deduplicated set can be.

The wrong answer is a direct injection from coarse pairs into a single fibre: several coarse pairs
share a left group, so no such injection exists.  The right answer is one level up — bound the
pair count by a **sum of fibre cardinalities over the retained left groups**:

`#(retained coarse pairs) ≤ ∑_{t ∈ retained} #(fib t)`.

`card_le_sum_fiber_of_encoding` is that statement, and it is pure finite counting over an
arbitrary carrier: a left-component map `lft`, and an encoding `enc` that lands in `fib` of a
member's left component and is injective *on each left fibre*.
Double counting (`Finset.card_eq_sum_card_fiberwise` along the left component, then
`Finset.card_le_card_of_injOn` inside each fibre) is the whole proof.  Nothing here mentions a
tensor, a leg, a hash or a paper.

## The shape of the pair set

`groupCoarsePairs` and `retainedGroupCoarsePairs` restate the coarse-pair construction with the
address type left abstract.  A client whose addresses are block addresses and whose compatibility
is read off a pivot leg instantiates at `α := BlockAddress A` and
`rel a b := compatible (a pivot) b`; the pivot never enters the counting argument, which is why it
does not appear here.

## Why one theorem and not two

The two directional clients — a `Z`-side bound summing compatible-target fibres and a `Y`-side
bound summing ordinary leg fibres — differ only in which fibre map and which membership rewrite
they supply.  Stating the bound once, parametrised by `fib` and `enc`, makes each of them a short
corollary instead of a duplicated proof.

`card_le_card_fiber_of_encoding` records the degenerate case in which the retained family is a
single group: the sum collapses and the statement becomes an ordinary injection of one `Finset`
into one fibre.
-/

namespace AlgebraicComplexity

open scoped BigOperators

universe u v w

/-! ## The deduplicated coarse-pair sets -/

section Pairs

variable {α : Type u} {Γ : Type v} [DecidableEq Γ]

/-- **Ordered coarse-group pairs induced by cross-group compatible ambient pairs.**

`rel a b` says that `b` is a compatibility competitor of `a`; the pair is kept only when the two
addresses lie in different coarse groups, and only the pair of groups is remembered. -/
noncomputable def groupCoarsePairs (ambient : Finset α) (group : α → Γ)
    (rel : α → α → Prop) : Finset (Γ × Γ) := by
  classical
  exact ((ambient ×ˢ ambient).filter fun p ↦ rel p.1 p.2 ∧ group p.2 ≠ group p.1).image
    fun p ↦ (group p.1, group p.2)

theorem mem_groupCoarsePairs (ambient : Finset α) (group : α → Γ) (rel : α → α → Prop)
    (q : Γ × Γ) :
    q ∈ groupCoarsePairs ambient group rel ↔
      ∃ a ∈ ambient, ∃ b ∈ ambient,
        rel a b ∧ group b ≠ group a ∧ (group a, group b) = q := by
  classical
  simp only [groupCoarsePairs, Finset.mem_image, Finset.mem_filter, Finset.mem_product]
  constructor
  · rintro ⟨p, ⟨⟨ha, hb⟩, hrel, hne⟩, hpq⟩
    exact ⟨p.1, ha, p.2, hb, hrel, hne, hpq⟩
  · rintro ⟨a, ha, b, hb, hrel, hne, hq⟩
    exact ⟨(a, b), ⟨⟨ha, hb⟩, hrel, hne⟩, hq⟩

/-- **Coarse pairs whose left group belongs to a prescribed retained family.** -/
noncomputable def retainedGroupCoarsePairs (ambient : Finset α) (retained : Finset Γ)
    (group : α → Γ) (rel : α → α → Prop) : Finset (Γ × Γ) := by
  classical
  exact (groupCoarsePairs ambient group rel).filter fun pair ↦ pair.1 ∈ retained

@[simp] theorem mem_retainedGroupCoarsePairs (ambient : Finset α) (retained : Finset Γ)
    (group : α → Γ) (rel : α → α → Prop) (q : Γ × Γ) :
    q ∈ retainedGroupCoarsePairs ambient retained group rel ↔
      q ∈ groupCoarsePairs ambient group rel ∧ q.1 ∈ retained := by
  classical
  simp only [retainedGroupCoarsePairs, Finset.mem_filter]

end Pairs

/-! ## The counting core -/

section Counting

variable {ρ : Type u} {Γ : Type v} [DecidableEq Γ] {Δ : Type w}

/-- **A finite set is bounded by a sum of fibres over a left-component map.**

`lft` reads a "left group" off each member, `enc` encodes each member by a element of `fib` of its
left group, and `enc` is injective *among members with the same left group*.  Double counting
along `lft` then bounds the whole set by the sum of the fibre cardinalities over `kept`.

The fibrewise injectivity hypothesis is exactly what a *deduplicated* count can supply and a fine
incidence count cannot: two members with the same left group are separated by `enc`, whereas two
fine addresses inducing the same coarse pair are not required to be. -/
theorem card_le_sum_fiber_of_encoding
    (S : Finset ρ) (kept : Finset Γ) (lft : ρ → Γ) (fib : Γ → Finset Δ) (enc : ρ → Δ)
    (hleft : ∀ p ∈ S, lft p ∈ kept)
    (hmem : ∀ p ∈ S, enc p ∈ fib (lft p))
    (hinj : ∀ p ∈ S, ∀ q ∈ S, lft p = lft q → enc p = enc q → p = q) :
    S.card ≤ ∑ t ∈ kept, (fib t).card := by
  classical
  rw [Finset.card_eq_sum_card_fiberwise (f := lft) (t := kept) hleft]
  refine Finset.sum_le_sum fun t _ ↦ ?_
  refine Finset.card_le_card_of_injOn enc ?_ ?_
  · intro p hp
    obtain ⟨hpS, hpt⟩ := Finset.mem_filter.mp hp
    have hfib := hmem p hpS
    rwa [hpt] at hfib
  · intro p hp q hq hpq
    obtain ⟨hpS, hpt⟩ := Finset.mem_filter.mp hp
    obtain ⟨hqS, hqt⟩ := Finset.mem_filter.mp hq
    exact hinj p hpS q hqS (hpt.trans hqt.symm) hpq

/-- **The one-cell degenerate case.**  When every member has the same left group the sum collapses
and the bound is an ordinary injection of one `Finset` into one fibre. -/
theorem card_le_card_fiber_of_encoding
    (S : Finset ρ) (t : Γ) (lft : ρ → Γ) (fib : Γ → Finset Δ) (enc : ρ → Δ)
    (hleft : ∀ p ∈ S, lft p = t)
    (hmem : ∀ p ∈ S, enc p ∈ fib (lft p))
    (hinj : ∀ p ∈ S, ∀ q ∈ S, lft p = lft q → enc p = enc q → p = q) :
    S.card ≤ (fib t).card := by
  classical
  have h := card_le_sum_fiber_of_encoding S {t} lft fib enc
    (fun p hp ↦ Finset.mem_singleton.mpr (hleft p hp)) hmem hinj
  rwa [Finset.sum_singleton] at h

end Counting

/-! ## The coarse-pair bound -/

section Bound

variable {α : Type u} {Γ : Type v} [DecidableEq Γ] {Δ : Type w}

/-- **The deduplicated coarse-pair count is bounded by a sum of directional fibres.**

Stated once, parametrised by the fibre map `fib` and the encoding `enc`.  Both directional clients
of the recursive cleanup charge — the `Z`-side sum over compatible-target fibres and the `Y`-side
sum over leg fibres — are this theorem with their own `fib` and their own membership rewrite; the
`hleft` hypothesis is discharged by the construction, because `retainedGroupCoarsePairs` filters on
exactly that condition. -/
theorem card_retainedGroupCoarsePairs_le_sum_fiber
    (ambient : Finset α) (retained : Finset Γ) (group : α → Γ) (rel : α → α → Prop)
    (fib : Γ → Finset Δ) (enc : Γ × Γ → Δ)
    (hmem : ∀ p ∈ retainedGroupCoarsePairs ambient retained group rel, enc p ∈ fib p.1)
    (hinj : ∀ p ∈ retainedGroupCoarsePairs ambient retained group rel,
      ∀ q ∈ retainedGroupCoarsePairs ambient retained group rel,
        p.1 = q.1 → enc p = enc q → p = q) :
    (retainedGroupCoarsePairs ambient retained group rel).card ≤
      ∑ t ∈ retained, (fib t).card := by
  classical
  refine card_le_sum_fiber_of_encoding _ retained Prod.fst fib enc ?_ hmem hinj
  intro p hp
  exact ((mem_retainedGroupCoarsePairs ambient retained group rel p).mp hp).2

end Bound

end AlgebraicComplexity
