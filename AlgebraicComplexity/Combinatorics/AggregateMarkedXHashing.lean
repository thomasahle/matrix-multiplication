/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Combinatorics.AggregateMarkedHashing
import AlgebraicComplexity.Combinatorics.MarkedXHashingExtraction

set_option autoImplicit false

/-!
# Aggregate marked X-only hashing

This module lifts the marked X-only affine-hashing theorem to a heterogeneous Cartesian family.
The aggregate X-fiber is the Cartesian product of the factor X-fibers, so one shared hash pays the
product of the factorwise X bounds.  The conclusion isolates only X.  In particular, it makes no
Y- or Z-uniqueness claim: those collisions remain available for the later fine compatibility
zero-outs and hole repair in Claim 6.18 of [alman2025more].

The result is entirely finite and tensor-independent.  It is the one-leg counterpart of
`AggregateMarkedHashing`, whose three-leg conclusion is intentionally stronger and has a larger
field budget.

This local theorem does not by itself choose the endpoint field.  Claim 6.18 takes a modulus large
enough for the maximum of this X-collision term and the later Y/Z compatibility-hole terms.  Such a
larger external choice is fully compatible with the X-only premise below; the subsequent costs are
proved at the cleanup and repair stages, not smuggled into the hashing relation.

## Reference

- [alman2025more] Josh Alman, Ran Duan, Virginia Vassilevska Williams, Yinzhan Xu, Zixuan Xu,
  and Renfei Zhou, *More Asymmetry Yields Faster Matrix Multiplication*, Claim 6.18.
-/

namespace AlgebraicComplexity

open scoped BigOperators

universe u v w

namespace ProgressionHash.LegalTriple

variable {R : Type u} [Field R]
variable {E : Type v} [Fintype E] [DecidableEq E]
variable {iota : E → Type w} [∀ e, Fintype (iota e)]
variable {target : R}

/-- The number of aggregate X-collision proxies is at most the product of the factor X-fiber
sizes.

Proof sketch: ordinary X-collision proxies inject only into the full aggregate X-fiber.  The
aggregate fiber theorem identifies that fiber with the Cartesian product of the factor fibers. -/
theorem card_aggregate_xCompetitorYIndices_le_product
    (targets : ∀ e, Finset (LegalTriple R (iota e) target))
    (factors : ∀ e, LegalTriple R (iota e) target) :
    (xCompetitorYIndices (aggregateTargets targets) (aggregate factors)).card ≤
      ∏ e, (xFiber (targets e) (factors e)).card := by
  calc
    (xCompetitorYIndices (aggregateTargets targets) (aggregate factors)).card ≤
        (xFiber (aggregateTargets targets) (aggregate factors)).card :=
      card_xCompetitorYIndices_le_card_xFiber _ _
    _ = (legFiber (aggregateTargets targets) (aggregate factors) .X).card := by
      rfl
    _ = ∏ e, (legFiber (targets e) (factors e) .X).card :=
      card_aggregate_legFiber targets factors .X
    _ = ∏ e, (xFiber (targets e) (factors e)).card := by
      rfl

/-- Factorwise X-fiber bounds imply the aggregate marked-X field budget.

Proof sketch: multiply the factor inequalities, apply the preceding aggregate competitor bound,
and then multiply both sides by four. -/
theorem aggregateX_quarter_of_factorXFiberBounds
    [Fintype R]
    (ambient marked : ∀ e, Finset (LegalTriple R (iota e) target))
    (bound : E → ℕ)
    (hfiber : ∀ e (triple : LegalTriple R (iota e) target),
      triple ∈ marked e → (xFiber (ambient e) triple).card ≤ bound e)
    (hfield : 4 * (∏ e, bound e) ≤ Fintype.card R) :
    ∀ (factors : ∀ e, LegalTriple R (iota e) target),
      (∀ e, factors e ∈ marked e) →
        4 * (xCompetitorYIndices
          (aggregateTargets ambient) (aggregate factors)).card ≤ Fintype.card R := by
  intro factors hfactors
  calc
    4 * (xCompetitorYIndices
        (aggregateTargets ambient) (aggregate factors)).card ≤
        4 * (∏ e, (xFiber (ambient e) (factors e)).card) :=
      Nat.mul_le_mul_left 4
        (card_aggregate_xCompetitorYIndices_le_product ambient factors)
    _ ≤ 4 * (∏ e, bound e) :=
      Nat.mul_le_mul_left 4 <|
        Finset.prod_le_prod' fun e _ ↦ hfiber e (factors e) (hfactors e)
    _ ≤ Fintype.card R := hfield

/-- One marked affine hash isolates X in a heterogeneous Cartesian product while retaining the
sharp marked-side count.

The selected targets survive the ambient common-bucket filter and are injective only on X.  The
field premise is the product of the factor X-fiber sizes; there is no hidden Y/Z completeness or
legwise-isolation premise.

Proof sketch: instantiate `exists_seed_many_markedXIsolatedTargets` on the two aggregate target
families.  Recover the unique factor presentation of each marked aggregate target, discharge its
competitor bound with `card_aggregate_xCompetitorYIndices_le_product`, and rewrite the marked
aggregate cardinality as a product. -/
theorem exists_seed_many_aggregateMarkedXIsolatedTargets
    [Fintype R] [NeZero (2 : R)]
    (ambient marked : ∀ e, Finset (LegalTriple R (iota e) target))
    (hmarked : ∀ e, marked e ⊆ ambient e)
    (B : Finset R)
    (hquarter : ∀ (factors : ∀ e, LegalTriple R (iota e) target),
      (∀ e, factors e ∈ marked e) →
        4 * (∏ e, (xFiber (ambient e) (factors e)).card) ≤ Fintype.card R) :
    ∃ seed : ProgressionHash.Seed R (Sigma iota),
      3 * (∏ e, (marked e).card) * B.card ≤
          4 * (Fintype.card R * Fintype.card R) *
            (markedXIsolatedTargets
              (aggregateTargets ambient) (aggregateTargets marked) B seed).card ∧
        markedXIsolatedTargets
            (aggregateTargets ambient) (aggregateTargets marked) B seed ⊆
          filteredTargets (aggregateTargets ambient) B seed ∧
        Set.InjOn
          (fun triple : LegalTriple R (Sigma iota) target ↦ triple.xIndex)
          (markedXIsolatedTargets
            (aggregateTargets ambient) (aggregateTargets marked) B seed : Set _) := by
  have hsubset : aggregateTargets marked ⊆ aggregateTargets ambient :=
    aggregateTargets_mono hmarked
  obtain ⟨seed, hcount, hfiltered, hinjective⟩ :=
    exists_seed_many_markedXIsolatedTargets
      (aggregateTargets ambient) (aggregateTargets marked) hsubset B (by
        intro triple htriple
        obtain ⟨factors, hfactors, rfl⟩ :=
          (mem_aggregateTargets marked triple).mp htriple
        exact (Nat.mul_le_mul_left 4
          (card_aggregate_xCompetitorYIndices_le_product ambient factors)).trans
            (hquarter factors hfactors))
  refine ⟨seed, ?_, hfiltered, hinjective⟩
  simpa only [card_aggregateTargets] using hcount

end ProgressionHash.LegalTriple

end AlgebraicComplexity
