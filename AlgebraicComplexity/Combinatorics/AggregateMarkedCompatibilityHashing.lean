/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Combinatorics.AggregateMarkedHashing
import AlgebraicComplexity.Combinatorics.MarkedCompatibilityHashingIsolation

set_option autoImplicit false

/-!
# Directional compatibility hashing for heterogeneous aggregate families

An aggregate laser step must choose one collision direction for the whole heterogeneous product.
If factor `e` has at most `b e c` competitors in direction `c`, the resulting aggregate budget is

`sum_c prod_e b e c`,

not a product of factorwise three-way sums.  This module proves that finite counting statement for
an arbitrary family of directional compatibility relations and feeds it to the existing marked
compatibility-hashing theorem.

The aggregate relation records explicit factor witnesses and one shared direction.  Every triple
in the image of `aggregate` has a unique factor presentation; the accompanying iff theorem exposes
the resulting `∃ c, ∀ e` quantifier order without introducing an arbitrary inverse operation.  A
semantic client must also prove that every directional factor relation forces equality of the
corresponding actual tensor leg.  That premise is what makes the standard affine collision proxy
sound.

Everything here is finite and tensor-independent.  There is no entropy estimate, asymptotic
passage, constituent degeneration, or matrix-multiplication assumption.
-/

namespace AlgebraicComplexity

open scoped BigOperators

universe u v w x

namespace ProgressionHash.LegalTriple

variable {R : Type u} [Field R]
variable {target : R}

/-- The targets in one factor family that are directionally compatible with a fixed target.

This named finite filter keeps classical decidable equality and proposition instances out of the
public counting-theorem signatures.
-/
noncomputable def directionalCompatibilityFiber
    {J : Type x}
    (ambient : Finset (LegalTriple R J target))
    (compatible : Tensor.Leg → LegalTriple R J target → LegalTriple R J target → Prop)
    (left : LegalTriple R J target) (c : Tensor.Leg) :
    Finset (LegalTriple R J target) := by
  classical
  exact ambient.filter (compatible c left)

/-- Membership in a directional compatibility fiber is ambient membership together with the
chosen directional relation.

Proof sketch: unfold the named filter and use the membership law for `Finset.filter`.
-/
@[simp] theorem mem_directionalCompatibilityFiber
    {J : Type x}
    (ambient : Finset (LegalTriple R J target))
    (compatible : Tensor.Leg → LegalTriple R J target → LegalTriple R J target → Prop)
    (left : LegalTriple R J target) (c : Tensor.Leg)
    (right : LegalTriple R J target) :
    right ∈ directionalCompatibilityFiber ambient compatible left c ↔
      right ∈ ambient ∧ compatible c left right := by
  classical
  simp [directionalCompatibilityFiber]

variable {E : Type v} [Fintype E] [DecidableEq E]
variable {ι : E → Type w} [∀ e, Fintype (ι e)]

/-- Two aggregate triples are directionally compatible when they have factor presentations and
one common tensor leg makes every corresponding factor pair compatible.

The witnesses deliberately include both aggregate equalities.  Injectivity of `aggregate` makes
the factor presentations unique; keeping them explicit makes the shared `∃ c, ∀ e` direction
visible to later counting proofs.
-/
def AggregateDirectionalCompatible
    (compatible : ∀ e, Tensor.Leg →
      LegalTriple R (ι e) target → LegalTriple R (ι e) target → Prop)
    (left right : LegalTriple R (Sigma ι) target) : Prop :=
  ∃ leftFactors rightFactors c,
    aggregate leftFactors = left ∧
      aggregate rightFactors = right ∧
      ∀ e, compatible e c (leftFactors e) (rightFactors e)

/-- On explicitly aggregated families, directional compatibility means that one common leg works
for every factor.

Proof sketch: injectivity of `aggregate` identifies the two existential factor presentations with
the displayed families.  Conversely, the displayed families themselves witness the aggregate
relation. -/
@[simp] theorem aggregateDirectionalCompatible_aggregate_iff
    (compatible : ∀ e, Tensor.Leg →
      LegalTriple R (ι e) target → LegalTriple R (ι e) target → Prop)
    (left right : ∀ e, LegalTriple R (ι e) target) :
    AggregateDirectionalCompatible compatible (aggregate left) (aggregate right) ↔
      ∃ c, ∀ e, compatible e c (left e) (right e) := by
  constructor
  · rintro ⟨leftFactors, rightFactors, c, hleft, hright, hfactor⟩
    have hleftFactors : leftFactors = left := aggregate_injective hleft
    have hrightFactors : rightFactors = right := aggregate_injective hright
    refine ⟨c, ?_⟩
    intro e
    simpa only [hleftFactors, hrightFactors] using hfactor e
  · rintro ⟨c, hfactor⟩
    exact ⟨left, right, c, rfl, rfl, hfactor⟩

/-- Sound factor relations make aggregate directional compatibility an actual tensor-leg
collision.

Proof sketch: unpack the two factor presentations and the common direction `c`.  Factor
soundness gives equality of the `c`-words in every sigma component; function extensionality then
assembles those equalities into equality of the aggregate `c`-words.
-/
theorem aggregateDirectionalCompatible_sharesLeg
    (compatible : ∀ e, Tensor.Leg →
      LegalTriple R (ι e) target → LegalTriple R (ι e) target → Prop)
    (hsound : ∀ e c left right,
      compatible e c left right → left.legIndex c = right.legIndex c)
    {left right : LegalTriple R (Sigma ι) target}
    (hcompatible : AggregateDirectionalCompatible compatible left right) :
    SharesLeg left right := by
  obtain ⟨leftFactors, rightFactors, c, hleft, hright, hfactor⟩ := hcompatible
  subst left
  subst right
  refine ⟨c, ?_⟩
  funext position
  obtain ⟨e, i⟩ := position
  rw [aggregate_legIndex_apply, aggregate_legIndex_apply]
  exact congrFun (hsound e c (leftFactors e) (rightFactors e) (hfactor e)) i

/-- Aggregate compatible targets are bounded by a sum of products of factor fiber sizes.

The left side excludes the intended target, as required by affine collision isolation.  The
factor fibers on the right do not erase that target; when the relation is reflexive they include
it.  In every case, each fixed-direction family is a literal Cartesian product.

Proof sketch: a compatible aggregate competitor supplies one common direction and two aggregate
factor presentations.  Injectivity identifies the left presentation with `factors` and the right
presentation with the competitor's ambient presentation.  It therefore lies in the corresponding
Cartesian directional fiber.  Take the union over the three directions, apply the finite union
bound, and use `card_aggregateTargets` on every member.
-/
theorem card_aggregateDirectionalCompatibilityAlternativeTargets_le_sum_products
    (ambient : ∀ e, Finset (LegalTriple R (ι e) target))
    (compatible : ∀ e, Tensor.Leg →
      LegalTriple R (ι e) target → LegalTriple R (ι e) target → Prop)
    (factors : ∀ e, LegalTriple R (ι e) target) :
    (ProgressionHash.Seed.compatibilityAlternativeTargets
        (aggregateTargets ambient)
        (AggregateDirectionalCompatible compatible)
        (aggregate factors)).card ≤
      ∑ c : Tensor.Leg, ∏ e,
        (directionalCompatibilityFiber
          (ambient e) (compatible e) (factors e) c).card := by
  classical
  calc
    (ProgressionHash.Seed.compatibilityAlternativeTargets
        (aggregateTargets ambient)
        (AggregateDirectionalCompatible compatible)
        (aggregate factors)).card ≤
      ((Finset.univ : Finset Tensor.Leg).biUnion fun c ↦
        aggregateTargets fun e ↦ directionalCompatibilityFiber
          (ambient e) (compatible e) (factors e) c).card := by
        apply Finset.card_le_card
        intro other hother
        unfold ProgressionHash.Seed.compatibilityAlternativeTargets at hother
        have hdata := Finset.mem_filter.mp hother
        have hotherAmbient : other ∈ aggregateTargets ambient :=
          (Finset.mem_erase.mp hdata.1).2
        obtain ⟨ambientFactors, hambientFactors, hambient⟩ :=
          (mem_aggregateTargets ambient other).mp hotherAmbient
        obtain ⟨leftFactors, rightFactors, c, hleft, hright, hrelation⟩ := hdata.2
        have hleftFactors : leftFactors = factors := aggregate_injective hleft
        have hrightFactors : rightFactors = ambientFactors :=
          aggregate_injective (hright.trans hambient.symm)
        apply Finset.mem_biUnion.mpr
        refine ⟨c, Finset.mem_univ c, ?_⟩
        apply (mem_aggregateTargets
          (fun e ↦ directionalCompatibilityFiber
            (ambient e) (compatible e) (factors e) c) other).mpr
        refine ⟨rightFactors, ?_, hright⟩
        intro e
        apply (mem_directionalCompatibilityFiber
          (ambient e) (compatible e) (factors e) c (rightFactors e)).mpr
        refine ⟨?_, ?_⟩
        · simpa only [hrightFactors] using hambientFactors e
        · simpa only [hleftFactors] using hrelation e
    _ ≤ ∑ c ∈ (Finset.univ : Finset Tensor.Leg),
        (aggregateTargets fun e ↦ directionalCompatibilityFiber
          (ambient e) (compatible e) (factors e) c).card :=
      Finset.card_biUnion_le
    _ = ∑ c : Tensor.Leg, ∏ e,
        (directionalCompatibilityFiber
          (ambient e) (compatible e) (factors e) c).card := by
      simp only [card_aggregateTargets]

/-- The aggregate collision-index family obeys the same branch-first sum-of-products bound.

Proof sketch: taking the image of compatible target competitors under `collisionProxy` cannot
increase cardinality; apply the preceding target-family estimate.
-/
theorem card_aggregateDirectionalCompatibilityAlternativeIndices_le_sum_products
    (ambient : ∀ e, Finset (LegalTriple R (ι e) target))
    (compatible : ∀ e, Tensor.Leg →
      LegalTriple R (ι e) target → LegalTriple R (ι e) target → Prop)
    (factors : ∀ e, LegalTriple R (ι e) target) :
    (ProgressionHash.Seed.compatibilityAlternativeIndices
        (aggregateTargets ambient)
        (AggregateDirectionalCompatible compatible)
        collisionProxy (aggregate factors)).card ≤
      ∑ c : Tensor.Leg, ∏ e,
        (directionalCompatibilityFiber
          (ambient e) (compatible e) (factors e) c).card := by
  exact (ProgressionHash.Seed.card_compatibilityAlternativeIndices_le
    (aggregateTargets ambient)
    (AggregateDirectionalCompatible compatible)
    collisionProxy (aggregate factors)).trans
      (card_aggregateDirectionalCompatibilityAlternativeTargets_le_sum_products
        ambient compatible factors)

/-- One marked affine hash isolates a heterogeneous Cartesian product using one common
directional choice.

The marked count is the product of factor marked-family sizes.  The collision budget multiplies
factor bounds *within* each direction and sums only afterwards, so no factorwise directional
minimum is introduced.  The conclusion is isolation for `AggregateDirectionalCompatible`, not
ordinary legwise isolation: upgrading it requires the additional, generally stronger statement
that every aggregate leg collision is witnessed by the client relation.  Keeping that implication
out of this theorem prevents a directional counting certificate from laundering a weaker cleanup
relation into the standard legwise one.

Proof sketch: turn the factor bounds into the aggregate alternative-index bound using the previous
theorem and monotonicity of finite sums and products.  Factor soundness turns the aggregate
relation into `SharesLeg`, discharging the semantic premise of
`exists_seed_many_markedCompatibilityHashIsolatedLegalTargets`.  Finally rewrite the cardinality
of the marked aggregate family by `card_aggregateTargets`.
-/
theorem exists_seed_many_aggregateMarkedDirectionalCompatibilityIsolatedTargets
    [Fintype R] [NeZero (2 : R)]
    (ambient marked : ∀ e, Finset (LegalTriple R (ι e) target))
    (hmarked : ∀ e, marked e ⊆ ambient e)
    (B : Finset R)
    (compatible : ∀ e, Tensor.Leg →
      LegalTriple R (ι e) target → LegalTriple R (ι e) target → Prop)
    (hsound : ∀ e c left right,
      compatible e c left right → left.legIndex c = right.legIndex c)
    (bound : E → Tensor.Leg → ℕ)
    (hbound : ∀ e c (left : LegalTriple R (ι e) target),
      left ∈ marked e →
        (directionalCompatibilityFiber
          (ambient e) (compatible e) left c).card ≤ bound e c)
    (hfield : 4 * (∑ c : Tensor.Leg, ∏ e, bound e c) ≤ Fintype.card R) :
    ∃ seed : ProgressionHash.Seed R (Sigma ι),
      3 * (∏ e, (marked e).card) * B.card ≤
          4 * (Fintype.card R * Fintype.card R) *
            (ProgressionHash.Seed.markedCompatibilityHashIsolatedTargets
              (aggregateTargets ambient) (aggregateTargets marked) B
              LegalTriple.xIndex LegalTriple.yIndex
              (AggregateDirectionalCompatible compatible) collisionProxy seed).card ∧
        ProgressionHash.Seed.markedCompatibilityHashIsolatedTargets
            (aggregateTargets ambient) (aggregateTargets marked) B
            LegalTriple.xIndex LegalTriple.yIndex
            (AggregateDirectionalCompatible compatible) collisionProxy seed ⊆
          ProgressionHash.Seed.commonBucketFilteredTargets
            (aggregateTargets ambient) B LegalTriple.xIndex LegalTriple.yIndex seed ∧
        ProgressionHash.Seed.markedCompatibilityHashIsolatedTargets
            (aggregateTargets ambient) (aggregateTargets marked) B
            LegalTriple.xIndex LegalTriple.yIndex
            (AggregateDirectionalCompatible compatible) collisionProxy seed ⊆
          ProgressionHash.Seed.compatibilityIsolatedTargets
            (ProgressionHash.Seed.commonBucketFilteredTargets
              (aggregateTargets ambient) B LegalTriple.xIndex LegalTriple.yIndex seed)
            (AggregateDirectionalCompatible compatible) := by
  have hquarter : ∀ left ∈ aggregateTargets marked,
      4 * (ProgressionHash.Seed.compatibilityAlternativeIndices
        (aggregateTargets ambient)
        (AggregateDirectionalCompatible compatible)
        collisionProxy left).card ≤ Fintype.card R := by
    intro left hleft
    obtain ⟨factors, hfactors, rfl⟩ :=
      (mem_aggregateTargets marked left).mp hleft
    apply (Nat.mul_le_mul_left 4 ?_).trans hfield
    exact (card_aggregateDirectionalCompatibilityAlternativeIndices_le_sum_products
      ambient compatible factors).trans <|
        Finset.sum_le_sum fun c _ ↦
          Finset.prod_le_prod' fun e _ ↦ hbound e c (factors e) (hfactors e)
  obtain ⟨seed, hcount, hfiltered, hisolated⟩ :=
    exists_seed_many_markedCompatibilityHashIsolatedLegalTargets
      (aggregateTargets ambient) (aggregateTargets marked)
      (aggregateTargets_mono hmarked) B
      (AggregateDirectionalCompatible compatible)
      (by
        intro left _hleft right _hright hcompatible
        exact aggregateDirectionalCompatible_sharesLeg
          compatible hsound hcompatible)
      hquarter
  refine ⟨seed, ?_, hfiltered, hisolated⟩
  simpa only [card_aggregateTargets] using hcount

end ProgressionHash.LegalTriple

end AlgebraicComplexity
