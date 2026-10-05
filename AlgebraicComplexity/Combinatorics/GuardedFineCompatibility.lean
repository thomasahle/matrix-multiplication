/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import Mathlib.Data.Finset.Card

set_option autoImplicit false

/-!
# Restricting fine compatibility to an allowed fine family

Claim 6.18 of Alman--Duan--Vassilevska Williams--Xu--Xu--Zhou first restricts the
fine blocks to the prescribed typical family and only then counts compatible competitors.  The
ambient fine-block type used by a hashing theorem can be larger than that selected family.  This
module records the preceding selection directly in the compatibility relation.

`FineGuardedCompatible allowed compatible` agrees with `compatible` on owner/fine pairs accepted
by `allowed` and is false otherwise.  Consequently filtering any finite ambient family by guarded
compatibility is unchanged on the allowed family and empty off it.  The final theorem turns a
cardinality bound required only for allowed fine blocks into a uniform `forall fine` bound.

This is the relation-level guard used in [alman2025more, Claim 6.18],
`papers/sources/2404.16349/constituent.tex:350-386`.  It performs no typical-set count, entropy
estimate, hashing selection, tensor restriction, or asymptotic passage.

## Reference

- [alman2025more] Josh Alman, Ran Duan, Virginia Vassilevska Williams, Yinzhan Xu, Zixuan Xu,
  and Renfei Zhou, *More Asymmetry Yields Faster Matrix Multiplication*.
-/

namespace AlgebraicComplexity

universe u v w x

namespace ProgressionHash.LegalTriple

variable {Owner : Type u} {Fine : Type v} {Competitor : Type w} {Index : Type x}

/-- Compatibility guarded by an owner-relative predicate on fine blocks.

Human-readable statement: `competitor` is related to the fine block only when the fine block was
retained by the preceding selection and the original compatibility relation holds.

Proof sketch: this is the conjunction of the two conditions, kept as a named relation so clients
cannot silently apply a selected-family estimate to excluded fine blocks. -/
def FineGuardedCompatible
    (allowed : Owner → Fine → Prop)
    (compatible : Owner → Fine → Competitor → Prop)
    (owner : Owner) (fine : Fine) (competitor : Competitor) : Prop :=
  allowed owner fine ∧ compatible owner fine competitor

/-- A guarded compatibility relation inherits every shared-leg conclusion of the underlying
relation.

Proof sketch: discard the guard and apply the supplied soundness theorem to the remaining
compatibility witness. -/
theorem fineGuardedCompatible_sharesLeg
    (allowed : Owner → Fine → Prop)
    (compatible : Owner → Fine → Competitor → Prop)
    (ownerIndex : Owner → Index) (competitorIndex : Competitor → Index)
    (hsound : ∀ owner fine competitor, compatible owner fine competitor →
      competitorIndex competitor = ownerIndex owner)
    {owner : Owner} {fine : Fine} {competitor : Competitor}
    (hcompatible : FineGuardedCompatible allowed compatible owner fine competitor) :
    competitorIndex competitor = ownerIndex owner :=
  hsound owner fine competitor hcompatible.2

/-- If an owner/fine pair is excluded, its guarded compatibility fiber is empty.

Proof sketch: membership would expose the false guard, so extensionality reduces every membership
test to `False`. -/
theorem filter_fineGuardedCompatible_eq_empty_of_not_allowed
    (ambient : Finset Competitor)
    (allowed : Owner → Fine → Prop)
    (compatible : Owner → Fine → Competitor → Prop)
    (owner : Owner) (fine : Fine)
    (hallowed : ¬ allowed owner fine) :
    @Finset.filter Competitor (FineGuardedCompatible allowed compatible owner fine)
      (Classical.decPred _) ambient = ∅ := by
  classical
  ext competitor
  simp [FineGuardedCompatible, hallowed]

/-- If an owner/fine pair is allowed, guarding leaves its compatibility fiber unchanged.

Proof sketch: the true guard disappears from the membership conjunction. -/
theorem filter_fineGuardedCompatible_eq_of_allowed
    (ambient : Finset Competitor)
    (allowed : Owner → Fine → Prop)
    (compatible : Owner → Fine → Competitor → Prop)
    (owner : Owner) (fine : Fine)
    (hallowed : allowed owner fine) :
    @Finset.filter Competitor (FineGuardedCompatible allowed compatible owner fine)
        (Classical.decPred _) ambient =
      @Finset.filter Competitor (compatible owner fine) (Classical.decPred _) ambient := by
  classical
  ext competitor
  simp [FineGuardedCompatible, hallowed]

/-- A bound proved only for allowed fine blocks extends uniformly to the guarded relation.

Human-readable statement: allowed fine blocks use the supplied estimate, while excluded fine
blocks have no competitors and hence satisfy every natural-number upper bound.

Proof sketch: split on `allowed owner fine`; rewrite the guarded fiber by the corresponding
on/off theorem, then use the supplied bound or the cardinality of the empty set. -/
theorem card_filter_fineGuardedCompatible_le
    (ambient : Finset Competitor)
    (allowed : Owner → Fine → Prop)
    (compatible : Owner → Fine → Competitor → Prop)
    (bound : ℕ) (owner : Owner) (fine : Fine)
    (hbound : allowed owner fine →
      (@Finset.filter Competitor (compatible owner fine)
        (Classical.decPred _) ambient).card ≤ bound) :
    (@Finset.filter Competitor (FineGuardedCompatible allowed compatible owner fine)
      (Classical.decPred _) ambient).card ≤ bound := by
  by_cases hallowed : allowed owner fine
  · rw [filter_fineGuardedCompatible_eq_of_allowed
      ambient allowed compatible owner fine hallowed]
    exact hbound hallowed
  · rw [filter_fineGuardedCompatible_eq_empty_of_not_allowed
      ambient allowed compatible owner fine hallowed]
    exact Nat.zero_le bound

/-! The singleton client below shows that the allowed branch is genuinely inhabited and that the
uniform cardinality theorem can be applied without an empty ambient family. -/

private example :
    (@Finset.filter Unit
      (FineGuardedCompatible
        (fun _owner _fine : Unit ↦ True)
        (fun _owner _fine competitor : Unit ↦ competitor = ()) () ())
      (Classical.decPred _) {()}).card ≤ 1 := by
  apply card_filter_fineGuardedCompatible_le
  intro _hallowed
  classical
  simp

end ProgressionHash.LegalTriple

end AlgebraicComplexity
