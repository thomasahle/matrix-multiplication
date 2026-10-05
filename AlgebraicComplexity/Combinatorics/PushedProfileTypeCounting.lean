import AlgebraicComplexity.Analysis.ProportionalTypeClassGrowth
import AlgebraicComplexity.Combinatorics.PushedConditionalEntropy
import AlgebraicComplexity.Combinatorics.PushedConditionalTypeCounting

/-!
# Type counting after a finite alphabet quotient

Compatibility extraction may observe a finite feature of a finer block symbol.  This file
records the exact method-of-types interface for that operation.  For a finite map `f : A → B`,
the pushed profile is `mappedType f p`; no representative of an `f`-fiber is chosen.

There are two complementary statements.

* A pushed type class has exactly its own multinomial cardinality and every word in it admits a
  fine lift of the prescribed source type.  The exact product identity shows where the unused
  fine-fiber multiplicity lives.
* With a fixed cell word, a pushed joint cell/feature profile has the conditional-entropy
  exponent `H(cell, feature) - H(cell)`, up to the existing structural-zero loss.  This is the
  finite counting statement used by a quotient-feature version of Claim 6.18.

The results are generic over finite alphabets.  A CW total-weight client only has to instantiate
`f` with `cwSplitWordTotalDigit` and prove that its prescribed integer tables are these mapped
profiles.
-/

open scoped BigOperators

namespace AlgebraicComplexity.WordType

universe u v w

variable {A : Type u} {B : Type v} [Fintype A] [Fintype B]

/-- A finite map sends every legal source type to a legal target type of the same word length. -/
theorem mappedType_mem_types
    (f : A → B) {profile : A → ℕ} {n : ℕ}
    (hprofile : profile ∈ types A n) :
    mappedType f profile ∈ types B n := by
  classical
  obtain ⟨word, hword⟩ := typeClass_nonempty profile hprofile
  have htype : multiplicity word = profile := mem_typeClass.mp hword
  rw [← htype, ← multiplicity_comp_eq_mappedType]
  exact multiplicity_mem_types (f ∘ word)

/-- The proportional pushed profile is a legal type at the original scaled word length. -/
theorem proportionalMappedType_mem_types
    (f : A → B) (profile : A → ℕ) (k : ℕ) :
    proportionalCounts (mappedType f profile) k ∈
      types B (profileMass profile * k) := by
  rw [← profileMass_mappedType f profile]
  exact proportionalCounts_mem_types (mappedType f profile) k

/-- Exact finite quotient/fiber factorization for a proportional source profile.  The quotient
type-class count and the equally-sized fine lift fiber multiply to the complete fine type class;
there is no choice of a representative word in this statement. -/
theorem card_pushedTypeClass_mul_card_typedFiber
    (f : A → B) (profile : A → ℕ) (k : ℕ)
    (target : Fin (profileMass profile * k) → B)
    (htarget : target ∈ typeClass (profileMass profile * k)
      (proportionalCounts (mappedType f profile) k)) :
    (typeClass (profileMass profile * k)
        (proportionalCounts (mappedType f profile) k)).card *
      (typedWordMapFiber f (proportionalCounts profile k) target).card =
        (typeClass (profileMass profile * k)
          (proportionalCounts profile k)).card := by
  have htarget' : target ∈ typeClass (profileMass profile * k)
      (mappedType f (proportionalCounts profile k)) := by
    simpa only [mappedType_proportionalCounts] using htarget
  simpa only [mappedType_proportionalCounts] using
    (card_targetType_mul_card_typedWordMapFiber
      f (proportionalCounts profile k) target htarget')

/-- Every quotient word of the exact pushed proportional type has at least one fine lift of the
entire prescribed source type. -/
theorem pushedType_typedFiber_nonempty
    (f : A → B) (profile : A → ℕ) (k : ℕ)
    (target : Fin (profileMass profile * k) → B)
    (htarget : target ∈ typeClass (profileMass profile * k)
      (proportionalCounts (mappedType f profile) k)) :
    (typedWordMapFiber f (proportionalCounts profile k) target).Nonempty := by
  rw [← Finset.card_pos]
  have hfactor := card_pushedTypeClass_mul_card_typedFiber
    f profile k target htarget
  have hfine : 0 < (typeClass (profileMass profile * k)
      (proportionalCounts profile k)).card :=
    card_proportionalTypeClass_pos profile k
  rw [← hfactor] at hfine
  exact Nat.pos_of_mul_pos_left hfine

/-- Entropy-base lower count for the pushed type class, allowing structural zeroes in either the
fine profile or its pushforward. -/
theorem pushedEntropyBase_pow_le_structuralZeroLoss_mul_card_typeClass
    (f : A → B) (profile : A → ℕ) (k : ℕ) :
    proportionalEntropyBase (mappedType f profile) ^ k ≤
      structuralZeroMultinomialLoss (mappedType f profile) k *
        ((typeClass (profileMass profile * k)
          (proportionalCounts (mappedType f profile) k)).card : ℝ) := by
  rw [← profileMass_mappedType f profile]
  exact proportionalEntropyBase_pow_le_structuralZeroLoss_mul_card_typeClass
    (mappedType f profile) k

end AlgebraicComplexity.WordType
