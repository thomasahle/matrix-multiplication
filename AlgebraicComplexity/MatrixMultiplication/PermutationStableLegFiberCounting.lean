import AlgebraicComplexity.MatrixMultiplication.PartitionedPowerHashing
import AlgebraicComplexity.Tensor.TypeExtraction

/-!
# Exact leg-fiber counts in permutation-stable word families

A type-selected laser family is invariant under a common permutation of sample positions.  If
every word has the same type on one tensor leg, then this action is transitive on all words of
that leg type.  Consequently every leg fiber has the same cardinality and an exact double count
gives

`leg type class size * one leg-fiber size = ambient family size`.

This is the division-free finite identity behind the combination-loss exponent.  It applies to
families selected by several marginal constraints and therefore does not require the ambient
words to have one fixed full joint type.
-/

namespace AlgebraicComplexity

open Tensor

universe u v w

namespace PartitionHashEncoding

variable {R : Type u} [Field R]
variable {A : Leg → Type v} [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]
variable {support : Finset (BlockAddress A)}

/-- Exact source-side double count for one leg of a permutation-stable word family. -/
theorem card_legType_mul_card_sourceWordLegFiber
    (n : ℕ) (words : Finset (PositiveWord support n)) (c : Leg)
    (hstable : ∀ (e : Equiv.Perm (Fin (n + 1))) word,
      word ∈ words ↔ positiveWordReindex n e word ∈ words)
    (legType : A c → ℕ)
    (hwords : ∀ word ∈ words,
      WordType.multiplicity
          (positiveWordEquiv (A c) n (supportWordAddress n word c)) = legType)
    (target : PositiveWord (A c) n)
    (htarget : target ∈ positiveTypeClass (A c) n legType) :
    (positiveTypeClass (A c) n legType).card *
        (sourceWordLegFiber n words c target).card = words.card := by
  classical
  symm
  calc
    words.card =
        ∑ candidate ∈ positiveTypeClass (A c) n legType,
          (words.filter fun word ↦ supportWordAddress n word c = candidate).card := by
      exact Finset.card_eq_sum_card_fiberwise (fun word hword ↦ by
        simpa using (mem_positiveTypeClass.mpr (hwords word hword)))
    _ = ∑ _candidate ∈ positiveTypeClass (A c) n legType,
          (sourceWordLegFiber n words c target).card := by
      apply Finset.sum_congr rfl
      intro candidate hcandidate
      change (sourceWordLegFiber n words c candidate).card = _
      apply card_sourceWordLegFiber_eq_of_multiplicity_eq n words c hstable
      exact (mem_positiveTypeClass.mp hcandidate).trans
        (mem_positiveTypeClass.mp htarget).symm
    _ = (positiveTypeClass (A c) n legType).card *
        (sourceWordLegFiber n words c target).card := by simp

/-- Hash encoding preserves the exact division-free leg-fiber identity. -/
theorem card_legType_mul_card_legFiber_legalTargets
    (H : PartitionHashEncoding (R := R) support)
    (n : ℕ) (words : Finset (PositiveWord support n)) (c : Leg)
    (hstable : ∀ (e : Equiv.Perm (Fin (n + 1))) word,
      word ∈ words ↔ positiveWordReindex n e word ∈ words)
    (legType : A c → ℕ)
    (hwords : ∀ word ∈ words,
      WordType.multiplicity
          (positiveWordEquiv (A c) n (supportWordAddress n word c)) = legType)
    {triple : ProgressionHash.LegalTriple R (Fin (n + 1)) H.target}
    (htriple : triple ∈ H.legalTargets n words)
    (htarget : H.modeledAddress n triple c ∈
      positiveTypeClass (A c) n legType) :
    (positiveTypeClass (A c) n legType).card *
        (ProgressionHash.LegalTriple.legFiber
          (H.legalTargets n words) triple c).card = words.card := by
  rw [H.card_legFiber_legalTargets_eq_card_sourceWordLegFiber n words htriple c]
  exact card_legType_mul_card_sourceWordLegFiber
    n words c hstable legType hwords (H.modeledAddress n triple c) htarget

end PartitionHashEncoding

end AlgebraicComplexity
