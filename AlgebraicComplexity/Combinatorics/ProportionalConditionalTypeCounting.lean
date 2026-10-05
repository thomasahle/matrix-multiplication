import AlgebraicComplexity.Analysis.StructuralZeroConditionalType
import AlgebraicComplexity.Combinatorics.PushedConditionalEntropyCore
import AlgebraicComplexity.Combinatorics.PushedProfileTypeCountingCore

/-! # Proportional conditional type counting -/

open scoped BigOperators

namespace AlgebraicComplexity.WordType

universe u v

variable {Cell : Type u} {Feature : Type v}
variable [Fintype Cell] [Fintype Feature]

/-- Exact division-free conditional type count for a proportional joint profile. -/
theorem multinomial_cell_mul_card_proportionalConditionalTypeClass
    (cellProfile : Cell → ℕ) (jointProfile : Cell × Feature → ℕ)
    (hmargin : mappedType Prod.fst jointProfile = cellProfile)
    (k : ℕ) (source : Fin (profileMass cellProfile * k) → Cell)
    (hsource : multiplicity source = proportionalCounts cellProfile k) :
    Nat.multinomial Finset.univ (multiplicity source) *
        (conditionalTypeClass source
          (proportionalCounts jointProfile k)).card =
      Nat.multinomial Finset.univ (proportionalCounts jointProfile k) := by
  have hmass : profileMass jointProfile = profileMass cellProfile := by
    rw [← hmargin]
    exact (profileMass_mappedType Prod.fst jointProfile).symm
  apply multinomial_source_mul_card_conditionalTypeClass
  · simpa only [hmass] using proportionalCounts_mem_types jointProfile k
  · rw [mappedType_proportionalCounts, hmargin]
    exact hsource.symm

/-- Sequence-ready upper count for one exact quotient cell/feature profile.  Its only loss is the
source profile's structural-zero factor; the exponential base is precisely the conditional
entropy recorded by the pushed compatibility tables. -/
theorem card_proportionalConditionalTypeClass_le_entropyBase_pow
    (cellProfile : Cell → ℕ) (jointProfile : Cell × Feature → ℕ)
    (hmargin : mappedType Prod.fst jointProfile = cellProfile)
    (hmass : 0 < profileMass cellProfile)
    (k : ℕ) (hk : 0 < k)
    (source : Fin (profileMass cellProfile * k) → Cell)
    (hsource : multiplicity source = proportionalCounts cellProfile k) :
    ((conditionalTypeClass source
        (proportionalCounts jointProfile k)).card : ℝ) ≤
      structuralZeroMultinomialLoss cellProfile k *
        conditionalProfileEntropyBase cellProfile jointProfile ^ k := by
  have hjointMass : profileMass jointProfile = profileMass cellProfile := by
    rw [← hmargin]
    exact (profileMass_mappedType Prod.fst jointProfile).symm
  have hjointMassPos : 0 < profileMass jointProfile := by
    rw [hjointMass]
    exact hmass
  have hjoint : proportionalCounts jointProfile k ∈
      types (Cell × Feature) (profileMass cellProfile * k) := by
    simpa only [hjointMass] using proportionalCounts_mem_types jointProfile k
  have hmap : mappedType Prod.fst (proportionalCounts jointProfile k) =
      multiplicity source := by
    rw [mappedType_proportionalCounts, hmargin]
    exact hsource.symm
  have hbound :=
    card_conditionalTypeClass_le_structuralZeroLoss_mul_exp_entropyDifference
      cellProfile k source (proportionalCounts jointProfile k)
        hmass hk hsource hjoint hmap
  have hscaledMass : profileMass (proportionalCounts jointProfile k) =
      profileMass jointProfile * k := by
    simp [profileMass, proportionalCounts, Finset.sum_mul]
  have hscaledEntropy :=
    profileEntropyNats_proportionalCounts jointProfile hjointMassPos k hk
  calc
    ((conditionalTypeClass source
        (proportionalCounts jointProfile k)).card : ℝ) ≤
        structuralZeroMultinomialLoss cellProfile k *
          Real.exp
            ((profileMass (proportionalCounts jointProfile k) : ℝ) *
                profileEntropyNats (proportionalCounts jointProfile k) -
              (k : ℝ) * (profileMass cellProfile : ℝ) *
                profileEntropyNats cellProfile) := hbound
    _ = structuralZeroMultinomialLoss cellProfile k *
        conditionalProfileEntropyBase cellProfile jointProfile ^ k := by
      congr 1
      unfold conditionalProfileEntropyBase
      rw [← Real.exp_nat_mul]
      congr 1
      rw [hscaledMass, hscaledEntropy, hjointMass]
      push_cast
      ring

/-- Sequence-facing restatement: the exact pushed conditional class is bounded by a fixed
entropy base to the repetition power, times the positive subexponential loss
`pushedConditionalTypeLoss`.  This is the shape consumed by full-bucket field-size data. -/
theorem card_proportionalConditionalTypeClass_le_loss_mul_entropyBase_pow
    (cellProfile : Cell → ℕ) (jointProfile : Cell × Feature → ℕ)
    (hmargin : mappedType Prod.fst jointProfile = cellProfile)
    (hmass : 0 < profileMass cellProfile)
    (k : ℕ) (hk : 0 < k)
    (source : Fin (profileMass cellProfile * k) → Cell)
    (hsource : multiplicity source = proportionalCounts cellProfile k) :
    ((conditionalTypeClass source
        (proportionalCounts jointProfile k)).card : ℝ) ≤
      pushedConditionalTypeLoss cellProfile k *
        conditionalProfileEntropyBase cellProfile jointProfile ^ k := by
  exact card_proportionalConditionalTypeClass_le_entropyBase_pow
    cellProfile jointProfile hmargin hmass k hk source hsource

end AlgebraicComplexity.WordType
