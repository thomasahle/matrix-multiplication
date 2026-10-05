import AlgebraicComplexity.Analysis.StructuralZeroMultinomial
import AlgebraicComplexity.Analysis.MaximumEntropyMappedFiber
import AlgebraicComplexity.Probability.IntegralProfile

/-!
# Maximum-entropy bounds for finite mapped-type fibers

This module formalizes the counting step behind classical laser arguments.  Fix an integral
reference profile on a finite alphabet and several visible coordinate maps.  If the normalized
reference profile maximizes entropy among probability laws with the same coordinate
pushforwards, then every finite family of words having those mapped types is at most a polynomial
factor larger than the reference type class.

The proof deliberately separates three reusable facts:

* normalized integral profiles turn exact mapped-count equalities into pushforward equalities;
* maximum entropy bounds every feasible multinomial coefficient by the reference entropy
  exponential; and
* there are at most `(n+1)^|I|` empirical types of words of length `n`.

Structural zeroes in competing empirical types are allowed.  The reference profile is required
only to have positive total mass; its multinomial lower bound uses the zero-safe loss from
`StructuralZeroMultinomial`.
-/

open scoped BigOperators

namespace AlgebraicComplexity.WordType

universe u v w

variable {I : Type u} [Fintype I]
variable {C : Type v}
variable {A : C → Type w} [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]

/-- A feasible empirical profile has no more entropy than a maximum-entropy reference profile.

Proof sketch: normalize both integral profiles.  Equality of total masses and every mapped count
gives equality of all visible pushforwards.  Apply the supplied maximum-entropy property and
rewrite the two probability entropies as profile entropies. -/
theorem profileEntropyNats_le_of_mappedTypes_eq
    (coordinate : ∀ c, I → A c)
    (reference joint : I → ℕ)
    (hrefMass : 0 < profileMass reference)
    (hjointMass : 0 < profileMass joint)
    (hmass : profileMass joint = profileMass reference)
    (hmapped : ∀ c, mappedType (coordinate c) joint =
      mappedType (coordinate c) reference)
    (hmaximum : IsMaximumEntropyInMappedFiber coordinate
      (normalizedProfileProbability reference hrefMass)) :
    profileEntropyNats joint ≤ profileEntropyNats reference := by
  let q := normalizedProfileProbability joint hjointMass
  let p := normalizedProfileProbability reference hrefMass
  have hfiber : ∀ c, q.pushforward (coordinate c) =
      p.pushforward (coordinate c) := by
    intro c
    apply ProbabilityVector.ext
    funext a
    rw [normalizedProfileProbability_pushforward_weight,
      normalizedProfileProbability_pushforward_weight, hmapped c, hmass]
  have h := hmaximum q hfiber
  simpa only [q, p, normalizedProfileProbability_entropy] using h

/-- Every feasible multinomial coefficient is bounded by the exponential entropy of a
maximum-entropy reference profile with the same mapped counts. -/
theorem multinomial_le_exp_referenceEntropy_of_mappedTypes_eq
    (coordinate : ∀ c, I → A c)
    (reference joint : I → ℕ)
    (hrefMass : 0 < profileMass reference)
    (hjointMass : 0 < profileMass joint)
    (hmass : profileMass joint = profileMass reference)
    (hmapped : ∀ c, mappedType (coordinate c) joint =
      mappedType (coordinate c) reference)
    (hmaximum : IsMaximumEntropyInMappedFiber coordinate
      (normalizedProfileProbability reference hrefMass)) :
    (Nat.multinomial Finset.univ joint : ℝ) ≤
      Real.exp ((profileMass reference : ℝ) * profileEntropyNats reference) := by
  calc
    (Nat.multinomial Finset.univ joint : ℝ) ≤
        Real.exp ((profileMass joint : ℝ) * profileEntropyNats joint) :=
      multinomial_le_exp_profileEntropy joint hjointMass
    _ ≤ Real.exp ((profileMass joint : ℝ) * profileEntropyNats reference) := by
      apply Real.exp_le_exp.mpr
      exact mul_le_mul_of_nonneg_left
        (profileEntropyNats_le_of_mappedTypes_eq coordinate reference joint
          hrefMass hjointMass hmass hmapped hmaximum) (by positivity)
    _ = Real.exp ((profileMass reference : ℝ) * profileEntropyNats reference) := by
      rw [hmass]

/-- A finite word family with prescribed proportional mapped types is bounded by the number of
possible empirical types times the reference entropy exponential.

The words are ordinary functions `Fin n → I`; clients using recursively encoded positive words can
transport their family through `positiveWordEquiv`.

Proof sketch: partition the supplied word family by its full empirical type.  An empty fiber costs
nothing.  A nonempty fiber is contained in the corresponding full type class, whose multinomial
cardinality is bounded by the preceding maximum-entropy theorem.  Finally bound the number of
possible types by `(n+1)^|I|`. -/
theorem card_words_le_typeCount_mul_exp_referenceEntropy
    (coordinate : ∀ c, I → A c)
    (reference : I → ℕ) (hrefMass : 0 < profileMass reference)
    (hmaximum : IsMaximumEntropyInMappedFiber coordinate
      (normalizedProfileProbability reference hrefMass))
    {n k : ℕ} (hk : 0 < k) (hn : n = profileMass reference * k)
    (words : Finset (Fin n → I))
    (hwords : ∀ word ∈ words, ∀ c,
      mappedType (coordinate c) (multiplicity word) =
        mappedType (coordinate c) (proportionalCounts reference k)) :
    (words.card : ℝ) ≤
      ((((n + 1) ^ Fintype.card I : ℕ) : ℝ)) *
        Real.exp (((k : ℝ) * profileMass reference) *
          profileEntropyNats reference) := by
  classical
  let scaled := proportionalCounts reference k
  have hscaledMass : profileMass scaled = profileMass reference * k := by
    simp [scaled, profileMass, proportionalCounts, Finset.sum_mul]
  have hscaledMassPos : 0 < profileMass scaled := by
    rw [hscaledMass]
    exact Nat.mul_pos hrefMass hk
  have hscaledProbability :
      normalizedProfileProbability scaled hscaledMassPos =
        normalizedProfileProbability reference hrefMass := by
    exact normalizedProfileProbability_proportionalCounts reference hrefMass hk
  have hscaledMaximum : IsMaximumEntropyInMappedFiber coordinate
      (normalizedProfileProbability scaled hscaledMassPos) := by
    simpa only [hscaledProbability] using hmaximum
  have hpartition :
      words.card =
        ∑ joint ∈ types I n,
          (words.filter fun word ↦ multiplicity word = joint).card := by
    exact Finset.card_eq_sum_card_fiberwise fun word _hword ↦
      multiplicity_mem_types word
  have hfiber (joint : I → ℕ) (hjoint : joint ∈ types I n) :
      (((words.filter fun word ↦ multiplicity word = joint).card : ℕ) : ℝ) ≤
        Real.exp (((k : ℝ) * profileMass reference) *
          profileEntropyNats reference) := by
    by_cases hempty : (words.filter fun word ↦ multiplicity word = joint).Nonempty
    · obtain ⟨word, hword⟩ := hempty
      have hwordData := Finset.mem_filter.mp hword
      have hmapped : ∀ c, mappedType (coordinate c) joint =
          mappedType (coordinate c) scaled := by
        intro c
        rw [← hwordData.2]
        exact hwords word hwordData.1 c
      have hmassJoint : profileMass joint = n := mem_types.mp hjoint
      have hmassEq : profileMass joint = profileMass scaled := by
        rw [hmassJoint, hn, hscaledMass]
      have hjointMassPos : 0 < profileMass joint := by
        rw [hmassEq]
        exact hscaledMassPos
      have hfilter :
          (words.filter fun word ↦ multiplicity word = joint) ⊆ typeClass n joint := by
        intro other hother
        exact mem_typeClass.mpr (Finset.mem_filter.mp hother).2
      calc
        (((words.filter fun word ↦ multiplicity word = joint).card : ℕ) : ℝ) ≤
            ((typeClass n joint).card : ℝ) := by
          exact_mod_cast Finset.card_le_card hfilter
        _ = (Nat.multinomial Finset.univ joint : ℝ) := by
          rw [card_typeClass_eq_multinomial joint hjoint]
        _ ≤ Real.exp ((profileMass scaled : ℝ) * profileEntropyNats scaled) :=
          multinomial_le_exp_referenceEntropy_of_mappedTypes_eq
            coordinate scaled joint hscaledMassPos hjointMassPos hmassEq hmapped
              hscaledMaximum
        _ = Real.exp (((k : ℝ) * profileMass reference) *
            profileEntropyNats reference) := by
          have hentropy : profileEntropyNats scaled = profileEntropyNats reference := by
            have h := congrArg ProbabilityVector.entropy hscaledProbability
            simpa only [normalizedProfileProbability_entropy] using h
          rw [hscaledMass, hentropy]
          push_cast
          congr 1
          ring
    · rw [Finset.not_nonempty_iff_eq_empty.mp hempty]
      simp
      exact Real.exp_nonneg _
  calc
    (words.card : ℝ) =
        ∑ joint ∈ types I n,
          (((words.filter fun word ↦ multiplicity word = joint).card : ℕ) : ℝ) := by
      exact_mod_cast hpartition
    _ ≤ ∑ _joint ∈ types I n,
          Real.exp (((k : ℝ) * profileMass reference) *
            profileEntropyNats reference) := by
      exact Finset.sum_le_sum fun joint hjoint ↦ hfiber joint hjoint
    _ = ((types I n).card : ℝ) *
          Real.exp (((k : ℝ) * profileMass reference) *
            profileEntropyNats reference) := by
      simp
    _ ≤ ((((n + 1) ^ Fintype.card I : ℕ) : ℝ)) *
          Real.exp (((k : ℝ) * profileMass reference) *
            profileEntropyNats reference) := by
      gcongr
      exact_mod_cast card_types_le I n

/-- Polynomial comparison between a mapped-type word family and the exact proportional reference
type class.

This is the division-free form most useful in finite hashing arguments: the ambient marginal
family is at most a type-selection factor times the structural-zero Stirling loss times the marked
joint type class. -/
theorem card_words_le_typeCount_mul_structuralZeroLoss_mul_referenceTypeClass
    (coordinate : ∀ c, I → A c)
    (reference : I → ℕ) (hrefMass : 0 < profileMass reference)
    (hmaximum : IsMaximumEntropyInMappedFiber coordinate
      (normalizedProfileProbability reference hrefMass))
    {n k : ℕ} (hk : 0 < k) (hn : n = profileMass reference * k)
    (words : Finset (Fin n → I))
    (hwords : ∀ word ∈ words, ∀ c,
      mappedType (coordinate c) (multiplicity word) =
        mappedType (coordinate c) (proportionalCounts reference k)) :
    (words.card : ℝ) ≤
      ((((n + 1) ^ Fintype.card I : ℕ) : ℝ)) *
        structuralZeroMultinomialLoss reference k *
          (Nat.multinomial Finset.univ (proportionalCounts reference k) : ℝ) := by
  have hambient := card_words_le_typeCount_mul_exp_referenceEntropy
    coordinate reference hrefMass hmaximum hk hn words hwords
  have hbase := proportionalEntropyBase_pow_le_structuralZeroLoss_mul_multinomial
    reference k
  have hbaseEq : proportionalEntropyBase reference ^ k =
      Real.exp (((k : ℝ) * profileMass reference) *
        profileEntropyNats reference) := by
    rw [proportionalEntropyBase_eq_exp_profileEntropy reference hrefMass,
      ← Real.exp_nat_mul]
    congr 1
    ring
  rw [hbaseEq] at hbase
  calc
    (words.card : ℝ) ≤
        ((((n + 1) ^ Fintype.card I : ℕ) : ℝ)) *
          Real.exp (((k : ℝ) * profileMass reference) *
            profileEntropyNats reference) := hambient
    _ ≤ ((((n + 1) ^ Fintype.card I : ℕ) : ℝ)) *
          (structuralZeroMultinomialLoss reference k *
            (Nat.multinomial Finset.univ (proportionalCounts reference k) : ℝ)) := by
      exact mul_le_mul_of_nonneg_left hbase (by positivity)
    _ = ((((n + 1) ^ Fintype.card I : ℕ) : ℝ)) *
        structuralZeroMultinomialLoss reference k *
          (Nat.multinomial Finset.univ (proportionalCounts reference k) : ℝ) := by
      ring

end AlgebraicComplexity.WordType
