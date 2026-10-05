import AlgebraicComplexity.Combinatorics.WordType
import AlgebraicComplexity.MatrixMultiplication.InterfaceTensorExactCore
import AlgebraicComplexity.MatrixMultiplication.InterfaceTensorWordSplitCore
import AlgebraicComplexity.Probability.Finite

/-!
# Complete-split data for recursive interface tensors

Recursive laser-method analyses group the base ternary block indices of a tensor power into fixed
binary chunks.  A paper-level `ℓ` constituent uses chunks of length `2^(ℓ-1)`; this module uses the
zero-based parameter `depth = ℓ - 1`, so a chunk has length `2^depth` and its three aggregate
constituent coordinates sum to `2^(depth+1)`.

This file defines only optimizer-independent semantic and exact finite data.  It does not define a
Coppersmith--Winograd tensor, an asymptotic approximation convention, or a paper certificate.
`CompleteSplitProfile` stores integer multiplicities at one finite sample size, while
`CompleteSplitDistribution` stores the corresponding real probability vector.  The normalization
bridge is proved below and will be consumed by later interface-tensor realizations.

Paper references in this module point to the in-repository manuscript *Rectangular Volume and
Parent-Consistent Compatibility in the Laser Method*
(`better_bound/paper.tex`); statement numbers may drift while
that manuscript is revised.
-/

open scoped BigOperators

namespace AlgebraicComplexity

open Tensor

universe u

/-- The flat level-1 index sequence underlying `samples` consecutive depth-`depth` chunks. -/
abbrev FlatSplitSequence (depth samples : ℕ) :=
  Fin (samples * 2 ^ depth) → SplitDigit

/-- Canonically view a flat sequence as `samples` consecutive complete-split chunks.  The
row-major `finProdFinEquiv` order is the paper's position `(t-1) * 2^depth + p`. -/
def chunkSplitSequenceEquiv (depth samples : ℕ) :
    FlatSplitSequence depth samples ≃ (Fin samples → SplitWord depth) :=
  (Equiv.arrowCongr finProdFinEquiv.symm (Equiv.refl SplitDigit)).trans
    (Equiv.curry (Fin samples) (Fin (2 ^ depth)) SplitDigit)

@[simp] theorem chunkSplitSequenceEquiv_apply (depth samples : ℕ)
    (sequence : FlatSplitSequence depth samples)
    (sample : Fin samples) (position : Fin (2 ^ depth)) :
    chunkSplitSequenceEquiv depth samples sequence sample position =
      sequence (finProdFinEquiv (sample, position)) :=
  rfl

@[simp] theorem splitWordWeight_concatSplitWords {depth : ℕ}
    (left right : SplitWord depth) :
    splitWordWeight (concatSplitWords left right) =
      splitWordWeight left + splitWordWeight right := by
  rw [splitWordWeight_succ, splitWordSuccEquiv_concatSplitWords]

/-- A real complete-split distribution supported on chunks with a prescribed digit sum. -/
structure CompleteSplitDistribution (depth total : ℕ) where
  probability : ProbabilityVector (SplitWord depth)
  supported : ∀ word, probability.weight word ≠ 0 → splitWordWeight word = total

namespace CompleteSplitDistribution

variable {depth total : ℕ}

/-- Weight of a complete-split chunk. -/
def weight (β : CompleteSplitDistribution depth total) (word : SplitWord depth) : ℝ :=
  β.probability.weight word

theorem weight_nonneg (β : CompleteSplitDistribution depth total) (word : SplitWord depth) :
    0 ≤ β.weight word :=
  β.probability.nonneg word

theorem sum_weight (β : CompleteSplitDistribution depth total) :
    ∑ word, β.weight word = 1 :=
  β.probability.total

/-- A complete-split distribution concentrated at one admissible chunk. -/
def pointMass (word : SplitWord depth) (hweight : splitWordWeight word = total) :
    CompleteSplitDistribution depth total where
  probability := ProbabilityVector.pointMass word
  supported := by
    intro other hother
    by_cases h : other = word
    · simpa [h] using hweight
    · exact False.elim (hother (by simp [ProbabilityVector.pointMass_weight, h]))

@[simp] theorem pointMass_weight (word : SplitWord depth)
    (hweight : splitWordWeight word = total) (other : SplitWord depth) :
    (CompleteSplitDistribution.pointMass word hweight).weight other =
      if other = word then 1 else 0 :=
  rfl

/-- Complete-split distributions are determined by their underlying probability vectors. -/
@[ext] theorem ext {β γ : CompleteSplitDistribution depth total}
    (h : β.probability = γ.probability) : β = γ := by
  cases β
  cases γ
  cases h
  rfl

/-- The expected digit sum is the prescribed constituent coordinate. -/
theorem expectation_splitWordWeight (β : CompleteSplitDistribution depth total) :
    β.probability.expectation (fun word ↦ (splitWordWeight word : ℝ)) = total := by
  classical
  unfold ProbabilityVector.expectation
  calc
    (∑ word, β.probability.weight word * (splitWordWeight word : ℝ)) =
        ∑ word, β.probability.weight word * (total : ℝ) := by
      apply Finset.sum_congr rfl
      intro word _
      by_cases hzero : β.probability.weight word = 0
      · simp [hzero]
      · rw [β.supported word hzero]
    _ = (∑ word, β.probability.weight word) * (total : ℝ) :=
      (Finset.sum_mul ..).symm
    _ = total := by rw [β.probability.total, one_mul]

/-- Independently concatenate two child complete-split distributions.  This is the elementary
product component from which recursive complete-split mixtures are assembled. -/
def independentConcat {left right : ℕ}
    (β : CompleteSplitDistribution depth left)
    (γ : CompleteSplitDistribution depth right) :
    CompleteSplitDistribution (depth + 1) (left + right) where
  probability :=
    (β.probability.product γ.probability).reindex (splitWordSuccEquiv depth).symm
  supported := by
    intro word hword
    have hproduct :
        (β.probability.product γ.probability).weight
            (splitWordSuccEquiv depth word) ≠ 0 := by
      simpa [ProbabilityVector.reindex_weight] using hword
    change
      β.probability.weight (splitWordSuccEquiv depth word).1 *
          γ.probability.weight (splitWordSuccEquiv depth word).2 ≠ 0 at hproduct
    obtain ⟨hleft, hright⟩ := mul_ne_zero_iff.mp hproduct
    rw [splitWordWeight_succ, β.supported _ hleft, γ.supported _ hright]

@[simp] theorem independentConcat_weight {left right : ℕ}
    (β : CompleteSplitDistribution depth left)
    (γ : CompleteSplitDistribution depth right) (word : SplitWord (depth + 1)) :
    (β.independentConcat γ).weight word =
      β.weight (splitWordSuccEquiv depth word).1 *
        γ.weight (splitWordSuccEquiv depth word).2 := by
  rfl

/-- Independent concatenation specializes to ordinary word concatenation on point masses. -/
theorem independentConcat_pointMass {leftTotal rightTotal : ℕ}
    (left right : SplitWord depth)
    (hleft : splitWordWeight left = leftTotal)
    (hright : splitWordWeight right = rightTotal) :
    (CompleteSplitDistribution.pointMass left hleft).independentConcat
        (CompleteSplitDistribution.pointMass right hright) =
      CompleteSplitDistribution.pointMass (concatSplitWords left right)
        (by simp [hleft, hright]) := by
  apply CompleteSplitDistribution.ext
  apply ProbabilityVector.ext
  funext word
  by_cases hword : word = concatSplitWords left right
  · subst word
    change
      ((CompleteSplitDistribution.pointMass left hleft).independentConcat
          (CompleteSplitDistribution.pointMass right hright)).weight
            (concatSplitWords left right) =
        (CompleteSplitDistribution.pointMass (concatSplitWords left right) _).weight
          (concatSplitWords left right)
    simp
  · have hpair : splitWordSuccEquiv depth word ≠ (left, right) := by
      intro h
      apply hword
      exact (splitWordSuccEquiv depth).injective
        (h.trans (splitWordSuccEquiv_concatSplitWords left right).symm)
    change
      ((CompleteSplitDistribution.pointMass left hleft).independentConcat
          (CompleteSplitDistribution.pointMass right hright)).weight word =
        (CompleteSplitDistribution.pointMass (concatSplitWords left right) _).weight word
    simp only [independentConcat_weight, pointMass_weight]
    rw [if_neg hword]
    rcases not_and_or.mp (mt Prod.ext_iff.mpr hpair) with h | h
    · rw [if_neg h, zero_mul]
    · rw [if_neg h, mul_zero]

/-- A finite mixture of complete-split distributions with the same depth and aggregate
coordinate. -/
def mixture {κ : Type*} [Fintype κ] (mix : ProbabilityVector κ)
    (family : κ → CompleteSplitDistribution depth total) :
    CompleteSplitDistribution depth total where
  probability := mix.mixture fun k ↦ (family k).probability
  supported := by
    intro word hword
    by_contra hweight
    have hzero : ∀ k, (family k).probability.weight word = 0 := by
      intro k
      by_contra hk
      exact hweight ((family k).supported word hk)
    apply hword
    simp [ProbabilityVector.mixture_weight, hzero]

@[simp] theorem mixture_weight {κ : Type*} [Fintype κ] (mix : ProbabilityVector κ)
    (family : κ → CompleteSplitDistribution depth total) (word : SplitWord depth) :
    (CompleteSplitDistribution.mixture mix family).weight word =
      ∑ k, mix.weight k * (family k).weight word :=
  rfl

end CompleteSplitDistribution

/-- One product component in a recursive decomposition of a parent complete-split distribution.
The two child aggregate coordinates may vary between components, but must add to the parent's
coordinate. -/
structure RecursiveSplitComponent (depth parentTotal : ℕ) where
  leftTotal : ℕ
  rightTotal : ℕ
  total_eq : leftTotal + rightTotal = parentTotal
  left : CompleteSplitDistribution depth leftTotal
  right : CompleteSplitDistribution depth rightTotal

namespace RecursiveSplitComponent

variable {depth parentTotal : ℕ}

/-- Concatenate the two independent child distributions and transport their aggregate coordinate
along the component's sum constraint. -/
def toParent (component : RecursiveSplitComponent depth parentTotal) :
    CompleteSplitDistribution (depth + 1) parentTotal :=
  component.total_eq ▸ component.left.independentConcat component.right

end RecursiveSplitComponent

/-- The parent distribution is a finite mixture of products of pairs of child distributions.
This is the semantic equation `β = ∑ₐ α(a) · (βₗ,a × βᵣ,a)` used in recursive interface-tensor
theorems. -/
def IsRecursiveSplitMixture {depth parentTotal : ℕ} {κ : Type*} [Fintype κ]
    (parent : CompleteSplitDistribution (depth + 1) parentTotal)
    (mix : ProbabilityVector κ) (component : κ → RecursiveSplitComponent depth parentTotal) : Prop :=
  CompleteSplitDistribution.mixture mix (fun k ↦ (component k).toParent) = parent

namespace CompleteSplitProfile

variable {depth total samples : ℕ}

/-- The exact complete-split profile empirically induced by a sequence of admissible chunks. -/
noncomputable def ofSequence (sequence : Fin samples → SplitWord depth)
    (hsupported : ∀ t, splitWordWeight (sequence t) = total) :
    CompleteSplitProfile depth total samples where
  counts := WordType.multiplicity sequence
  isType := WordType.multiplicity_mem_types sequence
  supported := by
    classical
    letI : DecidableEq (SplitWord depth) := Classical.decEq _
    intro word hcount
    unfold WordType.multiplicity at hcount
    have hnonempty := Finset.card_ne_zero.mp hcount
    obtain ⟨t, ht⟩ := hnonempty
    have hword : sequence t = word := (Finset.mem_filter.mp ht).2
    simpa [← hword] using hsupported t

/-- Construct an exact complete-split profile directly from an integer count table.  Generated
certificate clients usually establish the displayed sum and support conditions by bounded
computation; this constructor turns those checks into the semantic profile consumed by the
interface and compatibility libraries. -/
def ofCounts (counts : SplitWord depth → ℕ)
    (hsum : ∑ word, counts word = samples)
    (hsupported : ∀ word, counts word ≠ 0 → splitWordWeight word = total) :
    CompleteSplitProfile depth total samples where
  counts := counts
  isType := WordType.mem_types.mpr hsum
  supported := hsupported

@[simp] theorem ofCounts_counts (counts : SplitWord depth → ℕ)
    (hsum : ∑ word, counts word = samples)
    (hsupported : ∀ word, counts word ≠ 0 → splitWordWeight word = total)
    (word : SplitWord depth) :
    (ofCounts counts hsum hsupported).counts word = counts word :=
  rfl

/-- The empirical profile induced directly by a flat level-1 index sequence. -/
noncomputable def ofFlatSequence (sequence : FlatSplitSequence depth samples)
    (hsupported : ∀ t,
      splitWordWeight (chunkSplitSequenceEquiv depth samples sequence t) = total) :
    CompleteSplitProfile depth total samples :=
  ofSequence (chunkSplitSequenceEquiv depth samples sequence) hsupported

@[simp] theorem ofFlatSequence_counts (sequence : FlatSplitSequence depth samples)
    (hsupported : ∀ t,
      splitWordWeight (chunkSplitSequenceEquiv depth samples sequence t) = total) :
    (ofFlatSequence sequence hsupported).counts =
      WordType.multiplicity (chunkSplitSequenceEquiv depth samples sequence) :=
  rfl

@[simp] theorem ofSequence_counts (sequence : Fin samples → SplitWord depth)
    (hsupported : ∀ t, splitWordWeight (sequence t) = total) :
    (ofSequence sequence hsupported).counts = WordType.multiplicity sequence :=
  rfl

/-- A sequence belongs to the type class of its own empirical profile. -/
theorem ofSequence_isConsistent (sequence : Fin samples → SplitWord depth)
    (hsupported : ∀ t, splitWordWeight (sequence t) = total) :
    (ofSequence sequence hsupported).IsConsistent sequence :=
  rfl

/-- The stored chunk counts add up to the profile's sample size. -/
theorem sum_counts (β : CompleteSplitProfile depth total samples) :
    ∑ word, β.counts word = samples :=
  WordType.mem_types.mp β.isType

/-- Add the exact chunk counts of two profiles.  This is the denominator-free form of splitting
one interface term into two consecutive regions with the same constituent coordinate. -/
def add {leftSamples rightSamples : ℕ}
    (left : CompleteSplitProfile depth total leftSamples)
    (right : CompleteSplitProfile depth total rightSamples) :
    CompleteSplitProfile depth total (leftSamples + rightSamples) where
  counts word := left.counts word + right.counts word
  isType := by
    classical
    rw [WordType.mem_types]
    simp_rw [Finset.sum_add_distrib]
    rw [left.sum_counts, right.sum_counts]
  supported := by
    intro word hcount
    by_cases hleft : left.counts word = 0
    · apply right.supported word
      intro hright
      exact hcount (by simp [hleft, hright])
    · exact left.supported word hleft

@[simp] theorem add_counts {leftSamples rightSamples : ℕ}
    (left : CompleteSplitProfile depth total leftSamples)
    (right : CompleteSplitProfile depth total rightSamples) (word : SplitWord depth) :
    (left.add right).counts word = left.counts word + right.counts word :=
  rfl

/-- Concatenating sequences of the two regional types realizes the sum profile exactly. -/
theorem add_isConsistent_append {leftSamples rightSamples : ℕ}
    (left : CompleteSplitProfile depth total leftSamples)
    (right : CompleteSplitProfile depth total rightSamples)
    (leftSequence : Fin leftSamples → SplitWord depth)
    (rightSequence : Fin rightSamples → SplitWord depth)
    (hleft : left.IsConsistent leftSequence)
    (hright : right.IsConsistent rightSequence) :
    (left.add right).IsConsistent (Fin.append leftSequence rightSequence) := by
  unfold IsConsistent at *
  rw [WordType.multiplicity_append, hleft, hright]
  rfl

/-- Type-class form of `add_isConsistent_append`. -/
theorem append_mem_add_typeClass {leftSamples rightSamples : ℕ}
    (left : CompleteSplitProfile depth total leftSamples)
    (right : CompleteSplitProfile depth total rightSamples)
    {leftSequence : Fin leftSamples → SplitWord depth}
    {rightSequence : Fin rightSamples → SplitWord depth}
    (hleft : leftSequence ∈ left.typeClass)
    (hright : rightSequence ∈ right.typeClass) :
    Fin.append leftSequence rightSequence ∈ (left.add right).typeClass := by
  rw [← (left.add right).isConsistent_iff_mem_typeClass]
  exact left.add_isConsistent_append right leftSequence rightSequence
    (left.isConsistent_iff_mem_typeClass leftSequence |>.2 hleft)
    (right.isConsistent_iff_mem_typeClass rightSequence |>.2 hright)

/-- Every exact profile has the expected aggregate digit sum, before normalization. -/
theorem sum_counts_mul_splitWordWeight (β : CompleteSplitProfile depth total samples) :
    ∑ word, β.counts word * splitWordWeight word = samples * total := by
  classical
  calc
    (∑ word, β.counts word * splitWordWeight word) =
        ∑ word, β.counts word * total := by
      apply Finset.sum_congr rfl
      intro word _
      by_cases hzero : β.counts word = 0
      · simp [hzero]
      · rw [β.supported word hzero]
    _ = (∑ word, β.counts word) * total := (Finset.sum_mul ..).symm
    _ = samples * total := by rw [β.sum_counts]

theorem typeClass_nonempty (β : CompleteSplitProfile depth total samples) :
    β.typeClass.Nonempty :=
  WordType.typeClass_nonempty β.counts β.isType

/-- Normalize an exact positive-size profile to a real complete-split distribution. -/
noncomputable def toDistribution (β : CompleteSplitProfile depth total samples)
    (hsamples : 0 < samples) : CompleteSplitDistribution depth total where
  probability :=
    { weight := fun word ↦ (β.counts word : ℝ) / samples
      nonneg := fun word ↦ div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
      total := by
        simp_rw [div_eq_mul_inv]
        rw [← Finset.sum_mul]
        have hsum : ∑ word, β.counts word = samples := WordType.mem_types.mp β.isType
        rw [← Nat.cast_sum, hsum]
        exact mul_inv_cancel₀ (by exact_mod_cast hsamples.ne') }
  supported := by
    intro word hweight
    apply β.supported word
    intro hcount
    apply hweight
    simp [hcount]

@[simp] theorem toDistribution_weight (β : CompleteSplitProfile depth total samples)
    (hsamples : 0 < samples) (word : SplitWord depth) :
    (β.toDistribution hsamples).weight word = (β.counts word : ℝ) / samples :=
  rfl

/-- Normalizing a singleton profile gives the corresponding point-mass distribution. -/
theorem singleton_toDistribution (word : SplitWord depth)
    (hweight : splitWordWeight word = total) :
    (singleton word hweight).toDistribution Nat.zero_lt_one =
      CompleteSplitDistribution.pointMass word hweight := by
  apply CompleteSplitDistribution.ext
  apply ProbabilityVector.ext
  funext other
  by_cases h : other = word <;>
    simp [toDistribution, singleton, CompleteSplitDistribution.pointMass,
      ProbabilityVector.pointMass, h]

/-- Normalize the empirical profile of an admissible finite chunk sequence. -/
noncomputable def empiricalDistribution (sequence : Fin samples → SplitWord depth)
    (hsamples : 0 < samples)
    (hsupported : ∀ t, splitWordWeight (sequence t) = total) :
    CompleteSplitDistribution depth total :=
  (ofSequence sequence hsupported).toDistribution hsamples

@[simp] theorem empiricalDistribution_weight
    (sequence : Fin samples → SplitWord depth) (hsamples : 0 < samples)
    (hsupported : ∀ t, splitWordWeight (sequence t) = total)
    (word : SplitWord depth) :
    (empiricalDistribution sequence hsamples hsupported).weight word =
      (WordType.multiplicity sequence word : ℝ) / samples :=
  rfl

/-- Exact consistency says precisely that the normalized empirical distribution is the profile's
normalization. -/
theorem empiricalDistribution_eq_toDistribution_of_isConsistent
    (β : CompleteSplitProfile depth total samples)
    (sequence : Fin samples → SplitWord depth) (hsamples : 0 < samples)
    (hsupported : ∀ t, splitWordWeight (sequence t) = total)
    (hconsistent : β.IsConsistent sequence) :
    empiricalDistribution sequence hsamples hsupported = β.toDistribution hsamples := by
  apply CompleteSplitDistribution.ext
  apply ProbabilityVector.ext
  funext word
  change (WordType.multiplicity sequence word : ℝ) / samples =
    (β.counts word : ℝ) / samples
  rw [hconsistent]

/-- Approximate consistency in the paper's `L∞` sense. -/
def IsApproximatelyConsistent
    (β : CompleteSplitDistribution depth total)
    (sequence : Fin samples → SplitWord depth) (hsamples : 0 < samples)
    (hsupported : ∀ t, splitWordWeight (sequence t) = total) (ε : ℝ) : Prop :=
  ProbabilityVector.LinftyClose
    (empiricalDistribution sequence hsamples hsupported).probability β.probability ε

end CompleteSplitProfile

namespace LevelConstituentIndex

variable {depth : ℕ}

abbrev x (index : LevelConstituentIndex depth) : ℕ := index.count .X
abbrev y (index : LevelConstituentIndex depth) : ℕ := index.count .Y
abbrev z (index : LevelConstituentIndex depth) : ℕ := index.count .Z

/-- Coordinate relabelling of a recursive constituent address. -/
def permute (σ : Orientation) (index : LevelConstituentIndex depth) :
    LevelConstituentIndex depth where
  count c := index.count (σ.symm c)
  total := by
    classical
    rw [σ.symm.sum_comp index.count, index.total]

@[simp] theorem permute_count (σ : Orientation) (index : LevelConstituentIndex depth) (c : Leg) :
    (index.permute σ).count c = index.count (σ.symm c) :=
  rfl

@[simp] theorem permute_refl (index : LevelConstituentIndex depth) :
    index.permute (Equiv.refl Leg) = index := by
  cases index
  rfl

end LevelConstituentIndex

/-- Semantic metadata of one term in a recursive interface tensor. -/
structure InterfaceTermParameters (depth : ℕ) where
  multiplicity : ℕ
  index : LevelConstituentIndex depth
  split : ∀ c, CompleteSplitDistribution depth (index.count c)

/-- Exact finite certificate for dividing one interface term into two consecutive regions.

Both regions retain the same constituent index as the parent.  Their multiplicities add to the
parent multiplicity, and their complete-split counts add pointwise on every tensor leg.  Zero
multiplicities are allowed here because the published regional-division theorem permits zero
weights; tensor realizations that use nonempty positive powers add positivity hypotheses
separately. -/
structure ExactInterfaceTermBinaryDivision {depth : ℕ}
    (parent : ExactInterfaceTermParameters depth) where
  leftMultiplicity : ℕ
  rightMultiplicity : ℕ
  multiplicity_eq : parent.multiplicity = leftMultiplicity + rightMultiplicity
  leftSplit : ∀ c,
    CompleteSplitProfile depth (parent.index.count c) leftMultiplicity
  rightSplit : ∀ c,
    CompleteSplitProfile depth (parent.index.count c) rightMultiplicity
  split_counts_eq : ∀ c word,
    (parent.split c).counts word =
      (leftSplit c).counts word + (rightSplit c).counts word

namespace ExactInterfaceTermBinaryDivision

variable {depth : ℕ} {parent : ExactInterfaceTermParameters depth}

/-- Exact interface-term metadata of the left region. -/
def leftTerm (division : ExactInterfaceTermBinaryDivision parent) :
    ExactInterfaceTermParameters depth where
  multiplicity := division.leftMultiplicity
  index := parent.index
  split := division.leftSplit

/-- Exact interface-term metadata of the right region. -/
def rightTerm (division : ExactInterfaceTermBinaryDivision parent) :
    ExactInterfaceTermParameters depth where
  multiplicity := division.rightMultiplicity
  index := parent.index
  split := division.rightSplit

@[simp] theorem leftTerm_multiplicity
    (division : ExactInterfaceTermBinaryDivision parent) :
    division.leftTerm.multiplicity = division.leftMultiplicity :=
  rfl

@[simp] theorem rightTerm_multiplicity
    (division : ExactInterfaceTermBinaryDivision parent) :
    division.rightTerm.multiplicity = division.rightMultiplicity :=
  rfl

@[simp] theorem leftTerm_index
    (division : ExactInterfaceTermBinaryDivision parent) :
    division.leftTerm.index = parent.index :=
  rfl

@[simp] theorem rightTerm_index
    (division : ExactInterfaceTermBinaryDivision parent) :
    division.rightTerm.index = parent.index :=
  rfl

@[simp] theorem leftTerm_split
    (division : ExactInterfaceTermBinaryDivision parent) (c : Leg) :
    division.leftTerm.split c = division.leftSplit c :=
  rfl

@[simp] theorem rightTerm_split
    (division : ExactInterfaceTermBinaryDivision parent) (c : Leg) :
    division.rightTerm.split c = division.rightSplit c :=
  rfl

/-- Concatenate regional chunk sequences and transport the resulting length back to the stored
parent multiplicity. -/
def appendSequence (division : ExactInterfaceTermBinaryDivision parent)
    (leftSequence : Fin division.leftMultiplicity → SplitWord depth)
    (rightSequence : Fin division.rightMultiplicity → SplitWord depth) :
    Fin parent.multiplicity → SplitWord depth :=
  Fin.append leftSequence rightSequence ∘ Fin.cast division.multiplicity_eq

/-- Concatenating a left-consistent and a right-consistent sequence realizes the parent profile
exactly.  This is the finite combinatorial content of orientation-free regional division. -/
theorem appendSequence_isConsistent
    (division : ExactInterfaceTermBinaryDivision parent) (c : Leg)
    (leftSequence : Fin division.leftMultiplicity → SplitWord depth)
    (rightSequence : Fin division.rightMultiplicity → SplitWord depth)
    (hleft : (division.leftSplit c).IsConsistent leftSequence)
    (hright : (division.rightSplit c).IsConsistent rightSequence) :
    (parent.split c).IsConsistent
      (division.appendSequence leftSequence rightSequence) := by
  unfold CompleteSplitProfile.IsConsistent at *
  unfold appendSequence
  rw [WordType.multiplicity_cast, WordType.multiplicity_append, hleft, hright]
  funext word
  exact (division.split_counts_eq c word).symm

/-- Type-class form of `appendSequence_isConsistent`. -/
theorem appendSequence_mem_parent_typeClass
    (division : ExactInterfaceTermBinaryDivision parent) (c : Leg)
    {leftSequence : Fin division.leftMultiplicity → SplitWord depth}
    {rightSequence : Fin division.rightMultiplicity → SplitWord depth}
    (hleft : leftSequence ∈ (division.leftSplit c).typeClass)
    (hright : rightSequence ∈ (division.rightSplit c).typeClass) :
    division.appendSequence leftSequence rightSequence ∈ (parent.split c).typeClass := by
  rw [← (parent.split c).isConsistent_iff_mem_typeClass]
  exact division.appendSequence_isConsistent c leftSequence rightSequence
    ((division.leftSplit c).isConsistent_iff_mem_typeClass leftSequence |>.2 hleft)
    ((division.rightSplit c).isConsistent_iff_mem_typeClass rightSequence |>.2 hright)

end ExactInterfaceTermBinaryDivision

/-- Exact interface terms used in a nonempty tensor product have positive multiplicity.  Keeping
the positivity proof with the term avoids repeatedly choosing and reconciling predecessor
exponents when realizing `T^(n_t)`. -/
structure PositiveExactInterfaceTermParameters (depth : ℕ) where
  term : ExactInterfaceTermParameters depth
  multiplicity_pos : 0 < term.multiplicity

namespace PositiveExactInterfaceTermParameters

/-- Predecessor parameter used by the positive-power representation, whose value contains one
more tensor factor than its natural-number index. -/
def predMultiplicity {depth : ℕ} (term : PositiveExactInterfaceTermParameters depth) : ℕ :=
  term.term.multiplicity - 1

theorem multiplicity_eq_pred_add_one {depth : ℕ}
    (term : PositiveExactInterfaceTermParameters depth) :
    term.term.multiplicity = term.predMultiplicity + 1 :=
  (Nat.sub_add_cancel term.multiplicity_pos).symm

end PositiveExactInterfaceTermParameters

namespace ExactInterfaceTermParameters

/-- Normalize every leg profile of an exact positive-multiplicity interface term. -/
noncomputable def toSemantic {depth : ℕ} (term : ExactInterfaceTermParameters depth)
    (hmultiplicity : 0 < term.multiplicity) : InterfaceTermParameters depth where
  multiplicity := term.multiplicity
  index := term.index
  split c := (term.split c).toDistribution hmultiplicity

@[simp] theorem toSemantic_multiplicity {depth : ℕ}
    (term : ExactInterfaceTermParameters depth) (hmultiplicity : 0 < term.multiplicity) :
    (term.toSemantic hmultiplicity).multiplicity = term.multiplicity :=
  rfl

@[simp] theorem toSemantic_index {depth : ℕ}
    (term : ExactInterfaceTermParameters depth) (hmultiplicity : 0 < term.multiplicity) :
    (term.toSemantic hmultiplicity).index = term.index :=
  rfl

/-- Choose one concrete chunk sequence from each leg's nonempty exact type class. -/
noncomputable def chooseSequence {depth : ℕ}
    (term : ExactInterfaceTermParameters depth) (c : Leg) :
    Fin term.multiplicity → SplitWord depth :=
  Classical.choose (term.split c).typeClass_nonempty

theorem chooseSequence_mem_typeClass {depth : ℕ}
    (term : ExactInterfaceTermParameters depth) (c : Leg) :
    term.chooseSequence c ∈ (term.split c).typeClass :=
  Classical.choose_spec (term.split c).typeClass_nonempty

theorem chooseSequence_isConsistent {depth : ℕ}
    (term : ExactInterfaceTermParameters depth) (c : Leg) :
    (term.split c).IsConsistent (term.chooseSequence c) := by
  exact ((term.split c).isConsistent_iff_mem_typeClass
    (term.chooseSequence c)).2 (term.chooseSequence_mem_typeClass c)

/-- Every selected chunk has the aggregate coordinate prescribed by the term index. -/
theorem chooseSequence_supported {depth : ℕ}
    (term : ExactInterfaceTermParameters depth) (c : Leg)
    (sample : Fin term.multiplicity) :
    splitWordWeight (term.chooseSequence c sample) = term.index.count c := by
  apply (term.split c).supported
  rw [← term.chooseSequence_isConsistent c]
  exact WordType.multiplicity_apply_ne_zero (term.chooseSequence c) sample

/-- The concrete chosen sequence has exactly the semantic distribution obtained by normalizing
the stored profile. -/
theorem empiricalDistribution_chooseSequence {depth : ℕ}
    (term : ExactInterfaceTermParameters depth)
    (hmultiplicity : 0 < term.multiplicity) (c : Leg) :
    CompleteSplitProfile.empiricalDistribution (term.chooseSequence c) hmultiplicity
        (term.chooseSequence_supported c) =
      (term.toSemantic hmultiplicity).split c := by
  exact CompleteSplitProfile.empiricalDistribution_eq_toDistribution_of_isConsistent
    (term.split c) (term.chooseSequence c) hmultiplicity
    (term.chooseSequence_supported c) (term.chooseSequence_isConsistent c)

/-- Consequently, each chosen exact leg sequence is approximately consistent with its semantic
distribution with zero error. -/
theorem chooseSequence_isApproximatelyConsistent_zero {depth : ℕ}
    (term : ExactInterfaceTermParameters depth)
    (hmultiplicity : 0 < term.multiplicity) (c : Leg) :
    CompleteSplitProfile.IsApproximatelyConsistent
      ((term.split c).toDistribution hmultiplicity) (term.chooseSequence c) hmultiplicity
      (term.chooseSequence_supported c) 0 := by
  unfold CompleteSplitProfile.IsApproximatelyConsistent
  rw [CompleteSplitProfile.empiricalDistribution_eq_toDistribution_of_isConsistent
    (term.split c) (term.chooseSequence c) hmultiplicity
    (term.chooseSequence_supported c) (term.chooseSequence_isConsistent c)]
  exact ProbabilityVector.linftyClose_refl _ le_rfl

/-- An exact profile is admissible for every nonnegative approximation tolerance. -/
theorem chooseSequence_isApproximatelyConsistent {depth : ℕ}
    (term : ExactInterfaceTermParameters depth)
    (hmultiplicity : 0 < term.multiplicity) (c : Leg)
    {ε : ℝ} (hε : 0 ≤ ε) :
    CompleteSplitProfile.IsApproximatelyConsistent
      ((term.split c).toDistribution hmultiplicity) (term.chooseSequence c) hmultiplicity
      (term.chooseSequence_supported c) ε := by
  unfold CompleteSplitProfile.IsApproximatelyConsistent at *
  exact (term.chooseSequence_isApproximatelyConsistent_zero hmultiplicity c).mono hε

end ExactInterfaceTermParameters

end AlgebraicComplexity
