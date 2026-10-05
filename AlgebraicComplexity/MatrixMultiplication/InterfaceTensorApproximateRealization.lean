/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.InterfaceTensorRealization

/-!
# Tensor realization of approximate complete-split profiles

The recursive constituent theorem does not select one exact parent empirical profile.  It keeps
every parent block word whose empirical complete-split law is close to a prescribed semantic law.
This distinction is essential: independently assembled child interfaces produce many nearby
parent types, and concentration says that almost all of their labels lie in this approximate
selector.

This module supplies the reusable tensor-level selector.  Approximate consistency consists of
two independent conditions:

* every chunk has the constituent's prescribed aggregate coordinate; and
* the normalized multiplicity of every split word is within `epsilon` of the prescribed law.

The first condition is stated explicitly.  Pointwise closeness alone would permit a small number
of chunks from a different constituent and would therefore model a stronger tensor than the
paper uses.  The construction is an ordinary legwise variable zero-out, is invariant under every
sample-position permutation, and contains the corresponding exact selector at every
nonnegative tolerance.
-/

namespace AlgebraicComplexity

open Tensor

universe u v w

namespace CompleteSplitDistribution

variable {depth total samples : ℕ}

/-- A finite chunk sequence has the prescribed aggregate coordinate at every position and its
normalized empirical multiplicities are pointwise within `epsilon` of `beta`.

This definition is proof-free in its second conjunct.  It is equivalent to
`CompleteSplitProfile.IsApproximatelyConsistent` once the stored support proof is supplied, but
is substantially easier to use as a block-selection predicate. -/
def MatchesSequenceApproximately
    (beta : CompleteSplitDistribution depth total)
    (sequence : Fin samples → SplitWord depth) (epsilon : ℝ) : Prop :=
  (∀ sample, splitWordWeight (sequence sample) = total) ∧
    ∀ word,
      |(WordType.multiplicity sequence word : ℝ) / samples - beta.weight word| ≤ epsilon

/-- The proof-free predicate is exactly the existing `L∞` empirical-distribution predicate. -/
theorem matchesSequenceApproximately_iff
    (beta : CompleteSplitDistribution depth total)
    (sequence : Fin samples → SplitWord depth) (hsamples : 0 < samples)
    (epsilon : ℝ) :
    beta.MatchesSequenceApproximately sequence epsilon ↔
      ∃ hsupported : ∀ sample, splitWordWeight (sequence sample) = total,
        CompleteSplitProfile.IsApproximatelyConsistent
          beta sequence hsamples hsupported epsilon := by
  constructor
  · rintro ⟨hsupported, hclose⟩
    refine ⟨hsupported, ?_⟩
    intro word
    change |(CompleteSplitProfile.empiricalDistribution
      sequence hsamples hsupported).weight word - beta.weight word| ≤ epsilon
    rw [CompleteSplitProfile.empiricalDistribution_weight]
    exact hclose word
  · rintro ⟨hsupported, hclose⟩
    refine ⟨hsupported, ?_⟩
    intro word
    have hw := hclose word
    change |(CompleteSplitProfile.empiricalDistribution
      sequence hsamples hsupported).weight word - beta.weight word| ≤ epsilon at hw
    rw [CompleteSplitProfile.empiricalDistribution_weight] at hw
    exact hw

/-- Approximate complete-split consistency is invariant under every permutation of sample
positions. -/
theorem matchesSequenceApproximately_comp_perm_iff
    (beta : CompleteSplitDistribution depth total)
    (sequence : Fin samples → SplitWord depth)
    (sigma : Equiv.Perm (Fin samples)) (epsilon : ℝ) :
    beta.MatchesSequenceApproximately (sequence ∘ sigma) epsilon ↔
      beta.MatchesSequenceApproximately sequence epsilon := by
  have hmultiplicity :
      WordType.multiplicity (sequence ∘ sigma) =
        WordType.multiplicity sequence := by
    simpa using WordType.multiplicity_reindex sigma.symm sequence
  constructor
  · rintro ⟨hsupported, hclose⟩
    refine ⟨?_, ?_⟩
    · intro sample
      simpa [Function.comp_apply] using hsupported (sigma.symm sample)
    · intro word
      simpa [hmultiplicity] using hclose word
  · rintro ⟨hsupported, hclose⟩
    refine ⟨?_, ?_⟩
    · intro sample
      exact hsupported (sigma sample)
    · intro word
      simpa [hmultiplicity] using hclose word

/-- Exact consistency with a positive integral profile implies approximate consistency with its
normalized law at every nonnegative tolerance. -/
theorem matchesSequenceApproximately_of_isConsistent
    (profile : CompleteSplitProfile depth total samples)
    (hsamples : 0 < samples) (sequence : Fin samples → SplitWord depth)
    (hconsistent : profile.IsConsistent sequence)
    {epsilon : ℝ} (hepsilon : 0 ≤ epsilon) :
    (profile.toDistribution hsamples).MatchesSequenceApproximately sequence epsilon := by
  refine ⟨?_, ?_⟩
  · intro sample
    apply profile.supported
    rw [← hconsistent]
    exact WordType.multiplicity_apply_ne_zero sequence sample
  · intro word
    rw [CompleteSplitProfile.toDistribution_weight, hconsistent]
    simpa using hepsilon

end CompleteSplitDistribution

namespace CompleteSplitDistribution

variable {depth total n : ℕ}

/-- Approximate consistency for a recursively represented positive word. -/
def MatchesPositiveWordApproximately
    (beta : CompleteSplitDistribution depth total)
    (word : PositiveWord (SplitWord depth) n) (epsilon : ℝ) : Prop :=
  beta.MatchesSequenceApproximately
    (positiveWordEquiv (SplitWord depth) n word) epsilon

/-- Approximate consistency for a native alphabet equipped with a split-word encoding. -/
def MatchesEncodedPositiveWordApproximately
    {A : Type w} (beta : CompleteSplitDistribution depth total)
    (encode : A → SplitWord depth) (word : PositiveWord A n) (epsilon : ℝ) : Prop :=
  beta.MatchesSequenceApproximately
    (encode ∘ positiveWordEquiv A n word) epsilon

/-- Encoded approximate consistency is invariant under sample-position relabelling. -/
theorem matchesEncodedPositiveWordApproximately_positionEquiv_iff
    {A : Type w} (beta : CompleteSplitDistribution depth total)
    (encode : A → SplitWord depth) (word : PositiveWord A n)
    (sigma : Equiv.Perm (Fin (n + 1))) (epsilon : ℝ) :
    beta.MatchesEncodedPositiveWordApproximately encode
        (positiveWordPositionEquiv A n sigma word) epsilon ↔
      beta.MatchesEncodedPositiveWordApproximately encode word epsilon := by
  unfold MatchesEncodedPositiveWordApproximately
  rw [positiveWordEquiv_position_apply]
  simpa only [Function.comp_assoc] using
    beta.matchesSequenceApproximately_comp_perm_iff
      (encode ∘ positiveWordEquiv A n word) sigma epsilon

end CompleteSplitDistribution

private theorem positivePowerProfile_counts_for_approximation_aux {depth : ℕ}
    (index : LevelConstituentIndex depth) (multiplicity n : ℕ)
    (split : ∀ c, CompleteSplitProfile depth (index.count c) multiplicity)
    (hmultiplicity : multiplicity = n + 1) (c : Leg) :
    ((ExactInterfaceTermParameters.mk multiplicity index split).positivePowerProfile
      hmultiplicity c).counts = (split c).counts := by
  subst hmultiplicity
  rfl

private theorem positivePowerProfile_counts_for_approximation {depth n : ℕ}
    (term : ExactInterfaceTermParameters depth)
    (hmultiplicity : term.multiplicity = n + 1) (c : Leg) :
    (term.positivePowerProfile hmultiplicity c).counts = (term.split c).counts :=
  positivePowerProfile_counts_for_approximation_aux
    term.index term.multiplicity n term.split hmultiplicity c

section Encoded

variable {K : Type u} [CommSemiring K]
variable {depth n : ℕ}
variable {A : Leg → Type w} [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]
variable {V : ∀ c, A c → Type (max u v)}
variable [∀ c a, AddCommMonoid (V c a)] [∀ c a, Module K (V c a)]

/-- Select the approximately prescribed complete-split law independently on each leg.  The
aggregate-coordinate condition is part of the block predicate, so this is the approximate
interface term of one fixed constituent rather than a neighborhood mixing constituents. -/
noncomputable def Tensor.PartitionedTensor.selectEncodedApproximateInterfaceTerm
    (P : PartitionedTensor (K := K) (A := A) V)
    (encode : ∀ c, A c → SplitWord depth)
    (term : InterfaceTermParameters depth)
    (_hmultiplicity : term.multiplicity = n + 1) (epsilon : ℝ) :
    PartitionedTensor
      (K := K) (A := fun c ↦ PositiveWord (A c) n)
      (PositivePowerBlockSpace K V n) := by
  classical
  exact (P.positivePower n).select fun c word ↦
    (term.split c).MatchesEncodedPositiveWordApproximately
      (encode c) word epsilon

@[simp] theorem Tensor.PartitionedTensor.mem_selectEncodedApproximateInterfaceTerm_support
    (P : PartitionedTensor (K := K) (A := A) V)
    (encode : ∀ c, A c → SplitWord depth)
    (term : InterfaceTermParameters depth)
    (hmultiplicity : term.multiplicity = n + 1) (epsilon : ℝ)
    (address : BlockAddress (fun c ↦ PositiveWord (A c) n)) :
    address ∈ (P.selectEncodedApproximateInterfaceTerm
        encode term hmultiplicity epsilon).support ↔
      address ∈ (P.positivePower n).support ∧
        ∀ c, (term.split c).MatchesSequenceApproximately
          (encode c ∘ positiveWordEquiv (A c) n (address c)) epsilon := by
  classical
  simpa only [Tensor.PartitionedTensor.selectEncodedApproximateInterfaceTerm,
    CompleteSplitDistribution.MatchesEncodedPositiveWordApproximately] using
    (Tensor.PartitionedTensor.mem_select_support (P.positivePower n)
      (fun c word ↦ (term.split c).MatchesEncodedPositiveWordApproximately
        (encode c) word epsilon) address)

/-- Approximate interface selection is an ordinary variable restriction of the source power. -/
theorem Tensor.Restricts.power_selectEncodedApproximateInterfaceTerm
    (P : PartitionedTensor (K := K) (A := A) V)
    (encode : ∀ c, A c → SplitWord depth)
    (term : InterfaceTermParameters depth)
    (hmultiplicity : term.multiplicity = n + 1) (epsilon : ℝ) :
    Restricts (Tensor.power P.realize (n + 1))
      (P.selectEncodedApproximateInterfaceTerm
        encode term hmultiplicity epsilon).realize :=
  (Tensor.Restricts.power_partitionedPositivePower P n).trans <| by
    classical
    exact Tensor.Restricts.partitionedSelect (P.positivePower n)
      (fun c word ↦
        (term.split c).MatchesEncodedPositiveWordApproximately
          (encode c) word epsilon)

/-- Every sample-position permutation preserves the approximate selector. -/
noncomputable def Tensor.PartitionedTensor.selectEncodedApproximateInterfaceTermPositionRelabeling
    (P : PartitionedTensor (K := K) (A := A) V)
    (encode : ∀ c, A c → SplitWord depth)
    (term : InterfaceTermParameters depth)
    (hmultiplicity : term.multiplicity = n + 1) (epsilon : ℝ)
    (sigma : Equiv.Perm (Fin (n + 1))) :
    (P.selectEncodedApproximateInterfaceTerm
      encode term hmultiplicity epsilon).StructureRelabeling := by
  classical
  unfold Tensor.PartitionedTensor.selectEncodedApproximateInterfaceTerm
  let r := Tensor.PartitionedTensor.StructureRelabeling.positivePowerPositionRelabeling
    P n sigma
  refine r.select
    (fun c word ↦
      (term.split c).MatchesEncodedPositiveWordApproximately
        (encode c) word epsilon) ?_
  intro c word
  rw [show r.partEquiv c = positiveWordPositionEquiv (A c) n sigma by
    dsimp [r]
    exact Tensor.PartitionedTensor.StructureRelabeling.positivePowerPositionRelabeling_partEquiv
      P n sigma c]
  have h :=
    (term.split c).matchesEncodedPositiveWordApproximately_positionEquiv_iff
      (encode c) ((positiveWordPositionEquiv (A c) n sigma).symm word)
        sigma epsilon
  simpa using h.symm

/-- The exact selector is contained in the approximate selector at every nonnegative tolerance.
This theorem is deliberately a support inclusion, not an identification of the two tensors. -/
theorem Tensor.PartitionedTensor.selectEncodedExactInterfaceTerm_support_subset_approximate
    (P : PartitionedTensor (K := K) (A := A) V)
    (encode : ∀ c, A c → SplitWord depth)
    (term : ExactInterfaceTermParameters depth)
    (hmultiplicity : term.multiplicity = n + 1)
    {epsilon : ℝ} (hepsilon : 0 ≤ epsilon) :
    (P.selectEncodedExactInterfaceTerm encode term hmultiplicity).support ⊆
      (P.selectEncodedApproximateInterfaceTerm encode
        (term.toSemantic (hmultiplicity.symm ▸ Nat.zero_lt_succ n))
        (by simpa using hmultiplicity) epsilon).support := by
  classical
  intro address haddress
  have hdata := (P.mem_selectEncodedCompleteSplitProfiles_support
    encode term.index (fun c ↦ term.positivePowerProfile hmultiplicity c) address).1 haddress
  apply (P.mem_selectEncodedApproximateInterfaceTerm_support
    encode (term.toSemantic (hmultiplicity.symm ▸ Nat.zero_lt_succ n))
      (by simpa using hmultiplicity) epsilon address).2
  refine ⟨hdata.1, ?_⟩
  intro c
  have hconsistent :
      (term.positivePowerProfile hmultiplicity c).IsConsistent
        (encode c ∘ positiveWordEquiv (A c) n (address c)) := hdata.2 c
  have hpositive : 0 < term.multiplicity :=
    hmultiplicity.symm ▸ Nat.zero_lt_succ n
  have hdistribution :
      (term.positivePowerProfile hmultiplicity c).toDistribution (Nat.zero_lt_succ n) =
        (term.split c).toDistribution hpositive := by
    apply CompleteSplitDistribution.ext
    apply ProbabilityVector.ext
    funext word
    change ((term.positivePowerProfile hmultiplicity c).toDistribution
        (Nat.zero_lt_succ n)).weight word =
      ((term.split c).toDistribution hpositive).weight word
    rw [CompleteSplitProfile.toDistribution_weight,
      CompleteSplitProfile.toDistribution_weight,
      positivePowerProfile_counts_for_approximation]
    have hdenominator : (term.multiplicity : ℝ) = (n + 1 : ℝ) := by
      exact_mod_cast hmultiplicity
    rw [hdenominator]
    norm_num
  change ((term.split c).toDistribution hpositive).MatchesSequenceApproximately
    (encode c ∘ positiveWordEquiv (A c) n (address c)) epsilon
  rw [← hdistribution]
  exact CompleteSplitDistribution.matchesSequenceApproximately_of_isConsistent
    (term.positivePowerProfile hmultiplicity c) (Nat.zero_lt_succ n)
    (encode c ∘ positiveWordEquiv (A c) n (address c)) hconsistent hepsilon

end Encoded

end AlgebraicComplexity
