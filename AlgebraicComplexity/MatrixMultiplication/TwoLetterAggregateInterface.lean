/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.PartitionedTypeAssembly
import AlgebraicComplexity.MatrixMultiplication.RationalTypedLeafCore
import AlgebraicComplexity.Probability.TwoLetter
import AlgebraicComplexity.Tensor.TypeExtraction

/-!
# Aggregate interfaces for two-letter tensor products

A two-letter coupling need not preserve the reference type on each letter separately.  For the
external product of the two selected constituents, it is enough that the two exact multiplicity
tables add to twice the reference table.  Indeed, concatenating the row and column words then has
the same full support-address type as concatenating two copies of the reference word.  A single
permutation of sample positions therefore identifies the corresponding three-legged tensor
constituents.

This module formalizes that observation independently of any named tensor, entropy optimization,
or numerical certificate.  It includes:

* exact integral and empirical-probability formulations of the aggregate-interface condition;
* an exact rational-profile adapter for typed-leaf certificates;
* actual `Tensor.Isomorphic` and `Tensor.Restricts` theorems; and
* explicit corollaries allowing unequal row and column marginals.

The condition counts *full support addresses*.  Consequently the position permutation is shared
by all three tensor legs; no independent legwise relabeling is being assumed.
-/

open scoped BigOperators

namespace AlgebraicComplexity

open Tensor

namespace WordType

/-- Exact multiplicity table of a nonempty recursively represented word. -/
noncomputable def positiveMultiplicity {I : Type*} [Fintype I]
    {r : ℕ} (word : PositiveWord I r) : I → ℕ :=
  multiplicity (positiveWordEquiv I r word)

/-- The row and column words have the same aggregate interface as two copies of `base`.

All three words have length `r + 1`, so this is the denominator-free form of
`(row + column) / 2 = base`. -/
def HasAggregateInterface {I : Type*} [Fintype I]
    {r : ℕ} (row column base : PositiveWord I r) : Prop :=
  ∀ i, positiveMultiplicity row i + positiveMultiplicity column i =
    positiveMultiplicity base i + positiveMultiplicity base i

/-- Multiplicity tables add under concatenation of nonempty recursive words. -/
theorem positiveMultiplicity_append {I : Type*} [Fintype I]
    {n m : ℕ} (left : PositiveWord I n) (right : PositiveWord I m) :
    positiveMultiplicity (positiveWordAppend left m right) =
      positiveMultiplicity left + positiveMultiplicity right := by
  unfold positiveMultiplicity
  rw [positiveWordEquiv_append, multiplicity_cast, multiplicity_append]

/-- Multiplicity table of a constant nonempty recursive word. -/
theorem positiveMultiplicity_const {I : Type*} [Fintype I] [DecidableEq I]
    (i : I) (r : ℕ) :
    positiveMultiplicity (positiveWordConst i r) =
      fun j ↦ if j = i then r + 1 else 0 :=
  multiplicity_positiveWordConst i r

/-- The two-letter positive word with the displayed first and second letters. -/
def positiveWordPair {I : Type*} (left right : I) : PositiveWord I 1 :=
  (left, right)

/-- Exact multiplicity table of a two-letter word. -/
theorem positiveMultiplicity_pair {I : Type*} [Fintype I] [DecidableEq I]
    (left right : I) :
    positiveMultiplicity (positiveWordPair left right) =
      fun i ↦ (if i = left then 1 else 0) + (if i = right then 1 else 0) := by
  let leftWord : PositiveWord I 0 := positiveWordConst left 0
  let rightWord : PositiveWord I 0 := positiveWordConst right 0
  calc
    positiveMultiplicity (positiveWordPair left right) =
        positiveMultiplicity leftWord + positiveMultiplicity rightWord := by
      rw [show positiveWordPair left right =
        positiveWordAppend leftWord 0 rightWord by rfl,
        positiveMultiplicity_append]
    _ = _ := by
      rw [show leftWord = positiveWordConst left 0 by rfl,
        show rightWord = positiveWordConst right 0 by rfl,
        positiveMultiplicity_const, positiveMultiplicity_const]
      funext i
      rfl

/-- The aggregate-interface condition is exactly the equality of the two concatenated word
types used by tensor assembly. -/
theorem HasAggregateInterface.append_eq
    {I : Type*} [Fintype I] {r : ℕ}
    {row column base : PositiveWord I r}
    (h : HasAggregateInterface row column base) :
    positiveMultiplicity (positiveWordAppend row r column) =
      positiveMultiplicity (positiveWordAppend base r base) := by
  rw [positiveMultiplicity_append, positiveMultiplicity_append]
  funext i
  exact h i

/-- Aggregate preservation together with the fact that at least one regional type genuinely
differs from the reference type. -/
def HasUnequalAggregateInterface {I : Type*} [Fintype I]
    {r : ℕ} (row column base : PositiveWord I r) : Prop :=
  HasAggregateInterface row column base ∧
    (positiveMultiplicity row ≠ positiveMultiplicity base ∨
      positiveMultiplicity column ≠ positiveMultiplicity base)

/-- Exact rational-profile boundary: the two regional count tables need only add to twice the
proportional reference profile. -/
theorem hasAggregateInterface_of_proportionalProfile
    {I : Type*} [Fintype I] {r k : ℕ}
    (profile : PositiveIntegralProfile I)
    (row column base : PositiveWord I r)
    (hbase : base ∈ Tensor.positiveTypeClass I r
      (proportionalCounts profile.count k))
    (haggregate : ∀ i,
      positiveMultiplicity row i + positiveMultiplicity column i =
        2 * proportionalCounts profile.count k i) :
    HasAggregateInterface row column base := by
  intro i
  have hb := congrFun (Tensor.mem_positiveTypeClass.mp hbase) i
  change positiveMultiplicity row i + positiveMultiplicity column i =
    multiplicity (positiveWordEquiv I r base) i +
      multiplicity (positiveWordEquiv I r base) i
  rw [hb]
  simpa [two_mul] using haggregate i

/-- Empirical probability law of a nonempty recursive word. -/
noncomputable def positiveEmpiricalDistribution {I : Type*} [Fintype I]
    {r : ℕ} (word : PositiveWord I r) : ProbabilityVector I where
  weight i := (positiveMultiplicity word i : ℝ) / (r + 1 : ℕ)
  nonneg i := div_nonneg (by positivity) (by positivity)
  total := by
    rw [← Finset.sum_div]
    have hsum := sum_multiplicity (positiveWordEquiv I r word)
    unfold positiveMultiplicity
    rw [← Nat.cast_sum, hsum]
    exact div_self (by exact_mod_cast Nat.succ_ne_zero r)

@[simp] theorem positiveEmpiricalDistribution_weight
    {I : Type*} [Fintype I] {r : ℕ} (word : PositiveWord I r) (i : I) :
    (positiveEmpiricalDistribution word).weight i =
      (positiveMultiplicity word i : ℝ) / (r + 1 : ℕ) :=
  rfl

end WordType

namespace ProbabilityVector

/-- Pointwise probability form of aggregate-interface preservation.  Individual row and column
marginals need not equal `base`; only their average must equal it. -/
def HasAggregateInterface {I : Type*} [Fintype I]
    (row column base : ProbabilityVector I) : Prop :=
  ∀ i, row.weight i + column.weight i = 2 * base.weight i

/-- The equal-marginal case is a special case of aggregate-interface preservation. -/
theorem hasAggregateInterface_self {I : Type*} [Fintype I]
    (base : ProbabilityVector I) :
    HasAggregateInterface base base base := by
  intro i
  ring

/-- Aggregate-interface preservation is symmetric in the regional marginals. -/
theorem HasAggregateInterface.symm {I : Type*} [Fintype I]
    {row column base : ProbabilityVector I}
    (h : HasAggregateInterface row column base) :
    HasAggregateInterface column row base := by
  intro i
  rw [add_comm]
  exact h i

/-- Probability-level aggregate preservation with at least one genuinely unequal marginal. -/
def HasUnequalAggregateInterface {I : Type*} [Fintype I]
    (row column base : ProbabilityVector I) : Prop :=
  HasAggregateInterface row column base ∧ (row ≠ base ∨ column ≠ base)

/-- Exact integral aggregate interfaces imply the corresponding pointwise probability identity. -/
theorem positiveEmpiricalDistribution_hasAggregateInterface
    {I : Type*} [Fintype I] {r : ℕ}
    {row column base : Tensor.PositiveWord I r}
    (h : WordType.HasAggregateInterface row column base) :
    HasAggregateInterface
      (WordType.positiveEmpiricalDistribution row)
      (WordType.positiveEmpiricalDistribution column)
      (WordType.positiveEmpiricalDistribution base) := by
  intro i
  simp only [WordType.positiveEmpiricalDistribution_weight]
  rw [two_mul, ← add_div, ← add_div]
  congr 1
  exact_mod_cast h i

/-- At a fixed word length, equality of empirical laws implies equality of exact multiplicity
tables. -/
theorem positiveMultiplicity_eq_of_positiveEmpiricalDistribution_eq
    {I : Type*} [Fintype I] {r : ℕ} {left right : Tensor.PositiveWord I r}
    (h : WordType.positiveEmpiricalDistribution left =
      WordType.positiveEmpiricalDistribution right) :
    WordType.positiveMultiplicity left = WordType.positiveMultiplicity right := by
  funext i
  have hi := congrArg (fun p : ProbabilityVector I ↦ p.weight i) h
  simp only [WordType.positiveEmpiricalDistribution_weight] at hi
  have hdenom : (r + 1 : ℝ) ≠ 0 := by positivity
  have hcast : (WordType.positiveMultiplicity left i : ℝ) =
      WordType.positiveMultiplicity right i := by
    field_simp [hdenom] at hi
    exact hi
  exact_mod_cast hcast

/-- Exact unequal aggregate interfaces remain unequal after normalization to empirical laws. -/
theorem positiveEmpiricalDistribution_hasUnequalAggregateInterface
    {I : Type*} [Fintype I] {r : ℕ}
    {row column base : Tensor.PositiveWord I r}
    (h : WordType.HasUnequalAggregateInterface row column base) :
    HasUnequalAggregateInterface
      (WordType.positiveEmpiricalDistribution row)
      (WordType.positiveEmpiricalDistribution column)
      (WordType.positiveEmpiricalDistribution base) := by
  refine ⟨positiveEmpiricalDistribution_hasAggregateInterface h.1, ?_⟩
  rcases h.2 with hrow | hcolumn
  · exact Or.inl fun heq ↦ hrow
      (positiveMultiplicity_eq_of_positiveEmpiricalDistribution_eq heq)
  · exact Or.inr fun heq ↦ hcolumn
      (positiveMultiplicity_eq_of_positiveEmpiricalDistribution_eq heq)

/-- A coupling inherits the aggregate-interface identity from its specified marginals. -/
theorem IsCoupling.aggregateInterface_marginals
    {I : Type*} [Fintype I] [DecidableEq I]
    {joint : ProbabilityVector (I × I)} {row column base : ProbabilityVector I}
    (hcoupling : joint.IsCoupling row column)
    (haggregate : HasAggregateInterface row column base) :
    HasAggregateInterface
      (joint.pushforward Prod.fst) (joint.pushforward Prod.snd) base := by
  rw [hcoupling.1, hcoupling.2]
  exact haggregate

end ProbabilityVector

universe u v w

variable {K : Type u} [CommSemiring K]
variable {A : Leg → Type w} [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]
variable {V : ∀ c, A c → Type (max u v)}
variable [∀ c a, AddCommMonoid (V c a)] [∀ c a, Module K (V c a)]

namespace Tensor.Isomorphic

/-- If two regional support-address words have twice the reference type in aggregate, their
external product is isomorphic to the external square of the reference interface tensor.

The isomorphism first reassociates each external product to one concatenated positive-power
constituent, permutes sample positions using equality of full-address multiplicities, and then
undoes the reference reassociation. -/
theorem external_positiveSupportWordTensor_aggregateInterface
    (P : PartitionedTensor (K := K) (A := A) V)
    (r : ℕ) (row column base : PositiveWord P.support r)
    (haggregate : WordType.HasAggregateInterface row column base) :
    Isomorphic
      (Tensor.external (P.positiveSupportWordTensor r row)
        (P.positiveSupportWordTensor r column))
      (Tensor.external (P.positiveSupportWordTensor r base)
        (P.positiveSupportWordTensor r base)) := by
  let rowColumn := positiveWordAppend row r column
  let baseBase := positiveWordAppend base r base
  have htype :
      WordType.multiplicity (positiveWordEquiv P.support (r + r + 1) rowColumn) =
        WordType.multiplicity (positiveWordEquiv P.support (r + r + 1) baseBase) := by
    exact haggregate.append_eq
  have hmiddle := positivePower_constituent_of_same_type
    P (r + r + 1) rowColumn baseBase htype
  have hleft : Isomorphic
      (Tensor.external (P.positiveSupportWordTensor r row)
        (P.positiveSupportWordTensor r column))
      ((P.positivePower (r + r + 1)).constituent
        (positiveSupportWordBlockAddress P.support (r + r + 1) rowColumn)) := by
    dsimp only [rowColumn]
    rw [positiveSupportWordBlockAddress_append]
    refine ⟨fun c ↦ positivePowerBlockAppendEquiv (K := K) (V := V) c
        (positiveSupportWordBlockAddress P.support r row c) r
        (positiveSupportWordBlockAddress P.support r column c), ?_⟩
    exact P.map_positivePowerBlockAppendEquiv_external_positiveSupportWordTensors row column
  have hright : Isomorphic
      (Tensor.external (P.positiveSupportWordTensor r base)
        (P.positiveSupportWordTensor r base))
      ((P.positivePower (r + r + 1)).constituent
        (positiveSupportWordBlockAddress P.support (r + r + 1) baseBase)) := by
    dsimp only [baseBase]
    rw [positiveSupportWordBlockAddress_append]
    refine ⟨fun c ↦ positivePowerBlockAppendEquiv (K := K) (V := V) c
        (positiveSupportWordBlockAddress P.support r base c) r
        (positiveSupportWordBlockAddress P.support r base c), ?_⟩
    exact P.map_positivePowerBlockAppendEquiv_external_positiveSupportWordTensors base base
  exact hleft.trans hmiddle |>.trans hright.symm

/-- Unequal regional marginals are allowed: only their aggregate support-address multiplicities
must agree with two copies of the reference interface. -/
theorem external_positiveSupportWordTensor_unequalAggregateInterface
    (P : PartitionedTensor (K := K) (A := A) V)
    (r : ℕ) (row column base : PositiveWord P.support r)
    (haggregate : WordType.HasUnequalAggregateInterface row column base) :
    Isomorphic
      (Tensor.external (P.positiveSupportWordTensor r row)
        (P.positiveSupportWordTensor r column))
      (Tensor.external (P.positiveSupportWordTensor r base)
        (P.positiveSupportWordTensor r base)) :=
  external_positiveSupportWordTensor_aggregateInterface P r row column base haggregate.1

/-- Exact rational-profile form of aggregate-interface preservation. -/
theorem external_positiveSupportWordTensor_proportionalProfileAggregateInterface
    (P : PartitionedTensor (K := K) (A := A) V)
    {r k : ℕ} (profile : PositiveIntegralProfile P.support)
    (row column base : PositiveWord P.support r)
    (hbase : base ∈ positiveTypeClass P.support r
      (WordType.proportionalCounts profile.count k))
    (haggregate : ∀ i,
      WordType.positiveMultiplicity row i +
          WordType.positiveMultiplicity column i =
        2 * WordType.proportionalCounts profile.count k i) :
    Isomorphic
      (Tensor.external (P.positiveSupportWordTensor r row)
        (P.positiveSupportWordTensor r column))
      (Tensor.external (P.positiveSupportWordTensor r base)
        (P.positiveSupportWordTensor r base)) :=
  external_positiveSupportWordTensor_aggregateInterface P r row column base
    (WordType.hasAggregateInterface_of_proportionalProfile
      profile row column base hbase haggregate)

end Tensor.Isomorphic

namespace Tensor.Restricts

/-- Restriction form of aggregate-interface preservation. -/
theorem external_positiveSupportWordTensor_aggregateInterface
    (P : PartitionedTensor (K := K) (A := A) V)
    (r : ℕ) (row column base : PositiveWord P.support r)
    (haggregate : WordType.HasAggregateInterface row column base) :
    Restricts
      (Tensor.external (P.positiveSupportWordTensor r row)
        (P.positiveSupportWordTensor r column))
      (Tensor.external (P.positiveSupportWordTensor r base)
        (P.positiveSupportWordTensor r base)) :=
  (Isomorphic.external_positiveSupportWordTensor_aggregateInterface
    P r row column base haggregate).restricts

/-- Restriction corollary explicitly recording that at least one regional marginal differs from
the reference. -/
theorem external_positiveSupportWordTensor_unequalAggregateInterface
    (P : PartitionedTensor (K := K) (A := A) V)
    (r : ℕ) (row column base : PositiveWord P.support r)
    (haggregate : WordType.HasUnequalAggregateInterface row column base) :
    Restricts
      (Tensor.external (P.positiveSupportWordTensor r row)
        (P.positiveSupportWordTensor r column))
      (Tensor.external (P.positiveSupportWordTensor r base)
        (P.positiveSupportWordTensor r base)) :=
  (Isomorphic.external_positiveSupportWordTensor_unequalAggregateInterface
    P r row column base haggregate).restricts

/-- Restriction form at the exact rational-profile certificate boundary. -/
theorem external_positiveSupportWordTensor_proportionalProfileAggregateInterface
    (P : PartitionedTensor (K := K) (A := A) V)
    {r k : ℕ} (profile : PositiveIntegralProfile P.support)
    (row column base : PositiveWord P.support r)
    (hbase : base ∈ positiveTypeClass P.support r
      (WordType.proportionalCounts profile.count k))
    (haggregate : ∀ i,
      WordType.positiveMultiplicity row i +
          WordType.positiveMultiplicity column i =
        2 * WordType.proportionalCounts profile.count k i) :
    Restricts
      (Tensor.external (P.positiveSupportWordTensor r row)
        (P.positiveSupportWordTensor r column))
      (Tensor.external (P.positiveSupportWordTensor r base)
        (P.positiveSupportWordTensor r base)) :=
  (Isomorphic.external_positiveSupportWordTensor_proportionalProfileAggregateInterface
    P profile row column base hbase haggregate).restricts

end Tensor.Restricts

end AlgebraicComplexity
