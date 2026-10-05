/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.InterfaceTensorSelectionPredicateCore
import AlgebraicComplexity.Tensor.PartitionedPowerConstituent

/-!
# Finite exact-profile selection for interface tensors

This module selects prescribed complete-split profiles from a positive partitioned power and
characterizes the resulting support.  It deliberately stops before sample-position relabelings,
source-power restrictions, and heterogeneous product assembly.  Those semantic constructions
remain in `InterfaceTensorRealization`, which re-exports this core.
-/

namespace AlgebraicComplexity

open Tensor

universe u v w

section Native

variable {K : Type u} [CommSemiring K]
variable {depth n : ℕ}
variable {V : ∀ _c, SplitWord depth → Type (max u v)}
variable [∀ c a, AddCommMonoid (V c a)] [∀ c a, Module K (V c a)]

/-- Select the block-label sequences prescribed by one exact profile on each tensor leg. -/
noncomputable def Tensor.PartitionedTensor.selectCompleteSplitProfiles
    (P : PartitionedTensor (K := K) (A := fun _ : Leg ↦ SplitWord depth) V)
    (index : LevelConstituentIndex depth)
    (profile : ∀ c, CompleteSplitProfile depth (index.count c) (n + 1)) :
    PartitionedTensor
      (K := K) (A := fun _c ↦ PositiveWord (SplitWord depth) n)
      (PositivePowerBlockSpace K V n) := by
  classical
  exact (P.positivePower n).select fun c word ↦ (profile c).MatchesPositiveWord word

@[simp] theorem Tensor.PartitionedTensor.mem_selectCompleteSplitProfiles_support
    (P : PartitionedTensor (K := K) (A := fun _ : Leg ↦ SplitWord depth) V)
    (index : LevelConstituentIndex depth)
    (profile : ∀ c, CompleteSplitProfile depth (index.count c) (n + 1))
    (address : BlockAddress (fun _c ↦ PositiveWord (SplitWord depth) n)) :
    address ∈ (P.selectCompleteSplitProfiles index profile).support ↔
      address ∈ (P.positivePower n).support ∧
        ∀ c, (profile c).IsConsistent
          (positiveWordEquiv (SplitWord depth) n (address c)) := by
  classical
  simp [Tensor.PartitionedTensor.selectCompleteSplitProfiles,
    CompleteSplitProfile.matchesPositiveWord_iff_isConsistent]

/-- Select one exact native-alphabet interface term from its parameter record. -/
noncomputable def Tensor.PartitionedTensor.selectExactInterfaceTerm
    (P : PartitionedTensor (K := K) (A := fun _ : Leg ↦ SplitWord depth) V)
    (term : ExactInterfaceTermParameters depth)
    (hmultiplicity : term.multiplicity = n + 1) :
    PartitionedTensor
      (K := K) (A := fun _c ↦ PositiveWord (SplitWord depth) n)
      (PositivePowerBlockSpace K V n) :=
  P.selectCompleteSplitProfiles term.index
    (fun c ↦ term.positivePowerProfile hmultiplicity c)

end Native

section Encoded

variable {K : Type u} [CommSemiring K]
variable {depth n : ℕ}
variable {A : Leg → Type w} [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]
variable {V : ∀ c, A c → Type (max u v)}
variable [∀ c a, AddCommMonoid (V c a)] [∀ c a, Module K (V c a)]

/-- Exact complete-split selection for a native block alphabet with a legwise split-word
encoding. -/
noncomputable def Tensor.PartitionedTensor.selectEncodedCompleteSplitProfiles
    (P : PartitionedTensor (K := K) (A := A) V)
    (encode : ∀ c, A c → SplitWord depth)
    (index : LevelConstituentIndex depth)
    (profile : ∀ c, CompleteSplitProfile depth (index.count c) (n + 1)) :
    PartitionedTensor
      (K := K) (A := fun c ↦ PositiveWord (A c) n)
      (PositivePowerBlockSpace K V n) := by
  classical
  exact (P.positivePower n).select fun c word ↦
    (profile c).MatchesEncodedPositiveWord (encode c) word

@[simp] theorem Tensor.PartitionedTensor.mem_selectEncodedCompleteSplitProfiles_support
    (P : PartitionedTensor (K := K) (A := A) V)
    (encode : ∀ c, A c → SplitWord depth)
    (index : LevelConstituentIndex depth)
    (profile : ∀ c, CompleteSplitProfile depth (index.count c) (n + 1))
    (address : BlockAddress (fun c ↦ PositiveWord (A c) n)) :
    address ∈ (P.selectEncodedCompleteSplitProfiles encode index profile).support ↔
      address ∈ (P.positivePower n).support ∧
        ∀ c, (profile c).IsConsistent
          (encode c ∘ positiveWordEquiv (A c) n (address c)) := by
  classical
  simp [Tensor.PartitionedTensor.selectEncodedCompleteSplitProfiles,
    CompleteSplitProfile.matchesEncodedPositiveWord_iff]

/-- Encoded exact selection directly from an interface-term record. -/
noncomputable def Tensor.PartitionedTensor.selectEncodedExactInterfaceTerm
    (P : PartitionedTensor (K := K) (A := A) V)
    (encode : ∀ c, A c → SplitWord depth)
    (term : ExactInterfaceTermParameters depth)
    (hmultiplicity : term.multiplicity = n + 1) :
    PartitionedTensor
      (K := K) (A := fun c ↦ PositiveWord (A c) n)
      (PositivePowerBlockSpace K V n) :=
  P.selectEncodedCompleteSplitProfiles encode term.index
    (fun c ↦ term.positivePowerProfile hmultiplicity c)

end Encoded

end AlgebraicComplexity
