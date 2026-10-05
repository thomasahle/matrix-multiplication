/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.InterfaceTensorRealization
import AlgebraicComplexity.MatrixMultiplication.MoreAsymmetryCompatibility

/-!
# Native positive-power compatibility models

This lightweight module connects the finite compatibility predicate to native block labels in a
partitioned tensor power.  It contains only the semantic support bridge.  Exact pooled
`Split_avg` reconstruction remains in `MoreAsymmetryCompatibilityInterface`, whose substantially
larger aggregation import cone is unnecessary for elementary support clients.
-/

namespace AlgebraicComplexity
namespace MoreAsymmetryCompatibility

open Tensor

universe u v w x

/-- A legwise split-word encoding is fine-legal on a partitioned tensor support when every
supported source block address encodes a coordinatewise legal CW monomial. -/
def IsEncodedFineLegalOnSupport {A : Leg → Type u} {depth : ℕ}
    (support : Finset (BlockAddress A)) (encode : ∀ c, A c → SplitWord depth) : Prop :=
  ∀ address, address ∈ support → ∀ position,
    (encode .X (address .X) position : ℕ) +
      (encode .Y (address .Y) position : ℕ) +
      (encode .Z (address .Z) position : ℕ) = 2

/-- The compatibility model carried by a native positive-power block address.  `partAt` can be
constant in the global stage and can record a region/interface-term label in a recursive stage. -/
def encodedPositiveWordCompatibilityModel {A : Leg → Type u} {Part : Type v}
    {depth n : ℕ} (encode : ∀ c, A c → SplitWord depth)
    (partAt : Fin (n + 1) → Part) :
    CompatibilityModel (fun c ↦ PositiveWord (A c) n) Part depth (n + 1) where
  chunks c word sample := encode c (positiveWordEquiv (A c) n word sample)
  coarse address sample :=
    { part := partAt sample
      x := splitWordWeight (encode .X
        (positiveWordEquiv (A .X) n (address .X) sample))
      y := splitWordWeight (encode .Y
        (positiveWordEquiv (A .Y) n (address .Y) sample))
      z := splitWordWeight (encode .Z
        (positiveWordEquiv (A .Z) n (address .Z) sample)) }

@[simp] theorem encodedPositiveWordCompatibilityModel_chunks
    {A : Leg → Type u} {Part : Type v} {depth n : ℕ}
    (encode : ∀ c, A c → SplitWord depth) (partAt : Fin (n + 1) → Part)
    (c : Leg) (word : PositiveWord (A c) n) (sample : Fin (n + 1)) :
    (encodedPositiveWordCompatibilityModel encode partAt).chunks c word sample =
      encode c (positiveWordEquiv (A c) n word sample) :=
  rfl

/-- Every letter occurring in a sequence consistent with an exact complete-split profile has the
profile's prescribed total weight. -/
theorem completeSplitProfile_weight_eq_of_isConsistent
    {depth total samples : ℕ} (profile : CompleteSplitProfile depth total samples)
    (sequence : Fin samples → SplitWord depth) (hconsistent : profile.IsConsistent sequence)
    (sample : Fin samples) :
    splitWordWeight (sequence sample) = total := by
  apply profile.supported
  rw [← hconsistent]
  exact WordType.multiplicity_apply_ne_zero sequence sample

@[simp] theorem encodedPositiveWordCompatibilityModel_coarse_part
    {A : Leg → Type u} {Part : Type v} {depth n : ℕ}
    (encode : ∀ c, A c → SplitWord depth) (partAt : Fin (n + 1) → Part)
    (address : BlockAddress (fun c ↦ PositiveWord (A c) n)) (sample : Fin (n + 1)) :
    ((encodedPositiveWordCompatibilityModel encode partAt).coarse address sample).part =
      partAt sample :=
  rfl

/-- Coarse weights are definitionally correct for the native positive-power compatibility model. -/
theorem encodedPositiveWordCompatibilityModel_hasCoarseWeights
    {A : Leg → Type u} {Part : Type v} {depth n : ℕ}
    (encode : ∀ c, A c → SplitWord depth) (partAt : Fin (n + 1) → Part)
    (address : BlockAddress (fun c ↦ PositiveWord (A c) n)) :
    (encodedPositiveWordCompatibilityModel encode partAt).HasCoarseWeights address := by
  intro c sample
  cases c <;> rfl

/-- A word of supported source addresses induces a fine-legal positive-power block address. -/
theorem encodedPositiveWordCompatibilityModel_isFineLegal_supportWord
    {A : Leg → Type u} {Part : Type v} {depth n : ℕ}
    (support : Finset (BlockAddress A)) (encode : ∀ c, A c → SplitWord depth)
    (partAt : Fin (n + 1) → Part) (hlegal : IsEncodedFineLegalOnSupport support encode)
    (source : PositiveWord support n) :
    (encodedPositiveWordCompatibilityModel encode partAt).IsFineLegal
      (positiveSupportWordBlockAddress support n source) := by
  intro sample position
  change
    (encode .X
          (positiveWordEquiv (A .X) n
            (positiveSupportWordBlockAddress support n source .X) sample) position : ℕ) +
        (encode .Y
          (positiveWordEquiv (A .Y) n
            (positiveSupportWordBlockAddress support n source .Y) sample) position : ℕ) +
        (encode .Z
          (positiveWordEquiv (A .Z) n
            (positiveSupportWordBlockAddress support n source .Z) sample) position : ℕ) = 2
  rw [congrFun (positiveWordEquiv_positiveSupportWordBlockAddress support n source .X) sample,
    congrFun (positiveWordEquiv_positiveSupportWordBlockAddress support n source .Y) sample,
    congrFun (positiveWordEquiv_positiveSupportWordBlockAddress support n source .Z) sample]
  exact hlegal (positiveWordEquiv support n source sample).1
    (positiveWordEquiv support n source sample).2 position

section PartitionedTensor

variable {K : Type u} [CommSemiring K]
variable {A : Leg → Type w} [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]
variable {V : ∀ c, A c → Type (max u v)}
variable [∀ c a, AddCommMonoid (V c a)] [∀ c a, Module K (V c a)]
variable {Part : Type x} {depth n : ℕ}

/-- Read the exact coarse weight of one native chunk directly from selected-support membership. -/
theorem selectedExactInterfaceTerm_chunkWeight
    (P : PartitionedTensor (K := K) (A := A) V)
    (encode : ∀ c, A c → SplitWord depth)
    (term : ExactInterfaceTermParameters depth)
    (hmultiplicity : term.multiplicity = n + 1)
    (address : BlockAddress (fun c ↦ PositiveWord (A c) n))
    (haddress : address ∈
      (P.selectEncodedExactInterfaceTerm encode term hmultiplicity).support)
    (c : Leg) (sample : Fin (n + 1)) :
    splitWordWeight (encode c (positiveWordEquiv (A c) n (address c) sample)) =
      term.index.count c := by
  unfold Tensor.PartitionedTensor.selectEncodedExactInterfaceTerm at haddress
  have hconsistent :=
    ((Tensor.PartitionedTensor.mem_selectEncodedCompleteSplitProfiles_support
      P encode term.index (fun c ↦ term.positivePowerProfile hmultiplicity c) address).mp
        haddress).2 c
  exact completeSplitProfile_weight_eq_of_isConsistent
    (term.positivePowerProfile hmultiplicity c) _ hconsistent sample

/-- Fine legality on the source support transports through the positive tensor power. -/
theorem encodedPositiveWordCompatibilityModel_isFineLegal_of_mem_positivePower_support
    (P : PartitionedTensor (K := K) (A := A) V)
    (encode : ∀ c, A c → SplitWord depth) (partAt : Fin (n + 1) → Part)
    (hlegal : IsEncodedFineLegalOnSupport P.support encode)
    (address : BlockAddress (fun c ↦ PositiveWord (A c) n))
    (haddress : address ∈ (P.positivePower n).support) :
    (encodedPositiveWordCompatibilityModel encode partAt).IsFineLegal address := by
  obtain ⟨source, hsource⟩ :=
    P.exists_positiveSupportWord_of_mem_positivePower_support n haddress
  rw [← hsource]
  exact encodedPositiveWordCompatibilityModel_isFineLegal_supportWord
    P.support encode partAt hlegal source

/-- Exact complete-split selection preserves fine legality because it only zeroes blocks of the
positive tensor power. -/
theorem encodedPositiveWordCompatibilityModel_isFineLegal_of_mem_selected_support
    (P : PartitionedTensor (K := K) (A := A) V)
    (encode : ∀ c, A c → SplitWord depth) (partAt : Fin (n + 1) → Part)
    (hlegal : IsEncodedFineLegalOnSupport P.support encode)
    (index : LevelConstituentIndex depth)
    (profile : ∀ c, CompleteSplitProfile depth (index.count c) (n + 1))
    (address : BlockAddress (fun c ↦ PositiveWord (A c) n))
    (haddress : address ∈
      (P.selectEncodedCompleteSplitProfiles encode index profile).support) :
    (encodedPositiveWordCompatibilityModel encode partAt).IsFineLegal address := by
  apply encodedPositiveWordCompatibilityModel_isFineLegal_of_mem_positivePower_support
    P encode partAt hlegal address
  exact (P.mem_selectEncodedCompleteSplitProfiles_support encode index profile address).mp
    haddress |>.1

/-- The same support inheritance, specialized to the exact interface-term wrapper. -/
theorem encodedPositiveWordCompatibilityModel_isFineLegal_of_mem_exactInterfaceTerm_support
    (P : PartitionedTensor (K := K) (A := A) V)
    (encode : ∀ c, A c → SplitWord depth) (partAt : Fin (n + 1) → Part)
    (hlegal : IsEncodedFineLegalOnSupport P.support encode)
    (term : ExactInterfaceTermParameters depth)
    (hmultiplicity : term.multiplicity = n + 1)
    (address : BlockAddress (fun c ↦ PositiveWord (A c) n))
    (haddress : address ∈
      (P.selectEncodedExactInterfaceTerm encode term hmultiplicity).support) :
    (encodedPositiveWordCompatibilityModel encode partAt).IsFineLegal address := by
  exact encodedPositiveWordCompatibilityModel_isFineLegal_of_mem_selected_support
    P encode partAt hlegal term.index
      (fun c ↦ term.positivePowerProfile hmultiplicity c) address haddress

end PartitionedTensor

end MoreAsymmetryCompatibility
end AlgebraicComplexity
