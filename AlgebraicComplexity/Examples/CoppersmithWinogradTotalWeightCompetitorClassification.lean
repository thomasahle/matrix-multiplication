/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.CoppersmithWinogradTotalWeightQuotientCompatibility
import AlgebraicComplexity.Examples.CoppersmithWinogradCompatibilityTargetCounting
import AlgebraicComplexity.MatrixMultiplication.PushedProfileCompatibilityCounting

set_option autoImplicit false

/-!
# Source-aware competitor encodings for the CW total-weight quotient

A quotient compatibility competitor is still a complete supported quotient address, not merely
its compatibility-cell word.  This file recovers the unique supported atom word underlying each
address and proves that recovery injective.  Consequently, once the certificate's exact joint
profile is supplied, every `Y` or `Z` competitor embeds into the corresponding conditional type
class.  The final theorems immediately combine that finite encoding with the pushed-profile
entropy bound.

The remaining certificate-facing hypothesis is deliberately visible: every competitor's joint
`(fixed pivot word, tagged supported atom)` multiplicity must equal the stated proportional pushed
profile.  Compatibility-cell marginals alone do not imply this full joint-type equality.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor MoreAsymmetryCompatibility
open scoped BigOperators

universe u

/-- Recover the supported total-weight atom word underlying a positive-power address.

This local recovery interface deliberately has no dependency on the downstream whole-constituent
stage: competitor counting needs only the support-word/address equivalence. -/
noncomputable def cwTotalWeightCompetitorCoarseWordOfAddress
    (K : Type u) [CommRing K] (q depth n : ℕ)
    (address : BlockAddress (fun _c ↦ PositiveWord (CWCoarseDigit depth) n))
    (haddress : address ∈
      (((cwChunkPartitionedTensor K q depth).coarsen
        (cwTotalWeightChunkCoarsening depth)).positivePower n).support) :
    PositiveWord (CWTotalWeightCoarseSupport K q depth) n :=
  Classical.choose
    (((cwChunkPartitionedTensor K q depth).coarsen
      (cwTotalWeightChunkCoarsening depth)
        ).exists_positiveSupportWord_of_mem_positivePower_support n haddress)

/-- Transposing the locally recovered support word gives the original address. -/
theorem positiveSupportWordBlockAddress_cwTotalWeightCompetitorCoarseWordOfAddress
    (K : Type u) [CommRing K] (q depth n : ℕ)
    (address : BlockAddress (fun _c ↦ PositiveWord (CWCoarseDigit depth) n))
    (haddress : address ∈
      (((cwChunkPartitionedTensor K q depth).coarsen
        (cwTotalWeightChunkCoarsening depth)).positivePower n).support) :
    positiveSupportWordBlockAddress
        (CWTotalWeightCoarseSupport K q depth) n
        (cwTotalWeightCompetitorCoarseWordOfAddress
          K q depth n address haddress) = address :=
  Classical.choose_spec
    (((cwChunkPartitionedTensor K q depth).coarsen
      (cwTotalWeightChunkCoarsening depth)
        ).exists_positiveSupportWord_of_mem_positivePower_support n haddress)

/-- One complete total-weight quotient atom, tagged by its recursive region.

Only the underlying three-leg quotient address is retained.  Membership in the tensor support is
a proposition and carries no additional word data; forgetting that proof also keeps this finite
alphabet in `Type`, as required by the exact finite counting interface. -/
abbrev CWTotalWeightTaggedAtom
    (depth : ℕ) (Part : Type) :=
  Part × BlockAddress (fun _c ↦ CWCoarseDigit depth)

/-- Recover the full tagged quotient-support atom at every sample. -/
noncomputable def cwTotalWeightTaggedAtomWord
    (K : Type u) [CommRing K] (q depth n : ℕ)
    {Part : Type} (partAt : Fin (n + 1) → Part)
    (address : BlockAddress
      (fun _c ↦ PositiveWord (CWCoarseDigit depth) n))
    (haddress : address ∈
      (((cwChunkPartitionedTensor K q depth).coarsen
        (cwTotalWeightChunkCoarsening depth)).positivePower n).support) :
    Fin (n + 1) → CWTotalWeightTaggedAtom depth Part :=
  fun sample ↦
    (partAt sample,
      (positiveWordEquiv (CWTotalWeightCoarseSupport K q depth) n
        (cwTotalWeightCompetitorCoarseWordOfAddress
          K q depth n address haddress) sample).1)

/-- The recovered atom word remembers each quotient leg word coordinatewise. -/
theorem cwTotalWeightTaggedAtomWord_address_apply
    (K : Type u) [CommRing K] (q depth n : ℕ)
    {Part : Type} (partAt : Fin (n + 1) → Part)
    (address : BlockAddress
      (fun _c ↦ PositiveWord (CWCoarseDigit depth) n))
    (haddress : address ∈
      (((cwChunkPartitionedTensor K q depth).coarsen
        (cwTotalWeightChunkCoarsening depth)).positivePower n).support)
    (sample : Fin (n + 1)) (c : Leg) :
    ((cwTotalWeightTaggedAtomWord K q depth n partAt
      address haddress sample).2 c) =
      positiveWordEquiv (CWCoarseDigit depth) n (address c) sample := by
  have htranspose := positiveWordEquiv_positiveSupportWordBlockAddress
    (CWTotalWeightCoarseSupport K q depth) n
    (cwTotalWeightCompetitorCoarseWordOfAddress
      K q depth n address haddress) c
  rw [positiveSupportWordBlockAddress_cwTotalWeightCompetitorCoarseWordOfAddress
    K q depth n address haddress] at htranspose
  exact (congrFun htranspose sample).symm

/-- Complete tagged atom words are injective in supported quotient addresses. -/
theorem cwTotalWeightTaggedAtomWord_injective
    (K : Type u) [CommRing K] (q depth n : ℕ)
    {Part : Type} (partAt : Fin (n + 1) → Part)
    {left right : BlockAddress
      (fun _c ↦ PositiveWord (CWCoarseDigit depth) n)}
    (hleft : left ∈
      (((cwChunkPartitionedTensor K q depth).coarsen
        (cwTotalWeightChunkCoarsening depth)).positivePower n).support)
    (hright : right ∈
      (((cwChunkPartitionedTensor K q depth).coarsen
        (cwTotalWeightChunkCoarsening depth)).positivePower n).support)
    (hword : cwTotalWeightTaggedAtomWord K q depth n partAt left hleft =
      cwTotalWeightTaggedAtomWord K q depth n partAt right hright) :
    left = right := by
  funext c
  apply (positiveWordEquiv (CWCoarseDigit depth) n).injective
  funext sample
  rw [← cwTotalWeightTaggedAtomWord_address_apply
      K q depth n partAt left hleft sample c,
    ← cwTotalWeightTaggedAtomWord_address_apply
      K q depth n partAt right hright sample c]
  exact congrArg (fun word ↦ (word sample).2 c) hword

/-- Joint alphabet map which adjoins the selected pivot digit to a complete tagged atom. -/
def cwTotalWeightTaggedAtomPivotJoint
    {depth : ℕ} {Part : Type} (pivot : Leg) :
    CWTotalWeightTaggedAtom depth Part →
      CWCoarseDigit depth × CWTotalWeightTaggedAtom depth Part :=
  fun atom ↦ (atom.2 pivot, atom)

/-- The joint word used in competitor counting is just the complete tagged atom word mapped by
`cwTotalWeightTaggedAtomPivotJoint`.  This observation is what reduces the certificate-facing
premise from a separate competitor joint type to the already prescribed tagged atom type. -/
theorem cwTotalWeight_jointWord_eq_pivotJoint_comp_taggedAtomWord
    (K : Type u) [CommRing K] (q depth n : ℕ)
    {Part : Type} (partAt : Fin (n + 1) → Part)
    (pivot : Leg)
    (address : BlockAddress
      (fun _c ↦ PositiveWord (CWCoarseDigit depth) n))
    (haddress : address ∈
      (((cwChunkPartitionedTensor K q depth).coarsen
        (cwTotalWeightChunkCoarsening depth)).positivePower n).support) :
    WordType.jointWord
        (positiveWordEquiv (CWCoarseDigit depth) n (address pivot))
        (cwTotalWeightTaggedAtomWord K q depth n partAt address haddress) =
      cwTotalWeightTaggedAtomPivotJoint pivot ∘
        cwTotalWeightTaggedAtomWord K q depth n partAt address haddress := by
  funext sample
  apply Prod.ext
  · exact cwTotalWeightTaggedAtomWord_address_apply
      K q depth n partAt address haddress sample pivot |>.symm
  · rfl

/-- Consequently the complete competitor joint type is the deterministic pushforward of the
tagged atom type.  No compatibility-cell marginal is used in this identity. -/
theorem cwTotalWeight_jointMultiplicity_eq_mappedTaggedAtomMultiplicity
    (K : Type u) [CommRing K] (q depth n : ℕ)
    {Part : Type} [Fintype Part]
    (partAt : Fin (n + 1) → Part) (pivot : Leg)
    (address : BlockAddress
      (fun _c ↦ PositiveWord (CWCoarseDigit depth) n))
    (haddress : address ∈
      (((cwChunkPartitionedTensor K q depth).coarsen
        (cwTotalWeightChunkCoarsening depth)).positivePower n).support) :
    WordType.multiplicity
        (WordType.jointWord
          (positiveWordEquiv (CWCoarseDigit depth) n (address pivot))
          (cwTotalWeightTaggedAtomWord K q depth n partAt address haddress)) =
      WordType.mappedType (cwTotalWeightTaggedAtomPivotJoint pivot)
        (WordType.multiplicity
          (cwTotalWeightTaggedAtomWord K q depth n partAt address haddress)) := by
  rw [cwTotalWeight_jointWord_eq_pivotJoint_comp_taggedAtomWord]
  exact WordType.multiplicity_comp_eq_mappedType _ _

/-- With the identity orientation, the established full-cell word used by target-specific repair
is exactly the complete tagged total-weight atom word recovered from tensor support. -/
theorem cwTotalWeightTaggedAtomWord_eq_orientedFiniteCellSequence_refl
    (K : Type u) [CommRing K] (q depth n : ℕ)
    {Part : Type} (partAt : Fin (n + 1) → Part)
    (address : BlockAddress
      (fun _c ↦ PositiveWord (CWCoarseDigit depth) n))
    (haddress : address ∈
      (((cwChunkPartitionedTensor K q depth).coarsen
        (cwTotalWeightChunkCoarsening depth)).positivePower n).support) :
    cwTotalWeightTaggedAtomWord K q depth n partAt address haddress =
      cwOrientedFiniteCellSequence depth n partAt (Equiv.refl Leg) address := by
  funext sample
  apply Prod.ext
  · rfl
  · funext c
    exact cwTotalWeightTaggedAtomWord_address_apply
      K q depth n partAt address haddress sample c

/-- Preselecting one full tagged cell type before compatibility makes the complete atom
multiplicity constant.  This is the exact bridge from the existing polynomial-loss selector to
the sharper deterministic-pushforward competitor count. -/
theorem cwTotalWeightTaggedAtomMultiplicity_eq_reference_of_mem_fixedTargetCellType
    (K : Type u) [CommRing K] (q depth n : ℕ)
    {Part : Type} [Fintype Part] [DecidableEq Part]
    (partAt : Fin (n + 1) → Part)
    (coarseKept : Finset
      (BlockAddress (fun _c ↦ PositiveWord (CWCoarseDigit depth) n)))
    (hcoarseKept : coarseKept ⊆
      (((cwChunkPartitionedTensor K q depth).coarsen
        (cwTotalWeightChunkCoarsening depth)).positivePower n).support)
    (reference : BlockAddress
      (fun _c ↦ PositiveWord (CWCoarseDigit depth) n))
    (hreference : reference ∈ coarseKept)
    (address : BlockAddress
      (fun _c ↦ PositiveWord (CWCoarseDigit depth) n))
    (haddress : address ∈ cwFixedTargetCellTypeCoarseSupport
      depth n partAt (Equiv.refl Leg) coarseKept reference) :
    WordType.multiplicity
        (cwTotalWeightTaggedAtomWord K q depth n partAt address
          (hcoarseKept
            ((mem_cwFixedTargetCellTypeCoarseSupport_iff
              depth n partAt (Equiv.refl Leg) coarseKept reference address).1
                haddress).1)) =
      WordType.multiplicity
        (cwTotalWeightTaggedAtomWord K q depth n partAt reference
          (hcoarseKept hreference)) := by
  have hsame :=
    ((mem_cwFixedTargetCellTypeCoarseSupport_iff
      depth n partAt (Equiv.refl Leg) coarseKept reference address).1 haddress).2
  rw [cwTotalWeightTaggedAtomWord_eq_orientedFiniteCellSequence_refl,
    cwTotalWeightTaggedAtomWord_eq_orientedFiniteCellSequence_refl]
  exact hsame.symm

section Encoding

variable (K : Type u) [CommRing K] (q depth n : ℕ)
variable {Part : Type} [Fintype Part] [DecidableEq Part]
variable (partAt : Fin (n + 1) → Part)
variable (rawTargets : CompatibilityTargets Part depth)
variable (ambient : Finset
  (BlockAddress (fun _c ↦ PositiveWord (CWCoarseDigit depth) n)))
variable (hambient : ambient ⊆
  (((cwChunkPartitionedTensor K q depth).coarsen
    (cwTotalWeightChunkCoarsening depth)).positivePower n).support)

/-- Construct the exact `Y` competitor encoding from a supplied full joint-type equality. -/
noncomputable def cwTotalWeightYConditionalCompetitorEncoding
    (address : BlockAddress
      (fun _c ↦ PositiveWord (CWCoarseDigit depth) n))
    (jointType : CWCoarseDigit depth ×
      CWTotalWeightTaggedAtom depth Part → ℕ)
    (hlegal : jointType ∈ WordType.types
      (CWCoarseDigit depth × CWTotalWeightTaggedAtom depth Part) (n + 1))
    (hfst : WordType.mappedType Prod.fst jointType =
      WordType.multiplicity
        (positiveWordEquiv (CWCoarseDigit depth) n (address .Y)))
    (hjoint : ∀ other : {other // other ∈
      compatibilityCompetitors ambient .Y
        (cwTotalWeightCompatibilityY depth n partAt rawTargets) address},
      WordType.multiplicity
        (WordType.jointWord
          (positiveWordEquiv (CWCoarseDigit depth) n (address .Y))
          (cwTotalWeightTaggedAtomWord K q depth n partAt other.1
            (hambient (((mem_compatibilityCompetitors ambient .Y
              (cwTotalWeightCompatibilityY depth n partAt rawTargets)
              address other.1).1 other.2).1)))) = jointType) :
    ConditionalCompetitorEncoding ambient .Y
      (cwTotalWeightCompatibilityY depth n partAt rawTargets) address
      (CWCoarseDigit depth) (CWTotalWeightTaggedAtom depth Part) (n + 1) where
  source := positiveWordEquiv (CWCoarseDigit depth) n (address .Y)
  jointType := jointType
  jointType_legal := hlegal
  jointType_fst := hfst
  refinement other :=
    cwTotalWeightTaggedAtomWord K q depth n partAt other.1
      (hambient (((mem_compatibilityCompetitors ambient .Y
        (cwTotalWeightCompatibilityY depth n partAt rawTargets)
        address other.1).1 other.2).1))
  refinement_mem other := WordType.mem_conditionalTypeClass.mpr (hjoint other)
  refinement_injective := by
    intro left right heq
    apply Subtype.ext
    apply cwTotalWeightTaggedAtomWord_injective K q depth n partAt
      (hambient (((mem_compatibilityCompetitors ambient .Y
        (cwTotalWeightCompatibilityY depth n partAt rawTargets)
        address left.1).1 left.2).1))
      (hambient (((mem_compatibilityCompetitors ambient .Y
        (cwTotalWeightCompatibilityY depth n partAt rawTargets)
        address right.1).1 right.2).1))
    exact heq

/-- Construct the exact `Z` competitor encoding from a supplied full joint-type equality. -/
noncomputable def cwTotalWeightZConditionalCompetitorEncoding
    (address : BlockAddress
      (fun _c ↦ PositiveWord (CWCoarseDigit depth) n))
    (jointType : CWCoarseDigit depth ×
      CWTotalWeightTaggedAtom depth Part → ℕ)
    (hlegal : jointType ∈ WordType.types
      (CWCoarseDigit depth × CWTotalWeightTaggedAtom depth Part) (n + 1))
    (hfst : WordType.mappedType Prod.fst jointType =
      WordType.multiplicity
        (positiveWordEquiv (CWCoarseDigit depth) n (address .Z)))
    (hjoint : ∀ other : {other // other ∈
      compatibilityCompetitors ambient .Z
        (cwTotalWeightCompatibilityZ depth n partAt rawTargets) address},
      WordType.multiplicity
        (WordType.jointWord
          (positiveWordEquiv (CWCoarseDigit depth) n (address .Z))
          (cwTotalWeightTaggedAtomWord K q depth n partAt other.1
            (hambient (((mem_compatibilityCompetitors ambient .Z
              (cwTotalWeightCompatibilityZ depth n partAt rawTargets)
              address other.1).1 other.2).1)))) = jointType) :
    ConditionalCompetitorEncoding ambient .Z
      (cwTotalWeightCompatibilityZ depth n partAt rawTargets) address
      (CWCoarseDigit depth) (CWTotalWeightTaggedAtom depth Part) (n + 1) where
  source := positiveWordEquiv (CWCoarseDigit depth) n (address .Z)
  jointType := jointType
  jointType_legal := hlegal
  jointType_fst := hfst
  refinement other :=
    cwTotalWeightTaggedAtomWord K q depth n partAt other.1
      (hambient (((mem_compatibilityCompetitors ambient .Z
        (cwTotalWeightCompatibilityZ depth n partAt rawTargets)
        address other.1).1 other.2).1))
  refinement_mem other := WordType.mem_conditionalTypeClass.mpr (hjoint other)
  refinement_injective := by
    intro left right heq
    apply Subtype.ext
    apply cwTotalWeightTaggedAtomWord_injective K q depth n partAt
      (hambient (((mem_compatibilityCompetitors ambient .Z
        (cwTotalWeightCompatibilityZ depth n partAt rawTargets)
        address left.1).1 left.2).1))
      (hambient (((mem_compatibilityCompetitors ambient .Z
        (cwTotalWeightCompatibilityZ depth n partAt rawTargets)
        address right.1).1 right.2).1))
    exact heq

end Encoding

end AlgebraicComplexity.Examples
