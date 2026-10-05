/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.MatrixMultiplication.InterfaceTensor
import AlgebraicComplexity.MatrixMultiplication.InterfaceTensorSelectionCore
import AlgebraicComplexity.Tensor.PartitionedPowerRelabeling
import AlgebraicComplexity.Tensor.PowerFamily

/-!
# Tensor realization of exact complete-split profiles

This module connects the optimizer-independent complete-split data in `InterfaceTensor` to actual
partitioned tensor powers.  If a level constituent is partitioned on each leg by depth-`d` split
words, a positive power has block labels that are sequences of such words.  Independently keeping
the three leg sequences in prescribed exact type classes realizes the paper's notation
`T^[N][βX, βY, βZ]` at zero approximation error.

The semantic data file deliberately does not import partitioned tensor powers; this heavier bridge
is a separate module so downstream numerical clients do not contaminate the reusable definitions.

"The paper" in this module is the in-repository manuscript *Rectangular Volume and
Parent-Consistent Compatibility in the Laser Method*
(`better_bound/paper.tex`).
-/

namespace AlgebraicComplexity

open Tensor

universe u v w

namespace CompleteSplitProfile

variable {depth total n : ℕ}

/-- Permuting the samples of a positive word preserves its exact complete-split profile. -/
theorem matchesPositiveWord_positionEquiv_iff
    (β : CompleteSplitProfile depth total (n + 1))
    (word : PositiveWord (SplitWord depth) n)
    (sigma : Equiv.Perm (Fin (n + 1))) :
    β.MatchesPositiveWord
        (positiveWordPositionEquiv (SplitWord depth) n sigma word) ↔
      β.MatchesPositiveWord word := by
  rw [matchesPositiveWord_iff_isConsistent,
    matchesPositiveWord_iff_isConsistent,
    positiveWordEquiv_position_apply]
  exact β.isConsistent_comp_perm _ sigma

/-- The encoded form of exact complete-split selection is likewise invariant under arbitrary
sample-position permutations. -/
theorem matchesEncodedPositiveWord_positionEquiv_iff
    {A : Type w} (β : CompleteSplitProfile depth total (n + 1))
    (encode : A → SplitWord depth) (word : PositiveWord A n)
    (sigma : Equiv.Perm (Fin (n + 1))) :
    β.MatchesEncodedPositiveWord encode
        (positiveWordPositionEquiv A n sigma word) ↔
      β.MatchesEncodedPositiveWord encode word := by
  rw [matchesEncodedPositiveWord_iff, matchesEncodedPositiveWord_iff,
    positiveWordEquiv_position_apply]
  simpa only [Function.comp_assoc] using
    β.isConsistent_comp_perm
      (encode ∘ positiveWordEquiv A n word) sigma

end CompleteSplitProfile

section

variable {K : Type u} [CommSemiring K]
variable {depth n : ℕ}
variable {V : ∀ _c, SplitWord depth → Type (max u v)}
variable [∀ c a, AddCommMonoid (V c a)] [∀ c a, Module K (V c a)]

/-- Arbitrary sample-position permutations preserve a complete-split-selected interface tensor,
including every selected constituent and its dependent block space. -/
noncomputable def Tensor.PartitionedTensor.selectCompleteSplitProfilesPositionRelabeling
    (P : PartitionedTensor (K := K) (A := fun _ : Leg ↦ SplitWord depth) V)
    (index : LevelConstituentIndex depth)
    (profile : ∀ c, CompleteSplitProfile depth (index.count c) (n + 1))
    (sigma : Equiv.Perm (Fin (n + 1))) :
    (P.selectCompleteSplitProfiles index profile).StructureRelabeling := by
  classical
  unfold Tensor.PartitionedTensor.selectCompleteSplitProfiles
  let r := Tensor.PartitionedTensor.StructureRelabeling.positivePowerPositionRelabeling
    P n sigma
  refine r.select (fun c word ↦ (profile c).MatchesPositiveWord word) ?_
  intro c word
  rw [show r.partEquiv c = positiveWordPositionEquiv
      (SplitWord depth) n sigma by
    dsimp [r]
    exact Tensor.PartitionedTensor.StructureRelabeling.positivePowerPositionRelabeling_partEquiv
      P n sigma c]
  have h := CompleteSplitProfile.matchesPositiveWord_positionEquiv_iff
    (profile c) ((positiveWordPositionEquiv (SplitWord depth) n sigma).symm word) sigma
  simpa using h.symm

/-- Exact complete-split selection is an ordinary legwise variable zeroing of the positive
partitioned power. -/
theorem Tensor.Restricts.partitionedPositivePower_selectCompleteSplitProfiles
    (P : PartitionedTensor (K := K) (A := fun _ : Leg ↦ SplitWord depth) V)
    (index : LevelConstituentIndex depth)
    (profile : ∀ c, CompleteSplitProfile depth (index.count c) (n + 1)) :
    Restricts (P.positivePower n).realize
      (P.selectCompleteSplitProfiles index profile).realize := by
  classical
  exact Tensor.Restricts.partitionedSelect (P.positivePower n)
    (fun c word ↦ (profile c).MatchesPositiveWord word)

/-- Canonical tensor power followed by exact complete-split selection.  This is the tensor-level
realization of one exact interface term before taking products over a parameter list. -/
theorem Tensor.Restricts.power_selectCompleteSplitProfiles
    (P : PartitionedTensor (K := K) (A := fun _ : Leg ↦ SplitWord depth) V)
    (index : LevelConstituentIndex depth)
    (profile : ∀ c, CompleteSplitProfile depth (index.count c) (n + 1)) :
    Restricts (Tensor.power P.realize (n + 1))
      (P.selectCompleteSplitProfiles index profile).realize :=
  (Tensor.Restricts.power_partitionedPositivePower P n).trans
    (Tensor.Restricts.partitionedPositivePower_selectCompleteSplitProfiles P index profile)

/-- Every exact interface term inherits the full symmetric-group action on its samples. -/
noncomputable def Tensor.PartitionedTensor.selectExactInterfaceTermPositionRelabeling
    (P : PartitionedTensor (K := K) (A := fun _ : Leg ↦ SplitWord depth) V)
    (term : ExactInterfaceTermParameters depth)
    (hmultiplicity : term.multiplicity = n + 1)
    (sigma : Equiv.Perm (Fin (n + 1))) :
    (P.selectExactInterfaceTerm term hmultiplicity).StructureRelabeling :=
  P.selectCompleteSplitProfilesPositionRelabeling term.index
    (fun c ↦ term.positivePowerProfile hmultiplicity c) sigma

/-- A canonical tensor power restricts to the exact interface term specified by the parameter
record. -/
theorem Tensor.Restricts.power_selectExactInterfaceTerm
    (P : PartitionedTensor (K := K) (A := fun _ : Leg ↦ SplitWord depth) V)
    (term : ExactInterfaceTermParameters depth)
    (hmultiplicity : term.multiplicity = n + 1) :
    Restricts (Tensor.power P.realize (n + 1))
      (P.selectExactInterfaceTerm term hmultiplicity).realize :=
  Tensor.Restricts.power_selectCompleteSplitProfiles P term.index
    (fun c ↦ term.positivePowerProfile hmultiplicity c)

end

section Encoded

variable {K : Type u} [CommSemiring K]
variable {depth n : ℕ}
variable {A : Leg → Type w} [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]
variable {V : ∀ c, A c → Type (max u v)}
variable [∀ c a, AddCommMonoid (V c a)] [∀ c a, Module K (V c a)]

/-- Encoded complete-split interface tensors inherit the full symmetric-group action on their
sample positions.  This is the relabeling witness consumed by recursive hole repair in concrete
CW clients. -/
noncomputable def Tensor.PartitionedTensor.selectEncodedCompleteSplitProfilesPositionRelabeling
    (P : PartitionedTensor (K := K) (A := A) V)
    (encode : ∀ c, A c → SplitWord depth)
    (index : LevelConstituentIndex depth)
    (profile : ∀ c, CompleteSplitProfile depth (index.count c) (n + 1))
    (sigma : Equiv.Perm (Fin (n + 1))) :
    (P.selectEncodedCompleteSplitProfiles encode index profile).StructureRelabeling := by
  classical
  unfold Tensor.PartitionedTensor.selectEncodedCompleteSplitProfiles
  let r := Tensor.PartitionedTensor.StructureRelabeling.positivePowerPositionRelabeling
    P n sigma
  refine r.select
    (fun c word ↦ (profile c).MatchesEncodedPositiveWord (encode c) word) ?_
  intro c word
  rw [show r.partEquiv c = positiveWordPositionEquiv (A c) n sigma by
    dsimp [r]
    exact Tensor.PartitionedTensor.StructureRelabeling.positivePowerPositionRelabeling_partEquiv
      P n sigma c]
  have h := CompleteSplitProfile.matchesEncodedPositiveWord_positionEquiv_iff
    (profile c) (encode c)
    ((positiveWordPositionEquiv (A c) n sigma).symm word) sigma
  simpa using h.symm

/-- Tensor-power restriction form of encoded exact complete-split selection. -/
theorem Tensor.Restricts.power_selectEncodedCompleteSplitProfiles
    (P : PartitionedTensor (K := K) (A := A) V)
    (encode : ∀ c, A c → SplitWord depth)
    (index : LevelConstituentIndex depth)
    (profile : ∀ c, CompleteSplitProfile depth (index.count c) (n + 1)) :
    Restricts (Tensor.power P.realize (n + 1))
      (P.selectEncodedCompleteSplitProfiles encode index profile).realize :=
  (Tensor.Restricts.power_partitionedPositivePower P n).trans <| by
    classical
    exact Tensor.Restricts.partitionedSelect (P.positivePower n)
      (fun c word ↦ (profile c).MatchesEncodedPositiveWord (encode c) word)

/-- Encoded exact interface terms inherit the full symmetric-group action on their samples. -/
noncomputable def Tensor.PartitionedTensor.selectEncodedExactInterfaceTermPositionRelabeling
    (P : PartitionedTensor (K := K) (A := A) V)
    (encode : ∀ c, A c → SplitWord depth)
    (term : ExactInterfaceTermParameters depth)
    (hmultiplicity : term.multiplicity = n + 1)
    (sigma : Equiv.Perm (Fin (n + 1))) :
    (P.selectEncodedExactInterfaceTerm encode term hmultiplicity).StructureRelabeling :=
  P.selectEncodedCompleteSplitProfilesPositionRelabeling encode term.index
    (fun c ↦ term.positivePowerProfile hmultiplicity c) sigma

/-- A canonical tensor power restricts to an encoded exact interface term. -/
theorem Tensor.Restricts.power_selectEncodedExactInterfaceTerm
    (P : PartitionedTensor (K := K) (A := A) V)
    (encode : ∀ c, A c → SplitWord depth)
    (term : ExactInterfaceTermParameters depth)
    (hmultiplicity : term.multiplicity = n + 1) :
    Restricts (Tensor.power P.realize (n + 1))
      (P.selectEncodedExactInterfaceTerm encode term hmultiplicity).realize :=
  Tensor.Restricts.power_selectEncodedCompleteSplitProfiles P encode term.index
    (fun c ↦ term.positivePowerProfile hmultiplicity c)

/-- Package one positive exact interface term as a heterogeneous restriction of the corresponding
power of the partitioned realization.  Products of these packages are handled generically by
`PowerRestriction.positiveProduct`. -/
noncomputable def Tensor.PartitionedTensor.encodedExactInterfacePowerRestriction
    (P : PartitionedTensor (K := K) (A := A) V)
    (encode : ∀ c, A c → SplitWord depth)
    (term : PositiveExactInterfaceTermParameters depth) :
    PowerRestriction.{u, max u (max v w), max v w} P.realize := by
  let hmultiplicity : term.term.multiplicity = term.predMultiplicity + 1 :=
    term.multiplicity_eq_pred_add_one
  let selected := P.selectEncodedExactInterfaceTerm encode term.term hmultiplicity
  refine
    { exponent := term.term.multiplicity
      Target := LegModuleFamily.of.{u, max v w} (K := K) _
      target := selected.realize
      restricts := ?_ }
  change Restricts (power P.realize term.term.multiplicity)
    (P.selectEncodedExactInterfaceTerm encode term.term hmultiplicity).realize
  exact
    ((Tensor.Isomorphic.power_congr P.realize hmultiplicity).restricts).trans
      (Tensor.Restricts.power_selectEncodedExactInterfaceTerm
        P encode term.term hmultiplicity)

/-- Exact zero-error interface tensor for a nonempty parameter list: externally multiply all
selected terms while retaining a certificate from one flat source power.  This is the finite
formal counterpart of the paper's `⊗ₜ T_t^(n_t)[βX,t, βY,t, βZ,t]`. -/
noncomputable def Tensor.PartitionedTensor.encodedExactInterfacePowerProduct
    (P : PartitionedTensor (K := K) (A := A) V)
    (encode : ∀ c, A c → SplitWord depth) (termCount : ℕ)
    (terms : PositiveWord (PositiveExactInterfaceTermParameters depth) termCount) :
    PowerRestriction.{u, max u (max v w), max v w} P.realize :=
  PowerRestriction.positiveProduct termCount
    (positiveWordMap (P.encodedExactInterfacePowerRestriction encode) termCount terms)

@[simp] theorem Tensor.PartitionedTensor.encodedExactInterfacePowerProduct_exponent
    (P : PartitionedTensor (K := K) (A := A) V)
    (encode : ∀ c, A c → SplitWord depth) (termCount : ℕ)
    (terms : PositiveWord (PositiveExactInterfaceTermParameters depth) termCount) :
    (P.encodedExactInterfacePowerProduct encode termCount terms).exponent =
      positiveWordSum (fun term ↦ term.term.multiplicity) termCount terms := by
  unfold Tensor.PartitionedTensor.encodedExactInterfacePowerProduct
  rw [PowerRestriction.positiveProduct_exponent, positiveWordSum_map]
  rfl

/-- The exact interface tensor assembled from a parameter list is a restriction of the source
power whose exponent is the sum of all term multiplicities. -/
theorem Tensor.Restricts.power_encodedExactInterfacePowerProduct
    (P : PartitionedTensor (K := K) (A := A) V)
    (encode : ∀ c, A c → SplitWord depth) (termCount : ℕ)
    (terms : PositiveWord (PositiveExactInterfaceTermParameters depth) termCount) :
    Restricts
      (Tensor.power P.realize
        (positiveWordSum (fun term ↦ term.term.multiplicity) termCount terms))
      (P.encodedExactInterfacePowerProduct encode termCount terms).target := by
  let product := P.encodedExactInterfacePowerProduct encode termCount terms
  have hexponent : product.exponent =
      positiveWordSum (fun term ↦ term.term.multiplicity) termCount terms :=
    P.encodedExactInterfacePowerProduct_exponent encode termCount terms
  exact ((Tensor.Isomorphic.power_congr P.realize hexponent.symm).restricts).trans
    product.restricts

end Encoded

end AlgebraicComplexity
