/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Combinatorics.ComplementaryOccurrencePairedWordCore
import AlgebraicComplexity.Combinatorics.ComplementaryProductProjectionProfile
import AlgebraicComplexity.Probability.ComplementaryOccurrenceCellProjection

/-!
# Paired words after a complementary-occurrence cell quotient

Claim 6.18 of Alman--Duan--Vassilevska Williams--Xu--Xu--Zhou,
*More Asymmetry Yields Faster Matrix Multiplication*, fixes an ordered parent type and one
combined table of the two labelled child occurrences after quotienting parent states into
compatibility cells.  This module supplies the denominator-free bridge from those two exact
word-type equations to the pooled-profile predicate used by the information-projection count.

The result is the arbitrary-cell counterpart of
`ComplementaryOccurrenceLaw.isPooledMarginalProfile_of_pairWords`.  It keeps the two occurrences
of a self-complementary state distinct and assumes neither separate left/right tables nor a
probability-valued feasibility condition.  It formalizes the finite profile step in
[alman2025more, Claim 6.18], `papers/sources/2404.16349/constituent.tex:388-436`, especially
lines 402--429.
-/

set_option autoImplicit false

namespace AlgebraicComplexity
namespace ComplementaryOccurrenceLaw

universe u v w

variable {State : Type u} [Fintype State] [DecidableEq State]
variable {Symbol : Type v} [Fintype Symbol] [DecidableEq Symbol] [Nonempty Symbol]
variable {Cell : Type w} [Fintype Cell] [DecidableEq Cell]
variable {profile : State → ℕ}

/-- Exact state and combined labelled-cell word types instantiate the pooled projection after an
arbitrary state-cell quotient.

Proof sketch: the first marginal of the parent-pair word is the ordered-state word type.  The sum
of its two labelled feature marginals is the multiplicity of the concatenated left/right
cell-symbol word.  Rewriting these by the two hypotheses gives the reference state profile and
the reference pooled occurrence table, so the general arbitrary-cell integral adapter applies.
-/
theorem isPooledMarginalProfile_of_cellPairWords
    (law : ComplementaryOccurrenceLaw profile Symbol)
    (complement : Equiv.Perm State) (cellOf : State → Cell)
    (hmass : 0 < WordType.profileMass profile)
    {n : ℕ}
    (state : Fin n → State) (left right : Fin n → Symbol)
    (hstate : WordType.multiplicity state = profile)
    (hchildren :
      WordType.multiplicity
          (Fin.append
            (fun i ↦ (cellOf (state i), left i))
            (fun i ↦ (cellOf (complement (state i)), right i))) =
        law.cellJointProfile complement cellOf) :
    let M := law.toCellProductProjectionModel complement cellOf hmass
    WordType.IsPooledMarginalProfile M.toSparsePooledMarginalProjectionModel
      (WordType.multiplicity (parentPairWord state left right)) := by
  let M := law.toCellProductProjectionModel complement cellOf hmass
  let parentProfile := WordType.multiplicity (parentPairWord state left right)
  have hparentMass : WordType.profileMass parentProfile = WordType.profileMass profile := by
    calc
      WordType.profileMass parentProfile =
          WordType.profileMass (WordType.mappedType Prod.fst parentProfile) :=
        (WordType.profileMass_mappedType Prod.fst parentProfile).symm
      _ = WordType.profileMass (WordType.multiplicity state) := by
        rw [mappedType_fst_multiplicity_parentPairWord]
      _ = WordType.profileMass profile := congrArg WordType.profileMass hstate
  have hparentMassPos : 0 < WordType.profileMass parentProfile := by
    rw [hparentMass]
    exact hmass
  apply M.isPooledMarginalProfile_of_normalized_marginals parentProfile hparentMassPos
  · intro orderedState
    change (WordType.mappedType Prod.fst parentProfile orderedState : ℝ) /
        WordType.profileMass parentProfile = M.stateLaw.weight orderedState
    rw [mappedType_fst_multiplicity_parentPairWord, hstate, hparentMass]
    rfl
  · intro feature
    rw [← add_div, ← Nat.cast_add]
    rw [M.pooledMappedType_parentPairWord_eq_labelledCellWord state left right]
    change (WordType.multiplicity
        (Fin.append
          (fun i ↦ (cellOf (state i), left i))
          (fun i ↦ (cellOf (complement (state i)), right i))) feature : ℝ) /
      WordType.profileMass parentProfile = _
    rw [hchildren, hparentMass]
    obtain ⟨cell, symbol⟩ := feature
    exact
      (law.toCellProductProjectionModel_reference_pooledFeature_weight
        complement cellOf hmass cell symbol).symm

/-! The singleton instance below verifies that all data-carrying hypotheses of the public theorem
can hold simultaneously, including the combined two-occurrence table. -/

private def cellPairTinyLaw :
    ComplementaryOccurrenceLaw (fun _ : Unit ↦ 1) Unit where
  count := fun _ _ ↦ 1
  rowSum := by
    intro occurrence
    simp

private def cellPairTinyState : Fin 1 → Unit := fun _ ↦ ()

private def cellPairTinyChild : Fin 1 → Unit := fun _ ↦ ()

private theorem cellPairTiny_card_complementarySide :
    Fintype.card ComplementarySide = 2 := by
  decide

private theorem cellPairTinyState_multiplicity :
    WordType.multiplicity cellPairTinyState = fun _ : Unit ↦ 1 := by
  classical
  funext state
  have hstate : state = () := Subsingleton.elim _ _
  subst state
  rw [show cellPairTinyState = fun _ ↦ () by rfl, WordType.multiplicity_const]
  simp

private theorem cellPairTinyChildren_multiplicity :
    WordType.multiplicity
        (Fin.append
          (fun i ↦ ((fun _ : Unit ↦ ()) (cellPairTinyState i), cellPairTinyChild i))
          (fun i ↦
            ((fun _ : Unit ↦ ()) ((Equiv.refl Unit) (cellPairTinyState i)),
              cellPairTinyChild i))) =
      cellPairTinyLaw.cellJointProfile (Equiv.refl Unit) (fun _ ↦ ()) := by
  classical
  funext entry
  have hentry : entry = ((), ()) := Subsingleton.elim _ _
  subst entry
  rw [show Fin.append
      (fun i ↦ ((fun _ : Unit ↦ ()) (cellPairTinyState i), cellPairTinyChild i))
      (fun i ↦
        ((fun _ : Unit ↦ ()) ((Equiv.refl Unit) (cellPairTinyState i)),
          cellPairTinyChild i)) = fun _ ↦ ((), ()) by
        funext i
        exact Subsingleton.elim _ _]
  rw [WordType.multiplicity_const]
  simp [cellPairTinyLaw, ComplementaryOccurrenceLaw.cellJointProfile,
    cellPairTiny_card_complementarySide]

/-- Binder-level satisfiability check for the arbitrary-cell paired-word bridge. -/
private example :
    let M := cellPairTinyLaw.toCellProductProjectionModel
      (Equiv.refl Unit) (fun _ ↦ ()) (by simp [WordType.profileMass])
    WordType.IsPooledMarginalProfile M.toSparsePooledMarginalProjectionModel
      (WordType.multiplicity
        (parentPairWord cellPairTinyState cellPairTinyChild cellPairTinyChild)) := by
  exact isPooledMarginalProfile_of_cellPairWords
    cellPairTinyLaw (Equiv.refl Unit) (fun _ ↦ ())
    (by simp [WordType.profileMass])
    cellPairTinyState cellPairTinyChild cellPairTinyChild
    cellPairTinyState_multiplicity cellPairTinyChildren_multiplicity

end ComplementaryOccurrenceLaw
end AlgebraicComplexity
