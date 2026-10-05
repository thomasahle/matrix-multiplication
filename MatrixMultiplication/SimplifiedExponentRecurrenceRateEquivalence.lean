/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import Mathlib.Algebra.BigOperators.Finsupp.Basic
import MatrixMultiplication.SimplifiedExponentRecurrenceGrouping

/-!
# Order-independent sufficient statistics for level-two recurrence inputs

The executable `groupInputs` fold chooses a deterministic output order, but that order is not
stable under reassociation of independently checked chunks.  The retained-rate semantics does not
need an order: it sees only the total occurrence numerator at each
`(muNumerator, heavyCoordinate)` key.

This module records that sufficient statistic as a finitely supported map and defines
`KeyMassEquivalent` by equality of those maps.  It proves the equivalence and append laws needed
by a bounded merge tree, shows that `groupInputs` preserves the statistic, and factors both the
exact occurrence total and every branch rate through it.  Certificate clients may therefore
compose small checked grouping equalities without asserting equality of order-sensitive grouped
lists at a larger merge.
-/

namespace MatrixMultiplication.SimplifiedExponentRecurrence.Chunked

noncomputable section

/-- The finite map from `(muNumerator, heavyCoordinate)` to summed occurrence numerator. -/
abbrev KeyMass := (Nat × Nat) →₀ Nat

/-- The one-key contribution of an edge input to its sufficient statistic. -/
private def singletonKeyMass (input : EdgeInput) : KeyMass :=
  Finsupp.single input.key input.occurrenceNumerator

/-- Sum occurrence numerators independently at every sufficient-statistic key.

The codomain is a `Finsupp`, so zero rows disappear and list order is forgotten by construction.
Looking up `keyMass inputs key` returns the total numerator of precisely the inputs at `key`. -/
def keyMass : List EdgeInput → KeyMass
  | [] => 0
  | input :: inputs => singletonKeyMass input + keyMass inputs

/-- Two input lists carry the same order-independent retained-rate sufficient statistic. -/
def KeyMassEquivalent (left right : List EdgeInput) : Prop :=
  keyMass left = keyMass right

/-! ## Heavy-coordinate bands -/

/-- Retain, in source order, exactly the inputs whose heavy coordinate is zero. -/
def heavyZeroBand : List EdgeInput → List EdgeInput
  | [] => []
  | input :: inputs =>
      if input.heavyCoordinate = 0 then input :: heavyZeroBand inputs
      else heavyZeroBand inputs

/-- Retain, in source order, exactly the inputs whose heavy coordinate is one. -/
def heavyOneBand : List EdgeInput → List EdgeInput
  | [] => []
  | input :: inputs =>
      if input.heavyCoordinate = 1 then input :: heavyOneBand inputs
      else heavyOneBand inputs

/-- Retain every input whose heavy coordinate is neither zero nor one.

The residual predicate deliberately does not assume that the coordinate is two.  It therefore
makes the compact certificate partition exhaustive even for malformed or future inputs carrying
a larger coordinate; later semantic checks may establish the intended coordinate range. -/
def heavyResidualBand : List EdgeInput → List EdgeInput
  | [] => []
  | input :: inputs =>
      if input.heavyCoordinate = 0 then heavyResidualBand inputs
      else if input.heavyCoordinate = 1 then heavyResidualBand inputs
      else input :: heavyResidualBand inputs

/-- Combining two equal-key inputs replaces their singleton maps by their sum. -/
private theorem singletonKeyMass_combine_of_key_eq
    (left right : EdgeInput) (hkey : left.key = right.key) :
    singletonKeyMass (left.combine right) =
      singletonKeyMass left + singletonKeyMass right := by
  calc
    singletonKeyMass (left.combine right) =
        Finsupp.single left.key
          (left.occurrenceNumerator + right.occurrenceNumerator) := rfl
    _ = Finsupp.single left.key left.occurrenceNumerator +
          Finsupp.single left.key right.occurrenceNumerator :=
      Finsupp.single_add _ _ _
    _ = singletonKeyMass left + singletonKeyMass right := by
      unfold singletonKeyMass
      rw [hkey]

/-- Inserting an input by key preserves the complete key-mass map.

Proof sketch: at an equal key, `combine` turns two singleton maps into their sum.  At a different
key, insertion only commutes two additions before the induction hypothesis handles the tail. -/
theorem keyMass_insertInputByKey (input : EdgeInput) (inputs : List EdgeInput) :
    keyMass (insertInputByKey input inputs) = keyMass (input :: inputs) := by
  induction inputs with
  | nil => rfl
  | cons head tail ih =>
      by_cases hkey : input.key = head.key
      · simp only [insertInputByKey, hkey, if_true, keyMass]
        rw [singletonKeyMass_combine_of_key_eq input head hkey]
        exact add_assoc _ _ _
      · simp only [insertInputByKey, hkey, if_false, keyMass]
        rw [ih]
        exact add_left_comm _ _ _

/-- Executable grouping preserves the order-independent key-mass map.

Proof sketch: a zero row contributes the zero singleton map.  Every positive row is inserted into
the recursively grouped tail, where `keyMass_insertInputByKey` supplies the induction step. -/
theorem keyMass_groupInputs (inputs : List EdgeInput) :
    keyMass (groupInputs inputs) = keyMass inputs := by
  induction inputs with
  | nil => rfl
  | cons input inputs ih =>
      by_cases hzero : input.occurrenceNumerator = 0
      · simp only [groupInputs, hzero, if_true, keyMass]
        rw [ih]
        have hsingleton : singletonKeyMass input = 0 := by
          unfold singletonKeyMass
          rw [hzero]
          exact Finsupp.single_zero input.key
        rw [hsingleton, zero_add]
      · simp only [groupInputs, hzero, if_false]
        rw [keyMass_insertInputByKey]
        simp only [keyMass]
        rw [ih]

/-- Key mass is additive under concatenation.

This is the structural law used by a binary certificate merge tree: reassociation and
commutation happen in the additive `Finsupp`, not in the order-sensitive `groupInputs` output. -/
theorem keyMass_append (left right : List EdgeInput) :
    keyMass (left ++ right) = keyMass left + keyMass right := by
  induction left with
  | nil => simp [keyMass]
  | cons input left ih =>
      simp [keyMass, ih, add_assoc]

/-- A list permutation leaves the finite key-mass map unchanged. -/
private theorem keyMass_eq_of_perm {left right : List EdgeInput} (h : left.Perm right) :
    keyMass left = keyMass right := by
  have hsum (inputs : List EdgeInput) :
      keyMass inputs = (inputs.map singletonKeyMass).sum := by
    induction inputs with
    | nil => rfl
    | cons input inputs ih =>
        simp only [keyMass, List.map_cons, List.sum_cons, ih]
  rw [hsum left, hsum right]
  exact (h.map singletonKeyMass).sum_eq

namespace KeyMassEquivalent

/-- Every input list is key-mass equivalent to itself. -/
theorem refl (inputs : List EdgeInput) : KeyMassEquivalent inputs inputs := by
  exact Eq.refl (keyMass inputs)

/-- Key-mass equivalence is symmetric. -/
theorem symm {left right : List EdgeInput} (h : KeyMassEquivalent left right) :
    KeyMassEquivalent right left := by
  unfold KeyMassEquivalent at *
  exact h.symm

/-- Key-mass equivalence is transitive. -/
theorem trans {first second third : List EdgeInput}
    (h₁ : KeyMassEquivalent first second) (h₂ : KeyMassEquivalent second third) :
    KeyMassEquivalent first third := by
  unfold KeyMassEquivalent at *
  exact h₁.trans h₂

/-- Permuting input rows produces a key-mass equivalent list.

This theorem is the explicit order-independence law; the proof reduces adjacent swaps to
commutativity of addition in the finite key-mass map. -/
theorem of_perm {left right : List EdgeInput} (h : left.Perm right) :
    KeyMassEquivalent left right := by
  exact keyMass_eq_of_perm h

/-- Equivalent left and right pieces remain equivalent after concatenation.

Proof sketch: rewrite both concatenations with `keyMass_append`, then use equality congruence for
addition in the finite key-mass maps. -/
theorem append {left₁ left₂ right₁ right₂ : List EdgeInput}
    (hleft : KeyMassEquivalent left₁ left₂)
    (hright : KeyMassEquivalent right₁ right₂) :
    KeyMassEquivalent (left₁ ++ right₁) (left₂ ++ right₂) := by
  unfold KeyMassEquivalent at *
  calc
    keyMass (left₁ ++ right₁) = keyMass left₁ + keyMass right₁ :=
      keyMass_append left₁ right₁
    _ = keyMass left₂ + keyMass right₂ := by rw [hleft, hright]
    _ = keyMass (left₂ ++ right₂) := (keyMass_append left₂ right₂).symm

/-- A list and its executable grouped form have the same sufficient statistic. -/
theorem groupInputs_self (inputs : List EdgeInput) :
    KeyMassEquivalent (groupInputs inputs) inputs := by
  exact keyMass_groupInputs inputs

/-- Grouping respects key-mass equivalence on both sides. -/
theorem groupInputs_congr {left right : List EdgeInput}
    (h : KeyMassEquivalent left right) :
    KeyMassEquivalent (groupInputs left) (groupInputs right) := by
  unfold KeyMassEquivalent at *
  calc
    keyMass (groupInputs left) = keyMass left := keyMass_groupInputs left
    _ = keyMass right := h
    _ = keyMass (groupInputs right) := (keyMass_groupInputs right).symm

/-- A checked grouping equality implies order-independent equivalence with its output.

This is the certificate-facing constructor: a small leaf may prove
`groupInputs inputs = summary`, then larger nodes compose `inputs` and `summary` through the
relation without fixing one global output order. -/
theorem of_groupInputs_eq {inputs grouped : List EdgeInput}
    (h : groupInputs inputs = grouped) : KeyMassEquivalent inputs grouped := by
  unfold KeyMassEquivalent
  calc
    keyMass inputs = keyMass (groupInputs inputs) := (keyMass_groupInputs inputs).symm
    _ = keyMass grouped := congrArg keyMass h

/-- Splitting a list into the zero, one, and residual heavy-coordinate bands preserves key mass.

Proof sketch: induct over the source list and distinguish coordinate zero, coordinate one, and the
exhaustive residual case.  The selected input enters exactly one band.  In the latter two cases,
commutativity of addition moves its singleton mass past earlier bands; no coordinate-range premise
or executable decision proof is used. -/
theorem heavyBands (inputs : List EdgeInput) :
    KeyMassEquivalent inputs
      (heavyZeroBand inputs ++ heavyOneBand inputs ++ heavyResidualBand inputs) := by
  unfold KeyMassEquivalent
  induction inputs with
  | nil => rfl
  | cons input inputs ih =>
      by_cases hzero : input.heavyCoordinate = 0
      · simp [heavyZeroBand, heavyOneBand, heavyResidualBand, hzero, keyMass,
          keyMass_append, ih, add_assoc]
      · by_cases hone : input.heavyCoordinate = 1
        · simp [heavyZeroBand, heavyOneBand, heavyResidualBand, hzero, hone, keyMass,
            keyMass_append, ih, add_assoc, add_left_comm, add_comm]
        · simp [heavyZeroBand, heavyOneBand, heavyResidualBand, hzero, hone, keyMass,
            keyMass_append, ih, add_assoc, add_left_comm, add_comm]

/-- Merge two already partitioned summaries by grouping corresponding heavy-coordinate bands.

Each child hypothesis may come from a leaf's checked grouping equality plus `heavyBands`, or from a
smaller invocation of this theorem.  The three executable equalities remain small local checks.
The proof itself forgets order with `keyMass`, rearranges the six child masses additively, and uses
`of_groupInputs_eq` to replace each paired band by its checked output. -/
theorem mergeHeavyBands
    {leftSource rightSource : List EdgeInput}
    {leftZero leftOne leftResidual : List EdgeInput}
    {rightZero rightOne rightResidual : List EdgeInput}
    {outputZero outputOne outputResidual : List EdgeInput}
    (hleft : KeyMassEquivalent leftSource (leftZero ++ leftOne ++ leftResidual))
    (hright : KeyMassEquivalent rightSource (rightZero ++ rightOne ++ rightResidual))
    (hzero : groupInputs (leftZero ++ rightZero) = outputZero)
    (hone : groupInputs (leftOne ++ rightOne) = outputOne)
    (hresidual : groupInputs (leftResidual ++ rightResidual) = outputResidual) :
    KeyMassEquivalent (leftSource ++ rightSource)
      (outputZero ++ outputOne ++ outputResidual) := by
  have hzeroMass : KeyMassEquivalent (leftZero ++ rightZero) outputZero :=
    of_groupInputs_eq hzero
  have honeMass : KeyMassEquivalent (leftOne ++ rightOne) outputOne :=
    of_groupInputs_eq hone
  have hresidualMass : KeyMassEquivalent (leftResidual ++ rightResidual) outputResidual :=
    of_groupInputs_eq hresidual
  unfold KeyMassEquivalent at hleft hright hzeroMass honeMass hresidualMass ⊢
  calc
    keyMass (leftSource ++ rightSource) = keyMass leftSource + keyMass rightSource :=
      keyMass_append leftSource rightSource
    _ = keyMass (leftZero ++ leftOne ++ leftResidual) +
          keyMass (rightZero ++ rightOne ++ rightResidual) := by
      rw [hleft, hright]
    _ = keyMass (leftZero ++ rightZero) +
          (keyMass (leftOne ++ rightOne) + keyMass (leftResidual ++ rightResidual)) := by
      simp only [keyMass_append]
      ac_rfl
    _ = keyMass outputZero + (keyMass outputOne + keyMass outputResidual) := by
      rw [hzeroMass, honeMass, hresidualMass]
    _ = keyMass (outputZero ++ outputOne ++ outputResidual) := by
      simp only [keyMass_append, add_assoc]

end KeyMassEquivalent

/-! ## Semantic folds of key mass -/

/-- Total occurrence numerator represented by a finite key-mass map. -/
def keyMassOccurrenceTotal (massByKey : KeyMass) : Nat :=
  massByKey.sum fun _ occurrence => occurrence

/-- Summing the key-mass map recovers the existing list occurrence total.

Proof sketch: each singleton contributes its occurrence numerator and `Finsupp.sum` is additive,
so induction follows the recursive definitions of `keyMass` and `occurrenceTotal`. -/
theorem keyMassOccurrenceTotal_keyMass (inputs : List EdgeInput) :
    keyMassOccurrenceTotal (keyMass inputs) = occurrenceTotal inputs := by
  have hadd (left right : KeyMass) :
      keyMassOccurrenceTotal (left + right) =
        keyMassOccurrenceTotal left + keyMassOccurrenceTotal right := by
    unfold keyMassOccurrenceTotal
    apply Finsupp.sum_add_index'
    · intro key
      rfl
    · intro key leftOccurrence rightOccurrence
      rfl
  have hsingle (input : EdgeInput) :
      keyMassOccurrenceTotal (singletonKeyMass input) = input.occurrenceNumerator := by
    rcases input with ⟨occurrence, mu, heavy⟩
    unfold keyMassOccurrenceTotal singletonKeyMass EdgeInput.key
    exact Finsupp.sum_single_index rfl
  induction inputs with
  | nil => rfl
  | cons input inputs ih =>
      rw [keyMass, hadd, hsingle, ih]
      rfl

/-- Key-mass equivalent lists have the same exact occurrence total. -/
theorem KeyMassEquivalent.occurrenceTotal_eq {left right : List EdgeInput}
    (h : KeyMassEquivalent left right) :
    occurrenceTotal left = occurrenceTotal right := by
  unfold KeyMassEquivalent at h
  calc
    occurrenceTotal left = keyMassOccurrenceTotal (keyMass left) :=
      (keyMassOccurrenceTotal_keyMass left).symm
    _ = keyMassOccurrenceTotal (keyMass right) := congrArg keyMassOccurrenceTotal h
    _ = occurrenceTotal right := keyMassOccurrenceTotal_keyMass right

/-- Evaluate one retained-rate branch directly from a finite key-mass map. -/
def keyMassBranchRate (massByKey : KeyMass) (coordinate : Fin 3) : Real :=
  massByKey.sum fun key occurrence =>
    inputRate ⟨occurrence, key.1, key.2⟩ coordinate

/-- Evaluating a branch from key mass recovers the existing list branch rate.

Proof sketch: `inputRate_zero_occurrence` makes the finite-support sum zero-safe, and
`inputRate_combine_of_key_eq` proves additivity of the summand at each fixed key.  Induction then
factors `inputBranchRate` through `keyMass`. -/
theorem keyMassBranchRate_keyMass (inputs : List EdgeInput) (coordinate : Fin 3) :
    keyMassBranchRate (keyMass inputs) coordinate =
      inputBranchRate inputs coordinate := by
  have hadd (left right : KeyMass) :
      keyMassBranchRate (left + right) coordinate =
        keyMassBranchRate left coordinate + keyMassBranchRate right coordinate := by
    unfold keyMassBranchRate
    apply Finsupp.sum_add_index'
    · intro key
      exact inputRate_zero_occurrence key.1 key.2 coordinate
    · intro key leftOccurrence rightOccurrence
      simpa only [EdgeInput.combine] using
        (inputRate_combine_of_key_eq
          (⟨leftOccurrence, key.1, key.2⟩ : EdgeInput)
          (⟨rightOccurrence, key.1, key.2⟩ : EdgeInput) (by rfl) coordinate)
  have hsingle (input : EdgeInput) :
      keyMassBranchRate (singletonKeyMass input) coordinate = inputRate input coordinate := by
    rcases input with ⟨occurrence, mu, heavy⟩
    unfold keyMassBranchRate singletonKeyMass EdgeInput.key
    exact Finsupp.sum_single_index (inputRate_zero_occurrence mu heavy coordinate)
  induction inputs with
  | nil => rfl
  | cons input inputs ih =>
      rw [keyMass, hadd, hsingle, ih]
      rfl

/-- Key-mass equivalent lists have identical retained rates in every branch. -/
theorem KeyMassEquivalent.inputBranchRate_eq {left right : List EdgeInput}
    (h : KeyMassEquivalent left right) (coordinate : Fin 3) :
    inputBranchRate left coordinate = inputBranchRate right coordinate := by
  unfold KeyMassEquivalent at h
  calc
    inputBranchRate left coordinate = keyMassBranchRate (keyMass left) coordinate :=
      (keyMassBranchRate_keyMass left coordinate).symm
    _ = keyMassBranchRate (keyMass right) coordinate := by rw [h]
    _ = inputBranchRate right coordinate := keyMassBranchRate_keyMass right coordinate

end

end MatrixMultiplication.SimplifiedExponentRecurrence.Chunked
