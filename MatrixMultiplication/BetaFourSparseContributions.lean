/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import MatrixMultiplication.BetaFourLocalContributions
import MatrixMultiplication.DyadicNumeratorList

/-!
# Sparse canonical rows for routed beta-four contributions

`BetaFourLocalContributions` separates the expensive source routing from pointwise arithmetic.
For large paper certificates, however, checking every padded output position still repeats a scan
of the routed list, while reducing one persistent dense array creates a large kernel term.  This
module supplies a third representation: a sorted sparse row with one positive numerator per
occupied target.

Small routed rows are normalized independently, then combined by a linear merge.  The main
soundness theorem proves that expanding a canonical sparse row gives the original routed scatter,
and that deleting its zero padding leaves exactly the stored numerators.  Generated clients can
therefore certify only `(target, numerator)` pairs and never materialize a 1,107-cell intermediate
array inside a proof.
-/

namespace MatrixMultiplication.SimplifiedExponentLevelFourRecurrence

open MatrixMultiplication.BetaFourLocalGeometry
open MatrixMultiplication.DyadicEntropyForm

namespace BetaFourRoutedContribution

/-- Numerator represented by a sparse contribution row at one target. -/
def sparseNumeratorAt (row : List BetaFourRoutedContribution) (position : ℕ) : ℕ :=
  match row with
  | [] => 0
  | contribution :: tail =>
      (if contribution.target = position then contribution.numerator else 0) +
        sparseNumeratorAt tail position

/-- Insert one contribution into a target-sorted sparse row, combining an equal target.

Zero contributions are discarded.  The operation is semantically valid on every input row;
sortedness is needed only when clients want the result to be canonical. -/
def insertSparse (contribution : BetaFourRoutedContribution) :
    List BetaFourRoutedContribution → List BetaFourRoutedContribution
  | [] => if contribution.numerator = 0 then [] else [contribution]
  | head :: tail =>
      if contribution.numerator = 0 then head :: tail
      else if contribution.target < head.target then contribution :: head :: tail
      else if contribution.target = head.target then
        { target := head.target, numerator := head.numerator + contribution.numerator } :: tail
      else head :: insertSparse contribution tail

/-- Normalize one optional routed row by insertion into a sorted sparse row. -/
def normalizeSparse :
    List (Option BetaFourRoutedContribution) → List BetaFourRoutedContribution
  | [] => []
  | none :: tail => normalizeSparse tail
  | some contribution :: tail => insertSparse contribution (normalizeSparse tail)

/-- Merge two target-sorted sparse rows, adding numerators at common targets. -/
def mergeSparse : List BetaFourRoutedContribution → List BetaFourRoutedContribution →
    List BetaFourRoutedContribution
  | [], right => right
  | left, [] => left
  | leftHead :: leftTail, rightHead :: rightTail =>
      if leftHead.target < rightHead.target then
        leftHead :: mergeSparse leftTail (rightHead :: rightTail)
      else if rightHead.target < leftHead.target then
        rightHead :: mergeSparse (leftHead :: leftTail) rightTail
      else
        { target := leftHead.target,
          numerator := leftHead.numerator + rightHead.numerator } ::
            mergeSparse leftTail rightTail
termination_by left right => left.length + right.length

/-- Normalize small routed rows independently and merge their sparse results. -/
def canonicalizeRows (rows : List (List (Option BetaFourRoutedContribution))) :
    List BetaFourRoutedContribution :=
  (rows.map normalizeSparse).foldl mergeSparse []

/-- A sparse row whose targets are strictly increasing, positive, and within one half-open range.

The recursive lower bound makes the invariant convenient for the zero-padding proof: after the
head target is consumed, the tail is canonical starting at the next position. -/
def IsCanonicalFrom (start limit : ℕ) : List BetaFourRoutedContribution → Prop
  | [] => True
  | contribution :: tail =>
      start ≤ contribution.target ∧
      contribution.target < limit ∧
      0 < contribution.numerator ∧
      IsCanonicalFrom (contribution.target + 1) limit tail

/-- Every present routed contribution targets a genuine slot below `limit`.

Unlike `IsCanonicalFrom`, this predicate neither sorts nor combines the input.  It is the small
sentinel-safety check used before canonicalization: `List.idxOf` returns the list length for an
absent word, so checking against the actual support length rules out that failure mode even when
the surrounding dense row has a larger padded width. -/
def AllTargetsBelow (limit : ℕ) : List (Option BetaFourRoutedContribution) → Prop
  | [] => True
  | none :: tail => AllTargetsBelow limit tail
  | some contribution :: tail =>
      contribution.target < limit ∧ AllTargetsBelow limit tail

/-- Routed-target validity is decidable by a linear scan of the inert route list. -/
instance decidableAllTargetsBelow (limit : ℕ)
    (row : List (Option BetaFourRoutedContribution)) : Decidable (AllTargetsBelow limit row) := by
  induction row with
  | nil => exact isTrue trivial
  | cons contribution tail ih =>
      cases contribution with
      | none => simpa [AllTargetsBelow] using ih
      | some contribution =>
          simp only [AllTargetsBelow]
          infer_instance

/-- Every present contribution in an `AllTargetsBelow` row has an in-range target. -/
theorem AllTargetsBelow.target_lt_of_mem {limit : ℕ}
    {row : List (Option BetaFourRoutedContribution)} (hvalid : AllTargetsBelow limit row)
    {contribution : BetaFourRoutedContribution} (hmem : some contribution ∈ row) :
    contribution.target < limit := by
  induction row with
  | nil => simp at hmem
  | cons head tail ih =>
      cases head with
      | none =>
          simp only [AllTargetsBelow] at hvalid
          simp only [List.mem_cons, reduceCtorEq, false_or] at hmem
          exact ih hvalid hmem
      | some head =>
          simp only [AllTargetsBelow] at hvalid
          rcases hvalid with ⟨hhead, htail⟩
          simp only [List.mem_cons, Option.some.injEq] at hmem
          rcases hmem with rfl | hmem
          · exact hhead
          · exact ih htail hmem

/-- Canonical sparse-row validity is decidable by a linear scan. -/
instance decidableIsCanonicalFrom (start limit : ℕ)
    (row : List BetaFourRoutedContribution) : Decidable (IsCanonicalFrom start limit row) := by
  induction row generalizing start with
  | nil => exact isTrue trivial
  | cons contribution tail ih =>
      letI : Decidable (IsCanonicalFrom (contribution.target + 1) limit tail) :=
        ih (contribution.target + 1)
      simp only [IsCanonicalFrom]
      infer_instance

/-- Expand a canonical sparse row over `count` consecutive positions starting at `start`. -/
def expandSparseFrom : ℕ → ℕ → List BetaFourRoutedContribution → List ℕ
  | _, 0, _ => []
  | start, count + 1, [] => 0 :: expandSparseFrom (start + 1) count []
  | start, count + 1, contribution :: tail =>
      if contribution.target = start then
        contribution.numerator :: expandSparseFrom (start + 1) count tail
      else
        0 :: expandSparseFrom (start + 1) count (contribution :: tail)

/-- Sparse evaluation of an inserted contribution adds exactly its requested point mass. -/
theorem sparseNumeratorAt_insertSparse (contribution : BetaFourRoutedContribution)
    (row : List BetaFourRoutedContribution) (position : ℕ) :
    sparseNumeratorAt (insertSparse contribution row) position =
      sparseNumeratorAt row position +
        if contribution.target = position then contribution.numerator else 0 := by
  induction row with
  | nil =>
      by_cases hzero : contribution.numerator = 0 <;>
        simp [insertSparse, sparseNumeratorAt, hzero]
  | cons head tail ih =>
      by_cases hzero : contribution.numerator = 0
      · simp [insertSparse, sparseNumeratorAt, hzero]
      · by_cases hlt : contribution.target < head.target
        · rw [insertSparse]
          simp only [hzero, hlt, ↓reduceIte]
          by_cases hcontribution : contribution.target = position <;>
            by_cases hhead : head.target = position <;>
            simp [sparseNumeratorAt, hcontribution, hhead] <;> omega
        · by_cases heq : contribution.target = head.target
          · rw [insertSparse]
            simp only [hzero, heq, ↓reduceIte]
            by_cases hcontribution : contribution.target = position <;>
              by_cases hhead : head.target = position <;>
              simp [sparseNumeratorAt, hhead] <;> omega
          · rw [insertSparse]
            simp only [hzero, hlt, heq, ↓reduceIte]
            by_cases hcontribution : contribution.target = position <;>
              by_cases hhead : head.target = position <;>
              simp [sparseNumeratorAt, hcontribution, hhead, ih] <;> omega

/-- Merging sparse rows adds their represented numerators pointwise. -/
theorem sparseNumeratorAt_mergeSparse (left right : List BetaFourRoutedContribution)
    (position : ℕ) :
    sparseNumeratorAt (mergeSparse left right) position =
      sparseNumeratorAt left position + sparseNumeratorAt right position := by
  fun_induction mergeSparse left right <;>
    simp_all [sparseNumeratorAt, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  case case5 leftHead leftTail rightHead rightTail hright hleft ih =>
    have htarget : leftHead.target = rightHead.target := by omega
    by_cases hposition : rightHead.target = position <;>
      simp [htarget, hposition] <;> omega

/-- Filtering optional routes does not change their pointwise routed numerator. -/
theorem sparseNumeratorAt_filterMap_eq_numeratorAt
    (contributions : List (Option BetaFourRoutedContribution)) (position : ℕ) :
    sparseNumeratorAt (contributions.filterMap id) position =
      numeratorAt contributions position := by
  unfold numeratorAt
  have hfold (values : List (Option BetaFourRoutedContribution)) (initial : ℕ) :
      values.foldl (addOptionalAt position) initial =
        initial + sparseNumeratorAt (values.filterMap id) position := by
    induction values generalizing initial with
    | nil => simp [sparseNumeratorAt]
    | cons value values ih =>
        cases value with
        | none => simpa [addOptionalAt] using ih initial
        | some contribution =>
            rw [List.foldl_cons, ih]
            by_cases htarget : contribution.target = position <;>
              simp [addOptionalAt, sparseNumeratorAt, htarget, Nat.add_assoc]
  simpa using (hfold contributions 0).symm

/-- Normalizing one routed row preserves its pointwise numerator. -/
theorem sparseNumeratorAt_normalizeSparse
    (contributions : List (Option BetaFourRoutedContribution)) (position : ℕ) :
    sparseNumeratorAt (normalizeSparse contributions) position =
      numeratorAt contributions position := by
  calc
    sparseNumeratorAt (normalizeSparse contributions) position =
        sparseNumeratorAt (contributions.filterMap id) position := by
      induction contributions with
      | nil => rfl
      | cons contribution tail ih =>
          cases contribution with
          | none => simpa [normalizeSparse] using ih
          | some contribution =>
              rw [normalizeSparse, sparseNumeratorAt_insertSparse, ih]
              by_cases htarget : contribution.target = position <;>
                simp [sparseNumeratorAt, htarget, Nat.add_comm]
    _ = numeratorAt contributions position :=
      sparseNumeratorAt_filterMap_eq_numeratorAt contributions position

/-- Sparse numerator evaluation distributes over row concatenation. -/
theorem sparseNumeratorAt_append (left right : List BetaFourRoutedContribution)
    (position : ℕ) :
    sparseNumeratorAt (left ++ right) position =
      sparseNumeratorAt left position + sparseNumeratorAt right position := by
  induction left with
  | nil => simp [sparseNumeratorAt]
  | cons head tail ih =>
      simp [sparseNumeratorAt, ih, Nat.add_assoc]

/-- Routed numerator evaluation distributes over route-list concatenation. -/
theorem numeratorAt_append (left right : List (Option BetaFourRoutedContribution))
    (position : ℕ) :
    numeratorAt (left ++ right) position =
      numeratorAt left position + numeratorAt right position := by
  rw [← sparseNumeratorAt_filterMap_eq_numeratorAt,
    List.filterMap_append, sparseNumeratorAt_append,
    sparseNumeratorAt_filterMap_eq_numeratorAt,
    sparseNumeratorAt_filterMap_eq_numeratorAt]

/-- Canonicalizing routed rows preserves the pointwise numerator of their concatenation. -/
theorem sparseNumeratorAt_canonicalizeRows
    (rows : List (List (Option BetaFourRoutedContribution))) (position : ℕ) :
    sparseNumeratorAt (canonicalizeRows rows) position =
      numeratorAt rows.flatten position := by
  unfold canonicalizeRows
  have hfold (normalized : List (List BetaFourRoutedContribution))
      (accumulator : List BetaFourRoutedContribution) :
      sparseNumeratorAt (normalized.foldl mergeSparse accumulator) position =
        sparseNumeratorAt accumulator position +
          (normalized.map fun row ↦ sparseNumeratorAt row position).sum := by
    induction normalized generalizing accumulator with
    | nil => simp
    | cons row rows ih =>
        rw [List.foldl_cons, ih, sparseNumeratorAt_mergeSparse]
        simp only [List.map_cons, List.sum_cons]
        omega
  rw [hfold]
  simp only [sparseNumeratorAt, Nat.zero_add]
  induction rows with
  | nil => rfl
  | cons row rows ih =>
      simp only [List.map_cons, List.sum_cons, List.flatten_cons]
      rw [sparseNumeratorAt_normalizeSparse, ih, numeratorAt_append]

private theorem sparseNumeratorAt_eq_zero_of_forall_ne
    (row : List BetaFourRoutedContribution) (position : ℕ)
    (hrow : ∀ contribution ∈ row, contribution.target ≠ position) :
    sparseNumeratorAt row position = 0 := by
  induction row with
  | nil => rfl
  | cons head tail ih =>
      have hhead := hrow head (by simp)
      have htail : ∀ contribution ∈ tail, contribution.target ≠ position := by
        intro contribution hmem
        exact hrow contribution (by simp [hmem])
      simp only [sparseNumeratorAt, hhead, if_false, Nat.zero_add]
      exact ih htail

/-- Every target in a canonical row lies at or after its recursive start. -/
theorem IsCanonicalFrom.target_ge_of_mem {start limit : ℕ}
    {row : List BetaFourRoutedContribution} (hcanonical : IsCanonicalFrom start limit row)
    {contribution : BetaFourRoutedContribution} (hmem : contribution ∈ row) :
    start ≤ contribution.target := by
  induction row generalizing start with
  | nil => simp at hmem
  | cons head tail ih =>
      simp only [IsCanonicalFrom] at hcanonical
      rcases hcanonical with ⟨hstart, hlimit, hpositive, htail⟩
      rcases List.mem_cons.mp hmem with rfl | hmem
      · exact hstart
      · exact le_trans (by omega) (ih htail hmem)

/-- Every target in a canonical row lies below its common limit. -/
theorem IsCanonicalFrom.target_lt_of_mem {start limit : ℕ}
    {row : List BetaFourRoutedContribution} (hcanonical : IsCanonicalFrom start limit row)
    {contribution : BetaFourRoutedContribution} (hmem : contribution ∈ row) :
    contribution.target < limit := by
  induction row generalizing start with
  | nil => simp at hmem
  | cons head tail ih =>
      simp only [IsCanonicalFrom] at hcanonical
      rcases hcanonical with ⟨hstart, hlimit, hpositive, htail⟩
      rcases List.mem_cons.mp hmem with rfl | hmem
      · exact hlimit
      · exact ih htail hmem

/-- Every numerator in a canonical sparse row is positive. -/
theorem IsCanonicalFrom.numerator_pos_of_mem {start limit : ℕ}
    {row : List BetaFourRoutedContribution} (hcanonical : IsCanonicalFrom start limit row)
    {contribution : BetaFourRoutedContribution} (hmem : contribution ∈ row) :
    0 < contribution.numerator := by
  induction row generalizing start with
  | nil => simp at hmem
  | cons head tail ih =>
      simp only [IsCanonicalFrom] at hcanonical
      rcases hcanonical with ⟨hstart, hlimit, hpositive, htail⟩
      rcases List.mem_cons.mp hmem with rfl | hmem
      · exact hpositive
      · exact ih htail hmem

private theorem sparseNumeratorAt_head
    {start limit : ℕ} {head : BetaFourRoutedContribution}
    {tail : List BetaFourRoutedContribution}
    (hcanonical : IsCanonicalFrom start limit (head :: tail)) :
    sparseNumeratorAt (head :: tail) start =
      if head.target = start then head.numerator else 0 := by
  simp only [IsCanonicalFrom] at hcanonical
  rcases hcanonical with ⟨hstart, hlimit, hpositive, htail⟩
  by_cases heq : head.target = start
  · have hzero : sparseNumeratorAt tail start = 0 := by
      apply sparseNumeratorAt_eq_zero_of_forall_ne
      intro contribution hmem heqTarget
      have hge := htail.target_ge_of_mem hmem
      omega
    simp only [sparseNumeratorAt, heq, if_pos]
    rw [hzero, Nat.add_zero]
  · have hzero : sparseNumeratorAt (head :: tail) start = 0 := by
      apply sparseNumeratorAt_eq_zero_of_forall_ne
      intro contribution hmem heqTarget
      have hge := (show IsCanonicalFrom start limit (head :: tail) from
        ⟨hstart, hlimit, hpositive, htail⟩).target_ge_of_mem hmem
      rcases List.mem_cons.mp hmem with hEq | hmem
      · subst contribution
        exact heq heqTarget
      · have htailGe := htail.target_ge_of_mem hmem
        omega
    simp [heq, hzero]

/-- Expanding a canonical row agrees with evaluating its sparse numerator at each position. -/
theorem expandSparseFrom_eq_map_range'
    (start count : ℕ) (row : List BetaFourRoutedContribution)
    (hcanonical : IsCanonicalFrom start (start + count) row) :
    expandSparseFrom start count row =
      (List.range' start count).map (sparseNumeratorAt row) := by
  induction count generalizing start row with
  | zero =>
      cases row with
      | nil => rfl
      | cons head tail =>
          simp only [IsCanonicalFrom] at hcanonical
          omega
  | succ count ih =>
      cases row with
      | nil =>
          simp only [expandSparseFrom, List.range'_succ, List.map_cons,
            sparseNumeratorAt]
          rw [ih (start + 1) []]
          · rfl
          · simp [IsCanonicalFrom]
      | cons head tail =>
          rcases head with ⟨headTarget, headNumerator⟩
          simp only [IsCanonicalFrom] at hcanonical
          rcases hcanonical with ⟨hstart, hlimit, hpositive, htail⟩
          have hwhole : IsCanonicalFrom start (start + (count + 1))
              (⟨headTarget, headNumerator⟩ :: tail) :=
            ⟨hstart, hlimit, hpositive, htail⟩
          by_cases heq : headTarget = start
          · subst headTarget
            have htail' : IsCanonicalFrom (start + 1) ((start + 1) + count) tail := by
              convert htail using 1
              all_goals omega
            rw [show expandSparseFrom start (count + 1)
                (⟨start, headNumerator⟩ :: tail) =
                headNumerator :: expandSparseFrom (start + 1) count tail by
              simp [expandSparseFrom]]
            rw [List.range'_succ, List.map_cons, sparseNumeratorAt_head hwhole,
              if_pos rfl, ih (start + 1) tail htail']
            congr 1
            apply List.map_congr_left
            intro position hposition
            have hmem := List.mem_range'.mp hposition
            rcases hmem with ⟨index, hindex, rfl⟩
            simp [sparseNumeratorAt]
            omega
          · have hheadNext : start + 1 ≤ headTarget := by omega
            have htail' :
                IsCanonicalFrom (headTarget + 1) ((start + 1) + count) tail := by
              convert htail using 1
              all_goals omega
            have hwhole' :
                IsCanonicalFrom (start + 1) ((start + 1) + count)
                  (⟨headTarget, headNumerator⟩ :: tail) := by
              refine ⟨hheadNext, ?_, hpositive, htail'⟩
              change headTarget < (start + 1) + count
              omega
            rw [show expandSparseFrom start (count + 1)
                (⟨headTarget, headNumerator⟩ :: tail) =
                0 :: expandSparseFrom (start + 1) count
                  (⟨headTarget, headNumerator⟩ :: tail) by
              simp [expandSparseFrom, heq]]
            rw [List.range'_succ, List.map_cons, sparseNumeratorAt_head hwhole,
              if_neg heq, ih (start + 1) (⟨headTarget, headNumerator⟩ :: tail) hwhole']

/-- Deleting the zero padding of an expanded canonical row leaves its numerators in target order. -/
theorem dropZeros_expandSparseFrom
    (start count : ℕ) (row : List BetaFourRoutedContribution)
    (hcanonical : IsCanonicalFrom start (start + count) row) :
    dropZeros (expandSparseFrom start count row) = row.map (·.numerator) := by
  induction count generalizing start row with
  | zero =>
      cases row with
      | nil => rfl
      | cons head tail =>
          simp only [IsCanonicalFrom] at hcanonical
          omega
  | succ count ih =>
      cases row with
      | nil =>
          simp only [expandSparseFrom, dropZeros, List.map_nil]
          exact ih (start + 1) [] (by simp [IsCanonicalFrom])
      | cons head tail =>
          rcases head with ⟨headTarget, headNumerator⟩
          simp only [IsCanonicalFrom] at hcanonical
          rcases hcanonical with ⟨hstart, hlimit, hpositive, htail⟩
          by_cases heq : headTarget = start
          · subst headTarget
            have htail' : IsCanonicalFrom (start + 1) ((start + 1) + count) tail := by
              convert htail using 1
              all_goals omega
            obtain ⟨numerator, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hpositive)
            simp only [expandSparseFrom, ↓reduceIte, dropZeros, List.map_cons,
              List.cons.injEq, true_and]
            exact ih (start + 1) tail htail'
          · have hheadNext : start + 1 ≤ headTarget := by omega
            have htail' :
                IsCanonicalFrom (headTarget + 1) ((start + 1) + count) tail := by
              convert htail using 1
              all_goals omega
            have hwhole' :
                IsCanonicalFrom (start + 1) ((start + 1) + count)
                  (⟨headTarget, headNumerator⟩ :: tail) := by
              refine ⟨hheadNext, ?_, hpositive, htail'⟩
              change headTarget < (start + 1) + count
              omega
            simp only [expandSparseFrom, heq, ↓reduceIte, dropZeros]
            exact ih (start + 1) (⟨headTarget, headNumerator⟩ :: tail) hwhole'

/-- A checked canonical sparse row is a complete compact certificate for a routed padded row.

Proof sketch: canonicalization preserves every pointwise numerator.  The canonical row expands to
those pointwise values over the requested range, and its strict positive target order means that
removing zero padding leaves exactly the stored numerators. -/
theorem dropZeros_scatterOn_range_eq_map_numerator_of_canonicalizeRows_eq
    (rows : List (List (Option BetaFourRoutedContribution)))
    (width : ℕ) (canonical : List BetaFourRoutedContribution)
    (heq : canonicalizeRows rows = canonical)
    (hcanonical : IsCanonicalFrom 0 width canonical) :
    dropZeros (scatterOn rows.flatten (List.range width)) =
      canonical.map (·.numerator) := by
  have hscatter :
      scatterOn rows.flatten (List.range width) =
        (List.range width).map (sparseNumeratorAt canonical) := by
    unfold scatterOn
    apply List.map_congr_left
    intro position hposition
    rw [← sparseNumeratorAt_canonicalizeRows rows position, heq]
  rw [hscatter, List.range_eq_range']
  rw [← expandSparseFrom_eq_map_range' 0 width canonical (by simpa using hcanonical)]
  exact dropZeros_expandSparseFrom 0 width canonical (by simpa using hcanonical)

end BetaFourRoutedContribution

end MatrixMultiplication.SimplifiedExponentLevelFourRecurrence
