/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Combinatorics.FinpartitionBellCard
import AlgebraicComplexity.Examples.CoppersmithWinogradTightQuotientClassification
import Mathlib.Tactic.NormNum

/-!
# Counting tight depth-one Coppersmith--Winograd quotients

The structural classification gives ten normalized kernel partitions.  This file proves that
they are pairwise distinct by explicit collision tests, turns the classification into an
equivalence, and obtains the literal cardinality ten.  The denominator 21,147 follows from the
Bell-number decoder in `FinpartitionBellCard`; no `Fintype` enumeration of finite partitions is
evaluated.  It then decomposes total-preserving partitions over the five total-weight fibers,
proves the exact counts `20` per leg and `8000` legwise, and identifies by explicit collisions the
two candidates whose quotient support remains tight.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor MoreAsymmetryCompatibility

private theorem cwTightQuotientKind_partition_eq_rel
    {left right : CWTightQuotientKind} (h : left.partition = right.partition)
    (a b : SplitWord 1) :
    (cwSplitLinearForm left.coefficients.1 left.coefficients.2 a =
        cwSplitLinearForm left.coefficients.1 left.coefficients.2 b) ↔
      (cwSplitLinearForm right.coefficients.1 right.coefficients.2 a =
        cwSplitLinearForm right.coefficients.1 right.coefficients.2 b) := by
  have hleft := cwLinearFinpartition_part_eq_part
    left.coefficients.1 left.coefficients.2 a b
  have hright := cwLinearFinpartition_part_eq_part
    right.coefficients.1 right.coefficients.2 a b
  rw [← hleft, ← hright]
  change (left.partition.part a = left.partition.part b) ↔
    (right.partition.part a = right.partition.part b)
  rw [h]

/-- The ten normalized coefficient pairs induce ten distinct fiber partitions. -/
theorem cwTightQuotientKind_partition_injective :
    Function.Injective CWTightQuotientKind.partition := by
  intro left right hpartition
  have h10 := cwTightQuotientKind_partition_eq_rel hpartition
    (cwSplitPair 1 0) (cwSplitPair 0 0)
  have h01 := cwTightQuotientKind_partition_eq_rel hpartition
    (cwSplitPair 0 1) (cwSplitPair 0 0)
  have h1n1 := cwTightQuotientKind_partition_eq_rel hpartition
    (cwSplitPair 1 0) (cwSplitPair 0 1)
  have h11 := cwTightQuotientKind_partition_eq_rel hpartition
    (cwSplitPair 1 1) (cwSplitPair 0 0)
  have h1n2 := cwTightQuotientKind_partition_eq_rel hpartition
    (cwSplitPair 1 0) (cwSplitPair 0 2)
  have h12 := cwTightQuotientKind_partition_eq_rel hpartition
    (cwSplitPair 1 2) (cwSplitPair 0 0)
  have h2n1 := cwTightQuotientKind_partition_eq_rel hpartition
    (cwSplitPair 2 0) (cwSplitPair 0 1)
  have h21 := cwTightQuotientKind_partition_eq_rel hpartition
    (cwSplitPair 2 1) (cwSplitPair 0 0)
  clear hpartition
  cases left with
  | constant =>
      cases right <;>
        norm_num [CWTightQuotientKind.coefficients, cwSplitLinearForm, cwSplitPair] at *
  | firstCoordinate =>
      cases right <;>
        norm_num [CWTightQuotientKind.coefficients, cwSplitLinearForm, cwSplitPair] at *
  | secondCoordinate =>
      cases right <;>
        norm_num [CWTightQuotientKind.coefficients, cwSplitLinearForm, cwSplitPair] at *
  | sum =>
      cases right <;>
        norm_num [CWTightQuotientKind.coefficients, cwSplitLinearForm, cwSplitPair] at *
  | difference =>
      cases right <;>
        norm_num [CWTightQuotientKind.coefficients, cwSplitLinearForm, cwSplitPair] at *
  | twoFirstPlusSecond =>
      cases right <;>
        norm_num [CWTightQuotientKind.coefficients, cwSplitLinearForm, cwSplitPair] at *
  | negativeTwoFirstPlusSecond =>
      cases right <;>
        norm_num [CWTightQuotientKind.coefficients, cwSplitLinearForm, cwSplitPair] at *
  | firstPlusTwoSecond =>
      cases right <;>
        norm_num [CWTightQuotientKind.coefficients, cwSplitLinearForm, cwSplitPair] at *
  | firstMinusTwoSecond =>
      cases right <;>
        norm_num [CWTightQuotientKind.coefficients, cwSplitLinearForm, cwSplitPair] at *
  | discrete =>
      cases right <;>
        norm_num [CWTightQuotientKind.coefficients, cwSplitLinearForm, cwSplitPair] at *

/-- A partition of the nine depth-one split words whose quotient support is tight. -/
abbrev CWTightSamePartition :=
  {P : Finpartition (Finset.univ : Finset (SplitWord 1)) //
    IsTightSupport (cwSamePartitionQuotientSupport P)}

namespace CWTightSamePartition

/-- The unique normalized kind represented by a tight same-partition quotient. -/
noncomputable def kind (P : CWTightSamePartition) : CWTightQuotientKind :=
  Classical.choose ((cwSamePartitionQuotientSupport_isTight_iff_kind P.1).mp P.2)

/-- The chosen normalized kind reconstructs the original tight partition. -/
theorem eq_kind_partition (P : CWTightSamePartition) : P.1 = P.kind.partition :=
  Classical.choose_spec ((cwSamePartitionQuotientSupport_isTight_iff_kind P.1).mp P.2)

end CWTightSamePartition

/-- Tight same-partition quotients are equivalent to the ten normalized kernel kinds. -/
noncomputable def cwTightQuotientKindEquiv :
    CWTightQuotientKind ≃ CWTightSamePartition where
  toFun kind :=
    ⟨kind.partition,
      (cwSamePartitionQuotientSupport_isTight_iff_kind kind.partition).mpr
        ⟨kind, rfl⟩⟩
  invFun := CWTightSamePartition.kind
  left_inv kind := by
    apply cwTightQuotientKind_partition_injective
    exact (CWTightSamePartition.eq_kind_partition _).symm
  right_inv P := by
    apply Subtype.ext
    exact (CWTightSamePartition.eq_kind_partition P).symm

noncomputable instance : Fintype CWTightSamePartition :=
  Fintype.ofEquiv CWTightQuotientKind cwTightQuotientKindEquiv

private def cwTightQuotientKindCode : CWTightQuotientKind → Fin 10
  | .constant => 0
  | .firstCoordinate => 1
  | .secondCoordinate => 2
  | .sum => 3
  | .difference => 4
  | .twoFirstPlusSecond => 5
  | .negativeTwoFirstPlusSecond => 6
  | .firstPlusTwoSecond => 7
  | .firstMinusTwoSecond => 8
  | .discrete => 9

private def cwTightQuotientKindOfCode (i : Fin 10) : CWTightQuotientKind :=
  match i.1 with
  | 0 => .constant
  | 1 => .firstCoordinate
  | 2 => .secondCoordinate
  | 3 => .sum
  | 4 => .difference
  | 5 => .twoFirstPlusSecond
  | 6 => .negativeTwoFirstPlusSecond
  | 7 => .firstPlusTwoSecond
  | 8 => .firstMinusTwoSecond
  | _ => .discrete

private def cwTightQuotientKindEquivFin : CWTightQuotientKind ≃ Fin 10 where
  toFun := cwTightQuotientKindCode
  invFun := cwTightQuotientKindOfCode
  left_inv kind := by cases kind <;> rfl
  right_inv i := by
    apply Fin.ext
    fin_cases i <;> rfl

/-- There are ten normalized tight quotient kinds. -/
theorem fintypeCard_cwTightQuotientKind : Fintype.card CWTightQuotientKind = 10 := by
  simpa using Fintype.card_congr cwTightQuotientKindEquivFin

/-- Exactly ten partitions of the nine words give a tight same-partition quotient support. -/
theorem fintypeCard_cwTightSamePartition : Fintype.card CWTightSamePartition = 10 := by
  calc
    Fintype.card CWTightSamePartition = Fintype.card CWTightQuotientKind :=
      Fintype.card_congr cwTightQuotientKindEquiv.symm
    _ = 10 := fintypeCard_cwTightQuotientKind

/-- There are 21,147 partitions of the nine depth-one split words. -/
theorem fintypeCard_cwDepthOneFinpartition :
    Fintype.card (Finpartition (Finset.univ : Finset (SplitWord 1))) = 21147 := by
  calc
    Fintype.card (Finpartition (Finset.univ : Finset (SplitWord 1))) =
        Nat.bell (Finset.univ : Finset (SplitWord 1)).card :=
      FinpartitionBellCard.fintypeCard_finpartition_eq_bell _
    _ = Nat.bell 9 := by norm_num
    _ = 21147 := by
      norm_num [Nat.bell, Nat.choose, ← Nat.range_succ_eq_Iic, Finset.sum_range_succ]

/-! ## Total-preserving partitions

A total-preserving partition is assembled independently on the five fibers of
`cwSplitWordTotalDigit 1`.  The equivalence below is an actual encoder/decoder: restrict a
partition to each fiber, or recover the global partition as the kernel of the pair consisting of
the total and the local part.  This avoids evaluating the double-powerset `Fintype` instance for
finite partitions. -/

/-- The depth-one words of one fixed total weight. -/
def cwDepthOneTotalFiber (total : CWCoarseDigit 1) : Finset (SplitWord 1) :=
  Finset.univ.filter fun word ↦ cwSplitWordTotalDigit 1 word = total

@[simp] theorem mem_cwDepthOneTotalFiber (total : CWCoarseDigit 1) (word : SplitWord 1) :
    word ∈ cwDepthOneTotalFiber total ↔ cwSplitWordTotalDigit 1 word = total := by
  simp [cwDepthOneTotalFiber]

private theorem cwDepthOneTotalFiber_subset_univ (total : CWCoarseDigit 1) :
    cwDepthOneTotalFiber total ⊆ (Finset.univ : Finset (SplitWord 1)) := by
  simp

/-- A partition is total-preserving when no part contains words of different total weights. -/
def CWTotalPreservingPartition
    (P : Finpartition (Finset.univ : Finset (SplitWord 1))) : Prop :=
  ∀ left right, P.part left = P.part right →
    splitWordWeight left = splitWordWeight right

/-- The finite type of total-preserving partitions of the nine depth-one words. -/
abbrev CWTotalPreservingFinpartition :=
  {P : Finpartition (Finset.univ : Finset (SplitWord 1)) //
    CWTotalPreservingPartition P}

private theorem cwDepthOneFinpartition_eq_of_part_rel
    {s : Finset (SplitWord 1)} {P Q : Finpartition s}
    (hrel : ∀ left, left ∈ s → ∀ right, right ∈ s →
      (P.part left = P.part right ↔ Q.part left = Q.part right)) :
    P = Q := by
  have hpart (word : SplitWord 1) (hword : word ∈ s) : P.part word = Q.part word := by
    apply Finset.ext
    intro other
    by_cases hother : other ∈ s
    · rw [P.mem_part_iff_part_eq_part hother hword]
      rw [Q.mem_part_iff_part_eq_part hother hword]
      exact hrel other hother word hword
    · have hnotP : other ∉ P.part word :=
        fun hmem ↦ hother (P.part_subset word hmem)
      have hnotQ : other ∉ Q.part word :=
        fun hmem ↦ hother (Q.part_subset word hmem)
      simp [hnotP, hnotQ]
  apply Finpartition.ext
  apply Finset.ext
  intro part
  constructor
  · intro hP
    obtain ⟨word, hword⟩ := P.nonempty_of_mem_parts hP
    have hwordSupport : word ∈ s := P.le hP hword
    have hp := P.part_eq_of_mem hP hword
    rw [← hp, hpart word hwordSupport]
    exact Q.part_mem.mpr hwordSupport
  · intro hQ
    obtain ⟨word, hword⟩ := Q.nonempty_of_mem_parts hQ
    have hwordSupport : word ∈ s := Q.le hQ hword
    have hq := Q.part_eq_of_mem hQ hword
    rw [← hq, ← hpart word hwordSupport]
    exact P.part_mem.mpr hwordSupport

private theorem cwFinpartition_restrict_part_eq_part_iff
    (P : Finpartition (Finset.univ : Finset (SplitWord 1)))
    {s : Finset (SplitWord 1)} (hs : s ⊆ Finset.univ)
    {left right : SplitWord 1} (hleft : left ∈ s) (hright : right ∈ s) :
    (P.restrict hs).part left = (P.restrict hs).part right ↔
      P.part left = P.part right := by
  have hpart (word : SplitWord 1) (hword : word ∈ s) :
      (P.restrict hs).part word = P.part word ∩ s := by
    apply (P.restrict hs).part_eq_of_mem
    · simp only [Finpartition.restrict, Finset.mem_erase, Finset.mem_image]
      refine ⟨?_, ⟨P.part word, P.part_mem.mpr (hs hword), rfl⟩⟩
      intro hempty
      have hmem : word ∈ P.part word ∩ s :=
        Finset.mem_inter.mpr ⟨P.mem_part (hs hword), hword⟩
      simp [hempty] at hmem
    · exact Finset.mem_inter.mpr ⟨P.mem_part (hs hword), hword⟩
  rw [hpart left hleft, hpart right hright]
  constructor
  · intro hinter
    apply P.part_eq_of_mem (P.part_mem.mpr (hs hright))
    have hmem : left ∈ P.part left ∩ s :=
      Finset.mem_inter.mpr ⟨P.mem_part (hs hleft), hleft⟩
    rw [hinter] at hmem
    exact (Finset.mem_inter.mp hmem).1
  · intro hpartEq
    rw [hpartEq]

/-- Restrict a total-preserving partition to each of its five total fibers. -/
noncomputable def cwTotalFiberRestrictions
    (P : CWTotalPreservingFinpartition) (total : CWCoarseDigit 1) :
    Finpartition (cwDepthOneTotalFiber total) :=
  P.1.restrict (cwDepthOneTotalFiber_subset_univ total)

/-- The explicit decoder for a family of partitions of the five total fibers. -/
noncomputable def cwTotalFiberFamilyLabel
    (Q : ∀ total : CWCoarseDigit 1, Finpartition (cwDepthOneTotalFiber total))
    (word : SplitWord 1) : CWCoarseDigit 1 × Finset (SplitWord 1) :=
  let total := cwSplitWordTotalDigit 1 word
  (total, (Q total).part word)

/-- Recover a global partition by remembering both the total and the local fiber part. -/
noncomputable def cwTotalFiberFamilyPartition
    (Q : ∀ total : CWCoarseDigit 1, Finpartition (cwDepthOneTotalFiber total)) :
    Finpartition (Finset.univ : Finset (SplitWord 1)) := by
  classical
  exact Finpartition.ofSetoid (Setoid.ker (cwTotalFiberFamilyLabel Q))

private theorem cwTotalFiberFamilyPartition_part_eq_part
    (Q : ∀ total : CWCoarseDigit 1, Finpartition (cwDepthOneTotalFiber total))
    (left right : SplitWord 1) :
    (cwTotalFiberFamilyPartition Q).part left =
        (cwTotalFiberFamilyPartition Q).part right ↔
      cwTotalFiberFamilyLabel Q left = cwTotalFiberFamilyLabel Q right := by
  classical
  rw [← (cwTotalFiberFamilyPartition Q).mem_part_iff_part_eq_part
    (Finset.mem_univ left) (Finset.mem_univ right)]
  change left ∈
      (Finpartition.ofSetoid (Setoid.ker (cwTotalFiberFamilyLabel Q))).part right ↔ _
  rw [Finpartition.mem_part_ofSetoid_iff_rel]
  exact eq_comm

private theorem cwTotalFiberFamilyPartition_totalPreserving
    (Q : ∀ total : CWCoarseDigit 1, Finpartition (cwDepthOneTotalFiber total)) :
    CWTotalPreservingPartition (cwTotalFiberFamilyPartition Q) := by
  intro left right hpart
  have hlabel :=
    (cwTotalFiberFamilyPartition_part_eq_part Q left right).mp hpart
  have htotal := congrArg Prod.fst hlabel
  simpa only [cwTotalFiberFamilyLabel, cwSplitWordTotalDigit_val] using congrArg Fin.val htotal

/-- Total-preserving partitions are exactly independent partitions of the five total fibers. -/
noncomputable def cwTotalPreservingFinpartitionEquiv :
    CWTotalPreservingFinpartition ≃
      (∀ total : CWCoarseDigit 1, Finpartition (cwDepthOneTotalFiber total)) where
  toFun := cwTotalFiberRestrictions
  invFun := fun Q ↦
    ⟨cwTotalFiberFamilyPartition Q, cwTotalFiberFamilyPartition_totalPreserving Q⟩
  left_inv P := by
    apply Subtype.ext
    apply cwDepthOneFinpartition_eq_of_part_rel
    intro left _ right _
    rw [cwTotalFiberFamilyPartition_part_eq_part]
    constructor
    · intro hlabel
      have htotal : cwSplitWordTotalDigit 1 left = cwSplitWordTotalDigit 1 right := by
        simpa only [cwTotalFiberFamilyLabel] using congrArg Prod.fst hlabel
      have hleft : left ∈ cwDepthOneTotalFiber (cwSplitWordTotalDigit 1 left) := by
        simp
      have hright : right ∈ cwDepthOneTotalFiber (cwSplitWordTotalDigit 1 left) := by
        exact (mem_cwDepthOneTotalFiber _ _).2 htotal.symm
      have hrestricted :
          (cwTotalFiberRestrictions P (cwSplitWordTotalDigit 1 left)).part left =
            (cwTotalFiberRestrictions P (cwSplitWordTotalDigit 1 left)).part right := by
        have hsecond := congrArg Prod.snd hlabel
        change
          (cwTotalFiberRestrictions P (cwSplitWordTotalDigit 1 left)).part left =
            (cwTotalFiberRestrictions P (cwSplitWordTotalDigit 1 right)).part right at hsecond
        rw [← htotal] at hsecond
        exact hsecond
      apply (cwFinpartition_restrict_part_eq_part_iff P.1
        (cwDepthOneTotalFiber_subset_univ _) hleft hright).mp
      exact hrestricted
    · intro hpart
      have hweight := P.2 left right hpart
      have htotal : cwSplitWordTotalDigit 1 left = cwSplitWordTotalDigit 1 right := by
        apply Fin.ext
        exact hweight
      have hleft : left ∈ cwDepthOneTotalFiber (cwSplitWordTotalDigit 1 left) := by
        simp
      have hright : right ∈ cwDepthOneTotalFiber (cwSplitWordTotalDigit 1 left) := by
        exact (mem_cwDepthOneTotalFiber _ _).2 htotal.symm
      have hrestricted :
          (cwTotalFiberRestrictions P (cwSplitWordTotalDigit 1 left)).part left =
            (cwTotalFiberRestrictions P (cwSplitWordTotalDigit 1 left)).part right := by
        apply (cwFinpartition_restrict_part_eq_part_iff P.1
          (cwDepthOneTotalFiber_subset_univ _) hleft hright).mpr
        exact hpart
      unfold cwTotalFiberFamilyLabel
      rw [← htotal]
      change
        (cwSplitWordTotalDigit 1 left,
            (cwTotalFiberRestrictions P (cwSplitWordTotalDigit 1 left)).part left) =
          (cwSplitWordTotalDigit 1 left,
            (cwTotalFiberRestrictions P (cwSplitWordTotalDigit 1 left)).part right)
      exact congrArg (fun part ↦ (cwSplitWordTotalDigit 1 left, part)) hrestricted
  right_inv Q := by
    funext total
    apply cwDepthOneFinpartition_eq_of_part_rel
    intro left hleft right hright
    change
      ((cwTotalFiberFamilyPartition Q).restrict
            (cwDepthOneTotalFiber_subset_univ total)).part left =
          ((cwTotalFiberFamilyPartition Q).restrict
            (cwDepthOneTotalFiber_subset_univ total)).part right ↔
        (Q total).part left = (Q total).part right
    rw [cwFinpartition_restrict_part_eq_part_iff
      (cwTotalFiberFamilyPartition Q)
      (cwDepthOneTotalFiber_subset_univ total) hleft hright]
    rw [cwTotalFiberFamilyPartition_part_eq_part]
    have htotalLeft := (mem_cwDepthOneTotalFiber total left).mp hleft
    have htotalRight := (mem_cwDepthOneTotalFiber total right).mp hright
    unfold cwTotalFiberFamilyLabel
    rw [htotalLeft, htotalRight]
    dsimp only
    constructor
    · exact fun h ↦ congrArg Prod.snd h
    · exact fun h ↦ congrArg (fun part ↦ (total, part)) h

private def cwSplitPairEquiv : SplitDigit × SplitDigit ≃ SplitWord 1 where
  toFun pair := cwSplitPair pair.1 pair.2
  invFun word := (word 0, word 1)
  left_inv pair := by
    rcases pair with ⟨left, right⟩
    apply Prod.ext <;> rfl
  right_inv := cwSplitPair_eta

@[simp] private theorem cwSplitPair_eq_cwSplitPair_iff
    (a b c d : SplitDigit) :
    cwSplitPair a b = cwSplitPair c d ↔ a = c ∧ b = d := by
  constructor
  · intro h
    exact ⟨congrFun h 0, congrFun h 1⟩
  · rintro ⟨rfl, rfl⟩
    rfl

private def cwDepthOneTotalFiberWords (total : CWCoarseDigit 1) : Finset (SplitWord 1) :=
  match total.1 with
  | 0 => {cwSplitPair 0 0}
  | 1 => {cwSplitPair 0 1, cwSplitPair 1 0}
  | 2 => {cwSplitPair 0 2, cwSplitPair 1 1, cwSplitPair 2 0}
  | 3 => {cwSplitPair 1 2, cwSplitPair 2 1}
  | _ => {cwSplitPair 2 2}

@[simp] private theorem splitWordWeight_cwSplitPair
    (left right : SplitDigit) :
    splitWordWeight (cwSplitPair left right) = left.1 + right.1 := by
  simp [splitWordWeight, cwSplitPair, Fin.sum_univ_two]

@[simp] private theorem cwSplitWordTotalDigit_cwSplitPair_val
    (left right : SplitDigit) :
    (cwSplitWordTotalDigit 1 (cwSplitPair left right)).1 = left.1 + right.1 := by
  exact splitWordWeight_cwSplitPair left right

private theorem cwDepthOneTotalFiber_eq_words (total : CWCoarseDigit 1) :
    cwDepthOneTotalFiber total = cwDepthOneTotalFiberWords total := by
  ext word
  obtain ⟨⟨left, right⟩, rfl⟩ := cwSplitPairEquiv.surjective word
  rw [mem_cwDepthOneTotalFiber]
  fin_cases total <;> fin_cases left <;> fin_cases right <;>
    norm_num [cwSplitPairEquiv, cwDepthOneTotalFiberWords, Fin.ext_iff,
      cwSplitPair_eq_cwSplitPair_iff]

private theorem cwDepthOneTotalFiber_card (total : CWCoarseDigit 1) :
    (cwDepthOneTotalFiber total).card =
      match total.1 with
      | 0 => 1
      | 1 => 2
      | 2 => 3
      | 3 => 2
      | _ => 1 := by
  rw [cwDepthOneTotalFiber_eq_words]
  fin_cases total <;>
    norm_num [cwDepthOneTotalFiberWords, cwSplitPair, Fin.ext_iff,
      cwSplitPair_eq_cwSplitPair_iff]

noncomputable instance : Fintype CWTotalPreservingFinpartition :=
  Fintype.ofEquiv
    (∀ total : CWCoarseDigit 1, Finpartition (cwDepthOneTotalFiber total))
    cwTotalPreservingFinpartitionEquiv.symm

/-- Exactly twenty partitions of the nine words preserve total weight. -/
theorem fintypeCard_cwTotalPreservingFinpartition :
    Fintype.card CWTotalPreservingFinpartition = 20 := by
  calc
    Fintype.card CWTotalPreservingFinpartition =
        Fintype.card
          (∀ total : CWCoarseDigit 1, Finpartition (cwDepthOneTotalFiber total)) :=
      Fintype.card_congr cwTotalPreservingFinpartitionEquiv
    _ = ∏ total : CWCoarseDigit 1,
        Fintype.card (Finpartition (cwDepthOneTotalFiber total)) := Fintype.card_pi
    _ = ∏ total : CWCoarseDigit 1, Nat.bell (cwDepthOneTotalFiber total).card := by
      apply Finset.prod_congr rfl
      intro total _
      exact FinpartitionBellCard.fintypeCard_finpartition_eq_bell _
    _ = 20 := by
      have hbellOne : Nat.bell 1 = 1 := by
        norm_num [Nat.bell, Nat.choose, ← Nat.range_succ_eq_Iic, Finset.sum_range_succ]
      have hbellTwo : Nat.bell 2 = 2 := by
        norm_num [Nat.bell, Nat.choose, ← Nat.range_succ_eq_Iic, Finset.sum_range_succ]
      have hbellThree : Nat.bell 3 = 5 := by
        norm_num [Nat.bell, Nat.choose, ← Nat.range_succ_eq_Iic, Finset.sum_range_succ]
      change (∏ total : Fin 5, Nat.bell (cwDepthOneTotalFiber total).card) = 20
      rw [Fin.prod_univ_succ, Fin.prod_univ_succ, Fin.prod_univ_succ,
        Fin.prod_univ_succ, Fin.prod_univ_succ]
      norm_num [cwDepthOneTotalFiber_card,
        hbellOne, hbellTwo, hbellThree]

/-! ## Legwise candidates and the two tight triples -/

/-- Three independently chosen total-preserving partitions, one on each tensor leg. -/
abbrev CWTotalPreservingLegwiseFinpartition :=
  ∀ _c : Leg, CWTotalPreservingFinpartition

/-- There are `20^3 = 8000` independent legwise total-preserving candidates. -/
theorem fintypeCard_cwTotalPreservingLegwiseFinpartition :
    Fintype.card CWTotalPreservingLegwiseFinpartition = 8000 := by
  rw [Fintype.card_pi, prod_leg]
  norm_num [fintypeCard_cwTotalPreservingFinpartition]

/-- The canonical surjective quotient associated to an independent partition on each leg. -/
noncomputable def cwTotalPreservingLegwiseQuotient
    (P : CWTotalPreservingLegwiseFinpartition) :
    ∀ c, SplitWord 1 → ((P c).1).parts :=
  fun c ↦ cwFinpartitionQuotient (P c).1

/-- The physical depth-one support after an independent total-preserving quotient on each leg. -/
noncomputable def cwTotalPreservingLegwiseQuotientSupport
    (P : CWTotalPreservingLegwiseFinpartition) :
    Finset (BlockAddress (fun c ↦ ((P c).1).parts)) :=
  cwDepthOneQuotientSupport (cwTotalPreservingLegwiseQuotient P)

private theorem cwTotalPreservingLegwiseQuotient_surjective
    (P : CWTotalPreservingLegwiseFinpartition) :
    ∀ c, Function.Surjective (cwTotalPreservingLegwiseQuotient P c) := by
  intro c
  exact cwFinpartitionQuotient_surjective (P c).1

/-- The total-weight normalized kernel does preserve total weight. -/
theorem cwTightQuotientKind_sum_totalPreserving :
    CWTotalPreservingPartition CWTightQuotientKind.sum.partition := by
  intro left right hpart
  have hlinear : cwSplitLinearForm 1 1 left = cwSplitLinearForm 1 1 right := by
    apply (cwLinearFinpartition_part_eq_part 1 1 left right).mp
    simpa [CWTightQuotientKind.partition, CWTightQuotientKind.coefficients] using hpart
  rw [← cwSplitPair_eta left, ← cwSplitPair_eta right,
    splitWordWeight_cwSplitPair, splitWordWeight_cwSplitPair]
  norm_num [cwSplitLinearForm] at hlinear
  omega

/-- The discrete normalized kernel preserves every statistic, in particular total weight. -/
theorem cwTightQuotientKind_discrete_totalPreserving :
    CWTotalPreservingPartition CWTightQuotientKind.discrete.partition := by
  intro left right hpart
  have hlinear : cwSplitLinearForm 3 1 left = cwSplitLinearForm 3 1 right := by
    apply (cwLinearFinpartition_part_eq_part 3 1 left right).mp
    simpa [CWTightQuotientKind.partition, CWTightQuotientKind.coefficients] using hpart
  rw [cwSplitLinearForm_discrete_injective hlinear]

private theorem cwTightQuotientKind_weight_eq_of_linear_eq
    (kind : CWTightQuotientKind)
    (hpreserves : CWTotalPreservingPartition kind.partition)
    (left right : SplitWord 1)
    (hlinear :
      cwSplitLinearForm kind.coefficients.1 kind.coefficients.2 left =
        cwSplitLinearForm kind.coefficients.1 kind.coefficients.2 right) :
    splitWordWeight left = splitWordWeight right := by
  apply hpreserves left right
  change
    (cwLinearFinpartition kind.coefficients.1 kind.coefficients.2).part left =
      (cwLinearFinpartition kind.coefficients.1 kind.coefficients.2).part right
  exact (cwLinearFinpartition_part_eq_part _ _ left right).mpr hlinear

/-- Among the ten tight normalized kernels, only total weight and the discrete partition preserve
total weight.  Each excluded kernel is refuted by one explicit collision of different totals. -/
theorem cwTightQuotientKind_eq_sum_or_discrete_of_totalPreserving
    (kind : CWTightQuotientKind)
    (hpreserves : CWTotalPreservingPartition kind.partition) :
    kind = .sum ∨ kind = .discrete := by
  cases kind with
  | constant =>
      exfalso
      have hweight := cwTightQuotientKind_weight_eq_of_linear_eq .constant hpreserves
        (cwSplitPair 0 0) (cwSplitPair 1 0) (by
          norm_num [CWTightQuotientKind.coefficients, cwSplitLinearForm, cwSplitPair])
      norm_num [splitWordWeight_cwSplitPair] at hweight
  | firstCoordinate =>
      exfalso
      have hweight := cwTightQuotientKind_weight_eq_of_linear_eq .firstCoordinate hpreserves
        (cwSplitPair 0 0) (cwSplitPair 0 1) (by
          norm_num [CWTightQuotientKind.coefficients, cwSplitLinearForm, cwSplitPair])
      norm_num [splitWordWeight_cwSplitPair] at hweight
  | secondCoordinate =>
      exfalso
      have hweight := cwTightQuotientKind_weight_eq_of_linear_eq .secondCoordinate hpreserves
        (cwSplitPair 0 0) (cwSplitPair 1 0) (by
          norm_num [CWTightQuotientKind.coefficients, cwSplitLinearForm, cwSplitPair])
      norm_num [splitWordWeight_cwSplitPair] at hweight
  | sum => exact Or.inl rfl
  | difference =>
      exfalso
      have hweight := cwTightQuotientKind_weight_eq_of_linear_eq .difference hpreserves
        (cwSplitPair 0 0) (cwSplitPair 1 1) (by
          norm_num [CWTightQuotientKind.coefficients, cwSplitLinearForm, cwSplitPair])
      norm_num [splitWordWeight_cwSplitPair] at hweight
  | twoFirstPlusSecond =>
      exfalso
      have hweight := cwTightQuotientKind_weight_eq_of_linear_eq
        .twoFirstPlusSecond hpreserves (cwSplitPair 0 2) (cwSplitPair 1 0) (by
          norm_num [CWTightQuotientKind.coefficients, cwSplitLinearForm, cwSplitPair])
      norm_num [splitWordWeight_cwSplitPair] at hweight
  | negativeTwoFirstPlusSecond =>
      exfalso
      have hweight := cwTightQuotientKind_weight_eq_of_linear_eq
        .negativeTwoFirstPlusSecond hpreserves (cwSplitPair 0 0) (cwSplitPair 1 2) (by
          norm_num [CWTightQuotientKind.coefficients, cwSplitLinearForm, cwSplitPair])
      norm_num [splitWordWeight_cwSplitPair] at hweight
  | firstPlusTwoSecond =>
      exfalso
      have hweight := cwTightQuotientKind_weight_eq_of_linear_eq
        .firstPlusTwoSecond hpreserves (cwSplitPair 0 1) (cwSplitPair 2 0) (by
          norm_num [CWTightQuotientKind.coefficients, cwSplitLinearForm, cwSplitPair])
      norm_num [splitWordWeight_cwSplitPair] at hweight
  | firstMinusTwoSecond =>
      exfalso
      have hweight := cwTightQuotientKind_weight_eq_of_linear_eq
        .firstMinusTwoSecond hpreserves (cwSplitPair 0 0) (cwSplitPair 2 1) (by
          norm_num [CWTightQuotientKind.coefficients, cwSplitLinearForm, cwSplitPair])
      norm_num [splitWordWeight_cwSplitPair] at hweight
  | discrete => exact Or.inr rfl

/-- The legwise total-weight candidate. -/
noncomputable def cwTotalWeightLegwiseFinpartition :
    CWTotalPreservingLegwiseFinpartition :=
  fun _c ↦ ⟨CWTightQuotientKind.sum.partition,
    cwTightQuotientKind_sum_totalPreserving⟩

/-- The legwise discrete candidate. -/
noncomputable def cwDiscreteLegwiseFinpartition :
    CWTotalPreservingLegwiseFinpartition :=
  fun _c ↦ ⟨CWTightQuotientKind.discrete.partition,
    cwTightQuotientKind_discrete_totalPreserving⟩

/-- A total-preserving legwise quotient is tight exactly in the all-total and all-discrete cases.
The three partitions are not assumed equal; their equality follows from the common linear form in
the generic quotient decoder. -/
theorem cwTotalPreservingLegwiseQuotientSupport_isTight_iff
    (P : CWTotalPreservingLegwiseFinpartition) :
    IsTightSupport (cwTotalPreservingLegwiseQuotientSupport P) ↔
      P = cwTotalWeightLegwiseFinpartition ∨ P = cwDiscreteLegwiseFinpartition := by
  have hcore := cwDepthOneQuotientSupport_isTight_iff_fibers_linear
    (cwTotalPreservingLegwiseQuotient P)
    (cwTotalPreservingLegwiseQuotient_surjective P)
  constructor
  · intro htight
    obtain ⟨lambda, mu, hfibers⟩ := hcore.mp htight
    obtain ⟨kind, hkind⟩ := cwLinearFinpartition_eq_kind lambda mu
    have hall (c : Leg) : (P c).1 = kind.partition := by
      apply (cwDepthOneFinpartition_eq_of_part_rel (s := Finset.univ) ?_).trans hkind
      intro left _ right _
      exact (cwFinpartitionQuotient_eq_iff (P c).1 left right).symm.trans
        ((hfibers c left right).trans
          (cwLinearFinpartition_part_eq_part lambda mu left right).symm)
    have hpreserves : CWTotalPreservingPartition kind.partition := by
      rw [← hall .X]
      exact (P .X).2
    rcases cwTightQuotientKind_eq_sum_or_discrete_of_totalPreserving kind hpreserves with
      hsum | hdiscrete
    · subst kind
      left
      funext c
      apply Subtype.ext
      exact hall c
    · subst kind
      right
      funext c
      apply Subtype.ext
      exact hall c
  · intro hcandidate
    apply hcore.mpr
    rcases hcandidate with htotal | hdiscrete
    · subst P
      refine ⟨1, 1, ?_⟩
      intro c left right
      change cwFinpartitionQuotient CWTightQuotientKind.sum.partition left =
          cwFinpartitionQuotient CWTightQuotientKind.sum.partition right ↔
        cwSplitLinearForm 1 1 left = cwSplitLinearForm 1 1 right
      exact (cwFinpartitionQuotient_eq_iff _ left right).trans
        (cwLinearFinpartition_part_eq_part 1 1 left right)
    · subst P
      refine ⟨3, 1, ?_⟩
      intro c left right
      change cwFinpartitionQuotient CWTightQuotientKind.discrete.partition left =
          cwFinpartitionQuotient CWTightQuotientKind.discrete.partition right ↔
        cwSplitLinearForm 3 1 left = cwSplitLinearForm 3 1 right
      exact (cwFinpartitionQuotient_eq_iff _ left right).trans
        (cwLinearFinpartition_part_eq_part 3 1 left right)

private theorem cwTotalWeightLegwiseFinpartition_ne_discrete :
    cwTotalWeightLegwiseFinpartition ≠ cwDiscreteLegwiseFinpartition := by
  intro h
  have hX := congrArg (fun P ↦ (P .X).1) h
  have hkind := cwTightQuotientKind_partition_injective hX
  cases hkind

/-- Tight total-preserving candidates, as an honest finite subtype. -/
abbrev CWTightTotalPreservingLegwiseFinpartition :=
  {P : CWTotalPreservingLegwiseFinpartition //
    IsTightSupport (cwTotalPreservingLegwiseQuotientSupport P)}

noncomputable def cwTightTotalPreservingLegwiseEquivBool :
    CWTightTotalPreservingLegwiseFinpartition ≃ Bool where
  toFun P := if P.1 = cwTotalWeightLegwiseFinpartition then false else true
  invFun isDiscrete := if isDiscrete then
      ⟨cwDiscreteLegwiseFinpartition,
        (cwTotalPreservingLegwiseQuotientSupport_isTight_iff _).mpr (Or.inr rfl)⟩
    else
      ⟨cwTotalWeightLegwiseFinpartition,
        (cwTotalPreservingLegwiseQuotientSupport_isTight_iff _).mpr (Or.inl rfl)⟩
  left_inv P := by
    apply Subtype.ext
    rcases (cwTotalPreservingLegwiseQuotientSupport_isTight_iff P.1).mp P.2 with
      htotal | hdiscrete
    · simp [htotal]
    · have hdiscNe :
          cwDiscreteLegwiseFinpartition ≠ cwTotalWeightLegwiseFinpartition :=
        Ne.symm cwTotalWeightLegwiseFinpartition_ne_discrete
      have hPNe :
          P.1 ≠ cwTotalWeightLegwiseFinpartition := by
        intro htotal
        exact hdiscNe (hdiscrete.symm.trans htotal)
      simpa only [hPNe, if_false, Bool.true_eq, if_true] using hdiscrete.symm
  right_inv isDiscrete := by
    cases isDiscrete
    · simp
    · simp [Ne.symm cwTotalWeightLegwiseFinpartition_ne_discrete]

noncomputable instance : Fintype CWTightTotalPreservingLegwiseFinpartition :=
  Fintype.ofEquiv Bool cwTightTotalPreservingLegwiseEquivBool.symm

/-- Exactly two of the 8,000 total-preserving legwise candidates have tight quotient support. -/
theorem fintypeCard_cwTightTotalPreservingLegwiseFinpartition :
    Fintype.card CWTightTotalPreservingLegwiseFinpartition = 2 := by
  calc
    Fintype.card CWTightTotalPreservingLegwiseFinpartition = Fintype.card Bool :=
      Fintype.card_congr cwTightTotalPreservingLegwiseEquivBool
    _ = 2 := Fintype.card_bool

end AlgebraicComplexity.Examples
