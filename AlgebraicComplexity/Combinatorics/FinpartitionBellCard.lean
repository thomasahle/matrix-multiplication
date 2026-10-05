/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import Mathlib.Combinatorics.Enumerative.Bell
import Mathlib.Order.Partition.Finpartition

/-!
# Counting finite set partitions by Bell numbers

Mathlib defines both finite partitions and Bell numbers, but does not yet connect their
cardinalities.  This file supplies that bridge by an explicit decoder: in a partition of
`insert x s`, peel the unique part containing `x`, remember its other elements `t ⊆ s`, and retain
the induced partition of `s \ t`.  Reinserting `x ∪ t` is the inverse operation.

The resulting recurrence is the defining Bell recurrence.  No `Fintype` enumeration of
`Finpartition` is evaluated; that instance uses a double powerset and is unsuitable even for the
nine-element application motivating this module.
-/

namespace AlgebraicComplexity

open Finset

universe u

namespace FinpartitionBellCard

variable {α : Type u} [DecidableEq α]

/-- Finite subsets of `s`, kept as a type so they can index a dependent family of partitions. -/
abbrev Subsets (s : Finset α) := {t : Finset α // t ⊆ s}

private theorem erase_subset_of_subset_insert {x : α} {s t : Finset α}
    (ht : t ⊆ insert x s) : t.erase x ⊆ s := by
  intro y hy
  have hy' := mem_erase.mp hy
  exact (mem_insert.mp (ht hy'.2)).resolve_left hy'.1

private theorem insert_sdiff_part_eq_sdiff_erase {x : α} {s t : Finset α}
    (hx : x ∉ s) (hxt : x ∈ t) :
    insert x s \ t = s \ t.erase x := by
  ext y
  by_cases hyx : y = x
  · subst y
    simp [hx, hxt]
  · simp [hyx]

private theorem disjoint_sdiff_insert {x : α} {s t : Finset α}
    (hx : x ∉ s) : Disjoint (s \ t) (insert x t) := by
  rw [Finset.disjoint_left]
  intro y hy hyt
  simp only [mem_sdiff] at hy
  rcases mem_insert.mp hyt with rfl | hyt
  · exact hx hy.1
  · exact hy.2 hyt

private theorem sdiff_union_insert {x : α} {s t : Finset α}
    (hx : x ∉ s) (ht : t ⊆ s) :
    (s \ t) ∪ insert x t = insert x s := by
  ext y
  constructor
  · intro hy
    rcases mem_union.mp hy with hy | hy
    · exact mem_insert_of_mem (mem_sdiff.mp hy).1
    · rcases mem_insert.mp hy with rfl | hy
      · exact mem_insert_self _ _
      · exact mem_insert_of_mem (ht hy)
  · intro hy
    rcases mem_insert.mp hy with rfl | hy
    · exact mem_union_right _ (mem_insert_self _ _)
    · by_cases hyt : y ∈ t
      · exact mem_union_right _ (mem_insert_of_mem hyt)
      · exact mem_union_left _ (mem_sdiff.mpr ⟨hy, hyt⟩)

private theorem part_erase_subset (x : α) (s : Finset α)
    (P : Finpartition (insert x s)) :
    (P.part x).erase x ⊆ s :=
  erase_subset_of_subset_insert (P.part_subset x)

private theorem part_contains (x : α) (s : Finset α) (P : Finpartition (insert x s)) :
    x ∈ P.part x :=
  P.mem_part (mem_insert_self x s)

/-- Remove the distinguished part and remember its elements other than `x`. -/
private def peel (x : α) (s : Finset α) (hx : x ∉ s)
    (P : Finpartition (insert x s)) :
    Σ t : Subsets s, Finpartition (s \ t.1) :=
  let t : Subsets s := ⟨(P.part x).erase x, part_erase_subset x s P⟩
  ⟨t, (P.avoid (P.part x)).copy
    (insert_sdiff_part_eq_sdiff_erase hx (part_contains x s P))⟩

omit [DecidableEq α] in
private theorem subset_not_mem {x : α} {s t : Finset α}
    (hx : x ∉ s) (ht : t ⊆ s) : x ∉ t :=
  fun hxt ↦ hx (ht hxt)

/-- Reinsert the distinguished part `insert x t`. -/
private def unpeel (x : α) (s : Finset α) (hx : x ∉ s)
    (data : Σ t : Subsets s, Finpartition (s \ t.1)) :
    Finpartition (insert x s) :=
  data.2.extend (insert_ne_empty x data.1.1)
    (disjoint_sdiff_insert hx)
    (sdiff_union_insert hx data.1.2)

private theorem avoid_part_parts (x : α) (s : Finset α)
    (P : Finpartition (insert x s)) :
    (P.avoid (P.part x)).parts = P.parts.erase (P.part x) := by
  ext p
  rw [P.mem_avoid, mem_erase]
  constructor
  · rintro ⟨d, hd, hnotle, hdiff⟩
    have hdne : d ≠ P.part x := fun h ↦ hnotle h.le
    have hdisjoint : Disjoint d (P.part x) :=
      P.disjoint hd (P.part_mem.mpr (mem_insert_self x s)) hdne
    have hsame : d \ P.part x = d := Finset.sdiff_eq_self_of_disjoint hdisjoint
    rw [hsame] at hdiff
    subst p
    exact ⟨hdne, hd⟩
  · rintro ⟨hpne, hp⟩
    have hdisjoint : Disjoint p (P.part x) :=
      P.disjoint hp (P.part_mem.mpr (mem_insert_self x s)) hpne
    refine ⟨p, hp, ?_, Finset.sdiff_eq_self_of_disjoint hdisjoint⟩
    intro hle
    exact P.ne_bot hp (hdisjoint.eq_bot_of_le hle)

private theorem unpeel_peel (x : α) (s : Finset α) (hx : x ∉ s)
    (P : Finpartition (insert x s)) :
    unpeel x s hx (peel x s hx P) = P := by
  apply Finpartition.ext
  simp only [unpeel, peel, Finpartition.extend_parts, Finpartition.copy_parts]
  rw [insert_erase (part_contains x s P), avoid_part_parts]
  rw [insert_erase (P.part_mem.mpr (mem_insert_self x s))]

private theorem unpeel_part (x : α) (s : Finset α) (hx : x ∉ s)
    (t : Subsets s) (Q : Finpartition (s \ t.1)) :
    (unpeel x s hx ⟨t, Q⟩).part x = insert x t.1 := by
  apply (unpeel x s hx ⟨t, Q⟩).part_eq_of_mem
  · simp only [unpeel, Finpartition.extend_parts, mem_insert, true_or]
  · exact mem_insert_self _ _

private theorem inserted_part_not_mem (x : α) (s : Finset α) (hx : x ∉ s)
    (t : Subsets s) (Q : Finpartition (s \ t.1)) :
    insert x t.1 ∉ Q.parts := by
  intro hpart
  have hsubset := Q.le hpart
  have hxmem : x ∈ s \ t.1 := hsubset (mem_insert_self x t.1)
  exact hx (mem_sdiff.mp hxmem).1

private theorem avoid_inserted_part (x : α) (s : Finset α) (hx : x ∉ s)
    (t : Subsets s) (Q : Finpartition (s \ t.1)) :
    ((unpeel x s hx ⟨t, Q⟩).avoid (insert x t.1)).parts = Q.parts := by
  have hpart := unpeel_part x s hx t Q
  calc
    ((unpeel x s hx ⟨t, Q⟩).avoid (insert x t.1)).parts =
        ((unpeel x s hx ⟨t, Q⟩).avoid
          ((unpeel x s hx ⟨t, Q⟩).part x)).parts := by rw [hpart]
    _ = (unpeel x s hx ⟨t, Q⟩).parts.erase
        ((unpeel x s hx ⟨t, Q⟩).part x) :=
      avoid_part_parts x s (unpeel x s hx ⟨t, Q⟩)
    _ = Q.parts := by
      rw [hpart]
      simp only [unpeel, Finpartition.extend_parts]
      rw [erase_insert (inserted_part_not_mem x s hx t Q)]

private theorem finpartition_heq_of_parts_eq {s t : Finset α}
    (P : Finpartition s) (Q : Finpartition t) (hparts : P.parts = Q.parts) : HEq P Q := by
  have hst : s = t := by
    rw [← P.sup_parts, ← Q.sup_parts, hparts]
  subst t
  exact heq_of_eq (Finpartition.ext hparts)

private theorem peel_unpeel (x : α) (s : Finset α) (hx : x ∉ s)
    (data : Σ t : Subsets s, Finpartition (s \ t.1)) :
    peel x s hx (unpeel x s hx data) = data := by
  rcases data with ⟨t, Q⟩
  have hfirst :
      (⟨((unpeel x s hx ⟨t, Q⟩).part x).erase x,
          part_erase_subset x s (unpeel x s hx ⟨t, Q⟩)⟩ : Subsets s) = t := by
    apply Subtype.ext
    change ((unpeel x s hx ⟨t, Q⟩).part x).erase x = t.1
    simpa only [unpeel_part] using erase_insert (subset_not_mem hx t.2)
  refine Sigma.ext hfirst ?_
  apply finpartition_heq_of_parts_eq
  simp only [peel, Finpartition.copy_parts]
  rw [unpeel_part, avoid_inserted_part]

/-- Peeling the part containing a fresh point is equivalent to choosing its other elements and
partitioning the complement. -/
def insertEquivSigma (x : α) (s : Finset α) (hx : x ∉ s) :
    Finpartition (insert x s) ≃
      Σ t : Subsets s, Finpartition (s \ t.1) where
  toFun := peel x s hx
  invFun := unpeel x s hx
  left_inv := unpeel_peel x s hx
  right_inv := peel_unpeel x s hx

/-- Subsets represented by a proof of inclusion are equivalent to elements of the powerset. -/
private def subsetsEquivPowerset (s : Finset α) : Subsets s ≃ (s.powerset : Type u) where
  toFun t := ⟨t.1, mem_powerset.mpr t.2⟩
  invFun t := ⟨t.1, mem_powerset.mp t.2⟩
  left_inv t := by cases t; rfl
  right_inv t := by cases t; rfl

/-- The number of finite partitions of a finite set is its Bell number.

The proof uses `insertEquivSigma` at every induction step, so it never evaluates Mathlib's
double-powerset `Fintype (Finpartition s)` instance. -/
theorem fintypeCard_finpartition_eq_bell (s : Finset α) :
    Fintype.card (Finpartition s) = Nat.bell s.card := by
  classical
  induction s using Finset.case_strong_induction_on with
  | h₀ =>
      simp only [Finset.card_empty, Nat.bell_zero]
      apply Fintype.card_eq_one_of_forall_eq (i := Finpartition.empty (Finset α))
      intro P
      apply Finpartition.ext
      exact P.parts_eq_empty_iff.mpr rfl
  | h₁ x s hx ih =>
      letI : Fintype (Subsets s) :=
        Fintype.ofEquiv (s.powerset : Type u) (subsetsEquivPowerset s).symm
      rw [Fintype.card_congr (insertEquivSigma x s hx), Fintype.card_sigma]
      calc
        (∑ t : Subsets s, Fintype.card (Finpartition (s \ t.1))) =
            ∑ t : Subsets s, Nat.bell (s \ t.1).card := by
              apply Finset.sum_congr rfl
              intro t _
              exact ih (s \ t.1) (sdiff_subset)
        _ = ∑ t : (s.powerset : Type u), Nat.bell (s \ t.1).card := by
              exact Fintype.sum_equiv (subsetsEquivPowerset s) _ _ (fun _ ↦ rfl)
        _ = ∑ t ∈ s.powerset, Nat.bell (s.card - t.card) := by
              rw [← Finset.sum_subtype s.powerset (by simp)
                (fun t ↦ Nat.bell (s \ t).card)]
              apply Finset.sum_congr rfl
              intro t ht
              rw [card_sdiff_of_subset (mem_powerset.mp ht)]
        _ = Nat.bell (insert x s).card := by
              rw [Finset.sum_powerset_apply_card
                (f := fun k ↦ Nat.bell (s.card - k)) (x := s)]
              simp only [nsmul_eq_mul, Nat.cast_id, card_insert_of_notMem hx]
              rw [Nat.bell_succ, ← Nat.range_succ_eq_Iic]

/-- Bell-number count specialized to the standard `n`-element type. -/
theorem fintypeCard_finpartition_univ_fin (n : ℕ) :
    Fintype.card (Finpartition (Finset.univ : Finset (Fin n))) = Nat.bell n := by
  simpa using
    (fintypeCard_finpartition_eq_bell (Finset.univ : Finset (Fin n)))

end FinpartitionBellCard

end AlgebraicComplexity
