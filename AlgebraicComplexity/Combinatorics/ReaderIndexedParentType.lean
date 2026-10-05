/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Combinatorics.ConditionalWordTypeMultinomial
import AlgebraicComplexity.Combinatorics.WordTypeStatistics

/-!
# Exact finite reader-indexed parent-type counting

This module formalizes the finite counting step in `better_bound/paper.tex`, Appendix C.1,
Theorem `thm:reader-indexed-parent-type` (lines 3034--3071 in the 2026-09-05 manuscript snapshot).
That theorem corrects the parent-type drop in Alman--Duan--Vassilevska Williams--Xu--Xu--Zhou,
*More Asymmetry Yields Faster Matrix Multiplication*, Claim 6.18
(`papers/sources/2404.16349/constituent.tex:376-440`, especially line 402).

An ordered state word is fixed.  A raw parent block supplies one ordered pair of child symbols at
each position.  Its unique joint empirical table records the state and both symbols.  Feasibility
imposes exactly the paper's four finite conditions on that table: the state type, the raw parent
type, native structural support, and one *combined* left/right occurrence table formed through the
state-indexed readers.  There are deliberately no separate left- and right-occurrence constraints.

The compatible blocks are partitioned by their unique feasible joint table.  Distinct conditional
type classes are disjoint, and the existing exact conditional-type theorem counts each class by
the product of its row multinomials.  Hence the total count is exactly the sum in the paper, with no
asymptotics and no division.

This file does not prove the subsequent entropy maximization, compactness passage, candidate
feasibility, tensor degeneration, or an exponent bound.
-/

set_option autoImplicit false

namespace AlgebraicComplexity.WordType

open scoped BigOperators

universe u v w x y

/-- The state-indexed readers and the native support used by the corrected Claim 6.18 count.

For an ordered parent state `s`, `leftReader s` reads the left child symbol and `rightReader s`
reads the right child symbol.  A client with a complement involution incorporates it in
`rightCell` and `rightReader`; keeping those maps explicit prevents Lean from silently replacing
the right occurrence by an independently chosen state. -/
structure ReaderIndexedParentModel
    (State : Type u) (Left : Type v) (Right : Type w)
    (Cell : Type x) (Read : Type y) where
  leftCell : State → Cell
  rightCell : State → Cell
  leftReader : State → Left → Read
  rightReader : State → Right → Read
  nativeAdmissible : State → Left → Right → Prop

namespace ReaderIndexedParentModel

variable {State : Type u} {Left : Type v} {Right : Type w}
variable {Cell : Type x} {Read : Type y}

/-- Contribution of one `(state,left,right)` letter to one cell/reader-symbol coordinate of the
single combined labelled-occurrence table.  Both labelled occurrences are counted; a
self-complementary parent position therefore contributes two, exactly as in the manuscript. -/
noncomputable def occurrenceWeight (M : ReaderIndexedParentModel State Left Right Cell Read)
    (cellRead : Cell × Read) (entry : State × (Left × Right)) : ℕ := by
  classical
  exact
    (if M.leftCell entry.1 = cellRead.1 ∧
        M.leftReader entry.1 entry.2.1 = cellRead.2 then 1 else 0) +
      (if M.rightCell entry.1 = cellRead.1 ∧
        M.rightReader entry.1 entry.2.2 = cellRead.2 then 1 else 0)

/-- The combined labelled-occurrence table determined by a joint empirical profile.  This is the
finite integral form of the last constraint defining `Q_ρ(α,β,ν)` in the manuscript. -/
noncomputable def occurrenceProfileOfType
    [Fintype State] [Fintype Left] [Fintype Right]
    (M : ReaderIndexedParentModel State Left Right Cell Read)
    (joint : State × (Left × Right) → ℕ) : Cell × Read → ℕ :=
  fun cellRead ↦ ∑ entry, joint entry * M.occurrenceWeight cellRead entry

/-- The same combined occurrence table computed directly from a fixed state word and a raw parent
block. -/
noncomputable def occurrenceProfileOfBlock
    [Fintype State] [Fintype Left] [Fintype Right]
    (M : ReaderIndexedParentModel State Left Right Cell Read)
    {n : ℕ}
    (state : Fin n → State) (block : Fin n → Left × Right) : Cell × Read → ℕ :=
  fun cellRead ↦ ∑ i, M.occurrenceWeight cellRead (state i, block i)

/-- A word's combined occurrence table depends only on its full `(state,left,right)` empirical
profile. -/
theorem occurrenceProfileOfBlock_eq_occurrenceProfileOfType_multiplicity
    [Fintype State] [Fintype Left] [Fintype Right]
    (M : ReaderIndexedParentModel State Left Right Cell Read)
    {n : ℕ}
    (state : Fin n → State) (block : Fin n → Left × Right) :
    M.occurrenceProfileOfBlock state block =
      M.occurrenceProfileOfType (multiplicity (jointWord state block)) := by
  funext cellRead
  exact sum_word_eq_sum_multiplicity_mul
    (M.occurrenceWeight cellRead) (jointWord state block)

/-- The four table-level constraints of the reader-indexed parent-type problem.

The occurrence law is one combined left/right law.  In particular this definition does not impose
the stronger, generally false pair of separate occurrence marginals. -/
def IsFeasibleProfile
    [Fintype State] [Fintype Left] [Fintype Right]
    (M : ReaderIndexedParentModel State Left Right Cell Read)
    (n : ℕ) (alpha : State → ℕ) (beta : Left × Right → ℕ)
    (nu : Cell × Read → ℕ) (joint : State × (Left × Right) → ℕ) : Prop :=
  joint ∈ types (State × (Left × Right)) n ∧
    mappedType Prod.fst joint = alpha ∧
    mappedType Prod.snd joint = beta ∧
    (∀ entry, joint entry ≠ 0 →
      M.nativeAdmissible entry.1 entry.2.1 entry.2.2) ∧
    M.occurrenceProfileOfType joint = nu

/-- The finite set of integral feasible joint tables. -/
noncomputable def feasibleProfiles
    [Fintype State] [Fintype Left] [Fintype Right]
    (M : ReaderIndexedParentModel State Left Right Cell Read)
    (n : ℕ) (alpha : State → ℕ) (beta : Left × Right → ℕ)
    (nu : Cell × Read → ℕ) : Finset (State × (Left × Right) → ℕ) := by
  classical
  exact (types (State × (Left × Right)) n).filter
    (M.IsFeasibleProfile n alpha beta nu)

@[simp] theorem mem_feasibleProfiles
    [Fintype State] [Fintype Left] [Fintype Right]
    (M : ReaderIndexedParentModel State Left Right Cell Read)
    {n : ℕ} {alpha : State → ℕ} {beta : Left × Right → ℕ}
    {nu : Cell × Read → ℕ} {joint : State × (Left × Right) → ℕ} :
    joint ∈ M.feasibleProfiles n alpha beta nu ↔
      M.IsFeasibleProfile n alpha beta nu joint := by
  classical
  simp only [feasibleProfiles, Finset.mem_filter]
  constructor
  · exact fun h ↦ h.2
  · exact fun h ↦ ⟨h.1, h⟩

/-- Raw parent blocks, partitioned by the feasible joint empirical table they realize with the
fixed ordered state word. -/
noncomputable def parentBlocks
    [Fintype State] [Fintype Left] [Fintype Right]
    (M : ReaderIndexedParentModel State Left Right Cell Read)
    {n : ℕ}
    (state : Fin n → State) (alpha : State → ℕ) (beta : Left × Right → ℕ)
    (nu : Cell × Read → ℕ) : Finset (Fin n → Left × Right) := by
  classical
  exact (M.feasibleProfiles n alpha beta nu).biUnion (conditionalTypeClass state)

@[simp] theorem mem_parentBlocks
    [Fintype State] [Fintype Left] [Fintype Right]
    (M : ReaderIndexedParentModel State Left Right Cell Read)
    {n : ℕ} {state : Fin n → State} {alpha : State → ℕ} {beta : Left × Right → ℕ}
    {nu : Cell × Read → ℕ} {block : Fin n → Left × Right} :
    block ∈ M.parentBlocks state alpha beta nu ↔
      ∃ joint ∈ M.feasibleProfiles n alpha beta nu,
        multiplicity (jointWord state block) = joint := by
  classical
  simp [parentBlocks, mem_conditionalTypeClass]

/-- **Exact finite reader-indexed parent-type count.**

For a fixed ordered state sequence, the number of compatible raw parent blocks is the sum, over
integral feasible joint tables, of the product of row multinomial coefficients.  This is exactly
the finite display in `better_bound/paper.tex`, Theorem `thm:reader-indexed-parent-type`, before
the polynomial-number-of-types and entropy-maximization steps. -/
theorem card_parentBlocks_eq_sum_rowMultinomial
    [Fintype State] [Fintype Left] [Fintype Right]
    (M : ReaderIndexedParentModel State Left Right Cell Read)
    {n : ℕ}
    (state : Fin n → State) (alpha : State → ℕ) (beta : Left × Right → ℕ)
    (nu : Cell × Read → ℕ) (halpha : alpha = multiplicity state) :
    (M.parentBlocks state alpha beta nu).card =
      ∑ joint ∈ M.feasibleProfiles n alpha beta nu,
        ∏ s, Nat.multinomial Finset.univ fun pair ↦ joint (s, pair) := by
  classical
  rw [parentBlocks, Finset.card_biUnion]
  · apply Finset.sum_congr rfl
    intro joint hjoint
    have hfeasible := (M.mem_feasibleProfiles).mp hjoint
    exact card_conditionalTypeClass_eq_prod_multinomial state joint hfeasible.1
      (hfeasible.2.1.trans halpha)
  · intro left hleft right hright hne
    refine Finset.disjoint_left.mpr ?_
    intro block hblockLeft hblockRight
    have hleftType := mem_conditionalTypeClass.mp hblockLeft
    have hrightType := mem_conditionalTypeClass.mp hblockRight
    exact hne (hleftType.symm.trans hrightType)

/-! The singleton instance below checks that the state type, parent type, combined occurrence
table, and native-support constraints can be satisfied simultaneously. -/

example :
    (({
      leftCell := fun _ : Unit ↦ ()
      rightCell := fun _ : Unit ↦ ()
      leftReader := fun _ : Unit ↦ id
      rightReader := fun _ : Unit ↦ id
      nativeAdmissible := fun _ : Unit ↦ fun _ : Unit ↦ fun _ : Unit ↦ True
    } : ReaderIndexedParentModel Unit Unit Unit Unit Unit).parentBlocks
      (fun _ : Fin 1 ↦ ()) (fun _ ↦ 1) (fun _ ↦ 1) (fun _ ↦ 2)).Nonempty := by
  classical
  refine ⟨(fun _ : Fin 1 ↦ ((), ())), ?_⟩
  rw [mem_parentBlocks]
  refine ⟨(fun _ : Unit × (Unit × Unit) ↦ 1), ?_, ?_⟩
  · rw [mem_feasibleProfiles]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [mem_types]
      simp
    · funext state
      obtain rfl : state = () := Subsingleton.elim _ _
      simp [mappedType, letterFiber]
    · funext pair
      obtain rfl : pair = ((), ()) := Subsingleton.elim _ _
      simp [mappedType, letterFiber]
    · intro _ _
      trivial
    · funext cellRead
      obtain rfl : cellRead = ((), ()) := Subsingleton.elim _ _
      simp [occurrenceProfileOfType, occurrenceWeight]
  · funext entry
    obtain ⟨state, left, right⟩ := entry
    obtain rfl : state = () := Subsingleton.elim _ _
    obtain rfl : left = () := Subsingleton.elim _ _
    obtain rfl : right = () := Subsingleton.elim _ _
    simp [multiplicity, jointWord]

end ReaderIndexedParentModel

end AlgebraicComplexity.WordType
