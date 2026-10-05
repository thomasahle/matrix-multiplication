/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Combinatorics.ReaderIndexedParentType

/-!
# Cellwise counting for identity-reader parent blocks

This module proves the finite cellwise upper bound behind the homogeneous-reader specialization
of the parent-consistent compatibility count in `better_bound/paper.tex` at commit `e7317a1d`,
Theorem `thm:reader-indexed-parent-type`, lines 3126--3167.  It also follows the fixed-triple
doubled-cell count in [alman2025more, Claim 6.18],
`papers/sources/2404.16349/constituent.tex:402-436`, especially lines 414--429.

When both state-indexed readers are the identity, append the left and right raw children of every
ordered parent block.  The same append of the two state-cell words is fixed independently of the
block.  A prescribed combined occurrence table therefore puts every compatible parent block in
one conditional type class.  Appending the two raw halves is injective, so the existing exact
conditional-type formula bounds the parent blocks by the product of the cell-row multinomials.

The finite set `cells` only has to cover the cells read from the two sides.  The ambient `Cell`
type may be infinite.  The proof deliberately drops the prescribed paired-parent type and native
support only by embedding the actual `parentBlocks` family into a larger conditional type class;
it does not split the two labelled sides, choose a second state word, prove an asymptotic rate, or
instantiate a tensor extraction or numerical certificate.

## Reference

- [alman2025more] Josh Alman, Ran Duan, Virginia Vassilevska Williams, Yinzhan Xu, Zixuan Xu,
  and Renfei Zhou, *More Asymmetry Yields Faster Matrix Multiplication*.
-/

set_option autoImplicit false

open scoped BigOperators

namespace AlgebraicComplexity.WordType.ReaderIndexedParentModel

universe u v w

variable {State : Type u} {Raw : Type v} {Cell : Type w}

/-- Identity readers embed the paired parent-block family into the conditional type class of its
one combined labelled-occurrence table.

The source word has length `2 * n`: its first half is the left cell of each fixed state position
and its second half is the right cell of that same position.  A parent block is encoded by
appending its left and right raw projections in the same order.  This encoding is injective, and
identity of both readers makes its joint cell/raw multiplicity exactly `nu`.

If the parent-block family is empty, the result is immediate and no legality of `nu` is inferred.
Otherwise one actual block witnesses both legality of the restricted joint table and its fixed
cell marginal, after which `card_conditionalTypeClass_eq_prod_multinomial` applies. -/
theorem card_parentBlocks_le_prod_cellMultinomial_of_identityReaders
    [Fintype State] [Fintype Raw] [DecidableEq Cell]
    (M : ReaderIndexedParentModel State Raw Raw Cell Raw)
    {n : ℕ} (state : Fin n → State)
    (alpha : State → ℕ) (beta : Raw × Raw → ℕ) (nu : Cell × Raw → ℕ)
    (cells : Finset Cell)
    (hleftCell : ∀ s, M.leftCell s ∈ cells)
    (hrightCell : ∀ s, M.rightCell s ∈ cells)
    (hleftReader : ∀ s raw, M.leftReader s raw = raw)
    (hrightReader : ∀ s raw, M.rightReader s raw = raw) :
    (M.parentBlocks state alpha beta nu).card ≤
      ∏ cell : ↑cells,
        Nat.multinomial Finset.univ fun raw ↦ nu (cell.1, raw) := by
  classical
  let source : Fin (n + n) → ↑cells :=
    Fin.append
      (fun i ↦ ⟨M.leftCell (state i), hleftCell (state i)⟩)
      (fun i ↦ ⟨M.rightCell (state i), hrightCell (state i)⟩)
  let encode : (Fin n → Raw × Raw) → Fin (n + n) → Raw :=
    fun block ↦
      Fin.append (fun i ↦ (block i).1) (fun i ↦ (block i).2)
  let jointType : ↑cells × Raw → ℕ :=
    fun entry ↦ nu (entry.1.1, entry.2)
  have hencode : Function.Injective encode := by
    intro left right heq
    funext i
    apply Prod.ext
    · have h := congrFun heq (Fin.castAdd n i)
      simpa only [encode, Fin.append_left] using h
    · have h := congrFun heq (Fin.natAdd n i)
      simpa only [encode, Fin.append_right] using h
  have hencoded_mem (block : Fin n → Raw × Raw)
      (hblock : block ∈ M.parentBlocks state alpha beta nu) :
      encode block ∈ conditionalTypeClass source jointType := by
    rw [mem_conditionalTypeClass]
    have hoccurrence : M.occurrenceProfileOfBlock state block = nu := by
      obtain ⟨joint, hjoint, hrealized⟩ := M.mem_parentBlocks.mp hblock
      calc
        M.occurrenceProfileOfBlock state block =
            M.occurrenceProfileOfType (multiplicity (jointWord state block)) :=
          M.occurrenceProfileOfBlock_eq_occurrenceProfileOfType_multiplicity state block
        _ = M.occurrenceProfileOfType joint := congrArg M.occurrenceProfileOfType hrealized
        _ = nu := (M.mem_feasibleProfiles.mp hjoint).2.2.2.2
    let leftWord : Fin n → ↑cells × Raw :=
      fun i ↦ (⟨M.leftCell (state i), hleftCell (state i)⟩, (block i).1)
    let rightWord : Fin n → ↑cells × Raw :=
      fun i ↦ (⟨M.rightCell (state i), hrightCell (state i)⟩, (block i).2)
    have hword : jointWord source (encode block) = Fin.append leftWord rightWord := by
      funext position
      refine Fin.addCases ?_ ?_ position
      · intro i
        simp only [jointWord, source, encode, leftWord, Fin.append_left]
      · intro i
        simp only [jointWord, source, encode, rightWord, Fin.append_right]
    rw [hword, multiplicity_append]
    funext entry
    obtain ⟨cell, raw⟩ := entry
    simp only [Pi.add_apply, jointType]
    rw [← congrFun hoccurrence (cell.1, raw)]
    unfold multiplicity occurrenceProfileOfBlock
    simp only [occurrenceWeight, hleftReader, hrightReader]
    rw [Finset.card_filter, Finset.card_filter]
    simp only [Finset.sum_add_distrib]
    congr 1
    · apply Finset.sum_congr rfl
      intro i _
      by_cases hcell : M.leftCell (state i) = cell.1 <;>
        by_cases hraw : (block i).1 = raw <;>
          simp [leftWord, hcell, hraw, Prod.ext_iff, Subtype.ext_iff]
    · apply Finset.sum_congr rfl
      intro i _
      by_cases hcell : M.rightCell (state i) = cell.1 <;>
        by_cases hraw : (block i).2 = raw <;>
          simp [rightWord, hcell, hraw, Prod.ext_iff, Subtype.ext_iff]
  by_cases hnonempty : (M.parentBlocks state alpha beta nu).Nonempty
  · obtain ⟨witness, hwitness⟩ := hnonempty
    have hwitnessType :
        multiplicity (jointWord source (encode witness)) = jointType :=
      mem_conditionalTypeClass.mp (hencoded_mem witness hwitness)
    have hjointType : jointType ∈ types (↑cells × Raw) (n + n) := by
      rw [← hwitnessType]
      exact multiplicity_mem_types _
    have hjointTypeFst : mappedType Prod.fst jointType = multiplicity source := by
      rw [← hwitnessType, ← multiplicity_comp_eq_mappedType]
      rfl
    let embedding :
        {block // block ∈ M.parentBlocks state alpha beta nu} →
          {word // word ∈ conditionalTypeClass source jointType} :=
      fun block ↦ ⟨encode block.1, hencoded_mem block.1 block.2⟩
    have hembedding : Function.Injective embedding := by
      intro left right heq
      apply Subtype.ext
      apply hencode
      exact congrArg Subtype.val heq
    have hcard :
        (M.parentBlocks state alpha beta nu).card ≤
          (conditionalTypeClass source jointType).card := by
      simpa only [Fintype.card_coe] using
        Fintype.card_le_of_injective embedding hembedding
    calc
      (M.parentBlocks state alpha beta nu).card ≤
          (conditionalTypeClass source jointType).card := hcard
      _ = ∏ cell : ↑cells,
          Nat.multinomial Finset.univ fun raw ↦ nu (cell.1, raw) := by
        simpa only [jointType] using
          card_conditionalTypeClass_eq_prod_multinomial
            source jointType hjointType hjointTypeFst
  · rw [Finset.not_nonempty_iff_eq_empty.mp hnonempty]
    exact Nat.zero_le _

/-! The private client below makes the hypotheses jointly satisfiable.  Its single ordered parent
position has one self-cell, with raw pair `(false, true)`.  Thus the combined labelled-occurrence
table contains one `false` and one `true`, and the public theorem applies to a nonempty family. -/

private def identityCountTinyModel :
    ReaderIndexedParentModel Unit Bool Bool Unit Bool where
  leftCell := fun _ ↦ ()
  rightCell := fun _ ↦ ()
  leftReader := fun _ raw ↦ raw
  rightReader := fun _ raw ↦ raw
  nativeAdmissible := fun _ _ _ ↦ True

private def identityCountTinyState : Fin 1 → Unit := fun _ ↦ ()

private def identityCountTinyBlock : Fin 1 → Bool × Bool := fun _ ↦ (false, true)

private theorem identityCountTinyBlock_mem :
    identityCountTinyBlock ∈
      identityCountTinyModel.parentBlocks identityCountTinyState
        (multiplicity identityCountTinyState) (multiplicity identityCountTinyBlock)
        (identityCountTinyModel.occurrenceProfileOfBlock
          identityCountTinyState identityCountTinyBlock) := by
  classical
  rw [ReaderIndexedParentModel.mem_parentBlocks]
  let joint := multiplicity (jointWord identityCountTinyState identityCountTinyBlock)
  refine ⟨joint, ?_, rfl⟩
  rw [ReaderIndexedParentModel.mem_feasibleProfiles]
  refine ⟨multiplicity_mem_types _, ?_, ?_, ?_, ?_⟩
  · unfold joint
    rw [← multiplicity_comp_eq_mappedType]
    rfl
  · unfold joint
    rw [← multiplicity_comp_eq_mappedType]
    rfl
  · intro _ _
    trivial
  · exact
      (ReaderIndexedParentModel.occurrenceProfileOfBlock_eq_occurrenceProfileOfType_multiplicity
        identityCountTinyModel identityCountTinyState identityCountTinyBlock).symm

private example :
    let nu := identityCountTinyModel.occurrenceProfileOfBlock
      identityCountTinyState identityCountTinyBlock
    (identityCountTinyModel.parentBlocks identityCountTinyState
        (multiplicity identityCountTinyState) (multiplicity identityCountTinyBlock) nu).Nonempty ∧
      nu ((), false) = 1 ∧
      nu ((), true) = 1 ∧
      (identityCountTinyModel.parentBlocks identityCountTinyState
          (multiplicity identityCountTinyState) (multiplicity identityCountTinyBlock) nu).card ≤
        ∏ cell : ↑({()} : Finset Unit),
          Nat.multinomial Finset.univ fun raw ↦ nu (cell.1, raw) := by
  dsimp only
  refine ⟨⟨identityCountTinyBlock, identityCountTinyBlock_mem⟩, ?_, ?_, ?_⟩
  · simp [identityCountTinyModel, identityCountTinyState, identityCountTinyBlock,
      occurrenceProfileOfBlock, occurrenceWeight]
  · simp [identityCountTinyModel, identityCountTinyState, identityCountTinyBlock,
      occurrenceProfileOfBlock, occurrenceWeight]
  · exact identityCountTinyModel.card_parentBlocks_le_prod_cellMultinomial_of_identityReaders
      identityCountTinyState (multiplicity identityCountTinyState)
      (multiplicity identityCountTinyBlock)
      (identityCountTinyModel.occurrenceProfileOfBlock
        identityCountTinyState identityCountTinyBlock)
      ({()} : Finset Unit) (by simp) (by simp) (by simp [identityCountTinyModel])
      (by simp [identityCountTinyModel])

end AlgebraicComplexity.WordType.ReaderIndexedParentModel
