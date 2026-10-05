/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoLegDigitCount

/-!
# `N_triple` for the six-orientation power: the joint typical-word count

Layer 4 (`AlgebraicComplexity/Examples/`).  `[DuanWuZhou2022]` §6.3's degree `N_triple / N_X` needs
the joint count as well as the marginal one.  `Examples/DuanWuZhouLevelTwoLegDigitCount.lean`
supplied `N_X`; this module supplies `N_triple` for the count lane's own family
`dwz63TargetTypicalWords`, in the same product form.

## The count

A block word of `dwz63SymSixPartition K` of length `n + 1` is, by `dwz63TargetTupleEquiv` and
`mem_dwz63SymSixPartition_support_iff_target`, exactly a six-tuple of *independent* coarse words of
that length, each valued in the fifteen coarse addresses.  Prescribing the same type `a` for all
six therefore counts

`#(typeClass (n+1) a) ^ 6`,

which is `card_dwz63TargetTypedWords`.  Nothing here depends on which profile `a` is, beyond the
requirement that `a` charges only supported addresses --- which the section 6.3 profile
`dwz63AlphaAddress` does, by `mem_cwSquareSupport_of_dwz63AlphaAddress_ne_zero`.

## The bijection, and the one delicate point

The forward map (read the six target sub-words) is elementary.  The inverse --- *assemble* a block
word from six coarse words --- has to build elements of `((dwz63SymSixPartition K).support)`, and
building them directly makes the elaborator try to evaluate that `Finset`.  The assembly is
therefore routed through `Equiv.subtypeEquivRight` at the *predicate* level
(`dwz63SupportedEquiv`), where the six per-orientation support conditions are a plain proposition
and nothing about the ambient `Finset` is ever unfolded.

Primary source: Ran Duan, Hongxun Wu and Renfei Zhou, *Faster Matrix Multiplication via Asymmetric
Hashing*, arXiv:2210.10173, section 6.3.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor

open scoped BigOperators

universe u

/-! ## Supported block labels as a predicate subtype -/

set_option maxRecDepth 8000 in
set_option maxHeartbeats 1000000 in
set_option linter.constructorNameAsVariable false in
/-- **Supported block labels, presented by the six per-orientation conditions rather than by
membership in the ambient `Finset`.**  Elements of this subtype are cheap to build; elements of
`((dwz63SymSixPartition K).support)` are not, because building one asks the elaborator to evaluate
a `Finset` with `15 ^ 6` entries inside a type with `5 ^ 18`. -/
noncomputable def dwz63SupportedEquiv (K : Type u) [CommRing K] :
    {w : BlockAddress DwzSymSixBlock // ∀ o : Fin 6, dwz63TargetLetter o w ∈ cwSquareSupport}
      ≃ ((dwz63SymSixPartition K).support) :=
  Equiv.subtypeEquivRight fun w ↦ (mem_dwz63SymSixPartition_support_iff_target K w).symm

set_option maxRecDepth 8000 in
set_option maxHeartbeats 1000000 in
@[simp] theorem dwz63SupportedEquiv_val (K : Type u) [CommRing K]
    (x : {w : BlockAddress DwzSymSixBlock //
      ∀ o : Fin 6, dwz63TargetLetter o w ∈ cwSquareSupport}) :
    (dwz63SupportedEquiv K x).val = x.val := by
  rw [dwz63SupportedEquiv, Equiv.subtypeEquivRight_apply]

/-! ## Assembling a block word from six coarse words -/

set_option maxRecDepth 8000 in
set_option maxHeartbeats 1000000 in
/-- **Assemble a six-orientation block word from six supported coarse words**, position by
position: the inverse of reading the six target sub-words. -/
noncomputable def dwz63AssembleTargetWord (K : Type u) [CommRing K] (n : ℕ)
    (f : Fin 6 → Fin (n + 1) → CWSquareAddress)
    (hf : ∀ (j : Fin (n + 1)) (o : Fin 6), f o j ∈ cwSquareSupport) :
    PositiveWord ((dwz63SymSixPartition K).support) n :=
  (positiveWordEquiv _ n).symm fun j ↦
    dwz63SupportedEquiv K ⟨dwz63TargetTupleEquiv.symm fun o ↦ f o j, fun o ↦ by
      rw [dwz63TargetLetter_dwz63TargetTupleEquiv_symm]
      exact hf j o⟩

set_option maxRecDepth 8000 in
set_option maxHeartbeats 1000000 in
/-- Reading the assembled word's `o`-th target sub-word returns the `o`-th input word. -/
theorem dwz63TargetWord_dwz63AssembleTargetWord (K : Type u) [CommRing K] (n : ℕ)
    (f : Fin 6 → Fin (n + 1) → CWSquareAddress)
    (hf : ∀ (j : Fin (n + 1)) (o : Fin 6), f o j ∈ cwSquareSupport) (o : Fin 6) :
    dwz63TargetWord K n o (dwz63AssembleTargetWord K n f hf) = f o := by
  funext j
  unfold dwz63TargetWord dwz63AssembleTargetWord
  rw [Equiv.apply_symm_apply, dwz63SupportedEquiv_val,
    dwz63TargetLetter_dwz63TargetTupleEquiv_symm]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 1000000 in
/-- Assembling a word from its own six target sub-words returns the word. -/
theorem dwz63AssembleTargetWord_dwz63TargetWord (K : Type u) [CommRing K] (n : ℕ)
    (q : PositiveWord ((dwz63SymSixPartition K).support) n)
    (hf : ∀ (j : Fin (n + 1)) (o : Fin 6), dwz63TargetWord K n o q j ∈ cwSquareSupport) :
    dwz63AssembleTargetWord K n (fun o ↦ dwz63TargetWord K n o q) hf = q := by
  unfold dwz63AssembleTargetWord
  refine (Equiv.symm_apply_eq _).mpr ?_
  funext j
  refine Subtype.ext ?_
  rw [dwz63SupportedEquiv_val]
  exact dwz63TargetTupleEquiv.symm_apply_apply _

/-! ## The joint typical-word count -/

/-- **The block words all six of whose target sub-words carry a prescribed type.** -/
noncomputable def dwz63TargetTypedWords (K : Type u) [CommRing K] (n : ℕ)
    (a : CWSquareAddress → ℕ) : Finset (PositiveWord ((dwz63SymSixPartition K).support) n) := by
  classical
  exact Finset.univ.filter fun q ↦ ∀ o : Fin 6, WordType.multiplicity (dwz63TargetWord K n o q) = a

set_option maxRecDepth 8000 in
set_option maxHeartbeats 1000000 in
@[simp] theorem mem_dwz63TargetTypedWords {K : Type u} [CommRing K] {n : ℕ}
    {a : CWSquareAddress → ℕ} {q : PositiveWord ((dwz63SymSixPartition K).support) n} :
    q ∈ dwz63TargetTypedWords K n a ↔
      ∀ o : Fin 6, WordType.multiplicity (dwz63TargetWord K n o q) = a := by
  classical
  simp [dwz63TargetTypedWords]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 1000000 in
-- ELABORATION RISK: `Finset.card_bij'` takes its two maps first and then `hi`, `hj`,
-- `left_inv`, `right_inv`.  Fallback if that order differs: `Finset.card_bij` with the
-- injectivity of `dwz63TargetTupleEquiv` and surjectivity from `dwz63AssembleTargetWord`.
/-- **The joint count factorizes into six multinomial type classes.**

The six target letters of a supported block label range independently over the fifteen coarse
addresses (`mem_dwz63SymSixPartition_support_iff_target`), so prescribing one type for all six
counts its type class six times over.  The hypothesis is only that the prescribed type charges no
unsupported address, which is what confines the assembled label to the support. -/
theorem card_dwz63TargetTypedWords (K : Type u) [CommRing K] (n : ℕ) (a : CWSquareAddress → ℕ)
    (ha : ∀ s : CWSquareAddress, a s ≠ 0 → s ∈ cwSquareSupport) :
    (dwz63TargetTypedWords K n a).card = (WordType.typeClass (n + 1) a).card ^ 6 := by
  classical
  have hsupp : ∀ f : Fin 6 → Fin (n + 1) → CWSquareAddress,
      f ∈ Fintype.piFinset (fun _ : Fin 6 ↦ WordType.typeClass (n + 1) a) →
      ∀ (j : Fin (n + 1)) (o : Fin 6), f o j ∈ cwSquareSupport := by
    intro f hf j o
    refine ha _ ?_
    have hm : WordType.multiplicity (f o) = a :=
      WordType.mem_typeClass.mp (Fintype.mem_piFinset.mp hf o)
    have hne := WordType.multiplicity_apply_ne_zero (f o) j
    rw [hm] at hne
    exact hne
  have hpi : (Fintype.piFinset fun _ : Fin 6 ↦ WordType.typeClass (n + 1) a).card
      = (WordType.typeClass (n + 1) a).card ^ 6 := by
    rw [Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [← hpi]
  refine Finset.card_bij'
    (fun q _ ↦ fun o ↦ dwz63TargetWord K n o q)
    (fun f hf ↦ dwz63AssembleTargetWord K n f (hsupp f hf))
    ?_ ?_ ?_ ?_
  · intro q hq
    exact Fintype.mem_piFinset.mpr fun o ↦
      WordType.mem_typeClass.mpr (mem_dwz63TargetTypedWords.mp hq o)
  · intro f hf
    refine mem_dwz63TargetTypedWords.mpr fun o ↦ ?_
    rw [dwz63TargetWord_dwz63AssembleTargetWord]
    exact WordType.mem_typeClass.mp (Fintype.mem_piFinset.mp hf o)
  · intro q _
    exact dwz63AssembleTargetWord_dwz63TargetWord K n q _
  · intro f _
    funext o
    exact dwz63TargetWord_dwz63AssembleTargetWord K n f _ o

/-! ## `N_triple` at scale `t` -/

set_option maxRecDepth 8000 in
set_option maxHeartbeats 1000000 in
/-- **The count lane's target-typical family is the typed family at the section 6.3 profile.**
`Dwz63TargetTypical` unfolds to exactly the six conditions `dwz63TargetTypedWords` filters by. -/
theorem dwz63TargetTypicalWords_eq (K : Type u) [CommRing K] (n t : ℕ) :
    dwz63TargetTypicalWords K n t =
      dwz63TargetTypedWords K n (WordType.proportionalCounts dwz63AlphaAddress t) := by
  ext q
  rw [mem_dwz63TargetTypicalWords, mem_dwz63TargetTypedWords]
  exact Iff.rfl

set_option maxRecDepth 8000 in
set_option maxHeartbeats 1000000 in
/-- **`[DuanWuZhou2022]`'s `N_triple` for the six-orientation power at scale `t`**: the number of
target-typical block words, i.e. the cardinality of the count lane's own marked family. -/
noncomputable def dwz63JointTypicalCount (K : Type u) [CommRing K] (n t : ℕ) : ℕ :=
  (dwz63TargetTypicalWords K n t).card

set_option maxRecDepth 8000 in
set_option maxHeartbeats 1000000 in
/-- **`N_triple` is the sixth power of one multinomial type class.** -/
theorem dwz63JointTypicalCount_eq (K : Type u) [CommRing K] (n t : ℕ) :
    dwz63JointTypicalCount K n t =
      (WordType.typeClass (n + 1) (WordType.proportionalCounts dwz63AlphaAddress t)).card ^ 6 := by
  rw [dwz63JointTypicalCount, dwz63TargetTypicalWords_eq]
  exact card_dwz63TargetTypedWords K n _ fun _ hs ↦
    mem_cwSquareSupport_of_proportionalCounts_ne_zero hs

set_option maxRecDepth 8000 in
set_option maxHeartbeats 1000000 in
/-- At the forced word length the repeated fifteen-cell profile is a legal type. -/
theorem proportionalCounts_dwz63AlphaAddress_mem_types {n t : ℕ} (hn : n + 1 = 100000000 * t) :
    WordType.proportionalCounts dwz63AlphaAddress t ∈ WordType.types CWSquareAddress (n + 1) := by
  rw [WordType.mem_types, hn]
  show ∑ s, dwz63AlphaAddress s * t = 100000000 * t
  rw [← Finset.sum_mul,
    show (∑ s, dwz63AlphaAddress s) = WordType.profileMass dwz63AlphaAddress from rfl,
    profileMass_dwz63AlphaAddress]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 1000000 in
/-- **`N_triple` is positive** at the forced word length. -/
theorem dwz63JointTypicalCount_pos (K : Type u) [CommRing K] {n t : ℕ}
    (hn : n + 1 = 100000000 * t) : 0 < dwz63JointTypicalCount K n t := by
  rw [dwz63JointTypicalCount_eq]
  refine pow_pos ?_ 6
  rw [Finset.card_pos]
  exact WordType.typeClass_nonempty _ (proportionalCounts_dwz63AlphaAddress_mem_types hn)

set_option maxRecDepth 8000 in
set_option maxHeartbeats 1000000 in
/-- **The exponential rate of `N_triple`**, loss-free after a cutoff: every base strictly below the
fifteen-cell profile's own entropy rate is attained by `N_triple` itself, at the sixth power the
six orientations contribute. -/
theorem dwz63_exists_cutoff_pow_le_dwz63JointTypicalCount (K : Type u) [CommRing K]
    {lowerBase : ℝ} (hlower : 0 < lowerBase)
    (hlt : lowerBase < (2 : ℝ) ^ ((WordType.profileMass dwz63AlphaAddress : ℝ) *
      WordType.profileEntropyBits dwz63AlphaAddress)) :
    ∃ cutoff : ℕ, ∀ t : ℕ, cutoff ≤ t → ∀ n : ℕ, n + 1 = 100000000 * t →
      lowerBase ^ (6 * t) ≤ ((dwz63JointTypicalCount K n t : ℕ) : ℝ) := by
  have hmass : 0 < WordType.profileMass dwz63AlphaAddress := by
    rw [profileMass_dwz63AlphaAddress]; norm_num
  obtain ⟨cutoff, hcut⟩ :=
    WordType.exists_cutoff_forall_pow_le_card_proportionalTypeClass dwz63AlphaAddress hmass
      hlower hlt
  refine ⟨cutoff, fun t ht n hn ↦ ?_⟩
  have hclass := hcut t ht
  rw [profileMass_dwz63AlphaAddress, ← hn] at hclass
  rw [dwz63JointTypicalCount_eq, Nat.cast_pow, mul_comm 6 t, pow_mul]
  exact pow_le_pow_left₀ (pow_pos hlower t).le hclass 6

/-! ## The sharp degree at these two counts -/

set_option maxRecDepth 8000 in
set_option maxHeartbeats 1000000 in
/-- **The sharp leg-fiber degree at the two counts of this development**, `N_triple / N_X + 1`.
`dwz63SharpDegree_spec` applies to it because `N_X` is positive at the forced word length
(`dwz63XTypicalCount_pos`). -/
noncomputable def dwz63TargetSharpDegree (K : Type u) [CommRing K] (n t : ℕ) : ℕ :=
  dwz63SharpDegree (dwz63JointTypicalCount K n t) (dwz63XTypicalCount n t)

set_option maxRecDepth 8000 in
set_option maxHeartbeats 1000000 in
/-- The division-free defining inequality at the two counts. -/
theorem dwz63JointTypicalCount_le (K : Type u) [CommRing K] {n t : ℕ}
    (hn : n + 1 = 100000000 * t) :
    dwz63JointTypicalCount K n t ≤
      dwz63XTypicalCount n t * dwz63TargetSharpDegree K n t :=
  dwz63SharpDegree_spec _ _ (dwz63XTypicalCount_pos hn)

/-! ## The leg-label word of a block word, and its six digit marginals -/

set_option maxRecDepth 8000 in
set_option maxHeartbeats 1000000 in
/-- **The leg-`c` label word of a six-orientation block word**, a word of length `n + 1` over the
six-tuples of base-five digits.  For `c = .X` this is the object `[DuanWuZhou2022]` §6.3's hashing
branch counts, and `dwz63LegTypedWords` is the family it lands in. -/
noncomputable def dwz63LegWord (K : Type u) [CommRing K] (n : ℕ) (c : Leg)
    (q : PositiveWord ((dwz63SymSixPartition K).support) n) : Fin (n + 1) → DwzSymSixBlock .X :=
  fun j ↦ (positiveWordEquiv _ n q j).val c

set_option maxRecDepth 8000 in
set_option maxHeartbeats 1000000 in
/-- **The `o`-th digit sub-word of the leg-`c` label word is the leg-`c` reading of the `o`-th
target sub-word.**  Reading a digit and reading a leg commute, because the target reading applies
no transport. -/
theorem dwz63SymSixDigit_dwz63LegWord (K : Type u) [CommRing K] (n : ℕ) (c : Leg) (o : Fin 6)
    (q : PositiveWord ((dwz63SymSixPartition K).support) n) :
    (fun j ↦ dwz63SymSixDigit o (dwz63LegWord K n c q j))
      = (fun s : CWSquareAddress ↦ s c) ∘ dwz63TargetWord K n o q := by
  funext j
  exact (dwz63TargetLetter_apply o _ c).symm

set_option maxRecDepth 8000 in
set_option maxHeartbeats 1000000 in
/-- **The marginal corollary.**

If all six target sub-words of `q` carry the repeated fifteen-cell profile, then every one of the
six digit sub-words of every leg label word carries that leg's repeated coordinate marginal:
`α_X` on the `X` and `Y` legs, `α_Z` on the `Z` leg --- the same table for all six orientations,
because the target reading applies no leg permutation. -/
theorem multiplicity_dwz63SymSixDigit_dwz63LegWord (K : Type u) [CommRing K] (n t : ℕ) (c : Leg)
    (o : Fin 6) {q : PositiveWord ((dwz63SymSixPartition K).support) n}
    (hq : q ∈ dwz63TargetTypicalWords K n t) :
    WordType.multiplicity (fun j ↦ dwz63SymSixDigit o (dwz63LegWord K n c q j))
      = WordType.proportionalCounts (dwz63AlphaMarginal c) t := by
  rw [dwz63TargetTypicalWords_eq] at hq
  rw [dwz63SymSixDigit_dwz63LegWord, WordType.multiplicity_comp_eq_mappedType,
    mem_dwz63TargetTypedWords.mp hq o, mappedType_legRead_proportionalCounts]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 1000000 in
/-- **The leg label word of a jointly typical word is leg-typical.**  This is the containment the
sharp-degree fiber bound consumes: every jointly typical word has its `X` label word inside the
family `N_X` counts. -/
theorem dwz63LegWord_mem_dwz63LegTypedWords (K : Type u) [CommRing K] (n t : ℕ) (c : Leg)
    {q : PositiveWord ((dwz63SymSixPartition K).support) n}
    (hq : q ∈ dwz63TargetTypicalWords K n t) :
    dwz63LegWord K n c q ∈
      dwz63LegTypedWords n (WordType.proportionalCounts (dwz63AlphaMarginal c) t) :=
  mem_dwz63LegTypedWords.mpr fun o ↦
    multiplicity_dwz63SymSixDigit_dwz63LegWord K n t c o hq

set_option maxRecDepth 8000 in
set_option maxHeartbeats 1000000 in
/-- The `X` case, at the committed five-letter table. -/
theorem dwz63LegWord_X_mem_dwz63LegTypedWords (K : Type u) [CommRing K] (n t : ℕ)
    {q : PositiveWord ((dwz63SymSixPartition K).support) n}
    (hq : q ∈ dwz63TargetTypicalWords K n t) :
    dwz63LegWord K n .X q ∈
      dwz63LegTypedWords n (WordType.proportionalCounts dwz63AlphaX t) :=
  dwz63LegWord_mem_dwz63LegTypedWords K n t .X hq

set_option maxRecDepth 8000 in
set_option maxHeartbeats 1000000 in
/-- The `Z` case, at the committed five-letter table. -/
theorem dwz63LegWord_Z_mem_dwz63LegTypedWords (K : Type u) [CommRing K] (n t : ℕ)
    {q : PositiveWord ((dwz63SymSixPartition K).support) n}
    (hq : q ∈ dwz63TargetTypicalWords K n t) :
    dwz63LegWord K n .Z q ∈
      dwz63LegTypedWords n (WordType.proportionalCounts dwz63AlphaZ t) :=
  dwz63LegWord_mem_dwz63LegTypedWords K n t .Z hq

end AlgebraicComplexity.Examples
