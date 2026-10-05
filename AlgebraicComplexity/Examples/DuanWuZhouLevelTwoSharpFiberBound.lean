/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoTargetWordCount

/-!
# The sharp leg-fiber degree, discharged at one joint block-label type

Layer 4 (`AlgebraicComplexity/Examples/`).  `Examples/DuanWuZhouLevelTwoSharpDegree.lean` reduces
hash retention to a single obligation: a certified bound on the size of a *leg fiber* of legal
hashing targets.  `[DuanWuZhou2022]` §6.3's bound for it is `N_triple / N_X`, and
`dwz63SharpDegree` is that quotient in rounded, division-free form.  This module proves the fiber
bound.

## The counting identity

For a family `words` of supported block words that all carry **one** joint block-label type `a`,
the leg-`c` fiber of a legal target injects into the typed coordinatewise word fiber
(`PartitionHashEncoding.card_legFiber_legalTargets_le_card_typedWordMapFiber`), and that fiber is
counted exactly by `WordType.card_targetType_mul_card_typedWordMapFiber`:

`#(typeClass (n+1) (mappedType legRead a)) * #(typedWordMapFiber legRead a target)
   = #(typeClass (n+1) a)`.

So the fiber is *exactly* `N_triple / N_X` --- an equality, not an estimate --- and
`card_legFiber_le_sharpDegree` is the rounded consequence.  No conditional type class is needed:
`card_targetType_mul_card_typedWordMapFiber` already is the conditional method-of-types formula in
the form this obligation wants.

## One joint type, not six marginals

The hypothesis `hwords` of the committed injection asks that *all* words of the family share a
single multiplicity profile on the `15 ^ 6`-letter block-label alphabet.  Target typicality
(`Dwz63TargetTypical`) fixes only the six coarse marginals of that profile, so the target-typical
family is a **union** of joint type classes, not one of them.  `dwz63JointTypedWords` is the
refinement to one type, and `dwz63JointTypedWords_subset_targetTypicalWords` records that the
refinement is compatible: as soon as the fixed type's six target marginals are the section 6.3
ones, every word of the refined family is target typical, so all of
`Examples/DuanWuZhouLevelTwoTargetWordCount.lean`'s marginal machinery still applies to it.

Primary source: Ran Duan, Hongxun Wu and Renfei Zhou, *Faster Matrix Multiplication via Asymmetric
Hashing*, arXiv:2210.10173, section 6.3.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor

open scoped BigOperators

universe u v w

/-! ## The fiber bound, for an arbitrary partition hash encoding -/

/-- **The leg fiber of a legal hashing target is exactly the multinomial quotient.**

For a family of supported block words all carrying one joint block-label type `a`, the number of
legal targets sharing a target's leg-`c` block word is `#(typeClass a) / #(typeClass (legRead_* a))`
--- `[DuanWuZhou2022]`'s `N_triple / N_X` --- and hence at most `dwz63SharpDegree` of the two
counts.  This is the whole content of the `hsharp` obligation of
`Examples/DuanWuZhouLevelTwoSharpDegree.lean`, for a family-matched fiber. -/
theorem card_legFiber_le_sharpDegree
    {R : Type v} [Field R] {A : Leg → Type w} [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]
    {support : Finset (BlockAddress A)}
    (H : PartitionHashEncoding (R := R) support) (n : ℕ)
    (words : Finset (PositiveWord support n)) (a : support → ℕ)
    (hwords : ∀ q ∈ words, WordType.multiplicity (positiveWordEquiv support n q) = a)
    {triple : ProgressionHash.LegalTriple R (Fin (n + 1)) H.target}
    (htriple : triple ∈ H.legalTargets n words) (c : Leg) :
    (ProgressionHash.LegalTriple.legFiber (H.legalTargets n words) triple c).card ≤
      dwz63SharpDegree (WordType.typeClass (n + 1) a).card
        (WordType.typeClass (n + 1)
          (WordType.mappedType (fun s : support ↦ (s : BlockAddress A) c) a)).card := by
  classical
  have hq : H.sourceWordOfLegalTriple n triple ∈ words :=
    H.sourceWordOfLegalTriple_mem_of_mem n words htriple
  have htargetEq :
      positiveWordEquiv (A c) n (H.modeledAddress n triple c)
        = (fun s : support ↦ (s : BlockAddress A) c) ∘
            positiveWordEquiv support n (H.sourceWordOfLegalTriple n triple) :=
    PartitionHashEncoding.positiveWordEquiv_supportWordAddress n
      (H.sourceWordOfLegalTriple n triple) c
  have hmem : positiveWordEquiv (A c) n (H.modeledAddress n triple c) ∈
      WordType.typeClass (n + 1)
        (WordType.mappedType (fun s : support ↦ (s : BlockAddress A) c) a) := by
    rw [WordType.mem_typeClass, htargetEq, WordType.multiplicity_comp_eq_mappedType, hwords _ hq]
  have hfib := H.card_legFiber_legalTargets_le_card_typedWordMapFiber n words a hwords htriple c
  have hprod := WordType.card_targetType_mul_card_typedWordMapFiber
    (fun s : support ↦ (s : BlockAddress A) c) a
    (positiveWordEquiv (A c) n (H.modeledAddress n triple c)) hmem
  have hxpos : 0 < (WordType.typeClass (n + 1)
      (WordType.mappedType (fun s : support ↦ (s : BlockAddress A) c) a)).card :=
    Finset.card_pos.mpr ⟨_, hmem⟩
  have hdiv : (WordType.typeClass (n + 1) a).card /
      (WordType.typeClass (n + 1)
        (WordType.mappedType (fun s : support ↦ (s : BlockAddress A) c) a)).card
      = (WordType.typedWordMapFiber (fun s : support ↦ (s : BlockAddress A) c) a
          (positiveWordEquiv (A c) n (H.modeledAddress n triple c))).card := by
    refine Nat.div_eq_of_eq_mul_left hxpos ?_
    rw [← hprod]
    ring
  refine hfib.trans ?_
  unfold dwz63SharpDegree
  rw [hdiv]
  exact Nat.le_succ _

/-! ## The refinement of the marked family to one joint type -/

set_option maxRecDepth 8000 in
set_option maxHeartbeats 1000000 in
/-- **The block words of one fixed joint block-label type.**  This is the family `hsharp`'s
counting hypothesis needs: `dwz63TargetTypicalWords` fixes only six coarse marginals, so it is a
union of these. -/
noncomputable def dwz63JointTypedWords (K : Type u) [CommRing K] (n : ℕ)
    (a : ((dwz63SymSixPartition K).support) → ℕ) :
    Finset (PositiveWord ((dwz63SymSixPartition K).support) n) := by
  classical
  exact Finset.univ.filter fun q ↦
    WordType.multiplicity (positiveWordEquiv _ n q) = a

set_option maxRecDepth 8000 in
set_option maxHeartbeats 1000000 in
@[simp] theorem mem_dwz63JointTypedWords {K : Type u} [CommRing K] {n : ℕ}
    {a : ((dwz63SymSixPartition K).support) → ℕ}
    {q : PositiveWord ((dwz63SymSixPartition K).support) n} :
    q ∈ dwz63JointTypedWords K n a ↔
      WordType.multiplicity (positiveWordEquiv _ n q) = a := by
  classical
  simp [dwz63JointTypedWords]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 1000000 in
/-- The refined family is a block-label type class, transported through `positiveWordEquiv`. -/
theorem card_dwz63JointTypedWords (K : Type u) [CommRing K] (n : ℕ)
    (a : ((dwz63SymSixPartition K).support) → ℕ) :
    (dwz63JointTypedWords K n a).card = (WordType.typeClass (n + 1) a).card := by
  classical
  refine Finset.card_equiv (positiveWordEquiv _ n) fun q ↦ ?_
  rw [mem_dwz63JointTypedWords, WordType.mem_typeClass]

/-! ## The section 6.3 instance -/

set_option maxRecDepth 8000 in
set_option maxHeartbeats 1000000 in
/-- **A refined family whose six target marginals are the section 6.3 ones is target typical.**
So the whole marginal apparatus of `Examples/DuanWuZhouLevelTwoTargetWordCount.lean` survives the
refinement to a single joint type. -/
theorem dwz63JointTypedWords_subset_targetTypicalWords (K : Type u) [CommRing K] (n t : ℕ)
    (a : ((dwz63SymSixPartition K).support) → ℕ)
    (ha : ∀ o : Fin 6,
      WordType.mappedType
          (fun s : ((dwz63SymSixPartition K).support) ↦ dwz63TargetLetter o s.val) a =
        WordType.proportionalCounts dwz63AlphaAddress t) :
    dwz63JointTypedWords K n a ⊆ dwz63TargetTypicalWords K n t := by
  intro q hq
  refine mem_dwz63TargetTypicalWords.mpr fun o ↦ ?_
  have hword : WordType.multiplicity (positiveWordEquiv _ n q) = a :=
    mem_dwz63JointTypedWords.mp hq
  have hcomp : dwz63TargetWord K n o q
      = (fun s : ((dwz63SymSixPartition K).support) ↦ dwz63TargetLetter o s.val) ∘
        positiveWordEquiv _ n q := rfl
  rw [hcomp, WordType.multiplicity_comp_eq_mappedType, hword, ha o]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 1000000 in
/-- **The `hsharp` obligation, discharged at one joint type.**

For the refined marked family, every leg fiber of a legal target is bounded by the sharp degree
built from that family's own two counts.  Note the fiber is taken inside the *marked* family's
legal targets; see the module note in the count lane's report for the ambient variant. -/
theorem card_legFiber_le_dwz63SharpDegree (K : Type u) [CommRing K] {R : Type v} [Field R]
    {p : ℕ} [CharP R p] (hp : 15625 ≤ p) (n : ℕ)
    (a : ((dwz63SymSixPartition K).support) → ℕ) (c : Leg)
    {triple : ProgressionHash.LegalTriple R (Fin (n + 1))
      (dwz63SymSixHashEncoding K R hp).target}
    (htriple : triple ∈ (dwz63SymSixHashEncoding K R hp).legalTargets n
      (dwz63JointTypedWords K n a)) :
    (ProgressionHash.LegalTriple.legFiber
      ((dwz63SymSixHashEncoding K R hp).legalTargets n (dwz63JointTypedWords K n a))
      triple c).card ≤
      dwz63SharpDegree (dwz63JointTypedWords K n a).card
        (WordType.typeClass (n + 1)
          (WordType.mappedType
            (fun s : ((dwz63SymSixPartition K).support) ↦ s.val c) a)).card := by
  rw [card_dwz63JointTypedWords]
  exact card_legFiber_le_sharpDegree (dwz63SymSixHashEncoding K R hp) n
    (dwz63JointTypedWords K n a) a (fun _ hq ↦ mem_dwz63JointTypedWords.mp hq) htriple c

end AlgebraicComplexity.Examples
