/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoPlainMarkedBranch
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoTripleEntropyBound
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoSupportBridge

set_option autoImplicit false

/-!
# The joint-class hash loss, and the marginal-to-joint passage

Layer 4 (`AlgebraicComplexity/Examples/`).  `Examples/DuanWuZhouLevelTwoPlainMarkedBranch.lean`'s
`exists_behrend_dwz63_plainHashBranch` proves the hashing-branch input at the **marginal-typical**
family `dwz63PlainMarginalWords`.  The assembly lane's `hwitness` is available only at the
**joint** type class `dwz63MarkedWords`, so the batched endpoint's `hbranch` binder has to be
discharged there.  This module supplies the two ingredients of that move --- the enlarged loss and
the counting passage from the marginal family to the joint class --- and
`Examples/DuanWuZhouLevelTwoMarkedHashBranch.lean` assembles the branch itself.

## Notation: the field type and the hash-loss multiplier

Two different things are called `K` in the surrounding prose, and they are kept apart here.  `K` is
the **field type parameter** of every declaration below.  `hashMult` is this module's shorthand for
the committed real constant `dwz63HashLossMultiplier`, which is what the exponential factor
`hashMult ^ (n+1)` below refers to.  The claim proved downstream is that the *exponential power* of
`hashMult` cancels --- not that any definition is syntactically independent of the field type `K`,
which it is not: `dwz63PlainMarkedLossHashJoint` takes `K` as an argument.

## Where the hash-loss multiplier goes

Passing from the marginal family to the joint class costs exactly `[duan2023faster]`'s hash loss:

`N_triple ≤ typeCountLoss · e ^ ((n+1)(H(alpha) + log hashMult))`
`         = typeCountLoss · hashMult ^ (n+1) · e ^ ((n+1) H(alpha))`

by `dwz63_card_tripleSet_le_typeCountLoss_mul` at the discharged `dwz63_tripleEntropyBound`, and
`e ^ ((n+1) H(alpha)) ≤ structuralZeroMultinomialLoss · N_alpha` by the zero-safe method of
types.  The factor `hashMult ^ (n+1)` is **not** subexponential, so it may not sit in the loss.
It does not have to: `dwz63HashingBranch = e ^ H(alpha_X) / hashMult` carries
`hashMult ^ -(n+1)`, and the two cancel.  Concretely the chain is run at `e ^ H(alpha_X)` rather
than at the branch —

`e ^ (H(alpha_X)(n+1)) ≤ loss_X · N_X`,  `N_X · d ≤ 2 · N_alpha'`,
`N_alpha' ≤ typeCountLoss · hashMult ^ (n+1) · loss_alpha · N_alpha`

— and `e ^ (H(alpha_X)(n+1)) = dwz63HashingBranch ^ (n+1) · hashMult ^ (n+1)`, so dividing by
`hashMult ^ (n+1)` leaves the branch against a loss with no `hashMult` in it at all.  That is
`dwz63PlainMarkedLossHashJoint`, the committed `dwz63PlainMarkedLossHash` enlarged by the two
committed subexponential factors `typeCountLoss (Fin 15)` and
`structuralZeroMultinomialLoss dwz63Alpha`.

## The identification of the two families

`dwz63PlainMarginalWords K n t` and `Examples/DuanWuZhouLevelTwoSupportBridge.lean`'s
`dwz63AmbientWords n alpha_X alpha_X alpha_Z` are the same Finset: both cut the square-support
words by the three transposed leg types, and
`PartitionHashEncoding.positiveWordEquiv_supportWordAddress` identifies the two spellings of the
cut.  The alphabets `↥((cwSquarePartitionedTensor K dwz63Q).support)` and `CWSquareSupport` are
definitionally but not syntactically equal, so the identification is by `Finset.ext` in term mode
and never by `rw` across the boundary.

Primary source: `[duan2023faster]` --- Ran Duan, Hongxun Wu and Renfei Zhou, *Faster Matrix
Multiplication via Asymmetric Hashing*, arXiv:2210.10173.  The fixed-marginal count is
`papers/sources/2210.10173/hashing.tex:60-70` (`lem:numtriple_singledist` at `:63-70`), and its
use in the section 6.2 analysis is `papers/sources/2210.10173/global_value.tex:130-140,292-323`.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor

open scoped BigOperators

universe u

/-! ## The enlarged loss -/

/-- **The hash loss at the joint type class**: the committed marginal loss enlarged by the two
factors the marginal-to-joint passage costs.  No hash-loss multiplier appears — see the module
docstring. -/
noncomputable def dwz63PlainMarkedLossHashJoint (K : Type u) [CommRing K] (N : ℕ) : ℝ :=
  dwz63PlainMarkedLossHash K N * WordType.typeCountLoss (Fin 15) N *
    WordType.structuralZeroMultinomialLoss dwz63Alpha (N / 100000000)

theorem dwz63PlainMarkedLossHashJoint_pos (K : Type u) [CommRing K] (N : ℕ) :
    0 < dwz63PlainMarkedLossHashJoint K N :=
  mul_pos (mul_pos (dwz63PlainMarkedLossHash_pos K N) (WordType.typeCountLoss_pos _ _))
    (WordType.structuralZeroMultinomialLoss_pos _ _)

theorem dwz63PlainMarkedLossHashJoint_nonneg (K : Type u) [CommRing K] (N : ℕ) :
    0 ≤ dwz63PlainMarkedLossHashJoint K N :=
  (dwz63PlainMarkedLossHashJoint_pos K N).le

/-- The enlarged loss is still subexponential: a product of three committed subexponential
factors, the last precomposed with `N ↦ N / 10 ^ 8`. -/
theorem subexponential_dwz63PlainMarkedLossHashJoint (K : Type u) [CommRing K] :
    Growth.Subexponential (dwz63PlainMarkedLossHashJoint K) :=
  ((subexponential_dwz63PlainMarkedLossHash K).mul
      (WordType.typeCountLoss_subexponential (Fin 15))).mul
    (dwz63_subexponential_comp_of_le_self
      (WordType.structuralZeroMultinomialLoss_subexponential dwz63Alpha)
      (fun N ↦ N / 100000000) (fun _ ↦ Nat.div_le_self _ _))

/-! ## The marginal family is the bridge's ambient family -/

-- ELABORATION RISK: the two alphabets `↥((cwSquarePartitionedTensor K dwz63Q).support)` and
-- `CWSquareSupport` are definitionally, not syntactically, equal (image 124's note).  `Finset.ext`
-- is applied in term position so that the elaborator checks the two Finset types by defeq; a `rw`
-- across this boundary fails.
/-- **The marginal-typical family is the bridge's ambient family.**

Proof sketch: `Finset.ext`, applied in term position so that the elaborator checks the two Finset
types by defeq (the note above).  Membership on the left is
`mem_dwz63PlainMarginalWords` --- the three transposed leg words of the address have the
proportional leg profiles --- and on the right `mem_dwz63AmbientWords`.  Two rewritings make the
two readings the same statement: `PartitionHashEncoding.positiveWordEquiv_supportWordAddress`
identifies the transposed leg word of a supported word with the leg component of its letters, and
a three-way case split on the leg (`cases c <;> rfl`) identifies `dwz63LegProfile` at the three
proportional counts with `proportionalCounts (dwz63AlphaMarginal c) t`.  Both directions are then
the same three conjuncts.  No cardinality or estimate enters; this is an equality of Finsets. -/
theorem dwz63_plainMarginalWords_eq_ambientWords (K : Type u) [CommRing K] (n t : ℕ) :
    dwz63PlainMarginalWords K n t =
      dwz63AmbientWords n (WordType.proportionalCounts dwz63AlphaX t)
        (WordType.proportionalCounts dwz63AlphaX t)
        (WordType.proportionalCounts dwz63AlphaZ t) := by
  classical
  refine Finset.ext fun q ↦ Iff.trans mem_dwz63PlainMarginalWords
    (Iff.trans ?_ mem_dwz63AmbientWords.symm)
  have hleg : ∀ c : Leg,
      positiveWordEquiv (Fin 5) n
          (PartitionHashEncoding.supportWordAddress (A := fun _ : Leg ↦ Fin 5)
            (support := cwSquareSupport) n q c) =
        fun j ↦ ((positiveWordEquiv _ n q j).val c) :=
    fun c ↦ PartitionHashEncoding.positiveWordEquiv_supportWordAddress
      (A := fun _ : Leg ↦ Fin 5) (support := cwSquareSupport) n q c
  have hprof : ∀ c : Leg,
      dwz63LegProfile (WordType.proportionalCounts dwz63AlphaX t)
        (WordType.proportionalCounts dwz63AlphaX t)
        (WordType.proportionalCounts dwz63AlphaZ t) c =
      WordType.proportionalCounts (dwz63AlphaMarginal c) t := by
    intro c
    cases c <;> rfl
  constructor
  · intro h c
    rw [hleg c, hprof c]
    exact h c
  · intro h c
    have := h c
    rw [hleg c, hprof c] at this
    exact this

/-! ## The marginal-to-joint passage -/

set_option maxRecDepth 8000 in
/-- **The marginal family costs `typeCountLoss · hashMult ^ (n+1) · loss` over the joint class.**

`dwz63_card_tripleSet_le_typeCountLoss_mul` at the discharged `dwz63_tripleEntropyBound`, composed
with the zero-safe lower bound for the joint type class.  (`hashMult` is
`dwz63HashLossMultiplier`; `K` is the field type parameter, which the statement also carries.)

Proof sketch: the marginal family's cardinality is the triple count, by
`dwz63_plainMarginalWords_eq_ambientWords` and the committed `card_dwz63AmbientWords`.  That count
is bounded by `dwz63_card_tripleSet_le_typeCountLoss_mul` applied to the discharged
`dwz63_tripleEntropyBound`, giving `typeCountLoss (Fin 15) (n+1) · e ^ ((n+1)(H(alpha) + log
hashMult))`.  Splitting that exponential (`Real.exp_add`, then `Real.exp_log` at the positive
`hashMult`) separates the factor `hashMult ^ (n+1)`, and rewriting the remaining
`e ^ ((n+1) H(alpha))` as `proportionalEntropyBase dwz63Alpha ^ t` --- legitimate because
`profileMass dwz63Alpha * t = n + 1` --- lets the committed zero-safe method-of-types bound
`proportionalEntropyBase_pow_le_structuralZeroLoss_mul_card_typeClass` replace it by
`structuralZeroMultinomialLoss dwz63Alpha t · #(joint class)`.  The `calc` multiplies that step
back under the two nonnegative factors and `ring` regroups.  The one-line induction `hexp`
(`e ^ (m x) = (e ^ x) ^ m`) is local so that no cross-image import is needed for two lines of
arithmetic. -/
theorem dwz63_card_plainMarginalWords_le_marked (K : Type u) [CommRing K] {n t : ℕ}
    (ht : 0 < t) (hn : n + 1 = 100000000 * t) :
    (((dwz63PlainMarginalWords K n t).card : ℕ) : ℝ) ≤
      WordType.typeCountLoss (Fin 15) (n + 1) * dwz63HashLossMultiplier ^ (n + 1) *
        WordType.structuralZeroMultinomialLoss dwz63Alpha t *
        (((dwz63MarkedWords n (WordType.proportionalCounts dwz63Alpha t)).card : ℕ) : ℝ) := by
  -- The exponential power law, as a local `have`: the same idiom
  -- `dwz63_exp_entropyX_pow_le_loss_mul_dwz63PlainLegCount` uses, so that no cross-image import
  -- is needed for two lines of arithmetic.
  have hexp : ∀ (m : ℕ) (x : ℝ), Real.exp ((m : ℝ) * x) = Real.exp x ^ m := by
    intro m x
    induction m with
    | zero => simp
    | succ j ih =>
        have hstep : ((j + 1 : ℕ) : ℝ) * x = (j : ℝ) * x + x := by push_cast; ring
        rw [hstep, Real.exp_add, ih, pow_succ]
  have hlen : WordType.profileMass dwz63Alpha * t = n + 1 := by
    rw [profileMass_dwz63Alpha]; omega
  have hmass : 0 < WordType.profileMass dwz63Alpha := profileMass_dwz63Alpha_pos
  have hcard1 : ((dwz63PlainMarginalWords K n t).card : ℝ) =
      ((dwz63TripleSet (n + 1) (WordType.proportionalCounts dwz63AlphaX t)
        (WordType.proportionalCounts dwz63AlphaX t)
        (WordType.proportionalCounts dwz63AlphaZ t)).card : ℝ) := by
    have h1 := (congrArg Finset.card (dwz63_plainMarginalWords_eq_ambientWords K n t)).trans
      (card_dwz63AmbientWords n (WordType.proportionalCounts dwz63AlphaX t)
        (WordType.proportionalCounts dwz63AlphaX t)
        (WordType.proportionalCounts dwz63AlphaZ t))
    exact_mod_cast h1
  have htriple := dwz63_card_tripleSet_le_typeCountLoss_mul dwz63_tripleEntropyBound ht (k := t)
  rw [hlen] at htriple
  have hsplit : Real.exp (((n + 1 : ℕ) : ℝ) *
        (WordType.profileEntropyNats dwz63Alpha + Real.log dwz63HashLossMultiplier)) =
      Real.exp (((n + 1 : ℕ) : ℝ) * WordType.profileEntropyNats dwz63Alpha) *
        dwz63HashLossMultiplier ^ (n + 1) := by
    rw [mul_add, Real.exp_add]
    congr 1
    rw [hexp, Real.exp_log dwz63HashLossMultiplier_pos]
  have hbase : Real.exp (((n + 1 : ℕ) : ℝ) * WordType.profileEntropyNats dwz63Alpha) =
      WordType.proportionalEntropyBase dwz63Alpha ^ t := by
    rw [WordType.proportionalEntropyBase_eq_exp_profileEntropy dwz63Alpha hmass,
      ← hexp, ← hlen]
    congr 1
    push_cast
    ring
  have hjoint : WordType.proportionalEntropyBase dwz63Alpha ^ t ≤
      WordType.structuralZeroMultinomialLoss dwz63Alpha t *
        (((dwz63MarkedWords n (WordType.proportionalCounts dwz63Alpha t)).card : ℕ) : ℝ) := by
    have h := WordType.proportionalEntropyBase_pow_le_structuralZeroLoss_mul_card_typeClass
      dwz63Alpha t
    rw [hlen] at h
    rw [card_dwz63MarkedWords]
    exact h
  have hTC : (0 : ℝ) ≤ WordType.typeCountLoss (Fin 15) (n + 1) :=
    (WordType.typeCountLoss_pos _ _).le
  have hK : (0 : ℝ) ≤ dwz63HashLossMultiplier ^ (n + 1) :=
    pow_nonneg dwz63HashLossMultiplier_pos.le _
  rw [hcard1]
  calc ((dwz63TripleSet (n + 1) (WordType.proportionalCounts dwz63AlphaX t)
          (WordType.proportionalCounts dwz63AlphaX t)
          (WordType.proportionalCounts dwz63AlphaZ t)).card : ℝ)
      ≤ WordType.typeCountLoss (Fin 15) (n + 1) *
          Real.exp (((n + 1 : ℕ) : ℝ) *
            (WordType.profileEntropyNats dwz63Alpha + Real.log dwz63HashLossMultiplier)) :=
        htriple
    _ = WordType.typeCountLoss (Fin 15) (n + 1) *
          (WordType.proportionalEntropyBase dwz63Alpha ^ t *
            dwz63HashLossMultiplier ^ (n + 1)) := by
        rw [hsplit, hbase]
    _ ≤ WordType.typeCountLoss (Fin 15) (n + 1) *
          ((WordType.structuralZeroMultinomialLoss dwz63Alpha t *
            (((dwz63MarkedWords n (WordType.proportionalCounts dwz63Alpha t)).card : ℕ) : ℝ)) *
              dwz63HashLossMultiplier ^ (n + 1)) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hjoint hK) hTC
    _ = WordType.typeCountLoss (Fin 15) (n + 1) * dwz63HashLossMultiplier ^ (n + 1) *
          WordType.structuralZeroMultinomialLoss dwz63Alpha t *
          (((dwz63MarkedWords n (WordType.proportionalCounts dwz63Alpha t)).card : ℕ) : ℝ) := by
        ring

/-- **The joint class sits inside the marginal-typical family.**

`hmarked` for the joint class, obtained from the bridge's own containment rather than from the
assembly lane's `dwz63_marked_subset_marginal`, so that this module needs no further import. -/
theorem dwz63_markedWords_subset_plainMarginalWords (K : Type u) [CommRing K] (n t : ℕ) :
    dwz63MarkedWords n (WordType.proportionalCounts dwz63Alpha t) ⊆
      dwz63PlainMarginalWords K n t := by
  rw [dwz63_plainMarginalWords_eq_ambientWords]
  exact dwz63MarkedWords_subset_ambientWords_proportional n t

end AlgebraicComplexity.Examples
