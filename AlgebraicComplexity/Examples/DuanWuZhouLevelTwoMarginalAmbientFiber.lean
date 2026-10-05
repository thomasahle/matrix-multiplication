/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoHashingBranchRate

/-!
# The leg fiber over the *marginal-typical* ambient: stated, not proved

Layer 4 (`AlgebraicComplexity/Examples/`).  `Examples/DuanWuZhouLevelTwoSharpFiberBound.lean`
proves the leg-fiber bound when the fiber is taken inside the legal targets of the **marked**
family, and records two obstructions to using it for the `hsharp` of
`Examples/DuanWuZhouLevelTwoSharpDegree.lean`:

* that `hsharp` takes the fiber over `legalTargets n Finset.univ`, the *whole* ambient family, and
  the ambient fiber is not bounded by the sharp degree --- its rate is
  `Σ_x (α_X x / 10^8) · log (5 - x) = 1.2785728` nats per oriented letter against the sharp
  `H(α) - H(α_X) = 0.9240977`, an exponential gap of `1.4254322 ^ (6 N)`;
* that the committed injection's `hwords` asks for one joint block-label type, while
  `Dwz63TargetTypical` fixes only six coarse marginals.

This module states the intermediate question that decides the `X` side: the fiber taken over the
**marginal-typical** ambient `dwz63TargetTypicalWords`, which sits strictly between the marked
family and `Finset.univ`.  Nothing here is proved; the two `Prop`s are named so that the count lane
and this lane agree on their shape before either is claimed.

## Why this is the deciding number

Fixing a target's leg-`c` block word fixes, at each position, the `c`-digit of each of the six
orientations.  Over `Finset.univ` the remaining two digits of orientation `o` are free subject only
to the degree-four condition, which leaves `5 - d_o` completions and produces the vacuous rate
above.  Over the marginal-typical ambient they are additionally constrained by the *global* type of
each target sub-word, and the constraint decouples across the six orientations
(`dwz63TargetTupleEquiv`): orientation `o`'s completion ranges over the words of type
`proportionalCounts dwz63AlphaAddress t` whose leg-`c` reading is the prescribed digit word.  That
is a typed coordinatewise word fiber over the *coarse* fifteen-cell alphabet, and
`WordType.card_targetType_mul_card_typedWordMapFiber` counts it exactly, as
`#(typeClass (n+1) (proportionalCounts dwz63AlphaAddress t))
   / #(typeClass (n+1) (proportionalCounts (dwz63AlphaMarginal c) t))`
--- the marginal identity being the committed `mappedType_legRead_proportionalCounts`.  Taking the
product over the six orientations gives `dwz63JointTypicalCount / dwz63XTypicalCount` exactly, by
`dwz63JointTypicalCount_eq` and `dwz63XTypicalCount_eq`.  So the expected answer is **yes, the
fiber over the marginal-typical ambient is still `N_triple / N_X`**, and
`Dwz63MarginalAmbientFiberCount` states that in division-free form.

## What it would take to prove

Three steps, of which only the first is new work.

1. **The fiber decomposition.**  Show that `legFiber` membership over
   `legalTargets n (dwz63TargetTypicalWords K n t)` is, after
   `ProgressionHash.LegalTriple.mem_legFiber` and
   `PartitionHashEncoding.modeledAddress_leg_eq_iff`, exactly "the ambient word is target typical
   and its leg-`c` label word equals the marked word's", and that the map sending such a word to
   its six target sub-words is a bijection onto
   `∏ o, typedWordMapFiber (fun s ↦ s c) (proportionalCounts dwz63AlphaAddress t) (o-th digit word)`.
   Both halves of that bijection are already green: forward is `dwz63TargetWord` plus
   `dwz63SymSixDigit_dwz63LegWord`, and the inverse is `dwz63AssembleTargetWord` with its two
   round-trip identities, exactly as in `card_dwz63TargetTypedWords`.  The genuinely new content is
   only the identification of `legFiber` with the leg-word condition, which is hashing-side
   bookkeeping and carries no counting.
2. **The per-orientation count.**  `WordType.card_targetType_mul_card_typedWordMapFiber` at
   `f := fun s : CWSquareAddress ↦ s c`, `a := proportionalCounts dwz63AlphaAddress t`, whose
   mapped type is `proportionalCounts (dwz63AlphaMarginal c) t` by
   `mappedType_legRead_proportionalCounts`.  Already committed.
3. **The product.**  `Fintype.card_piFinset` and `Finset.prod_const`, as in
   `card_dwz63TargetTypedWords`.  Already committed.

Note that **no refinement of the marked family to a single joint type is needed** for this route:
the decoupling comes from the *ambient* being marginal typical, not from the marked family, so
`marked` may stay `dwz63TargetTypicalWords` (or any subfamily of it).  If the ambient question is
settled in favour of the marginal-typical family, the joint-type refinement of
`Examples/DuanWuZhouLevelTwoSharpFiberBound.lean` becomes unnecessary and the laser-soundness
question it raises does not arise.

## What is *not* settled here

Whether the isolation and crossing arguments downstream may take their ambient to be the
marginal-typical family rather than `Finset.univ`.  That is a soundness question about the
restriction, not a counting question, and it is not addressed by anything in this module.

Primary source: Ran Duan, Hongxun Wu and Renfei Zhou, *Faster Matrix Multiplication via Asymmetric
Hashing*, arXiv:2210.10173, section 6.3.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor

universe u v

/-- **Stated, not proved.**  The leg fiber of a marked target, taken over the *marginal-typical*
ambient, is exactly `N_triple / N_X` --- in division-free form, so that no positivity side
condition is carried. -/
def Dwz63MarginalAmbientFiberCount (K : Type u) [CommRing K] (R : Type v) [Field R]
    {p : ℕ} [CharP R p] (hp : 15625 ≤ p) (n t : ℕ)
    (marked : Finset (PositiveWord ((dwz63SymSixPartition K).support) n)) : Prop :=
  ∀ c : Leg,
    ∀ triple ∈ (dwz63SymSixHashEncoding K R hp).legalTargets n marked,
      (ProgressionHash.LegalTriple.legFiber
        ((dwz63SymSixHashEncoding K R hp).legalTargets n (dwz63TargetTypicalWords K n t))
        triple c).card * dwz63XTypicalCount n t = dwz63JointTypicalCount K n t

/-- **Stated, not proved.**  The rounded consequence: the same fiber is at most the sharp degree
built from this lane's two counts.  This is the shape `hsharp` would consume if the ambient in
`dwz63_retained_card_lower_sharp` were the marginal-typical family rather than `Finset.univ`. -/
def Dwz63MarginalAmbientFiberBound (K : Type u) [CommRing K] (R : Type v) [Field R]
    {p : ℕ} [CharP R p] (hp : 15625 ≤ p) (n t : ℕ)
    (marked : Finset (PositiveWord ((dwz63SymSixPartition K).support) n)) : Prop :=
  ∀ c : Leg,
    ∀ triple ∈ (dwz63SymSixHashEncoding K R hp).legalTargets n marked,
      (ProgressionHash.LegalTriple.legFiber
        ((dwz63SymSixHashEncoding K R hp).legalTargets n (dwz63TargetTypicalWords K n t))
        triple c).card ≤
        dwz63SharpDegree (dwz63JointTypicalCount K n t) (dwz63XTypicalCount n t)

/-- **The exact count implies the rounded bound.**  This is the only arithmetic in the module, and
it is the same divisibility step as in `card_legFiber_le_sharpDegree`: positivity of `N_X` at the
forced word length comes from `dwz63XTypicalCount_pos`. -/
theorem dwz63MarginalAmbientFiberBound_of_count (K : Type u) [CommRing K] (R : Type v) [Field R]
    {p : ℕ} [CharP R p] (hp : 15625 ≤ p) {n t : ℕ} (hn : n + 1 = 100000000 * t)
    {marked : Finset (PositiveWord ((dwz63SymSixPartition K).support) n)}
    (h : Dwz63MarginalAmbientFiberCount K R hp n t marked) :
    Dwz63MarginalAmbientFiberBound K R hp n t marked := by
  intro c triple htriple
  have hx : 0 < dwz63XTypicalCount n t := dwz63XTypicalCount_pos hn
  have hcount := h c triple htriple
  have hdiv : dwz63JointTypicalCount K n t / dwz63XTypicalCount n t =
      (ProgressionHash.LegalTriple.legFiber
        ((dwz63SymSixHashEncoding K R hp).legalTargets n (dwz63TargetTypicalWords K n t))
        triple c).card :=
    Nat.div_eq_of_eq_mul_left hx hcount.symm
  unfold dwz63SharpDegree
  rw [hdiv]
  exact Nat.le_succ _

end AlgebraicComplexity.Examples
