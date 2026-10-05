/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoMarginalAmbientFiber

/-!
# The leg fiber over the marginal-typical ambient: proved

Layer 4 (`AlgebraicComplexity/Examples/`).  `Examples/DuanWuZhouLevelTwoMarginalAmbientFiber.lean`
stated the question; this module answers it.  For the ambient family
`dwz63TargetTypicalWords K n t`, the leg-`c` fiber of any legal target is **exactly**
`N_triple / N_c`, division-free:

`#legFiber * dwz63LegTypicalCount c n t = dwz63JointTypicalCount K n t`.

## The route

The hashing half is entirely committed: `card_legFiber_legalTargets_eq_card_sourceWordLegFiber`
identifies the fiber of legal targets with `PartitionHashEncoding.sourceWordLegFiber`, the source
words carrying one prescribed leg-`c` block word.  So the new step I expected --- reading
`legFiber` membership back to the leg-word condition --- was already in the repository, and only
the counting is new.

The counting is the six-fold decoupling: fixing the leg-`c` label word fixes each orientation's
`c`-digit, and the completions decouple across orientations because `dwz63TargetTupleEquiv` makes
the six target letters free coordinates.  Orientation `o`'s completion set is
`WordType.typedWordMapFiber (fun s ↦ s c) (proportionalCounts dwz63AlphaAddress t)` at the `o`-th
digit word, counted exactly by `WordType.card_targetType_mul_card_typedWordMapFiber` --- the
mapped type being `proportionalCounts (dwz63AlphaMarginal c) t` by the committed
`mappedType_legRead_proportionalCounts`.  Multiplying the six gives the claim, by
`dwz63JointTypicalCount_eq` and `dwz63LegTypicalCount_eq`.

**No refinement of the marked family is used.**  The decoupling comes from the *ambient* being
marginal typical; the marked family enters only through `marked ⊆ dwz63TargetTypicalWords`.

## The `Z` leg is not bounded by the `X` sharp degree

`dwz63LegTypicalCount` is genuinely leg-dependent: the `X` and `Y` legs carry `alpha_X` and the `Z`
leg carries `alpha_Z`, and `H(alpha_Z) < H(alpha_X)` (`exp` of them being `2.9435…` and
`2.9718…`).  So `N_Z < N_X` and the `Z` fiber `N_triple / N_Z` is *larger* than
`dwz63TargetSharpDegree`, by the same factor by which the two marginal rates differ.  Hence
`dwz63MarginalAmbientFiberBound_XY` is stated for the `X` and `Y` legs only; the general
`card_legFiber_le_dwz63LegSharpDegree` carries each leg's own count.  This is not a defect of the
construction --- section 6.3 hashes and isolates only the `X` and `Y` legs, and
`exists_seed_dwz63JointRetained` consumes only `hsharp .X` and `hsharp .Y` --- but it does mean
that a shared `degree` quantified over all three legs cannot be the sharp one.

Primary source: Ran Duan, Hongxun Wu and Renfei Zhou, *Faster Matrix Multiplication via Asymmetric
Hashing*, arXiv:2210.10173, section 6.3.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor

open scoped BigOperators

universe u v

/-! ## The leg-typical count, per leg -/

/-- **`N_c` at scale `t`**: the leg-`c` label words all six of whose digit sub-words carry the
repeated marginal that leg reads.  At `c = .X` and `c = .Y` this is `dwz63XTypicalCount`. -/
noncomputable def dwz63LegTypicalCount (c : Leg) (n t : ℕ) : ℕ :=
  (dwz63LegTypedWords n (WordType.proportionalCounts (dwz63AlphaMarginal c) t)).card

@[simp] theorem dwz63LegTypicalCount_X (n t : ℕ) :
    dwz63LegTypicalCount .X n t = dwz63XTypicalCount n t := rfl

@[simp] theorem dwz63LegTypicalCount_Y (n t : ℕ) :
    dwz63LegTypicalCount .Y n t = dwz63XTypicalCount n t := rfl

theorem dwz63LegTypicalCount_eq (c : Leg) (n t : ℕ) :
    dwz63LegTypicalCount c n t =
      (WordType.typeClass (n + 1)
        (WordType.proportionalCounts (dwz63AlphaMarginal c) t)).card ^ 6 :=
  card_dwz63LegTypedWords n _

/-! ## The word-level fiber -/

set_option maxRecDepth 8000 in
set_option maxHeartbeats 1000000 in
/-- **The marginal-typical words carrying one prescribed leg-`c` label word.** -/
noncomputable def dwz63LegFiberWords (K : Type u) [CommRing K] (n t : ℕ) (c : Leg)
    (x : Fin (n + 1) → DwzSymSixBlock .X) :
    Finset (PositiveWord ((dwz63SymSixPartition K).support) n) := by
  classical
  exact (dwz63TargetTypicalWords K n t).filter fun q ↦ dwz63LegWord K n c q = x

set_option maxRecDepth 8000 in
set_option maxHeartbeats 1000000 in
@[simp] theorem mem_dwz63LegFiberWords {K : Type u} [CommRing K] {n t : ℕ} {c : Leg}
    {x : Fin (n + 1) → DwzSymSixBlock .X}
    {q : PositiveWord ((dwz63SymSixPartition K).support) n} :
    q ∈ dwz63LegFiberWords K n t c x ↔
      q ∈ dwz63TargetTypicalWords K n t ∧ dwz63LegWord K n c q = x := by
  classical
  simp [dwz63LegFiberWords]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 1000000 in
/-- **The fiber is exactly `N_triple / N_c`, division-free.**

The six orientations decouple, and each contributes one typed coordinatewise word fiber over the
coarse fifteen-cell alphabet. -/
theorem card_dwz63LegFiberWords_mul (K : Type u) [CommRing K] (n t : ℕ) (c : Leg)
    (x : Fin (n + 1) → DwzSymSixBlock .X)
    (hx : ∀ o : Fin 6, WordType.multiplicity (fun j ↦ dwz63SymSixDigit o (x j)) =
      WordType.proportionalCounts (dwz63AlphaMarginal c) t) :
    (dwz63LegFiberWords K n t c x).card * dwz63LegTypicalCount c n t =
      dwz63JointTypicalCount K n t := by
  classical
  have hmemx : ∀ o : Fin 6, (fun j ↦ dwz63SymSixDigit o (x j)) ∈
      WordType.typeClass (n + 1)
        (WordType.mappedType (fun s : CWSquareAddress ↦ s c)
          (WordType.proportionalCounts dwz63AlphaAddress t)) := by
    intro o
    rw [WordType.mem_typeClass, mappedType_legRead_proportionalCounts]
    exact hx o
  have hsupp : ∀ f : Fin 6 → Fin (n + 1) → CWSquareAddress,
      f ∈ Fintype.piFinset (fun o : Fin 6 ↦
        WordType.typedWordMapFiber (fun s : CWSquareAddress ↦ s c)
          (WordType.proportionalCounts dwz63AlphaAddress t)
          (fun j ↦ dwz63SymSixDigit o (x j))) →
      ∀ (j : Fin (n + 1)) (o : Fin 6), f o j ∈ cwSquareSupport := by
    intro f hf j o
    refine mem_cwSquareSupport_of_proportionalCounts_ne_zero (t := t) ?_
    have hm := (WordType.mem_typedWordMapFiber.mp (Fintype.mem_piFinset.mp hf o)).1
    have hne := WordType.multiplicity_apply_ne_zero (f o) j
    rw [hm] at hne
    exact hne
  have hbij : (dwz63LegFiberWords K n t c x).card =
      (Fintype.piFinset fun o : Fin 6 ↦
        WordType.typedWordMapFiber (fun s : CWSquareAddress ↦ s c)
          (WordType.proportionalCounts dwz63AlphaAddress t)
          (fun j ↦ dwz63SymSixDigit o (x j))).card := by
    refine Finset.card_bij'
      (fun q _ ↦ fun o ↦ dwz63TargetWord K n o q)
      (fun f hf ↦ dwz63AssembleTargetWord K n f (hsupp f hf))
      ?_ ?_ ?_ ?_
    · intro q hq
      obtain ⟨htyp, hleg⟩ := mem_dwz63LegFiberWords.mp hq
      refine Fintype.mem_piFinset.mpr fun o ↦ WordType.mem_typedWordMapFiber.mpr ⟨?_, ?_⟩
      · exact mem_dwz63TargetTypicalWords.mp htyp o
      · rw [← dwz63SymSixDigit_dwz63LegWord, hleg]
    · intro f hf
      refine mem_dwz63LegFiberWords.mpr ⟨mem_dwz63TargetTypicalWords.mpr fun o ↦ ?_, ?_⟩
      · rw [dwz63TargetWord_dwz63AssembleTargetWord]
        exact (WordType.mem_typedWordMapFiber.mp (Fintype.mem_piFinset.mp hf o)).1
      · funext j
        refine dwz63SymSixBlock_ext fun o ↦ ?_
        have h1 := congrFun (dwz63SymSixDigit_dwz63LegWord K n c o
          (dwz63AssembleTargetWord K n f (hsupp f hf))) j
        have h2 := congrFun (WordType.mem_typedWordMapFiber.mp
          (Fintype.mem_piFinset.mp hf o)).2 j
        rw [h1, Function.comp_apply, dwz63TargetWord_dwz63AssembleTargetWord]
        exact h2
    · intro q _
      exact dwz63AssembleTargetWord_dwz63TargetWord K n q _
    · intro f _
      funext o
      exact dwz63TargetWord_dwz63AssembleTargetWord K n f _ o
  have hper : ∀ o : Fin 6,
      (WordType.typedWordMapFiber (fun s : CWSquareAddress ↦ s c)
        (WordType.proportionalCounts dwz63AlphaAddress t)
        (fun j ↦ dwz63SymSixDigit o (x j))).card *
        (WordType.typeClass (n + 1)
          (WordType.proportionalCounts (dwz63AlphaMarginal c) t)).card =
      (WordType.typeClass (n + 1) (WordType.proportionalCounts dwz63AlphaAddress t)).card := by
    intro o
    have h := WordType.card_targetType_mul_card_typedWordMapFiber
      (fun s : CWSquareAddress ↦ s c) (WordType.proportionalCounts dwz63AlphaAddress t)
      (fun j ↦ dwz63SymSixDigit o (x j)) (hmemx o)
    rw [mappedType_legRead_proportionalCounts] at h
    rw [mul_comm]
    exact h
  rw [hbij, Fintype.card_piFinset, dwz63LegTypicalCount_eq, dwz63JointTypicalCount_eq]
  have hm6 : (∏ _o : Fin 6,
      (WordType.typeClass (n + 1)
        (WordType.proportionalCounts (dwz63AlphaMarginal c) t)).card)
      = (WordType.typeClass (n + 1)
          (WordType.proportionalCounts (dwz63AlphaMarginal c) t)).card ^ 6 := by
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  calc (∏ o : Fin 6, (WordType.typedWordMapFiber (fun s : CWSquareAddress ↦ s c)
          (WordType.proportionalCounts dwz63AlphaAddress t)
          (fun j ↦ dwz63SymSixDigit o (x j))).card) *
        (WordType.typeClass (n + 1)
          (WordType.proportionalCounts (dwz63AlphaMarginal c) t)).card ^ 6
      = (∏ o : Fin 6, (WordType.typedWordMapFiber (fun s : CWSquareAddress ↦ s c)
          (WordType.proportionalCounts dwz63AlphaAddress t)
          (fun j ↦ dwz63SymSixDigit o (x j))).card) *
        (∏ _o : Fin 6, (WordType.typeClass (n + 1)
          (WordType.proportionalCounts (dwz63AlphaMarginal c) t)).card) := by rw [hm6]
    _ = ∏ o : Fin 6, ((WordType.typedWordMapFiber (fun s : CWSquareAddress ↦ s c)
          (WordType.proportionalCounts dwz63AlphaAddress t)
          (fun j ↦ dwz63SymSixDigit o (x j))).card *
        (WordType.typeClass (n + 1)
          (WordType.proportionalCounts (dwz63AlphaMarginal c) t)).card) :=
        (Finset.prod_mul_distrib).symm
    _ = ∏ _o : Fin 6, (WordType.typeClass (n + 1)
          (WordType.proportionalCounts dwz63AlphaAddress t)).card :=
        Finset.prod_congr rfl fun o _ ↦ hper o
    _ = (WordType.typeClass (n + 1)
          (WordType.proportionalCounts dwz63AlphaAddress t)).card ^ 6 := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-! ## Positivity of the per-leg count -/

/-- At the forced word length the repeated leg marginal is a legal type. -/
theorem proportionalCounts_dwz63AlphaMarginal_mem_types (c : Leg) {n t : ℕ}
    (hn : n + 1 = 100000000 * t) :
    WordType.proportionalCounts (dwz63AlphaMarginal c) t ∈ WordType.types (Fin 5) (n + 1) := by
  rw [WordType.mem_types, hn]
  show ∑ i, dwz63AlphaMarginal c i * t = 100000000 * t
  rw [← Finset.sum_mul,
    show (∑ i, dwz63AlphaMarginal c i) = WordType.profileMass (dwz63AlphaMarginal c) from rfl,
    profileMass_dwz63AlphaMarginal]

/-- **`N_c` is positive** at the forced word length, for every leg. -/
theorem dwz63LegTypicalCount_pos (c : Leg) {n t : ℕ} (hn : n + 1 = 100000000 * t) :
    0 < dwz63LegTypicalCount c n t := by
  rw [dwz63LegTypicalCount_eq]
  refine pow_pos ?_ 6
  rw [Finset.card_pos]
  exact WordType.typeClass_nonempty _ (proportionalCounts_dwz63AlphaMarginal_mem_types c hn)

/-! ## The hashing-level fiber -/

set_option maxRecDepth 8000 in
set_option maxHeartbeats 1000000 in
/-- **The leg fiber of a legal target over the marginal-typical ambient is exactly
`N_triple / N_c`.**  The hashing half is the committed
`card_legFiber_legalTargets_eq_card_sourceWordLegFiber`; the counting half is
`card_dwz63LegFiberWords_mul`. -/
theorem card_legFiber_dwz63TargetTypicalWords_mul (K : Type u) [CommRing K] (R : Type v) [Field R]
    {p : ℕ} [CharP R p] (hp : 15625 ≤ p) (n t : ℕ) (c : Leg)
    {triple : ProgressionHash.LegalTriple R (Fin (n + 1))
      (dwz63SymSixHashEncoding K R hp).target}
    (htriple : triple ∈ (dwz63SymSixHashEncoding K R hp).legalTargets n
      (dwz63TargetTypicalWords K n t)) :
    (ProgressionHash.LegalTriple.legFiber
      ((dwz63SymSixHashEncoding K R hp).legalTargets n (dwz63TargetTypicalWords K n t))
      triple c).card * dwz63LegTypicalCount c n t = dwz63JointTypicalCount K n t := by
  classical
  have hq0mem : (dwz63SymSixHashEncoding K R hp).sourceWordOfLegalTriple n triple ∈
      dwz63TargetTypicalWords K n t :=
    (dwz63SymSixHashEncoding K R hp).sourceWordOfLegalTriple_mem_of_mem n _ htriple
  rw [(dwz63SymSixHashEncoding K R hp).card_legFiber_legalTargets_eq_card_sourceWordLegFiber
    n _ htriple c]
  have hfilter :
      PartitionHashEncoding.sourceWordLegFiber n (dwz63TargetTypicalWords K n t) c
          ((dwz63SymSixHashEncoding K R hp).modeledAddress n triple c) =
        dwz63LegFiberWords K n t c
          (dwz63LegWord K n c
            ((dwz63SymSixHashEncoding K R hp).sourceWordOfLegalTriple n triple)) := by
    ext q
    rw [PartitionHashEncoding.sourceWordLegFiber, Finset.mem_filter, mem_dwz63LegFiberWords]
    refine and_congr_right fun _ ↦ ?_
    rw [← (positiveWordEquiv (DwzSymSixBlock c) n).apply_eq_iff_eq]
    show positiveWordEquiv (DwzSymSixBlock c) n
        (PartitionHashEncoding.supportWordAddress n q c) =
      positiveWordEquiv (DwzSymSixBlock c) n
        (PartitionHashEncoding.supportWordAddress n
          ((dwz63SymSixHashEncoding K R hp).sourceWordOfLegalTriple n triple) c) ↔ _
    rw [PartitionHashEncoding.positiveWordEquiv_supportWordAddress,
      PartitionHashEncoding.positiveWordEquiv_supportWordAddress]
    exact Iff.rfl
  rw [hfilter]
  exact card_dwz63LegFiberWords_mul K n t c _
    fun o ↦ multiplicity_dwz63SymSixDigit_dwz63LegWord K n t c o hq0mem

set_option maxRecDepth 8000 in
set_option maxHeartbeats 1000000 in
/-- Legal targets are monotone in the source family. -/
theorem legalTargets_subset_of_subset (K : Type u) [CommRing K] (R : Type v) [Field R]
    {p : ℕ} [CharP R p] (hp : 15625 ≤ p) (n : ℕ)
    {marked ambient : Finset (PositiveWord ((dwz63SymSixPartition K).support) n)}
    (hsub : marked ⊆ ambient) :
    (dwz63SymSixHashEncoding K R hp).legalTargets n marked ⊆
      (dwz63SymSixHashEncoding K R hp).legalTargets n ambient := by
  classical
  unfold PartitionHashEncoding.legalTargets
  exact Finset.image_subset_image hsub

set_option maxRecDepth 8000 in
set_option maxHeartbeats 1000000 in
/-- **The `hsharp` bound over the marginal-typical ambient, at each leg's own sharp degree.**

The marked family enters only through `marked ⊆ dwz63TargetTypicalWords`; no refinement to a
single joint type is used. -/
theorem card_legFiber_le_dwz63LegSharpDegree (K : Type u) [CommRing K] (R : Type v) [Field R]
    {p : ℕ} [CharP R p] (hp : 15625 ≤ p) {n t : ℕ} (hn : n + 1 = 100000000 * t) (c : Leg)
    {marked : Finset (PositiveWord ((dwz63SymSixPartition K).support) n)}
    (hmarked : marked ⊆ dwz63TargetTypicalWords K n t)
    {triple : ProgressionHash.LegalTriple R (Fin (n + 1))
      (dwz63SymSixHashEncoding K R hp).target}
    (htriple : triple ∈ (dwz63SymSixHashEncoding K R hp).legalTargets n marked) :
    (ProgressionHash.LegalTriple.legFiber
      ((dwz63SymSixHashEncoding K R hp).legalTargets n (dwz63TargetTypicalWords K n t))
      triple c).card ≤
      dwz63SharpDegree (dwz63JointTypicalCount K n t) (dwz63LegTypicalCount c n t) := by
  have hamb : triple ∈ (dwz63SymSixHashEncoding K R hp).legalTargets n
      (dwz63TargetTypicalWords K n t) :=
    legalTargets_subset_of_subset K R hp n hmarked htriple
  have hcount := card_legFiber_dwz63TargetTypicalWords_mul K R hp n t c hamb
  have hpos : 0 < dwz63LegTypicalCount c n t := dwz63LegTypicalCount_pos c hn
  have hdiv : dwz63JointTypicalCount K n t / dwz63LegTypicalCount c n t =
      (ProgressionHash.LegalTriple.legFiber
        ((dwz63SymSixHashEncoding K R hp).legalTargets n (dwz63TargetTypicalWords K n t))
        triple c).card :=
    Nat.div_eq_of_eq_mul_left hpos hcount.symm
  unfold dwz63SharpDegree
  rw [hdiv]
  exact Nat.le_succ _

set_option maxRecDepth 8000 in
set_option maxHeartbeats 1000000 in
/-- **`hsharp` at `dwz63TargetSharpDegree`, for the two hashed legs.**

`exists_seed_dwz63JointRetained` consumes only `hsharp .X` and `hsharp .Y`, and those are the two
legs whose marginal is `alpha_X`.  The `Z` leg carries `alpha_Z`, whose type class is strictly
smaller, so its fiber is strictly larger than this degree --- see the module docstring. -/
theorem dwz63MarginalAmbientFiberBound_XY (K : Type u) [CommRing K] (R : Type v) [Field R]
    {p : ℕ} [CharP R p] (hp : 15625 ≤ p) {n t : ℕ} (hn : n + 1 = 100000000 * t)
    {marked : Finset (PositiveWord ((dwz63SymSixPartition K).support) n)}
    (hmarked : marked ⊆ dwz63TargetTypicalWords K n t) (c : Leg) (hc : c = .X ∨ c = .Y) :
    ∀ triple ∈ (dwz63SymSixHashEncoding K R hp).legalTargets n marked,
      (ProgressionHash.LegalTriple.legFiber
        ((dwz63SymSixHashEncoding K R hp).legalTargets n (dwz63TargetTypicalWords K n t))
        triple c).card ≤ dwz63TargetSharpDegree K n t := by
  intro triple htriple
  have h := card_legFiber_le_dwz63LegSharpDegree K R hp hn c hmarked htriple
  rcases hc with rfl | rfl
  · rwa [dwz63LegTypicalCount_X] at h
  · rwa [dwz63LegTypicalCount_Y] at h

end AlgebraicComplexity.Examples
