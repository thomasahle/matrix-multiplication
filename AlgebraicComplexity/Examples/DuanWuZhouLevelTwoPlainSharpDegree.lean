/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoPlainFiberCount

set_option autoImplicit false

/-!
# `hsharp` at the plain partition

Layer 4 (`AlgebraicComplexity/Examples/`).  `exists_seed_dwz63PlainJointRetained` takes its two
leg-fibre hypotheses `hXfiber` and `hYfiber` at a client-supplied degree `d`.  This module supplies
them at the sharp degree `N_α' / N_X`, discharging the last counting obligation of the plain
hashing step.

## The chain

`PartitionHashEncoding.card_legFiber_legalTargets_eq_card_sourceWordLegFiber` converts the fibre of
legal targets into the source-word fibre, and
`card_sourceWordLegFiber_le_sharpDegree` of `Examples/DuanWuZhouLevelTwoPlainFiberCount.lean`
bounds that by `dwz63SharpDegree` of the ambient count and `N_c`.  The only step in between is
that a marked target's modelled leg word is one of the leg words the marginal cut keeps, which is
the count lane's `mem_dwz63PlainMarginalWords_iff_keep` applied to the recovered source word.

The marked family enters only through `markedWords ⊆ dwz63PlainMarginalWords K n t`, the same
`hmarked` the retention theorem already asks for; the fibre itself is measured against the
marginal-typical ambient throughout.

## Only two legs, and why that is enough

`dwz63PlainLegCount` is leg-dependent --- the `X` and `Y` legs carry `α_X`, the `Z` leg carries
`α_Z`, and `H(α_Z) < H(α_X)` --- so the `Z` fibre is strictly larger than `dwz63PlainSharpDegree`
and no single degree bounds all three.  This costs nothing: section 6.3 hashes and isolates only
the `X` and `Y` legs, and `exists_seed_dwz63PlainJointRetained` asks for exactly those two.  Since
`dwz63AlphaMarginal .Y = dwz63AlphaMarginal .X` definitionally, one degree serves both.

Primary source: Ran Duan, Hongxun Wu and Renfei Zhou, *Faster Matrix Multiplication via Asymmetric
Hashing*, arXiv:2210.10173, section 6.3.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor

universe u v

/-- **The plain sharp degree**, `⌊N_α' / N_X⌋ + 1` at the marginal-typical ambient. -/
noncomputable def dwz63PlainSharpDegree (K : Type u) [CommRing K] (n t : ℕ) : ℕ :=
  dwz63SharpDegree (dwz63PlainMarginalWords K n t).card (dwz63PlainLegCount .X n t)

section Fiber

variable {R : Type v} [Field R]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 1000000 in
/-- **The leg-fibre bound, at each leg's own sharp degree.** -/
theorem dwz63_plain_legFiber_le_sharpDegree (K : Type u) [CommRing K]
    (hinj : Function.Injective (cwSquareFieldValue (R := R))) {n t : ℕ}
    (hn : n + 1 = 100000000 * t)
    {markedWords : Finset (PositiveWord ((cwSquarePartitionedTensor K dwz63Q).support) n)}
    (hmarked : markedWords ⊆ dwz63PlainMarginalWords K n t) (c : Leg) :
    ∀ triple ∈ (cwSquarePartitionHashEncoding hinj).legalTargets n markedWords,
      (ProgressionHash.LegalTriple.legFiber
        ((cwSquarePartitionHashEncoding hinj).legalTargets n (dwz63PlainMarginalWords K n t))
        triple c).card ≤
        dwz63SharpDegree (dwz63PlainMarginalWords K n t).card (dwz63PlainLegCount c n t) := by
  classical
  intro triple htriple
  have hamb : triple ∈ (cwSquarePartitionHashEncoding hinj).legalTargets n
      (dwz63PlainMarginalWords K n t) := by
    unfold PartitionHashEncoding.legalTargets
    exact Finset.image_subset_image hmarked htriple
  have hq : (cwSquarePartitionHashEncoding hinj).sourceWordOfLegalTriple n triple ∈
      dwz63PlainMarginalWords K n t :=
    (cwSquarePartitionHashEncoding hinj).sourceWordOfLegalTriple_mem_of_mem n _ hamb
  have hx : (cwSquarePartitionHashEncoding hinj).modeledAddress n triple c ∈
      dwz63PlainLegTargets c n t :=
    mem_dwz63PlainLegTargets.mpr ((mem_dwz63PlainMarginalWords_iff_keep K n t _).mp hq c)
  rw [(cwSquarePartitionHashEncoding hinj).card_legFiber_legalTargets_eq_card_sourceWordLegFiber
    n _ hamb c]
  exact card_sourceWordLegFiber_le_sharpDegree K c hn hx

set_option maxRecDepth 8000 in
set_option maxHeartbeats 1000000 in
/-- **`hXfiber` at the sharp degree.** -/
theorem dwz63_plain_hXfiber (K : Type u) [CommRing K]
    (hinj : Function.Injective (cwSquareFieldValue (R := R))) {n t : ℕ}
    (hn : n + 1 = 100000000 * t)
    {markedWords : Finset (PositiveWord ((cwSquarePartitionedTensor K dwz63Q).support) n)}
    (hmarked : markedWords ⊆ dwz63PlainMarginalWords K n t) :
    ∀ triple ∈ (cwSquarePartitionHashEncoding hinj).legalTargets n markedWords,
      (ProgressionHash.LegalTriple.legFiber
        ((cwSquarePartitionHashEncoding hinj).legalTargets n (dwz63PlainMarginalWords K n t))
        triple .X).card ≤ dwz63PlainSharpDegree K n t :=
  dwz63_plain_legFiber_le_sharpDegree K hinj hn hmarked .X

set_option maxRecDepth 8000 in
set_option maxHeartbeats 1000000 in
/-- **`hYfiber` at the same degree.**  `dwz63AlphaMarginal .Y = dwz63AlphaMarginal .X`
definitionally, so `N_Y = N_X` and one degree serves both hashed legs. -/
theorem dwz63_plain_hYfiber (K : Type u) [CommRing K]
    (hinj : Function.Injective (cwSquareFieldValue (R := R))) {n t : ℕ}
    (hn : n + 1 = 100000000 * t)
    {markedWords : Finset (PositiveWord ((cwSquarePartitionedTensor K dwz63Q).support) n)}
    (hmarked : markedWords ⊆ dwz63PlainMarginalWords K n t) :
    ∀ triple ∈ (cwSquarePartitionHashEncoding hinj).legalTargets n markedWords,
      (ProgressionHash.LegalTriple.legFiber
        ((cwSquarePartitionHashEncoding hinj).legalTargets n (dwz63PlainMarginalWords K n t))
        triple .Y).card ≤ dwz63PlainSharpDegree K n t :=
  dwz63_plain_legFiber_le_sharpDegree K hinj hn hmarked .Y

set_option maxRecDepth 8000 in
set_option maxHeartbeats 1000000 in
/-- **The good seed, at the sharp degree.**  The two fibre hypotheses of
`exists_seed_dwz63PlainJointRetained` are now discharged; the only remaining side condition is the
modulus bound `8 d ≤ #R`, which is the client's choice of field. -/
theorem exists_seed_dwz63PlainJointRetained_at_sharpDegree [Fintype R] [NeZero (2 : R)]
    (K : Type u) [CommRing K]
    (hinj : Function.Injective (cwSquareFieldValue (R := R))) {n t : ℕ}
    (hn : n + 1 = 100000000 * t)
    (markedWords : Finset (PositiveWord ((cwSquarePartitionedTensor K dwz63Q).support) n))
    (hmarked : markedWords ⊆ dwz63PlainMarginalWords K n t)
    (B : Finset R) (hB : ThreeAPFree (B : Set R))
    (hmodulus : 8 * dwz63PlainSharpDegree K n t ≤ Fintype.card R) :
    ∃ seed : ProgressionHash.Seed R (Fin (n + 1)),
      3 * markedWords.card * B.card ≤
        4 * (Fintype.card R * Fintype.card R) *
          (dwz63PlainJointRetainedSupport K hinj n t markedWords B seed).card :=
  exists_seed_dwz63PlainJointRetained K hinj n t markedWords hmarked B hB
    (dwz63PlainSharpDegree K n t)
    (dwz63_plain_hXfiber K hinj hn hmarked)
    (dwz63_plain_hYfiber K hinj hn hmarked) hmodulus

end Fiber

end AlgebraicComplexity.Examples
