/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoCofinalCompetitorDegree

set_option autoImplicit false
set_option maxRecDepth 8000

/-!
# `hT` is not an extra datum: the cofinal `hVdeg` with no side condition

Layer 4 (`AlgebraicComplexity/Examples/`).
`Examples/DuanWuZhouLevelTwoCofinalCompetitorDegree.lean`'s
`dwz63_cofinal_plainCompetitorBound_le_sharpDegree` carries

`hT : ∀ m, 0 < ((dwz63Split (m + 1)).typicalSet (dwz63ZIndex ∘ comp₀ m)).card`,

the positivity `Examples/DuanWuZhouLevelTwoCompetitorBound.lean`'s `dwz63_competitorBound_le_iff`
needs to turn `V ≤ D` into a product inequality.  This module discharges it outright: it is a
consequence of the component word's own type, and no further datum about the witness family is
required.

## Why it is free

`Combinatorics/CompatibleSplitCount.lean`'s `SplitRequirements.typicalSet_nonempty` is exactly the
statement, for any `SplitRequirements`: if the split profile refines `αType` (`RefinesType`) and
`comp` has multiplicity type `αType`, then `S.typicalSet (S.zIndex ∘ comp)` is nonempty.  Its two
side conditions — that `γ = S.typicalType` has total mass equal to the word length, and that its
first marginal is the multiplicity type of the large `Z`-block — are both immediate from
`RefinesType` (`sum_usefulType`, `mappedType_fst_typicalType`), and
`WordType.conditionalTypeClass_nonempty` supplies the witness.  The paper's own anti-vacuity
remark for the denominator of `lemma:pcomp_g` is therefore already formalised, and at section 6.3
`dwz63Split_refinesType` is the committed `RefinesType` instance.

So the witness family the endpoint supplies — a component word `comp₀ m` of the exact
fifteen-cell
proportional type, which is precisely `hcomp₀`, the hypothesis `hupper` already needs — carries
`hT` with it.  Nothing is assumed that was not already assumed.

Primary source: Ran Duan, Hongxun Wu and Renfei Zhou, *Faster Matrix Multiplication via Asymmetric
Hashing*, arXiv:2210.10173, §6.2 (`global_value.tex`), `lemma:pcomp_g`.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor ProgressionHash CompatibleSplit

universe u

/-! ## The typical set at section 6.3 is nonempty -/

/-- **The section 6.3 typical set is nonempty**, for every component word of the prescribed
fifteen-cell type.  This is the committed `SplitRequirements.typicalSet_nonempty` at
`dwz63Split`, whose `RefinesType` hypothesis is the committed `dwz63Split_refinesType`. -/
theorem dwz63_card_split_typicalSet_pos {N : ℕ} (k : ℕ) (comp : Fin N → Fin 15)
    (hcomp : WordType.multiplicity comp =
      WordType.proportionalCounts dwz63Alpha (200000000 * k)) :
    0 < ((dwz63Split k).typicalSet (dwz63ZIndex ∘ comp)).card := by
  refine Finset.card_pos.mpr ?_
  exact SplitRequirements.typicalSet_nonempty (S := dwz63Split k)
    (dwz63Split_refinesType k) comp hcomp

/-! ## The cofinal `hVdeg`, with no side condition -/

/-- **`hVdeg`, cofinally, at the section 6.3 instance — unconditional in the typical count.**

The same statement as `dwz63_cofinal_plainCompetitorBound_le_sharpDegree`, with `hT` discharged.
The only remaining hypotheses are the two witness families and their types: a component word of
the exact fifteen-cell proportional type at each group index, and an `X`-leg target word kept by
the plain marginal cut. -/
theorem dwz63_cofinal_competitorBound_le_plainSharpDegree (K : Type u) [CommRing K]
    (comp₀ : ∀ m : ℕ, Fin (dwz63PlainCountDepth dwz63AssemblyBlocks m + 1) → Fin 15)
    (hcomp₀ : ∀ m : ℕ, WordType.multiplicity (comp₀ m) =
      WordType.proportionalCounts dwz63Alpha (dwz63AssemblyBlocks * (m + 1)))
    (xword : ∀ m : ℕ, PositiveWord (Fin 5) (dwz63PlainCountDepth dwz63AssemblyBlocks m))
    (hxword : ∀ m : ℕ, xword m ∈ dwz63PlainLegTargets .X
      (dwz63PlainCountDepth dwz63AssemblyBlocks m) (dwz63AssemblyBlocks * (m + 1))) :
    ∃ cutoff : ℕ, ∀ m : ℕ, cutoff ≤ m →
      dwz63CompetitorBound (dwz63Split (m + 1))
          (WordType.proportionalCounts dwz63Alpha (dwz63AssemblyBlocks * (m + 1)))
          (dwz63ZIndex ∘ comp₀ m) (comp₀ m) ≤
        dwz63PlainSharpDegree K (dwz63PlainCountDepth dwz63AssemblyBlocks m)
          (dwz63AssemblyBlocks * (m + 1)) := by
  refine dwz63_cofinal_plainCompetitorBound_le_sharpDegree K comp₀ hcomp₀ xword hxword ?_
  intro m
  refine dwz63_card_split_typicalSet_pos (m + 1) (comp₀ m) ?_
  rw [hcomp₀ m, dwz63AssemblyBlocks_eq]

end AlgebraicComplexity.Examples
