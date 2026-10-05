/-
Copyright (c) 2026 Thomas Dybdahl Ahle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Dybdahl Ahle
-/

import AlgebraicComplexity.Combinatorics.SplitRequirementsLetterPushforward
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoCountingSplit
import AlgebraicComplexity.Examples.DuanWuZhouLevelTwoFinePairSum

set_option autoImplicit false

/-!
# The section 6.3 split record on the pair alphabet, and its bridge to the `k_l` record

Layer 4 (`AlgebraicComplexity/Examples/`).  `Examples/DuanWuZhouLevelTwoCountingSplit.lean`'s
`dwz63Split k` is a `SplitRequirements (Fin 15) (Fin 3) (Fin 5)` over the **left-half** letter
`k_l`; the hole side reads whole **pairs** `(k_l, k_r)`, i.e. it needs a
`SplitRequirements (Fin 15) (PositiveWord CWBlock 1) (Fin 5)` whose `splitCount` is the joined
`alphatilde` table.  This module supplies that record and the comparison of the two competitor
families.

## The comparison is a subset, not a cardinality transport

`Combinatorics/SplitRequirementsLetterPushforward.lean` records why: neither `matchable` nor
`matchableCompatible` mentions the split alphabet in its *element* type, so both families are
Finsets of `Fin n → Fin 15` and the fine one is contained in the coarse one.  The letter map is
`dwz63FineLeftDegree`, which forgets `k_r`; **no injectivity is used**, and neither is
`dwz63AlphaTilde_swap`.

## The one arithmetic input

`dwz63_splitPair_letterPushforward` is the whole content: for each of the fifteen cells and each
of the three left degrees,

`dwz63SplitCount c l * s = Σ_{p : p.1 has degree l} dwz63AlphaTilde c p * (dwz63Alpha c * s)`.

The two tables are **not** equal entry for entry: `dwz63SplitCount`'s rows sum to
`2 · 10 ^ 8 · α(c)` while `dwz63AlphaTilde`'s rows sum to `2 · 10 ^ 8` (`dwz63AlphaTildeMass`),
so
the fine table must be weighted by the cell mass `dwz63Alpha c` — which is exactly where the
assembly lane's `dwz63JoinedAlphaTilde s t = proportionalCounts (dwz63AlphaTilde t)
(dwz63Alpha t · s)` puts it.  `(dwz63SplitPair s).splitCount` is that function on the nose, so a
client's
`hS : S.splitCount = dwz63JoinedAlphaTilde s` — the hypothesis of
`isUseful_of_segmentedAvailableWord` — closes by `rfl`; this module does not import the assembly
module for a definitional identity.

The sum over the nine pairs is taken with the committed `dwz63_sum_finePair_expand`
(`Examples/DuanWuZhouLevelTwoFinePairSum.lean`), which is what keeps the noncomputable
`positiveWordFintype` on `PositiveWord CWBlock 1` out of the proof: there is no `decide` over that
alphabet anywhere here.

## Which paper statements this combines, and what is reusable

This module is **project-specific**: it assembles three separate parts of the paper into the one
record the hole side reads.  `dwz63FineLeftDegree` and `dwz63LeftBlock` implement the left digit of
a split, which is what `split` means at `papers/sources/2210.10173/global_value.tex:35`.
`dwz63SplitPair` bundles that with pair typicalness --- the typicalness definition and the
compatibility probability of `:145-173` --- over the pair alphabet.
`dwz63_splitCount_eq_alpha_mul_leftFibre`
and `dwz63_splitPair_letterPushforward` reconcile the two split tables against the numerical
level-two rows of the section 6.3 example, `:332-375`.  `dwz63_matchableCompatiblePair_subset`,
`dwz63_card_matchableCompatiblePair_le` and `dwz63_hV_pair_of_hV` are instances of the reusable
coarsening of `Combinatorics/SplitRequirementsLetterPushforward.lean`; no declaration here is a
published theorem.

Primary source `[duan2023faster]`: Ran Duan, Hongxun Wu and Renfei Zhou, *Faster Matrix
Multiplication via Asymmetric Hashing*, arXiv:2210.10173, section 6.1 `sec:global-algo` and section
6.3 `sec:level-2-global`, `papers/sources/2210.10173/global_value.tex:35, 145-173, 332-375`.
-/

namespace AlgebraicComplexity.Examples

open AlgebraicComplexity Tensor CompatibleSplit

open scoped BigOperators

/-! ## The letter map and the pair-alphabet record -/

-- ELABORATION RISK: `PositiveWord CWBlock 1` is definitionally `CWBlock × CWBlock` with `.1` the
-- left digit (this is what `cwPairProfile` already relies on), so the match below is on the left
-- digit.  A `Fin 3`-valued match avoids carrying a `< 3` proof, and avoids `cwBlockDegree`, whose
-- `ℕ` value would have to be bundled.
/-- **The left half of a fine letter, as its degree.**  This is the map that forgets `k_r`. -/
def dwz63FineLeftDegree : PositiveWord CWBlock 1 → Fin 3 := fun p ↦
  match p.1 with
  | .zero => 0
  | .middle => 1
  | .last => 2

/-- **The section 6.3 splitting data on the pair alphabet**, at scale `s`.

`zIndex` and `boundary` are the very same fields as `dwz63Split s`; only the split table moves to
the fine letter.  The table is `dwz63JoinedAlphaTilde s` definitionally. -/
def dwz63SplitPair (s : ℕ) :
    CompatibleSplit.SplitRequirements (Fin 15) (PositiveWord CWBlock 1) (Fin 5) where
  zIndex := dwz63ZIndex
  boundary := dwz63Boundary
  splitCount := fun t ↦ WordType.proportionalCounts (dwz63AlphaTilde t) (dwz63Alpha t * s)

/-- The split table is the assembly lane's `dwz63JoinedAlphaTilde s`, on the nose. -/
theorem dwz63SplitPair_splitCount (s : ℕ) :
    (dwz63SplitPair s).splitCount =
      fun t ↦ WordType.proportionalCounts (dwz63AlphaTilde t) (dwz63Alpha t * s) := rfl

theorem dwz63SplitPair_zIndex (s : ℕ) : (dwz63SplitPair s).zIndex = (dwz63Split s).zIndex := rfl

theorem dwz63SplitPair_boundary (s : ℕ) :
    (dwz63SplitPair s).boundary = (dwz63Split s).boundary := rfl

/-! ## The nine pairs, cut down to the three with a prescribed left digit -/

/-- The left digit of the prescribed degree. -/
def dwz63LeftBlock : Fin 3 → CWBlock := ![.zero, .middle, .last]

@[simp] theorem dwz63FineLeftDegree_leftBlock (l : Fin 3) (r : CWBlock) :
    dwz63FineLeftDegree (dwz63LeftBlock l, r) = l := by
  fin_cases l <;> rfl

-- ELABORATION RISK: `rw [dwz63_sum_finePair_expand]` does NOT fire on a goal whose binder ranges
-- over `PositiveWord CWBlock 1` — that binder carries the noncomputable `positiveWordFintype`
-- while the lemma is stated over the product instance, and the rewrite's motive fails at
-- reducible transparency (the failure mode the `FinePairSum` docstring records).  The committed
-- idiom is term-level `Eq.trans`, where the two sums are checked defeq at default transparency;
-- `dwz63_profileMass_alphaTilde` uses exactly that.
/-- **A left-digit fibre sum over the nine pairs keeps three terms.**

Stated for an arbitrary profile, so that no numeral is touched here: the three cases are closed by
`dwz63FineLeftDegree`'s own definition. -/
theorem dwz63_finePair_leftFibre_sum (l : Fin 3) (g : PositiveWord CWBlock 1 → ℕ) :
    (∑ p : CWBlock × CWBlock, if dwz63FineLeftDegree p = l then g p else 0) =
      g (dwz63LeftBlock l, .zero) + g (dwz63LeftBlock l, .middle)
        + g (dwz63LeftBlock l, .last) := by
  refine Eq.trans (dwz63_sum_finePair_expand (M := ℕ)
    (fun p ↦ if dwz63FineLeftDegree p = l then g p else 0)) ?_
  fin_cases l <;> simp [dwz63FineLeftDegree, dwz63LeftBlock] <;> rfl

/-! ## The 45-entry table identity -/

set_option maxRecDepth 8000 in
/-- **The `k_l` table is the fine table's left-digit fibre sum, weighted by the cell mass.**

Fifteen cells times three left degrees, in pure integer arithmetic: no `s`, no `ring`, and no
`decide` over the fine alphabet. -/
theorem dwz63_splitCount_eq_alpha_mul_leftFibre (c : Fin 15) (l : Fin 3) :
    dwz63SplitCount c l =
      (dwz63AlphaTilde c (dwz63LeftBlock l, .zero)
        + dwz63AlphaTilde c (dwz63LeftBlock l, .middle)
        + dwz63AlphaTilde c (dwz63LeftBlock l, .last)) * dwz63Alpha c := by
  fin_cases c <;> fin_cases l <;>
    norm_num [dwz63SplitCount, dwz63AlphaTilde, dwz63Alpha, dwz63LeftBlock,
      cwPairProfile, cwProfile, cwZeroProfile]

/-- **The coarse table is the fine table summed over the fibres of `dwz63FineLeftDegree`**, which
is the single hypothesis of `SplitRequirements.card_matchableCompatible_le_of_letterPushforward`. -/
theorem dwz63_splitPair_letterPushforward (s : ℕ) (c : Fin 15) (l : Fin 3) :
    WordType.mappedType dwz63FineLeftDegree
        (fun p ↦ (dwz63SplitPair s).splitCount c p) l = (dwz63Split s).splitCount c l := by
  rw [WordType.mappedType_eq_sum_ite]
  refine Eq.trans (dwz63_finePair_leftFibre_sum l
    (fun p ↦ dwz63AlphaTilde c p * (dwz63Alpha c * s))) ?_
  show dwz63AlphaTilde c (dwz63LeftBlock l, .zero) * (dwz63Alpha c * s)
      + dwz63AlphaTilde c (dwz63LeftBlock l, .middle) * (dwz63Alpha c * s)
      + dwz63AlphaTilde c (dwz63LeftBlock l, .last) * (dwz63Alpha c * s)
    = dwz63SplitCount c l * s
  rw [dwz63_splitCount_eq_alpha_mul_leftFibre c l]
  ring

/-! ## The competitor comparison -/

/-- **The pair-alphabet competitor family is contained in the `k_l` one.** -/
theorem dwz63_matchableCompatiblePair_subset (s : ℕ) (αType : Fin 15 → ℕ) {N : ℕ}
    (K : Fin N → Fin 5) (w : Fin N → PositiveWord CWBlock 1) :
    (dwz63SplitPair s).matchableCompatible αType K w ⊆
      (dwz63Split s).matchableCompatible αType K (dwz63FineLeftDegree ∘ w) :=
  SplitRequirements.matchableCompatible_subset_of_letterPushforward
    (dwz63SplitPair s) (dwz63Split s) dwz63FineLeftDegree (dwz63SplitPair_zIndex s)
    (dwz63SplitPair_boundary s) (dwz63_splitPair_letterPushforward s) αType K w

/-- **The competitor count**, in the form `hV` wants. -/
theorem dwz63_card_matchableCompatiblePair_le (s : ℕ) (αType : Fin 15 → ℕ) {N : ℕ}
    (K : Fin N → Fin 5) (w : Fin N → PositiveWord CWBlock 1) :
    ((dwz63SplitPair s).matchableCompatible αType K w).card ≤
      ((dwz63Split s).matchableCompatible αType K (dwz63FineLeftDegree ∘ w)).card :=
  Finset.card_le_card (dwz63_matchableCompatiblePair_subset s αType K w)

/-- **`hV` transported to the pair alphabet.**

A bound on the `k_l` competitor family, uniform in the small block, bounds the pair-alphabet
family — which is the `hV` premise of `dwz63_hcompetitorsTyped` at the hole lane's record. -/
theorem dwz63_hV_pair_of_hV (s : ℕ) (αType : Fin 15 → ℕ) {N : ℕ} (V : ℕ)
    (hV : ∀ (K : Fin N → Fin 5) (w : Fin N → Fin 3),
      ((dwz63Split s).matchableCompatible αType K w).card ≤ V) :
    ∀ (K : Fin N → Fin 5) (w : Fin N → PositiveWord CWBlock 1),
      ((dwz63SplitPair s).matchableCompatible αType K w).card ≤ V :=
  fun K w ↦ (dwz63_card_matchableCompatiblePair_le s αType K w).trans
    (hV K (dwz63FineLeftDegree ∘ w))

end AlgebraicComplexity.Examples
